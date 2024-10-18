module Tbd.Doc
open Tbd

type Selector = 
  // Applicable to lists only
  | All
  | Index of int 
  | Tag of string
  // Applicable to records only
  | Field of string

type Selectors = Selector list

type Primitive =
  | Number of float
  | String of string

type Node = 
  | Record of string * list<string * Node>
  | List of string * list<Node>
  | Primitive of Primitive
  | Reference of Selectors

type Transformation = { Key : string; Label : string; Function : Primitive -> Primitive }

let transformations = 
  [ { Key = "take-first"; Label = "Take first letter of a string"
      Function = function String s -> String(s.Substring(0, 1)) | p -> p }
    { Key = "skip-first"; Label = "Skip first letter of a string"
      Function = function String s -> String(s.Substring(1)) | p -> p }
    { Key = "before-comma"; Label = "Take substring before comma"
      Function = function String s when s.Contains(",") -> String(s.Substring(0, s.IndexOf(","))) | p -> p }
    { Key = "after-comma"; Label = "Take substring after comma"
      Function = function String s when s.Contains(",") -> String(s.Substring(s.IndexOf(",")+1)) | p -> p }
    { Key = "upper"; Label = "Turn string into uppercase"
      Function = function String s -> String(s.ToUpper()) | p -> p }
    { Key = "lower"; Label = "Turn string into lowercase"
      Function = function String s -> String(s.ToLower()) | p -> p }
  ]

let transformationsLookup = System.Collections.Generic.Dictionary<_, _>() 
for t in transformations do transformationsLookup.[t.Key] <- t.Function

// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------

let replace f nd = 
  let rec loop path nd =
    match f path nd with 
    | Some res -> res
    | _ -> 
    match nd with 
    | List(tag, els) -> 
        List(tag, els |> List.mapi (fun i nd -> loop (path @ [Index i]) nd))
    | Record(tag, attrs) -> 
        Record(tag, attrs |> List.map (fun (n, nd) -> n, loop (path @ [Field n]) nd))
    | Reference _ | Primitive _ -> nd 
  loop [] nd

let fold f st value = 
  let rec loop path st nd =
    let st = f path nd st 
    match nd with 
    | List(_, els) -> 
        els |> List.foldi (fun st (i, nd) -> loop (path @ [Index i]) st nd) st
    | Record(_, nds) -> 
        nds |> List.fold (fun st (n, nd) -> loop (path @ [Field n]) st nd) st
    | Primitive _ | Reference _ -> 
        st
  loop [] st value

/// This is symmetric, i.e. matches p1 p2 = matches p2 = p1
let rec matches p1 p2 = 
  match p1, p2 with 
  | [], [] -> true
  | [], _ | _, [] -> false
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && matches p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && matches p1 p2
  | Tag(t1)::p1, Tag(t2)::p2 -> t1 = t2 && matches p1 p2
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> matches p1 p2
  | Tag(_)::p1, All::p2 | All::p1, Tag(_)::p2 -> matches p1 p2
  | _ -> false

/// Is 'p1' prefix of 'p2' 
let rec includes p1 p2 = 
  match p1, p2 with 
  | [], _ -> true
  | _, [] -> false
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && includes p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && includes p1 p2
  | Tag(t1)::p1, Tag(t2)::p2 -> t1 = t2 && includes p1 p2
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> includes p1 p2
  | Tag(_)::p1, All::p2 | All::p1, Tag(_)::p2 -> includes p1 p2
  | _ -> false

let select sel doc = 
  doc |> fold (fun p value st -> 
    if matches sel p then value::st else st) [] |> List.rev

let trace sel doc = 
  let rec loop trace sel nd = seq {
    match nd, sel with 
    | nd, [] -> yield nd, List.rev trace
    | List(_, els), (Index(i) as s)::sel -> 
        if i < 0 || i >= els.Length then ()
        else yield! loop ((nd, s)::trace) sel els.[i]
    | List(_, els), (Tag(t) as s)::sel -> 
        let els = els |> List.filter (function Record(t2, _) | List(t2, _) -> t2 = t | _ -> false)
        for el in els do yield! loop ((nd, s)::trace) sel el
    | List(_, els), (All as s)::sel -> 
        for el in els do yield! loop ((nd, s)::trace) sel el
    | Record(_, els), (Field(f) as s)::sel -> 
        let chOpt = List.tryFind (fst >> (=) f) els
        match chOpt with 
        | Some ch -> yield! loop ((nd, s)::trace) sel (snd ch)
        | _ -> ()
    | _ -> ()  }
  loop [] sel doc 

/// Generates a list of selectors where each 'All' or 'Tag'
/// is replaced with all possible 'Index' values.
let expandWildcards sel doc = 
  let rec loop acc sel nd = 
    match nd, sel with 
    | nd, [] -> List.map List.rev acc
    | Record(_, els), (Field(f) as s)::sel -> 
        loop (List.map (fun acc -> s::acc) acc) sel (snd (List.find (fst >> (=) f) els))
    | List(_, els), (Index(i) as s)::sel -> 
        loop (List.map (fun acc -> s::acc) acc) sel els.[i]
    | List(_, els), (Tag(t) as s)::sel -> 
        List.concat [
          for i, nd in Seq.indexed els do
            match nd with 
            | Record(t2, _) | List(t2, _) when t2 = t ->
                loop (List.map (fun acc -> (Index i)::acc) acc) sel nd
            | _ -> () ]
    | List(_, els), (All as s)::sel -> 
        List.concat [
          for i, nd in Seq.indexed els do
            loop (List.map (fun acc -> (Index i)::acc) acc) sel nd ]
    | _ -> failwith "expandWildcards: No matching element"
  loop [[]] sel doc 

let selectSingle sel doc = 
  match select sel doc with
  | [it] -> it
  | res -> failwithf "selectSingle: Looking for single %A but found %d" sel res.Length

// --------------------------------------------------------------------------------------
// Edits
// --------------------------------------------------------------------------------------
       
type Condition = EqualsTo of Primitive | NonEmpty 

type SharedEdit = 
  | ListReorder of Selectors * list<int>
  | RecordRenameField of Selectors * string * string
  | Copy of Selectors * Selectors
  | WrapRecord of id:string * tag:string * target:Selectors
  | WrapList of tag:string * target:Selectors
  | UpdateTag of Selectors * string * string
  | ListDelete of Selectors * int
  | RecordDelete of Selectors * string

type ValueEdit = 
  | PrimitiveEdit of Selectors * string
  | ListAppend of Selectors * Node
  | ListAppendFrom of Selectors * Selectors
  | RecordAdd of Selectors * string * Node
  | Check of Selectors * Condition

type SharedEditKind = ValueKind | StructuralKind

type EditKind =
  | Shared of SharedEditKind * SharedEdit
  | Value of ValueEdit

type Edit = 
  { Kind : EditKind }

// --------------------------------------------------------------------------------------
// Pretty printing
// --------------------------------------------------------------------------------------

let formatSelector = 
  List.map (function All -> "*" | Tag t -> $"<{t}>" | Index i -> string i | Field f -> f)
  >> String.concat "/"
  >> (+) "/"

let formatNode nd = 
  sprintf "%A" nd
  
let formatSharedKind = function
  | ValueKind -> "v" | StructuralKind -> "s"

let formatString (s:string) = 
  "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""

let formatEdit ed = 
  let fmt kvd kind args = $"""{formatSharedKind kind}.{kvd}({ String.concat "," args })"""
  match ed.Kind with
  | Value(PrimitiveEdit(sel, op)) -> 
      fmt "primitive" ValueKind [formatSelector sel; formatString op]
  | Value(ListAppend(sel, nd)) -> 
      fmt "listAppend" ValueKind [formatSelector sel; formatNode nd]
  | Value(ListAppendFrom(sel, src)) -> 
      fmt "listAppendFrom" ValueKind [formatSelector sel; formatSelector src]
  | Value(RecordAdd(sel, n, nd)) -> 
      fmt "recordAdd" ValueKind [formatSelector sel; formatString n; formatNode nd]
  | Value(Check(sel, NonEmpty)) -> 
      fmt "check" ValueKind [formatSelector sel; "nonempty"]
  | Value(Check(sel, EqualsTo (String s))) -> 
      fmt "check" ValueKind [formatSelector sel; "equals"; formatString s]
  | Value(Check(sel, EqualsTo (Number n))) -> 
      fmt "check" ValueKind [formatSelector sel; "equals"; string n]
  | Shared(sk, ListReorder(sel, ord)) -> 
      fmt "listReorder" sk [formatSelector sel; $"""[{ String.concat "," (List.map string ord) }])"""]
  | Shared(sk, RecordRenameField(sel, o, n)) -> 
      fmt "renameField" sk [formatSelector sel; formatString o; formatString n]
  | Shared(sk, Copy(sel, src)) -> 
      fmt "copy" sk [formatSelector sel; formatSelector src]
  | Shared(sk, WrapRecord(id, tag, sel)) -> 
      fmt "wrapRec" sk [formatSelector sel; formatString id; formatString tag]
  | Shared(sk, WrapList(tag, sel)) -> 
      fmt "wrapList" sk [formatSelector sel; formatString tag]
  | Shared(sk, UpdateTag(sel, tagOld, tagNew)) -> 
      fmt "updateTag" sk [formatSelector sel; formatString tagOld; formatString tagNew]
  | Shared(sk, ListDelete(sel, i)) -> 
      fmt "listDelete" sk [formatSelector sel; string i]
  | Shared(sk, RecordDelete(sel, f)) -> 
      fmt "recordDelete" sk [formatSelector sel; formatString f]

// --------------------------------------------------------------------------------------
// General purpose helpers for working with selectors
// --------------------------------------------------------------------------------------

let rec getNodeSelectors = function
  | Record(_, nds) -> List.collect getNodeSelectors (List.map snd nds)
  | List(_, nds) -> List.collect getNodeSelectors nds
  | Reference sels -> [sels]
  | Primitive _ -> []

let withNodeSelectors nd sels = 
  let mutable sels = sels
  let next() = let r = List.head sels in sels <- List.tail sels; r
  let rec loop nd = 
    match nd with 
    | Record(tag,  nds) -> Record(tag, List.map (fun (n, nd) -> n, loop nd) nds)
    | List(tag,  nds) -> List(tag, List.map loop nds)
    | Reference sels -> Reference(next()) 
    | Primitive _ -> nd
  loop nd

(*
/// Not including 'Reference' selectors in expressions
let getDependenciesSelectors ed = 
  match ed.Kind with 
  | PrimitiveEdit(s, _) | ListReorder(s, _) | RecordRenameField(s, _) 
  | UpdateTag(s, _, _) | WrapRecord(_, _, s) | WrapList(_, s)
  | ListAppend(s, _) | RecordAdd(s, _, _) | Replace(s, _) -> [s]
  | Copy(s1, s2) -> s1::s2::[]
*)

let getTargetSelector ed = 
  match ed.Kind with 
  // Selector is already pointing directly to the affected node
  | Shared(_, ListReorder(s, _)) 
  | Shared(_, UpdateTag(s, _, _)) 
  | Shared(_, Copy(s, _))
  | Value(PrimitiveEdit(s, _)) 
  | Value(Check(s, _)) -> s
  // Add selector to the end, pointing to the affected node
  | Shared(_, WrapList(_, s)) 
  | Value(ListAppend(s, _))
  | Value(ListAppendFrom(s, _)) -> s @ [All]
  | Shared(_, ListDelete(s, i)) -> s @ [Index i]
  | Shared(_, RecordRenameField(s, id, _)) 
  | Shared(_, RecordDelete(s, id))
  | Shared(_, WrapRecord(_, id, s)) 
  | Value(RecordAdd(s, id, _)) -> s @ [Field id]

let withTargetSelector tgt ed = 
  let getLastField tgt = match List.last tgt with Field f -> f | _ -> failwith "withTargetSelector - expected selector ending with a field"
  let getLastIndex tgt = match List.last tgt with Index i -> i | _ -> failwith "withTargetSelector - expected selector ending with an index"
  let ret nk = { Kind = nk }
  match ed.Kind with 
  // Selector is already pointing directly to the affected node
  | Shared(sk, ListReorder(_, m)) -> Shared(sk, ListReorder(tgt, m)) |> ret
  | Shared(sk, UpdateTag(_, t1, t2)) -> Shared(sk, UpdateTag(tgt, t1, t2)) |> ret
  | Shared(sk, Copy(_, s)) -> Shared(sk, Copy(tgt, s)) |> ret
  | Value(PrimitiveEdit(_, f)) -> Value(PrimitiveEdit(tgt, f)) |> ret
  | Value(Check(_, cond)) -> Value(Check(tgt, cond)) |> ret
  // Remove added selector, pointing to the affected node
  | Shared(sk, WrapList(t, _)) -> Shared(sk, WrapList(t, List.dropLast tgt)) |> ret
  | Value(ListAppend(_, nd)) -> Value(ListAppend(List.dropLast tgt, nd)) |> ret
  | Value(ListAppendFrom(_, src)) -> Value(ListAppendFrom(List.dropLast tgt, src)) |> ret
  | Shared(sk, ListDelete(_, _)) -> Shared(sk, ListDelete(List.dropLast tgt, getLastIndex tgt)) |> ret
  | Shared(sk, RecordRenameField(_, _, n)) -> Shared(sk, RecordRenameField(tgt, getLastField tgt, n)) |> ret
  | Shared(sk, RecordDelete(_, _)) -> Shared(sk, RecordDelete(List.dropLast tgt, getLastField tgt)) |> ret
  | Shared(sk, WrapRecord(t, _, _)) -> Shared(sk, WrapRecord(t, getLastField tgt, List.dropLast tgt)) |> ret
  | Value(RecordAdd(_, _, nd)) -> Value(RecordAdd(List.dropLast tgt, getLastField tgt, nd)) |> ret

let getTargetSelectorPrefixes eds = 
  let sels = System.Collections.Generic.HashSet<_>()
  for ed in eds do
    let sel = getTargetSelector ed
    for prefix in List.prefixes sel do ignore(sels.Add(prefix))
  List.sort (List.ofSeq sels)


let getSelectors ed = 
  match ed.Kind with 
  | Shared(_, ListReorder(s, _)) 
  | Shared(_, RecordRenameField(s, _, _)) 
  | Shared(_, UpdateTag(s, _, _)) 
  | Shared(_, WrapRecord(_, _, s)) 
  | Shared(_, WrapList(_, s)) 
  | Shared(_, ListDelete(s, _))
  | Shared(_, RecordDelete(s, _))
  | Value(PrimitiveEdit(s, _)) 
  | Value(Check(s, _)) -> [s]
  | Value(ListAppend(s, nd)) 
  | Value(RecordAdd(s, _, nd)) -> s :: (getNodeSelectors nd)
  | Value(ListAppendFrom(s1, s2)) 
  | Shared(_, Copy(s1, s2)) -> [s1; s2]

let withSelectors sels ed =
  let ret nk = { Kind = nk }
  match ed.Kind with
  | Value(ListAppend(_, nd)) -> Value(ListAppend(List.head sels, withNodeSelectors nd (List.tail sels))) |> ret
  | Value(ListAppendFrom(_, _)) -> Value(ListAppendFrom(List.head sels, List.exactlyOne (List.tail sels))) |> ret
  | Value(RecordAdd(_, s, nd)) -> Value(RecordAdd(List.head sels, s, withNodeSelectors nd (List.tail sels))) |> ret
  | Value(PrimitiveEdit(_, f)) -> Value(PrimitiveEdit(List.exactlyOne sels, f)) |> ret
  | Value(Check(_, cond)) -> Value(Check(List.exactlyOne sels, cond)) |> ret
  | Shared(sk, ListDelete(_, i)) -> Shared(sk, ListDelete(List.exactlyOne sels, i)) |> ret
  | Shared(sk, RecordDelete(_, f)) -> Shared(sk, RecordDelete(List.exactlyOne sels, f)) |> ret
  | Shared(sk, ListReorder(_, m)) -> Shared(sk, ListReorder(List.exactlyOne sels, m)) |> ret
  | Shared(sk, WrapRecord(t, f, _)) -> Shared(sk, WrapRecord(t, f, List.exactlyOne sels) ) |> ret
  | Shared(sk, WrapList(t, _)) -> Shared(sk, WrapList(t, List.exactlyOne sels) ) |> ret
  | Shared(sk, UpdateTag(_, t1, t2)) -> Shared(sk, UpdateTag(List.exactlyOne sels, t1, t2) ) |> ret
  | Shared(sk, Copy(_, _)) -> Shared(sk, Copy(List.head sels, List.exactlyOne (List.tail sels))) |> ret
  | Shared(sk, RecordRenameField(_, o, n)) -> Shared(sk, RecordRenameField(List.exactlyOne sels, o, n) ) |> ret

let mapSelectors f ed = 
  withSelectors (List.map f (getSelectors ed)) ed

/// If 'p1' is prefix of 'p2', return the rest of 'p2'.
/// This also computes 'more specific prefix' which is a version
/// of the prefix where 'Index' is preferred over 'All' when matched.
let removeSelectorPrefix p1 p2 = 
  let rec loop specPref p1 p2 = 
    match p1, p2 with 
    | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> loop (Field(f1)::specPref) p1 p2
    | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> loop (Index(i1)::specPref) p1 p2
    | Tag(t1)::p1, Tag(t2)::p2 when t1 = t2 -> loop (Tag(t1)::specPref) p1 p2
    // TODO: Arguably, we should not insert into specific index (only All) as that is a 'type error'
    // Meaning that when called from 'scopeEdit', then 'p1' should not contain 'Index' ?
    | Index(i)::p1, All::p2 ->
        failwith "removeSelectorPrefix - Index/All - arguably error %"
      //  loop (Index(i)::specPref) p1 p2
    //| Index(_)::_ | All(_::)
    //| Tag(t)::p1, All::p2 | All::p1, Tag(t)::p2 -> loop (Tag(t)::specPref) p1 p2
    //
    // More thinking - When called from 'scopeEdit' we maybe do not want to scope edits that 
    // have been applied to specific indices (because we do not want to 
    // apply those to newly added nodes)? but maybe it is ok??
    //
    // When called from 'copyEdits' - if we copied All of something (p1) but
    // have an edit to a specific index in the source, we want to also apply it
    // to the other location at the given index.
    // So for that we need -
    // (when called from scopeEdit, if we are appending to All, but an edit was
    // done at a specific index, we do not want to apply it to All - but are ok
    // with applying it at the specific index - so this is also OK)
    | All::p1, Index(i)::p2 ->
        loop (Index(i)::specPref) p1 p2

    | All::p1, All::p2 -> loop (All::specPref) p1 p2
    | [], p2 -> Some(List.rev specPref, p2)
    | _ -> None
  loop [] p1 p2
  
// --------------------------------------------------------------------------------------
// Helpes for transforming edits when merging / applying
// --------------------------------------------------------------------------------------

let (|MatchingFirst|_|) = function 
  | All::selOther, All::selWrap -> Some(All, selOther, selWrap)
  | Field(fo)::selOther, Field(fr)::selWrap when fo = fr -> Some(Field(fo), selOther, selWrap)
  | Index(io)::selOther, Index(ir)::selWrap when io = ir -> Some(Index(io), selOther, selWrap)
  | Index(io)::selOther, All::selWrap -> Some(Index(io), selOther, selWrap)
  | Tag(tgo)::selOther, Tag(tgr)::selWrap when tgo = tgr -> Some(Tag(tgo), selOther, selWrap)
  | Tag(tgo)::selOther, All::selWrap -> Some(Tag(tgo), selOther, selWrap)
  | _ -> None

let (|IncompatibleFirst|_|) = function
  | Field(f1)::_, Field(f2)::_ when f1 <> f2 -> Some()
  | Index(i1)::_, Index(i2)::_ when i1 <> i2 -> Some()
  | Tag(t1)::_, Tag(t2)::_ when t1 <> t2 -> Some()
  | (All|Index _|Tag _|Field _)::_, []
  | (All|Index _|Tag _)::_, Field(_)::_ 
  | Field(_)::_, (All|Index _|Tag _)::_ -> Some()
  | [], _ -> Some()
  | _ -> None

let (|TooSpecific|_|) = function
  | All::_,  (s & Index _)::_ 
  | All::_, (s & Tag _)::_ -> Some(s)
  | _ -> None 

/// Returns a modified version of 'selOther' to match
/// item deletion at selDelete (by decrementing indices of affected selectors)
let decrementSelectorsAfterDel selDelete idel selOther = 
  let rec decafter selDelete selOther =
    match selOther, selDelete with 
    | Index(io)::selOther, [] -> 
        if io >= idel then Index(io - 1)::selOther
        else Index(io)::selOther
    | MatchingFirst(s, selOther, selDelete) -> s::(decafter selDelete selOther)
    | TooSpecific(s) -> failwith $"decrementSelectorsAfterDel - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"decrementSelectorsAfterDel - Missing case: {selOther} vs. {selDelete}"
  decafter selDelete selOther
 
/// Returns a modified version of 'selOther' to match
/// reordering of indices 'ord' at location specified by 'selReord'
let reorderSelectors ord selReord selOther = 
  let rec reorder selOther selReord =
    match selOther, selReord with 
    | Index(io)::selOther, [] -> Index(List.findIndex ((=) io) ord)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(reorder selOther selWrap)
    | TooSpecific(s) -> failwith $"reorderSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther        
    | _ -> failwith $"reorderSelectors - Missing case: {selOther} vs. {selReord}"
  reorder selOther selReord

/// Returns a modified version of 'selOther' to match
/// the additional wrapping (in a record with original at @id) at location specified by 'selWrap'
let wrapRecordSelectors id selWrap selOther =
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> Field(id)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
    | TooSpecific(s) -> failwith $"wrapRecordSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"wrapRecordSelectors - Missing case: {selOther} vs. {selWrap}"
  wrapsels selOther selWrap
  
/// Returns a modified version of 'selOther' to match
/// the additional wrapping (in a list) at location specified by 'selWrap'
let wrapListSelectors selWrap selOther =
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> All::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
    | TooSpecific(s) -> failwith $"wrapListSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"wrapListSelectors - Missing case: {selOther} vs. {selWrap}"
  wrapsels selOther selWrap

/// Returns a modified version of 'selOther' to match
/// the tag rename done at location specified by 'selUpd'
let updateTagSelectors tagOld tagNew selUpd selOther =
  let rec wrapsels selOther selUpd =
    match selOther, selUpd with 
    | Tag(t)::selOther, [] when t = tagOld -> Tag(tagNew)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selUpd)
    | TooSpecific(s) -> failwith $"updateTagSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"updateTagSelectors - Missing case: {selOther} vs. {selUpd}"
  wrapsels selOther selUpd

/// Returns a modified version of 'selOther' to match
/// the changed field ID at location specified by 'selReord'
let renameFieldSelectors fold fnew selRename selOther =
  let rec reidsels selOther selRename =
    match selOther, selRename with 
    | Field(fo)::selOther, [] when fo = fold -> Field(fnew)::(reidsels selOther []) // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(reidsels selOther selWrap)
    | TooSpecific(s) -> failwith $"renameFieldSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"renameFieldSelectors - Missing case: {selOther} vs. {selRename}"
  reidsels selOther selRename

// --------------------------------------------------------------------------------------
// Apply
// --------------------------------------------------------------------------------------

exception ConditionCheckFailed of string

let rec isStructuralSelector sel = 
  match sel with 
  | [] -> true
  | Index _::_ -> false
  | (All | Tag _ | Field _)::sel -> isStructuralSelector sel

let apply doc edit =
  match edit.Kind with

  // **Value edits** - These do not affect any selectors elsewhere in the document.
  // Add and Append change structure in that they add new items that may have a different
  // shape. This is allowed at runtime, but it may break code referring to newly added
  // things. We could check this using some kind of type system.

  | Value(Check(sel, cond)) ->
      match cond, select sel doc with 
      | EqualsTo(String s1), [Primitive(String s2)] -> if s1 <> s2 then raise(ConditionCheckFailed $"apply.Check: EqualsTo failed ({s1}<>{s2})")
      | EqualsTo(Number n1), [Primitive(Number n2)] -> if n1 <> n2 then raise(ConditionCheckFailed $"apply.Check: EqualsTo failed ({n1}<>{n2})")
      | NonEmpty, [Primitive(Number _)] -> ()
      | NonEmpty, [Primitive(String s)] -> if System.String.IsNullOrWhiteSpace(s) then raise(ConditionCheckFailed $"apply.Check: NonEmpty failed ({s})")
      | cond, nd -> raise (ConditionCheckFailed $"apply.Check Condition ({cond}) failed ({nd})")
      doc

  | Value(PrimitiveEdit(sel, f)) ->
      replace (fun p el -> 
        match el with 
        | Primitive(v) when matches p sel -> Some(Primitive(transformationsLookup.[f] v))
        | _ -> None ) doc

  | Value(ListAppend(sel, nd)) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> Some(List(tag, nds @ [nd]))
        | _ -> None ) doc

  | Value(ListAppendFrom(sel, src)) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> Some(List(tag, nds @ [selectSingle src doc]))
        | _ -> None ) doc

  | Value(RecordAdd(sel, fld, nd)) ->
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> 
            let nds = nds |> List.filter (fun (k, _) -> k <> fld)
            Some(Record(tag, nds @ [fld, nd]))
        | _ -> None ) doc

  // **Shared edits** - These can be applied both as structural edits to change document shape
  // or as value edits to affect only particular values. We allow structural edits only when
  // the target selector is structural too! Using those as value edits changes structure too
  // and could consequently break things (but see note above).

  | Shared(sk, ListDelete(sel, idel)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.ListDelete - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p -> function
        | List(t, items) when matches p sel -> 
            let items = items |> List.indexed |> List.choose (fun (j, it) -> 
              if idel <> j  then Some it else None)
            Some(List(t, items))
        | _ -> None) doc
      if sk = StructuralKind then 
        let nsels = getNodeSelectors doc |> List.map (decrementSelectorsAfterDel sel idel)
        withNodeSelectors doc nsels
      else doc

  | Shared(sk, RecordDelete(sel, fdel)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.RecordDelete - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p -> function
        | Record(t, nds) when matches p sel ->
            let nds = nds |> List.filter (fun (f, _) -> f <> fdel)
            Some(Record(t, nds))
        | _ -> None) doc
      if sk = StructuralKind then 
        // We cannot update selectors if the target node was deleted, but 
        // we can check there are no such selectors in the document.
        for docSel in getNodeSelectors doc do 
          if includes (sel @ [Field fdel])docSel then
            failwith $"apply.RecordDelete - Cannot delete {formatSelector sel}. Document contains conflicting selector {formatSelector docSel}."
        doc
      else doc

  | Shared(sk, ListReorder(sel, ord)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.ListReorder - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> Some(List(tag, [ for i in ord -> nds.[i]]))
        | _ -> None ) doc
      if sk = StructuralKind then
        let nsels = getNodeSelectors doc |> List.map (reorderSelectors ord sel)
        withNodeSelectors doc nsels
      else doc

  | Shared(sk, WrapRecord(id, tag, sel)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.WrapRecord - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el -> 
        if matches p sel then Some(Record(tag, [id, el]))
        else None ) doc
      if sk = StructuralKind then
        let nsels = getNodeSelectors doc |> List.map (wrapRecordSelectors id sel)
        withNodeSelectors doc nsels
      else doc

  | Shared(sk, WrapList(tag, sel)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.WrapList - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el -> 
        if matches p sel then Some(List(tag, [el]))
        else None ) doc
      if sk = StructuralKind then
        let nsels = getNodeSelectors doc |> List.map (wrapListSelectors sel)
        withNodeSelectors doc nsels
      else doc
    
  | Shared(sk, UpdateTag(sel, tagOld, tagNew)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.UpdateTag - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el ->
        match el with 
        | Record(t, nds) when matches p sel && t = tagOld -> Some(Record(tagNew, nds))
        | List(t, nds) when matches p sel && t = tagOld -> Some(List(tagNew, nds))
        | _ -> None ) doc
      if sk = StructuralKind then
        let nsels = getNodeSelectors doc |> List.map (updateTagSelectors tagOld tagNew sel)
        withNodeSelectors doc nsels
      else doc

  | Shared(sk, RecordRenameField(sel, fold, fnew)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.RecordRenameField - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el -> 
        match el with 
        | Record(t, nds) when matches p sel -> 
            Some(Record(t, List.map (fun (f, nd) -> if f = fold then fnew, nd else f, nd) nds))
        | _ -> None ) doc
      if sk = StructuralKind then
        let nsels = getNodeSelectors doc |> List.map (renameFieldSelectors fold fnew sel)
        withNodeSelectors doc nsels
      else doc

  | Shared(sk, Copy(sel, src)) ->
      if sk = StructuralKind && not (isStructuralSelector sel) then 
        failwith $"apply.Copy - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."

      let mutable exprs = 
        let srcNodes = select src doc
        match select sel doc with         
        | tgs when tgs.Length = srcNodes.Length -> srcNodes
        // Slightly clever in that we can copy multiple source nodes into a single target list node
        // (this is needed for evaluation of arguments - see eval.fs)
        | [List(t, _)] -> [List(t, srcNodes)] 
        | [tgt] -> failwith $"apply.Copy - Single target {formatSelector sel} but multiple source nodes from {formatSelector src}. Target={formatNode tgt}"; 
        | tgtNodes -> failwith $"apply.Copy - Mismatching number of source and target notes. Edit: {formatEdit edit}, src nodes: {srcNodes.Length}, tgt nodes: {tgtNodes.Length} "
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy - Unexpected"
      let doc = replace (fun p el -> 
        if matches p sel then Some(next())
        else None ) doc

      if sk = StructuralKind then 
        // We cannot update selectors in the document to match this edit, so make sure 
        // there are none (when copying from referenced source, we'd need to duplicate 
        // the reference as done when merging in 'copyEdit'; when copying to 
        // a location, we have no clue what the structure change is, so cannot update.)
        for docSel in getNodeSelectors doc do
          if includes sel docSel then
            failwith $"apply.RecordDelete - Cannot copy to {formatSelector sel}. Document contains conflicting selector {formatSelector docSel}."
          if includes src docSel then
            failwith $"apply.RecordDelete - Cannot copy from {formatSelector sel}. Document contains conflicting selector {formatSelector docSel}."
        doc
      else doc


// --------------------------------------------------------------------------------------
// Merge
// --------------------------------------------------------------------------------------

type ScopingResult = AllOutOfScope | TargetOutOfScope | SourceOutOfScope | InScope of Edit

let tryScopeSelectors f edit = 
  let sels = getSelectors edit 
  let nsels = sels |> List.choose f
  if nsels.Length = 0 then AllOutOfScope
  elif nsels.Length = sels.Length then InScope(withSelectors nsels edit)
  else 
    match f (getTargetSelector edit) with 
    | None -> TargetOutOfScope
    | _ -> SourceOutOfScope

let scopeEdit oldBase newBase edit = 
  edit |> tryScopeSelectors (fun s -> 
    match removeSelectorPrefix oldBase s with 
    | Some(_, sel) -> Some(newBase @ sel)
    | _ -> None)

let rec substituteWithMoreSpecific specPrefix sels = 
  match specPrefix, sels with
  | Field(f1)::specPrefix, Field(f2)::sels when f1 = f2 -> Field(f1)::(substituteWithMoreSpecific specPrefix sels)
  | Index(i1)::specPrefix, Index(i2)::sels when i1 = i2 -> Index(i1)::(substituteWithMoreSpecific specPrefix sels)
  | All::specPrefix, Index(i1)::sels 
  | Index(i1)::specPrefix, All::sels -> Index(i1)::(substituteWithMoreSpecific specPrefix sels)
  | All::specPrefix, Tag(t1)::sels 
  | Tag(t1)::specPrefix, All::sels -> Tag(t1)::(substituteWithMoreSpecific specPrefix sels)
  | All::specPrefix, All::sels -> All::(substituteWithMoreSpecific specPrefix sels)
  | _ -> sels  // Not matching, but that's OK, we only want to subsitute prefix
 

let copyEdit e1 srcSel tgtSel = 
  // For cases when the copied thing is directly the target of the edit 'e1'
  let e1tgtSel = getTargetSelector e1
  if matches e1tgtSel srcSel then 
    Some [e1; withTargetSelector tgtSel e1]
  else
  // For cases when the edit 'e1' targets something inside the copied (from srcSel to tgtSel)
  let origSels = getSelectors e1 
  let newSels = origSels |> List.map (fun sel ->
    match removeSelectorPrefix srcSel sel with 
    | Some(specPrefix, suffix) -> 
        tgtSel @ suffix |> substituteWithMoreSpecific specPrefix
    | _ -> sel)
  if origSels = newSels then None
  else 
    Some [e1; withSelectors newSels e1]
  

// Assuming 'e1' and 'e2' happened independently, we want to modify
// 'e1' so that it can be placed after 'e2'. If the edit 'e2' was 
// structural edit that affected the shape of the document, we need
// to transform the selectors in 'e1' to match the new shape.
//
// If the 'e2' edit was structural Copy and the target of 'e1' was
// the source of the copy, we return [e1;e1'] that targets both the
// original node and the one produced by the copying.
//
// Note that this is doing almost exactly the same thing as when 
// editing existing document (there, we update selectors in document)
//
let updateSelectors e1 e2 = 
  match e2.Kind with 
  // Value edits do not affect other selectors
  | Value(_)
  | Shared(ValueKind, _) -> [e1]
  
  // For structural edits, transform the selectors in the
  // other edit in a way corresponding to the edit
  | Shared(StructuralKind, ListDelete(sel, idel)) ->
      [mapSelectors (decrementSelectorsAfterDel sel idel) e1]
  | Shared(StructuralKind, WrapRecord(id, tag, sel)) ->             
      [mapSelectors (wrapRecordSelectors id sel) e1]
  | Shared(StructuralKind, WrapList(tag, sel)) -> 
      [mapSelectors (wrapListSelectors sel) e1]
  | Shared(StructuralKind, UpdateTag(sel, t1, t2)) ->
      [mapSelectors (updateTagSelectors t1 t2 sel) e1]
  | Shared(StructuralKind, RecordRenameField(sel, fold, fnew)) ->
      [mapSelectors (renameFieldSelectors fold fnew sel) e1]
  | Shared(StructuralKind, ListReorder(sel, ord)) -> 
      // TODO: If 'e1' is ListReorder pointing to the same thing, do something clever!
      // (treat this as a conflict and then do something about it...)
      // (get back to this once we have conflict detection...)
      [mapSelectors (reorderSelectors ord sel) e1]

  // For structural copy, we may need to duplicate the edit e1
  | Shared(StructuralKind, Copy(tgtSel, srcSel)) -> 
      match copyEdit e1 srcSel tgtSel with 
      | Some res -> res
      | _ ->
          // TODO: What does this even do?
          let target = getTargetSelector e1
          let conflict = removeSelectorPrefix srcSel target |> Option.isSome
          if conflict then failwith $"CONFLICT!!!\ne1={e1}\ne2={e2}"
          else [e1]
  
  | Shared(StructuralKind, RecordDelete _) -> failwith "updateSelectors - Detect conflicts - record delete"


// Assuming 'e1' and 'e2' happened independently, we want to modify
// 'e1' so that it can be placed after 'e2'. 
//
// * If the edit 'e1' is adding new items to the document, we want to apply the 
//   transformation done by 'e2' to the value to be added. If the edit 'e1' is copying.
//
// * If the edit 'e1' is appending a list item from somewhere else in the document and
//   'e2' did some operation to the list we are appending to, return edit that first
//   does the same operation to the source of the copy 
//
// * If the edit 'e1' is adding new item to a record, then .. think about this.
// * If the edit 'e1' is copying .. think about this.
//
type EditMoveState = 
  { UniqueTempField : string; PrefixEdits : Edit list; SuffixEdits : Edit list }

let applyToAdded ctx e1 e2 = 
  //printfn $"applyToAdded\n  * e1={formatEdit e1}\n  * e2={formatEdit e2}"
  match e1.Kind with 
   // We are appending under 'sel', so the selector for 'nd' will be 'sel/*' 
  | Value(ListAppend(sel, nd)) -> 
      match scopeEdit (sel @ [All]) [] e2 with
      | InScope e2scoped ->
          let nnd = apply nd e2scoped
          [ { e1 with Kind = Value(ListAppend(sel, nnd)) }], ctx
      | AllOutOfScope | TargetOutOfScope -> [e1], ctx
      | SourceOutOfScope -> 
          // TODO: If we have a more elaborate transform, we can probably do this
          // (e.g., store 'nd' somewhere in doc, transform it & ListAppendFrom)
          failwith "applyToAdded: Source out of scope (TODO)" 


  | Value(ListAppendFrom(sel, src)) -> 
      // A naive implementation is to scope e2 to 'src' and then return [e2scoped; e1] 
      // This mutates the source in-place in the document - which works for my demos
      // but it is not correct in general. Instead, we create temp field, apply
      // all edits to this field and then appendfrom this new temp field.
      match scopeEdit (sel @ [All]) [Field ctx.UniqueTempField ] e2 with
      | InScope e2scoped -> 
          let prefix = [
            { Kind = Value(RecordAdd([], ctx.UniqueTempField, Primitive (String "empty"))) }
            { Kind = Shared(ValueKind, Copy([Field ctx.UniqueTempField], src)) } ]
          let suffix = [
            { Kind = Shared(ValueKind, RecordDelete([], ctx.UniqueTempField)) } ]
          let res = [
            e2scoped
            { Kind = Value(ListAppendFrom(sel, [Field ctx.UniqueTempField] )) } ]
          if ctx.PrefixEdits = [] then res, { ctx with PrefixEdits = prefix; SuffixEdits = suffix } else 
          res, ctx
      | _ -> [e1], ctx

  | Value(RecordAdd(sel, fld, nd)) -> 
      match scopeEdit (sel @ [Field fld]) [] e2 with
      | InScope _ | SourceOutOfScope -> 
          // TODO: This is conflict, because e2 was doing something with a 
          // record field and e1 is now replacing it with a new thing.
          // We can let 'e1' win (return [e1]) or 'e2' win (return [])
          [e1], ctx
      | AllOutOfScope | TargetOutOfScope -> [e1], ctx

  | Shared(_, Copy(sel, src)) -> 
      match scopeEdit sel src e2 with
      | InScope _ | SourceOutOfScope -> 
          // TODO: Same conflict as in the case of RecordAdd - with same options.
          [e1], ctx
      | AllOutOfScope | TargetOutOfScope -> [e1], ctx

  | _ -> [e1], ctx

// Assuming 'e1' and 'e2' happened independently,
// modify 'e1' so that it can be placed after 'e2'.
let moveBefore ctx e1 e2 = 
  let e1s, ctx = applyToAdded ctx e1 e2
  e1s |> List.collect (fun e1 -> updateSelectors e1 e2), ctx


// --------------------------------------------------------------------------------------
// Edit groups
// --------------------------------------------------------------------------------------

type EditList = 
  { Groups : Edit list list }
  member x.Item(i) = x.[i .. i].Groups |> Seq.head |> Seq.head
  member x.GetSlice(start, finish) =
    let start = start |> Option.defaultValue 0
    let finish = finish |> Option.defaultWith (fun () -> x.Length - 1)
    { Groups = List.sliceNested  start finish x.Groups }
  member x.Length = 
    List.sumBy List.length x.Groups
  member x.Truncate n =
    { Groups = List.truncateNested n x.Groups }
  member x.Append eds = 
    { Groups = x.Groups @ eds.Groups }
  member x.Hash = 
    x.Groups |> List.collect id |> List.fold (fun hashSoFar edit -> hash (hashSoFar, edit)) 0
  member x.EditsByHash(hashToFind) = 
    let mutable hashSoFar = 0
    let res = x.Groups |> List.takeWhileNested (fun edit -> 
      if hashSoFar = hashToFind then false else
      hashSoFar <- hash (hashSoFar, edit) 
      true )
    if hashSoFar = hashToFind then Some { Groups = res } else None

let applyHistory initial hist =
  hist.Groups |> List.fold (List.fold apply) initial
  
let filterDisabledGroups initial hist = 
  { Groups = hist.Groups |> List.filterWithState (fun state group ->
      try true, group |> List.fold apply state
      with ConditionCheckFailed _ -> false, state) initial }
  
let mergeHistories h1 h2 =
  let shared, (e1s, e2s) = List.sharedPrefixNested h1.Groups h2.Groups
  let counter = let mutable n = 0 in (fun () -> n <- n + 1; n)
  let e2sAfter = 
    e2s |> List.collectNested (fun e2 ->
        printfn $"Move edit e2: {formatEdit e2}"
        // For a given edit 'e2', move it before all the edits in 'e1s' using 'moveBefore'
        // (caveat is that the operation can turn it into multiple edits)
        let mutable ctx = { UniqueTempField = $"$uniquetemp_{counter()}"; PrefixEdits = []; SuffixEdits = [] }
        let res = 
          List.foldNested (fun e2 e1 -> 
            printfn $"    - after e1: {formatEdit e1}"
            //printfn "Moving %A before %s" (List.map formatEdit e2) (formatEdit e1)
            let e2s, nctx = e2 |> List.foldCollect (fun ctx e2 -> moveBefore ctx e2 e1) ctx
            ctx <- nctx
            e2s ) [e2] e1s 
        let res = ctx.PrefixEdits @ res @ ctx.SuffixEdits
        printfn $"""    = [{String.concat ", " (List.map formatEdit res)}]"""
        res
          )         
  //printfn "MERGE HISTORIES"
  //printfn "Before transform: %A" (List.mapNested formatEdit e2s)
  //printfn "After transform: %A" (List.mapNested formatEdit e2sAfter)
  { Groups = shared @ e1s @ e2sAfter }



// --------------------------------------------------------------------------------------
// Representing edits as nodes
// --------------------------------------------------------------------------------------
  
let (|Lookup|) args = dict args
let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  if d.ContainsKey k then Some(d.[k]) else None
let (|Finds|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(String s) -> Some s | _ -> None
let (|Findn|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(Number n) -> Some (int n) | _ -> None
let (|Findsk|_|) (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue("kind") with 
  | true, Primitive(String "structural") -> Some(StructuralKind)
  | true, Primitive(String "value") -> Some(ValueKind)
  | true, v -> failwith $"Findsk: expected 'structural' or 'value' but got '{v}'"
  | _ -> None
let rcd id kvp = Record(id, kvp)

let representKind = function
  | StructuralKind -> "kind", Primitive(String "structural")
  | ValueKind -> "kind", Primitive(String "value")

let representSel sel = 
  List("x-selectors", 
    [ for s in sel ->
        match s with 
        | All -> Primitive(String "*")
        | Tag t -> Primitive(String("#" + t))
        | Index n -> Primitive(Number n)
        | Field f -> Primitive(String f) ])

let unrepresentSel expr =
  match expr with 
  | List("x-selectors", sels) ->
      sels |> List.map (function 
        | Primitive(String "*") -> All 
        | Primitive(String s) when s.Length <> 0 && s.[0] = '#' -> Field (s.Substring(1))
        | Primitive(String s) -> Field s
        | Primitive(Number n) -> Index (int n)
        | _ -> failwith "unrepresentSel: Invalid selector")
  | _ -> failwith $"unrepresentSel: Not a selector: {expr}"

let representIntList ns =
  List("x-int-list", [for n in ns -> Primitive(Number(float n)) ])

let unrepresentIntList nd =
  match nd with 
  | List("x-int-list", nds) ->
      List.map (function Primitive(Number n) -> int n | _ -> failwith "unrepresentIntList - Not a number") nds
  | _ -> failwith $"unrepresentIntList - Invalid node {nd}"

let representCond cond = 
  match cond with 
  | EqualsTo(nd) -> [ "node", Primitive nd ] |> rcd "x-cond-equals"
  | NonEmpty -> [] |> rcd "x-cond-nonempty"

let unrepresentCond nd = 
  match nd with 
  | Record("x-cond-equals", Lookup(Find "node" (Primitive v))) -> EqualsTo(v)
  | Record("x-cond-nonempty", []) -> NonEmpty
  | _ -> failwith $"unrepresentCond - Invalid node {nd}"

let unrepresent nd = 
  // NOTE: This works if the 'match' is not wrapped inside another expression (e.g. let) otherwise
  // Fable creates 600MB JavaScript file (https://x.com/tomaspetricek/status/1845753585163731319)
  let ret nd = { Kind = nd }
  match nd with
  // Value edits
  | Record("x-edit-append", Lookup (Find "target" sel & Find "node" nd)) ->
      Value(ListAppend(unrepresentSel sel, nd)) |> ret
  | Record("x-edit-appendfrom", Lookup (Find "target" sel & Find "src" src)) ->
      Value(ListAppendFrom(unrepresentSel sel, unrepresentSel src)) |> ret
  | Record("x-edit-add", Lookup (Find "target" sel & Finds "field" f & Find "node" nd)) ->
      Value(RecordAdd(unrepresentSel sel, f, nd)) |> ret
  | Record("x-edit-check", Lookup (Find "target" tgt & Find "cond" cond)) ->
      Value(Check(unrepresentSel tgt, unrepresentCond cond)) |> ret
  | Record("x-edit-primitive", Lookup (Find "target" tgt & Finds "op" op)) ->
      Value(PrimitiveEdit(unrepresentSel tgt, op)) |> ret
  // Shared edits
  | Record("x-edit-wraprec", Lookup(Findsk sk & Finds "tag" tag & Finds "fld" id & Find "target" target)) ->
      Shared(sk, WrapRecord(tag, id, unrepresentSel target)) |> ret
  | Record("x-edit-renamefld", Lookup (Findsk sk & Find "target" sel & Finds "old" fold & Finds "new" fnew)) ->
      Shared(sk, RecordRenameField(unrepresentSel sel, fold, fnew)) |> ret
  | Record("x-edit-copy", Lookup (Findsk sk & Find "target" tgt & Find "source" src)) ->
      Shared(sk, Copy(unrepresentSel tgt, unrepresentSel src)) |> ret
  | Record("x-edit-listdelete", Lookup (Findsk sk & Find "target" tgt & Findn "index" i)) ->
      Shared(sk, ListDelete(unrepresentSel tgt, i)) |> ret
  | Record("x-edit-recdelete", Lookup (Findsk sk & Find "target" tgt & Finds "field" fld)) ->
      Shared(sk, RecordDelete(unrepresentSel tgt, fld)) |> ret
  | Record("x-edit-wraplist", Lookup (Findsk sk & Find "target" tgt & Finds "tag" tag)) ->
      Shared(sk, WrapList(tag, unrepresentSel tgt)) |> ret
  | Record("x-edit-listreorder", Lookup (Findsk sk & Find "target" tgt & Find "perm" perm)) ->
      Shared(sk, ListReorder(unrepresentSel tgt, unrepresentIntList perm)) |> ret
  | Record("x-edit-updatetag", Lookup (Findsk sk & Find "target" tgt & Finds "old" otag & Finds "new" ntag)) ->
      Shared(sk, UpdateTag(unrepresentSel tgt, otag, ntag)) |> ret
  | _ -> failwith $"unrepresent - Missing case for: {nd}"

let represent op = 
  let ps v = Primitive(String v)
  let pn i = Primitive(Number i)
  match op.Kind with 
  // Value edits
  | Value(ListAppend(target, nd)) ->
      rcd "x-edit-append" [ "target", representSel target; "node", nd ]
  | Value(ListAppendFrom(target, src)) ->
      rcd "x-edit-appendfrom" [ "target", representSel target; "src", representSel src ]
  | Value(RecordAdd(target, f, nd)) ->
      rcd "x-edit-add" [ "target", representSel target; "field", ps f; "node", nd ]
  | Value(Check(target, cond)) -> 
      rcd "x-edit-check" [ "target", representSel target; "cond", representCond cond ]
  | Value(PrimitiveEdit(target, op)) ->
      rcd "x-edit-primitive" [ "target", representSel target; "op", ps op ]
  // Shared edits
  | Shared(sk, WrapRecord(tag, id, target)) ->
      rcd "x-edit-wraprec" [ "tag", ps tag; "fld", ps id; "target", representSel target; representKind sk ] 
  | Shared(sk, RecordRenameField(target, fold, fnew)) ->
      rcd "x-edit-renamefld" [ "target", representSel target; "old", ps fold; "new", ps fnew; representKind sk ]
  | Shared(sk, Copy(target, source)) ->
      rcd "x-edit-copy" [ "target", representSel target; "source", representSel source; representKind sk ]
  | Shared(sk, ListDelete(target, i)) ->
      rcd "x-edit-listdelete" [ "target", representSel target; representKind sk; "index", pn i ]
  | Shared(sk, RecordDelete(target, fld)) ->
      rcd "x-edit-recdelete" [ "target", representSel target; representKind sk; "field", ps fld ]
  | Shared(sk, WrapList(tag, target)) ->
      rcd "x-edit-wraplist" [ "target", representSel target; "tag", ps tag; representKind sk ]
  | Shared(sk, ListReorder(target, perm)) ->
      rcd "x-edit-listreorder" [ "target", representSel target; "perm", representIntList perm; representKind sk ]
  | Shared(sk, UpdateTag(target, otag, ntag)) ->
      rcd "x-edit-updatetag" [ "target", representSel target; "old", ps otag; "new", ps ntag; representKind sk ]

