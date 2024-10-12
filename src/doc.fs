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

let replaceField f nd = 
  let rec loop path nd =
    match nd with 
    | List(tag, els) -> 
        List(tag, els |> List.mapi (fun i nd -> loop (path @ [Index i]) nd))
    | Record(tag, attrs) -> 
        Record(tag, attrs |> List.map (fun (n, nd) -> 
          let path = path @ [Field n]
          match f path nd with 
          | Some res -> res
          | _ -> n, loop path nd))
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

type Source = ConstSource of Node | RefSource of Selectors
                                                            // Kind   | Effect on selectors
type EditKind =                                             // =======|====================
  | PrimitiveEdit of Selectors * string                     // Value  | NS
  | ListAppend of Selectors * Source                        // ?      | NS
  | ListReorder of Selectors * list<int>                    // Value  | Change index
  | RecordAdd of Selectors * string * Source                // Struct | NS
  | RecordRenameField of Selectors * string                 // Struct | Change field
  | Copy of Selectors * Source                              // Struct | Duplicate edits
  | WrapRecord of id:string * tag:string * target:Selectors // Struct | Add field
  | WrapList of tag:string * target:Selectors               // Struct | Add 'All'
  | UpdateTag of Selectors * string * string                // Struct | Change 'Tag'
  | Delete of Selectors
  | Check of Selectors * Condition

//type RelationalOperator = 
//  | Equals | NotEquals 

//type EditCondition = 
  //| SelectorHashEquals of Selectors * int
  //| Never
//| TagCondition of Selectors * RelationalOperator * string

type Edit = 
  { Kind : EditKind 
//    Conditions : EditCondition list
    //Dependencies : Selectors list
    //IsEvaluated : bool
    //CanDuplicate : bool 
  }

// --------------------------------------------------------------------------------------
// Pretty printing
// --------------------------------------------------------------------------------------

let formatSelector = 
  List.map (function All -> "*" | Tag t -> $"<{t}>" | Index i -> string i | Field f -> f)
  >> List.map (fun s -> "/" + s)
  >> String.concat ""

let formatSource = function 
  | ConstSource(nd) -> sprintf "node(%A)" nd
  | RefSource(sel) -> $"ref({formatSelector sel})"

let formatEdit ed = 
  match ed.Kind with
  | PrimitiveEdit(sel, op) -> $"primitive({formatSelector sel}, op)"
  | ListAppend(sel, src) -> $"listAppend({formatSelector sel}, {formatSource src})"
  | ListReorder(sel, ord) -> $"""listReorder({formatSelector sel}, [{ String.concat "," (List.map string ord) }])"""
  | RecordAdd(sel, n, src) -> $"recordAdd({formatSelector sel}, {n}, {formatSource src})"
  | RecordRenameField(sel, n) -> $"renameField({formatSelector sel}, {n})"
  | Copy(sel, src) -> $"copy({formatSelector sel}, {formatSource src})"
  | WrapRecord(id, tag, sel) -> $"wrapRec({formatSelector sel}, {id}, {tag})"
  | WrapList(tag, sel) -> $"wrapList({formatSelector sel}, {tag})"
  | UpdateTag(sel, tagOld, tagNew) -> $"updateTag({formatSelector sel}, {tagOld} => {tagNew})"
  | Delete(sel) -> $"delete({formatSelector sel})"
  | Check(sel, NonEmpty) -> $"check({formatSelector sel}, not empty)"
  | Check(sel, EqualsTo (String s)) -> $"check({formatSelector sel}, equals {s})"
  | Check(sel, EqualsTo (Number n)) -> $"check({formatSelector sel}, equals {n})"

// --------------------------------------------------------------------------------------
// Merge and apply helpers
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

let getSelectors ed = 
  match ed.Kind with 
  | PrimitiveEdit(s, _) | ListReorder(s, _) | RecordRenameField(s, _) 
  | UpdateTag(s, _, _) | WrapRecord(_, _, s) | WrapList(_, s) | Delete(s) | Check(s, _) -> [s]
  | ListAppend(s, ConstSource nd) | RecordAdd(s, _, ConstSource nd) 
  | Copy(s, ConstSource nd) -> s :: (getNodeSelectors nd)
  | ListAppend(s1, RefSource s2) | RecordAdd(s1, _, RefSource s2) 
  | Copy(s1, RefSource s2) -> [s1; s2]


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
  | PrimitiveEdit(s, _) | ListReorder(s, _) | RecordRenameField(s, _) 
  | UpdateTag(s, _, _) | Copy(s, _) | Delete(s) | Check(s, _) -> s
  | WrapRecord(_, id, s) | RecordAdd(s, id, _) -> s @ [Field id]
  | ListAppend(s, _) | WrapList(_, s) -> s @ [All]

let getTargetSelectorPrefixes eds = 
  let sels = System.Collections.Generic.HashSet<_>()
  for ed in eds do
    let sel = getTargetSelector ed
    for prefix in List.prefixes sel do ignore(sels.Add(prefix))
  List.sort (List.ofSeq sels)

let withTargetSelector tgt ed = 
  let dropLast (tgt:_ list) = tgt.[0 .. tgt.Length - 2] // Remove the last, added in 'getTargetSelector'
  let nkind =
    match ed.Kind with 
    | Delete(_) -> Delete(dropLast tgt)
    | ListAppend(_, nd) -> ListAppend(dropLast tgt, nd) 
    | WrapList(t, _) -> WrapList(t, dropLast tgt) 
    | RecordAdd(_, s, nd) -> RecordAdd(dropLast tgt, s, nd) 
    | WrapRecord(t, i, n) -> WrapRecord(t, i, dropLast tgt) 
    | PrimitiveEdit(_, f) -> PrimitiveEdit(tgt, f)
    | ListReorder(_, m) -> ListReorder(tgt, m)
    | UpdateTag(_, t1, t2) -> UpdateTag(tgt, t1, t2) 
    | RecordRenameField(_, s) -> RecordRenameField(tgt, s) 
    | Copy(_, s) -> Copy(tgt, s)
    | Check(_, cond) -> Check(tgt, cond)
  { ed with Kind = nkind }

let withSelectors sels ed =
  let nkind =
    match ed.Kind with
    | Delete(_) -> Delete(List.exactlyOne sels)
    | ListAppend(_, ConstSource nd) -> ListAppend(List.head sels, ConstSource(withNodeSelectors nd (List.tail sels)))
    | RecordAdd(_, s, ConstSource nd) -> RecordAdd(List.head sels, s, ConstSource(withNodeSelectors nd (List.tail sels)))
    | Copy(_, ConstSource nd) -> Copy(List.head sels, ConstSource(withNodeSelectors nd (List.tail sels)))
    | PrimitiveEdit(_, f) -> PrimitiveEdit(List.exactlyOne sels, f)
    | ListReorder(_, m) -> ListReorder(List.exactlyOne sels, m)
    | WrapRecord(t, f, _) -> WrapRecord(t, f, List.exactlyOne sels) 
    | WrapList(t, _) -> WrapList(t, List.exactlyOne sels) 
    | UpdateTag(_, t1, t2) -> UpdateTag(List.exactlyOne sels, t1, t2) 
    | RecordRenameField(_, s) -> RecordRenameField(List.exactlyOne sels, s) 
    | Copy(_, RefSource _) -> Copy(List.head sels, RefSource (List.exactlyOne (List.tail sels)))
    | ListAppend(_, RefSource _) -> ListAppend(List.head sels, RefSource (List.exactlyOne (List.tail sels)))
    | RecordAdd(_, f, RefSource _) -> RecordAdd(List.head sels, f, RefSource (List.exactlyOne (List.tail sels)))
    | Check(_, cond) -> Check(List.exactlyOne sels, cond)
  { ed with Kind = nkind }

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
    //| Index(i)::p1, All::p2 | All::p1, Index(i)::p2 -> 
        //failwith "removeSelectorPrefix - Index/All - arguably error %"
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
  
//let (|ScopeSelector|_|) selbase sel = 
//  removeSelectorPrefix selbase sel |> Option.map snd

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

let decrementSelectorsAfterDel selDelete selOther = 
  let rec decafter selDelete selOther =
    match selOther, selDelete with 
    | Index(io)::selOther, [Index(id)] -> 
        if io >= id then Index(io - 1)::selOther
        else Index(io)::selOther
    | MatchingFirst(s, selOther, selDelete) -> s::(decafter selDelete selOther)
    | TooSpecific(s) -> failwith $"decrementSelectorsAfterDel - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"decrementSelectorsAfterDel - Missing case: {selOther} vs. {selDelete}"
  decafter selDelete selOther
 
let reorderSelectors ord selOther selReord = 
  // Returns a modified version of 'selOther' to match
  // reordering of indices 'ord' at location specified by 'selReord'
  let rec reorder selOther selReord =
    match selOther, selReord with 
    | Index(io)::selOther, [] -> Index(List.findIndex ((=) io) ord)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(reorder selOther selWrap)
    | TooSpecific(s) -> failwith $"reorderSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther        
    | _ -> failwith $"reorderSelectors - Missing case: {selOther} vs. {selReord}"
  reorder selOther selReord

let wrapRecordSelectors id selOther selWrap =
  // Returns a modified version of 'selOther' to match
  // the additional wrapping (in a record with original at @id) at location specified by 'selWrap'
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> 
        if id = "" then failwith "wrapRecordSelectors - Cannot wrap without an id"
        Field(id)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
    | TooSpecific(s) -> failwith $"wrapRecordSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"wrapRecordSelectors - Missing case: {selOther} vs. {selWrap}"
  wrapsels selOther selWrap
  
let wrapListSelectors selOther selWrap =
  // Returns a modified version of 'selOther' to match
  // the additional wrapping (in a list) at location specified by 'selWrap'
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> All::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
    | TooSpecific(s) -> failwith $"wrapListSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"wrapListSelectors - Missing case: {selOther} vs. {selWrap}"
  wrapsels selOther selWrap

let updateTagSelectors tagOld tagNew selOther selUpd =
  // Returns a modified version of 'selOther' to match
  // the tag rename done at location specified by 'selUpd'
  let rec wrapsels selOther selUpd =
    match selOther, selUpd with 
    | Tag(t)::selOther, [] when t = tagOld -> Tag(tagNew)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selUpd)
    | TooSpecific(s) -> failwith $"updateTagSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"updateTagSelectors - Missing case: {selOther} vs. {selUpd}"
  wrapsels selOther selUpd

let renameFieldSelectors id selOther selReord =
  // Returns a modified version of 'selOther' to match
  // the changed ID at location specified by 'selReord'
  let rec reidsels selOther selReord =
    match selOther, selReord with 
    | Field(fo)::selOther, Field(fr)::[] when fo = fr -> Field(id)::(reidsels selOther []) // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(reidsels selOther selWrap)
    | TooSpecific(s) -> failwith $"renameFieldSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"renameFieldSelectors - Missing case: {selOther} vs. {selReord}"
  reidsels selOther selReord

// --------------------------------------------------------------------------------------
// Apply
// --------------------------------------------------------------------------------------

let rec isStructuralSelector sel = 
  match sel with 
  | [] -> true
  | Index _::_ -> false
  | (All | Tag _ | Field _)::sel -> isStructuralSelector sel

  (*
let enabled doc edit = 
  edit.Conditions |> List.forall (function 
    | SelectorHashEquals(sel, h) -> hash (select sel doc) = h
    | Never -> false
  )
  | TagCondition(sel, rel, t1) -> select sel doc |> List.forall (function
      | { Expression = Record(t2, _, _) } ->
          (rel = Equals && t1 = t2) || (rel = NotEquals && t1 <> t2)        
      | _ -> rel = NotEquals )) // No tag - also passes != check
      *)

exception ConditionCheckFailed of string

let apply doc edit =
  //(fun f -> try f() with e -> printfn "update: Failed for edit '%A'" edit; reraise()) <| fun () -> 
  match edit.Kind with
  //| _ when not (enabled doc edit) ->
    //  doc
  | Check(sel, cond) ->
      match cond, select sel doc with 
      | EqualsTo(String s1), [Primitive(String s2)] -> if s1 <> s2 then raise(ConditionCheckFailed $"apply.Check: EqualsTo failed ({s1}<>{s2})")
      | EqualsTo(Number n1), [Primitive(Number n2)] -> if n1 <> n2 then raise(ConditionCheckFailed $"apply.Check: EqualsTo failed ({n1}<>{n2})")
      | NonEmpty, [Primitive(Number _)] -> ()
      | NonEmpty, [Primitive(String s)] -> if System.String.IsNullOrWhiteSpace(s) then raise(ConditionCheckFailed $"apply.Check: NonEmpty failed ({s})")
      | cond, nd -> raise (ConditionCheckFailed $"apply.Check Condition ({cond}) failed ({nd})")
      doc

  // This may invalidate some selectors, but there is not much we can do
  // (just do this...) but we also need to update indicies in selectors that
  // refer to later items in the affected list (in case the target is a list item)
  | Delete(sel) ->
      let last, sel = match List.rev sel with last::sel -> last, List.rev sel | _ -> failwith "apply.Delete - Expected non-empty selector"
      let doc = replace (fun p el ->
        match el, last with
        | List(t, items), Index(i) when matches p sel -> 
            let items = items |> List.indexed |> List.choose (fun (j, it) -> if i <> j  then Some it else None)
            Some(List(t, items))
        | List(t, _), All when matches p sel -> 
            Some(List(t, []))
        | List(t, items), Tag tdel when matches p sel -> 
            let items = items |> List.filter (function Record(t, _) | List(t, _) when t = tdel -> false | _ -> true)
            Some(List(t, items))
        | Record(t, nds), Field(fdel) when matches p sel ->
            let nds = nds |> List.filter (fun (f, nd) -> f <> fdel)
            Some(Record(t, nds))
        | _ -> None) doc
      // Replace all relevant selectors (in references in code)
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> decrementSelectorsAfterDel sel s1)
      withNodeSelectors doc nsels

  // We can always do this, but it may add new kinds of things to a list
  // This has no effect on any selectors 
  // (But old selectors may not be compatible with the newly added thing!)
  | ListAppend(sel, src) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> 
            let nd = match src with RefSource sel -> selectSingle sel doc | ConstSource nd -> nd
            Some(List(tag, nds @ [nd]))
        | _ -> None ) doc

  // We can always do this, it has no effect on any selectors
  | PrimitiveEdit(sel, f) ->
      replace (fun p el -> 
        match el with 
        | Primitive(v) when matches p sel -> Some(Primitive(transformationsLookup.[f] v))
        | _ -> None ) doc

  // We can always do this.
  // We need to update 'Index' selectors in code refs 
  // (this logic is mirrored below in 'updateSelectors', called when merging)
  | ListReorder(sel, ord) ->
      // Do the actual reordering 
      let doc = replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> Some(List(tag, [ for i in ord -> nds.[i]]))
        | _ -> None ) doc
      // Replace all relevant selectors (in references in code)
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> reorderSelectors ord s1 sel)
      withNodeSelectors doc nsels

  // Changes structure, so only do this if selector is not value-specific
  // We need to wrap selectors in code refs 
  // (dtto.)
  | WrapRecord(id, tag, sel) ->
      //if not (isStructuralSelector sel) then failwith $"apply.WrapRecord - Maybe allow, but do not update refs? WrapRecord with non-structural selector {sel}"
      // Do the actual record wrapping
      let doc = replace (fun p el -> 
        if matches p sel then Some(Record(tag, [id, el]))
        else None ) doc
      // Replace all relevant selectors (in references in code)
      // if notupd then doc else
      if isStructuralSelector sel then
        let nsels = getNodeSelectors doc |> List.map (fun s1 -> wrapRecordSelectors id s1 sel)
        withNodeSelectors doc nsels
      else 
        doc

  // Changes structure, so only do this if selector is not value-specific
  // We need to wrap selectors in code refs 
  // (dtto.)
  | WrapList(tag, sel) ->
      // TODO: Do the same as with WrapRecord? 
      //if not (isStructuralSelector sel) then failwith $"apply.WrapList - Maybe allow, but do not update refs? WrapList with non-structural selector {sel}"
      // Do the actual record wrapping
      let doc = replace (fun p el -> 
        if matches p sel then Some(List(tag, [el]))
        else None ) doc
      // Replace all relevant selectors (in references in code)
      // if notupd then doc else
      if isStructuralSelector sel then
        let nsels = getNodeSelectors doc |> List.map (fun s1 -> wrapListSelectors s1 sel)
        withNodeSelectors doc nsels
      else 
        doc
    
  // Changes structure, so only do this if selector is not value-specific
  // We need to update selectors in code refs  (but this is a bit experimental - changes only 'Tag' refs for lists...)
  // (dtto.)
  | UpdateTag(sel, tagOld, tagNew) ->
      if not (isStructuralSelector sel) then failwith $"apply.UpdateTag - Maybe allow, but do not update refs? UpdateTag with non-structural selector {sel}"
      let doc = replace (fun p el ->
        match el with 
        | Record(t, nds) when matches p sel && t = tagOld -> Some(Record(tagNew, nds))
        | List(t, nds) when matches p sel && t = tagOld -> Some(List(tagNew, nds))
        | _ -> None ) doc
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> updateTagSelectors tagOld tagNew s1 sel)
      withNodeSelectors doc nsels

  // Changes structure, so only do this if selector is not value-specific
  // We need to update selectors in code refs  (replace field name)
  // (dtto.)
  | RecordRenameField(sel, id) ->
      if not (isStructuralSelector sel) then failwith $"apply.RecordRenameField - Maybe allow, but do not update refs? RecordRenameField with non-structural selector {sel}"
      let doc = replaceField (fun p el -> 
        if matches p sel then Some(id, el) else None) doc
      // Replace all relevant selectors (in references in code)
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> renameFieldSelectors id s1 sel)
      withNodeSelectors doc nsels

  // Changes structure, so only do this if selector is not value-specific
  // Additive so no need to update references
  | RecordAdd(sel, fld, src) ->
      // NOTE: Allowing this, otherwise we cannot construct a list of formulas!
      // (but the operation creates a heterogeneous list temporarily...)
      //
      // if not (isStructuralSelector sel) then failwith $"apply.RecordAdd - Maybe allow, but do not update refs? RecordAdd  with non-structural selector {sel}"
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> 
            let nds = nds |> List.filter (fun (k, _) -> k <> fld)
            let nd = match src with RefSource sel -> selectSingle sel doc | ConstSource nd -> nd
            Some(Record(tag, nds @ [fld, nd]))
        | _ -> None ) doc

(*
  // Changes structure, so only do this if selector is not value-specific
  // Could in principle break references pointing to the replaced thing
  // (but we have no fix)
  | Replace(sel, nd) ->
      if not (isStructuralSelector sel) then
        // NOTE: As in copy - this potentially changes the structure of the target list
        // but we need to allow this so that we can evaluate lists of formulas!
        ()
        //failwith $"apply.Replace - Maybe allow, but do not update refs? Replace  with non-structural selector {sel}"
      replace (fun p el -> 
        if matches p sel then Some(nd)
        else None ) doc
*)

  // May change structure
  // What should we do if there are selectors in the doc pointing to the copied source?
  // (duplicate something? this makes no good sense...)
  | Copy(sel, src) ->
      if not (isStructuralSelector sel) then 
        ()
        // NOTE: As below - this potentially changes the structure of the target list
        // but we need to allow this so that we can evaluate lists of formulas!
        // failwith $"apply.Copy - Maybe allow, but potentially changes structure"
      let codeRefExists = 
        match src with RefSource selSrc -> getNodeSelectors doc |> List.exists (includes selSrc) | _ -> false
      if codeRefExists then 
        // NOTE: What to do if there are refs to the source in the document?
        // For now, allow, because we need to allow this for "transient" evaluated edits!
        () //failwith "apply.Copy - Maybe allow, but there are refs to the source"

      let exprs = 
        let srcNodes = match src with ConstSource nd -> [nd] | RefSource s -> select s doc
        match select sel doc with         
        | tgs when tgs.Length = srcNodes.Length -> srcNodes

            // NOTE: This is a bit too clever (if there is one target, it 
            // implicitly creates list with all source nodes to be copied there)
            // NOTE: In the conf organizer, we had /$builtins/count(arg=/speakers/*)
            // which refers to multiple nodes - copying that into a single node required
            // evil magic - but we can just refer to /speakers/ directly.
            // 
            // printfn $"TGTSEL={sel2}, TARGETS={tgt}, SOURCES={nds.Length}"
            //
            // But the above does not work for computing the totals where we need
            // to select /totals/*/item/formula - so
            // perhaps this is ok if the target to be copied into is a list???
            //
            // "splice" values into the parent list
            
            (*
            match List.rev sel2 with 
            | Index _::sel2par ->
                let sel2mod = List.rev sel2par
                match select sel2mod doc with
                | [List(t, _)] ->
                    sel2mod, [ List(t, nds) ]
                | tgt ->
                    failwith $"apply.Copy - Tried to be too clever, but no list here = {tgt}"
            | _ ->
              *)
        | [List(t, _)] -> [List(t, srcNodes)]
        | [tgt] -> 
            failwith $"apply.Copy - Be too clever and autowrap target?? target={formatSelector sel}, source={src}"; 
        | _ -> failwith "apply.Copy - Mismatching number of source and target notes"

      let mutable exprs = exprs
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy - Unexpected"
      replace (fun p el -> 
        if matches p sel then Some(next())
        else None ) doc


// --------------------------------------------------------------------------------------
// Merge
// --------------------------------------------------------------------------------------

let rec substituteWithMoreSpecific specPrefix sels = 
  match specPrefix, sels with
  | Field(f1)::specPrefix, Field(f2)::sels when f1 = f2 -> Field(f1)::(substituteWithMoreSpecific specPrefix sels)
  | Index(i1)::specPrefix, Index(i2)::sels when i1 = i2 -> Index(i1)::(substituteWithMoreSpecific specPrefix sels)
  | All::specPrefix, Index(i1)::sels 
  | Index(i1)::specPrefix, All::sels -> Index(i1)::(substituteWithMoreSpecific specPrefix sels)
  | All::specPrefix, All::sels -> All::(substituteWithMoreSpecific specPrefix sels)
  | _ -> sels  // Not matching, but that's OK, we only want to subsitute prefix
 
let copyEdit e1 srcSel tgtSel = 
  // For cases when the copied thing is directly the target of the edit 'e1'
  let e1tgtSel = getTargetSelector e1
  if e1tgtSel = srcSel then 
    Some [e1; withTargetSelector tgtSel e1]
  else
  // For cases when the edit 'e1' targets something inside the copied (from srcSel to tgtSel)
  let origSels = getSelectors e1 
  let newSels = origSels |> List.map (fun sel ->
    //printfn $"COPY EDIT {srcSel}, {sel}"
    match removeSelectorPrefix srcSel sel with 
    | Some(specPrefix, suffix) -> 
        tgtSel @ suffix |> substituteWithMoreSpecific specPrefix
    | _ -> sel)
  if origSels = newSels then None
  else 
    Some [e1; withSelectors newSels e1]
  
/// Returns [e1;e1'] with modified (possibly duplicated) edits
let updateSelectors e1 e2 = 
  //printfn "Update selectors in %A based on %A" (formatEdit e1) (formatEdit e2)
  //(fun res -> printfn "  returning %A" [List.map formatEdit res]; res) <|
  match e2.Kind with 
  // Similar selector update is also applied when editing existing document!
  // (this logic is mirrored below in 'apply' called when applying edit)
  // [REMOVED] Edits creating code are for now typically marked 'CanDuplicate=false' so the 
  // logic for 'Copy' is not duplicated above.
  | ListReorder(sel, ord) -> 
      // TODO: If e1 is itself ListReorder pointing to the same thing.. do something clever?
      let nsels = getSelectors e1 |> List.map (fun s1 -> reorderSelectors ord s1 sel)
      [withSelectors nsels e1]
  | Delete(sel) ->
      let nsels = getSelectors e1 |> List.map (fun s1 -> decrementSelectorsAfterDel sel s1)
      [withSelectors nsels e1]
  | WrapRecord(id, tag, sel) -> 
      let nsels = getSelectors e1 |> List.map (fun s1 -> wrapRecordSelectors id s1 sel)
      [withSelectors nsels e1]
  | WrapList(tag, sel) -> 
      let nsels = getSelectors e1 |> List.map (fun s1 -> wrapListSelectors s1 sel)
      [withSelectors nsels e1]
  | UpdateTag(sel, t1, t2) ->
      let nsels = getSelectors e1 |> List.map (fun s1 -> updateTagSelectors t1 t2 s1 sel)
      [withSelectors nsels e1]
  | RecordRenameField(sel, id) ->
      let nsels = getSelectors e1 |> List.map (fun s1 -> renameFieldSelectors id s1 sel)
      [withSelectors nsels e1]
  | Copy(tgtSel, RefSource srcSel) -> 
      match copyEdit e1 srcSel tgtSel with 
      | Some res -> res // when e1.CanDuplicate -> res
      | _ ->
          let target = getTargetSelector e1
          let conflict = removeSelectorPrefix srcSel target |> Option.isSome
          //if conflict && e2.IsEvaluated then failwith $"CONFLICT (but isEvaluated=true)!!!\ne1={e1}\ne2={e2}"
          //else
          if conflict then failwith $"CONFLICT!!!\ne1={e1}\ne2={e2}"
          else [e1]
    
  | Copy(_, ConstSource _) // TODO: Think about this
  | Check _
  // TODO: EVALUATION?
  | Delete _
  | UpdateTag _
  | RecordAdd _
  | PrimitiveEdit _ 
  | ListAppend _ ->
      [e1]

/// If the 'edit' is to something with a prefix specified by the selector 'selbase',
/// returns new edit that is relatively to the subtree specified by selbase 
let tryMapSelectors f edit = 
  let sels = getSelectors edit 
  let nsels = sels |> List.choose f
  if nsels.Length = 0 then None
  elif nsels.Length = sels.Length then Some(withSelectors nsels edit)
  else failwith $"tryMapSelectors - some selectors scoped, but some not. Think about this. Edit: {formatEdit edit}"

let scopeEdit oldBase newBase edit = 
  edit |> tryMapSelectors (fun s -> 
    match removeSelectorPrefix oldBase s with 
    | Some(_, sel) -> Some(newBase @ sel)
    | _ -> None)

  // The above should be the same as the original implementation below
  // with the difference that it also looks at selectors inside added nodes
  // (getDependenciesSelectors does not do this, but it's commented out)

(*
  let ret ed = Some { Kind = ed }
  match edit.Kind with 
  | ListAppend(ScopeSelector selBase sel, src) -> ret (ListAppend(sel, src))
  | PrimitiveEdit(ScopeSelector selBase sel, f) -> ret (PrimitiveEdit(sel, f))
  | ListReorder(ScopeSelector selBase sel, p) -> ret (ListReorder(sel, p))
  | WrapRecord(id, tag, ScopeSelector selBase sel) -> ret (WrapRecord(id, tag, sel))
  | RecordAdd(ScopeSelector selBase sel, fld, src) -> ret (RecordAdd(sel, fld, src))
  | UpdateTag(ScopeSelector selBase sel, t1, t2) -> ret (UpdateTag(sel, t1, t2))
  | RecordRenameField(ScopeSelector selBase sel, t) -> ret (RecordRenameField(sel, t))
  | Copy(ScopeSelector selBase sel, ConstSource nd) -> ret (Copy(sel, ConstSource nd)) 
  | Copy(ScopeSelector selBase s1, RefSource(ScopeSelector selBase s2)) -> ret (Copy(s1, RefSource s2))
  | Copy(s1, RefSource s2) -> 
      match removeSelectorPrefix selBase s1, removeSelectorPrefix selBase s2 with
      | None, None -> 
          // Both are source and target of the copy are outside of the location 
          // where we are adding something, so we can happily skip the Copy edit
          None
      | _ ->
        failwith $"scopeEdit.Copy - non-local copy - need to think about this one: BASE={selBase}, EDIT={edit}"
  
  | _ -> None
  *)
let applyToAdded e1 e2 = 
  match e1.Kind with 
  | ListAppend(sel, RefSource src) -> 
      
      match scopeEdit (sel @ [All]) src e2 with
      | Some e2scoped ->
          printfn "append %s from %s" (formatSelector sel) (formatSelector src)
          printfn "apply %A" (formatEdit e2)
          printfn " *** scoped %s" (formatEdit e2scoped)
          [e2scoped; e1]
          //e1
      | _ -> [e1]

  | ListAppend(sel, ConstSource nd) -> 
      // We are appending under 'sel', so the selector for 
      // the node 'nd' itself will be 'sel; All' (for added field, this needs the field name)
      match scopeEdit (sel @ [All]) [] e2 with
      | Some e2scoped ->
          //printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          [ { e1 with Kind = ListAppend(sel, ConstSource (apply nd e2scoped)) } ]
      | None -> [ e1 ]

  | RecordAdd(sel, fld, ConstSource nd) -> 
      // TODO: Untested. Also maybe this assumes nd.ID <> ""
      match scopeEdit (sel @ [Field fld]) [] e2 with
      | Some e2scoped ->
          //printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          [ { e1 with Kind = RecordAdd(sel, fld, ConstSource(apply nd e2scoped)) } ]
      | None -> [ e1 ]

  | Copy(_, ConstSource _) -> failwith "applyToAdded - Replace TODO"
  | _ -> [ e1 ]

// Assuming 'e1' and 'e2' happened independently,
// modify 'e1' so that it can be placed after 'e2'.
let moveBefore e1 e2 = 
  //printfn "MOVE BEFORE"
  //printfn "move => %A" e1.Kind
  //printfn "beore => %A" e2.Kind
  let e1 = applyToAdded e1 e2
  let e1 = e1 |> List.collect (fun e1 -> updateSelectors e1 e2)
  e1
  
(*
let merge e1s e2s = 
  let rec loop acc e1s e2s =
    match e1s, e2s with 
    | e1::e1s, e2::e2s when e1 = e2 -> 
        // Collect shared edits until the two histories diverge
        loop (e1::acc) e1s e2s
    | e1s, e2s ->
    (*
        // We want to modify 'e2' edits so that they can be placed after 'e1'
        // If edits in 'e2' conflict with "evaluation" edits in 'e1', remove those
        //printfn $"MERGEING! Target selectors={e2s |> List.map getTargetSelector}"
        let mutable tgtSels = e2s |> List.map getTargetSelector |> Set.ofSeq
        let e1s = e1s |> List.map (fun e1 ->
          //if not e1.IsEvaluated then true else
            let sels = getDependenciesSelectors e1
            let affected = sels |> Seq.exists (fun sel -> 
              tgtSels |> Set.exists (fun tgtSel -> Option.isSome (removeSelectorPrefix tgtSel sel)))
            if affected then 
              //printfn $"AFFECTED - {e1}"
              //printfn $"AFFECTED - target selector {getTargetSelector e1}"
              tgtSels <- tgtSels.Add(getTargetSelector e1)
              { e1 with Conditions = e1.Conditions @ [Never] }
            else 
              //printfn $"FINE - {e1}"
              e1 )
      *)  
        let e2sAfter = 
          e2s |> List.collect (fun e2 ->
              // For a given edit 'e2', move it before all the edits in 'e1s' using 'moveBefore'
              // (caveat is that the operation can turn it into multiple edits)
              List.fold (fun e2 e1 -> 
                e2 |> List.collect (fun e2 -> moveBefore e2 e1)) [e2] e1s )         

        (List.rev acc) @ e1s @ e2sAfter

  loop [] e1s e2s 
*)

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
  let e2sAfter = 
    e2s |> List.collectNested (fun e2 ->
        // For a given edit 'e2', move it before all the edits in 'e1s' using 'moveBefore'
        // (caveat is that the operation can turn it into multiple edits)
        List.foldNested (fun e2 e1 -> 
          //printfn "Moving %A before %s" (List.map formatEdit e2) (formatEdit e1)
          e2 |> List.collect (fun e2 -> moveBefore e2 e1)) [e2] e1s )         
  //printfn "MERGE HISTORIES"
  //printfn "Before transform: %A" (List.mapNested formatEdit e2s)
  //printfn "After transform: %A" (List.mapNested formatEdit e2sAfter)
  { Groups = shared @ e1s @ e2sAfter }



// --------------------------------------------------------------------------------------
// Representing edits as nodes
// --------------------------------------------------------------------------------------

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
  
let (|Lookup|) args = dict args
let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  if d.ContainsKey k then Some(d.[k]) else None
let (|Finds|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(String s) -> Some s | _ -> None
let rcd id kvp = Record(id, kvp)

let unrepresentIntList nd =
  match nd with 
  | List("x-int-list", nds) ->
      List.map (function Primitive(Number n) -> int n | _ -> failwith "unrepresentIntList - Not a number") nds
  | _ -> failwith $"unrepresentIntList - Invalid node {nd}"

let unrepresentSrc nd = 
  match nd with 
  | Record("x-src-node", Lookup(Find "const" nd)) -> ConstSource(nd)
  | Record("x-src-ref", Lookup(Find "selector" nd)) -> RefSource(unrepresentSel nd)
  | _ -> failwith $"unrepresentSrc - Invalid node {nd}"

let unrepresentCond nd = 
  match nd with 
  | Record("x-cond-equals", Lookup(Find "node" (Primitive v))) -> EqualsTo(v)
  | Record("x-cond-nonempty", []) -> NonEmpty
  | _ -> failwith $"unrepresentCond - Invalid node {nd}"

let unrepresent nd = 
  let editKind =
    match nd with
    | Record("x-edit-wraprec", Lookup(Finds "tag" tag & Finds "id" id & Find "target" target)) ->
        EditKind.WrapRecord(tag, id, unrepresentSel target)
    | Record("x-edit-append", Lookup (Find "target" sel & Find "src" src)) ->
        EditKind.ListAppend(unrepresentSel sel, unrepresentSrc src)
    | Record("x-edit-add", Lookup (Find "target" sel & Finds "field" f & Find "src" src)) ->
        EditKind.RecordAdd(unrepresentSel sel, f, unrepresentSrc src)
    | Record("x-edit-updateid", Lookup (Find "target" sel & Finds "id" id)) ->
        EditKind.RecordRenameField(unrepresentSel sel, id) 
    | Record("x-edit-copy", Lookup (Find "target" tgt & Find "src" src)) ->
        EditKind.Copy(unrepresentSel tgt, unrepresentSrc src) 
    | Record("x-edit-delete", Lookup (Find "target" tgt)) ->
        EditKind.Delete(unrepresentSel tgt) 
    | Record("x-check", Lookup (Find "target" tgt & Find "cond" cond)) ->
        EditKind.Check(unrepresentSel tgt, unrepresentCond cond) 
    | Record("x-wrap-list", Lookup (Find "target" tgt & Finds "tag" tag)) ->
        EditKind.WrapList(tag, unrepresentSel tgt) 
    | Record("x-primitive-edit", Lookup (Find "target" tgt & Finds "op" op)) ->
        EditKind.PrimitiveEdit(unrepresentSel tgt, op) 
    | Record("x-list-reorder", Lookup (Find "target" tgt & Find "perm" perm)) ->
        EditKind.ListReorder(unrepresentSel tgt, unrepresentIntList perm) 
    | Record("x-update-tag", Lookup (Find "target" tgt & Finds "old" otag & Finds "new" ntag)) ->
        EditKind.UpdateTag(unrepresentSel tgt, otag, ntag) 
    | _ -> failwith $"unrepresent - Missing case for: {nd}"  
  { Kind = editKind }

let representIntList ns =
  List("x-int-list", [for n in ns -> Primitive(Number(float n)) ])

let representSrc src = 
  match src with 
  | ConstSource(nd) -> [ "const", nd ] |> rcd "x-src-node"
  | RefSource(sel) -> [ "selector", representSel sel ] |> rcd "x-src-ref"

let representCond cond = 
  match cond with 
  | EqualsTo(nd) -> [ "node", Primitive nd ] |> rcd "x-cond-equals"
  | NonEmpty -> [] |> rcd "x-cond-nonempty"

let represent op = 
  let ps v = Primitive(String v)
  match op.Kind with 
  | EditKind.WrapRecord(tag, id, target) ->
      rcd "x-edit-wraprec" [ "tag", ps tag; "id", ps id; "target", representSel target ] 
  | EditKind.ListAppend(target, src) ->
      rcd "x-edit-append" [ "target", representSel target; "src", representSrc src ]
  | EditKind.RecordAdd(target, f, src) ->
      rcd "x-edit-add" [ "target", representSel target; "field", ps f; "src", representSrc src ]
  | EditKind.RecordRenameField(target, id) ->
      rcd "x-edit-updateid" [ "target", representSel target; "id", ps id ]
  | EditKind.Copy(target, source) ->
      rcd "x-edit-copy" [ "target", representSel target; "src", representSrc source ]
  | EditKind.Delete(target) ->
      rcd "x-edit-delete" [ "target", representSel target ]
  | EditKind.Check(target, cond) -> 
      rcd "x-check" [ "target", representSel target; "cond", representCond cond ]
  | EditKind.WrapList(tag, target) ->
      rcd "x-wrap-list" [ "target", representSel target; "tag", ps tag ]
  | EditKind.PrimitiveEdit(target, op) ->
      rcd "x-primitive-edit" [ "target", representSel target; "op", ps op ]
  | EditKind.ListReorder(target, perm) ->
      rcd "x-list-reorder" [ "target", representSel target; "perm", representIntList perm ]
  | EditKind.UpdateTag(target, otag, ntag) ->
      rcd "x-update-tag" [ "target", representSel target; "old", ps otag; "new", ps ntag ]

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

let rec evalSiteRecordChildren inFormula sels nds =
  let rec loop i = function 
    | (f, nd)::nds -> 
        match evalSite inFormula (Field f::sels) nd with 
        | Some res -> Some res
        | None -> loop (i + 1) nds
    | _ -> None
  loop 0 nds 

and evalSiteListChildren inFormula sels nds =
  let rec loop i = function 
    | nd::nds -> 
        match evalSite inFormula (Index i::sels) nd with 
        | Some res -> Some res
        | None -> loop (i + 1) nds
    | _ -> None
  loop 0 nds 

and (|EvalSiteRecordChildren|_|) inFormula sels nds = 
  evalSiteRecordChildren inFormula sels nds

and (|EvalSiteListChildren|_|) inFormula sels nds = 
  evalSiteListChildren inFormula sels nds

/// Evaluate references only if they are inside formula
/// (they may be used for other things in the document, e.g. event handlers)
and evalSite inFormula sels nd : option<Selectors> =
  match nd with 
  | Primitive _ | Reference(Field "$builtins"::_) -> None
  | Reference(p) when inFormula -> Some (List.rev sels)
  | Reference _ -> None
  | Record("x-evaluated", _) -> None
  | Record("x-formula", EvalSiteRecordChildren true sels res) -> Some res // Call by value - evaluate children first
  | Record("x-formula", _) -> Some(List.rev sels)
  | Record(_, EvalSiteRecordChildren false sels res) -> Some res
  | List(_, EvalSiteListChildren false sels res) -> Some res
  | List _ | Record _ -> None

let (|Args|) args = 
  let args = Map.ofSeq args
  args.["op"], args

let (|ListFind|_|) k = List.tryFind (fst >> (=) k) >> Option.map snd

let evaluateRaw doc =
  match evalSite false [] doc with
  | None -> []
  | Some sels ->
      let it = match select sels doc with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sels}\n Resulted in {nds}"
      match it with 
      | Reference(p) -> 
          [ //Copy(p, sels), [TagCondition(p, NotEquals, "x-evaluated")], [p]
            //Copy(p @ [Field "result"], sels), [TagCondition(p, Equals, "x-evaluated")], [p @ [Field "result"]] 
            WrapRecord("ref", "x-evaluated", sels)
            RecordAdd(sels, "result", ConstSource(List("ul", [])))
            Copy(sels @ [Field "result"], RefSource p) //, [SelectorHashEquals(p, hash (select p doc))]
            

            ]
      | Record("x-formula", Args(Reference [ Field("$builtins"); Field op ], args)) ->
          // Used previously for dependencies - now not needed
          // let ss = args.Keys |> Seq.map (fun k -> sels @ [Field k]) |> List.ofSeq

          let args = args |> Map.map (fun _ v ->
            match v with 
            | Record("x-evaluated", ListFind "result" r) -> r
            | _ -> v
          )

          let res = 
            match op with 
            | "count" | "sum" ->
                let sum = List.map (function Primitive(Number n) -> n | _ -> failwith "evaluate: Argument of 'sum' is not a number.") >> List.sum 
                let count = List.length >> float
                let f = (dict [ "count", count; "sum", sum ]).[op]
                match args.TryFind "arg" with
                | Some(List(_, nds)) -> 
                     Primitive(Number(f nds))
                | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."
            | "+" | "*" -> 
                let f = (dict [ "+",(+); "*",(*) ]).[op]
                match args.TryFind "left", args.TryFind "right" with
                | Some(Primitive(Number n1)),
                  Some(Primitive(Number n2)) -> 
                    Primitive(Number(f n1 n2))
                | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
            | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"      
            
          //printfn "wrap %A" sels
          [ Copy(sels, ConstSource res) ]//, [] ]  // Dependencies = ss
          (*
          [ WrapRecord("result", "x-evaluated", Object, sels, true), [], ss
            ListAppend(sels, { ID = "previous"; Expression = Primitive(String "na") }), [], ss
            Copy(sels @ [Field "result"], sels @ [Field "previous"]), [], ss
            Replace(sels @ [Field "result"], { ID = "result"; Expression = res } ), [], ss
            ] *)
      | Record("x-formula", nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for f, _ in nds -> f]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it}"

let evaluateDoc doc =
  let eds = 
    [ for ed(*, conds, deps *) in evaluateRaw doc -> 
        //{ CanDuplicate = false; IsEvaluated = true; Kind = ed; Conditions = conds; Dependencies = deps } ]
        { Kind = ed } ]
  { Groups = [eds] }

let evaluateAll doc = 
  let rec loop doc = seq {
    let edits = evaluateDoc doc
    yield! edits.Groups
    let ndoc = applyHistory doc edits 
    if doc <> ndoc then yield! loop ndoc }
  { Groups = List.ofSeq (loop doc) }
