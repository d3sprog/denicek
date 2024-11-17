module Tbd.Doc
open Tbd
open Tbd.Parsec
open Tbd.Parsec.Operators

type Selector = 
  // Applicable to lists only
  | All
  | Index of string
  // Applicable to records only
  | Field of string
  // Only used for relative references, should be gone
  // by the time we want to do anything useful with this
  | DotDot

type Selectors = Selector list

type Primitive =
  | Number of float
  | String of string

type ReferenceKind = Absolute | Relative

type Node = 
  | Record of string * list<string * Node>
  | List of string * list<string * Node>
  | Primitive of Primitive
  | Reference of ReferenceKind * Selectors

type Transformation = { Key : string; Label : string; Function : string option * Primitive -> Primitive; Args : Parser<string option> }

let transformations = 
  [ { Key = "take-first"; Label = "Take first letter of a string"; Args = P.unit None
      Function = function _, String s -> String(s.Substring(0, 1)) | _, p -> p }
    { Key = "skip-first"; Label = "Skip first letter of a string"; Args = P.unit None
      Function = function _, String s -> String(s.Substring(1)) | _, p -> p }
    { Key = "before-comma"; Label = "Take substring before comma"; Args = P.unit None
      Function = function _, String s when s.Contains(",") -> String(s.Substring(0, s.IndexOf(","))) | _, p -> p }
    { Key = "after-comma"; Label = "Take substring after comma"; Args = P.unit None
      Function = function _, String s when s.Contains(",") -> String(s.Substring(s.IndexOf(",")+1)) | _, p -> p }
    { Key = "upper"; Label = "Turn string into uppercase"; Args = P.unit None
      Function = function _, String s -> String(s.ToUpper()) | _, p -> p }
    { Key = "lower"; Label = "Turn string into lowercase"; Args = P.unit None
      Function = function _, String s -> String(s.ToLower()) | _, p -> p }
    { Key = "replace"; Label = "Replace substring using"; 
      Args = P.char ' ' <*>> P.hole "old" P.nonSlash <<*> P.char '/' <*> P.hole "new" P.nonSlash |> P.map (fun (o, n) -> Some(o + "/" + n))
      Function = function Some repl, String s -> (let parts = repl.Split('/') in String(s.Replace(parts.[0], parts.[1]))) | _, p -> p }
  ]

let transformationsLookup = System.Collections.Generic.Dictionary<_, _>() 
for t in transformations do transformationsLookup.[t.Key] <- t.Function

// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------

let resolveReference baseSels (kind, ref) = 
  let rec normalize acc sel = 
    match sel, acc with 
    | DotDot::sel, _::acc -> normalize acc sel
    | DotDot::_, [] -> failwith "resolveReference: Reference to outside of document!"
    | s::sel, _ -> normalize (s::acc) sel
    | [], _ -> List.rev acc
  if kind = Relative then normalize [] (baseSels @ ref)
  else normalize [] ref

let replace f nd = 
  let rec loop path nd =
    match f path nd with 
    | Some res -> res
    | _ -> 
    match nd with 
    | List(tag, nds) -> 
        List(tag, nds |> List.map (fun (n, nd) -> n, loop (path @ [Index n]) nd))
    | Record(tag, nds) -> 
        Record(tag, nds |> List.map (fun (n, nd) -> n, loop (path @ [Field n]) nd))
    | Reference _ | Primitive _ -> nd 
  loop [] nd

let fold f st value = 
  let rec loop path st nd =
    let st = f path nd st 
    match nd with 
    | List(_, nds) -> 
        nds |> List.fold (fun st (n, nd) -> loop (path @ [Index n]) st nd) st
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
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> matches p1 p2
  | _ -> false

/// Is 'p1' prefix of 'p2' 
let rec includes p1 p2 = 
  match p1, p2 with 
  | [], _ -> true
  | _, [] -> false
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && includes p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && includes p1 p2
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> includes p1 p2
  | _ -> false

/// Is 'p1' prefix of 'p2' 
/// (unlike 'includes', this does not match if p1=/123 and p2=/*)
let rec includesStrict p1 p2 = 
  match p1, p2 with 
  | [], _ -> true
  | _, [] -> false
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && includesStrict p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && includesStrict p1 p2
  | All::p1, Index(_)::p2 -> includesStrict p1 p2
  | _ -> false

let includesReference p1 (p2base, p2ref) =
  includes p1 (resolveReference p2base p2ref)

let select sel doc = 
  doc |> fold (fun p value st -> 
    if matches sel p then value::st else st) [] |> List.rev

let trace sel doc = 
  let rec loop trace sel nd = seq {
    match nd, sel with 
    | nd, [] -> yield nd, List.rev trace
    | List(_, els), All::sel -> 
        for _, el in els do yield! loop ((nd, All)::trace) sel el
    | List(_, els), (Index(n) as s)::sel -> 
        for _, ch in List.filter (fst >> (=) n) els do
          yield! loop ((nd, s)::trace) sel ch
    | Record(_, els), (Field(n) as s)::sel -> 
        for _, ch in List.filter (fst >> (=) n) els do
          yield! loop ((nd, s)::trace) sel ch
    | _ -> ()  }
  loop [] sel doc 

/// Generates a list of selectors where each 'All' 
/// is replaced with all possible 'Index' values.
let expandWildcards sel doc = 
  let rec loop acc sel nd = 
    match nd, sel with 
    | _, [] -> List.map List.rev acc
    | Record(_, els), (Field(n) as s)::sel -> 
        loop (List.map (fun acc -> s::acc) acc) sel (snd (List.find (fst >> (=) n) els))
    | List(_, els), (Index(n) as s)::sel -> 
        loop (List.map (fun acc -> s::acc) acc) sel (snd (List.find (fst >> (=) n) els))
    | List(_, els), All::sel -> 
        List.concat [
          for n, nd in els do
            loop (List.map (fun acc -> (Index n)::acc) acc) sel nd ]
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

type ReferenceBehaviour = 
  | UpdateReferences
  | KeepReferences

type EditKind = 
  // Edits that can affect references in document
  | RecordRenameField of ReferenceBehaviour * Selectors * string * string
  | Copy of ReferenceBehaviour * Selectors * Selectors
  | WrapRecord of ReferenceBehaviour * id:string * tag:string * target:Selectors
  | WrapList of ReferenceBehaviour * id:string * tag:string * target:Selectors
  | RecordDelete of ReferenceBehaviour * Selectors * string
  // Edits that cannot affect references in document
  | ListReorder of Selectors * list<string>
  | ListDelete of Selectors * string
  | ListAppend of Selectors * string * Node
  | ListAppendFrom of Selectors * string * Selectors
  | UpdateTag of Selectors * string
  | PrimitiveEdit of Selectors * string * string option
  | RecordAdd of Selectors * string * Node
  | Check of Selectors * Condition

type Edit = 
  { Kind : EditKind 
    GroupLabel : string
    Dependencies : Selectors list
    Disabled : bool }

// --------------------------------------------------------------------------------------
// Pretty printing
// --------------------------------------------------------------------------------------

let formatSelector = 
  List.map (function 
    | All -> "*" | DotDot -> ".." | Index i -> "#" + i | Field f -> f)
  >> String.concat "/"

let formatReference (kind, sel) =
  (if kind = Relative then "./" else "/") + formatSelector sel

let formatNode nd = 
  sprintf "%A" nd
  
let formatReferenceBehaviour = function
  | UpdateReferences -> "v" | KeepReferences -> "s"

let formatString (s:string) = 
  "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""

let formatEdit ed = 
  let fmt kvd kind args = $"""{formatReferenceBehaviour kind}.{kvd}({ String.concat "," args })"""
  let fmtv kvd args = $"""{kvd}({ String.concat "," args })"""
  match ed.Kind with
  | PrimitiveEdit(sel, op, None) -> 
      fmtv "primitive" [formatSelector sel; formatString op]
  | PrimitiveEdit(sel, op, Some arg) -> 
      fmtv "primitive" [formatSelector sel; formatString op; formatString arg]
  | RecordAdd(sel, n, nd) -> 
      fmtv "recordAdd" [formatSelector sel; formatString n; formatNode nd]
  | Check(sel, NonEmpty) -> 
      fmtv "check" [formatSelector sel; "nonempty"]
  | Check(sel, EqualsTo (String s)) -> 
      fmtv "check" [formatSelector sel; "equals"; formatString s]
  | Check(sel, EqualsTo (Number n)) -> 
      fmtv "check" [formatSelector sel; "equals"; string n]
  | UpdateTag(sel, tagNew) -> 
      fmtv "updateTag" [formatSelector sel; formatString tagNew]
  | ListAppend(sel, n,nd) -> 
      fmtv "listAppend" [formatSelector sel; formatString n; formatNode nd]
  | ListAppendFrom(sel, n, src) -> 
      fmtv "appendFrom" [formatSelector sel; formatString n; formatSelector src]
  | ListReorder(sel, ord) -> 
      fmtv "listReorder" [formatSelector sel; $"""[{ String.concat "," (List.map string ord) }])"""]
  | ListDelete(sel, i) -> 
      fmtv "listDelete" [formatSelector sel; string i]
  | RecordRenameField(rb, sel, o, n) -> 
      fmt "renameField" rb [formatSelector sel; formatString o; formatString n]
  | Copy(rb, sel, src) -> 
      fmt "copy" rb [formatSelector sel; formatSelector src]
  | WrapRecord(rb, id, tag, sel) -> 
      fmt "wrapRec" rb [formatSelector sel; formatString id; formatString tag]
  | WrapList(rb, id, tag, sel) -> 
      fmt "wrapList" rb [formatSelector sel; formatString id; formatString tag]
  | RecordDelete(rb, sel, f) -> 
      fmt "recordDelete" rb [formatSelector sel; formatString f]

// --------------------------------------------------------------------------------------
// General purpose helpers for working with selectors
// --------------------------------------------------------------------------------------

let withReferenceBehaviour rb e = 
  let ret ek = { e with Kind = ek }
  match e.Kind with 
  | RecordRenameField(_, s, o, n) -> RecordRenameField(rb, s, o, n) |> ret
  | Copy(_, s1, s2) -> Copy(rb, s1, s2) |> ret
  | WrapRecord(_, i, g, t) -> WrapRecord(rb, i, g, t) |> ret
  | WrapList(_, i, g, t) -> WrapList(rb, i, g, t) |> ret
  | RecordDelete(_, t, f) -> RecordDelete(rb, t, f) |> ret
  | _ -> e

/// Returns all references in a given node as a triple consisting of the
/// base path, reference kind & the selectors; expects the base path of 
/// the given node as an argument
let rec getNodeReferences path nd = 
  match nd with 
  | Record(_, nds) -> nds |> List.collect (fun (n, nd) -> getNodeReferences (path @ [Field n]) nd)
  | List(_, nds) -> nds |> List.collect (fun (n, nd) -> getNodeReferences (path @ [Index n]) nd)
  | Reference(Absolute, sels) -> [[], (Absolute, sels)]
  | Reference(Relative, sels) -> [path, (Relative, sels)]
  | Primitive _ -> []

/// Like 'getNodeReferences' but assumes the base path is empty
let getDocumentReferences nd = getNodeReferences [] nd

let withNodeReferences nd sels = 
  let mutable sels = sels
  let next() = let r = List.head sels in sels <- List.tail sels; r
  let rec loop nd = 
    match nd with 
    | Record(tag,  nds) -> Record(tag, List.map (fun (n, nd) -> n, loop nd) nds)
    | List(tag,  nds) -> List(tag, List.map (fun (n, nd) -> n, loop nd) nds)
    | Reference _ -> let k, s = next() in Reference(k, s) 
    | Primitive _ -> nd
  loop nd

/// Target selector points to the affected nodes, after the edit is done (?)
let getTargetSelector ed = 
  match ed.Kind with 
  // Selector is already pointing directly at the affected node
  | ListReorder(s, _) 
  | Copy(_, s, _)
  | UpdateTag(s, _) 
  | PrimitiveEdit(s, _, _) 
  | Check(s, _) -> s
  // Add selector to the end, pointing at the affected node
  | WrapList(_, _, _, s) -> s @ [All]
  | ListAppend(s, i, _) 
  | ListAppendFrom(s, i, _) 
  | ListDelete(s, i) -> s @ [Index i]
  | RecordRenameField(_, s, id, _) 
  | RecordDelete(_, s, id)
  | WrapRecord(_, _, id, s) 
  | RecordAdd(s, id, _) -> s @ [Field id]

let withTargetSelector tgt ed = 
  let getLastField tgt = match List.last tgt with Field f -> f | _ -> failwith "withTargetSelector - expected selector ending with a field"
  let getLastIndex tgt = match List.last tgt with Index i -> i | _ -> failwith "withTargetSelector - expected selector ending with an index"
  let ret nk = { ed with Kind = nk }
  match ed.Kind with 
  // Selector is already pointing directly at the affected node
  | ListReorder(_, m) -> ListReorder(tgt, m) |> ret
  | Copy(rb, _, s) -> Copy(rb, tgt, s) |> ret
  | UpdateTag(_, t) -> UpdateTag(tgt, t) |> ret
  | PrimitiveEdit(_, f, arg) -> PrimitiveEdit(tgt, f, arg) |> ret
  | Check(_, cond) -> Check(tgt, cond) |> ret
  // Remove added selector, pointing at the affected node
  | WrapList(rb, id, t, _) -> WrapList(rb, id, t, List.dropLast tgt) |> ret
  | ListAppendFrom(_, _, s) -> ListAppendFrom(List.dropLast tgt, getLastIndex tgt, s) |> ret
  | ListAppend(_, _, nd) -> ListAppend(List.dropLast tgt, getLastIndex tgt, nd) |> ret
  | ListDelete(_, _) -> ListDelete(List.dropLast tgt, getLastIndex tgt) |> ret
  | RecordRenameField(rb, _, _, n) -> RecordRenameField(rb, List.dropLast tgt, getLastField tgt, n) |> ret
  | RecordDelete(rb, _, _) -> RecordDelete(rb, List.dropLast tgt, getLastField tgt) |> ret
  | WrapRecord(rb, t, _, _) -> WrapRecord(rb, t, getLastField tgt, List.dropLast tgt) |> ret
  | RecordAdd(_, _, nd) -> RecordAdd(List.dropLast tgt, getLastField tgt, nd) |> ret

let getTargetSelectorPrefixes eds = 
  let sels = System.Collections.Generic.HashSet<_>()
  for ed in eds do
    let sel = getTargetSelector ed
    for prefix in List.prefixes sel do ignore(sels.Add(prefix))
  List.sort (List.ofSeq sels)

// Selector pointing to the affected node, at a location where it is before the edit
let getAllReferences inNodes ed = 
  match ed.Kind with 
  // Selector is already pointing directly at the affected node
  | ListReorder(s, _) 
  | UpdateTag(s, _) 
  | PrimitiveEdit(s, _, _) 
  | Check(s, _) -> [[], (Absolute, s)]
  | ListAppendFrom(s1, _, s2)
  | Copy(_, s1, s2) -> [[], (Absolute, s1); [], (Absolute, s2)]
  // Pointing at a node that will be modified by the edit
  | WrapRecord(_, _, _, s) 
  | WrapList(_, _, _, s) -> [[], (Absolute, s)]
  | ListAppend(s, _, nd) 
  | RecordAdd(s, _, nd) -> ([], (Absolute, s)) :: (if inNodes then getNodeReferences s nd else [])
  // Add selector pointing to the previously existing thing 
  | RecordDelete(_, s, fld) 
  | RecordRenameField(_,s, fld, _) -> [[], (Absolute, s @ [Field fld])]
  | ListDelete(s, idx) -> [[], (Absolute, s @ [Index idx])]

let withAllReferences inNodes refs ed =
  let getLastField tgt = match List.last tgt with Field f -> f | _ -> failwith "withAllReferences - expected selector ending with a field"
  let getLastIndex tgt = match List.last tgt with Index i -> i | _ -> failwith "withAllReferences - expected selector ending with an index"
  let oneAbsolute = function [Absolute, sels] -> sels | _ -> failwith "withAllReferences - expected one absolute selector"
  let headAbsolute = function (Absolute, sels)::_ -> sels | _ -> failwith "withAllReferences - expected at least one absolute selector"
  let ret nk = { ed with Kind = nk }
  match ed.Kind with
  // Selector is already pointing directly at the affected node
  | ListReorder(_, m) -> ListReorder(oneAbsolute refs, m) |> ret
  | UpdateTag(_, t) -> UpdateTag(oneAbsolute refs, t) |> ret
  | PrimitiveEdit(_, f, arg) -> PrimitiveEdit(oneAbsolute refs, f, arg) |> ret
  | Check(_, cond) -> Check(oneAbsolute refs, cond) |> ret
  | Copy(rb, _, _) -> Copy(rb, headAbsolute refs, oneAbsolute (List.tail refs)) |> ret
  | ListAppendFrom(s1, n, s2) -> ListAppendFrom(headAbsolute refs, n, oneAbsolute (List.tail refs)) |> ret
  // Pointing at a node that will be modified by the edit
  | WrapRecord(rb, id, t, _) -> WrapRecord(rb, id, t, oneAbsolute refs) |> ret
  | WrapList(rb, id, t, _) -> WrapList(rb, id, t, oneAbsolute refs) |> ret
  | ListAppend(_, n, nd) -> ListAppend(headAbsolute refs, n, if inNodes then withNodeReferences nd (List.tail refs) else nd) |> ret
  | RecordAdd(_, s, nd) -> RecordAdd(headAbsolute refs, s, if inNodes then withNodeReferences nd (List.tail refs) else nd) |> ret
  // Add selector pointing to the previously existing thing 
  | ListDelete(_, _) -> ListDelete(List.dropLast (oneAbsolute refs), getLastIndex (oneAbsolute refs)) |> ret
  | RecordDelete(rb, _, f) -> RecordDelete(rb, List.dropLast (oneAbsolute refs), getLastField (oneAbsolute refs)) |> ret
  | RecordRenameField(rb, _, _, n) -> RecordRenameField(rb, List.dropLast (oneAbsolute refs), getLastField (oneAbsolute refs), n) |> ret


let mapReferences f ed = 
  // Here it may be useful to transform selectors inside added nodes too
  withAllReferences true (List.map f (getAllReferences true ed)) ed


// The following three functions only transform absolute references in the edit itself
// (but they do not look at references inside nodes - so they can work on selectors directly)
let getSelectors = getAllReferences false >> List.map (snd >> snd)
let withSelectors = List.map (fun s -> Absolute, s) >> withAllReferences false
let tryWithSelectors sels ed = 
  // Here we do not want to look inside added nodes because otherwise
  // it is impossible to scope any edits adding references
  try Some(withSelectors sels ed)
  with _ -> None


/// If 'p1' is prefix of 'p2', return the rest of 'p2'.
/// This also computes 'more specific prefix' which is a version
/// of the prefix where 'Index' is preferred over 'All' when matched.
let removeSelectorPrefix p1 p2 = 
  let rec loop specPref p1 p2 = 
    match p1, p2 with 
    | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> loop (Field(f1)::specPref) p1 p2
    | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> loop (Index(i1)::specPref) p1 p2
    // TODO: Arguably, we should not insert into specific index (only All) as that is a 'type error'
    // Meaning that when called from 'scopeEdit', then 'p1' should not contain 'Index' ?
    | Index(i)::p1, All::p2 ->
        None //failwith "removeSelectorPrefix - Index/All - arguably error %"
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
  | _ -> None

let (|IncompatibleFirst|_|) = function
  | Field(f1)::_, Field(f2)::_ when f1 <> f2 -> Some()
  | Index(i1)::_, Index(i2)::_ when i1 <> i2 -> Some()
  | (All|Index _|Field _)::_, []
  | (All|Index _)::_, Field(_)::_ 
  | Field(_)::_, (All|Index _)::_ -> Some()
  | [], _ -> Some()
  | _ -> None

let (|TooSpecific|_|) = function
  | All::_,  (s & Index _)::_ -> Some(s)
  | _ -> None 

// Base can only be specific (no Alls) but absolute can be general.
// Keep it general if it is.
let rec makeRelative baseSels absoluteSels = 
  match baseSels, absoluteSels with 
  | MatchingFirst(_, baseSels, absoluteSels) -> makeRelative baseSels absoluteSels
  | baseSels, absoluteSels -> List.init baseSels.Length (fun _ -> DotDot) @ absoluteSels

let transformBasedReference (baseOther, (kindOther, selsOther)) f = 
  let selOther = resolveReference baseOther (kindOther, selsOther)
  match kindOther with
  | Absolute -> Absolute, f selOther
  | Relative -> Relative, makeRelative (f baseOther) (f selOther)
 
/// Returns a modified version of 'selOther' to match
/// the additional wrapping (in a record with original at @id) at location specified by 'selWrap'
let wrapRecordSelectors id selWrap refOther =
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> Field(id)::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
    | TooSpecific(s) -> failwith $"wrapRecordSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"wrapRecordSelectors.wrapsels - Missing case: {selOther} vs. {selWrap}"
  transformBasedReference refOther (fun selOther -> wrapsels selOther selWrap)

/// Returns a modified version of 'selOther' to match
/// the additional wrapping (in a list) at location specified by 'selWrap'
let wrapListSelectors selWrap refOther =
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> All::selOther // interesting case here
    | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
    | TooSpecific(s) -> failwith $"wrapListSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"wrapListSelectors - Missing case: {selOther} vs. {selWrap}"
  transformBasedReference refOther (fun selOther -> wrapsels selOther selWrap)

/// Returns a modified version of 'selOther' to match
/// the changed field ID at location specified by 'selReord'
let renameFieldSelectors fold fnew selRename refOther =
  let rec reidsels selOther selRename =
    match selOther, selRename with 
    | Field(fo)::selOther, [] when fo = fold -> Field(fnew)::(reidsels selOther []) // interesting case here
    | MatchingFirst(s, selOther, selRename) -> s::(reidsels selOther selRename)
    | TooSpecific(s) -> failwith $"renameFieldSelectors - Too specific selector {s} matched against Any"
    | IncompatibleFirst() -> selOther
    | _ -> failwith $"renameFieldSelectors - Missing case: {selOther} vs. {selRename}"
  transformBasedReference refOther (fun selOther -> reidsels selOther selRename)

// --------------------------------------------------------------------------------------
// Apply
// --------------------------------------------------------------------------------------

exception ConditionCheckFailed of string

let rec isStructuralSelector sel = 
  match sel with 
  | [] -> true
  | Index _::_ -> false
  | (All | Field _)::sel -> isStructuralSelector sel
  | DotDot::_ -> failwith "isStructuralSelector: Unresolved relative reference"

let apply doc edit =
  match edit.Kind with
  | _ when edit.Disabled -> doc

  // **Value edits** - These do not affect any selectors elsewhere in the document.
  // Add and Append change structure in that they add new items that may have a different
  // shape. This is allowed at runtime, but it may break code referring to newly added
  // things. We could check this using some kind of type system.

  | Check(sel, cond) ->
      match cond, select sel doc with 
      | EqualsTo(String s1), [Primitive(String s2)] -> if s1 <> s2 then raise(ConditionCheckFailed $"apply.Check: EqualsTo failed ({s1}<>{s2})")
      | EqualsTo(Number n1), [Primitive(Number n2)] -> if n1 <> n2 then raise(ConditionCheckFailed $"apply.Check: EqualsTo failed ({n1}<>{n2})")
      | NonEmpty, [Primitive(Number _)] -> ()
      | NonEmpty, [Primitive(String s)] -> if System.String.IsNullOrWhiteSpace(s) then raise(ConditionCheckFailed $"apply.Check: NonEmpty failed ({s})")
      | cond, nd -> raise (ConditionCheckFailed $"apply.Check Condition ({cond}) failed ({nd})")
      doc

  | PrimitiveEdit(sel, f, arg) ->
      replace (fun p el -> 
        match el with 
        | Primitive(v) when matches p sel -> Some(Primitive(transformationsLookup.[f] (arg, v)))
        | _ -> None ) doc

  | ListAppend(sel, n, nd) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> 
            // Similar to 'RecordAdd' but we do not remove duplicates (what will that do?)
            Some(List(tag, nds @ [n, nd]))
        | _ -> None ) doc

  | ListAppendFrom(sel, n, src) ->
      replace (fun p el ->
        match el with
        | List(tag, nds) when matches p sel -> 
            Some(List(tag, nds @ [n, selectSingle src doc]))
        | _ -> None ) doc

  | RecordAdd(sel, fld, nd) ->
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> 
            let nds = nds |> List.filter (fun (k, _) -> k <> fld)
            Some(Record(tag, nds @ [fld, nd]))
        | _ -> None ) doc
    
  | UpdateTag(sel, tagNew) ->
      replace (fun p el ->
        match el with 
        | Record(t, nds) when matches p sel -> Some(Record(tagNew, nds))
        | List(t, nds) when matches p sel -> Some(List(tagNew, nds))
        | _ -> None ) doc

  | ListDelete(sel, idel) ->
      replace (fun p -> function
        | List(t, items) when matches p sel -> 
            let items = items |> List.choose (fun (j, it) -> 
              if idel <> j  then Some(j, it) else None)
            Some(List(t, items))
        | _ -> None) doc

  | ListReorder(sel, ord) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> Some(List(tag, [ for i in ord -> List.find (fst >> (=) i) nds])) // TODO: Not compatible with multikeys
        | _ -> None ) doc

  // **Structural edits** - These can be applied both as structural edits to change document shape
  // or as value edits to affect only particular values. We allow structural edits only when
  // the target selector is structural too! Using those as value edits changes structure too
  // and could consequently break things (but see note above).

  | RecordDelete(rb, sel, fdel) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.RecordDelete - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p -> function
        | Record(t, nds) when matches p sel ->
            let nds = nds |> List.filter (fun (f, _) -> f <> fdel)
            Some(Record(t, nds))
        | _ -> None) doc
      if rb = UpdateReferences then 
        // We cannot update selectors if the target node was deleted, but 
        // we can check there are no such selectors in the document.
        for docRef in getDocumentReferences doc do 
          if includesReference (sel @ [Field fdel]) docRef then
            failwith $"apply.RecordDelete - Cannot delete {formatSelector sel}. Document contains conflicting selector {formatReference (snd docRef)}."
        doc
      else doc
      
  | WrapRecord(rb, id, tag, sel) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.WrapRecord - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = 
        // TODO: Need to update references before transforming the document - but why was that?
        if rb = UpdateReferences then
          let nsels = getDocumentReferences doc |> List.map (wrapRecordSelectors id sel)
          withNodeReferences doc nsels
        else doc
      replace (fun p el -> 
        if matches p sel then Some(Record(tag, [id, el]))
        else None ) doc

  | WrapList(rb, id, tag, sel) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.WrapList - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el -> 
        if matches p sel then Some(List(tag, [id, el]))
        else None ) doc
      if rb = UpdateReferences then
        let nsels = getDocumentReferences doc |> List.map (wrapListSelectors sel)
        withNodeReferences doc nsels
      else doc

  | RecordRenameField(rb, sel, fold, fnew) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.RecordRenameField - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el -> 
        match el with 
        | Record(t, nds) when matches p sel -> 
            Some(Record(t, List.map (fun (f, nd) -> if f = fold then fnew, nd else f, nd) nds))
        | _ -> None ) doc
      if rb = UpdateReferences then
        let nsels = getDocumentReferences doc |> List.map (renameFieldSelectors fold fnew sel)
        withNodeReferences doc nsels
      else doc

  | Copy(rb, sel, src) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.Copy - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."

      let mutable exprs = 
        let srcNodes = select src doc
        match select sel doc with         
        | tgs when tgs.Length = srcNodes.Length -> srcNodes
        // Slightly clever in that we can copy multiple source nodes into a single target list node
        // (this is needed for evaluation of arguments - see eval.fs)
        | [List(t, _)] -> [List(t, List.mapi (fun i nd -> string i, nd) srcNodes)] 
        | tgtNodes -> failwith $"apply.Copy - Mismatching number of source and target notes. Edit: {formatEdit edit}, src nodes: {srcNodes.Length}, target nodes: {tgtNodes.Length} "
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy - Unexpected"
      let doc = replace (fun p el -> 
        if matches p sel then Some(next())
        else None ) doc

      if rb = UpdateReferences then 
        // We cannot update selectors in the document to match this edit, so make sure 
        // there are none (when copying from referenced source, we'd need to duplicate 
        // the reference as done when merging in 'copyEdit'; when copying to 
        // a location, we have no clue what the structure change is, so cannot update.)
        for docRef in getDocumentReferences doc do
          if includesReference sel docRef then
            failwith $"apply.RecordDelete - Cannot copy to {formatSelector sel}. Document contains conflicting selector {formatReference (snd docRef)}."
          if includesReference src docRef then
            failwith $"apply.RecordDelete - Cannot copy from {formatSelector sel}. Document contains conflicting selector {formatReference (snd docRef)}."
        doc
      else doc


// --------------------------------------------------------------------------------------
// Merge
// --------------------------------------------------------------------------------------

type ScopingResult = 
  // All selectors were in the specified scope and have been changed as required
  | InScope of Edit
  // All selectors were outside of the specified scope - no change to edit
  | AllOutOfScope 
  // Target was out of scope, but source selectors may be in scope 
  | TargetOutOfScope 
  // Target was in scope, but source outside - if the transform did not do 
  // something invalid, we can return rescoped edit (leaving original source)
  // (this can be None if 'tryWithSelectors' fails because the scoping affected
  // selector that must have stayed the same because it is a part of edit)
  | SourceOutOfScope of Edit option 

let tryScopeSelectors f edit = 
  let sels = getSelectors edit 
  let scopedSels = 
    List.choose f sels 
  let fullyScopedEditOpt = 
    tryWithSelectors scopedSels edit
  let scopedTargetSel = 
    f (getTargetSelector edit) 
  let partiallyScopedEdit () = 
    tryWithSelectors (sels |> List.map (fun s -> defaultArg (f s) s)) edit

  match fullyScopedEditOpt, scopedTargetSel with 
  // None of the selectors satisfied the condition
  | _ when scopedSels.Length = 0 -> AllOutOfScope
  // All selectors satisfied the condition
  | Some nedit, _ when scopedSels.Length = sels.Length -> InScope nedit 
  // Target selector did not satisfy the condition
  | _, None -> TargetOutOfScope
  // Either just source selectors did not satisfy the condition
  // or 'tryWithSelectors' failed because the scoping would create
  // invalid selector (e.g., drop field name from Delete edit)
  | _, Some _ -> SourceOutOfScope(partiallyScopedEdit())

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
  // For structural edits, transform the selectors in the
  // other edit in a way corresponding to the edit
  | WrapRecord(UpdateReferences, id, _, sel) ->
      [mapReferences (wrapRecordSelectors id sel) e1]
  | WrapList(UpdateReferences, _, _, sel) -> 
      [mapReferences (wrapListSelectors sel) e1]
  | RecordRenameField(UpdateReferences, sel, fold, fnew) ->
      [mapReferences (renameFieldSelectors fold fnew sel) e1]
  
  // For structural copy, we may need to duplicate the edit e1
  | Copy(UpdateReferences, tgtSel, srcSel) -> 
      match copyEdit e1 srcSel tgtSel with 
      | Some res -> res
      | _ ->
          // TODO: What does this even do?
          let target = getTargetSelector e1
          let conflict = removeSelectorPrefix srcSel target |> Option.isSome
          if conflict then failwith $"CONFLICT!!!\ne1={e1}\ne2={e2}"
          else [e1]
  
  | RecordDelete(UpdateReferences, _, _) -> 
      [e1] // failwith "updateSelectors - Detect conflicts - record delete"

  // Value edits do not affect other selectors
  | _ -> [e1]
  

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
let applyToAdded e1 e2 = 
  let mkEd ed = { Kind = ed; Dependencies = []; Disabled = false; GroupLabel = e2.GroupLabel }

  match e1.Kind with   
   // We are appending under 'sel', so the selector for 'nd' will be 'sel/*' 
  | ListAppendFrom(sel, n, src) -> 
      match scopeEdit (sel @ [All]) (sel @ [Index n]) e2 with
      | InScope e2scoped -> [ e1; withReferenceBehaviour KeepReferences e2scoped ]
      | _ -> [e1]

  | ListAppend(sel, n, nd) -> 
      match scopeEdit (sel @ [All]) [] e2 with
      | InScope e2scoped ->
          [ { e1 with Kind = ListAppend(sel, n, apply nd e2scoped) }]
      | AllOutOfScope | TargetOutOfScope -> [e1]
      | SourceOutOfScope None -> failwith "todo - think about this"
      | SourceOutOfScope (Some _) -> 
          match scopeEdit (sel @ [All]) (sel @ [Index n]) e2 with 
          | SourceOutOfScope (Some e2scoped) -> [ e1; e2scoped ]
          | _ -> failwith "applyToAdded: should not happen"

  | RecordAdd(sel, fld, nd) -> 
      match scopeEdit (sel @ [Field fld]) [] e2 with
      | InScope _ | SourceOutOfScope _ -> 
          // TODO: This is conflict, because e2 was doing something with a 
          // record field and e1 is now replacing it with a new thing.
          // We can let 'e1' win (return [e1]) or 'e2' win (return [])
          [e1]
      | AllOutOfScope | TargetOutOfScope -> [e1]

  | Copy(_, sel, src) -> 
      match scopeEdit sel src e2 with
      | InScope _ | SourceOutOfScope _ -> 
          // TODO: Same conflict as in the case of RecordAdd - with same options.
          [e1]
      | AllOutOfScope | TargetOutOfScope -> [e1]

  | _ -> [e1]

// Assuming 'e1' and 'e2' happened independently,
// modify 'e1' so that it can be placed after 'e2'.
let moveBefore e1 e2 = 
  let e1s = applyToAdded e1 e2
  e1s |> List.collect (fun e1 -> updateSelectors e1 e2)

// --------------------------------------------------------------------------------------
// Edit groups
// --------------------------------------------------------------------------------------

let hashEditList initial eds = 
  eds |> List.fold (fun hashSoFar edit -> hash (hashSoFar, edit)) initial

let withHistoryHash initial (f:_ -> Edit) eds = 
  let hashes = eds |> List.scan (fun hashSoFar edit -> hash (hashSoFar, f edit)) initial
  List.zip (List.tail hashes) eds

let takeUntilHash hashToFind (f:_ -> Edit) eds = 
  let mutable hashSoFar = 0
  let res = eds |> List.takeWhile (fun edit -> 
    if hashSoFar = hashToFind then false else
    hashSoFar <- hash (hashSoFar, f edit) 
    true )
  if hashSoFar = hashToFind then Some res else None

let takeAfterHash hashToFind eds = 
  let mutable hashSoFar = 0
  let res = eds |> List.skipWhile (fun edit -> 
    if hashSoFar = hashToFind then false else
    hashSoFar <- hash (hashSoFar, edit) 
    true )
  if hashSoFar = hashToFind then Some res else None

// let eds = ["a"; "b"; "c"]  
// withHistoryHash 0 eds
// takeUntilHash -1539880934 eds
// takeAfterHash -1539880934 eds

let applyHistory initial hist =
  hist |> List.fold apply initial
  
let filterDisabledGroups initial hist = 
  hist 
  |> List.chunkBy (fun ed -> ed.GroupLabel)
  |> List.mapWithState (fun doc group ->
      let keep, state = 
        try true, group |> List.fold apply doc
        with ConditionCheckFailed _ -> false, doc
      let ngroup =
        if keep then group
        else group |> List.map (fun ed -> { ed with Disabled = true })
      ngroup, state) initial
  |> List.collect id
  
let getDependencies ed = 
  match ed.Kind with 
  | ListAppendFrom(_, _, src)
  | Copy(_, _, src) ->  getTargetSelector ed :: src :: ed.Dependencies
  | _ -> getTargetSelector ed :: ed.Dependencies
  
let filterConflicting = 
  List.mapWithState (fun modsels ed ->
    // Conflict if any dependency depends on any of the modified locations
    let conflict = getDependencies ed |> List.exists (fun dep -> 
      List.exists (fun modsel -> includes dep modsel || includes modsel dep) modsels)
    if conflict then { ed with Disabled = true }, (getTargetSelector ed)::modsels
    else ed, modsels) 


type ConflictResolution = 
  | IgnoreConflicts
  | RemoveConflicting

let counter = let mutable n = 0 in (fun () -> n <- n + 1; n)

let pushEditsThrough crmode hashBefore hashAfter e1s e2s = 
  let e2s = 
    if crmode = RemoveConflicting then
      let e1ModSels = e1s |> List.map getTargetSelector
      filterConflicting e1ModSels e2s
    else e2s

  // TODO: Clean this up so that it does not look so ugly?
  // (As we push edits 'e2s' through 'e1s', we also compute
  // map that maps hashes of old edits to hashes of new edits)

  let mutable hashBefore = hashBefore
  let mutable hashAfter = hashAfter
  let hashMap = System.Collections.Generic.Dictionary<_, _>()

  e2s |> List.collect (fun e2 ->
      // For a given edit 'e2', move it before all the edits in 'e1s' using 'moveBefore'
      // (caveat is that the operation can turn it into multiple edits)
      let res = List.fold (fun e2 e1 -> 
        e2 |> List.collect (fun e2 -> moveBefore e2 e1)) [e2] e1s 
      
      let resHashed = withHistoryHash hashAfter id res
      hashBefore <- hash(hashBefore, e2)
      hashAfter <- hashEditList hashAfter res
      hashMap.Add(hashBefore, (hashAfter, resHashed))

      res ), hashMap

let pushEditsThroughSimple crmode e1s e2s = 
  pushEditsThrough crmode 0 0 e1s e2s |> fst



  (*
type Effect = 
  | ValueEffect
  | StructureEffect 

let getEffect ed = 
  match ed.Kind with 
  | Value _ 
  | Shared(ValueKind, _) -> ValueEffect, getTargetSelector ed
  | Shared(StructuralKind, _) -> StructureEffect, getTargetSelector ed
let addEffect effs (kindEff, selEff) = 
  List.exists (fun (k, e) -> includesStrict e selEff)

  effs |> Set.fi

let getEffects eds =
  set (List.map getEffect eds)

*)
let mergeHistories crmode (h1:Edit list) (h2:Edit list) =
  let shared, (e1s, e2s) = List.sharedPrefix h1 h2

  (*
  let e1eff = getEffects e1s
  let e2eff = getEffects e2s
  printfn "E1 (BASE) EFFECTS"
  for eff in e1eff do printfn $"  {fst eff} {formatSelector (snd eff)}"
  printfn "E2 (MERGE) EFFECTS"
  for eff in e2eff do printfn $"  {fst eff} {formatSelector (snd eff)}"
  *)
  let e2sAfter, hashMap = pushEditsThrough crmode (hashEditList 0 (shared)) (hashEditList 0 (shared @ e1s)) e1s e2s
  shared @ e1s @ e2sAfter, hashMap

let mergeHistoriesSimple crmode h1 h2 = 
  mergeHistories crmode h1 h2 |> fst
