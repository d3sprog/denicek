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
  | Record of string * OrdList<string, Node>
  | List of string * OrdList<string, Node>
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
        List(tag, nds |> OrdList.mapValues (fun n nd -> loop (path @ [Index n]) nd))
    | Record(tag, nds) -> 
        Record(tag, nds |> OrdList.mapValues (fun n nd -> loop (path @ [Field n]) nd))
    | Reference _ | Primitive _ -> nd 
  loop [] nd

let fold f st value = 
  let rec loop path st nd =
    let st = f path nd st 
    match nd with 
    | List(_, nds) -> 
        nds |> OrdList.fold (fun st (n, nd) -> loop (path @ [Index n]) st nd) st
    | Record(_, nds) -> 
        nds |> OrdList.fold (fun st (n, nd) -> loop (path @ [Field n]) st nd) st
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
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 | All::p1, All::p2 -> matches p1 p2
  | _ -> false

/// If 'p1' is prefix of 'p2', return the rest of 'p2'.
/// This also computes 'more specific prefix' which is a version
/// of the prefix where 'Index' is preferred over 'All' when matched.
let removePrefix matchAllIndex matchIndexAll p1 p2 = 
  let rec loop specPref p1 p2 = 
    match p1, p2 with 
    | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> loop (Field(f1)::specPref) p1 p2
    | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> loop (Index(i1)::specPref) p1 p2
    | Index(i)::p1, All::p2 when matchIndexAll -> loop (Index(i)::specPref) p1 p2
    | All::p1, Index(i)::p2 when matchAllIndex -> loop (Index(i)::specPref) p1 p2
    | All::p1, All::p2 -> loop (All::specPref) p1 p2
    | [], p2 -> Some(List.rev specPref, p2)
    | _ -> None
  loop [] p1 p2

/// Replace as much as possible of p2 with more specific matching part of p1
let replaceWithMoreSpecificPrefix p1 p2 = 
  let rec loop acc p1 p2 = 
    match p1, p2 with 
    | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> loop (Field(f1)::acc) p1 p2
    | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> loop (Index(i1)::acc) p1 p2
    | Index(i)::p1, All::p2 | All::p1, Index(i)::p2 -> loop (Index(i)::acc) p1 p2
    | All::p1, All::p2 -> loop (All::acc) p1 p2
    | _ -> List.rev acc @ p2
  loop [] p1 p2

let includesGeneral matchAllIndex matchIndexAll p1 p2 =
  removePrefix matchAllIndex matchIndexAll p1 p2 |> Option.isSome

let includes = includesGeneral true true

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
        for _, ch in Seq.filter (fst >> (=) n) els do
          yield! loop ((nd, s)::trace) sel ch
    | Record(_, els), (Field(n) as s)::sel -> 
        for _, ch in Seq.filter (fst >> (=) n) els do
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
        loop (List.map (fun acc -> s::acc) acc) sel (snd (Seq.find (fst >> (=) n) els))
    | List(_, els), (Index(n) as s)::sel -> 
        loop (List.map (fun acc -> s::acc) acc) sel (snd (Seq.find (fst >> (=) n) els))
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
  | Copy of ReferenceBehaviour * target:Selectors * source:Selectors
  | WrapRecord of ReferenceBehaviour * id:string * tag:string * target:Selectors
  | WrapList of ReferenceBehaviour * id:string * tag:string * target:Selectors
  | RecordDelete of ReferenceBehaviour * Selectors * string
  // Edits that cannot affect references in document
  | ListReorder of Selectors * list<string>
  | ListDelete of Selectors * string
  | ListAppend of Selectors * index:string * pred:string option * Node 
  | ListAppendFrom of Selectors * index:string * pred:string option * Selectors 
  | UpdateTag of Selectors * string
  | PrimitiveEdit of Selectors * string * string option
  | RecordAdd of Selectors * field:string * pred:string option * Node

and Edit = 
  { Kind : EditKind 
    GroupLabel : string
    Dependencies : Selectors list }

// --------------------------------------------------------------------------------------
// Pretty printing
// --------------------------------------------------------------------------------------

let formatSelector = 
  List.map (function 
    | All -> "*" | DotDot -> ".." | Index i -> "#" + i | Field f -> f)
  >> String.concat "/"

let formatString (s:string) = 
  "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""

let formatReference (kind, sel) =
  (if kind = Relative then "./" else "/") + formatSelector sel

let rec formatNode nd = 
  match nd with 
  | Primitive(String s) -> formatString s
  | Primitive(Number n) -> string n
  | List(tag, nds) -> sprintf "%s[%s]" tag (String.concat ", " [for k, v in nds -> $"{k}={formatNode nd}" ])
  | Record(tag, nds) -> sprintf "%s{%s}" tag (String.concat ", " [for k, v in nds -> $"{k}={formatNode nd}" ])
  | Reference(kind, sel) -> formatReference (kind, sel)

let formatReferenceBehaviour = function
  | UpdateReferences -> "s" | KeepReferences -> "v"

let formatStringOpt nd = Option.map formatString nd |> Option.defaultValue "na"

let formatEdit ed = 
  let fmt kvd kind args = $"""{formatReferenceBehaviour kind}.{kvd}({ String.concat "," args })"""
  let fmtv kvd args = $"""{kvd}({ String.concat "," args })"""
  match ed.Kind with
  | PrimitiveEdit(sel, op, None) -> 
      fmtv "primitive" [formatSelector sel; formatString op]
  | PrimitiveEdit(sel, op, Some arg) -> 
      fmtv "primitive" [formatSelector sel; formatString op; formatString arg]
  | RecordAdd(sel, n, pred, nd) -> 
      fmtv "recordAdd" [formatSelector sel; formatString n; formatStringOpt pred; formatNode nd]
  | UpdateTag(sel, tagNew) -> 
      fmtv "updateTag" [formatSelector sel; formatString tagNew]
  | ListAppend(sel, n, pred, nd) ->       
      fmtv "listAppend" [formatSelector sel; formatString n; formatStringOpt pred; formatNode nd ]
  | ListAppendFrom(sel, n, pred, src) -> 
      fmtv "appendFrom" [formatSelector sel; formatString n; formatStringOpt pred; formatSelector src ]
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
  | Record(_, nds) -> nds |> Seq.collect (fun (n, nd) -> getNodeReferences (path @ [Field n]) nd) |> List.ofSeq
  | List(_, nds) -> nds |> Seq.collect (fun (n, nd) -> getNodeReferences (path @ [Index n]) nd) |> List.ofSeq
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
    | Record(tag,  nds) -> Record(tag, OrdList.mapValues (fun n nd -> loop nd) nds)
    | List(tag,  nds) -> List(tag, OrdList.mapValues (fun n nd -> loop nd) nds)
    | Reference _ -> let k, s = next() in Reference(k, s) 
    | Primitive _ -> nd
  loop nd

/// Target selector points to the affected nodes, after the edit is done (?)
let getAnySelector afterTarget copySourceSel ed = 
  match ed.Kind with 
  | Copy(_, _, s) when copySourceSel -> s
  // Selector is already pointing directly at the affected node
  | ListReorder(s, _) 
  | UpdateTag(s, _) 
  | Copy(_, s, _) 
  | PrimitiveEdit(s, _, _) -> s
  // Add selector to the end, pointing at the affected node
  | WrapList(_, _, _, s) -> s @ [All] // do not append if not afterTarget?
  | ListAppend(s, i, _, _) 
  | ListAppendFrom(s, i, _, _) 
  | ListDelete(s, i) -> s @ [Index i]
  | RecordRenameField(_, s, _, id) when afterTarget -> s @ [Field id]
  | RecordRenameField(_, s, id, _) 
  | RecordDelete(_, s, id)
  | WrapRecord(_, _, id, s) 
  | RecordAdd(s, id, _, _) -> s @ [Field id]

let withAnySelector afterTarget copySourceSel tgt ed = 
  let getLastField tgt = match List.last tgt with Field f -> f | _ -> failwith "withTargetSelector - expected selector ending with a field"
  let getLastIndex tgt = match List.last tgt with Index i -> i | _ -> failwith "withTargetSelector - expected selector ending with an index"
  let ret nk = { ed with Kind = nk }
  match ed.Kind with 
  | Copy(rb, s, _) when copySourceSel -> Copy(rb, s, tgt) |> ret
  // Selector is already pointing directly at the affected node
  | ListReorder(_, m) -> ListReorder(tgt, m) |> ret
  | Copy(rb, _, s) -> Copy(rb, tgt, s) |> ret
  | UpdateTag(_, t) -> UpdateTag(tgt, t) |> ret
  | PrimitiveEdit(_, f, arg) -> PrimitiveEdit(tgt, f, arg) |> ret
  // Remove added selector, pointing at the affected node
  | WrapList(rb, id, t, _) -> WrapList(rb, id, t, List.dropLast tgt) |> ret
  | ListAppendFrom(_, _, pred, s) -> ListAppendFrom(List.dropLast tgt, getLastIndex tgt, pred, s) |> ret
  | ListAppend(_, _, pred, nd) -> ListAppend(List.dropLast tgt, getLastIndex tgt, pred, nd) |> ret
  | ListDelete(_, _) -> ListDelete(List.dropLast tgt, getLastIndex tgt) |> ret
  | RecordRenameField(rb, _, n, _) when afterTarget -> RecordRenameField(rb, List.dropLast tgt, n, getLastField tgt) |> ret
  | RecordRenameField(rb, _, _, n) -> RecordRenameField(rb, List.dropLast tgt, getLastField tgt, n) |> ret
  | RecordDelete(rb, _, _) -> RecordDelete(rb, List.dropLast tgt, getLastField tgt) |> ret
  | WrapRecord(rb, t, _, _) -> WrapRecord(rb, t, getLastField tgt, List.dropLast tgt) |> ret
  | RecordAdd(_, _, pred, nd) -> RecordAdd(List.dropLast tgt, getLastField tgt, pred, nd) |> ret

let getBaseTargetSelector ed = 
  match ed.Kind with 
  | Copy(_, _, s)
  | ListReorder(s, _) 
  | UpdateTag(s, _) 
  | PrimitiveEdit(s, _, _) 
  | WrapList(_, _, _, s) 
  | ListAppend(s, _, _, _) 
  | ListAppendFrom(s, _, _, _) 
  | ListDelete(s, _) -> s 
  | RecordDelete(_, s, _)
  | RecordAdd(s, _, _, _) 
  | WrapRecord(_, _, _, s) -> s
  | RecordRenameField(_, s, f, _) -> s @ [Field f]

let withBaseTargetSelector tgt ed = 
  let getLastField tgt = match List.last tgt with Field f -> f | _ -> failwith "withTargetSelector - expected selector ending with a field"
  let ret nk = { ed with Kind = nk }
  match ed.Kind with 
  | Copy(rb, s, _) -> Copy(rb, s, tgt) |> ret
  | ListReorder(_, m) -> ListReorder(tgt, m) |> ret
  | UpdateTag(_, t) -> UpdateTag(tgt, t) |> ret
  | PrimitiveEdit(_, f, arg) -> PrimitiveEdit(tgt, f, arg) |> ret
  | WrapList(rb, id, t, _) -> WrapList(rb, id, t, tgt) |> ret
  | ListAppendFrom(_, i, pred, s) -> ListAppendFrom(tgt, i, pred, s) |> ret
  | ListAppend(_, i, pred, nd) -> ListAppend(tgt, i, pred, nd) |> ret
  | ListDelete(_, i) -> ListDelete(tgt, i) |> ret
  | RecordRenameField(rb, _, _, fn) -> RecordRenameField(rb, List.dropLast tgt, getLastField tgt, fn) |> ret
  | RecordDelete(rb, _, f) -> RecordDelete(rb, tgt, f) |> ret
  | WrapRecord(rb, i, t, _) -> WrapRecord(rb, i, t, tgt) |> ret
  | RecordAdd(_, f, pred, nd) -> RecordAdd(tgt, f, pred, nd) |> ret

let getTargetSelector = getAnySelector false false 
let withTargetSelector = withAnySelector false false

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
  | PrimitiveEdit(s, _, _) -> [[], (Absolute, s)]
  | ListAppendFrom(s1, _, _, s2)
  | Copy(_, s1, s2) -> [[], (Absolute, s1); [], (Absolute, s2)]
  // Pointing at a node that will be modified by the edit
  | WrapRecord(_, _, _, s) 
  | WrapList(_, _, _, s) -> [[], (Absolute, s)]
  | ListAppend(s, _, _, nd) 
  | RecordAdd(s, _, _, nd) -> ([], (Absolute, s)) :: (if inNodes then getNodeReferences s nd else [])
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
  | Copy(rb, _, _) -> Copy(rb, headAbsolute refs, oneAbsolute (List.tail refs)) |> ret
  | ListAppendFrom(_, n, pred, _) -> ListAppendFrom(headAbsolute refs, n, pred, oneAbsolute (List.tail refs)) |> ret
  // Pointing at a node that will be modified by the edit
  | WrapRecord(rb, id, t, _) -> WrapRecord(rb, id, t, oneAbsolute refs) |> ret
  | WrapList(rb, id, t, _) -> WrapList(rb, id, t, oneAbsolute refs) |> ret
  | ListAppend(_, n, pred, nd) -> ListAppend(headAbsolute refs, n, pred, (if inNodes then withNodeReferences nd (List.tail refs) else nd)) |> ret
  | RecordAdd(_, s, pred, nd) -> RecordAdd(headAbsolute refs, s, pred, if inNodes then withNodeReferences nd (List.tail refs) else nd) |> ret
  // Add selector pointing to the previously existing thing 
  | ListDelete(_, _) -> ListDelete(List.dropLast (oneAbsolute refs), getLastIndex (oneAbsolute refs)) |> ret
  | RecordDelete(rb, _, f) -> RecordDelete(rb, List.dropLast (oneAbsolute refs), getLastField (oneAbsolute refs)) |> ret
  | RecordRenameField(rb, _, _, n) -> RecordRenameField(rb, List.dropLast (oneAbsolute refs), getLastField (oneAbsolute refs), n) |> ret


// The following three functions only transform absolute references in the edit itself
// (but they do not look at references inside nodes - so they can work on selectors directly)
let getSelectors = getAllReferences false >> List.map (snd >> snd)

let withSelectors = List.map (fun s -> Absolute, s) >> withAllReferences false
let tryWithSelectors sels ed = 
  // Here we do not want to look inside added nodes because otherwise
  // it is impossible to scope any edits adding references
  try Some(withSelectors sels ed)
  with _ -> None


let removeSelectorPrefix = removePrefix true false
  
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

let rec isStructuralSelector sel = 
  match sel with 
  | [] -> true
  | Index _::_ -> false
  | (All | Field _)::sel -> isStructuralSelector sel
  | DotDot::_ -> failwith "isStructuralSelector: Unresolved relative reference"

let apply doc edit =
  match edit.Kind with

  // **Value edits** - These do not affect any selectors elsewhere in the document.
  // Add and Append change structure in that they add new items that may have a different
  // shape. This is allowed at runtime, but it may break code referring to newly added
  // things. We could check this using some kind of type system.

  | PrimitiveEdit(sel, f, arg) ->
      replace (fun p el -> 
        match el with 
        | Primitive(v) when matches p sel -> Some(Primitive(transformationsLookup.[f] (arg, v)))
        | _ -> None ) doc

  | ListAppend(sel, n, pred, nd) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> 
            // Similar to 'RecordAdd' but we do not remove duplicates (what will that do?)
            Some(List(tag, OrdList.add (n, nd) pred nds))
        | _ -> None ) doc
      
  | ListAppendFrom(sel, n, pred, src) ->
      replace (fun p el ->
        match el with
        | List(tag, nds) when matches p sel -> 
            Some(List(tag, OrdList.add (n, selectSingle src doc) pred nds))
        | _ -> None ) doc
      
  | RecordAdd(sel, fld, pred, nd) ->
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> 
            let nds = nds |> OrdList.remove fld
            Some(Record(tag, OrdList.add (fld, nd) pred nds))
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
            let items = items |> OrdList.remove idel
            Some(List(t, items))
        | _ -> None) doc

  | ListReorder(sel, ord) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> 
            Some(List(tag, OrdList.withOrder ord nds))
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
            let nds = nds |> OrdList.remove fdel
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
        if matches p sel then Some(Record(tag, OrdList.singleton id el))
        else None ) doc

  | WrapList(rb, id, tag, sel) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.WrapList - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."
      let doc = replace (fun p el -> 
        if matches p sel then Some(List(tag, OrdList.singleton id el))
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
            Some(Record(t, OrdList.renameKey fold fnew nds))
        | _ -> None ) doc
      if rb = UpdateReferences then
        let nsels = getDocumentReferences doc |> List.map (renameFieldSelectors fold fnew sel)
        withNodeReferences doc nsels
      else doc

  | Copy(rb, sel, src) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.Copy - Non-structural selector {formatSelector sel} used with structural edit {formatEdit edit}."

      let mutable exprs, ok = 
        let srcNodes = select src doc
        match select sel doc with         
        | tgs when tgs.Length = srcNodes.Length -> srcNodes, true
        // Slightly clever in that we can copy multiple source nodes into a single target list node
        // (this is needed for evaluation of arguments - see eval.fs)
        | [List(t, _)] -> [List(t, OrdList.ofList (List.mapi (fun i nd -> string i, nd) srcNodes))], true 
        // If source or target is empty, do not do anything
        // (needed if we create merged edits that do not apply to anything)
        | tgtNodes when srcNodes.Length = 0 || tgtNodes.Length = 0 -> [], false 
        | tgtNodes -> failwith $"apply.Copy - Mismatching number of source and target notes. Edit: {formatEdit edit}, src nodes: {srcNodes.Length}, target nodes: {tgtNodes.Length} "
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy - Unexpected"
      if ok then 
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
      else doc

// --------------------------------------------------------------------------------------
// Merge
// --------------------------------------------------------------------------------------
(*
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
  | _, None when scopedSels.Length = 0 -> AllOutOfScope
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
    *)
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
// 'e2' so that it can be placed after 'e1'. If the edit 'e1' was 
// structural edit that affected the shape of the document, we need
// to transform the selectors in 'e2' to match the new shape.
// Note that this is doing almost exactly the same thing as when 
// editing existing document (there, we update selectors in document)
//
// If the 'e1' edit was structural Copy and the target of 'e2' was
// the source of the copy, we return [e2;e2'] that targets both the
// original node and the one produced by the copying. (When editing
// document, such structural copy would be disallowed.)
//
let updateSelectors e1 e2 = 
  let mapReferences f e2 = 
    let sels = getAllReferences true e2 |> List.map f
    withAllReferences true sels e2

  match e1.Kind with 
  // For structural edits, transform the selectors in the
  // other edit in a way corresponding to the edit
  | WrapRecord(UpdateReferences, id, _, sel) ->
      [mapReferences (wrapRecordSelectors id sel) e2]
  | WrapList(UpdateReferences, _, _, sel) -> 
      [mapReferences (wrapListSelectors sel) e2]
  | RecordRenameField(UpdateReferences, sel, fold, fnew) ->
      [mapReferences (renameFieldSelectors fold fnew sel) e2]
  
  // For structural copy, we may need to duplicate the edit e1
  | Copy(UpdateReferences, tgtSel, srcSel) -> 
      match copyEdit e2 srcSel tgtSel with 
      | Some res -> res 
      | _ ->
          // TODO: What does this even do?
          let target = getTargetSelector e2
          let conflict = removeSelectorPrefix srcSel target |> Option.isSome
          if conflict then failwith $"CONFLICT!!!\ne1={e2}\ne2={e1}"
          else [e2]

  // Value edits do not affect other selectors
  | _ -> [e2]

let simpleRemoveSelectorPrefix p1 p2 = 
  let rec loop specPref p1 p2 = 
    match p1, p2 with 
    | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> loop (Field(f1)::specPref) p1 p2
    | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> loop (Index(i1)::specPref) p1 p2
    | Index(i)::p1, All::p2 ->
        None //failwith "removeSelectorPrefix - Index/All - arguably error %"
    | All::p1, Index(i)::p2 ->
        //None //
        loop (Index(i)::specPref) p1 p2

    | All::p1, All::p2 -> loop (All::specPref) p1 p2
    | [], p2 -> Some(List.rev specPref, p2)
    | _ -> None
  loop [] p1 p2

let destructsTarget conflicting e = 
  let target = getAnySelector true false e
  match e.Kind with 
  | RecordDelete _ | RecordAdd _ | Copy _ | WrapRecord _ -> matches target conflicting
  | _ -> false

let isStructuralEdit e =
  match e.Kind with 
  | WrapRecord(UpdateReferences, _, _, _) 
  | WrapList(UpdateReferences, _, _, _) 
  | RecordRenameField(UpdateReferences, _, _, _) 
  | Copy(UpdateReferences, _, _) -> true
  | _ -> false

// Scope e1 to affect the target of e2  
let simpleScopeEdit e1 e2 = 
  // Scope e1 based on a selector that points to copy source / location before the edit is applied
  // (because this is what e2 is adding and so we want to scope e1 if it affects the sources)
  let e2sel, e1sel = (getAnySelector true false e2), getBaseTargetSelector e1
  match e2.Kind, removePrefix false true e2sel e1sel with 
  | _ when destructsTarget e2sel e1 ->
      None
  | Copy _, Some(_, []) when isStructuralEdit e1 ->  
      // Target of Copy is already created, so we only scope edits that do something inside
      // (but not edits that affect the target as such, as those have already been applied earlier)
      None
  | _, Some(specificPrefix, rest) ->
      // Still transform all other selectors here e.g. when e1 is Copy inside the target of e2
      let e1target = specificPrefix @ rest
      // Maybe a bit hackish trick? It is hard to figure out what exactly part of the
      // selector to scope in the case of copY!
      let nsels = getSelectors e1 |> List.map (replaceWithMoreSpecificPrefix e1target) 
      let e1 = defaultArg (tryWithSelectors nsels e1) e1
      let scoped = withBaseTargetSelector (specificPrefix @ rest) e1
      Some(withReferenceBehaviour KeepReferences scoped)
  | _ -> None
  

// Assuming 'e1' and 'e2' happened independently, we want to modify
// 'e2' so that it can be placed after 'e1'. If the 
//
// * If the edit 'e2' is adding new items to the document, we want to apply the 
//   transformation done by 'e1' to the value to be added. If the edit 'e1' is copying.
//
// * If the edit 'e1' is appending a list item from somewhere else in the document and
//   'e2' did some operation to the list we are appending to, return edit that first
//   does the same operation to the source of the copy 
//
// * If the edit 'e1' is adding new item to a record, then .. think about this.
// * If the edit 'e1' is copying .. think about this.
//
let applyToAdded e1 (e2, e2extras) = 
  (*
  match e2.Kind with   
  | ListAppendFrom(sel, n, src) -> 
      match scopeEdit (sel @ [All]) (sel @ [Index n]) e1 with
      | InScope e1scoped | SourceOutOfScope (Some e1scoped) -> 
          Some [ withReferenceBehaviour KeepReferences e1scoped ]
      | TargetOutOfScope | AllOutOfScope | SourceOutOfScope None ->
          None

  | ListAppend(sel, n, nd) -> 
      //printfn $"APPLY {formatEdit e1} to added {formatEdit e2}"
      match scopeEdit (sel @ [All]) (sel @ [Index n]) e1 with
      | InScope e1scoped 
      | SourceOutOfScope (Some e1scoped) ->
          //printfn $"SCOPED {formatEdit e1}"
          //printfn $"AS {formatEdit e1scoped}"
          Some [ withReferenceBehaviour KeepReferences e1scoped ]
          //printfn $"IN SCOPE ({formatSelector (sel @ [All])}): {formatEdit e2}"
          //[ { e1 with Kind = ListAppend(sel, n, apply nd e2scoped) }]
      (*| AllOutOfScope | TargetOutOfScope -> e1, []
      | SourceOutOfScope None -> failwith "todo - think about this"
      | SourceOutOfScope (Some _) -> 
          printfn $"SOURCE OUT OF SCOPE: {formatEdit e2}"
          match scopeEdit (sel @ [All]) (sel @ [Index n]) e2 with 
          | SourceOutOfScope (Some e2scoped) -> [ e1; e2scoped ]
          | _ -> failwith "applyToAdded: should not happen"
          *)
      | TargetOutOfScope | AllOutOfScope | SourceOutOfScope None ->
          None

  | Copy(_, sel, src) -> 
      match scopeEdit sel src e2 with
      | InScope _ | SourceOutOfScope _ -> 
          // TODO: Same conflict as in the case of RecordAdd - with same options.
          [e1]
      | AllOutOfScope | TargetOutOfScope -> [e1]
  *)

  match e2.Kind with   
  | ListAppendFrom _
  | ListAppend _
  | Copy _
  | RecordAdd _ -> 
      // If we are handling edit that adds something, we may need to apply 'e1' to it!
      // Try to scope e1 to target of either e2 itself or any of the later added edits
      e2::e2extras |> List.tryPick (fun e2 ->
        match simpleScopeEdit e1 e2 with
        | Some e1 -> Some [ withReferenceBehaviour KeepReferences e1 ]
        | _ -> None)
  | _ -> None

// Assuming 'e1' and 'e2' happened independently,
// modify 'e2' so that it can be placed after 'e1'.
let moveBefore e1 (e2, e2extras) = 
  let e2extras = 
    match applyToAdded e1 (e2, e2extras) with 
    | Some e2moreExtras -> e2extras @ e2moreExtras
    | None -> List.collect (updateSelectors e1) e2extras
  match updateSelectors e1 e2 with 
  | e2::e2s -> (e2, e2extras) :: [ for e in e2s -> e, [] ] // no extras for copied?
  | [] -> failwith "never"

  //extras //|> List.collect (fun ee -> updateSelectors e1 ee)

let moveAllBefore e1 e2s = 
  //printfn $"MOVE BEFORE {formatEdit e1}"
  //printfn $" * edits = {List.map formatEdit e2s}"
  //printfn $" * extras = {List.map formatEdit e2extras}"
  //let e2s, e2extras0 = List.map (moveBefore e1) e2s |> List.unzip
  //let e2extras, e2extras1 = List.map (applyToAdded e1) e2extras |> List.unzip
  //printfn $" * nedits = {List.map formatEdit (List.concat e2s)}"
  //printfn $" * nextras = {List.map formatEdit (List.concat e2extras)} // {List.map formatEdit (List.concat e2extras0)} // {List.map formatEdit (List.concat e2extras1)}"
  //List.concat e2s, e2extras @ (List.concat (e2extras0 @ e2extras1))
  List.collect (moveBefore e1) e2s

// --------------------------------------------------------------------------------------
// Edit groups
// --------------------------------------------------------------------------------------

let hashEditList initial (eds:Edit list) = 
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
  
let getDependencies ed = 
  match ed.Kind with 
  | ListAppendFrom(_, _, _, src)
  | Copy(_, _, src) ->  getTargetSelector ed :: src :: ed.Dependencies
  | _ -> getTargetSelector ed :: ed.Dependencies
  
let filterConflicting = 
  List.filterWithState (fun modsels ed ->
    // Conflict if any dependency depends on any of the modified locations
    let conflict = getDependencies ed |> List.exists (fun dep -> 
      List.exists (fun modsel -> includes dep modsel || includes modsel dep) modsels)
    if conflict then false, (getTargetSelector ed)::modsels
    else true, modsels) 


type ConflictResolution = 
  | IgnoreConflicts
  | RemoveConflicting

let counter = let mutable n = 0 in (fun () -> n <- n + 1; n)

// Push edits 'e2s' through 'e1s'
let pushEditsThrough crmode hashBefore hashAfter e1s e2s =
  (*
  printfn "PUSH EDITS"
  for e in e2s do printfn $"  {formatEdit e}"
  printfn "THROUGH"
  for e in e1s do printfn $"  {formatEdit e}"
  //*)
  let e2s = 
    if crmode = RemoveConflicting then
      let e1ModSels = e1s |> List.map getTargetSelector
      filterConflicting e1ModSels e2s
    else e2s

  let log = false //|| true
  let e2smap =  
    e2s |> List.map (fun e2 ->
      if log then
        printfn "========================"
        printfn $"PUSHING EDIT\n  * {formatEdit e2}"
      let res = e1s |> List.fold (fun e2s e1 -> 
        if log then printfn $"  * through: {formatEdit e1}"
        let res = moveAllBefore e1 e2s //moveAllBefore e1 e2s
        if log then printfn "    -> now have: %s" (String.concat "," [ for e, es in res do $"  {formatEdit e} {List.map formatEdit es}" ])
        res           ) [e2, []]
      //printfn $"GOT"
      //for e in res do printfn $"  * {formatEdit e}"
      e2, [ for e,ee in res do yield! e::ee ]
    )
    (*
  let e2smap = 
    e2s |> List.map (fun e2 ->
      printfn $"UPDATING {formatEdit e2}"
      let e2init = [e2], []
      let e2after, e2extras = 
        e1s |> List.fold (fun e2state e1 -> 
          let res = moveAllBefore e1 e2state
          printfn $"... {formatEdit e1} = {List.map formatEdit (fst res)}"
          res ) e2init
      printfn $" * after {List.map formatEdit e2after}"
      printfn $" * extras {List.map formatEdit e2extras}"
      e2, e2after, e2extras) 
      *)
  // Compute before and after hashes for original and new edits
  let hashMap = 
    e2smap |> List.mapWithState (fun (hashBefore, hashAfter) (e2, e2after) ->
      let hashBefore = hash(hashBefore, e2)
      let e2afterHashed = withHistoryHash hashAfter id e2after
      let hashAfter = hashEditList hashAfter e2after
      (hashBefore, (hashAfter, e2afterHashed)), (hashBefore, hashAfter)) (hashBefore, hashAfter) |> dict
  (*
  // Computer after hashes for the extra added edits
  let e2smap = 
    e2smap |> List.mapWithState (fun hashAfter (e2, e2after, e2extras) ->
      let e2extrasHashed = withHistoryHash hashAfter id e2extras
      let hashAfter = hashEditList hashAfter e2extras
      (e2, e2after, e2extrasHashed), hashAfter) hashAfter
      *)
  //let hashMap = 
    //[ for (_, e2hash), e2after, e2extras in e2smap -> 
      //  e2hash, (fst (List.last e2after), e2after, e2extras) ] |> dict
  
  //List.collect (fun (_, e2s, _) -> List.map snd e2s) e2smap @ 
  //List.collect (fun (_, _, extras) -> List.map snd extras) e2smap,
  List.collect snd e2smap,
  hashMap

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
  //printfn "MERGE EDITS"
  //for e in e2s do printfn $"  {formatEdit e}"
  //printfn "AFTER"
  //for e in e1s do printfn $"  {formatEdit e}"
  let e2sAfter, hashMap = pushEditsThrough crmode (hashEditList 0 (shared)) (hashEditList 0 (shared @ e1s)) e1s e2s
  shared @ e1s @ e2sAfter, hashMap

let mergeHistoriesSimple crmode h1 h2 = 
  mergeHistories crmode h1 h2 |> fst
