module Denicek.Doc
open Denicek

// --------------------------------------------------------------------------------------
// Document representation
// --------------------------------------------------------------------------------------

/// 'All' and 'Index' select children of a list; 'Field' selects element of a record
/// 'DotDot' appreas in relative references only (inside document, not in edits)
type Selector = 
  | All
  | Index of string
  | Field of string
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

// --------------------------------------------------------------------------------------
// Selector and reference operations
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

/// Checks if two selectors (partly) match, i.e. it is true when matching
/// All with Index. This is symmetric, i.e. matches p1 p2 = matches p2 p1
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

/// Replace as much as possible of p2 with more specific matching part of p1.
/// This matches Index with All and also All with Index.
let replaceWithMoreSpecificPrefix p1 p2 = 
  let rec loop acc p1 p2 = 
    match p1, p2 with 
    | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> loop (Field(f1)::acc) p1 p2
    | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> loop (Index(i1)::acc) p1 p2
    | Index(i)::p1, All::p2 | All::p1, Index(i)::p2 -> loop (Index(i)::acc) p1 p2
    | All::p1, All::p2 -> loop (All::acc) p1 p2
    | _ -> List.rev acc @ p2
  loop [] p1 p2

/// Check if 'p1' is prefix of 'p2'. Behaviour of Index/All match can be specified.
let prefixGeneral matchAllIndex matchIndexAll p1 p2 =
  removePrefix matchAllIndex matchIndexAll p1 p2 |> Option.isSome

/// Check if 'p1' is prefix of 'p2'. Matches Index/All and All/Index.
let prefix = prefixGeneral true true

/// Check if 'p1' is prefix of a reference. Matches Index/All and All/Index.
let prefixOfReference p1 (p2base, p2ref) =
  prefix p1 (resolveReference p2base p2ref)


// --------------------------------------------------------------------------------------
// Document transformations
// --------------------------------------------------------------------------------------

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

let select sel doc = 
  doc |> fold (fun p value st -> 
    if matches sel p then value::st else st) [] |> List.rev

let selectSingle sel doc = 
  match select sel doc with
  | [it] -> it
  | res -> failwithf "selectSingle: Looking for single %A but found %d" sel res.Length



/// Collect all paths that are specified by the given selector.
/// Returns a sequence of paths, where each path consists of the
/// target node and all nodes & selectors along the way.
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



/// Returns all references in a given node as a triple consisting of the
/// base path, reference kind & the selectors; expects the base path of 
/// the given node as an argument
let rec getNodeReferences path nd = 
  match nd with 
  | Record(_, nds) -> 
      nds |> OrdList.toListUnordered |> List.collect (fun (n, nd) -> 
        getNodeReferences (path @ [Field n]) nd)
  | List(_, nds) -> 
      nds |> OrdList.toListUnordered |> List.collect (fun (n, nd) -> 
        getNodeReferences (path @ [Index n]) nd)
  | Reference(Absolute, sels) -> [[], (Absolute, sels)]
  | Reference(Relative, sels) -> [path, (Relative, sels)]
  | Primitive _ -> []

/// Like 'getNodeReferences' but assumes the base path is empty
let getDocumentReferences nd = getNodeReferences [] nd

/// Replaces references in a node with new references. Assumes the same
/// order of references as that returned by 'getNodeReferences'
let withNodeReferences nd sels = 
  let mutable sels = sels
  let next() = let r = List.head sels in sels <- List.tail sels; r
  let rec loop nd = 
    match nd with 
    | Record(tag,  nds) -> Record(tag, OrdList.mapValuesUnordered (fun _ nd -> loop nd) nds)
    | List(tag,  nds) -> List(tag, OrdList.mapValuesUnordered (fun _ nd -> loop nd) nds)
    | Reference _ -> let k, s = next() in Reference(k, s) 
    | Primitive _ -> nd
  loop nd


// --------------------------------------------------------------------------------------
// Edits
// --------------------------------------------------------------------------------------
       
type ReferenceBehaviour = 
  | UpdateReferences
  | KeepReferences

type EditKind = 
  // Edits that can affect references in document
  // (when ReferenceBehaviour is set to UpdateReferences)
  | RecordRenameField of ReferenceBehaviour * target:Selectors * fold:string * fnew:string
  | Copy of ReferenceBehaviour * target:Selectors * source:Selectors
  | WrapRecord of ReferenceBehaviour * field:string * tag:string * target:Selectors
  | WrapList of ReferenceBehaviour * index:string * tag:string * target:Selectors
  | RecordDelete of ReferenceBehaviour * target:Selectors * field:string

  // Edits that cannot affect references in document
  | ListReorder of Selectors * permutation:list<string>
  | ListDelete of Selectors * index:string
  | ListAppend of Selectors * index:string * pred:string option * node:Node 
  // TODO: Delete this (but it will require recreating demo JSONs...)
  | ListAppendFrom_DELETE_ME of Selectors * index:string * pred:string option * source:Selectors 
  | UpdateTag of Selectors * ntag:string
  | PrimitiveEdit of Selectors * op:string * args:string option
  | RecordAdd of Selectors * field:string * pred:string option * node:Node

type Edit = 
  { Kind : EditKind 
    GroupLabel : string
    Dependencies : Selectors list }

// --------------------------------------------------------------------------------------
// Pretty printing
// --------------------------------------------------------------------------------------

module Format = 
  let formatSelector = 
    List.map (function 
      | All -> "*" | DotDot -> ".." | Index i -> "#" + i | Field f -> f)
    >> String.concat "/"

  let formatString (s:string) = 
    "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""

  let formatReference (kind, sel) =
    (if kind = Relative then "./" else "/") + formatSelector sel

  let formatNode nd = 
    let rec loop depth nd =
      match nd with 
      | _ when depth > 3 -> "..."
      | Primitive(String s) -> formatString s
      | Primitive(Number n) -> string n
      | List(tag, nds) -> sprintf "%s[%s]" tag (String.concat ", " [for k, v in nds -> $"{k}={loop (depth+1) v}" ])
      | Record(tag, nds) -> sprintf "%s{%s}" tag (String.concat ", " [for k, v in nds -> $"{k}={loop (depth+1) v}" ])
      | Reference(kind, sel) -> formatReference (kind, sel)
    loop 0 nd

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
// Helpes for transforming edits when merging / applying
// --------------------------------------------------------------------------------------

module Transforms = 

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

  // Base can only be specific (no Alls) but absolute can be general. Keep it general if it is.
  let rec makeRelative baseSels absoluteSels = 
    match baseSels, absoluteSels with 
    | MatchingFirst(_, baseSels, absoluteSels) -> makeRelative baseSels absoluteSels
    | baseSels, absoluteSels -> List.init baseSels.Length (fun _ -> DotDot) @ absoluteSels

  /// Transform reference with respect to given base path.
  /// Previously relative references are resolved and then made relative again.
  let transformBasedReference (baseOther, (kindOther, selsOther)) f = 
    let selOther = resolveReference baseOther (kindOther, selsOther)
    match kindOther with
    | Absolute -> Absolute, f selOther
    | Relative -> Relative, makeRelative (f baseOther) (f selOther)
 
  /// Returns a modified version of 'refOther' to match
  /// the additional wrapping (as record field named 'id') at location specified by 'selWrap'
  let wrapRecordSelectors id selWrap refOther =
    let rec wrapsels selOther selWrap =
      match selOther, selWrap with 
      | selOther, [] -> Field(id)::selOther // interesting case here
      | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
      | TooSpecific(s) -> failwith $"wrapRecordSelectors - Too specific selector {s} matched against Any"
      | IncompatibleFirst() -> selOther
      | _ -> failwith $"wrapRecordSelectors.wrapsels - Missing case: {selOther} vs. {selWrap}"
    transformBasedReference refOther (fun selOther -> wrapsels selOther selWrap)

  /// Returns a modified version of 'refOther' to match
  /// the additional list wrapping at location specified by 'selWrap'
  let wrapListSelectors selWrap refOther =
    let rec wrapsels selOther selWrap =
      match selOther, selWrap with 
      | selOther, [] -> All::selOther // interesting case here
      | MatchingFirst(s, selOther, selWrap) -> s::(wrapsels selOther selWrap)
      | TooSpecific(s) -> failwith $"wrapListSelectors - Too specific selector {s} matched against Any"
      | IncompatibleFirst() -> selOther
      | _ -> failwith $"wrapListSelectors - Missing case: {selOther} vs. {selWrap}"
    transformBasedReference refOther (fun selOther -> wrapsels selOther selWrap)

  /// Returns a modified version of 'refOther' to match
  /// the new field name at location specified by 'selRename'
  let renameFieldSelectors fold fnew selRename refOther =
    let rec reidsels selOther selRename =
      match selOther, selRename with 
      | Field(fo)::selOther, [] when fo = fold -> Field(fnew)::(reidsels selOther []) // interesting case here
      | MatchingFirst(s, selOther, selRename) -> s::(reidsels selOther selRename)
      | TooSpecific(s) -> failwith $"renameFieldSelectors - Too specific selector {s} matched against Any"
      | IncompatibleFirst() -> selOther
      | _ -> failwith $"renameFieldSelectors - Missing case: {selOther} vs. {selRename}"
    transformBasedReference refOther (fun selOther -> reidsels selOther selRename)

