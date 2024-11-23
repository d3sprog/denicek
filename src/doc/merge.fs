module Denicek.Merge

open Denicek.Doc

// --------------------------------------------------------------------------------------
// Merge
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

let getInNodeReferences ed = 
  match ed.Kind with 
  | ListAppend(s, _, _, nd) 
  | RecordAdd(s, _, _, nd) -> getNodeReferences s nd
  | _ -> []

let withInNodeRferences refs ed = 
  let ret nk = { ed with Kind = nk }
  match ed.Kind with 
  | ListAppend(sel, i, pred, nd) -> ListAppend(sel, i, pred, withNodeReferences nd refs) |> ret
  | RecordAdd(sel, f, pred, nd) -> RecordAdd(sel, f, pred, withNodeReferences nd refs) |> ret
  | _ -> ed

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
      [mapReferences (Transforms.wrapRecordSelectors id sel) e2]
  | WrapList(UpdateReferences, _, _, sel) -> 
      [mapReferences (Transforms.wrapListSelectors sel) e2]
  | RecordRenameField(UpdateReferences, sel, fold, fnew) ->
      [mapReferences (Transforms.renameFieldSelectors fold fnew sel) e2]
  
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

let updateNodeReferences e1 e2 = 
  let mapReferences f e2 = 
    let sels = getInNodeReferences e2 |> List.map f
    withInNodeRferences sels e2
  match e1.Kind with 
  | WrapRecord(_, id, _, sel) ->
      mapReferences (Transforms.wrapRecordSelectors id sel) e2
  | WrapList(_, _, _, sel) -> 
      mapReferences (Transforms.wrapListSelectors sel) e2
  | RecordRenameField(_, sel, fold, fnew) ->
      mapReferences (Transforms.renameFieldSelectors fold fnew sel) e2
  | _ -> e2

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
  match e2.Kind with   
  | ListAppendFrom _
  | ListAppend _
  | Copy _
  | RecordAdd _ -> 
      // If we are handling edit that adds something, we may need to apply 'e1' to it!
      // Try to scope e1 to target of either e2 itself or any of the later added edits
      e2::e2extras |> List.tryPick (simpleScopeEdit e1)
  | _ -> None

// Assuming 'e1' and 'e2' happened independently,
// modify 'e2' so that it can be placed after 'e1'.
let moveBefore e1 (e2, e2extras) = 
  let e2extras = 
    match applyToAdded e1 (e2, e2extras) with 
    | Some e2moreExtras -> e2extras @ [e2moreExtras]
    | None -> List.collect (updateNodeReferences e1 >> updateSelectors e1) e2extras
  match updateSelectors e1 e2 with 
  | e2::e2s -> (e2, e2extras) :: [ for e in e2s -> e, [] ] // no extras for copied?
  | [] -> failwith "never"

  //extras //|> List.collect (fun ee -> updateSelectors e1 ee)

let moveAllBefore e1 e2s = 
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

let getDependencies ed = 
  match ed.Kind with 
  | ListAppendFrom(_, _, _, src)
  | Copy(_, _, src) ->  getTargetSelector ed :: src :: ed.Dependencies
  | _ -> getTargetSelector ed :: ed.Dependencies
  
let filterConflicting = 
  List.filterWithState (fun modsels ed ->
    // Conflict if any dependency depends on any of the modified locations
    let conflict = getDependencies ed |> List.exists (fun dep -> 
      List.exists (fun modsel -> prefix dep modsel || prefix modsel dep) modsels)
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
        printfn $"PUSHING EDIT\n  * {Format.formatEdit e2}"
      let res = e1s |> List.fold (fun e2s e1 -> 
        if log then printfn $"  * through: {Format.formatEdit e1}"
        let res = moveAllBefore e1 e2s //moveAllBefore e1 e2s
        if log then printfn "    -> now have: %s" (String.concat "," [ for e, es in res do $"  {Format.formatEdit e} {List.map Format.formatEdit es}" ])
        res           ) [e2, []]
      //printfn $"GOT"
      //for e in res do printfn $"  * {formatEdit e}"
      e2, [ for e,ee in res do yield! e::ee ]
    )

  // Compute before and after hashes for original and new edits
  let hashMap = 
    e2smap |> List.mapWithState (fun (hashBefore, hashAfter) (e2, e2after) ->
      let hashBefore = hash(hashBefore, e2)
      let e2afterHashed = withHistoryHash hashAfter id e2after
      let hashAfter = hashEditList hashAfter e2after
      (hashBefore, (hashAfter, e2afterHashed)), (hashBefore, hashAfter)) (hashBefore, hashAfter) |> dict

  List.collect snd e2smap,
  hashMap

let pushEditsThroughSimple crmode e1s e2s = 
  pushEditsThrough crmode 0 0 e1s e2s |> fst

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


