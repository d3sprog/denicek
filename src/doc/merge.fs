module Denicek.Merge

open Denicek.Doc


let getLastField tgt = 
  match List.last tgt with Field f -> f | _ -> failwith "getLastField - expected selector ending with a field"
let getLastIndex tgt = 
  match List.last tgt with Index i -> i | _ -> failwith "getLastIndex - expected selector ending with an index"

// --------------------------------------------------------------------------------------
// getSelectors/withSelectors 
//
// Selector pointing to involved nodes, at a location where they are before the edit
// (i.e., the only modified selectors are the Rename & Delete ones)
// --------------------------------------------------------------------------------------

let getSelectors ed = 
  match ed.Kind with 
  // Selector is already pointing directly at the affected node
  | ListReorder(s, _) 
  | UpdateTag(s, _) 
  | PrimitiveEdit(s, _, _) -> [s]
  | Copy(_, s1, s2) -> [s1; s2]
  // Pointing at a node that will be modified by the edit
  | WrapRecord(_, _, _, s) 
  | WrapList(_, _, _, s) 
  | ListAppend(s, _, _, _) 
  | RecordAdd(s, _, _, _) -> [s]
  // Add selector pointing to the previously existing thing 
  | RecordDelete(_, s, fld) 
  | RecordRenameField(_,s, fld, _) -> [s @ [Field fld]]
  | ListDelete(s, idx) -> [s @ [Index idx]]
  
let withSelectors sels ed =
  let ret nk = { ed with Kind = nk }
  match ed.Kind with
  // Selector is already pointing directly at the affected node
  | ListReorder(_, m) -> ListReorder(List.exactlyOne sels, m) |> ret
  | UpdateTag(_, t) -> UpdateTag(List.exactlyOne sels, t) |> ret
  | PrimitiveEdit(_, f, arg) -> PrimitiveEdit(List.exactlyOne sels, f, arg) |> ret
  | Copy(rb, _, _) -> Copy(rb, List.head sels, List.exactlyOne (List.tail sels)) |> ret
  // Pointing at a node that will be modified by the edit
  | WrapRecord(rb, id, t, _) -> WrapRecord(rb, id, t, List.exactlyOne sels) |> ret
  | WrapList(rb, id, t, _) -> WrapList(rb, id, t, List.exactlyOne sels) |> ret
  | ListAppend(_, n, pred, nd) -> ListAppend(List.head sels, n, pred, nd) |> ret
  | RecordAdd(_, s, pred, nd) -> RecordAdd(List.head sels, s, pred, nd) |> ret
  // Add selector pointing to the previously existing thing 
  | ListDelete(_, _) -> ListDelete(List.dropLast (List.exactlyOne sels), getLastIndex (List.exactlyOne sels)) |> ret
  | RecordDelete(rb, _, f) -> RecordDelete(rb, List.dropLast (List.exactlyOne sels), getLastField (List.exactlyOne sels)) |> ret
  | RecordRenameField(rb, _, _, n) -> RecordRenameField(rb, List.dropLast (List.exactlyOne sels), getLastField (List.exactlyOne sels), n) |> ret

// --------------------------------------------------------------------------------------
// getTargetSelector/withTargetSelector
//
// Selector pointing at the target of the edit, after the edit was done
// (i.e., use new names, add Index/Field to the target whenever possible)
// --------------------------------------------------------------------------------------

let getTargetSelector ed = 
  match ed.Kind with 
  // Selector is already pointing directly at the affected node
  | ListReorder(s, _) 
  | UpdateTag(s, _) 
  | PrimitiveEdit(s, _, _)
  | Copy(_, s, _) -> s
  // Add selector to the end, pointing at the affected node
  | ListAppend(s, i, _, _) 
  | ListDelete(s, i) -> s @ [Index i]
  | RecordRenameField(_, s, _, id) 
  | RecordDelete(_, s, id)
  | WrapRecord(_, _, id, s) 
  | WrapList(_, id, _, s)
  | RecordAdd(s, id, _, _) -> s @ [Field id]

let withTargetSelector tgt ed = 
  let ret nk = { ed with Kind = nk }
  match ed.Kind with 
  // Selector is already pointing directly at the affected node
  | ListReorder(_, m) -> ListReorder(tgt, m) |> ret
  | UpdateTag(_, t) -> UpdateTag(tgt, t) |> ret
  | PrimitiveEdit(_, f, arg) -> PrimitiveEdit(tgt, f, arg) |> ret
  | Copy(rb, _, s) -> Copy(rb, tgt, s) |> ret
  // Remove added selector, pointing at the affected node
  | ListAppend(_, _, pred, nd) -> ListAppend(List.dropLast tgt, getLastIndex tgt, pred, nd) |> ret
  | ListDelete(_, _) -> ListDelete(List.dropLast tgt, getLastIndex tgt) |> ret
  | RecordRenameField(rb, _, o, _) -> RecordRenameField(rb, List.dropLast tgt, o, getLastField tgt) |> ret
  | RecordDelete(rb, _, _) -> RecordDelete(rb, List.dropLast tgt, getLastField tgt) |> ret
  | WrapRecord(rb, t, _, _) -> WrapRecord(rb, t, getLastField tgt, List.dropLast tgt) |> ret
  | WrapList(rb, _, t, _) -> WrapList(rb, getLastField tgt, t, List.dropLast tgt) |> ret
  | RecordAdd(_, _, pred, nd) -> RecordAdd(List.dropLast tgt, getLastField tgt, pred, nd) |> ret


// --------------------------------------------------------------------------------------
// getAfterTargetSelector/withAfterTargetSelector
//
// Target selector but pointing at the new location after rename
// (i.e., like getTargetSelector, but returns the new field name)
// --------------------------------------------------------------------------------------

let getBaseTargetSelector ed = 
  match ed.Kind with 
  | Copy(_, _, s)
  | ListReorder(s, _) 
  | UpdateTag(s, _) 
  | PrimitiveEdit(s, _, _) 
  | WrapList(_, _, _, s) 
  | ListAppend(s, _, _, _) 
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
  | ListAppend(_, i, pred, nd) -> ListAppend(tgt, i, pred, nd) |> ret
  | ListDelete(_, i) -> ListDelete(tgt, i) |> ret
  | RecordRenameField(rb, _, _, fn) -> RecordRenameField(rb, List.dropLast tgt, getLastField tgt, fn) |> ret
  | RecordDelete(rb, _, f) -> RecordDelete(rb, tgt, f) |> ret
  | WrapRecord(rb, i, t, _) -> WrapRecord(rb, i, t, tgt) |> ret
  | RecordAdd(_, f, pred, nd) -> RecordAdd(tgt, f, pred, nd) |> ret
 

// --------------------------------------------------------------------------------------
// Merge - update selectors
// --------------------------------------------------------------------------------------

module UpdateSelectors = 

  let rec substituteWithMoreSpecific specPrefix sels = 
    match specPrefix, sels with
    | Field(f1)::specPrefix, Field(f2)::sels when f1 = f2 -> Field(f1)::(substituteWithMoreSpecific specPrefix sels)
    | Index(i1)::specPrefix, Index(i2)::sels when i1 = i2 -> Index(i1)::(substituteWithMoreSpecific specPrefix sels)
    | All::specPrefix, Index(i1)::sels 
    | Index(i1)::specPrefix, All::sels -> Index(i1)::(substituteWithMoreSpecific specPrefix sels)
    | All::specPrefix, All::sels -> All::(substituteWithMoreSpecific specPrefix sels)
    | _ -> sels  // Not matching, but that's OK, we only want to subsitute prefix

  let copyEdit e1 srcSel tgtSel = 
    // Works both when the copied thing is directly the target of the edit 'e1'
    // and when the edit 'e1' targets something inside the copied
    let origSels = getSelectors e1 
    let newSels = origSels |> List.map (fun sel ->
      match removePrefix true false srcSel sel with 
      | Some(specPrefix, suffix) -> 
          tgtSel @ suffix |> substituteWithMoreSpecific specPrefix
      | _ -> sel)
    if origSels = newSels then None
    else 
      Some [e1; withSelectors newSels e1]


  let getInNodeReferences ed = 
    match ed.Kind with 
    | ListAppend(s, _, _, nd) 
    | RecordAdd(s, _, _, nd) -> getNodeReferences s nd
    | _ -> []

  let getAllReferences = 
    getSelectors >> List.map (fun sel -> [], (Absolute, sel))

  let withAllReferences = 
    List.map (function (Absolute, s) -> s | _ -> failwith "withAllReferences - expected absolute reference") 
    >> withSelectors 

  let withInNodeReferences refs ed = 
    let ret nk = { ed with Kind = nk }
    match ed.Kind with 
    | ListAppend(sel, i, pred, nd) -> ListAppend(sel, i, pred, withNodeReferences nd refs) |> ret
    | RecordAdd(sel, f, pred, nd) -> RecordAdd(sel, f, pred, withNodeReferences nd refs) |> ret
    | _ -> ed


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
      let ndsels = getInNodeReferences e2 |> List.map f
      let edsels = getAllReferences e2 |> List.map f
      e2 |> withAllReferences edsels |> withInNodeReferences ndsels

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
        | None -> [e2]

    // Value edits do not affect other selectors
    | _ -> [e2]


  let updateNodeReferences e1 e2 = 
    let mapReferences f e2 = 
      let sels = getInNodeReferences e2 |> List.map f
      withInNodeReferences sels e2
    match e1.Kind with 
    | WrapRecord(_, id, _, sel) ->
        mapReferences (Transforms.wrapRecordSelectors id sel) e2
    | WrapList(_, _, _, sel) -> 
        mapReferences (Transforms.wrapListSelectors sel) e2
    | RecordRenameField(_, sel, fold, fnew) ->
        mapReferences (Transforms.renameFieldSelectors fold fnew sel) e2
    | _ -> e2

// --------------------------------------------------------------------------------------
// Merge - apply to added
// --------------------------------------------------------------------------------------

module ApplyToAdded = 
  let withReferenceBehaviour rb e = 
    let ret ek = { e with Kind = ek }
    match e.Kind with 
    | RecordRenameField(_, s, o, n) -> RecordRenameField(rb, s, o, n) |> ret
    | Copy(_, s1, s2) -> Copy(rb, s1, s2) |> ret
    | WrapRecord(_, i, g, t) -> WrapRecord(rb, i, g, t) |> ret
    | WrapList(_, i, g, t) -> WrapList(rb, i, g, t) |> ret
    | RecordDelete(_, t, f) -> RecordDelete(rb, t, f) |> ret
    | _ -> e

  let destructsTarget conflicting e = 
    let target = getTargetSelector e
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
    let e1sel = getBaseTargetSelector e1
    let e2sel = getTargetSelector e2
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
        let e1 = withSelectors nsels e1 
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
    | ListAppend _
    | Copy _
    | RecordAdd _ -> 
        // If we are handling edit that adds something, we may need to apply 'e1' to it!
        // Try to scope e1 to target of either e2 itself or any of the later added edits
        e2::e2extras |> List.tryPick (simpleScopeEdit e1)
    | _ -> None


// --------------------------------------------------------------------------------------
// Merge - move before
// --------------------------------------------------------------------------------------
 
// Assuming 'e1' and 'e2' happened independently,
// modify 'e2' so that it can be placed after 'e1'.
let moveBefore e1 (e2, e2extras) = 
  let e2extras = 
    match ApplyToAdded.applyToAdded e1 (e2, e2extras) with 
    | Some e2moreExtras -> e2extras @ [e2moreExtras]
    | None -> 
        e2extras |> List.collect (UpdateSelectors.updateNodeReferences e1 
          >> UpdateSelectors.updateSelectors e1) 
  match UpdateSelectors.updateSelectors e1 e2 with 
  | e2::e2s -> (e2, e2extras) :: [ for e in e2s -> e, [] ] // no extras for copied?
  | [] -> failwith "never"


let moveAllBefore e1 e2s = 
  List.collect (moveBefore e1) e2s

// --------------------------------------------------------------------------------------
// Hash operations
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

// --------------------------------------------------------------------------------------
// Effect system
// --------------------------------------------------------------------------------------

type ConflictResolution = 
  | IgnoreConflicts
  | RemoveConflicting

type Effect = 
  | TagEffect
  | ValueEffect 
  | StructureEffect 


/// Format effect info in a readable way
let formatEffect (kind, sels) = 
  sprintf 
    ( match kind with 
      | ValueEffect -> "val(%s)" 
      | TagEffect -> "tag(%s)"
      | StructureEffect -> "struct(%s)") (Format.formatSelector sels)


/// Returns information about the effect caused by the edit
let getEditEffect ed = 
  match ed.Kind with 
  // Edits that affect structure of document 
  // (for the purpose of effects, we ignore reference behaviour)
  | RecordRenameField(_, t, _, _) | Copy(_, t, _)
  | WrapRecord(_, _, _, t) | WrapList(_, _, _, t)
  | RecordDelete(_, t, _) -> StructureEffect, t

  // Edit that affects the tag of a node
  | UpdateTag(t, _) -> TagEffect, t

  // Edits that affect the value of a node
  | ListReorder(t, _) | ListDelete(t, _) | ListAppend(t, _, _, _)
  | PrimitiveEdit(t, _, _) | RecordAdd(t, _, _, _) -> ValueEffect, t

let getEditsEffects eds =
  set (List.map getEditEffect eds)


/// Returns the target effect alongside with all dependencies
/// (edit conflicts if any of those returned conflict)
let getEditDependencies ed = 
  let cs = match ed.Kind with Copy(_, _, s) -> [s] | _ -> [] 
  getEditEffect ed :: [for d in cs @ ed.Dependencies -> ValueEffect, d]

let getEditsDependencies eds =
  set (List.collect getEditDependencies eds)


/// Two effects are in conflict
let conflicts (ef1kind, ef1sel) (ef2kind, ef2sel) = 
  ef1kind = ef2kind && (prefix ef1sel ef2sel || prefix ef2sel ef1sel)

/// Effect is in conflict with any other effect
let conflictsWith ef effs = 
  List.exists (conflicts ef) effs

/// Any effect is in conflict with any other effect
let conflictsWithAny effs1 effs2 = 
  List.exists (fun e -> conflictsWith e effs1) effs2


/// Return all effects of a nested edit list (as used inside pushEditsThrough)
let getAllEffects x = 
  x |> List.collect (fun (e, es) -> e::es) |> getEditsEffects |> List.ofSeq
/// Return all dependencies of a nested edit list (as used inside pushEditsThrough)
let getAllDependencies x = 
  x |> List.collect (fun (e, es) -> e::es) |> getEditsDependencies |> List.ofSeq


// Push edits 'e2s' through 'e1s'
let pushEditsThrough crmode hashBefore hashAfter e1s e2s =
  let e2smap =  
    // Push each individual 'e2' edit through all 'e1s'. The edit 'e2'
    // may become multiple edits. We keep this as list<Edit * list<Edit>>
    // where the outer list is multiple copied edits (via Copy) and the
    // nested list keeps edits that need to be applied after the Edit
    // (they were generated to transform things added by the edit).
    //
    // For conflict detection, we keep 'dropped', which are effects of
    // all edits 'e2' that we dropped because of conflict. If a subsequent
    // edit 'e2' conflicts with any 'dropped', it also must be dropped!
    //
    e2s |> List.mapWithState (fun dropped e2 ->
      let conflict = conflictsWithAny (getEditDependencies e2) dropped 

      let res, conflict = 
        e1s |> List.fold (fun (e2s, conflict) e1 -> 
          // e2 conflicts with e1s if it conflicted with anything before or
          // if its effects (TODO: dependencies?) conflict with effects of e1
          let conflict = conflict || (crmode = RemoveConflicting &&
              conflictsWith (getEditEffect e1) (getAllDependencies e2s))
          moveAllBefore e1 e2s, conflict)  ([e2, []], conflict)

      // If 'e2' was conflicting, replace with [] and add its effects to dropped list
      // Otherwise, flatten edits and keep original dropped list
      if conflict then (e2, []), dropped @ getAllEffects res
      else (e2, [ for e,ee in res do yield! e::ee ]), dropped) []


  // Compute before and after hashes for original and new edits
  let hashMap = 
    e2smap |> List.mapWithState (fun (hashBefore, hashAfter) (e2, e2after) ->
      let hashBefore = hash(hashBefore, e2)
      let e2afterHashed = withHistoryHash hashAfter id e2after
      let hashAfter = hashEditList hashAfter e2after
      (hashBefore, (hashAfter, e2afterHashed)), (hashBefore, hashAfter)
    ) (hashBefore, hashAfter) |> dict

  // Return the new edits and hashmap for mapping old edits to new
  List.collect snd e2smap, hashMap


/// Push edits e1s through e2s and return just new edits
let pushEditsThroughSimple crmode e1s e2s = 
  pushEditsThrough crmode 0 0 e1s e2s |> fst


/// Merge histories - find common prefix, push remaining 'h2' edits 
/// through 'h1' and append them to the end of the history
let mergeHistories crmode (h1:Edit list) (h2:Edit list) =
  let shared, (e1s, e2s) = List.sharedPrefix h1 h2
  let hashBefore, hashAfter = hashEditList 0 (shared), hashEditList 0 (shared @ e1s)
  let e2sAfter, hashMap = pushEditsThrough crmode hashBefore hashAfter e1s e2s
  shared @ e1s @ e2sAfter, hashMap

/// Merge histories - find common prefix, push remaining 'h2' edits 
/// through 'h1' and append them to the end of the history (ignore hashtable)
let mergeHistoriesSimple crmode h1 h2 = 
  mergeHistories crmode h1 h2 |> fst


