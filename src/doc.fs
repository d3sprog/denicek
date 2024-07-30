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

let transformations = System.Collections.Generic.Dictionary<string, Primitive -> Primitive>()

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
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && matches p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && matches p1 p2
  | Tag(t1)::p1, Tag(t2)::p2 -> t1 = t2 && matches p1 p2
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> matches p1 p2
  | Tag(_)::p1, All::p2 | All::p1, Tag(_)::p2 -> matches p1 p2
  | _ -> false

let select sel doc = 
  doc |> fold (fun p value st -> 
    if matches sel p then value::st else st) [] |> List.rev

let selectSingle sel doc = 
  match select sel doc with
  | [it] -> it
  | _ -> failwith "selectSingle: Expected to find single node"

// --------------------------------------------------------------------------------------
// Edits
// --------------------------------------------------------------------------------------
                                             
                                                            // Kind   | Effect on selectors
type EditKind =                                             // =======|====================
  | PrimitiveEdit of Selectors * string                     // Value  | NS
  | ListAppend of Selectors * Node                          // ?      | NS
  | ListReorder of Selectors * list<int>                    // Value  | Change index
  | RecordAdd of Selectors * string * Node                  // Struct | NS
  | RecordRenameField of Selectors * string                 // Struct | Change field
  | Copy of source:Selectors * target:Selectors             // Struct | Duplicate edits
  | WrapRecord of id:string * tag:string * target:Selectors // Struct | Add field
  | WrapList of tag:string * target:Selectors               // Struct | Add 'All'
  | Replace of target:Selectors * Node                      // ?      | ?
  | UpdateTag of Selectors * string * string                // Struct | Change 'Tag'

//type RelationalOperator = 
//  | Equals | NotEquals 

//type EditCondition = 
  //| TagCondition of Selectors * RelationalOperator * string

type Edit = 
  { Kind : EditKind 
    //Conditions : EditCondition list
    //Dependencies : Selectors list
    //IsEvaluated : bool
    //CanDuplicate : bool 
  }

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
  | UpdateTag(s, _, _) | WrapRecord(_, _, s) | WrapList(_, s) -> [s]
  | ListAppend(s, nd) | Replace(s, nd) | RecordAdd(s, _, nd) -> s :: (getNodeSelectors nd)
  | Copy(s1, s2) -> [s1; s2]

/// Not including 'Reference' selectors in expressions
(*
let getDependenciesSelectors ed = 
  match ed.Kind with 
  | PrimitiveEdit(s, _) | ListReorder(s, _) | RecordRenameField(s, _) 
  | UpdateTag(s, _) | WrapRecord(_, _, s) | WrapList(_, s)
  | ListAppend(s, _) | RecordAdd(s, _) | Replace(s, _) -> s::ed.Dependencies
  | Copy(s1, s2) -> s1::s2::ed.Dependencies
*)
let getTargetSelector ed = 
  match ed.Kind with 
  | PrimitiveEdit(s, _) | ListReorder(s, _) | RecordRenameField(s, _) 
  | UpdateTag(s, _, _) | Replace(s, _) | Copy(_, s) -> s
  | WrapRecord(_, id, s) | RecordAdd(s, id, _) -> s @ [Field id]
  | ListAppend(s, _) | WrapList(_, s) -> s @ [All]

let withTargetSelector tgt ed = 
  let dropLast (tgt:_ list) = tgt.[0 .. tgt.Length - 2] // Remove the last, added in 'getTargetSelector'
  let nkind =
    match ed.Kind with 
    | ListAppend(_, nd) -> ListAppend(dropLast tgt, nd) 
    | WrapList(t, _) -> WrapList(t, dropLast tgt) 
    | RecordAdd(_, s, nd) -> RecordAdd(dropLast tgt, s, nd) 
    | WrapRecord(t, i, n) -> WrapRecord(t, i, dropLast tgt) 
    | Replace(_, nd) -> Replace(tgt, nd) 
    | PrimitiveEdit(_, f) -> PrimitiveEdit(tgt, f)
    | ListReorder(_, m) -> ListReorder(tgt, m)
    | UpdateTag(_, t1, t2) -> UpdateTag(tgt, t1, t2) 
    | RecordRenameField(_, s) -> RecordRenameField(tgt, s) 
    | Copy(_, s) -> Copy(tgt, s)
  { ed with Kind = nkind }

let withSelectors sels ed =
  let nkind =
    match ed.Kind with 
    | ListAppend(_, nd) -> ListAppend(List.head sels, withNodeSelectors nd (List.tail sels)) 
    | RecordAdd(_, s, nd) -> RecordAdd(List.head sels, s, withNodeSelectors nd (List.tail sels)) 
    | Replace(_, nd) -> Replace(List.head sels, withNodeSelectors nd (List.tail sels)) 
    | PrimitiveEdit(_, f) -> PrimitiveEdit(List.exactlyOne sels, f)
    | ListReorder(_, m) -> ListReorder(List.exactlyOne sels, m)
    | WrapRecord(t, f, _) -> WrapRecord(t, f, List.exactlyOne sels) 
    | WrapList(t, _) -> WrapList(t, List.exactlyOne sels) 
    | UpdateTag(_, t1, t2) -> UpdateTag(List.exactlyOne sels, t1, t2) 
    | RecordRenameField(_, s) -> RecordRenameField(List.exactlyOne sels, s) 
    | Copy(_, _) -> Copy(List.head sels, List.exactlyOne (List.tail sels))
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
    | Index(i)::p1, All::p2 | All::p1, Index(i)::p2 -> 
        failwithf "removeSelectorPrefix - Index/All - arguably error"; loop (Index(i)::specPref) p1 p2
    | Tag(t)::p1, All::p2 | All::p1, Tag(t)::p2 -> loop (Tag(t)::specPref) p1 p2
    | All::p1, All::p2 -> loop (All::specPref) p1 p2
    | [], p2 -> Some(List.rev specPref, p2)
    | _ -> None
  loop [] p1 p2
  
let (|RemoveSelectorPrefix|_|) selbase sel = 
  removeSelectorPrefix selbase sel |> Option.map snd

let (|MatchingFirst|_|) = function 
  | All::selOther, All::selWrap -> Some(All, selOther, selWrap)
  | Field(fo)::selOther, Field(fr)::selWrap when fo = fr -> Some(Field(fo), selOther, selWrap)
  | Index(io)::selOther, Index(ir)::selWrap when io = ir -> Some(Index(io), selOther, selWrap)
  | Index(io)::selOther, All::selWrap -> Some(Index(io), selOther, selWrap)
  | Tag(tgo)::selOther, Tag(tgr)::selWrap when tgo = tgr -> Some(Tag(tgo), selOther, selWrap)
  | Tag(tgo)::selOther, All::selWrap -> Some(Tag(tgo), selOther, selWrap)
  | _ -> None

let (|IncompatibleFirst|_|) = function
  | (All|Index _|Tag _|Field _)::_, []
  | (All|Index _|Tag _)::_, Field(_)::_ 
  | Field(_)::_, (All|Index _|Tag _)::_ -> Some()
  | [], _ -> Some()
  | _ -> None

let (|TooSpecific|_|) = function
  | All::_,  (s & Index _)::_ 
  | All::_, (s & Tag _)::_ -> Some(s)
  | _ -> None 

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
  if id = "" then failwith "wrapRecordSelectors - Cannot wrap without an id"
  // Returns a modified version of 'selOther' to match
  // the additional wrapping (in a record with original at @id) at location specified by 'selWrap'
  let rec wrapsels selOther selWrap =
    match selOther, selWrap with 
    | selOther, [] -> Field(id)::selOther // interesting case here
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

let apply doc edit =
(*
  let enabled = edit.Conditions |> List.forall (function 
    | TagCondition(sel, rel, t1) -> select sel doc |> List.forall (function
        | { Expression = Record(t2, _, _) } ->
            (rel = Equals && t1 = t2) || (rel = NotEquals && t1 <> t2)        
        | _ -> rel = NotEquals )) // No tag - also passes != check
*)
  match edit.Kind with
  //| _ when not enabled ->
  //    doc

  // We can always do this, but it may add new kinds of things to a list
  // This has no effect on any selectors 
  // (But old selectors may not be compatible with the newly added thing!)
  | ListAppend(sel, nd) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> Some(List(tag, nds @ [nd]))
        | _ -> None ) doc

  // We can always do this, it has no effect on any selectors
  | PrimitiveEdit(sel, f) ->
      replace (fun p el -> 
        match el with 
        | Primitive(v) when matches p sel -> Some(Primitive(transformations.[f] v))
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
      if not (isStructuralSelector sel) then failwith $"apply.WrapRecord - Maybe allow, but do not update refs? WrapRecord with non-structural selector {sel}"
      // Do the actual record wrapping
      let doc = replace (fun p el -> 
        if matches p sel then Some(Record(tag, [id, el]))
        else None ) doc
      // Replace all relevant selectors (in references in code)
      // if notupd then doc else
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> wrapRecordSelectors id s1 sel)
      withNodeSelectors doc nsels

  // Changes structure, so only do this if selector is not value-specific
  // We need to wrap selectors in code refs 
  // (dtto.)
  | WrapList(tag, sel) ->
      if not (isStructuralSelector sel) then failwith $"apply.WrapList - Maybe allow, but do not update refs? WrapList with non-structural selector {sel}"
      // Do the actual record wrapping
      let doc = replace (fun p el -> 
        if matches p sel then Some(List(tag, [el]))
        else None ) doc
      // Replace all relevant selectors (in references in code)
      // if notupd then doc else
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> wrapListSelectors s1 sel)
      withNodeSelectors doc nsels
    
  // Changes structure, so only do this if selector is not value-specific
  // We need to update selectors in code refs  (but this is a bit experimental - changes only 'Tag' refs for lists...)
  // (dtto.)
  | UpdateTag(sel, tagOld, tagNew) ->
      if not (isStructuralSelector sel) then failwith $"apply.UpdateTag - Maybe allow, but do not update refs? UpdateTag with non-structural selector {sel}"
      let doc = replace (fun p el -> 
        match el with 
        | Record(t, nds) when matches p sel && t = tagOld -> Some(Record(tagNew, nds))
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
  | Replace(sel, nd) ->
      if not (isStructuralSelector sel) then failwith $"apply.Replace - Maybe allow, but do not update refs? Replace  with non-structural selector {sel}"
      replace (fun p el -> 
        if matches p sel then Some(nd)
        else None ) doc

  | RecordAdd(sel, fld, v) ->
      if not (isStructuralSelector sel) then failwith $"apply.RecordAdd - Maybe allow, but do not update refs? RecordAdd  with non-structural selector {sel}"
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> Some(Record(tag, nds @ [fld, v]))
        | _ -> None ) doc

  // May change structure
  // What should we do if there are selectors in the doc pointing to the copied source?
  // (duplicate something? this makes no good sense...)
  | Copy(sel1, sel2) ->
      if not (isStructuralSelector sel2) then failwith $"apply.Copy - Maybe allow, but potentially changes structure"
      let codeRefExists = getNodeSelectors doc |> List.exists (fun s1 -> includes sel1 s1)
      if codeRefExists then failwith "apply.Copy - Maybe allow, but there are refs to the source"

      // NOTE: This is a bit too clever (if there is one target, it 
      // implicitly creates list with all source nodes to be copied there)
      let mutable exprs = 
        match select sel2 doc, select sel1 doc with         
        | tgs, srcs when tgs.Length = srcs.Length -> srcs
        | [_], nds -> failwith "apply.Copy - Be too clever and autowrap target??"; [ List("div", nds) ]
        | _ -> failwith "apply.Copy - Mismatching number of source and target notes"
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy - Unexpected"
      replace (fun p el -> 
        if matches p sel2 then Some(next())
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
    match removeSelectorPrefix srcSel sel with 
    | Some(specPrefix, suffix) -> 
        tgtSel @ suffix |> substituteWithMoreSpecific specPrefix
    | _ -> sel)
  if origSels = newSels then None
  else 
    Some [e1; withSelectors newSels e1]
  
/// Returns [e1;e1'] with modified (possibly duplicated) edits
let updateSelectors e1 e2 = 
  match e2.Kind with 
  // Similar selector update is also applied when editing existing document!
  // (this logic is mirrored below in 'apply' called when applying edit)
  // Edits creating code are for now typically marked 'CanDuplicate=false' so the 
  // logic for 'Copy' is not duplicated above.
  | ListReorder(sel, ord) -> 
      let nsels = getSelectors e1 |> List.map (fun s1 -> reorderSelectors ord s1 sel)
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
  | Copy(srcSel, tgtSel) -> 
      match copyEdit e1 srcSel tgtSel with 
      | Some res -> res // when e1.CanDuplicate -> res
      | _ ->
          let target = getTargetSelector e1
          let conflict = removeSelectorPrefix srcSel target |> Option.isSome
          //if conflict && e2.IsEvaluated then failwith $"CONFLICT (but isEvaluated=true)!!!\ne1={e1}\ne2={e2}"
          //else
          if conflict then failwith $"CONFLICT!!!\ne1={e1}\ne2={e2}"
          else [e1]
    
  | Replace _ // TODO: EVALUATION?
  | UpdateTag _
  | RecordAdd _
  | PrimitiveEdit _ 
  | ListAppend _ ->
      [e1]

/// If the 'edit' is to something with a prefix specified by the selector 'selbase',
/// returns new edit that is relatively to the subtree specified by selbase 
let scopeEdit selBase edit = 
  match edit with 
  | ListAppend(RemoveSelectorPrefix selBase sel, nd) -> Some(ListAppend(sel, nd))
  | PrimitiveEdit(RemoveSelectorPrefix selBase sel, f) -> Some(PrimitiveEdit(sel, f))
  | ListReorder(RemoveSelectorPrefix selBase sel, p) -> Some(ListReorder(sel, p))
  | WrapRecord(id, tag, RemoveSelectorPrefix selBase sel) -> Some(WrapRecord(id, tag, sel))
  | Replace(RemoveSelectorPrefix selBase sel, nd) -> Some(Replace(sel, nd)) 
  | RecordAdd(RemoveSelectorPrefix selBase sel, fld, nd) -> Some(RecordAdd(sel, fld, nd))
  | UpdateTag(RemoveSelectorPrefix selBase sel, t1, t2) -> Some(UpdateTag(sel, t1, t2))
  | RecordRenameField(RemoveSelectorPrefix selBase sel, t) -> Some(RecordRenameField(sel, t))
  | Copy(RemoveSelectorPrefix selBase s1, RemoveSelectorPrefix selBase s2) -> Some(Copy(s1, s2))
  | Copy _ // TODO: failwith "scopeEdit.Copy - non-local copy - need to think about this one"
  | _ -> None

let applyToAdded e1 e2 = 
  match e1.Kind with 
  | ListAppend(sel, nd) -> 
      // We are appending under 'sel', so the selector for 
      // the node 'nd' itself will be 'sel; All' (for added field, this needs the field name)
      match scopeEdit (sel @ [All]) e2.Kind with
      | Some e2scoped ->
          //printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          { e1 with Kind = ListAppend(sel, apply nd { e2 with Kind = e2scoped }) }
      | None -> e1

  | RecordAdd(sel, fld, nd) -> 
      // TODO: Untested. Also maybe this assumes nd.ID <> ""
      match scopeEdit (sel @ [Field fld]) e2.Kind with
      | Some e2scoped ->
          //printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          { e1 with Kind = RecordAdd(sel, fld, apply nd { e2 with Kind = e2scoped }) }
      | None -> e1

  | Replace _ -> failwith "applyToAdded - Replace TODO"
  | _ -> e1

// Assuming 'e1' and 'e2' happened independently,
// modify 'e1' so that it can be placed after 'e2'.
let moveBefore e1 e2 = 
  //printfn "MOVE BEFORE"
  //printfn "move => %A" e1.Kind
  //printfn "beore => %A" e2.Kind
  let e1 = applyToAdded e1 e2
  let e1 = updateSelectors e1 e2
  e1
  
let merge e1s e2s = 
  let rec loop acc e1s e2s =
    match e1s, e2s with 
    | e1::e1s, e2::e2s when e1 = e2 -> 
        // Collect shared edits until the two histories diverge
        loop (e1::acc) e1s e2s
    | e1s, e2s ->
        // We want to modify 'e2' edits so that they can be placed after 'e1'
        // If edits in 'e2' conflict with "evaluation" edits in 'e1', remove those
        //printfn $"MERGEING! Target selectors={e2s |> List.map getTargetSelector}"
        (*
        let mutable tgtSels = e2s |> List.map getTargetSelector |> Set.ofSeq
        let e1s = e1s |> List.filter (fun e1 ->
          if not e1.IsEvaluated then true else
            let sels = getDependenciesSelectors e1
            let affected = sels |> Seq.exists (fun sel -> 
              tgtSels |> Set.exists (fun tgtSel -> Option.isSome (removeSelectorPrefix tgtSel sel)))
            if affected then 
              //printfn $"AFFECTED - {e1}"
              //printfn $"AFFECTED - target selector {getTargetSelector e1}"
              tgtSels <- tgtSels.Add(getTargetSelector e1)
              false
            else 
              //printfn $"FINE - {e1}"
              true )
        *)

        let e2sAfter = 
          e2s |> List.collect (fun e2 ->
              // For a given edit 'e2', move it before all the edits in 'e1s' using 'moveBefore'
              // (caveat is that the operation can turn it into multiple edits)
              List.fold (fun e2 e1 -> 
                e2 |> List.collect (fun e2 -> moveBefore e2 e1)) [e2] e1s )         

        (List.rev acc) @ e1s @ e2sAfter

  loop [] e1s e2s 

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

let rec evalSiteRecordChildren sels nds =
  let rec loop i = function 
    | (f, nd)::nds -> 
        match evalSite (Field f::sels) nd with 
        | Some res -> Some res
        | None -> loop (i + 1) nds
    | _ -> None
  loop 0 nds 

and evalSiteListChildren sels nds =
  let rec loop i = function 
    | nd::nds -> 
        match evalSite (Index i::sels) nd with 
        | Some res -> Some res
        | None -> loop (i + 1) nds
    | _ -> None
  loop 0 nds 

and (|EvalSiteRecordChildren|_|) sels nds = 
  evalSiteRecordChildren sels nds

and (|EvalSiteListChildren|_|) sels nds = 
  evalSiteListChildren sels nds

and evalSite sels nd : option<Selectors> =
  match nd with 
  | Primitive _ | Reference(Field "$builtins"::_) -> None
  | Reference(p) -> Some (List.rev sels)
  | Record("x-evaluated", _) -> None
  | Record("x-formula", EvalSiteRecordChildren sels res) -> Some res // Call by value - evaluate children first
  | Record("x-formula", _) -> Some(List.rev sels)
  | Record(_, EvalSiteRecordChildren sels res) -> Some res
  | List(_, EvalSiteListChildren sels res) -> Some res
  | List _ | Record _ -> None

let (|Args|) args = 
  let args = Map.ofSeq args
  args.["op"], args

let evaluateRaw nd =
  match evalSite [] nd with
  | None -> []
  | Some sels ->
      let it = match select sels nd with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sels}\n Resulted in {nds}"
      match it with 
      | Reference(p) -> 
          [ //Copy(p, sels), [TagCondition(p, NotEquals, "x-evaluated")], [p]
            //Copy(p @ [Field "result"], sels), [TagCondition(p, Equals, "x-evaluated")], [p @ [Field "result"]] 
            Copy(p, sels)
            ]
      | Record("x-formula", Args(Reference [ Field("$builtins"); Field op ], args)) ->
          let ss = args.Keys |> Seq.map (fun k -> sels @ [Field k]) |> List.ofSeq
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
          [ Replace(sels, res) ]  // Dependencies = ss
          (*
          [ WrapRecord("result", "x-evaluated", Object, sels, true), [], ss
            ListAppend(sels, { ID = "previous"; Expression = Primitive(String "na") }), [], ss
            Copy(sels @ [Field "result"], sels @ [Field "previous"]), [], ss
            Replace(sels @ [Field "result"], { ID = "result"; Expression = res } ), [], ss
            ] *)
      | Record("x-formula", nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for f, _ in nds -> f]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it}"

let evaluate nd =
  [ for ed(* conds, deps *) in evaluateRaw nd -> 
      //{ CanDuplicate = false; IsEvaluated = true; Kind = ed; Conditions = conds; Dependencies = deps } ]
      { Kind = ed } ]

let rec evaluateAll doc = seq {
  let edits = evaluate doc
  yield! edits
  let ndoc = edits |> List.fold apply doc
  if doc <> ndoc then yield! evaluateAll ndoc }

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

let rcd tag = Record(tag, [])
let lst tag = List(tag, [])
let ref sel = Reference(sel)
let nds fld tag s = Record(tag, [fld, Primitive(String s)])
let ndn fld tag n = Record(tag, [fld, Primitive(Number n)])

let ap s n = { Kind = ListAppend(s, n) } //}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let apnd s n = { Kind = ListAppend(s, n) } //}//; CanDuplicate = false; IsEvaluated = false; Conditions = []; Dependencies=[] }
let wr s fld tag = { Kind = WrapRecord(fld, tag, s) }
let wl s tag = { Kind = WrapList(tag, s) }//}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let ord s l = { Kind = ListReorder(s, l) } //CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let ed sel fn f = transformations.[fn] <- f; { Kind = PrimitiveEdit(sel, fn) } //}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let add sel f n = { Kind = RecordAdd(sel, f, n)}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let cp s1 s2 = { Kind = Copy(s1, s2)}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let tag s t1 t2 = { Kind = UpdateTag(s, t1, t2)}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }
let uid s id = { Kind = RecordRenameField(s, id)}//; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies=[] }

(*
let representSel sel = 
  Record("x-selectors", List, 
    [ for s in sel ->
        match s with 
        | All -> { ID = ""; Expression = Primitive(String "*") }
        | Index n -> { ID = ""; Expression = Primitive(Number n) }
        | Field f -> { ID = ""; Expression = Primitive(String f) } ])

let unrepresentSel expr =
  match expr with 
  | Record("x-selectors", List, sels) ->
      sels |> List.map (function 
        | { Expression = Primitive(String "*") } -> All 
        | { Expression = Primitive(String s) } -> Field s
        | { Expression = Primitive(Number n) } -> Index (int n)
        | _ -> failwith "unrepresentSel: Invalid selector")
  | _ -> failwith "unrepresentSel: Not a selector"
  

let unrepresent nd = 
  let (|Lookup|) args = dict [ for a in args -> a.ID, a ]
  let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
    if d.ContainsKey k then Some(d.[k].Expression) else None
  let editKind =
    match nd.ID, nd.Expression with
    | "x-edit-wrap", Record(_, _, Lookup args) ->
        let (|ParseKind|_|) = function "object" -> Some Object | "apply" -> Some Apply | "list" -> Some List | _ -> None
        match args with 
        | Find "tag" (Primitive(String tag)) &
          Find "id" (Primitive(String id)) &
          Find "kind" (Primitive(String(ParseKind kind))) &
          Find "target" sel ->
            EditKind.WrapRecord(tag, id, kind, unrepresentSel sel, false)
        | _ -> failwith "unrepresent - invalid arguments of x-edit-wrap"
    | "x-edit-append", Record(_, _, Lookup (Find "target" sel & Find "node" (Record(_, _, [nd])))) ->
        EditKind.ListAppend(unrepresentSel sel, nd)
    | "x-edit-updateid", Record(_, _, Lookup (Find "target" sel & Find "id" (Primitive(String id)))) ->
        EditKind.RecordRenameField(unrepresentSel sel, id) 
  { Kind = editKind}//; CanDuplicate = false; IsEvaluated = false; Conditions = []; Dependencies=[] }

let represent op = 
  let repr id kvp = 
    let args = [ for k,v in kvp -> { ID=k; Expression=v } ]
    { ID = id; Expression = Record(id, Object, args) }
  match op.Kind with 
  | EditKind.WrapRecord(tag, id, kind, target, _) ->
      let ty = match kind with Object -> "object" | Apply -> "apply" | List -> "list"
      repr "x-edit-wrap" [ 
        "tag", Primitive(String tag); "id", Primitive(String id)
        "kind", Primitive(String ty); "target", representSel target 
      ]
  | EditKind.ListAppend(target, nd) ->
      repr "x-edit-append" [
        "target", representSel target; "node", Record("x-node-wrapper", Object, [nd])
      ]
  | EditKind.RecordRenameField(target, id) ->
      repr "x-edit-updateid" [
        "target", representSel target; "id", Primitive(String id)
      ]
     *) 
     (*
let opsBaseCounter = 
  [ 
    ap [] (nds "title" "h1" "Counter")
    ap [] (rcd "counter" "p")
    ap [Field "counter"] (nds "label" "strong" "Count: ")
    ap [Field "counter"] (ndnp "value" 0)
    ap [] (nds "inc" "button" "Increment")
    ap [] (nds "dec" "button" "Decrement")
  ]
let opsCounterInc = 
  [
    wr [Field "counter"; Field "value"] Apply "value" "span"
    ap [Field "counter"; Field "value"] (ref "op" [Field "$builtins"; Field "+"])
    ap [Field "counter"; Field "value"] (ndnp "left" 1)
    uid [Field "counter"; Field "value"; Field "value"] "right"
  ]
let opsCounterDec = 
  [
    wr [Field "counter"; Field "value"] Apply "value" "span"
    ap [Field "counter"; Field "value"] (ref "op" [Field "$builtins"; Field "+"])
    ap [Field "counter"; Field "value"] (ndnp "left" -1)
    uid [Field "counter"; Field "value"; Field "value"] "right"
  ]
let opsCounterHndl = 
  [ yield ap [Field "inc"] (lst "click" "x-event-handler")
    for op in opsCounterInc ->
      ap [Field "inc"; Field "click"] (represent op) 
    yield ap [Field "dec"] (lst "click" "x-event-handler")
    for op in opsCounterDec ->
      ap [Field "dec"; Field "click"] (represent op) ]



let addSpeakerOps = 
  [ 
    ap [Field "speakers"] (nds "" "li" "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ord [Field "speakers"] [3; 0; 1; 2] 
  ]

let fixSpeakerNameOps = 
  [
    ed [Field("speakers"); Index(2); Field("value")] "rename Jean" <| fun s -> 
      s.Replace("Betty Jean Jennings", "Jean Jennings Bartik").Replace("betty@", "jean@")
  ]

let refactorListOps = 
  [
    uid [Field "speakers"; All; Field "value"] "name"
    wr [Field "speakers"; All; Field "name"] Object "contents" "td"
    add [Field "speakers"; All] (nds "email" "td" "")
    tag [Field "speakers"; All] "tr"
    tag [Field "speakers"] "tbody"
    
    wr [Field "speakers"] Object "body" "table"
    add [Field "speakers"] (rcd "head" "thead")
    add [Field "speakers"; Field "head"] (nds "name" "td" "Name")
    add [Field "speakers"; Field "head"] (nds "email" "td" "E-mail")

    cp [Field "speakers"; Field "body"; All; Field "name"] [Field "speakers"; Field "body"; All; Field "email"]
    ed [Field "speakers"; Field "body"; All; Field "name"; Field "contents"] "get name" <| fun s -> 
      s.Substring(0, s.IndexOf(','))
    ed [Field "speakers"; Field "body"; All; Field "email"; Field "contents"] "get email" <| fun s -> 
      s.Substring(s.IndexOf(',')+1).Trim()
  ]

let addTransformOps = 
  [
    ap [] (nds "ttitle" "h2" "Transformers")
    add [] (rcd "x-patterns" "x-patterns")
    add [ Field "x-patterns"] (rcd "head" "thead")
    add [ Field "x-patterns"; Field "head" ] (rcd "*" "td")
    add [ Field "x-patterns"; Field "head"; Field "*" ] (rcd "*" "x-hole")
    add [ Field "x-patterns"; Field "head"; Field "*"; Field "*" ] (rcd "mq" "marquee")
    add [ Field "x-patterns"; Field "head"; Field "*"; Field "*"; Field "mq" ] (rcd "" "x-match")
  ] 
  *)
let opsCore = 
  [
    add [] "" (nds "title" "h1" "Programming conference 2023")
    add [] "" (nds "stitle" "h2" "Speakers")
    add [] "speakers" (lst "ul")
    ap [Field "speakers"] (nds "" "li" "Adele Goldberg, adele@xerox.com") 
    ap [Field "speakers"] (nds "" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap [Field "speakers"] (nds "" "li" "Betty Jean Jennings, betty@rand.com") 
  ]
  (*
let opsBudget = 
  [
    ap [] (nds "btitle" "h2" "Budgeting")
    ap [] (nds "ntitle" "h3" "Number of people")
    ap [] (rcd "counts" "ul")
    ap [Field "counts"] (nds "attendees" "span" "Attendees: ") 
    wr [Field "counts"; Field "attendees"] Object "" "li"
    ap [Field "counts"; Field "attendees"] (ndn "count" "strong" 100)
    ap [Field "counts"] (nds "speakers" "span" "Speakers: ") 
    wr [Field "counts"; Field "speakers"] Object "" "li"
    apnd [Field "counts"; Field "speakers"] (ref "count" [Field "speakers"; All])
    wr [Field "counts"; Field "speakers"; Field "count"] Apply "arg" "span"
    ap [Field "counts"; Field "speakers"; Field "count"] (ref "op" [Field "$builtins"; Field "count"])

    ap [] (nds "ititle" "h3" "Item costs")
    ap [] (rcd "costs" "ul")
    ap [Field "costs"] (nds "travel" "span" "Travel per speaker: ") 
    wr [Field "costs"; Field "travel"] Object "" "li"
    ap [Field "costs"; Field "travel"] (ndn "cost" "strong" 1000)
    ap [Field "costs"] (nds "coffee" "span" "Coffee break per person: ") 
    wr [Field "costs"; Field "coffee"] Object "" "li"
    ap [Field "costs"; Field "coffee"] (ndn "cost" "strong" 5)
    ap [Field "costs"] (nds "lunch" "span" "Lunch per person: ") 
    wr [Field "costs"; Field "lunch"] Object "" "li"
    ap [Field "costs"; Field "lunch"] (ndn "cost" "strong" 20)
    ap [Field "costs"] (nds "dinner" "span" "Dinner per person: ") 
    wr [Field "costs"; Field "dinner"] Object "" "li"
    ap [Field "costs"; Field "dinner"] (ndn "cost" "strong" 80)
    
    ap [] (nds "ttitle" "h3" "Total costs")
    ap [] (lst "totals" "ul")

    // NOTE: Construct things in a way where all structural edits (wrapping)
    // are applied to the entire list using All (this should be required!)
    // because otherwise we may end up with inconsistent structures
    ap [Field "totals"] (nds "" "span" "Refreshments: ") 
    ap [Field "totals"] (nds "" "span" "Speaker travel: ") 
    wr [Field "totals"; All] Object "" "li"
    ap [Field "totals"; Index 0] (ref "item" [Field "costs"; Field "coffee"; Field "cost"; Field "value"])
    ap [Field "totals"; Index 1] (ref "item" [Field "costs"; Field "travel"; Field "cost"; Field "value"])
    wr [Field "totals"; All; Field "item"] Apply "left" "span"
    ap [Field "totals"; Index 0; Field "item"] (ref "right" [Field "counts"; Field "attendees"; Field "count"; Field "value"])
    ap [Field "totals"; Index 1; Field "item"] (ref "right" [Field "counts"; Field "speakers"; Field "count"])
    ap [Field "totals"; Index 0; Field "item"] (ref "op" [Field "$builtins"; Field "*"])
    ap [Field "totals"; Index 1; Field "item"] (ref "op" [Field "$builtins"; Field "*"])
    wr [Field "totals"; All; Field "item"] Object "value" "strong"
    
    ap [] (nds "ultimate" "h3" "Total: ") 
    wr [Field "ultimate" ] Object "" "span"
    ap [Field "ultimate" ] (ref "item" [Field "totals"; All; Field "item"; Field "value"])
    wr [Field "ultimate"; Field "item"] Apply "arg" "span"
    ap [Field "ultimate"; Field "item"] (ref "op" [Field "$builtins"; Field "sum"])
  ]
  *)