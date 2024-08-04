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

let trace sel doc = 
  let rec loop trace sel nd = seq {
    match nd, sel with 
    | nd, [] -> yield nd, List.rev trace
    | List(_, els), (Index(i) as s)::sel -> 
        yield! loop ((nd, s)::trace) sel els.[i]
    | List(_, els), (Tag(t) as s)::sel -> 
        let els = els |> List.filter (function Record(t2, _) | List(t2, _) -> t2 = t | _ -> false)
        for el in els do yield! loop ((nd, s)::trace) sel el
    | List(_, els), (All as s)::sel -> 
        for el in els do yield! loop ((nd, s)::trace) sel el
    | Record(_, els), (Field(f) as s)::sel -> 
        yield! loop ((nd, s)::trace) sel (snd (List.find (fst >> (=) f) els)) 
    | _ -> ()  }
  loop [] sel doc 

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
  
let (|ScopeSelector|_|) selbase sel = 
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

let apply doc edit =
  match edit.Kind with
  //| _ when not (enabled doc edit) ->
    //  doc

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

  // Changes structure, so only do this if selector is not value-specific
  // Additive so no need to update references
  | RecordAdd(sel, fld, v) ->
      // NOTE: Allowing this, otherwise we cannot construct a list of formulas!
      // (but the operation creates a heterogeneous list temporarily...)
      //
      // if not (isStructuralSelector sel) then failwith $"apply.RecordAdd - Maybe allow, but do not update refs? RecordAdd  with non-structural selector {sel}"
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> 
            let nds = nds |> List.filter (fun (k, _) -> k <> fld)
            Some(Record(tag, nds @ [fld, v]))
        | _ -> None ) doc

  // May change structure
  // What should we do if there are selectors in the doc pointing to the copied source?
  // (duplicate something? this makes no good sense...)
  | Copy(sel1, sel2) ->
      if not (isStructuralSelector sel2) then 
        ()
        // NOTE: As below - this potentially changes the structure of the target list
        // but we need to allow this so that we can evaluate lists of formulas!
        // failwith $"apply.Copy - Maybe allow, but potentially changes structure"
      let codeRefExists = getNodeSelectors doc |> List.exists (fun s1 -> includes sel1 s1)
      if codeRefExists then 
        // NOTE: What to do if there are refs to the source in the document?
        // For now, allow, because we need to allow this for "transient" evaluated edits!
        () //failwith "apply.Copy - Maybe allow, but there are refs to the source"

      let sel2, exprs = 
        match select sel2 doc, select sel1 doc with         
        | tgs, srcs when tgs.Length = srcs.Length -> sel2, srcs

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
        | [List(t, _)], nds -> sel2, [List(t, nds)]
        | [tgt], nds -> 
            failwith $"apply.Copy - Be too clever and autowrap target?? sel2={sel2}"; 

        | _ -> failwith "apply.Copy - Mismatching number of source and target notes"

      let mutable exprs = exprs
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
      //printfn "======%A========" (getSelectors e1)
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
  | ListAppend(ScopeSelector selBase sel, nd) -> Some(ListAppend(sel, nd))
  | PrimitiveEdit(ScopeSelector selBase sel, f) -> Some(PrimitiveEdit(sel, f))
  | ListReorder(ScopeSelector selBase sel, p) -> Some(ListReorder(sel, p))
  | WrapRecord(id, tag, ScopeSelector selBase sel) -> Some(WrapRecord(id, tag, sel))
  | Replace(ScopeSelector selBase sel, nd) -> Some(Replace(sel, nd)) 
  | RecordAdd(ScopeSelector selBase sel, fld, nd) -> Some(RecordAdd(sel, fld, nd))
  | UpdateTag(ScopeSelector selBase sel, t1, t2) -> Some(UpdateTag(sel, t1, t2))
  | RecordRenameField(ScopeSelector selBase sel, t) -> Some(RecordRenameField(sel, t))
  | Copy(ScopeSelector selBase s1, ScopeSelector selBase s2) -> Some(Copy(s1, s2))
  | Copy(s1, s2) -> 
      match removeSelectorPrefix selBase s1, removeSelectorPrefix selBase s2 with
      | None, None -> 
          // Both are source and target of the copy are outside of the location 
          // where we are adding something, so we can happily skip the Copy edit
          None
      | _ ->
        failwith $"scopeEdit.Copy - non-local copy - need to think about this one: BASE={selBase}, EDIT={edit}"
  
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

let (|ListFind|_|) k = List.tryFind (fst >> (=) k)

let evaluateRaw doc =
  match evalSite [] doc with
  | None -> []
  | Some sels ->
      let it = match select sels doc with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sels}\n Resulted in {nds}"
      match it with 
      | Reference(p) -> 
          [ //Copy(p, sels), [TagCondition(p, NotEquals, "x-evaluated")], [p]
            //Copy(p @ [Field "result"], sels), [TagCondition(p, Equals, "x-evaluated")], [p @ [Field "result"]] 
            WrapRecord("ref", "x-evaluated", sels)
            RecordAdd(sels, "result", List("ul", []))
            Copy(p, sels @ [Field "result"]) //, [SelectorHashEquals(p, hash (select p doc))]
            

            ]
      | Record("x-formula", Args(Reference [ Field("$builtins"); Field op ], args)) ->
          // Used previously for dependencies - now not needed
          // let ss = args.Keys |> Seq.map (fun k -> sels @ [Field k]) |> List.ofSeq

          let args = args |> Map.map (fun _ v ->
            match v with 
            | Record("x-evaluated", ListFind "result" r) -> snd r
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
          [ Replace(sels, res) ]//, [] ]  // Dependencies = ss
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
  [ for ed(*, conds, deps *) in evaluateRaw doc -> 
      //{ CanDuplicate = false; IsEvaluated = true; Kind = ed; Conditions = conds; Dependencies = deps } ]
      { Kind = ed } ]

let rec evaluateAll doc = seq {
  let edits = evaluateDoc doc
  yield! edits
  let ndoc = edits |> List.fold apply doc
  if doc <> ndoc then yield! evaluateAll ndoc }

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
  | _ -> failwith "unrepresentSel: Not a selector"
  

let unrepresent nd = 
  let (|Lookup|) args = dict args
  let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
    if d.ContainsKey k then Some(d.[k]) else None
  let (|Finds|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
    match d.TryGetValue(k) with true, Primitive(String s) -> Some s | _ -> None
  let editKind =
    match nd with
    | Record("x-edit-wraprec", Lookup(Finds "tag" tag & Finds "id" id & Find "target" target)) ->
        EditKind.WrapRecord(tag, id, unrepresentSel target)
    | Record("x-edit-append", Lookup (Find "target" sel & Find "node" (Record(_, [_, nd])))) ->
        EditKind.ListAppend(unrepresentSel sel, nd)
    | Record("x-edit-add", Lookup (Find "target" sel & Finds "field" f & Find "node" (Record(_, [_, nd])))) ->
        EditKind.RecordAdd(unrepresentSel sel, f, nd)
    | Record("x-edit-updateid", Lookup (Find "target" sel & Finds "id" id)) ->
        EditKind.RecordRenameField(unrepresentSel sel, id) 
    | _ -> failwith $"unrepresent - Missing case for: {nd}"
  { Kind = editKind }


let represent op = 
  let repr id kvp = Record(id, kvp)
  let ps v = Primitive(String v)
  match op.Kind with 
  | EditKind.WrapRecord(tag, id, target) ->
      [ "tag", ps tag; "id", ps id; "target", representSel target ] 
      |> repr "x-edit-wraprec"
  | EditKind.ListAppend(target, nd) ->
      [ "target", representSel target; "node", Record("x-node-wrapper", ["it", nd]) ]
      |> repr "x-edit-append"
  | EditKind.RecordAdd(target, f, nd) ->
      [ "target", representSel target; "field", ps f; "node", Record("x-node-wrapper", ["it", nd]) ]
      |> repr "x-edit-add"
  | EditKind.RecordRenameField(target, id) ->
      [ "target", representSel target; "id", ps id ]
      |> repr "x-edit-updateid"
  | _ -> failwith $"represent - Missing case for: {op.Kind}"