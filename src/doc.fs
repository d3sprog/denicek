module Tbd.Doc

// TODO: Right now, we always identify 'Object' members by field
// and 'List' members by 'Index' but those are not so different and
// we could also use indexing into objects (which would mean not
// all fields would need to have an id). But this requires changing
// 'match' below and path recording in 'replace' and 'fold'.

type Selector = 
  | All
  | Field of string
  | Index of int 

type Selectors = Selector list

type Primitive =
  | Number of float
  | String of string

type Node = 
  { ID : string
    Expression : Expr
    Previous : Node option 
    }

and RecordType = 
  | List | Object | Apply

and Expr = 
  | Record of string * RecordType * list<Node>
  | Primitive of Primitive
  | Reference of Selectors

let transformations = System.Collections.Generic.Dictionary<string, string -> string>()

// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------

let replace recordHistory f nd = 
  let rec loop path nd =
    match f path nd with 
    | Some res when recordHistory -> { res with Previous = Some nd }
    | Some res -> res
    | _ -> 
    let rtrn e = { nd with Expression = e }
    match nd.Expression with 
    | Record(tag, typ, attrs) -> 
        Record(tag, typ, List.mapi (fun i nd -> 
          let sel = if typ = List then Index(i) else Field(nd.ID)
          loop (path @ [sel]) nd) attrs) |> rtrn
    | Reference _ | Primitive _ -> nd 
  loop [] nd

let fold f st value = 
  let rec loop path st nd =
    //match nd.Evaluated with 
    //| Some nd -> loop path st nd
    //| _ -> 
    let st = f path nd st 
    match nd.Expression with 
    | Record(tag, typ, nds) -> 
        nds |> List.indexed |> List.fold (fun st (i, nd) -> 
          let sel = if typ = List then Index(i) else Field(nd.ID)
          loop (path @ [sel]) st nd) st
    | Primitive _ | Reference _ -> 
        st
  loop [] st value

let rec matches p1 p2 = 
  match p1, p2 with 
  | [], [] -> true
  | [], _ | _, [] -> false
  | Field(f1)::p1, Field(f2)::p2 -> f1 = f2 && matches p1 p2
  | Index(i1)::p1, Index(i2)::p2 -> i1 = i2 && matches p1 p2
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 -> matches p1 p2
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

type EditKind = 
  | Append of Selectors * Node
  | EditText of Selectors * string //(string -> string)
  | Reorder of Selectors * list<int>
  | Copy of source:Selectors * target:Selectors 
  | WrapRecord of id:string * tag:string * kind:RecordType * target:Selectors 
  | Replace of target:Selectors * dependencies:Selectors list * Node
  | AddField of Selectors * Node
  | UpdateTag of Selectors * string
  | UpdateId of Selectors * string

type Edit = 
  { Kind : EditKind 
    IsEvaluated : bool
    CanDuplicate : bool }

// --------------------------------------------------------------------------------------
// Merge and apply helpers
// --------------------------------------------------------------------------------------

let rec getNodeSelectors = function
  | { Expression = Record(_, _, nds) } -> List.collect getNodeSelectors nds
  | { Expression = Reference sels } -> [sels]
  | { Expression = Primitive _ } -> []

let withNodeSelectors nd sels = 
  let mutable sels = sels
  let next() = let r = List.head sels in sels <- List.tail sels; r
  let rec loop nd = 
    match nd with 
    | { Expression = Record(tag, typ, nds) } -> { nd with Expression = Record(tag, typ, List.map loop nds) }
    | { Expression = Reference sels } -> { nd with Expression = Reference(next()) }
    | { Expression = Primitive _ } -> nd
  loop nd

let getSelectors ed = 
  match ed.Kind with 
  | EditText(s, _) | Reorder(s, _) | UpdateId(s, _) | UpdateTag(s, _) | WrapRecord(_, _, _, s) -> [s]
  | Append(s, nd) | Replace(s, _, nd) | AddField(s, nd) -> s :: (getNodeSelectors nd)
  | Copy(s1, s2) -> [s1; s2]

/// Not including 'Reference' selectors in expressions
let getDependenciesSelectors ed = 
  match ed.Kind with 
  | EditText(s, _) | Reorder(s, _) | UpdateId(s, _) | UpdateTag(s, _) | WrapRecord(_, _, _, s) 
  | Append(s, _) | AddField(s, _) -> [s]
  | Replace(s, ss, _) -> s::ss
  | Copy(s1, s2) -> [s1; s2]

let getTargetSelector ed = 
  match ed.Kind with 
  | EditText(s, _) | Reorder(s, _) | UpdateId(s, _) | UpdateTag(s, _) | Replace(s, _, _) | Copy(_, s) -> s
  | WrapRecord(_, id, _, s) | AddField(s, { ID = id }) -> s @ [Field id]
  | Append(s, _)-> s @ [All]

let withTargetSelector tgt ed = 
  let dropLast (tgt:_ list) = tgt.[0 .. tgt.Length - 2] // Remove the last, added in 'getTargetSelector'
  let nkind =
    match ed.Kind with 
    | Append(_, nd) -> Append(dropLast tgt, nd) 
    | AddField(_, nd) -> AddField(dropLast tgt, nd) 
    | Replace(_, ss, nd) -> Replace(tgt, ss, nd) 
    | EditText(_, f) -> EditText(tgt, f)
    | Reorder(_, m) -> Reorder(tgt, m)
    | WrapRecord(t, i, k, _) -> WrapRecord(t, i, k, dropLast tgt) 
    | UpdateTag(_, t) -> UpdateTag(tgt, t) 
    | UpdateId(_, s) -> UpdateTag(tgt, s) 
    | Copy(_, s) -> Copy(tgt, s)
  { ed with Kind = nkind }

let withSelectors sels ed =
  let nkind =
    match ed.Kind with 
    | Append(_, nd) -> Append(List.head sels, withNodeSelectors nd (List.tail sels)) 
    | AddField(_, nd) -> AddField(List.head sels, withNodeSelectors nd (List.tail sels)) 
    | Replace(_, ss, nd) -> Replace(List.head sels, ss, withNodeSelectors nd (List.tail sels)) 
    | EditText(_, f) -> EditText(List.exactlyOne sels, f)
    | Reorder(_, m) -> Reorder(List.exactlyOne sels, m)
    | WrapRecord(t, i, k, _) -> WrapRecord(t, i, k, List.exactlyOne sels) 
    | UpdateTag(_, t) -> UpdateTag(List.exactlyOne sels, t) 
    | UpdateId(_, s) -> UpdateId(List.exactlyOne sels, s) 
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
    // TODO: Arguably, we should not insert into specific index (only All) as that is a 'type error'
    // Meaning that when called from 'scopeEdit', then 'p1' should not contain 'Index' ?
    | Index(i)::p1, All::p2 | All::p1, Index(i)::p2 -> loop (Index(i)::specPref) p1 p2
    | All::p1, All::p2 -> loop (All::specPref) p1 p2
    | [], p2 -> Some(List.rev specPref, p2)
    | _ -> None
  loop [] p1 p2
  
let (|RemoveSelectorPrefix|_|) selbase sel = 
  removeSelectorPrefix selbase sel |> Option.map snd

let reorderSelectors ord selOther selReord = 
  // Returns a modified version of 'selOther' to match
  // reordering of indices 'ord' at location specified by 'selReord'
  let rec reorder selOther selReord =
    match selOther, selReord with 
    | All::selOther, All::selReord -> All::(reorder selOther selReord)
    | Field(fo)::selOther, Field(fr)::selReord when fo = fr -> Field(fo)::(reorder selOther selReord)
    | Field(_)::_, _ -> selOther
    | Index(io)::selOther, Index(ir)::selReord when io = ir -> Index(io)::(reorder selOther selReord)
    | Index(io)::selOther, All::selReord -> Index(io)::(reorder selOther selReord)
    | Index(io)::selOther, [] -> Index(List.findIndex ((=) io) ord)::selOther
    | All::selOther, [] -> All::selOther
    | All::selOther, Index(i)::selReorder -> failwith "moveBefore.Reorder - Too specific reordering! Not sure what to do. See RANDOM NOTES in datatype-edits.fsx"
    | (All|Index _)::_, Field(_)::_ 
    | Field(_)::_, (All|Index _)::_ -> selOther        
    | [], _ -> []
    | _ -> failwith $"moveBefore.Reorder - Missing case: {selOther} vs. {selReord}"
  reorder selOther selReord

let wrapSelectors typ id tag selOther selReord =
  // Returns a modified version of 'selOther' to match
  // the additional wrapping at location specified by 'selReord'
  let rec wrapsels selOther selReord =
    match selOther, selReord with 
    | Field(fo)::selOther, Field(fr)::selReord when fo = fr -> Field(fo)::(wrapsels selOther selReord)
    | Field(_)::_, _ -> selOther
    | All::selOther, All::selReord -> All::(wrapsels selOther selReord)
    | Index(io)::selOther, Index(ir)::selReord when io = ir -> Index(io)::(wrapsels selOther selReord)
    | Index(io)::selOther, All::selReord -> Index(io)::(wrapsels selOther selReord)
    | selOther, [] when typ <> Object || tag = "" -> failwith $"moveBefore.WrapRecord - Cannot add field ref for non-object or wrap without a name! c.f. {(typ,id,tag,selOther)}"
    | selOther, [] -> Field(id)::selOther
    | (All|Index _)::_, Field(_)::_ 
    | Field(_)::_, (All|Index _)::_ -> selOther        
    | [], _ -> []
    | _ -> failwith $"moveBefore.WrapCase - Missing case: {selOther} vs. {selReord}"
  wrapsels selOther selReord

let updateSelectorsId id selOther selReord =
  // Returns a modified version of 'selOther' to match
  // the changed ID at location specified by 'selReord'
  // NOTE: Pretty much the same as above, except for the removed "selOther, []" cases
  // and added "Rename ID" case
  let rec reidsels selOther selReord =
    match selOther, selReord with 
    | Field(fo)::selOther, Field(fr)::[] when fo = fr -> Field(id)::(reidsels selOther []) // Rename ID in the selector!
    | Field(fo)::selOther, Field(fr)::selReord when fo = fr -> Field(fo)::(reidsels selOther selReord)
    | Field(_)::_, _ -> selOther
    | All::selOther, All::selReord -> All::(reidsels selOther selReord)
    | Index(io)::selOther, Index(ir)::selReord when io = ir -> Index(io)::(reidsels selOther selReord)
    | Index(io)::selOther, All::selReord -> Index(io)::(reidsels selOther selReord)
    | (All|Index _)::_, Field(_)::_ 
    | Field(_)::_, (All|Index _)::_ -> selOther        
    | [], _ -> []
    | _ -> failwith $"moveBefore.WrapCase - Missing case: {selOther} vs. {selReord}"
  reidsels selOther selReord

// --------------------------------------------------------------------------------------
// Apply
// --------------------------------------------------------------------------------------

let apply doc edit =
  match edit.Kind with
  | Append(sel, nd) ->
      replace edit.IsEvaluated (fun p el ->
        match el.Expression with 
        | Record(tag, typ, nds) when matches p sel -> 
            Some { el with Expression = Record(tag, typ, nds @ [nd]) }
        | _ -> None ) doc

  | EditText(sel, f) ->
      replace edit.IsEvaluated (fun p el -> 
        match el.Expression with 
        | Primitive(String(s)) when matches p sel -> 
            Some { el with Expression = Primitive(String(transformations.[f] s)) }
        | _ -> None ) doc

  // The next two also need to fix selectors in code references
  // (this logic is mirrored below in 'updateSelectors' called when merging)
  | Reorder(sel, ord) ->
      // Do the actual reordering 
      let doc = replace edit.IsEvaluated (fun p el ->
        match el.Expression with 
        | Record(tag, typ, vals) when matches p sel -> 
            Some { el with Expression = Record(tag, typ, [ for i in ord -> vals.[i]]) }
        | _ -> None ) doc
      // Replace all relevant selectors (in references in code)
      // NOTE: This is untested, but may work.
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> reorderSelectors ord s1 sel)
      withNodeSelectors doc nsels

  | WrapRecord(id, tag, typ, sel) ->
      // Do the actual record wrapping
      let doc = replace edit.IsEvaluated (fun p el -> 
        if matches p sel then Some { el with Expression = Record(tag, typ, [{ el with ID = id }]) }
        else None ) doc
      // Replace all relevant selectors (in references in code)
      let nsels = getNodeSelectors doc |> List.map (fun s1 -> wrapSelectors typ id tag s1 sel)
      withNodeSelectors doc nsels

  | Copy(sel1, sel2) ->
      // NOTE: This is a bit too clever (if there is one target, it 
      // implicitly creates list with all source nodes to be copied there)
      let mutable exprs = 
        match select sel2 doc, select sel1 doc with         
        | tgs, srcs when tgs.Length = srcs.Length -> [ for s in srcs -> s.Expression ]
        | [_], nds -> [ Record("div", List, nds) ]
        | _ -> failwith "apply.Copy: Mismatching number of source and target notes"
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy: Unexpected"
      replace edit.IsEvaluated (fun p el -> 
        if matches p sel2 then Some({ el with Expression = next() })
        else None ) doc

  | UpdateTag(sel, tag) ->
      replace edit.IsEvaluated (fun p el -> 
        match el with 
        | { Expression = Record(_, typ, nds) } when matches p sel -> 
            Some({ el with Expression = Record(tag, typ, nds)})
        | _ -> None ) doc

  | UpdateId(sel, id) ->
      replace edit.IsEvaluated (fun p el -> 
        if matches p sel then Some { el with ID = id } else None) doc

  | Replace(sel, _, nd) ->
      replace edit.IsEvaluated (fun p el -> 
        if matches p sel then Some(nd)
        else None ) doc

  | AddField(sel, v) ->
      replace edit.IsEvaluated (fun p el -> 
        match el.Expression with 
        | Record(tag, Object, attrs) when matches p sel -> Some({ el with Expression = Record(tag, Object, attrs @ [v]) })
        | _ -> None ) doc

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
  | Reorder(sel, ord) -> 
      let nsels = getSelectors e1 |> List.map (fun s1 -> reorderSelectors ord s1 sel)
      [withSelectors nsels e1]
  | WrapRecord(id, tag, typ, sel) -> 
      let nsels = getSelectors e1 |> List.map (fun s1 -> wrapSelectors typ id tag s1 sel)
      [withSelectors nsels e1]
  | UpdateId(sel, id) ->
      let nsels = getSelectors e1 |> List.map (fun s1 -> updateSelectorsId id s1 sel)
      [withSelectors nsels e1]
  | Copy(srcSel, tgtSel) -> 
      match copyEdit e1 srcSel tgtSel with 
      | Some res when e1.CanDuplicate -> res
      | _ ->
          let target = getTargetSelector e1
          let conflict = removeSelectorPrefix srcSel target |> Option.isSome
          if conflict && e2.IsEvaluated then failwith $"CONFLICT (but isEvaluated=true)!!!\ne1={e1}\ne2={e2}"
          elif conflict then failwith $"CONFLICT!!!\ne1={e1}\ne2={e2}"
          else [e1]
    
  | Replace _ // TODO: EVALUATION?
  | UpdateTag _
  | AddField _
  | EditText _ 
  | Append _ ->
      [e1]

/// If the 'edit' is to something with a prefix specified by the selector 'selbase',
/// returns new edit that is relatively to the subtree specified by selbase 
let scopeEdit selBase edit = 
  match edit with 
  | Append(RemoveSelectorPrefix selBase sel, nd) -> Some(Append(sel, nd))
  | EditText(RemoveSelectorPrefix selBase sel, f) -> Some(EditText(sel, f))
  | Reorder(RemoveSelectorPrefix selBase sel, p) -> Some(Reorder(sel, p))
  | WrapRecord(id, tag, typ, RemoveSelectorPrefix selBase sel) -> Some(WrapRecord(id, tag, typ, sel))
  | Replace(RemoveSelectorPrefix selBase sel, ss, nd) -> Some(Replace(sel, ss, nd)) 
  | AddField(RemoveSelectorPrefix selBase sel, nd) -> Some(AddField(sel, nd))
  | UpdateTag(RemoveSelectorPrefix selBase sel, t) -> Some(UpdateTag(sel, t))
  | UpdateId(RemoveSelectorPrefix selBase sel, t) -> Some(UpdateId(sel, t))
  | Copy(RemoveSelectorPrefix selBase s1, RemoveSelectorPrefix selBase s2) -> Some(Copy(s1, s2))
  | Copy _ // TODO: failwith "scopeEdit.Copy - non-local copy - need to think about this one"
  | _ -> None

let applyToAdded e1 e2 = 
  match e1.Kind with 
  | Append(sel, nd) -> 
      // We are appending under 'sel', so the selector for 
      // the node 'nd' itself will be 'sel; All' (for added field, this needs the field name)
      match scopeEdit (sel @ [All]) e2.Kind with
      | Some e2scoped ->
          //printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          { e1 with Kind = Append(sel, apply nd { e2 with Kind = e2scoped }) }
      | None -> e1

  | AddField(sel, nd) -> 
      // TODO: Untested. Also maybe this assumes nd.ID <> ""
      match scopeEdit (sel @ [Field nd.ID]) e2.Kind with
      | Some e2scoped ->
          //printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          { e1 with Kind = AddField(sel, apply nd { e2 with Kind = e2scoped }) }
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

let (|Args|) args = 
  let args = Map.ofSeq [ for arg in args -> arg.ID, arg ]
  args.["op"], args

let rec evalSiteChildren sels typ nds =
  let rec loop i = function 
    | nd::nds -> 
        let sel = if typ = List then Index(i) else Field(nd.ID)
        match evalSite (sel::sels) nd with 
        | Some res -> Some res
        | None -> loop (i + 1) nds
    | _ -> None
  loop 0 nds 

and evalSite sels nd : option<Selectors> =
  match nd.Expression with 
  | Primitive _ | Reference(Field "$builtins"::_) -> None
  | Reference(p) -> Some (List.rev sels)
  | Record(_, typ, nds) -> 
      match typ, evalSiteChildren sels typ nds with
      | _, Some res -> Some res
      | Object, None | List, None -> None
      | _ -> Some(List.rev sels)

let evaluateRaw nd = //: int list =
  match evalSite [] nd with
  | None -> []
  | Some sels ->
      let it = match select sels nd with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sels}\n Resulted in {nds}"
      match it.Expression with 
      | Reference(p) -> [ Copy(p, sels) ]  
      | Record(_, Apply, Args({ Expression = Reference [ Field("$builtins"); Field op ] }, args)) ->
          let ss = args.Keys |> Seq.map (fun k -> sels @ [Field k]) |> List.ofSeq
          match op with 
          | "count" | "sum" ->
              let sum = List.map (function { Expression = Primitive(Number n) } -> n | _ -> failwith "evaluate: Argument of 'sum' is not a number.") >> List.sum 
              let count = List.length >> float
              let f = (dict [ "count", count; "sum", sum ]).[op]
              match args.TryFind "arg" with
              | Some { Expression = Record(_, List, nds) } -> 
                  let res = Primitive(Number(f nds))
                  [ Replace(sels, ss, { it with Expression = res } )  ] 
              | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."
          | "+" | "*" -> 
              let f = (dict [ "+",(+); "*",(*) ]).[op]
              match args.TryFind "left", args.TryFind "right" with
              | Some { Expression = Primitive(Number n1) },
                Some { Expression = Primitive(Number n2) } -> 
                  let res = Primitive(Number(f n1 n2))
                  [ Replace(sels, ss, { it with Expression = res } )  ] 
              | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
          | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"      
      | Record(_, Apply, nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for nd in nds -> nd.ID]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it.Expression}"

let evaluate nd =
  [ for ed in evaluateRaw nd -> { CanDuplicate = false; IsEvaluated = true; Kind = ed } ]

let rec evaluateAll doc = seq {
  let edits = evaluate doc
  yield! edits
  let ndoc = edits |> List.fold apply doc
  if doc <> ndoc then yield! evaluateAll ndoc }

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

let rcd id tag = 
  { ID = id; Expression = Record(tag, Object, []); Previous = None }
let lst id tag = 
  { ID = id; Expression = Record(tag, List, []); Previous = None }

let wrap id tag nd =
  { ID = id; Expression = Record(tag, Object, [nd]); Previous = None }  
let ref id sel = 
  { ID = id; Expression = Reference(sel); Previous = None }
let nds id tag s = 
  wrap id tag { ID = "value"; Expression = Primitive(String s); Previous = None }
let ndn id tag n = 
  wrap id tag { ID = "value"; Expression = Primitive(Number n); Previous = None }
let ndnp id n = 
  { ID = id; Expression = Primitive(Number n); Previous = None }

let ap s n = { Kind = Append(s, n); CanDuplicate = true; IsEvaluated = false }
let apnd s n = { Kind = Append(s, n); CanDuplicate = false; IsEvaluated = false }
let wr s typ id tag = { Kind = WrapRecord(id, tag, typ, s); CanDuplicate = true; IsEvaluated = false }
let ord s l = { Kind = Reorder(s, l); CanDuplicate = true; IsEvaluated = false }
let ed sel fn f = transformations.[fn] <- f; { Kind = EditText(sel, fn); CanDuplicate = true; IsEvaluated = false }
let add sel n = { Kind = AddField(sel, n); CanDuplicate = true; IsEvaluated = false }
let cp s1 s2 = { Kind = Copy(s1, s2); CanDuplicate = true; IsEvaluated = false }
let tag s t = { Kind = UpdateTag(s, t); CanDuplicate = true; IsEvaluated = false }
let uid s id = { Kind = UpdateId(s, id); CanDuplicate = true; IsEvaluated = false }


let representSel sel = 
  Record("x-selectors", List, 
    [ for s in sel ->
        match s with 
        | All -> { ID = ""; Expression = Primitive(String "*"); Previous = None }
        | Index n -> { ID = ""; Expression = Primitive(Number n); Previous = None }
        | Field f -> { ID = ""; Expression = Primitive(String f); Previous = None } ])

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
            EditKind.WrapRecord(tag, id, kind, unrepresentSel sel)
        | _ -> failwith "unrepresent - invalid arguments of x-edit-wrap"
    | "x-edit-append", Record(_, _, Lookup (Find "target" sel & Find "node" (Record(_, _, [nd])))) ->
        EditKind.Append(unrepresentSel sel, nd)
    | "x-edit-updateid", Record(_, _, Lookup (Find "target" sel & Find "id" (Primitive(String id)))) ->
        EditKind.UpdateId(unrepresentSel sel, id) 
  { Kind = editKind; CanDuplicate = false; IsEvaluated = false }

let represent op = 
  let repr id kvp = 
    let args = [ for k,v in kvp -> { ID=k; Expression=v; Previous=None } ]
    { ID = id; Expression = Record(id, Object, args); Previous=None }
  match op.Kind with 
  | EditKind.WrapRecord(tag, id, kind, target) ->
      let ty = match kind with Object -> "object" | Apply -> "apply" | List -> "list"
      repr "x-edit-wrap" [ 
        "tag", Primitive(String tag); "id", Primitive(String id)
        "kind", Primitive(String ty); "target", representSel target 
      ]
  | EditKind.Append(target, nd) ->
      repr "x-edit-append" [
        "target", representSel target; "node", Record("x-node-wrapper", Object, [nd])
      ]
  | EditKind.UpdateId(target, id) ->
      repr "x-edit-updateid" [
        "target", representSel target; "id", Primitive(String id)
      ]
      

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

let opsCounter = opsBaseCounter //@ opsCounterInc @ opsCounterHndl


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

let opsCore = 
  [
    ap [] (nds "title" "h1" "Programming conference 2023")
    ap [] (nds "stitle" "h2" "Speakers")
    ap [] (lst "speakers" "ul")
    ap [Field "speakers"] (nds "" "li" "Adele Goldberg, adele@xerox.com") 
    ap [Field "speakers"] (nds "" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap [Field "speakers"] (nds "" "li" "Betty Jean Jennings, betty@rand.com") 
  ]

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
    ap [Field "totals"] (nds "" "span" "Refreshments: ") 
    wr [Field "totals"; Index 0] Object "" "li"
    ap [Field "totals"; Index 0] (ref "item" [Field "costs"; Field "coffee"; Field "cost"; Field "value"])
    wr [Field "totals"; Index 0; Field "item"] Apply "left" "span"
    ap [Field "totals"; Index 0; Field "item"] (ref "right" [Field "counts"; Field "attendees"; Field "count"; Field "value"])
    ap [Field "totals"; Index 0; Field "item"] (ref "op" [Field "$builtins"; Field "*"])
    wr [Field "totals"; Index 0; Field "item"] Object "value" "strong"

    ap [Field "totals"] (nds "" "span" "Speaker travel: ") 
    wr [Field "totals"; Index 1] Object "" "li"
    ap [Field "totals"; Index 1] (ref "item" [Field "costs"; Field "travel"; Field "cost"; Field "value"])
    wr [Field "totals"; Index 1; Field "item"] Apply "left" "span"
    ap [Field "totals"; Index 1; Field "item"] (ref "right" [Field "counts"; Field "speakers"; Field "count"])
    ap [Field "totals"; Index 1; Field "item"] (ref "op" [Field "$builtins"; Field "*"])
    wr [Field "totals"; Index 1; Field "item"] Object "value" "strong"

    ap [] (nds "ultimate" "h3" "Total: ") 
    wr [Field "ultimate" ] Object "" "span"
    ap [Field "ultimate" ] (ref "item" [Field "totals"; All; Field "item"; Field "value"])
    wr [Field "ultimate"; Field "item"] Apply "arg" "span"
    ap [Field "ultimate"; Field "item"] (ref "op" [Field "$builtins"; Field "sum"])
  ]
