module Denicek.Apply

open Denicek.Doc
open Denicek.Parsec
open Denicek.Parsec.Operators

// --------------------------------------------------------------------------------------
// Built-in primitive operations
// --------------------------------------------------------------------------------------

type Transformation = 
  { Key : string
    Label : string
    Function : string option * Primitive -> Primitive
    Args : Parser<string option> }

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
// Apply edits to document
// --------------------------------------------------------------------------------------

/// Structural selector does not contain 'Index'
let isStructuralSelector sel = 
  sel |> List.forall (function 
    | DotDot -> failwith "isStructuralSelector - Unresolved relative reference"
    | Index _ -> false | _ -> true)


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

  | RecordAdd(sel, fld, pred, nd) ->
      replace (fun p el -> 
        match el with 
        | Record(tag, nds) when matches p sel -> 
            let nds = nds |> OrdList.remove fld
            Some(Record(tag, OrdList.add (fld, nd) pred nds))
        | _ -> None ) doc
    
  | ListAppend(sel, n, pred, nd) ->
      replace (fun p el ->
        match el with 
        | List(tag, nds) when matches p sel -> 
            // Similar to 'RecordAdd' but we do not remove duplicates (but what this does is untested)
            Some(List(tag, OrdList.add (n, nd) pred nds))
        | _ -> None ) doc
      
  | ListAppendFrom(sel, n, pred, src) ->
      replace (fun p el ->
        match el with
        | List(tag, nds) when matches p sel -> 
            Some(List(tag, OrdList.add (n, selectSingle src doc) pred nds))
        | _ -> None ) doc
      
  | UpdateTag(sel, tagNew) ->
      replace (fun p el ->
        match el with 
        | Record(_, nds) when matches p sel -> Some(Record(tagNew, nds))
        | List(_, nds) when matches p sel -> Some(List(tagNew, nds))
        | _ -> None ) doc

  | ListDelete(sel, idel) ->
      replace (fun p -> function
        | List(t, items) when matches p sel -> 
            Some(List(t, OrdList.remove idel items))
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
        failwith $"apply.RecordDelete - Non-structural selector {Format.formatSelector sel} used with structural edit {Format.formatEdit edit}."
      let doc = replace (fun p -> function
        | Record(t, nds) when matches p sel ->
            let nds = nds |> OrdList.remove fdel
            Some(Record(t, nds))
        | _ -> None) doc
      if rb = UpdateReferences then 
        // We cannot update selectors if the target node was deleted, but 
        // we can check there are no such selectors in the document.
        for docRef in getDocumentReferences doc do 
          if prefixOfReference (sel @ [Field fdel]) docRef then
            failwith $"apply.RecordDelete - Cannot delete {Format.formatSelector sel}. Document contains conflicting selector {Format.formatReference (snd docRef)}."
        doc
      else doc
      
  | WrapRecord(rb, id, tag, sel) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.WrapRecord - Non-structural selector {Format.formatSelector sel} used with structural edit {Format.formatEdit edit}."
      let doc = 
        // TODO: Need to update references before transforming the document - but why was that?
        if rb = UpdateReferences then
          let nsels = getDocumentReferences doc |> List.map (Transforms.wrapRecordSelectors id sel)
          withNodeReferences doc nsels
        else doc
      replace (fun p el -> 
        if matches p sel then Some(Record(tag, OrdList.singleton id el))
        else None ) doc

  | WrapList(rb, id, tag, sel) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.WrapList - Non-structural selector {Format.formatSelector sel} used with structural edit {Format.formatEdit edit}."
      let doc = replace (fun p el -> 
        if matches p sel then Some(List(tag, OrdList.singleton id el))
        else None ) doc
      if rb = UpdateReferences then
        let nsels = getDocumentReferences doc |> List.map (Transforms.wrapListSelectors sel)
        withNodeReferences doc nsels
      else doc

  | RecordRenameField(rb, sel, fold, fnew) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.RecordRenameField - Non-structural selector {Format.formatSelector sel} used with structural edit {Format.formatEdit edit}."
      let doc = replace (fun p el -> 
        match el with 
        | Record(t, nds) when matches p sel -> 
            Some(Record(t, OrdList.renameKey fold fnew nds))
        | _ -> None ) doc
      if rb = UpdateReferences then
        let nsels = getDocumentReferences doc |> List.map (Transforms.renameFieldSelectors fold fnew sel)
        withNodeReferences doc nsels
      else doc

  | Copy(rb, sel, src) ->
      if rb = UpdateReferences && not (isStructuralSelector sel) then 
        failwith $"apply.Copy - Non-structural selector {Format.formatSelector sel} used with structural edit {Format.formatEdit edit}."

      let mutable exprs, proceed = 
        let srcNodes = select src doc
        match select sel doc with         
        | tgs when tgs.Length = srcNodes.Length -> srcNodes, true
        // Slightly clever in that we can copy multiple source nodes into a single target list node
        // (this is needed for evaluation of arguments - see eval.fs)
        | [List(t, _)] -> [List(t, OrdList.ofList (List.mapi (fun i nd -> string i, nd) srcNodes))], true 
        // If source or target is empty, do not do anything
        // (needed if we create merged edits that do not apply to anything)
        | tgtNodes when srcNodes.Length = 0 || tgtNodes.Length = 0 -> [], false 
        | tgtNodes -> failwith $"apply.Copy - Mismatching number of source and target notes. Edit: {Format.formatEdit edit}, src nodes: {srcNodes.Length}, target nodes: {tgtNodes.Length} "
      
      if proceed then 
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
            if prefixOfReference sel docRef then
              failwith $"apply.RecordDelete - Cannot copy to {Format.formatSelector sel}. Document contains conflicting selector {Format.formatReference (snd docRef)}."
            if prefixOfReference src docRef then
              failwith $"apply.RecordDelete - Cannot copy from {Format.formatSelector sel}. Document contains conflicting selector {Format.formatReference (snd docRef)}."
          doc
        else doc
      else doc

let applyHistory initial hist =
  hist |> List.fold apply initial
