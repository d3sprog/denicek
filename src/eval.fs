module Tbd.Eval

open Tbd
open Tbd.Doc

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

// Formulas look like this:
//
// <x-formula>
//  <x-reference ...>
//  <x-reference ...>
// </x-formula>
//
// We first replace all children with <x-evaluated> and then the formula itself.
// <x-evaluated> has two children - 'formula' (original) and 'result' (the value).

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
/// The evaluation site will always be inside formula (it may be nested
/// formulas) - this returns the most top-level one as the first part of the result
and evalSite (formulaSel:option<_>) sels nd : option<Selectors * Selectors> =
  match nd, formulaSel with 
  // Evaluated alread - do not need to look inside
  | Record("x-evaluated", _), _ -> None
  // Evaluate references but not outside formula & not builtins 
  // Formula - Call by value - evaluate children first
  | Record("x-formula", children), _ -> 
      let formulaSel = Option.defaultValue (List.rev sels) formulaSel
      match evalSiteRecordChildren (Some formulaSel) sels children with 
      | Some res -> Some res
      | None -> Some(formulaSel, List.rev sels)
  | Reference(Field "$builtins"::_), _ -> None
  | Reference(p), Some(formulaSel) -> Some (formulaSel, List.rev sels)
  | Reference _, _ -> None
  // Look recursively
  | Record(_, EvalSiteRecordChildren None sels res), _ -> Some res
  | List(_, EvalSiteListChildren None sels res), _ -> Some res
  | (Primitive _ | List _ | Record _), _ -> None

let (|OpAndArgs|) args = 
  let args = Map.ofSeq args
  args.["op"], args.Remove("op")

let getEvaluatedResult nd =
  let rec loop = function
    | Record("x-evaluated", Patterns.ListFind "result" r) -> loop r
    | v -> v
  loop nd

let (|EvaluatedResult|) nd = getEvaluatedResult nd

let evaluateBuiltin op (args:Map<string, Node>)= 
  match op with 
  | "count" | "sum" ->
      let sum = List.map (function 
        | Primitive(Number n) -> n 
        | nd -> failwith $"evaluate: Argument of 'sum' is not a number but {formatNode nd}") >> List.sum 
      let count = List.length >> float
      let f = (dict [ "count", count; "sum", sum ]).[op]
      match args.TryFind "arg" with
      | Some(EvaluatedResult(List(_, nds))) -> 
          Primitive(Number(f (List.map getEvaluatedResult nds))), [Field "arg"]
      | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."

  | "plus" | "mul" | "minus" -> 
      let f = (dict [ "plus",(+); "mul",(*); "minus",(-) ]).[op]
      match args.TryFind "left", args.TryFind "right" with
      | Some(EvaluatedResult(Primitive(Number n1))), Some(EvaluatedResult(Primitive(Number n2))) -> 
          Primitive(Number(f n1 n2)), [Field "left"; Field "right"]
      | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
  | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"          

let evaluateRaw doc =
  match evalSite None [] doc with
  | None -> []
  | Some(formulaSel, sel) ->
      // Evaluation generates value edits - because they change doc structure
      let it = match select sel doc with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sel}\n Resulted in {nds}"
      match it with 
      | Reference(p) -> 
          [ Shared(ValueKind, WrapRecord("reference", "x-evaluated", sel)), [p]
            Value(RecordAdd(sel, "result", List("empty", []))), [p] // Allow 'slightly clever' case of Copy from doc.fs
            Shared(ValueKind, Copy(sel @ [Field "result"], p)), [] ]

      | Record("x-formula", allArgs & OpAndArgs(Reference [ Field("$builtins"); Field op ], args)) ->
          let res, deps = evaluateBuiltin op args
          // More fine grained dependency would be [ for p in deps -> sel @ [p] ]
          // but this does not seem to work so we just add dependency on the entire
          // formula (the most top-level one) - which is safe overapproximation
          // (value edits can transform the formula, breaking the dependencies)
          let deps = [ formulaSel ] 
          printfn $"Formula selector: {formatSelector formulaSel}"
          [ Shared(ValueKind, WrapRecord("formula", "x-evaluated", sel)), deps
            Value(RecordAdd(sel, "result", res)), deps ]          

      | Record("x-formula", nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for f, _ in nds -> f]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it}"


let evaluateOne doc =
  let lbl = "evaluate." + System.Guid.NewGuid().ToString("N")
  [ for ed, deps in evaluateRaw doc -> 
      { Disabled = false; Kind = ed; Dependencies = deps; GroupLabel = lbl } ]
  
let evaluateAll doc = 
  let rec loop doc = seq {
    let edits = evaluateOne doc
    yield! edits
    let ndoc = applyHistory doc edits 
    if doc <> ndoc then yield! loop ndoc }
  List.ofSeq (loop doc)


/// Push evalauted edits through document edits that were added after the
/// document was evaluated (we always assume evaluated edits are attached 
/// on the "side" of main history) and re-evaluate invalidated things.
let updateEvaluatedEdits all finalDoc evalBaseHash docEdits evalEdits = 
  let editsAfterEval = takeAfterHash evalBaseHash docEdits |> Option.get
  let updatedEvalEdits = pushEditsThroughSimple RemoveConflicting editsAfterEval evalEdits
  let relevantEvalEdits = updatedEvalEdits |> List.filter (fun ed -> not ed.Disabled)
  let extraEval = if all then evaluateAll finalDoc else evaluateOne finalDoc
  relevantEvalEdits @ extraEval
  
/// The evaluated edits branch off from the doc edits at a given hash.
/// This merges them with the (possibly updated) document edits to 
/// get a list of all edits that we should display to the user.
let updateDisplayEdits evalBaseHash docEdits evalEdits = 
  let evalEdits = 
    if List.isEmpty evalEdits then [] else
    match takeUntilHash evalBaseHash docEdits with 
    | Some ee -> ee @ evalEdits
    | None -> failwith "updateDocument: EvaluatedBaseHash not found"
  mergeHistoriesSimple RemoveConflicting docEdits evalEdits
