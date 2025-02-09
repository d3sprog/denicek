module Denicek.Eval

open Denicek
open Denicek.Doc

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

let rec evalSiteChildren kind inFormula sels nds =
  let rec loop i = function 
    | (f, nd)::nds -> 
        match evalSite inFormula (kind f::sels) nd with 
        | Some res -> Some res
        | None -> loop (i + 1) nds
    | _ -> None
  loop 0 nds 

and (|EvalSiteRecordChildren|_|) inFormula sels nds = 
  evalSiteChildren Field inFormula sels (OrdList.toList nds)

and (|EvalSiteListChildren|_|) inFormula sels nds = 
  evalSiteChildren Index inFormula sels (OrdList.toList nds)

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
      match evalSiteChildren Field (Some formulaSel) sels (OrdList.toList children) with 
      | Some res -> Some res
      | None -> Some(formulaSel, List.rev sels)
  | Reference(Absolute, Field b::_ ), _ when b.StartsWith("$") -> None
  | Reference _, Some(formulaSel) -> Some (formulaSel, List.rev sels)
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
    | Record("x-evaluated", OrdList.Find "result" r) -> loop r
    | v -> v
  loop nd

let (|EvaluatedResult|) nd = getEvaluatedResult nd

let evaluateBuiltin (data:Map<string, Node>) op (args:Map<string, Node>)= 
  match op with 
  | "read-csv" ->
      match args.TryFind "url" with
      | Some(EvaluatedResult(Primitive(String fname))) -> 
          data.[fname], [Field "url"]      
      | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."

  | "count" | "sum" ->
      let sum = List.map (function 
        | Primitive(Number n) -> n 
        | nd -> failwith $"evaluate: Argument of 'sum' is not a number but {Format.formatNode nd}") >> List.sum 
      let count = List.length >> float
      let f = (dict [ "count", count; "sum", sum ]).[op]
      match args.TryFind "arg" with
      | Some(EvaluatedResult(List(_, nds))) -> 
          Primitive(Number(f (List.map (snd >> getEvaluatedResult) (OrdList.toList nds)))), [Field "arg"]
      | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."

  | "equals" -> 
      match args.TryFind "left", args.TryFind "right" with
      | Some(EvaluatedResult(Primitive(p1))), Some(EvaluatedResult(Primitive(p2))) -> 
          Primitive(String(if p1 = p2 then "true" else "false")), [Field "left"; Field "right"]
      | _ -> 
          // NOTE: This also works on references that failed to evaluate 
          // (and so left/right is <empty> list added by Reference evaluation)
          Primitive(String("false")), [Field "left"; Field "right"]

  | "round" ->
      match args.TryFind "arg", args.TryFind "digits" with
      | Some(EvaluatedResult(Primitive(Number f))), Some(EvaluatedResult(Primitive(Number d))) -> 
          Primitive(Number(System.Math.Round(f, int d))), [Field "arg"; Field "digits"]
      | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
      
  | "plus" | "mul" | "minus" | "div" -> 
      let f = (dict [ "plus",(+); "mul",(*); "minus",(-); "div",(/) ]).[op]
      match args.TryFind "left", args.TryFind "right" with
      | Some(EvaluatedResult(Primitive(Number n1))), Some(EvaluatedResult(Primitive(Number n2))) -> 
          Primitive(Number(f n1 n2)), [Field "left"; Field "right"]
      | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
  | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"          

let evaluateRaw evaluateBuiltin doc =
  match evalSite None [] doc with
  | None -> []
  | Some(formulaSel, sel) ->
      // Evaluation generates value edits - because they change doc structure
      let it = match select sel doc with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sel}\n Resulted in {nds}"
      match it with 
      | Reference(kind, p) ->
          let p = resolveReference sel (kind, p)
          [ WrapRecord(KeepReferences, "reference", "x-evaluated", sel), [p;formulaSel]
            RecordAdd(sel, "result", None, None, List("empty", OrdList.empty ())), [p;formulaSel] // Allow 'slightly clever' case of Copy from doc.fs
            Copy(KeepReferences, sel @ [Field "result"], p), [p;formulaSel] ] // DENICEK: add [p] ref here too (because of weaker effect checker)

      | Record("x-formula", allArgs & OpAndArgs(Reference(Absolute, op & (Field ophd)::_), args)) when ophd.StartsWith("$") ->
          //
          // let res, deps = evaluateBuiltin data op args
          //
          // More fine grained dependency would be [ for p in deps -> sel @ [p] ]
          // but this does not seem to work so we just add dependency on the entire
          // formula (the most top-level one) - which is a safe overapproximation
          // (value edits can transform the formula, breaking the dependencies)
          let res = evaluateBuiltin op args          
          let deps = [ formulaSel ] 
          [ WrapRecord(KeepReferences, "formula", "x-evaluated", sel), deps
            RecordAdd(sel, "result", None, None, res), deps ]

      | Record("x-formula", nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for f, _ in nds -> f]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it}"


let webnicekEvaluateBuiltins data op args = 
  match op with 
  | [Field "$builtins"; Field op ] -> fst (evaluateBuiltin data op args)
  | _ -> failwith $"evaluate: Unknown builtin {op}"

let evaluateOne evaluateBuiltins doc =
  let lbl = "evaluate." + System.Guid.NewGuid().ToString("N")
  [ for ed, deps in evaluateRaw evaluateBuiltins doc -> 
      { Kind = ed; Dependencies = deps; GroupLabel = lbl } ]
  
let evaluateAll evaluateBuiltins doc = 
  let rec loop doc = seq {
    let edits = evaluateOne evaluateBuiltins doc
    yield! edits
    let ndoc = Apply.applyHistory doc edits 
    if doc <> ndoc then yield! loop ndoc }
  List.ofSeq (loop doc)


/// Push evalauted edits through document edits that were added after the
/// document was evaluated (we always assume evaluated edits are attached 
/// on the "side" of main history) and re-evaluate invalidated things.
let updateEvaluatedEdits oldDocEdits newDocEdits evalEdits = 
  let editsAfterEval = List.skip (List.length oldDocEdits) newDocEdits
  Merge.pushEditsThroughSimple Merge.RemoveConflicting editsAfterEval evalEdits
  