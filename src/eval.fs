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
and evalSite inFormula sels nd : option<Selectors> =
  match nd with 
  // Evaluated alread - do not need to look inside
  | Record("x-evaluated", _) -> None
  // Evaluate references but not outside formula & not builtins 
  // Formula - Call by value - evaluate children first
  | Record("x-formula", EvalSiteRecordChildren true sels res) -> Some res 
  | Record("x-formula", _) -> Some(List.rev sels)
  | Reference(Field "$builtins"::_) -> None
  | Reference(p) when inFormula -> Some (List.rev sels)
  | Reference _ -> None
  // Look recursively
  | Record(_, EvalSiteRecordChildren false sels res) -> Some res
  | List(_, EvalSiteListChildren false sels res) -> Some res
  | Primitive _ | List _ | Record _ -> None

let (|OpAndArgs|) args = 
  let args = Map.ofSeq args
  args.["op"], args.Remove("op")

let getEvaluatedResult nd =
  let rec loop acc = function
    | Record("x-evaluated", Patterns.ListFind "result" r) -> loop (Field "result"::acc) r
    | v -> List.rev acc, v
  loop [] nd

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
      | Some(EvaluatedResult(path, List(_, nds))) -> 
          Primitive(Number(f (List.map (getEvaluatedResult >> snd) nds))), [(Field "arg")::path]
      | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."

  | "plus" | "mul" -> 
      let f = (dict [ "plus",(+); "mul",(*) ]).[op]
      match args.TryFind "left", args.TryFind "right" with
      | Some(EvaluatedResult(p1, Primitive(Number n1))), Some(EvaluatedResult(p2, Primitive(Number n2))) -> 
          Primitive(Number(f n1 n2)), [(Field "left")::p1; (Field "right")::p2]
      | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
  | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"          

let evaluateRaw doc =
  match evalSite false [] doc with
  | None -> []
  | Some sel ->
      // Evaluation generates value edits - because they change doc structure
      let it = match select sel doc with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sel}\n Resulted in {nds}"
      match it with 
      | Reference(p) -> 
          [ Shared(ValueKind, WrapRecord("reference", "x-evaluated", sel)), [p]
            Value(RecordAdd(sel, "result", List("empty", []))), [p] // Allow 'slightly clever' case of Copy from doc.fs
            Shared(ValueKind, Copy(sel @ [Field "result"], p)), [] ]

      | Record("x-formula", allArgs & OpAndArgs(Reference [ Field("$builtins"); Field op ], args)) ->
          let res, deps = evaluateBuiltin op args
          let deps = [ for p in deps -> sel @ p ]
          [ Shared(ValueKind, WrapRecord("formula", "x-evaluated", sel)), deps
            Value(RecordAdd(sel, "result", res)), deps ]          

      | Record("x-formula", nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for f, _ in nds -> f]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it}"


let evaluateDoc doc =
  let eds = [ for ed, deps in evaluateRaw doc -> { Kind = ed; Dependencies = deps } ]
  { Groups = [eds] }

let evaluateAll doc = 
  let rec loop doc = seq {
    let edits = evaluateDoc doc
    yield! edits.Groups
    let ndoc = applyHistory doc edits 
    if doc <> ndoc then yield! loop ndoc }
  { Groups = List.ofSeq (loop doc) }
