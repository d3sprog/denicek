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
  //| Record("x-evaluated", _) -> None
  | Record("x-formula", Patterns.ListFind "result" _) -> None

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
  args.["op"], args

let evaluateRaw doc =
  match evalSite false [] doc with
  | None -> []
  | Some sels ->
      let it = match select sels doc with [it] -> it | nds -> failwith $"evaluate: Ambiguous evaluation site: {sels}\n Resulted in {nds}"
      match it with 
      | Reference(p) -> 
          [ //Copy(p, sels), [TagCondition(p, NotEquals, "x-evaluated")], [p]
            //Copy(p @ [Field "result"], sels), [TagCondition(p, Equals, "x-evaluated")], [p @ [Field "result"]] 

            // cannot - update tag
            //WrapRecord("result", "x-formula", sels)
            //RecordAdd(sels, "ref", RefSource(sels @ [Field "result"]))
            //Copy(sels @ [Field "result"], RefSource p) //, [SelectorHashEquals(p, hash (select p doc))]
          ]

      | Record("x-formula", allArgs & OpAndArgs(Reference [ Field("$builtins"); Field op ], args)) ->
          // Used previously for dependencies - now not needed
          // let ss = args.Keys |> Seq.map (fun k -> sels @ [Field k]) |> List.ofSeq

          let args = args |> Map.map (fun _ v ->
            match v with 
            | Record("x-formula", Patterns.ListFind "result" r) -> r
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
            | "plus" | "mul" -> 
                let f = (dict [ "plus",(+); "mul",(*) ]).[op]
                match args.TryFind "left", args.TryFind "right" with
                | Some(Primitive(Number n1)),
                  Some(Primitive(Number n2)) -> 
                    Primitive(Number(f n1 n2))
                | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
            | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"      
            
          //printfn "wrap %A" sels
          //[ Copy(sels, ConstSource res) ]//, [] ]  // Dependencies = ss
          
          [ // Ideally, we would restructure the formula too, but these are all structural
            // edits, so it breaks references. We need some way of using structural edits
            // as non-structural - when "changing DU case" rather than changing value

            // WrapRecord("result", "x-evaluated", sels)
            // RecordAdd(sels, "formula", RefSource(sels @ [Field "result"]))
            // RecordAdd(sels, "result", ConstSource(res))
            //RecordAdd(sels, "result", ConstSource(res))

            //ListAppend(sels, { ID = "previous"; Expression = Primitive(String "na") })
            //Copy(sels @ [Field "result"], sels @ [Field "previous"])
            //Replace(sels @ [Field "result"], { ID = "result"; Expression = res } )
            ] //*)
      | Record("x-formula", nds) -> 
          failwith $"evaluate: Unexpected format of arguments {[for f, _ in nds -> f]}: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it}"

let evaluateDoc doc =
  let eds = [ for ed in evaluateRaw doc -> { Kind = ed } ]
  { Groups = [eds] }

let evaluateAll doc = 
  let rec loop doc = seq {
    let edits = evaluateDoc doc
    yield! edits.Groups
    let ndoc = applyHistory doc edits 
    if doc <> ndoc then yield! loop ndoc }
  { Groups = List.ofSeq (loop doc) }
