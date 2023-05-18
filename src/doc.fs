#if INTERACTIVE
#else
module Tbd.Doc
#endif

type Selector = 
  | Field of string
  | All
  | Index of int 

type Selectors = Selector list

type Primitive =
  | Number of float
  | String of string

type Node = 
  { ID : string
    Tag : string 
    Expression : Expr
    Evaluated : Node option }

and RecordType = 
  | List | Object | Apply

and Expr = 
  | Record of RecordType * list<Node>
  | Primitive of Primitive
  | Reference of Selectors

// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------

let replace f nd = 
  let rec loop path nd =
    match f path nd with 
    | Some res -> res
    | _ -> 
    let rtrn e = { nd with Expression = e }
    match nd.Expression with 
    | Record(typ, attrs) -> 
        Record(typ, List.mapi (fun i nd -> 
          let sel = if typ = List then Index(i) else Field(nd.ID)
          loop (path @ [sel]) nd) attrs) |> rtrn
    | Reference _ | Primitive _ -> nd 
  loop [] nd

let fold f st value = 
  let rec loop path st nd =
    let st = f path nd st 
    match nd.Expression with 
    | Record(typ, nds) -> 
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
  | _ -> failwithf "matches: Incompatible paths %A and %A" p1 p2

let select sel doc = 
  doc |> fold (fun p value st -> 
    if matches sel p then value::st else st) [] |> List.rev

// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------

type Edit = 
  | Append of Selectors * Node
  | EditText of Selectors * (string -> string)
  | Reorder of Selectors * list<int>
  | Copy of Selectors * Selectors
  | WrapRecord of string * string * RecordType * Selectors 

let apply doc edit =
  match edit with
  | Append(sel, nd) ->
      replace (fun p el ->
        match el.Expression with 
        | Record(typ, nds) when matches p sel -> 
            Some { el with Expression = Record(typ, nds @ [nd]) }
        | _ -> None ) doc
  | Reorder(sel, indices) ->
      replace (fun p el ->
        match el.Expression with 
        | Record(typ, vals) when matches p sel -> 
            Some { el with Expression = Record(typ, [ for i in indices -> vals.[i]]) }
        | _ -> None ) doc
  | EditText(sel, f) ->
      replace (fun p el -> 
        match el.Expression with 
        | Primitive(String(s)) when matches p sel -> 
            Some { el with Expression = Primitive(String(f s)) }
        | _ -> None ) doc
  | WrapRecord(id, tag, typ, sel) ->
      replace (fun p el -> 
        if matches p sel then Some { el with Expression = Record(typ, [{ el with ID = id; Tag = tag }]) }
        else None ) doc
  | Copy(sel1, sel2) ->
      let mutable vals = select sel1 doc
      let next () = match vals with h::tl -> vals <- tl; h | [] -> failwith "apply.Copy: Insufficient number of selected elements"
      replace (fun p el -> 
        if matches p sel2 then Some(next())
        else None ) doc

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------


let childrenAndBuilder e = 
  match e with
  | Record(typ, nds) -> nds, fun nds -> Record(typ, nds)
  | Primitive _ | Reference _ -> [], fun _ -> e

let rec evalSite orig : (Node * _) option = 
  match orig.Evaluated with 
  | Some nd when nd.Expression = orig.Expression -> None
  | Some nd -> 
      evalSite nd |> Option.map (fun (es, ctor) ->
        es, fun nnd -> { orig with Evaluated = Some (ctor nnd)})
  | None ->
      let children, rebuild = childrenAndBuilder orig.Expression
      let rec childEvalSite skipped = function
        | c::cs -> 
            match evalSite c with 
            | None -> childEvalSite (c::skipped) cs
            | Some(es, ctor) -> 
                Some(es, fun nnd -> 
                  let evald = 
                    { ID = orig.ID; Tag = orig.Tag; Evaluated = None
                      Expression = rebuild ((List.rev skipped) @ (ctor nnd)::cs) }
                  { orig with Evaluated = Some evald })
        | [] -> None
      match childEvalSite [] children with 
      | None -> Some(orig, fun nnd -> { orig with Evaluated = Some(nnd) })
      | Some es -> Some es

(*
let rec substitute v arg nd = 
  if nd.Evaluated.IsSome then failwith "substitute: Cannot subsitutute in evaluated subexpressions"
  match nd.Expression with 
  | Apply(e, es) -> { nd with Expression = Apply(substitute v arg e, List.map (substitute v arg) es) }
  | Let(id, e1, e2) -> { nd with Expression = Let(id, substitute v arg e1, substitute v arg e2) }
  | Reference(id) when id = v -> arg
  | Reference _ | List _ | Tuple _ | Primitive _ -> nd
*)

let rec mostEvalauted nd = 
  match nd.Evaluated with 
  | Some nd -> mostEvalauted nd
  | _ -> nd

let (|MostEvaluated|) nd = mostEvalauted nd

let (|Args|) args = 
  let args = Map.ofSeq [ for arg in args -> arg.ID, mostEvalauted arg ]
  args.["op"], args

let evalSingle doc nd = 
  match nd.Expression with 
  | Record(Object, _) | Record(List, _) | Primitive _ -> nd.Expression
  | Reference(Field "$builtins"::_) -> nd.Expression
  | Reference(sel) -> (List.exactlyOne (select sel doc)).Expression
  | Record(Apply, Args({ Expression = Reference [ Field("$builtins"); Field op ] }, args)) -> 
      match op with 
      | "+" | "*" -> 
          let f = (dict [ "+",(+); "*",(*) ]).[op]
          match args.TryFind "left", args.TryFind "right" with
          | Some { Expression = Primitive(Number n1) },
            Some { Expression = Primitive(Number n2) } -> Primitive(Number(f n1 n2))
          | _ -> failwith $"evalSingle: Invalid arguments of built-in op '{op}'."
      | _ -> failwith $"evalSingle: Built-in op '{op}' not implemented!"      
  | Record(Apply, _) -> 
      failwith "evalSingle: Apply of non-builtins not implemented"

let evaluate doc nd = 
  match evalSite nd with 
  | Some(nd, f) -> f { nd with Expression = evalSingle doc nd }
  | None -> nd

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

let ap s n = Append(s, n)
let wr s typ id tag = WrapRecord(id, tag, typ, s)

let nds id tag s = 
  { ID = id; Tag = tag; Expression = Primitive(String s); Evaluated = None }

let ndn id tag n = 
  { ID = id; Tag = tag; Expression = Primitive(Number n); Evaluated = None }

let rcd id tag = 
  { ID = id; Tag = tag; Expression = Record(Object, []); Evaluated = None }

let lst id tag = 
  { ID = id; Tag = tag; Expression = Record(List, []); Evaluated = None }

let ref id sel = 
  { ID = id; Tag = "span"; Expression = Reference(sel); Evaluated = None }

let doc = 
  [
    ap [] (nds "title" "h1" "Programming conference 2023")
    ap [] (nds "" "h2" "Speakers")
    ap [] (lst "speakers" "ul")
    ap [Field "speakers"] (nds "" "li" "Adele Goldberg, adele@xerox.com") 
    ap [Field "speakers"] (nds "" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap [Field "speakers"] (nds "" "li" "Betty Jean Jennings, betty@rand.com") 
    
    ap [] (nds "" "h2" "Budgeting")
    ap [] (nds "" "h3" "Number of people")
    ap [] (rcd "counts" "ul")
    ap [Field "counts"] (nds "attendees" "li" "Attendees: ") 
    wr [Field "counts"; Field "attendees"] Object "" "span"
    ap [Field "counts"; Field "attendees"] (ndn "count" "strong" 100)
    ap [Field "counts"] (nds "speakers" "li" "Speakers: ") 
    wr [Field "counts"; Field "speakers"] Object "" "span"
    ap [Field "counts"; Field "speakers"] (nds "count" "strong" "TODO")

    ap [] (nds "" "h3" "Item costs")
    ap [] (rcd "costs" "ul")
    ap [Field "costs"] (nds "coffee" "li" "Coffee break per person: ") 
    wr [Field "costs"; Field "coffee"] Object "" "span"
    ap [Field "costs"; Field "coffee"] (ndn "cost" "strong" 5)
    ap [Field "costs"] (nds "lunch" "li" "Lunch per person: ") 
    wr [Field "costs"; Field "lunch"] Object "" "span"
    ap [Field "costs"; Field "lunch"] (ndn "cost" "strong" 20)
    ap [Field "costs"] (nds "dinner" "li" "Dinner per person: ") 
    wr [Field "costs"; Field "dinner"] Object "" "span"
    ap [Field "costs"; Field "dinner"] (ndn "cost" "strong" 80)
    
    ap [] (nds "" "h3" "Total costs")
    ap [] (lst "totals" "ul")
    ap [Field "totals"] (nds "" "li" "Refreshments: ") 
    wr [Field "totals"; Index 0] Object "" "span"
    ap [Field "totals"; Index 0] (ref "item" [Field "costs"; Field "coffee"; Field "cost"])
    wr [Field "totals"; Index 0; Field "item"] Apply "left" "span"
    ap [Field "totals"; Index 0; Field "item"] (ref "right" [Field "counts"; Field "attendees"; Field "count"])
    ap [Field "totals"; Index 0; Field "item"] (ref "op" [Field "$builtins"; Field "*"])
  ]
  |> List.fold apply (rcd "root" "div")


(*

# Programming conference 2023

## Speakers
- Adele Goldberg, adele@xerox.com
- Margaret Hamilton, hamilton@mit.com 
- Betty Jean Jennings, betty@rand.com

## Budgeting

### Number of people
- Attendees: 100
- Speakers: =SUM(...)

### Item costs
- Coffee break per person: 5
- Lunch per person: 20
- Dinner per person: 100

### Total costs
- Refreshments: =Attendees*(Coffee+Lunch+Dinner)
- Travel: =SUM(....)
- Total: =Refreshments+Travel

*)


let foo() = 
  let e d = evaluate d d 

  let doc' = 
    doc 
      |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e
      |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e |> e

  evalSite doc'
