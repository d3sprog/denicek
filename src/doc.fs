#if INTERACTIVE
#else
module Tbd.Doc
#endif

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
    Tag : string 
    Expression : Expr
//    Evaluated : Node option 
    }

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
    //match nd.Evaluated with 
    //| Some nd -> loop path nd
    //| _ -> 
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
    //match nd.Evaluated with 
    //| Some nd -> loop path st nd
    //| _ -> 
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
  | Replace of Selectors * Node

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
      let expr = 
        match select sel1 doc with 
        | [nd] -> nd.Expression
        | nds -> Record(List, nds)
      replace (fun p el -> 
        if matches p sel2 then Some({ el with Expression = expr })
        else None ) doc
  | Replace(sel, nd) ->
      replace (fun p el -> 
        if matches p sel then Some(nd)
        else None ) doc

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
  | Record(typ, nds) -> 
      match typ, evalSiteChildren sels typ nds with
      | _, Some res -> Some res
      | Object, None | List, None -> None
      | _ -> Some(List.rev sels)

let evaluate nd =
  match evalSite [] nd with
  | None -> []
  | Some sels ->
      let it = match select sels nd with [it] -> it | _ -> failwith "evaluate: Ambiguous evaluation site"
      match it.Expression with 
      | Reference(p) -> [ Copy(p, sels) ]  
      | Record(Apply, Args({ Expression = Reference [ Field("$builtins"); Field op ] }, args)) ->
          match op with 
          | "count" | "sum" ->
              let sum = List.map (function { Expression = Primitive(Number n) } -> n | _ -> failwith "evaluate: Argument of 'sum' is not a number.") >> List.sum 
              let count = List.length >> float
              let f = (dict [ "count", count; "sum", sum ]).[op]
              match args.TryFind "arg" with
              | Some { Expression = Record(List, nds) } -> 
                  let res = Primitive(Number(f nds))
                  [ Replace(sels, { it with Expression = res } )  ] 
              | _ -> failwith $"evaluate: Invalid argument of built-in op '{op}'."
          | "+" | "*" -> 
              let f = (dict [ "+",(+); "*",(*) ]).[op]
              match args.TryFind "left", args.TryFind "right" with
              | Some { Expression = Primitive(Number n1) },
                Some { Expression = Primitive(Number n2) } -> 
                  let res = Primitive(Number(f n1 n2))
                  [ Replace(sels, { it with Expression = res } )  ] 
              | _ -> failwith $"evaluate: Invalid arguments of built-in op '{op}'."
          | _ -> failwith $"evaluate: Built-in op '{op}' not implemented!"      
      | Record(Apply, nds) -> 
          failwith $"evaluate: Unexpected format of arguments: {nds}"
      | _ -> failwith $"evaluate: Evaluation site returned unevaluable thing: {it.Expression}"

// --------------------------------------------------------------------------------------
// Evaluation
// --------------------------------------------------------------------------------------

let ap s n = Append(s, n)
let wr s typ id tag = WrapRecord(id, tag, typ, s)

let nds id tag s = 
  { ID = id; Tag = tag; Expression = Primitive(String s); } //Evaluated = None }

let ndn id tag n = 
  { ID = id; Tag = tag; Expression = Primitive(Number n); } //Evaluated = None }

let rcd id tag = 
  { ID = id; Tag = tag; Expression = Record(Object, []); } //Evaluated = None }

let lst id tag = 
  { ID = id; Tag = tag; Expression = Record(List, []); } //Evaluated = None }

let ref id tag sel = 
  { ID = id; Tag = tag; Expression = Reference(sel); } //Evaluated = None }

let ops = 
  [
    ap [] (nds "title" "h1" "Programming conference 2023")
    ap [] (nds "stitle" "h2" "Speakers")
    ap [] (lst "speakers" "ul")
    ap [Field "speakers"] (nds "" "li" "Adele Goldberg, adele@xerox.com") 
    ap [Field "speakers"] (nds "" "li" "Margaret Hamilton, hamilton@mit.com") 
    ap [Field "speakers"] (nds "" "li" "Betty Jean Jennings, betty@rand.com") 
    
    ap [] (nds "btitle" "h2" "Budgeting")
    ap [] (nds "ntitle" "h3" "Number of people")
    ap [] (rcd "counts" "ul")
    ap [Field "counts"] (nds "attendees" "li" "Attendees: ") 
    wr [Field "counts"; Field "attendees"] Object "" "span"
    ap [Field "counts"; Field "attendees"] (ndn "count" "strong" 100)
    ap [Field "counts"] (nds "speakers" "li" "Speakers: ") 
    wr [Field "counts"; Field "speakers"] Object "" "span"
    ap [Field "counts"; Field "speakers"] (ref "count" "strong" [Field "speakers"; All])
    wr [Field "counts"; Field "speakers"; Field "count"] Apply "arg" "span"
    ap [Field "counts"; Field "speakers"; Field "count"] (ref "op" "span" [Field "$builtins"; Field "count"])

    ap [] (nds "ititle" "h3" "Item costs")
    ap [] (rcd "costs" "ul")
    ap [Field "costs"] (nds "travel" "li" "Travel per speaker: ") 
    wr [Field "costs"; Field "travel"] Object "" "span"
    ap [Field "costs"; Field "travel"] (ndn "cost" "strong" 1000)
    ap [Field "costs"] (nds "coffee" "li" "Coffee break per person: ") 
    wr [Field "costs"; Field "coffee"] Object "" "span"
    ap [Field "costs"; Field "coffee"] (ndn "cost" "strong" 5)
    ap [Field "costs"] (nds "lunch" "li" "Lunch per person: ") 
    wr [Field "costs"; Field "lunch"] Object "" "span"
    ap [Field "costs"; Field "lunch"] (ndn "cost" "strong" 20)
    ap [Field "costs"] (nds "dinner" "li" "Dinner per person: ") 
    wr [Field "costs"; Field "dinner"] Object "" "span"
    ap [Field "costs"; Field "dinner"] (ndn "cost" "strong" 80)
    
    ap [] (nds "ttitle" "h3" "Total costs")
    ap [] (lst "totals" "ul")
    ap [Field "totals"] (nds "" "li" "Refreshments: ") 
    wr [Field "totals"; Index 0] Object "" "span"
    ap [Field "totals"; Index 0] (ref "item" "strong" [Field "costs"; Field "coffee"; Field "cost"])
    wr [Field "totals"; Index 0; Field "item"] Apply "left" "span"
    ap [Field "totals"; Index 0; Field "item"] (ref "right" "span" [Field "counts"; Field "attendees"; Field "count"])
    ap [Field "totals"; Index 0; Field "item"] (ref "op" "span" [Field "$builtins"; Field "*"])

    ap [Field "totals"] (nds "" "li" "Speaker travel: ") 
    wr [Field "totals"; Index 1] Object "" "span"
    ap [Field "totals"; Index 1] (ref "item" "strong" [Field "costs"; Field "travel"; Field "cost"])
    wr [Field "totals"; Index 1; Field "item"] Apply "left" "span"
    ap [Field "totals"; Index 1; Field "item"] (ref "right" "span" [Field "counts"; Field "speakers"; Field "count"])
    ap [Field "totals"; Index 1; Field "item"] (ref "op" "span" [Field "$builtins"; Field "*"])

    ap [] (nds "ultimate" "h3" "Total: ") 
    wr [Field "ultimate" ] Object "" "span"
    ap [Field "ultimate" ] (ref "item" "strong" [Field "totals"; All; Field "item"])
    wr [Field "ultimate"; Field "item"] Apply "arg" "span"
    ap [Field "ultimate"; Field "item"] (ref "op" "span" [Field "$builtins"; Field "sum"])
  ]


let doc =
  ops |> List.fold apply (rcd "root" "div")


let e d = 
  d |> evaluate |> List.fold apply d

let foo () =
  doc 
  |> e
  |> e
  |> e
  |> evaluate

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

