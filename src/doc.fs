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

let transformations = System.Collections.Generic.Dictionary<string, string -> string>()

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
  | EditText of Selectors * string //(string -> string)
  | Reorder of Selectors * list<int>
  | Copy of Selectors * Selectors 
  | WrapRecord of string * string * RecordType * Selectors 
  | Replace of Selectors * Node
  | AddField of Selectors * Node
  | UpdateTag of Selectors * string

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
            Some { el with Expression = Primitive(String(transformations.[f] s)) }
        | _ -> None ) doc
  | WrapRecord(id, tag, typ, sel) ->
      replace (fun p el -> 
        if matches p sel then Some { el with Expression = Record(typ, [{ el with ID = id; Tag = tag }]) }
        else None ) doc
  | Copy(sel1, sel2) ->
      // NOTE: This is a bit too clever (if there is one target, it 
      // implicitly creates list with all source nodes to be copied there)
      let mutable exprs = 
        match select sel2 doc, select sel1 doc with         
        | tgs, srcs when tgs.Length = srcs.Length -> [ for s in srcs -> s.Expression ]
        | [_], nds -> [ Record(List, nds) ]
        | _ -> failwith "apply.Copy: Mismatching number of source and target notes"
      let next() = match exprs with e::es -> exprs <- es; e | [] -> failwith "apply.Copy: Unexpected"
      replace (fun p el -> 
        if matches p sel2 then Some({ el with Expression = next() })
        else None ) doc
  | UpdateTag(sel, tag) ->
      replace (fun p el -> 
        if matches p sel then Some({ el with Tag = tag})
        else None ) doc
  | Replace(sel, nd) ->
      replace (fun p el -> 
        if matches p sel then Some(nd)
        else None ) doc
  | AddField(sel, v) ->
      replace (fun p el -> 
        match el.Expression with 
        | Record(Object, attrs) when matches p sel -> Some({ el with Expression = Record(Object, attrs @ [v]) })
        | _ -> None ) doc

// --------------------------------------------------------------------------------------
// Merge
// --------------------------------------------------------------------------------------

let getSelectors = function
  | EditText(s, _) | Append(s, _) | Reorder(s, _)
  | UpdateTag(s, _) | Replace(s, _) | WrapRecord(_, _, _, s) | AddField(s, _) -> [s]
  | Copy(s1, s2) -> [s1; s2]

let withSelectors sels = function
  | EditText(_, f) -> EditText(List.exactlyOne sels, f)
  | Append(_, v) -> Append(List.exactlyOne sels, v) 
  | Reorder(_, m) -> Reorder(List.exactlyOne sels, m)
  | WrapRecord(t, i, k, _) -> WrapRecord(t, i, k, List.exactlyOne sels) 
  | AddField(_, v) -> AddField(List.exactlyOne sels, v) 
  | UpdateTag(_, t) -> UpdateTag(List.exactlyOne sels, t) 
  | Replace(_, n) -> Replace(List.exactlyOne sels, n) 
  | Copy(_, _) -> Copy(List.head sels, List.exactlyOne (List.tail sels))


let reorderSelectors e1 sel ord = 
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
  let nsels = getSelectors e1 |> List.map (fun s1 -> reorder s1 sel)
  withSelectors nsels e1

let wrapSelectors e1 sel typ id tag =
  // Returns a modified version of 'selOther' to match
  // the additional wrapping at location specified by 'selReord'
  let rec wrapsels selOther selReord =
    match selOther, selReord with 
    | Field(fo)::selOther, Field(fr)::selReord when fo = fr -> Field(fo)::(wrapsels selOther selReord)
    | Field(_)::_, _ -> selOther
    | Index(io)::selOther, Index(ir)::selReord when io = ir -> Index(io)::(wrapsels selOther selReord)
    | Index(io)::selOther, All::selReord -> Index(io)::(wrapsels selOther selReord)
    | selOther, [] when typ <> Object || tag = "" -> failwith $"moveBefore.WrapRecord - Cannot add field ref for non-object or wrap without a name! c.f. {(typ,id,tag,sel)}"
    | selOther, [] -> Field(id)::selOther
    | (All|Index _)::_, Field(_)::_ 
    | Field(_)::_, (All|Index _)::_ -> selOther        
    | [], _ -> []
    | _ -> failwith $"moveBefore.WrapCase - Missing case: {selOther} vs. {selReord}"
  let nsels = getSelectors e1 |> List.map (fun s1 -> wrapsels s1 sel)
  withSelectors nsels e1  

let updateSelectors e1 e2 = 
  match e2 with 
  | Reorder(sel, ord) -> reorderSelectors e1 sel ord
  | WrapRecord(id, tag, typ, sel) -> wrapSelectors e1 sel typ id tag
  
  | Copy _ // TODO: If e1 modified source of copying, it should apply to its target now too!
  | UpdateTag _
  | AddField _
  | EditText _ 
  | Append _ ->
      e1

  | _ -> failwith $"moveBefore - Missing case: Edit to be considered: {e2}"


/// If 'p1' is prefix of 'p2', return the rest of 'p2'
let rec removeSelectorPrefix p1 p2 = 
  match p1, p2 with 
  | Field(f1)::p1, Field(f2)::p2 when f1 = f2 -> removeSelectorPrefix p1 p2
  | Index(i1)::p1, Index(i2)::p2 when i1 = i2 -> removeSelectorPrefix p1 p2
  // TODO: Arguably, we should not insert into specific index (only All) as that is a 'type error'
  // Meaning that when called from 'scopeEdit', then 'p1' should not contain 'Index' ?
  | Index(_)::p1, All::p2 | All::p1, Index(_)::p2 | All::p1, All::p2 -> removeSelectorPrefix p1 p2
  | [], p2 -> Some p2
  | _ -> None
  
let (|RemoveSelectorPrefix|_|) selbase sel = removeSelectorPrefix selbase sel

let scopeEdit selBase edit = 
  match edit with 
  | Append(RemoveSelectorPrefix selBase sel, nd) -> Some(Append(sel, nd))
  | EditText(RemoveSelectorPrefix selBase sel, f) -> Some(EditText(sel, f))
  | Reorder(RemoveSelectorPrefix selBase sel, p) -> Some(Reorder(sel, p))
  | WrapRecord(id, tag, typ, RemoveSelectorPrefix selBase sel) -> Some(WrapRecord(id, tag, typ, sel))
  | Replace(RemoveSelectorPrefix selBase sel, nd) -> Some(Replace(sel, nd))
  | AddField(RemoveSelectorPrefix selBase sel, nd) -> Some(AddField(sel, nd))
  | UpdateTag(RemoveSelectorPrefix selBase sel, t) -> Some(UpdateTag(sel, t))
  | Copy(RemoveSelectorPrefix selBase s1, RemoveSelectorPrefix selBase s2) -> Some(Copy(s1, s2))
  | Copy _ -> failwith "scopeEdit.Copy - non-local copy - need to think about this one"
  | _ -> None

let applyToAdded e1 e2 = 
  match e1 with 
  | Append(sel, nd) -> 
      // We are appending under 'sel', so the selector for 
      // the node 'nd' itself will be 'sel; All' (for added field, this needs the field name)
      match scopeEdit (sel @ [All]) e2 with
      | Some e2scoped ->
          printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          Append(sel, apply nd e2scoped)
      | None -> e1

  | AddField(sel, nd) -> 
      // TODO: Untested. Also maybe this assumes nd.ID <> ""
      match scopeEdit (sel @ [Field nd.ID]) e2 with
      | Some e2scoped ->
          printfn $"applyToAdded: Applying edit {e2scoped} to {nd}.\n  Got: {apply nd e2scoped}" 
          AddField(sel, apply nd e2scoped)
      | None -> e1

  | Replace _ -> failwith "applyToAdded - Replace TODO"
  | _ -> e1

// Assuming 'e1' and 'e2' happened independently,
// modify 'e1' so that it can be placed after 'e2'.
let moveBefore e1 e2 = 
  let e1 = applyToAdded e1 e2
  let e1 = updateSelectors e1 e2
  e1
  
let merge e1s e2s = 
  let rec loop acc e1s e2s =
    match e1s, e2s with 
    | e1::e1s, e2::e2s when e1 = e2 -> loop (e1::acc) e1s e2s
    | e1s, e2s ->
        let e2sAfter = e2s |> List.map (fun e2 -> List.fold moveBefore e2 e1s)
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

let ap s n = Append(s, n)
let wr s typ id tag = WrapRecord(id, tag, typ, s)
let ord s l = Reorder(s, l)
let ed sel fn f = transformations.[fn] <- f; EditText(sel, fn)
let add sel n = AddField(sel, n)
let cp s1 s2 = Copy(s1, s2)
let tag s t = UpdateTag(s, t)

(*
  | Append of Selectors * Node
  | EditText of Selectors * (string -> string)
  | Reorder of Selectors * list<int>
  | Copy of Selectors * Selectors 
  | WrapRecord of string * string * RecordType * Selectors 
  | Replace of Selectors * Node
*)


let addSpeakerOps = 
  [ 
    ap [Field "speakers"] (nds "" "li" "Ada Lovelace, lovelace@royalsociety.ac.uk")
    ord [Field "speakers"] [3; 0; 1; 2] 
  ]

let fixSpeakerNameOps = 
  [
    ed [Field("speakers"); Index(2)] "rename Jean" <| fun s -> 
      s.Replace("Betty Jean Jennings", "Jean Jennings Bartik").Replace("betty@", "jean@")
  ]

let refactorListOps = 
  [
    wr [Field "speakers"; All] Object "name" "td"
    add [Field "speakers"; All] (nds "email" "td" "")
    tag [Field "speakers"; All] "tr"
    tag [Field "speakers"] "table"
    
    wr [Field "speakers"] Object "body" "tbody"
    add [Field "speakers"] (rcd "head" "thead")
    add [Field "speakers"; Field "head"] (nds "" "td" "Name")
    add [Field "speakers"; Field "head"] (nds "" "td" "E-mail")

    cp [Field "speakers"; Field "body"; All; Field "name"] [Field "speakers"; Field "body"; All; Field "email"]
    ed [Field "speakers"; Field "body"; All; Field "name"] "get name" <| fun s -> 
      s.Substring(0, s.IndexOf(','))
    ed [Field "speakers"; Field "body"; All; Field "email"] "get email" <| fun s -> 
      s.Substring(s.IndexOf(',')+1).Trim()
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

let opsExtras = 
  [
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

