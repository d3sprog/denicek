module Tbd.Serializer
open Tbd.Doc
open Fable.Core

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
  | _ -> failwith $"unrepresentSel: Not a selector: {expr}"
  
let (|Lookup|) args = dict args
let (|Find|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  if d.ContainsKey k then Some(d.[k]) else None
let (|Finds|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(String s) -> Some s | _ -> None
let rcd id kvp = Record(id, kvp)

let unrepresentIntList nd =
  match nd with 
  | List("x-int-list", nds) ->
      List.map (function Primitive(Number n) -> int n | _ -> failwith "unrepresentIntList - Not a number") nds
  | _ -> failwith $"unrepresentIntList - Invalid node {nd}"

let unrepresentSrc nd = 
  match nd with 
  | Record("x-src-node", Lookup(Find "const" nd)) -> ConstSource(nd)
  | Record("x-src-ref", Lookup(Find "selector" nd)) -> RefSource(unrepresentSel nd)
  | _ -> failwith $"unrepresentSrc - Invalid node {nd}"

let unrepresentCond nd = 
  match nd with 
  | Record("x-cond-equals", Lookup(Find "node" (Primitive v))) -> EqualsTo(v)
  | Record("x-cond-nonempty", []) -> NonEmpty
  | _ -> failwith $"unrepresentCond - Invalid node {nd}"

let unrepresent nd = 
  let editKind =
    match nd with
    | Record("x-edit-wraprec", Lookup(Finds "tag" tag & Finds "id" id & Find "target" target)) ->
        EditKind.WrapRecord(tag, id, unrepresentSel target)
    | Record("x-edit-append", Lookup (Find "target" sel & Find "src" src)) ->
        EditKind.ListAppend(unrepresentSel sel, unrepresentSrc src)
    | Record("x-edit-add", Lookup (Find "target" sel & Finds "field" f & Find "src" src)) ->
        EditKind.RecordAdd(unrepresentSel sel, f, unrepresentSrc src)
    | Record("x-edit-updateid", Lookup (Find "target" sel & Finds "id" id)) ->
        EditKind.RecordRenameField(unrepresentSel sel, id) 
    | Record("x-edit-copy", Lookup (Find "target" tgt & Find "src" src)) ->
        EditKind.Copy(unrepresentSel tgt, unrepresentSrc src) 
    | Record("x-edit-delete", Lookup (Find "target" tgt)) ->
        EditKind.Delete(unrepresentSel tgt) 
    | Record("x-check", Lookup (Find "target" tgt & Find "cond" cond)) ->
        EditKind.Check(unrepresentSel tgt, unrepresentCond cond) 
    | Record("x-wrap-list", Lookup (Find "target" tgt & Finds "tag" tag)) ->
        EditKind.WrapList(tag, unrepresentSel tgt) 
    | Record("x-primitive-edit", Lookup (Find "target" tgt & Finds "op" op)) ->
        EditKind.PrimitiveEdit(unrepresentSel tgt, op) 
    | Record("x-list-reorder", Lookup (Find "target" tgt & Find "perm" perm)) ->
        EditKind.ListReorder(unrepresentSel tgt, unrepresentIntList perm) 
    | Record("x-update-tag", Lookup (Find "target" tgt & Finds "old" otag & Finds "new" ntag)) ->
        EditKind.UpdateTag(unrepresentSel tgt, otag, ntag) 
    | _ -> failwith $"unrepresent - Missing case for: {nd}"  
  { Kind = editKind }

let representIntList ns =
  List("x-int-list", [for n in ns -> Primitive(Number(float n)) ])

let representSrc src = 
  match src with 
  | ConstSource(nd) -> [ "const", nd ] |> rcd "x-src-node"
  | RefSource(sel) -> [ "selector", representSel sel ] |> rcd "x-src-ref"

let representCond cond = 
  match cond with 
  | EqualsTo(nd) -> [ "node", Primitive nd ] |> rcd "x-cond-equals"
  | NonEmpty -> [] |> rcd "x-cond-nonempty"

let represent op = 
  let ps v = Primitive(String v)
  match op.Kind with 
  | EditKind.WrapRecord(tag, id, target) ->
      rcd "x-edit-wraprec" [ "tag", ps tag; "id", ps id; "target", representSel target ] 
  | EditKind.ListAppend(target, src) ->
      rcd "x-edit-append" [ "target", representSel target; "src", representSrc src ]
  | EditKind.RecordAdd(target, f, src) ->
      rcd "x-edit-add" [ "target", representSel target; "field", ps f; "src", representSrc src ]
  | EditKind.RecordRenameField(target, id) ->
      rcd "x-edit-updateid" [ "target", representSel target; "id", ps id ]
  | EditKind.Copy(target, source) ->
      rcd "x-edit-copy" [ "target", representSel target; "src", representSrc source ]
  | EditKind.Delete(target) ->
      rcd "x-edit-delete" [ "target", representSel target ]
  | EditKind.Check(target, cond) -> 
      rcd "x-check" [ "target", representSel target; "cond", representCond cond ]
  | EditKind.WrapList(tag, target) ->
      rcd "x-wrap-list" [ "target", representSel target; "tag", ps tag ]
  | EditKind.PrimitiveEdit(target, op) ->
      rcd "x-primitive-edit" [ "target", representSel target; "op", ps op ]
  | EditKind.ListReorder(target, perm) ->
      rcd "x-list-reorder" [ "target", representSel target; "perm", representIntList perm ]
  | EditKind.UpdateTag(target, otag, ntag) ->
      rcd "x-update-tag" [ "target", representSel target; "old", ps otag; "new", ps ntag ]

// --------------------------------------------------------------------------------------
// Serializing nodes as JSON
// --------------------------------------------------------------------------------------

let selToJson = function
  | Field f -> box f
  | Tag t -> box ("#" + t)
  | Index n -> box n
  | All -> box "*"

let rec nodeToJson = function
  | Primitive(String s) -> box s
  | Primitive(Number n) -> box n
  | List(tag, nds) -> JsInterop.createObj [ 
        "kind", box "list" 
        "tag", box tag
        "nodes", box [| for nd in nds -> nodeToJson nd |]
      ]
  | Record(tag, nds) -> JsInterop.createObj [ 
        "kind", box "record" 
        "tag", box tag
        "nodes", box [| for n, nd in nds -> [| box n; nodeToJson nd |] |]
      ]
  | Reference(sels) -> JsInterop.createObj [ 
        "kind", box "reference" 
        "selectors", box [| for s in sels -> selToJson s |]
      ]

[<Emit("typeof $0")>]
let jsTypeof (x: obj) : string = jsNative

[<Emit("$0[$1]")>]
let (?) (d:obj) (s:string) : 'R = jsNative

let selFromJson o = 
  if jsTypeof o = "number" then Index(unbox o)
  elif jsTypeof o = "string" then 
    let s = unbox<string> o
    if s = "*" then All
    elif s.StartsWith("#") then Tag(s.[1..])
    else Field(s)
  else failwith $"selFromJson - unexpected object {o}"

let rec nodeFromJson o =
  if jsTypeof o = "string" then Primitive(String(unbox o))
  elif jsTypeof o = "number" then Primitive(Number(unbox o))
  elif o?kind = "list" then List(o?tag, [ for o in unbox<obj[]> o?nodes -> nodeFromJson o ])
  elif o?kind = "record" then Record(o?tag, [ for o in unbox<obj[][]> o?nodes -> unbox o.[0], nodeFromJson o.[1] ])
  elif o?kind = "reference" then Reference [ for o in unbox<obj[]> o?selectors -> selFromJson o ]
  else failwith $"nodeFromJson - unexpected object: {o}"

let nodesToJson ndss = box [| for nds in ndss -> box [| for nd in nds -> nodeToJson nd |] |]
let nodesFromJson obj = [ for os in unbox<obj[][]> obj -> [ for o in os -> nodeFromJson o ] ]
let nodesToJsonString nds = JS.JSON.stringify(nodesToJson nds)
let nodesFromJsonString s = nodesFromJson(JS.JSON.parse(s))
  

