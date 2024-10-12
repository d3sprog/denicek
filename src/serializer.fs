module Tbd.Serializer
open Tbd.Doc
open Fable.Core

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
  

