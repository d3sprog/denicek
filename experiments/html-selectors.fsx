// --------------------------------------------------------------------------------------
// Elements, Selectors, Paths
// --------------------------------------------------------------------------------------


// Homogeneous lists - prevents changing shape of only one element (e.g. nesting)
//   * <body><div /><div /></body>
//   * maybe edits cannot change type?
//
// Every element has ID (needs to have a structure to support cloning)
// Maybe you can have '*' or 'ID' in selectors.
//
// It only works if you have a sensible type?
// Maybe need timestamps on edits (like git) so that we can identify shared history with the "same" edits
//

type Element = 
  | Element of Attributes * Elements
  | Text of string

and Attributes = Map<string, string>
and Elements = Element list

type Selector = 
  | Any 
  | Tag of string 
  | Index of int 
type Selectors = Selector list

let eval sel (attrs:Map<_, _>) = 
  match sel with 
  | Any -> true
  | Tag t -> attrs.["tag"] = t
  | Index i -> attrs.["index"] = string i

// type Selector = Map<string, string> -> bool
// let Any : Selector = fun _ -> true
// let Tag t : Selector = fun m -> m.["tag"] = t
// let Index (i:int) : Selector = fun m -> m.["index"] = string i

type Path = 
  | Child of Map<string, string>
type Paths = Path list

// --------------------------------------------------------------------------------------
// Matching, folds, replaces
// --------------------------------------------------------------------------------------

let rec matchesText el (path:Paths) (sel:Selectors) = 
  match el with 
  | Text _ -> 
      let path = path |> List.rev
      List.length path = List.length sel &&
        (List.forall2 (fun (Child(attrs)) f -> eval f attrs) path sel)
  | _ -> false

let rec matches el (path:Paths) (sel:Selectors) = 
  match el with 
  | Element(attrs, _) -> 
      let path = Child(attrs)::path |> List.rev
      List.length path = List.length sel &&
        (List.forall2 (fun (Child(attrs)) f -> eval f attrs) path sel)
  | _ -> false

let fold f st el = 
  let rec loop path st el =
    let st = f path el st 
    match el with 
    | Element(attrs, children) -> 
        children |> List.fold (loop (Child(attrs)::path)) st
    | Text s -> 
        st
  loop [] st el      

let replace f el = 
  let rec loop path el =
    match f path el with 
    | Some res -> res
    | _ -> 
    match el with 
    | Element(attrs, children) -> 
        Element(attrs, List.map (loop (Child(attrs)::path)) children)
    | Text s -> 
        Text s
  loop [] el      

let select sel doc = 
  doc |> fold (fun p el st ->
    if matches el p sel then el::st else st) [] 

// --------------------------------------------------------------------------------------
// Edits
// --------------------------------------------------------------------------------------

type Edit =
  | SetAttr of Selectors * (string * string)
  | Nest of Selectors * (Elements -> Element)
  | EditText of Selectors * (string -> string)
  | Duplicate of Selectors
  | InsertBefore of Selectors * Element

let updateIndices el = 
  let rec loop i = function
    | Element(attrs, children) ->
        Element(attrs.Add("index", string i), List.mapi loop children)
    | el -> el
  loop 0 el 

let apply edit doc = 
  updateIndices <|
    match edit with 
    | InsertBefore(sel, ins) ->
        let last, sel = match List.rev sel with last::sel -> last, List.rev sel | _ -> failwith "apply.Duplicate: Needs selector"
        replace (fun p el ->
          match el with 
          | Element(attrs, children) when matches el p sel ->
              let nchildren = children |> List.collect (fun c ->
                match c with 
                | Element(attrs, _) when eval last attrs -> [ins; c]
                | _ -> [c])
              Some(Element(attrs, nchildren))
          | _ -> None) doc
    | Duplicate(sel) ->
        let last, sel = match List.rev sel with last::sel -> last, List.rev sel | _ -> failwith "apply.Duplicate: Needs selector"
        replace (fun p el -> 
          match el with 
          | Element(attrs, children) when matches el p sel -> 
              let nchildren = children |> List.collect (function 
                | Element(attrs, c) as el when eval last attrs -> [el; el]
                | el -> [el])
              Some(Element(attrs, nchildren))
          | _ -> None ) doc  
    | EditText(sel, f) -> 
        replace (fun p el -> 
          match el with 
          | Text(s) when matchesText el p sel -> Some(Text(f s))
          | _ -> None ) doc
    | Nest(sel, wrapper) -> 
        replace (fun p el -> 
          match el with 
          | Element(attrs, children) when matches el p sel -> 
              Some(wrapper [el])
          | _ -> None ) doc
    | SetAttr(sel, (k, v)) -> 
        replace (fun p el -> 
          match el with 
          | Element(attrs, children) when matches el p sel -> 
              Some(Element(attrs.Add(k, v), children))
          | _ -> None ) doc

(*
let rec merge edits1 edits2 = 
  match edits1, edits2 with 
  |

  | (SetAttr(_, ("tag", _)) as e1)::e1s, 

  | SetAttr of Selectors * (string * string)
  | Nest of Selectors * (Elements -> Element)
  | EditText of Selectors * (string -> string)
  | Duplicate of Selectors
  | InsertBefore of Selectors * Element
*)

// --------------------------------------------------------------------------------------
// DSL & Demo
// --------------------------------------------------------------------------------------

type H() = 
  static member (?) (_, s:string) = fun attrs children ->
    let children = children |> List.mapi (fun i -> function 
      | Element(attrs, c) -> Element(attrs.Add("index", string i), c)
      | e -> e)
    Element(Map.ofList(("tag", s)::attrs), children)
let h = H()
let txt s = Text(s)

let toHtml (f:string) el = 
  use wr = new System.IO.StreamWriter(f)
  let rec loop el = 
    match el with 
    | Text s -> wr.Write(s)
    | Element(attrs, children) ->
        let other = 
          attrs.Remove("tag").Remove("index") 
          |> Seq.map (fun (KeyValue(k, v)) -> $" {k}='{v}'")
          |> String.concat ""
        wr.Write($"""<{attrs.["tag"]}{other}>""")
        for el in children do loop el
        wr.Write($"""</{attrs.["tag"]}>""")
  loop el

let doc = 
  h?body [] [
    h?h1 [] [ txt "Programming conference 2023" ]
    h?h2 [] [ txt "List of people to invite" ]
    h?ul [] [
      h?li [] [ txt "Adele Goldberg, adele@xerox.com" ] 
      h?li [] [ txt "Margaret Hamilton, hamilton@mit.com" ] 
      h?li [] [ txt "Betty Jean Jennings, betty@rand.com" ] 
    ]
  ]

let people = [ Any; Tag("ul"); Tag("li") ]
let jean = [ Any; Tag("ul"); Index(2) ]

doc |> select people
doc |> select jean

let edits1 = [
  SetAttr([Any; Tag("ul")], ("tag", "table"))
  SetAttr([Any; Tag("table"); Tag("li") ], ("tag", "td"))
  Nest([Any; Tag("table"); Tag("td") ], h?tr [])
  Duplicate([Any; Tag("table"); Tag("tr"); Tag("td")])
  EditText([Any; Tag("table"); Tag("tr"); Index(0)], fun s -> s.Substring(0, s.IndexOf(',')))
  EditText([Any; Tag("table"); Tag("tr"); Index(1)], fun s -> s.Substring(s.IndexOf(',')+1))
  SetAttr([Any; Tag("table"); Tag("tr"); Tag("td") ], ("style", "border:solid 1px black"))
]

doc
|> apply edits1.[0]
|> apply edits1.[1]
|> apply edits1.[2]
|> apply edits1.[3]
|> apply edits1.[4]
|> apply edits1.[5]
|> apply edits1.[6]
|> toHtml "c:/temp/demo.html"

let edits2 = [
  EditText([Any; Tag("ul"); Index(2)], fun s -> 
    s.Replace("Betty Jean Jennings", "Jean Jennings Bartik"))
]

doc 
|> apply edits2.[0]

let edits3 = [
  InsertBefore([Any; Tag("ul"); Index(0)], h?li [] [ txt "Ada Lovelace, lovelace@royalsociety.ac.uk" ] )
]

doc 
|> apply edits3.[0]

module Conflicts = 
  let doc = 
    h?body [] [
      h?div [] [ 
        h?p [] [ txt "Hello world" ]
      ]
    ]
  let edit1 = SetAttr([Any; Tag("div")], ("tag", "article"))
  let edit2 = Duplicate([Any; Tag("div"); Tag("p")])

  doc |> apply edit1 |> apply edit2
  doc |> apply edit2 |> apply edit1

