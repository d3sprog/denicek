type Element = 
  | Text of string
  | Emphasis of Elements
  | Paragraph of Elements
  | Heading of int * Elements
  | List of Elements list
  | Table of string list * Elements list

and Elements = Element list


type Selector =
  | Nth of int list
  | Children

type Selectors = Selector list

let rec select sel els = 
  match sel with 
  | [] -> els
  | Nth(is)::sel ->
      select sel [ for i in is -> els.[i] ] 
  | Children::sel ->
      [ for el in els do 
          match el with 
          | Emphasis els | Paragraph els | Heading(_, els) -> yield! els
          | List(elss) | Table(_, elss) -> yield! Seq.concat elss
          | _ -> () ] |> select sel

let rec replace sel repl (els:_ list) = 
  match sel with 
  | [] -> repl
  | Nth(is)::sel ->
      [ for i, el in Seq.indexed els do
          if List.contains i is then 
            yield! replace sel repl els.[i .. i] 
          else yield el ]
  | Children::sel ->
      failwith "TODO"

type Edit =
  | MakeTable of Selectors * Selectors
  | SplitColumn of Selectors * string * string list * (Element -> Element list)


let apply edit els = 
  match edit with
  | MakeTable(replaceSel, child) ->
      let repl = Table(["Column"], List.map List.singleton (select child els))
      replace replaceSel [repl] els
  | SplitColumn(tableSel, col, newCols, splitter) ->
      match select tableSel els with
      | [Table(cols, rows)] ->
          let i = List.tryFindIndex ((=) col) cols // NOTE: Does not handle duplicates
          let i = match i with Some i -> i | _ -> failwithf "apply.SplitColumn: Column '%s' not found" col
          let ncols = cols |> List.collect (fun c -> if c = col then newCols else [c])
          let nrows = rows |> List.map (fun row -> 
            List.indexed row |> List.collect (fun (j, col) -> 
              if i = j then splitter col else [col]))
          replace tableSel [Table(ncols, nrows)] els
      | _ -> failwith "apply.SplitColumn: Expected single table"
      
let doc = 
  [ Heading(1, [ Text "Programming conference 2023" ]) 
    Heading(2, [ Text "List of people to invite"])
    List [
      [ Paragraph [ Text "Adele Goldberg, adele@xerox.com" ] ]
      [ Paragraph [ Text "Margaret Hamilton, hamilton@mit.com" ] ]
      [ Paragraph [ Text "Jean Jennings Bartik, betty@rand.com" ] ]
    ]
  ]

let edits = [ 
  MakeTable([Nth [2]], [ Nth [2]; Children; Children ])
  SplitColumn([Nth [2]], "Column", ["Name"; "Email"], fun (Text s) -> 
    let i = s.IndexOf(',') in [Text(s.Substring(0, i).Trim()); Text(s.Substring(i+1).Trim())]
  )
  SplitColumn([Nth [2]], "Name", ["First"; "Last"], fun (Text s) -> 
    let i = s.IndexOf(' ') in [Text(s.Substring(0, i).Trim()); Text(s.Substring(i+1).Trim())]
  )
]

doc 
|> apply edits.[0]
|> apply edits.[1]
|> apply edits.[2]
