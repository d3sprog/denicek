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
      let repls = replace sel repl [ for i in is -> els.[i] ]
      [ for i, el in Seq.indexed els ->
          if List.contains i is then 
            let j = List.findIndex ((=) i) is
            repls.[j]
          else el ]
  | Children::sel ->
      [ for el in els do 
          match el with 
          | Emphasis els -> Emphasis(replace sel repl els)
          | Paragraph els -> Paragraph(replace sel repl els)
          | Heading(n, els) -> Heading(n, replace sel repl els)
          | List(elss) -> List([for els in elss -> replace sel repl els])
          | Table(cols, elss) -> Table(cols,[for els in elss -> replace sel repl els])
          | el -> el ]

type Edit =
  | EditElement of Selectors * (Element -> Element)
  | MakeTable of Selectors * Selectors
  | SplitColumn of Selectors * string * string list * (Element -> Element list)

let apply edit els = 
  match edit with
  | EditElement(elementSel, update) ->
      replace elementSel (List.map update (select elementSel els)) els
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
      [ Paragraph [ Text "Betty Jean Jennings, betty@rand.com" ] ]
    ]
  ]

let edits1 = [ 
  MakeTable([Nth [2]], [ Nth [2]; Children; Children ])
  SplitColumn([Nth [2]], "Column", ["Name"; "Email"], fun (Text s) -> 
    let i = s.IndexOf(',') in [Text(s.Substring(0, i).Trim()); Text(s.Substring(i+1).Trim())]
  )
  SplitColumn([Nth [2]], "Name", ["First"; "Last"], fun (Text s) -> 
    let i = s.IndexOf(' ') in [Text(s.Substring(0, i).Trim()); Text(s.Substring(i+1).Trim())]
  )
]

let edits2 = [
  EditElement([Nth [2]; Children; Nth [2]; Children], fun (Text s) ->
    Text(s.Replace("Betty Jean Jennings", "Jean Jennings Bartik"))
  )
]

doc 
|> apply edits1.[0]
|> apply edits1.[1]
|> apply edits1.[2]

doc
|> apply edits2.[0]

let elementSel = [Nth [2]; Children; Nth [2]; Children]

select elementSel doc
replace elementSel [Text "!!!"] doc
