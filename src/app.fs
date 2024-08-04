module Tbd.App.Main

open Tbd.Html
open Tbd.Doc
open Tbd.Demos
open System.Text.RegularExpressions

let (|Regex|_|) reg s = 
  let m = Regex.Match(s, "^" + reg + "$")
  if m.Success then Some [ for i in 1 .. m.Groups.Count-1 -> m.Groups.[i].Value ]
  else None


// --------------------------------------------------------------------------------------
// Command handling
// --------------------------------------------------------------------------------------

//type CommandState = 
  //{ }

module Commands = 
  let isRecord = function Record _ -> true | _ -> false
  let isList = function List _ -> true | _ -> false
  let parseCommand doc cursorSel recordedEds cmd = 
    let nd, trace = trace cursorSel doc |> Seq.head    
    
    let parseSel sel =
      [ for s in sel -> 
          match s, System.Int32.TryParse s with 
          | _, (true, n) -> Index n
          | "*", _ -> All
          | s, _ -> Field s ]
    let retEhEds eds = true, [ for ed in eds -> { Kind = ed } ]
    let retEd ed = false, [ { Kind = ed } ] 
    let ffld f = if f = "" then "=" + System.Convert.ToBase64String(System.Guid.NewGuid().ToByteArray()) else f

    match cmd with 
    | Regex "<([^ ]+) ([^ ]+)>" [tag; fld] ->
        WrapRecord(fld, tag, cursorSel) |> retEd
    | Regex "<([^ ]+)>" [tag] ->
        WrapRecord(ffld "", tag, cursorSel) |> retEd
    | Regex "\[([^ ]+)\]" [tag] ->
        WrapList(tag, cursorSel) |> retEd
    | Regex "@([^ ]+)" [fld] ->
        RecordRenameField(cursorSel, fld) |> retEd

    | Regex ":([^ ]+)=!" [evt] ->
        [ yield RecordAdd(cursorSel, evt, Record("x-event-handler", [])) 
          for op in recordedEds ->
            ListAppend(cursorSel @ [Field evt], represent op) ]
        |> retEhEds

    | Regex ":([^ ]*)=<([^> ]+)>" [fld; tag] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, Record(tag, [])) |> retEd
    | Regex ":([^ ]*)=\[([^\] ]+)\]" [fld; tag] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, List(tag, [])) |> retEd
    | Regex ":([^ ]*)=([0-9]+)" [fld; num] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, Primitive(Number (int num))) |> retEd
    | Regex ":([^ ]*)=/(.+)" [fld; sel] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, Reference(parseSel (sel.Split('/')))) |> retEd
    | Regex ":([^ ]*)=(.+)" [fld; str] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, Primitive(String str)) |> retEd

    | Regex ":<([^> ]+)>" [tag] when isList nd ->
        ListAppend(cursorSel, Record(tag, [])) |> retEd
    | Regex ":\[([^\] ]+)\]" [tag] when isList nd ->
        ListAppend(cursorSel, List(tag, [])) |> retEd
    | Regex ":([0-9]+)" [num] when isList nd ->
        ListAppend(cursorSel, Primitive(Number (int num))) |> retEd
    | Regex ":/(.+)" [sel] when isList nd ->
        ListAppend(cursorSel, Reference(parseSel (sel.Split('/')))) |> retEd
    | Regex ":(.+)" [str] when isList nd ->
        ListAppend(cursorSel, Primitive(String str)) |> retEd

    | _ -> failwithf "EnterCommand: Unsupported command >>%A<<" cmd

  let renderCommandHelp doc cursorSel (cmd:string) isRecording = 
    let nd, trace = trace cursorSel doc |> Seq.head    
    h?div [ "id" => "cmd" ] [
      let cmdgroups = [
        "Document edits", [
          "<", "<tag fld>", "Wrap current element as field in a record", true
          "<", "<tag>", "Wrap current element as field in a record", true
          "[", "[tag]", "Wrap current element as item in a list", true
          "@", "@fld", "Rename field holding the current element", 
            (not (List.isEmpty trace) && isRecord (fst (List.last trace)))

          ":", ":fld=num", "Add numerical field to current record", isRecord nd
          ":", ":fld=str", "Add string field to current record", isRecord nd
          ":", ":fld=/s1/s2/...", "Add reference field to current record", isRecord nd
          ":", ":fld=<tag>", "Add record field to current record", isRecord nd
          ":", ":fld=[tag]", "Add list field to current record", isRecord nd
          ":", ":fld=!", "Append recorded edits as event handler", isRecord nd 

          ":", ":num", "Add numerical value to current list", isList nd
          ":", ":str", "Add string value to current list", isList nd
          ":", ":/s1/s2/...", "Add reference value to current list", isList nd
          ":", ":<tag>", "Add record value to current list", isList nd
          ":", ":[tag]", "Add list value to current list", isList nd
          ]
        "Meta commands", [
          "alt + m", "", (if isRecording then "End macro recording" else "Start macro recording"), true
          "alt + e", "", "Evaluate all formulas", true
          "alt + z", "", "Undo last edit", true]
      ]
      if cmd.Length > 0 then 
        let current = cmdgroups |> List.collect snd |> List.filter (fun (k, _, _, b) -> b && cmd.StartsWith(k))
        if not (Seq.isEmpty current) then 
          yield h?h3 [] [text "Entering command..."]
          for _, args, _, _ in current do
            yield h?pre [] [text args]
      for title, cmds in cmdgroups do
        yield h?h3 [] [text title]
        yield h?ul [] [
          for k, _, doc, b in Seq.distinctBy (fun (k, _, doc, b) -> k, doc, b) cmds do
            if b then yield h?li [] [ 
              h?kbd [ "class" => if k.Contains "+" then "long" else "" ] [ text k ]
              h?span [ "class" => "doc" ] [ text doc ]
            ]
        ]
    ]
// --------------------------------------------------------------------------------------
// Navigation
// --------------------------------------------------------------------------------------

type LocationModifier = Before | After
type Cursor = int list * LocationModifier

type CursorMove = Backward | Forward

let locations nd : seq<Cursor * Selectors> = 
  let rec loop loc sel nd = seq {
    match nd with 
    | Primitive(String s) -> 
        yield (loc, Before), sel
        yield (loc, After), sel
    | Primitive(Number n) ->
        yield (loc, Before), sel
        yield (loc, After), sel
    | Record(tag, nds) ->
        yield (loc, Before), sel
        for i, (k, v) in Seq.indexed nds do 
          yield! loop (i::loc) (Field k::sel) v
        yield (loc, After), sel
    | List(tag, nds) ->
        yield (loc, Before), sel
        for i, v in Seq.indexed nds do 
          yield! loop (i::loc) (Index i::sel) v
        yield (loc, After), sel
    | Reference _ ->
        yield (loc, Before), sel
        yield (loc, After), sel
    }
  loop [] [] nd
  |> Seq.map (fun ((loc, md), sel) -> (List.rev loc, md), List.rev sel)

let moveCursor doc cur dir = 
  let locs = (locations doc).GetEnumerator()
  let rec back prev =
    if locs.MoveNext() then
      if fst locs.Current = cur then prev
      else back (Some locs.Current)
    else None
  let rec forw () = 
    if locs.MoveNext() then
      if fst locs.Current = cur then 
        if locs.MoveNext() then Some locs.Current else None
      else forw ()
    else None
  match dir with
  | Backward -> back None |> Option.defaultWith (fun _ -> Seq.head (locations doc))
  | Forward -> forw () |> Option.defaultWith (fun _ -> Seq.last (locations doc))


// --------------------------------------------------------------------------------------

type State = 
  { Initial : Node 
    Edits : Edit list 
    //SelectedNode : string option
    HighlightedSelector : Selectors option
    //ControlsLocation : float * float
    //HistoryIndex : Map<string, int>
    Location : int 

    CursorLocation : Cursor
    CursorSelector : Selectors

    Command : string 

    MacroRange : int option * int option
    }
  member x.CurrentDocument = 
    x.Edits.[0 .. x.Location]
    |> List.fold apply x.Initial
  member x.FinalDocument = 
    x.Edits
    |> List.fold apply x.Initial

type Event = 
  | MoveCursor of CursorMove

  | SwitchMacro
  | UndoLastEdit
  
  | StartCommand 
  | CancelCommand
  | BackspaceCommand
  | TypeCommand of string
  | EnterCommand

  | Show of int
  | Move of int 
  | Evaluate of all:bool
  | MergeEdits of Edit list
  | HighlightSelector of Selectors option

  //| SelectNode of option<string * (float * float)>
  //| MoveHistory of int 


let formatSelector state trigger sel = 
  let parts = sel |> List.map (function All -> "*" | Tag t -> ":" + t | Index i -> string i | Field f -> f)
  h?a [ 
    "href" => "javascript:;"
    "class" => if state.HighlightedSelector = Some sel then "hisel" else ""
    "mouseover" =!> fun _ _ -> trigger(HighlightSelector(Some sel)) 
    "mouseout" =!> fun _ _ -> trigger(HighlightSelector None) 
  ] [ 
    text ("/" + (String.concat "/" parts))
  ]

let rec formatNode state trigger (nd:Node) = 
  match nd with 
  | Primitive(Number n) -> text (string n)
  | Primitive(String s) -> text s
  | Reference(sel) -> formatSelector state trigger sel
  | List(tag, nds) -> h?span [] [
        yield text "["
        for i, nd in Seq.indexed nds do 
          if i <> 0 then yield text ", "
          yield formatNode state trigger nd
        yield text "]"
      ]
  | Record(tag, nds) -> h?span [] [
        yield text "{"
        for i, (f, nd) in Seq.indexed nds do 
          if i <> 0 then yield text ", "
          yield text $"{f}="
          yield formatNode state trigger nd
        yield text "}"
      ]

let renderContext state trigger = [
  if state.Command <> "" then
    yield h?span [ "class" => "input" ] [ text state.Command ]
  yield h?div [ "id" => "ctx" ] [ h?div [ "id" => "ctx-body" ] [
    yield h?div [ "class" => "loc" ] [
      let nd, trc = trace state.CursorSelector state.CurrentDocument |> Seq.head
      for nd, s in trc do h?span [] [
        yield text "<"
        match nd with 
        | Record(t, _) | List(t, _) -> yield h?strong [] [ text t ]
        | _ -> ()
        match s with 
        | Index i -> yield text $"[{i}]"
        | Tag t -> yield text $"[#{t}]"
        | All -> yield text $"[*]"
        | Field f when f.[0] = '=' -> yield text ""
        | Field f -> yield text ("." + f)
        yield text ">"
      ]
      h?span [] [ 
        let pf = if snd state.CursorLocation = After then "(after)" else "(before)" 
        match nd with 
        | Record(t, _) -> text $"{pf} record {t}"
        | List(t, _) -> text $"{pf} list {t}"
        | Primitive(String s) -> text $"{pf} string '{s}'"
        | Primitive(Number n) -> text $"{pf} number '{n}'"
        | Reference r -> text $"{pf} reference '{r}'"
      ]
    ]
    let isRecording = match state.MacroRange with Some _, None -> true | _ -> false
    yield Commands.renderCommandHelp state.CurrentDocument state.CursorSelector state.Command isRecording 
  ] ] ]

(*
let rec getPreviousNode nd i = 
  match nd.Previous with 
  | _ when i = 0 -> nd 
  | Some nd -> getPreviousNode nd (i - 1)
  | None -> nd
  *)
let rec renderNode state trigger path pid nd = 
  let (++) s1 s2 = if s1 <> "" then s1 + "_" + s2 else s2
  (*
  let nd, historyIndex = 
    match state.HistoryIndex.TryFind(pid) with 
    | Some hist -> getPreviousNode nd hist, hist
    | _ -> nd, 0
  *)
  let tag = 
    match nd with 
    | List(tag, _) | Record(tag, _) -> tag
    | Primitive(Number _) -> "x-prim-num"
    | Primitive(String _) -> "x-prim-str"
    | Reference _ -> "x-ref"
  let handlers = 
    match nd with 
    | Record(_, nds) -> nds |> List.choose (function
        | id, List("x-event-handler", edits) ->
            Some(id =!> fun _ _ ->
              let handler = [ for e in edits -> unrepresent e ]
              trigger(Evaluate(true))
              trigger(MergeEdits(state.Edits @ handler))
              trigger(Evaluate(true))
              trigger(Move(System.Int32.MaxValue))
            )
        | _ -> None)
    | _ -> []
  let handlers = 
    if tag <> "input" then handlers else
    [ "change" =!> fun el _ ->
          let el = unbox<Browser.Types.HTMLInputElement> el
          let ed = RecordAdd(path, "@value", Primitive(String el.value))
          trigger(MergeEdits(state.Edits @ [ { Kind = ed } ]))
    ] @ handlers

  let rcdattrs = 
    match nd with 
    | Record(_, nds) -> nds |> List.choose (function 
        | n, Primitive(String s) when n.StartsWith("@") -> Some(n.Substring(1) => s)
        | _ -> None)
    | _ -> []
  let attrs = [ 
    yield "id" => pid 
    yield "class" => 
      ( match state.HighlightedSelector with Some s when matches s path -> "hidoc " | _ -> "") + 
      //( if historyIndex > 0 then "historical " else "") +
      ( if matches state.CursorSelector path then 
          if snd state.CursorLocation = Before then "cursor cursor-before "
          else "cursor cursor-after "
        else "")
    yield! handlers
    yield! rcdattrs
    (*
    if List.forall (fun (k, _) -> k <> "click") handlers then
      yield "click" =!> fun h e ->
        if (unbox<Browser.Types.MouseEvent> e).ctrlKey then
          e.cancelBubble <- true;
          trigger(SelectNode(Some(pid, (h.offsetLeft(* + h.offsetWidth*), h.offsetTop))))
    *)
  ] 
  let body = [
    (*
    if state.SelectedNode = Some pid then 
      let x, y = state.ControlsLocation      
      let canDown = historyIndex > 0 
      let canUp = nd.Previous.IsSome
      yield h?div ["id" => "hcontrols"; "style" => $"left:{int x}px; top:{int y}px"] [
        h?i [ "class" => "fa fa-circle-chevron-left " + if canDown then "" else "disabled"; 
              "click" =!> fun _ e -> e.cancelBubble <- true; if canDown then trigger(MoveHistory -1) ] []
        h?span ["class"=>"histindex"] [ text (string historyIndex) ]
        h?i [ "class" => "fa fa-circle-chevron-right " + if canUp then "" else "disabled"; 
              "click" =!> fun _ e -> e.cancelBubble <- true; if canUp then trigger(MoveHistory 1) ] []
        h?span [ "class" => "details" ] [ formatNode state trigger nd ]
      ]
      *)
    match nd with 
    | Record("x-formula", nds) -> 
        let op = nds |> List.tryFind (fun (f,_) -> f = "op") |> Option.map snd
        let args = nds |> List.filter (fun (f,_)-> f <> "op")
        if op.IsSome then yield! renderNode state trigger (path @ [Field "op"]) (pid ++ "op") op.Value
        else yield text "@"
        yield text "("
        for i, (f, a) in Seq.indexed args do
          if i <> 0 then yield text ", "
          yield text $"{f}="
          yield! renderNode state trigger (path @ [Field f]) (pid ++ f) a
        yield text ")"
    | List(_, nds) -> 
        for i, a in Seq.indexed nds do
          yield! renderNode state trigger (path @ [Index i]) (pid ++ string i) a
    | Record(_, nds) -> 
        for f, a in nds do
          if not (f.StartsWith("@")) then
            yield! renderNode state trigger (path @ [Field f]) (pid ++ f) a
    | Reference(sel) -> yield formatSelector state trigger sel
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

  [ //if matches state.CursorSelector path && snd state.CursorLocation = Before then 
      //yield! renderContext state trigger
    yield h?(tag) attrs body 
    //if matches state.CursorSelector path && snd state.CursorLocation = After then 
      //yield! renderContext state trigger
    ]
     

let renderEdit trigger state i ed doc = 
  let recorded = match state.MacroRange with Some l, Some h -> i >= l && i <= h | _ -> false
  let render n fa sel args = 
    h?li ["class" => (if recorded then "recorded" else "") ] [             
      h?a [ 
        "class" => 
          (if i = state.Location then "sel " else " ") //+ 
          //(if enabled doc ed then "" else "eval ") 
        "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(Show i) 
      ] [ 
        yield h?i [ "class" => "fa " + fa ] [] 
        yield text " "
        yield h?strong [] [ text n ]
        yield text " at "
        yield formatSelector state trigger sel
        yield text " with ("
        for i, (k, v) in Seq.indexed args do
          if i <> 0 then yield text ", "
          yield text $"{k} = "
          yield v
        yield text ")"
        //if ed.Conditions <> [] then 
          //yield text " [*]"
      ]
    ]
  match ed.Kind with 
  | ListAppend(sel, nd) -> render "append" "fa-at" sel ["node", formatNode state trigger nd]
  | PrimitiveEdit(sel, fn) -> render "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
  | ListReorder(sel, perm) -> render "reorder" "fa-list-ol" sel ["perm", text (string perm)]
  | Copy(src, tgt) -> render "copy" "fa-copy" tgt ["from", formatSelector state trigger src]
  | WrapRecord(id, tg, sel) -> render "wraprec" "fa-regular fa-square" sel ["id", text id; "tag", text tg]
  | WrapList(tg, sel) -> render "wraplist" "fa-solid fa-list-ul" sel ["tag", text tg]
  | Replace(sel, nd) -> render "replace" "fa-repeat" sel ["node", formatNode state trigger nd]
  | RecordAdd(sel, f, nd) -> render "addfield" "fa-plus" sel ["node", formatNode state trigger nd; "fld", text f]
  | UpdateTag(sel, t1, t2) -> render "retag" "fa-code" sel ["t1", text t1; "t2", text t2]
  | RecordRenameField(sel, id) -> render "updid" "fa-font" sel ["id", text id]



let render trigger (state:State) = 
  printfn "%A" state.CurrentDocument
  h?div [] [
    h?div [ "id" => "main" ] [
      yield h?div [ "id" => "doc" ] [
        let doc = state.CurrentDocument // Matcher.applyMatchers state.CurrentDocument 
        yield! renderContext state trigger
        yield! renderNode state trigger [] "" doc
      ]
      yield h?div [ "id" => "edits" ] [
        h?button ["click" =!> fun _ _ -> trigger (Evaluate(false)) ] [text "Eval step!"]
        h?button ["click" =!> fun _ _ -> trigger (Evaluate(true)) ] [text "Eval all!"]
        h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ opsBudget)) ] [text "Add budget"]
        h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ opsBudget @ addSpeakerOps)) ] [text "Add speaker"]
        h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ fixSpeakerNameOps)) ] [text "Fix name"]
        h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ refactorListOps)) ] [text "Refacor list"]
        //h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addTransformOps)) ] [text "Add transformers"]
        h?ol [] [
          if not (Seq.isEmpty state.Edits) then
            let indexed = Seq.indexed state.Edits
            let (_, headEd), tail = Seq.head indexed, Seq.tail indexed
            let edits = tail |> Seq.scan (fun (_, ed, st) (i, nextEd) -> i, nextEd, apply st ed) (0, headEd, state.Initial)
            for i, ed, doc in Seq.rev edits -> renderEdit trigger state i ed doc
        ]
      ]
    ]
    h?script [ "type" => "application/json"; "id" => "serialized" ] [
      text (Serializer.nodesToJsonString (List.map represent state.Edits))
    ]
  ]

//let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
//let ops1 = merge (opsCore @ refactorListOps) (merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps))
//let ops = merge ops1 (opsCore @ opsBudget)
//let ops = merge (opsCore @ opsBudget) ops1

//let ops = opsCore @ opsBudget
//let ops = [] //opsCore 

let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","=vsI7ZGu0ekafcavqvbN3Ww=="],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it","Todo list demo"]]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","=dX7kLxMX6U6MMViZT8DqmQ=="],["id","h1"],["target",{"kind":"list","tag":"x-selectors","nodes":["=vsI7ZGu0ekafcavqvbN3Ww=="]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","items"],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it",{"kind":"list","tag":"ul","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items",0]}],["field","done"],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items",0]}],["field","label"],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it","Do some work"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items",0,"done"]}],["field","@type"],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","input"],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it",{"kind":"record","tag":"button","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","=p/fbupTXCkehmk6J9kKaeA=="],["node",{"kind":"record","tag":"x-node-wrapper","nodes":[["it","Add"]]}]]}]"""
let ops = List.map unrepresent (Serializer.nodesFromJsonString json)

//let ops = opsBaseCounter
//let ops = opsBaseCounter //@ opsCounterInc @ opsCounterHndl
  
let state = 
  { Initial = rcd "div"
    HighlightedSelector = None
    Edits = ops
    //HistoryIndex = Map.empty
    //ControlsLocation = 0.0, 0.0
    //SelectedNode = None
    Location = ops.Length - 1 
    CursorLocation = [], Before
    CursorSelector = []
    Command = ""
    MacroRange = None, None
    }

let rec update (state:State) = function
  (*
  | MoveHistory diff ->
    match state.SelectedNode with 
    | Some nd -> 
        let hist = state.HistoryIndex.TryFind(nd) |> Option.defaultValue 0
        { state with HistoryIndex = state.HistoryIndex.Add(nd, hist + diff) }
    | _ -> state
  | SelectNode(None) ->
    { state with SelectedNode = None }
  | SelectNode(Some(pid, pos)) ->
    { state with SelectedNode = Some(pid); ControlsLocation = pos }
  *)
  | UndoLastEdit ->
    let nedits = List.truncate (state.Edits.Length - 1) state.Edits
    { state with Edits = nedits; Location = min state.Location (nedits.Length - 1) }
    
  | HighlightSelector sel ->
    { state with HighlightedSelector = sel }
  | Evaluate all -> 
    let edits = 
      if all then state.FinalDocument |> evaluateAll |> List.ofSeq
      else state.FinalDocument |> evaluateDoc
    let nedits = state.Edits @ edits
    { state with Edits = nedits; Location = nedits.Length-1 }
  | MergeEdits edits ->
    let state = { state with Edits = merge state.Edits edits } 
    { state with Location = state.Edits.Length-1 }
  | Move d ->
    { state with Location = max 0 (min (state.Edits.Length - 1) (state.Location + d)) }
  | Show i ->
    { state with Location = i }


  | MoveCursor dir ->
    let ncur, nsel = moveCursor state.CurrentDocument state.CursorLocation dir
    //printfn $"CURSOR {ncur}\nSEL {nsel}"
    { state with CursorLocation = ncur; CursorSelector = nsel }

  | StartCommand -> { state with Command = "" }
  | CancelCommand -> { state with Command = "" }
  | BackspaceCommand -> 
      if state.Command.Length <= 1 then { state with Command = "" }
      else { state with Command = state.Command.[0 .. state.Command.Length-2] }
  | TypeCommand c -> 
      { state with Command = state.Command + c }
  | EnterCommand -> 
      let recordedEds =
        match state.MacroRange with 
        | Some l, Some h -> state.Edits.[l .. h]
        | _ -> []
      let resetMacro, eds = Commands.parseCommand state.CurrentDocument state.CursorSelector recordedEds state.Command
      { state with 
          Edits = state.Edits @ eds
          MacroRange = if resetMacro then None, None else state.MacroRange
          Location = state.Edits.Length + eds.Length - 1; Command = "" }      
    | SwitchMacro -> 
        match state.MacroRange with 
        | Some s, None -> 
            { state with MacroRange = Some s, Some (state.Edits.Length-1) }
        | _ -> 
            { state with MacroRange = Some (state.Edits.Length), None }

let trigger, _ = createVirtualDomApp "out" state render update
//Browser.Dom.window.onclick <- fun e -> 
//  trigger(SelectNode None)

Browser.Dom.window.onkeypress <- fun e -> 
  if (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" then
    e.preventDefault();
    trigger(TypeCommand e.key)
  
Browser.Dom.window.onkeydown <- fun e -> 
  if e.ctrlKey then
    if e.key = "ArrowUp" then e.preventDefault(); trigger(Move +1)
    if e.key = "ArrowDown" then e.preventDefault(); trigger(Move -1)
  else
    //Browser.Dom.console.log(e.ctrlKey, e.altKey, e.key)
    if e.key = "Escape" then e.preventDefault(); trigger(CancelCommand)
    if e.key = "Backspace" then e.preventDefault(); trigger(BackspaceCommand)
    if e.key = "Enter" then e.preventDefault(); trigger(EnterCommand)
    if e.key = "ArrowRight" then e.preventDefault(); trigger(MoveCursor Forward)
    if e.key = "ArrowLeft" then e.preventDefault(); trigger(MoveCursor Backward)

    if e.altKey && e.key = "e" then e.preventDefault(); trigger(Evaluate(true))
    if e.altKey && e.key = "m" then e.preventDefault(); trigger(SwitchMacro)
    if e.altKey && e.key = "z" then e.preventDefault(); trigger(UndoLastEdit)


//trigger (MergeEdits(opsCore @ opsBudget))
//trigger (Evaluate true)
//trigger (Move 100000)
