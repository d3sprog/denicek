module Tbd.App.Main

open Tbd.Html
open Tbd.Doc
open Tbd.Demos

let (+?) s1 (b, s2) = if b then (s1 + " " + s2) else s1

// --------------------------------------------------------------------------------------
// Document state
// --------------------------------------------------------------------------------------

type DocumentState = 
  { Initial : Node 
    Edits : Edit list 
    EditIndex : int }
  
  member x.CurrentDocument = 
    x.Edits.[0 .. x.EditIndex]
    |> List.fold apply x.Initial
  
  member x.FinalDocument = 
    x.Edits
    |> List.fold apply x.Initial

type DocumentEvent = 
  | UndoLastEdit
  | Evaluate of all:bool
  | MergeEdits of Edit list
  | SetEditIndex of int
  | MoveEditIndex of int 

module Doc = 
  let update state e = 
    match e with 
    | UndoLastEdit ->
        let nedits = List.truncate (state.Edits.Length - 1) state.Edits
        { state with Edits = nedits; EditIndex = min state.EditIndex (nedits.Length - 1) }
    
    | Evaluate all -> 
        let edits = 
          if all then state.FinalDocument |> evaluateAll |> List.ofSeq
          else state.FinalDocument |> evaluateDoc
        let nedits = state.Edits @ edits
        { state with Edits = nedits; EditIndex = nedits.Length-1 }
  
    | MergeEdits edits ->
        let state = { state with Edits = merge state.Edits edits } 
        { state with EditIndex = state.Edits.Length-1 }
  
    | MoveEditIndex d ->
        { state with EditIndex = max 0 (min (state.Edits.Length - 1) (state.EditIndex + d)) }

    | SetEditIndex i ->
        { state with EditIndex = i }

// --------------------------------------------------------------------------------------
// History state
// --------------------------------------------------------------------------------------

type HistoryState = 
  { HighlightedSelector : Selectors option
    SelectedEdits : Set<int>
    Display : bool }

type HistoryEvent = 
  | HighlightSelector of Selectors option
  | ToggleEdit of int * bool
  | ExtendSelection of int (* -1 or +1 *)
  | SelectAll 
  | SelectNone
  | ToggleEditHistory
  
module History = 
  let update docState state = function
    | ToggleEditHistory -> 
        { state with Display = not state.Display }
    | ExtendSelection(dir) ->
        let nsel = set [ docState.EditIndex; docState.EditIndex+dir ]
        let other = 
          Seq.initInfinite (fun i -> docState.EditIndex-(i*dir)) 
          |> Seq.takeWhile (state.SelectedEdits.Contains)
          |> set
        { state with SelectedEdits = nsel + other  }
    | ToggleEdit(i, true) ->
        { state with SelectedEdits = state.SelectedEdits.Add(i) }
    | ToggleEdit(i, false) ->
        { state with SelectedEdits = state.SelectedEdits.Remove(i) }
    | HighlightSelector sel ->
        { state with HighlightedSelector = sel }        
    | SelectNone ->
        { state with SelectedEdits = set [] }
    | SelectAll ->
        { state with SelectedEdits = set [ 0 .. docState.Edits.Length - 1 ] }


  let formatSelector state trigger sel = 
    let parts = sel |> List.map (function All -> "*" | Tag t -> ":" + t | Index i -> string i | Field f -> f)
    h?a [ 
      "href" => "javascript:;"
      "class" => if state.HighlightedSelector = Some sel then "hselhist" else ""
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

  let formatSource state trigger = function
    | ConstSource nd -> formatNode state trigger nd
    | RefSource sel -> formatSelector state trigger sel

  let renderEdit trigger histState triggerDoc docState (i, ed) = 
    let render n fa sel args = 
      h?li [] [ 
        h?input [ 
          yield "type" => "checkbox"
          if histState.SelectedEdits.Contains(i) then yield "checked" => "checked"
          yield "click" =!> fun el _ ->
            let chk = (unbox<Browser.Types.HTMLInputElement> el).``checked``
            trigger(ToggleEdit(i, chk))
        ] []
        h?a [ 
          "class" => "" +? (i = docState.EditIndex, "sel")
          "href" => "javascript:;"; "click" =!> fun _ _ -> triggerDoc(SetEditIndex i)
        ] [ 
          yield h?i [ "class" => "fa " + fa ] [] 
          yield text " "
          yield h?strong [] [ text n ]
          yield text " at "
          yield formatSelector histState trigger sel
          yield text " with ("
          for i, (k, v) in Seq.indexed args do
            if i <> 0 then yield text ", "
            yield text $"{k} = "
            yield v
          yield text ")"
        ]
      ]
    match ed.Kind with 
    | ListAppend(sel, nd) -> render "append" "fa-at" sel ["node", formatSource histState trigger nd]
    | PrimitiveEdit(sel, fn) -> render "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
    | ListReorder(sel, perm) -> render "reorder" "fa-list-ol" sel ["perm", text (string perm)]
    | Copy(tgt, src) -> render "copy" "fa-copy" tgt ["from", formatSource histState trigger src]
    | WrapRecord(id, tg, sel) -> render "wraprec" "fa-regular fa-square" sel ["id", text id; "tag", text tg]
    | WrapList(tg, sel) -> render "wraplist" "fa-solid fa-list-ul" sel ["tag", text tg]
    | RecordAdd(sel, f, nd) -> render "addfield" "fa-plus" sel ["node", formatSource histState trigger nd; "fld", text f]
    | UpdateTag(sel, t1, t2) -> render "retag" "fa-code" sel ["t1", text t1; "t2", text t2]
    | RecordRenameField(sel, id) -> render "updid" "fa-font" sel ["id", text id]
    | Delete(sel) -> render "del" "fa-xmark" sel []

  let renderHistory trigger histState triggerDoc docState = 
    if not histState.Display then [] else [
      h?div [ "id" => "edits" ] [
        h?button ["click" =!> fun _ _ -> triggerDoc((Evaluate(false))) ] [text "Eval step!"]
        h?button ["click" =!> fun _ _ -> triggerDoc((Evaluate(true))) ] [text "Eval all!"]
        h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ opsBudget))) ] [text "Add budget"]
        h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ opsBudget @ addSpeakerOps))) ] [text "Add speaker"]
        h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ fixSpeakerNameOps))) ] [text "Fix name"]
        h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ refactorListOps))) ] [text "Refacor list"]
        //h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addTransformOps)) ] [text "Add transformers"]
        h?p [] [ 
          text "Use "
          h?kbd [] [ text "ctrl+shift+up"]
          text " / "
          h?kbd [] [ text "ctrl+shift+down"]
          text " to select a range of edits"
        ]
        h?p [] [
          text "Select edits "
          h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(SelectNone) ] [ text "none" ]
          text " | "
          h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(SelectAll) ] [ text "all" ]
        ]
        h?ol [] [
          for ied in Seq.rev (Seq.indexed docState.Edits) -> 
            renderEdit trigger histState triggerDoc docState ied
        ]
      ] 
    ]

// --------------------------------------------------------------------------------------
// Command handling
// --------------------------------------------------------------------------------------

type CommandState =
  { Command : string 
    CopySource : Selectors option }

type CommandEvent = 
  | CancelCommand
  | BackspaceCommand
  | TypeCommand of string
  | EnterCommand
  //| SwitchMacro
  | CopyNode  
  
module Commands = 
  open System.Text.RegularExpressions

  let isRecord = function Record _ -> true | _ -> false
  let isList = function List _ -> true | _ -> false

  let (|Regex|_|) reg s = 
    let m = Regex.Match(s, "^" + reg + "$")
    if m.Success then Some [ for i in 1 .. m.Groups.Count-1 -> m.Groups.[i].Value ]
    else None
  
  let parseCommand doc cursorSel recordedEds state = 
    let cmd = state.Command
    let nd, _ = trace cursorSel doc |> Seq.head
    
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
    | "!v" ->        
        match state.CopySource with
        | Some src -> Copy(cursorSel, RefSource src) |> retEd
        | _ -> failwith "parseCommand - no source specified for !v"
    | "!d" ->
        Delete(cursorSel) |> retEd
    | Regex "<([^ ]+) ([^ ]+)>" [tag; fld] ->
        WrapRecord(fld, tag, cursorSel) |> retEd
    | Regex "<([^ ]+)>" [tag] ->
        WrapRecord(ffld "", tag, cursorSel) |> retEd
    | Regex "\[([^ ]+)\]" [tag] ->
        WrapList(tag, cursorSel) |> retEd
    | Regex "@([^ ]+)" [fld] ->
        RecordRenameField(cursorSel, fld) |> retEd

    | Regex ":([^ ]+)=!m" [evt] ->
        [ yield RecordAdd(cursorSel, evt, ConstSource(List("x-event-handler", [])))
          for op in recordedEds ->
            ListAppend(cursorSel @ [Field evt], ConstSource(represent op)) ]
        |> retEhEds

    | Regex ":([^ ]*)=!v" [fld] when isRecord nd ->
        match state.CopySource with
        | Some src -> RecordAdd(cursorSel, ffld fld, RefSource(src)) |> retEd
        | _ -> failwith "parseCommand - no source specified for !v"        
    | Regex ":([^ ]*)=<([^> ]+)>" [fld; tag] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, ConstSource(Record(tag, []))) |> retEd
    | Regex ":([^ ]*)=\[([^\] ]+)\]" [fld; tag] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, ConstSource(List(tag, []))) |> retEd
    | Regex ":([^ ]*)=([0-9]+)" [fld; num] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, ConstSource(Primitive(Number (int num)))) |> retEd
    | Regex ":([^ ]*)=/(.+)" [fld; sel] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, ConstSource(Reference(parseSel (sel.Split('/'))))) |> retEd
    | Regex ":([^ ]*)=(.+)" [fld; str] when isRecord nd ->
        RecordAdd(cursorSel, ffld fld, ConstSource(Primitive(String str))) |> retEd

    | ":!v" when isList nd ->
        match state.CopySource with
        | Some src -> ListAppend(cursorSel, RefSource(src)) |> retEd
        | _ -> failwith "parseCommand - no source specified for !v"        
    | Regex ":<([^> ]+)>" [tag] when isList nd ->
        ListAppend(cursorSel, ConstSource(Record(tag, []))) |> retEd
    | Regex ":\[([^\] ]+)\]" [tag] when isList nd ->
        ListAppend(cursorSel, ConstSource(List(tag, []))) |> retEd
    | Regex ":([0-9]+)" [num] when isList nd ->
        ListAppend(cursorSel, ConstSource(Primitive(Number (int num)))) |> retEd
    | Regex ":/(.+)" [sel] when isList nd ->
        ListAppend(cursorSel, ConstSource(Reference(parseSel (sel.Split('/'))))) |> retEd
    | Regex ":(.+)" [str] when isList nd ->
        ListAppend(cursorSel, ConstSource(Primitive(String str))) |> retEd

    | _ -> failwithf "EnterCommand: Unsupported or disabled command >>%A<<" cmd

  let renderCommandHelp doc cursorSel state = 
    //let isRecording = match state.MacroRange with Some _, None -> true | _ -> false
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
          ":", ":fld=!v", "Add copied node to current record", isRecord nd 
          ":", ":fld=!m", "Add selected edits as event handler", isRecord nd 

          ":", ":num", "Add numerical value to current list", isList nd
          ":", ":str", "Add string value to current list", isList nd
          ":", ":/s1/s2/...", "Add reference value to current list", isList nd
          ":", ":<tag>", "Add record value to current list", isList nd
          ":", ":[tag]", "Add list value to current list", isList nd
          ":", ":!v", "Add copied node to current list", isList nd 
          
          "!", "!v", "Paste currnet document node here", state.CopySource.IsSome
          "!", "!d", "Delete currnet document node", true
          ]
        "Document commands", [
          "alt + d", "", "Delete current document node", true
          "alt + c", "", "Copy current document node", true
          "alt + v", "", "Paste currnet document node here", state.CopySource.IsSome
        ]
        "Meta commands", [
          //"alt + m", "", (if isRecording then "End macro recording" else "Start macro recording"), true
          "alt + e", "", "Evaluate all formulas", true
          "alt + z", "", "Undo last edit", true
          "alt + u", "", "Toggle source code view", true
          "alt + h", "", "Toggle edit history view", true]
      ]
      if state.Command.Length > 0 then 
        let current = cmdgroups |> List.collect snd |> List.filter (fun (k, _, _, b) -> b && state.Command.StartsWith(k))
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


  let update docState state cmd = 
    match cmd with 
    | CancelCommand -> 
        { state with Command = "" }
    | BackspaceCommand -> 
        if state.Command.Length <= 1 then { state with Command = "" }
        else { state with Command = state.Command.[0 .. state.Command.Length-2] }
    | TypeCommand c -> 
        { state with Command = state.Command + c }
        (*
    | SwitchMacro -> 
        match state.MacroRange with 
        | Some s, None -> 
            { state with MacroRange = Some s, Some (docState.Edits.Length-1) }
        | _ -> 
            { state with MacroRange = Some (docState.Edits.Length), None }
            *)
    | CopyNode 
    | EnterCommand -> failwith "handled elsewhere"
    
// --------------------------------------------------------------------------------------
// Navigation
// --------------------------------------------------------------------------------------

type LocationModifier = Before | After
type Cursor = int list * LocationModifier

type CursorMove = Backward | Forward | Previous | Next

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
  let orFirst = Option.defaultWith (fun _ -> Seq.head (locations doc))
  let orLast = Option.defaultWith (fun _ -> Seq.last (locations doc))
  match dir, cur with
  | Previous, (loc, After) -> locations doc |> Seq.tryFind (fun (c, _) -> c = (loc, Before)) |> orFirst
  | Next, (loc, Before) -> locations doc |> Seq.tryFind (fun (c, _) -> c = (loc, After)) |> orLast
  | Previous, _ 
  | Backward, _ -> back None |> orFirst
  | Next, _
  | Forward, _ -> forw () |> orLast

let fixCursor doc cur = 
  let locs = locations doc |> dict
  let rec loop ((curi, curm) as cur) =
    if locs.ContainsKey(cur) then cur, locs.[cur]
    else loop (curi.[0 .. curi.Length - 2], curm)
  loop cur

// --------------------------------------------------------------------------------------
// Document state and edits
// --------------------------------------------------------------------------------------

type GlobalState = 
  { // View - cursor, selector and view source
    CursorLocation : Cursor
    CursorSelector : Selectors
    ViewSourceSelector : Selectors option

    CommandState : CommandState
    DocumentState : DocumentState
    HistoryState : HistoryState
  }

type Event =  
  // View related
  | MoveCursor of CursorMove
  | ToggleViewSource

  | HistoryEvent of HistoryEvent
  | CommandEvent of CommandEvent
  | DocumentEvent of DocumentEvent

// --------------------------------------------------------------------------------------
// Rendering
// --------------------------------------------------------------------------------------

let renderContext state trigger =
  h?div [ "id" => "ctx" ] [ h?div [ "id" => "ctx-body" ] [
    yield h?div [ "class" => "loc" ] [
      let nd, trc = trace state.CursorSelector state.DocumentState.CurrentDocument |> Seq.head
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
    yield Commands.renderCommandHelp state.DocumentState.CurrentDocument state.CursorSelector state.CommandState 
  ] ]

let (++) s1 s2 = if s1 <> "" then s1 + "_" + s2 else s2
  
let getTag nd = 
  match nd with 
  | List(tag, _) | Record(tag, _) -> tag
  | Primitive(Number _) -> "x-prim-num"
  | Primitive(String _) -> "x-prim-str"
  | Reference _ -> "x-reference"

let isPlainTextNode = function
  | Reference _ | Primitive _ | Primitive _ -> true | _ -> false
let isListNode = function List _ -> true | _ -> false
let cursorBefore state path =
  matches state.CursorSelector path && snd state.CursorLocation = Before 
let cursorAfter state path =
  matches state.CursorSelector path && snd state.CursorLocation = After
let highlightedSel state path =
  match state.HistoryState.HighlightedSelector with Some s -> matches s path | _ -> false
let commandBefore state path =
  matches state.CursorSelector path && snd state.CursorLocation = Before 
    && state.CommandState.Command <> ""
let commandAfter state path =
  matches state.CursorSelector path && snd state.CursorLocation = After
    && state.CommandState.Command <> ""

let rec renderTree state trigger path idAttrs nd = 
  h?div [
    "class" => 
      "treenode" 
      +? (isPlainTextNode nd, "inline") 
      +? (highlightedSel state path, "hseltree")
      +? (cursorBefore state path, "cursor cursor-before")
      +? (cursorAfter state path, "cursor cursor-after")
  ] [
    if commandBefore state path then 
      yield h?div [ "class" => "treeinput" ] [ text state.CommandState.Command ]    
    yield h?div ["class" => "treetag" ] [
      yield text "<"
      yield h?span [] [ text (getTag nd) ]
      for k, v in idAttrs do  
        yield text " "
        yield h?span [ "class" => "attrname" ] [ text k ]
        yield text "=\""
        yield h?span [ "class" => "attrvalue" ] [ text v ]
        yield text "\""
      yield text ">"
    ]
    yield h?div ["class" => "treebody" ] [
      match nd with
      | List(_, nds) -> 
          for i, a in Seq.indexed nds do
            yield renderTree state trigger (path @ [Index i]) ["index", string i] a
      | Record(_, nds) -> 
          for f, a in nds do
            //if not (f.StartsWith("@")) then
            yield renderTree state trigger (path @ [Field f]) ["id", f] a
      | Reference(sel) -> yield History.formatSelector state.HistoryState (HistoryEvent >> trigger) sel
      | Primitive(String s) -> yield text s
      | Primitive(Number n) -> yield text (string n)              
    ]
    yield h?div ["class" => "treetag" ] [
      text "</"
      h?span [] [ text (getTag nd) ]
      text ">"
    ]
  ]

(*
let rec getPreviousNode nd i = 
  match nd.Previous with 
  | _ when i = 0 -> nd 
  | Some nd -> getPreviousNode nd (i - 1)
  | None -> nd
  *)
let rec renderNode state trigger path pid nd = 
  match state.ViewSourceSelector with 
  | Some sel when matches path sel -> 
      [ h?div ["class" => "treedoc"] [ renderTree state trigger path [] nd ] ]
  | _ -> 
  (*
  let nd, historyIndex = 
    match state.HistoryIndex.TryFind(pid) with 
    | Some hist -> getPreviousNode nd hist, hist
    | _ -> nd, 0
  *)
  let tag = getTag nd
  let handlers = 
    match nd with 
    | Record(_, nds) -> nds |> List.choose (function
        | id, List("x-event-handler", edits) ->
            Some(id =!> fun _ _ ->
              let handler = [ for e in edits -> unrepresent e ]
              trigger(DocumentEvent(Evaluate(true)))
              trigger(DocumentEvent(MergeEdits(state.DocumentState.Edits @ handler)))
              trigger(DocumentEvent(Evaluate(true)))
              trigger(DocumentEvent(MoveEditIndex(System.Int32.MaxValue)))
            )
        | _ -> None)
    | _ -> []
  let handlers = 
    if tag <> "input" then handlers else
    [ "change" =!> fun el _ ->
          let el = unbox<Browser.Types.HTMLInputElement> el
          let ed = 
            if el.``type`` = "checkbox" && el.``checked`` then
              RecordAdd(path, "@checked", ConstSource(Primitive(String "checked")))
            elif el.``type`` = "checkbox" && not el.``checked`` then
              Delete(path @ [Field "@checked"])
            else
              RecordAdd(path, "@value", ConstSource(Primitive(String el.value)))
          trigger(DocumentEvent(MergeEdits(state.DocumentState.Edits @ [ { Kind = ed } ])))
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
      ""
      +? (highlightedSel state path, "hselnode")
      +? (cursorBefore state path, "cursor cursor-before")
      +? (cursorAfter state path, "cursor cursor-after")
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
    | Reference(sel) -> yield History.formatSelector state.HistoryState (HistoryEvent >> trigger) sel
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

  [ if commandBefore state path then 
      yield h?span [ "class" => "docinput" ] [ text state.CommandState.Command ]
    yield h?(tag) attrs body 
    if commandAfter state path then 
      yield h?span [ "class" => "docinput" ] [ text state.CommandState.Command ]    
  ]
     


let render trigger (state:GlobalState) = 
  h?div [] [
    h?div [ "id" => "main" ] [
      yield h?div [ "id" => "doc" ] [
        let doc = state.DocumentState.CurrentDocument // Matcher.applyMatchers state.CurrentDocument 
        yield! renderNode state trigger [] "" doc
      ]
      yield renderContext state trigger
      yield! History.renderHistory (HistoryEvent >> trigger) state.HistoryState (DocumentEvent >> trigger) state.DocumentState
    ]
    h?script [ "type" => "application/json"; "id" => "serialized" ] [
      text (Serializer.nodesToJsonString (List.map represent state.DocumentState.Edits))
    ]
  ]

// --------------------------------------------------------------------------------------
// Update operation
// --------------------------------------------------------------------------------------

let update (state:GlobalState) e = 
  match e with 
  | ToggleViewSource ->
      match state.ViewSourceSelector with 
      | None -> { state with ViewSourceSelector = Some state.CursorSelector }
      | Some _ -> { state with ViewSourceSelector = None }
  
  | MoveCursor dir ->
      let ncur, nsel = moveCursor state.DocumentState.CurrentDocument state.CursorLocation dir
      { state with CursorLocation = ncur; CursorSelector = nsel }
  

  | CommandEvent(CopyNode) ->
      { state with CommandState = { state.CommandState with CopySource = Some state.CursorSelector } }
  | CommandEvent(EnterCommand) -> 
      let recordedEds =
        [ for i in Seq.sort state.HistoryState.SelectedEdits ->
            state.DocumentState.Edits.[i] ]
      let resetSel, eds = 
        Commands.parseCommand state.DocumentState.CurrentDocument 
          state.CursorSelector recordedEds state.CommandState
      
      let doc = 
        { state.DocumentState with 
            EditIndex = state.DocumentState.Edits.Length + eds.Length - 1;
            Edits = state.DocumentState.Edits @ eds }

      let cursorLoc, cursorSel = fixCursor doc.CurrentDocument state.CursorLocation

      { state with 
          CursorSelector = cursorSel
          CursorLocation = cursorLoc
          DocumentState = doc
          HistoryState = { state.HistoryState with SelectedEdits = if resetSel then set [] else state.HistoryState.SelectedEdits }
          CommandState = { state.CommandState with Command = "" } }

  | CommandEvent e ->
      { state with CommandState = Commands.update state.DocumentState state.CommandState e }
  | DocumentEvent e ->
      { state with DocumentState = Doc.update state.DocumentState e }
  | HistoryEvent e ->
      { state with HistoryState = History.update state.DocumentState state.HistoryState e }

// --------------------------------------------------------------------------------------
// Initial state and global handlers
// --------------------------------------------------------------------------------------

//let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
//let ops1 = merge (opsCore @ refactorListOps) (merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps))
//let ops = merge ops1 (opsCore @ opsBudget)
//let ops = merge (opsCore @ opsBudget) ops1

//let ops = opsCore @ opsBudget

let json = """[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","=vXYI2bHIj0yhbcNIbNuHfw=="],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Todo list demo"]]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","=i6AeAzX8J0OnGsLAlCn35w=="],["id","h1"],["target",{"kind":"list","tag":"x-selectors","nodes":["=vXYI2bHIj0yhbcNIbNuHfw=="]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","items"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"ul","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-updateid","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["id","inp"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"button","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","=8zRye0YNiEqYYqO6GWzDvg=="],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Add"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp"]}],["field","@value"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Do some work"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","click"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"x-event-handler","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add","click"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add","click"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add","click"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add","click"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add","click"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add","click"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp"]}],["field","@value"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Testing todo list"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]"""
let ops = List.map unrepresent (Serializer.nodesFromJsonString json)
//let ops = [] //opsCore 

//let ops = opsBaseCounter
//let ops = opsBaseCounter @ opsCounterInc @ opsCounterHndl
  
let state = 
  { DocumentState = { Initial = rcd "div"; Edits = ops; EditIndex = ops.Length - 1 }
    CursorLocation = [], Before
    CursorSelector = []
    ViewSourceSelector = None
    CommandState = { Command = ""; CopySource = None }
    HistoryState = { HighlightedSelector = None; SelectedEdits = Set.empty; Display = false }
  }

let trigger, _ = createVirtualDomApp "out" state render update

Browser.Dom.window.onkeypress <- fun e -> 
  if (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" then
    e.preventDefault();
    trigger(CommandEvent(TypeCommand e.key))
  
Browser.Dom.window.onkeydown <- fun e -> 
  if (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" then
    if e.ctrlKey then
      if e.key = "ArrowUp" && e.shiftKey then e.preventDefault(); trigger(HistoryEvent(ExtendSelection +1))
      if e.key = "ArrowDown" && e.shiftKey then e.preventDefault(); trigger(HistoryEvent(ExtendSelection -1))
      if e.key = "ArrowUp" then e.preventDefault(); trigger(DocumentEvent(MoveEditIndex +1))
      if e.key = "ArrowDown" then e.preventDefault(); trigger(DocumentEvent(MoveEditIndex -1))
    else
      //Browser.Dom.console.log(e.ctrlKey, e.altKey, e.key)
      if e.key = "Escape" then e.preventDefault(); trigger(CommandEvent(CancelCommand))
      if e.key = "Backspace" then e.preventDefault(); trigger(CommandEvent(BackspaceCommand))
      if e.key = "Enter" then e.preventDefault(); trigger(CommandEvent(EnterCommand))
      if e.key = "ArrowRight" then e.preventDefault(); trigger(MoveCursor Forward)
      if e.key = "ArrowLeft" then e.preventDefault(); trigger(MoveCursor Backward)
      if e.key = "ArrowUp" then e.preventDefault(); trigger(MoveCursor Previous)
      if e.key = "ArrowDown" then e.preventDefault(); trigger(MoveCursor Next)

      if e.altKey && e.key = "e" then e.preventDefault(); trigger(DocumentEvent(Evaluate(true)))
      //if e.altKey && e.key = "m" then e.preventDefault(); trigger(CommandEvent(SwitchMacro))
      if e.altKey && e.key = "z" then e.preventDefault(); trigger(DocumentEvent(UndoLastEdit))
      if e.altKey && e.key = "u" then e.preventDefault(); trigger(ToggleViewSource)
      if e.altKey && e.key = "h" then e.preventDefault(); trigger(HistoryEvent(ToggleEditHistory))
      if e.altKey && e.key = "c" then e.preventDefault(); trigger(CommandEvent(CopyNode))
      if e.altKey && e.key = "v" then e.preventDefault(); trigger(CommandEvent(CancelCommand)); trigger(CommandEvent(TypeCommand "!v")); trigger(CommandEvent(EnterCommand))
      if e.altKey && e.key = "d" then e.preventDefault(); trigger(CommandEvent(CancelCommand)); trigger(CommandEvent(TypeCommand "!d")); trigger(CommandEvent(EnterCommand))


//trigger (MergeEdits(opsCore @ opsBudget))
//trigger (Evaluate true)
//trigger (Move 100000)
