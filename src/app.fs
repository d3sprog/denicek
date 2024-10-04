module Tbd.App.Main

open Tbd
open Tbd.Html
open Tbd.Doc
open Tbd.Demos

// --------------------------------------------------------------------------------------
// Application state
// --------------------------------------------------------------------------------------

// (1) Document and its history - state

type DocumentState = 
  { Initial : Node 
    Edits : EditList
    EditIndex : int 
    CurrentDocument : Node 
    FinalDocument : Node }

// (2) Edit history panel - state

type HistoryState = 
  { HighlightedSelector : Selectors option
    SelectedEdits : Set<int>
    Display : bool }

// (3) View and navigation - state

type LocationModifier = Before | After
type Cursor = int list * LocationModifier

type ViewState = 
  { CursorLocation : Cursor
    CursorSelector : Selectors
    ViewSourceSelector : Selectors option
    Markers : Selectors list
    GeneralizedMarkersSelector : Selectors option }

// (4) Command toolbox - state

type CommandRecommendationResult = 
  | EditRecommendation of EditList
  | NestedRecommendation of CommandRecommendation list
  | CompleteCommand of string
  
and CommandRecommendation = 
  { Icon : string
    Label : ApplicationState -> DomNode
    Parser : Parsec.Parser<CommandRecommendationResult> }

and CommandState =
  { AltMenuDisplay : bool
    Command : string 
    KnownRecommendations : CommandRecommendation list
    Recommendations : (CommandRecommendation * Parsec.Template) list
    SelectedRecommendation : int
    CopySource : Selectors option }

// All the states grouped together

and ApplicationState = 
  { ViewState : ViewState  
    CommandState : CommandState
    DocumentState : DocumentState
    HistoryState : HistoryState }

// --------------------------------------------------------------------------------------
// Application events
// --------------------------------------------------------------------------------------

// (1) Document and its history - events

type DocumentEvent = 
  | UndoLastEdit
  | Evaluate of all:bool
  | MergeEdits of EditList
  | SetEditIndex of int
  | MoveEditIndex of int 

// (2) Edit history panel - events

type HistoryEvent = 
  | HighlightSelector of Selectors option
  | ToggleEdit of int * bool
  | ExtendSelection of int (* -1 or +1 *)
  | SelectAll 
  | SelectNone
  | ToggleEditHistory

// (3) View and navigation - events

type CursorMove = 
  Backward | Forward | Previous | Next

type ViewEvent = 
  | MoveCursor of CursorMove
  | ToggleViewSource
  | AddMarker
  | ClearMarkers

// (4) Command toolbox - events

type CommandEvent = 
  | CancelCommand
  | BackspaceCommand
  | TypeCommand of string
  | PreviousRecommendation
  | NextRecommendation
  | SetRecommendation of int
  | CopyNode  
  | ToggleAltMenu of bool

// All the events grouped together
// (EnterCommand is here because entering a command affects global application 
// state in too complex ways - it updates document, view, history, etc.)

type ApplicationEvent =  
  | ViewEvent of ViewEvent
  | HistoryEvent of HistoryEvent
  | CommandEvent of CommandEvent
  | DocumentEvent of DocumentEvent
  | ResetState of ApplicationState
  | EnterCommand  

// --------------------------------------------------------------------------------------
// General purpose helpers
// --------------------------------------------------------------------------------------

let (+?) s1 (b, s2) = if b then (s1 + " " + s2) else s1

module Helpers = 

  let getSavedInteractions doc = 
    match select [Field "saved-interactions"] doc with 
    | [ Record("x-saved-interactions", saved) ] ->
      [ for k, nd in saved ->
          match nd with 
          | List("x-event-handler", ops) -> k, List.map unrepresent ops
          | _ -> failwith "getSavedInteractions: Expected x-event-handler" ]
    | _ -> []

  let formatSelector = 
    List.map (function All -> "*" | Tag t -> ":" + t | Index i -> string i | Field f -> f)
    >> List.map (fun s -> "/" + s)
    >> String.concat ""

  let renderSelector state trigger sel = 
    let selected = state.HistoryState.HighlightedSelector = Some sel
    h?a [ 
      "href" => "javascript:;"
      "class" => "selector" +? (selected, "selsel")
      "mouseover" =!> fun _ _ -> trigger(HistoryEvent(HighlightSelector(Some sel)))
      "mouseout" =!> fun _ _ -> trigger(HistoryEvent(HighlightSelector None))
    ] [ 
      text (formatSelector sel)
    ]

  let rec generalizeSelectors sels = 
    let allEmpty = List.forall List.isEmpty sels
    let allCons = List.forall (List.isEmpty >> not) sels
    if allEmpty then Some [] else
    if not allCons then None else
    let heads = List.map List.head sels
    let tails = List.map List.tail sels
    generalizeSelectors tails |> Option.bind (fun tail ->
      heads 
      |> List.tryReduce (fun s1 s2 ->
          match s1, s2 with 
          | _ when s1 = s2 -> Some s1
          | (Index _ | Tag _ | All), (Index _ | Tag _ | All) -> Some All
          | _ -> None)
      |> Option.map (fun head -> head :: tail))

  let replacePrefixInEdits prefix replacementSel edits = 
    edits |> List.map (fun op ->
      let newSels = getSelectors op |> List.map (fun sel -> 
        match removeSelectorPrefix prefix sel with 
        | Some (_, rest) -> replacementSel @ rest
        | None -> sel)
      withSelectors newSels op)
  
// --------------------------------------------------------------------------------------
// Document and its history 
// --------------------------------------------------------------------------------------

module Document =
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
  let marked state path = 
    state.ViewState.GeneralizedMarkersSelector |> Option.exists (fun gs -> matches gs path)
  let cursorBefore state path =
    matches state.ViewState.CursorSelector path && snd state.ViewState.CursorLocation = Before 
  let cursorAfter state path =
    matches state.ViewState.CursorSelector path && snd state.ViewState.CursorLocation = After
  let highlightedSel state path =
    match state.HistoryState.HighlightedSelector with Some s -> matches s path | _ -> false
  let (|Select|) doc sel = select sel doc

  /// Render document as source code tree (browser dev-tools style)
  let renderSourceTree state trigger =  
    let rec loop path idAttrs nd = 
      h?div [
        "class" => 
          "treenode" 
          +? (isPlainTextNode nd, "inline") 
          +? (highlightedSel state path, "selsel")
          +? (cursorBefore state path, "cursor cursor-before")
          +? (cursorAfter state path, "cursor cursor-after")
          +? (marked state path, "marked")
      ] [
        h?div ["class" => "treetag" ] [
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
        h?div ["class" => "treebody" ] [
          match nd with
          | List(_, nds) -> 
              for i, a in Seq.indexed nds do
                yield loop (path @ [Index i]) ["index", string i] a
          | Record(_, nds) -> 
              for f, a in nds do
                yield loop (path @ [Field f]) ["id", f] a
          | Reference(sel) -> yield Helpers.renderSelector state trigger sel
          | Primitive(String s) -> yield text s
          | Primitive(Number n) -> yield text (string n)              
        ]
        h?div ["class" => "treetag" ] [
          text "</"
          h?span [] [ text (getTag nd) ]
          text ">"
        ]
      ]
    loop

  /// Render node as document, potentially with embedded source code view somewhere
  let renderDocument state trigger =

    /// Event handlers specified as reference attributes and special "change" event for inputs
    let getEventHandlers nd tag path = [
      match nd with 
      | Record(_, nds) -> 
          for nd in nds do
            match nd with 
            | id, Reference(Select state.DocumentState.CurrentDocument 
                    [List("x-event-handler", edits)]) when id.StartsWith "@" ->
                yield id.Substring(1) =!> fun _ _ ->
                  let handler = { Groups = [[ for e in edits -> unrepresent e ]] }
                  trigger(DocumentEvent(Evaluate(true)))
                  trigger(DocumentEvent(MergeEdits(state.DocumentState.Edits.Append handler)))
                  trigger(DocumentEvent(Evaluate(true)))
                  trigger(DocumentEvent(MoveEditIndex(System.Int32.MaxValue)))
            | _ -> ()
      | _ -> ()
      if tag = "input" then 
        yield "change" =!> fun el _ ->
          let el = unbox<Browser.Types.HTMLInputElement> el
          let ed = 
            if el.``type`` = "checkbox" && el.``checked`` then
              RecordAdd(path, "@checked", ConstSource(Primitive(String "checked")))
            elif el.``type`` = "checkbox" && not el.``checked`` then
              Delete(path @ [Field "@checked"])
            else
              RecordAdd(path, "@value", ConstSource(Primitive(String el.value)))
          let edit = { Groups = [[ { Kind = ed } ]] }
          trigger(DocumentEvent(MergeEdits(state.DocumentState.Edits.Append edit)))
    ]

    /// Render source code or preview, depending on what's selected
    let rec loop path pid nd = 
      match state.ViewState.ViewSourceSelector with 
      | Some sel when matches path sel -> 
          h?div ["class" => "treedoc"] [ renderSourceTree state trigger path [] nd ]
      | _ -> 
          renderPreview path pid nd

    /// Render node in a what you see is what you get style
    and renderPreview path pid nd = 
      let tag = getTag nd

      let rcdattrs = 
        match nd with 
        | Record(_, nds) -> nds |> List.choose (function 
            | n, Primitive(String s) when n.StartsWith("@") -> Some(n.Substring(1) => s)
            | n, Primitive(Number m) when n.StartsWith("@") -> Some(n.Substring(1) => string m)
            | _ -> None)
        | _ -> []

      let attrs = [ 
        yield "id" => pid 
        yield "class" => 
          ""
          +? (highlightedSel state path, "selsel")
          +? (cursorBefore state path, "cursor cursor-before")
          +? (cursorAfter state path, "cursor cursor-after")
          +? (marked state path, "marked")
        yield! getEventHandlers nd tag path
        yield! rcdattrs ]

      h?(tag) attrs [
        match nd with 
        | Record("x-formula", nds) -> 
            let op = nds |> List.tryFind (fun (f,_) -> f = "op") |> Option.map snd
            let args = nds |> List.filter (fun (f,_)-> f <> "op")
            if op.IsSome then yield loop (path @ [Field "op"]) (pid ++ "op") op.Value
            else yield text "@"
            yield text "("
            for i, (f, a) in Seq.indexed args do
              if i <> 0 then yield text ", "
              yield text $"{f}="
              yield loop (path @ [Field f]) (pid ++ f) a
            yield text ")"
        | List(_, nds) -> 
            for i, a in Seq.indexed nds do
              yield loop (path @ [Index i]) (pid ++ string i) a
        | Record(_, nds) -> 
            for f, a in nds do
              if not (f.StartsWith("@")) then
                yield loop (path @ [Field f]) (pid ++ f) a
        | Reference(sel) -> yield Helpers.renderSelector state trigger sel
        | Primitive(String s) -> yield text s
        | Primitive(Number n) -> yield text (string n)        
      ]

    loop [] ""
    

  let update appstate state = function
    | UndoLastEdit ->
        let nedits = state.Edits.Truncate(state.Edits.Length - 1)
        { state with Edits = nedits; EditIndex = min state.EditIndex (nedits.Length - 1) }
    
    | Evaluate all -> 
        let edits = 
          if all then state.FinalDocument |> evaluateAll
          else state.FinalDocument |> evaluateDoc
        let nedits = state.Edits.Append edits
        { state with Edits = nedits; EditIndex = nedits.Length-1 }
  
    | MergeEdits edits ->
        let state = { state with Edits = mergeHistories state.Edits edits } 
        { state with EditIndex = state.Edits.Length-1 }
  
    | MoveEditIndex d ->
        { state with EditIndex = max 0 (min (state.Edits.Length - 1) (state.EditIndex + d)) }

    | SetEditIndex i ->
        { state with EditIndex = i }

// --------------------------------------------------------------------------------------
// Edit history panel
// --------------------------------------------------------------------------------------

module History = 
  let update appstate state = function
    | ExtendSelection(dir) ->
        let nsel = set [ appstate.DocumentState.EditIndex; appstate.DocumentState.EditIndex+dir ]
        let other = 
          Seq.initInfinite (fun i -> appstate.DocumentState.EditIndex-(i*dir)) 
          |> Seq.takeWhile (state.SelectedEdits.Contains)
          |> set
        { state with SelectedEdits = nsel + other  }

    | ToggleEditHistory -> 
        { state with Display = not state.Display }
    | ToggleEdit(i, true) ->
        { state with SelectedEdits = state.SelectedEdits.Add(i) }
    | ToggleEdit(i, false) ->
        { state with SelectedEdits = state.SelectedEdits.Remove(i) }
    | HighlightSelector sel ->
        { state with HighlightedSelector = sel }        
    | SelectNone ->
        { state with SelectedEdits = set [] }
    | SelectAll ->
        { state with SelectedEdits = set [ 0 .. appstate.DocumentState.Edits.Length - 1 ] }


  let rec formatNode state trigger (nd:Node) = 
    match nd with 
    | Primitive(Number n) -> text (string n)
    | Primitive(String s) -> text s
    | Reference(sel) -> Helpers.renderSelector state trigger sel
    | List(tag, nds) -> h?span [] [
          yield text "["
          for i, nd in Seq.indexed nds do 
            if i <> 0 then yield text ", "
            yield formatNode state trigger nd
          yield text "]"
        ]
    | Record(tag, nds) -> h?span [] [
          yield text (tag + "{")
          for i, (f, nd) in Seq.indexed nds do 
            if i <> 0 then yield text ", "
            yield text $"{f}="
            yield formatNode state trigger nd
          yield text "}"
        ]

  let formatSource state trigger = function
    | ConstSource nd -> formatNode state trigger nd
    | RefSource sel -> Helpers.renderSelector state trigger sel

  let renderEdit state trigger (i, ed) = 
    let render n fa sel args = 
      h?li [] [ 
        h?input [ 
          yield "type" => "checkbox"
          if state.HistoryState.SelectedEdits.Contains(i) then yield "checked" => "checked"
          yield "click" =!> fun el _ ->
            let chk = (unbox<Browser.Types.HTMLInputElement> el).``checked``
            trigger(HistoryEvent(ToggleEdit(i, chk)))
        ] []
        h?a [ 
          "class" => "" +? (i = state.DocumentState.EditIndex, "sel")
          "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(DocumentEvent(SetEditIndex i))
        ] [ 
          yield h?i [ "class" => "fa " + fa ] [] 
          yield text " "
          yield h?strong [] [ text n ]
          yield text " at "
          yield Helpers.renderSelector state trigger sel
          yield text " with ("
          for i, (k, v) in Seq.indexed args do
            if i <> 0 then yield text ", "
            yield text $"{k} = "
            yield v
          yield text ")"
        ]
      ]
    match ed.Kind with 
    | ListAppend(sel, nd) -> render "append" "fa-at" sel ["node", formatSource state trigger nd]
    | PrimitiveEdit(sel, fn) -> render "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
    | ListReorder(sel, perm) -> render "reorder" "fa-list-ol" sel ["perm", text (string perm)]
    | Copy(tgt, src) -> render "copy" "fa-copy" tgt ["from", formatSource state trigger src]
    | WrapRecord(id, tg, sel) -> render "wraprec" "fa-regular fa-square" sel ["id", text id; "tag", text tg]
    | WrapList(tg, sel) -> render "wraplist" "fa-solid fa-list-ul" sel ["tag", text tg]
    | RecordAdd(sel, f, nd) -> render "addfield" "fa-plus" sel ["node", formatSource state trigger nd; "fld", text f]
    | UpdateTag(sel, t1, t2) -> render "retag" "fa-code" sel ["t1", text t1; "t2", text t2]
    | RecordRenameField(sel, id) -> render "updid" "fa-font" sel ["id", text id]
    | Delete(sel) -> render "del" "fa-xmark" sel []
    | Check(sel, NonEmpty) -> render "check" "fa-circle-check" sel ["cond", text "nonempty"]
    | Check(sel, EqualsTo(Number n)) -> render "check" "fa-circle-check" sel ["=", text (string n)]
    | Check(sel, EqualsTo(String s)) -> render "check" "fa-circle-check" sel ["=", text s]

  let renderHistory trigger state = 
    if not state.HistoryState.Display then [] else [
      h?div [ "id" => "edits" ] [
        yield h?h3 [] [text "Demo buttons"]
        yield h?div [] [
          h?button ["click" =!> fun _ _ -> trigger(DocumentEvent(Evaluate(false))) ] [text "Eval step!"]
          h?button ["click" =!> fun _ _ -> trigger(DocumentEvent(Evaluate(true))) ] [text "Eval all!"]
          // TODO: This needs to move into demos (and does not belong here anyway)
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ opsBudget))) ] [text "Add budget"]
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ opsBudget @ addSpeakerOps))) ] [text "Add speaker"]
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ fixSpeakerNameOps))) ] [text "Fix name"]
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ refactorListOps))) ] [text "Refacor list"]
          //h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addTransformOps)) ] [text "Add transformers"]
        ]

        let saved = Helpers.getSavedInteractions state.DocumentState.CurrentDocument
        if not (List.isEmpty saved) then 
          yield h?h3 [] [text "Saved interactions"]
          yield h?ul [] [
            for k, ops in saved ->
              h?li [] [ 
                yield h?p [] [ text k ]
                yield h?ol [] [
                  for ied in Seq.rev (Seq.indexed ops) -> 
                    renderEdit state trigger ied
                ]
              ]
          ]
        
        yield h?h3 [] [text "Edit history" ]
        yield h?p [] [ 
          text "Use "
          h?kbd [] [ text "ctrl+shift+up"]
          text " / "
          h?kbd [] [ text "ctrl+shift+down"]
          text " to select a range of edits"
        ]
        yield h?p [] [
          text "Select edits "
          h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(HistoryEvent SelectNone) ] [ text "none" ]
          text " | "
          h?a [ "href" => "javascript:;"; "click" =!> fun _ _ -> trigger(HistoryEvent SelectAll) ] [ text "all" ]
        ]
        yield h?ol [] [              
          for ieds in List.revNested (List.indexedNested state.DocumentState.Edits.Groups) do
            for ied in ieds do
              yield renderEdit state trigger ied
            yield h?li [] [ h?hr [] [] ]
        ]
      ] 
    ]

// --------------------------------------------------------------------------------------
// Keyboard shortcuts
// --------------------------------------------------------------------------------------

type Shortcut = 
  { Key : string 
    IconCode : string
    Header : string 
    Events : ApplicationEvent list }

module Shortcuts =
  let shortcuts = [
    { Key = "d"
      Header = "Delete current document node"
      IconCode = "las la-trash"
      Events = [ CommandEvent(CancelCommand); CommandEvent(TypeCommand "!d"); EnterCommand ] }
    { Key = "c"
      Header = "Copy current document node"
      IconCode = "las la-copy"
      Events = [ CommandEvent(CopyNode) ] }
    { Key = "v"
      Header = "Paste current document node here"
      IconCode = "las la-paste"
      Events = [ CommandEvent(CancelCommand); CommandEvent(TypeCommand "!v"); EnterCommand ] }
    { Key = "m"
      Header = "Mark current node"
      IconCode = "las la-bookmark"
      Events = [ ViewEvent(AddMarker) ] }
    { Key = "n"
      Header = "Clear all marked nodes"
      IconCode = "las la-backspace"
      Events = [ ViewEvent(ClearMarkers) ] }
    { Key = "e"
      Header = "Evaluate all formulas"
      IconCode = "las la-play"
      Events = [ DocumentEvent(Evaluate(true)) ] }
    { Key = "z"
      Header = "Undo last edit"
      IconCode = "las la-undo-alt"
      Events = [ DocumentEvent(UndoLastEdit) ] }
    { Key = "u"
      Header = "Toggle source code view"
      IconCode = "las la-code"
      Events = [ ViewEvent(ToggleViewSource) ] }
    { Key = "h"
      Header = "Toggle edit history view"
      IconCode = "las la-history"
      Events = [ HistoryEvent(ToggleEditHistory) ] }
  ]

// --------------------------------------------------------------------------------------
// Command toolbox
// --------------------------------------------------------------------------------------

module Commands = 
  open Tbd.Parsec
  open Tbd.Parsec.Operators

  let isRecord = function Record _ -> true | _ -> false
  let isList = function List _ -> true | _ -> false
  let isString = function Primitive (String _) -> true | _ -> false
  let isNumber = function Primitive (Number _) -> true | _ -> false

  let (|NonEmpty|_|) (s:string) = 
    if System.String.IsNullOrEmpty(s) then None else Some s
  let (|StartsWith|_|) prefix (s:string) = 
    if s.StartsWith(prefix) then Some(s.Substring(prefix.Length)) else None

  let rec getFixedTemplatePrefix t = 
    match t with 
    | Fixed s -> Some s
    | Empty -> Some ""
    | Hole _ -> None
    | Repeat(t, _) -> getFixedTemplatePrefix t
    | Append ts -> 
        let prefix = 
          List.map getFixedTemplatePrefix ts 
          |> List.takeWhile Option.isSome
          |> List.choose id
        if List.isEmpty prefix then None
        else Some (String.concat "" prefix)

  let rec formatTemplate t = 
    match t with 
    | Fixed s -> h?strong [] [ text s ]
    | Append ts -> h?span [] [ for t in ts -> formatTemplate t ]
    | Hole s -> h?em [] [ text s ]
    | Empty -> text ""
    | Repeat(t, r) -> h?span [] [ text "("; formatTemplate t; text (")" + r) ]

  let command i l p = { Icon = i; Label = (fun _ -> text l); Parser = p }
  let commandh i l p = { Icon = i; Label = (fun s -> h?span [] (l s)); Parser = p }

  let tagHole = P.hole "tag" P.ident
  let fieldHole = P.hole "field" (P.ident <|> P.atIdent)
  let numHole = P.hole "num" P.num
  let strHole = P.hole "str" P.str

  let recordTag = P.char '<' <*>> tagHole <<*> P.char '>'
  let listTag = P.char '[' <*>> fieldHole <<*> P.char ']'
  let fieldAssignment = P.char ':' <*>> fieldHole <<*> P.char '='
  let anonAssignment = P.char ':'
  let mapEd f = P.map (fun x -> EditRecommendation { Groups = [[{ Kind = f x }]] })
  let mapEds f = P.map (fun x -> EditRecommendation { Groups = f x })
  let mapEdg f = P.map (fun x -> EditRecommendation { Groups = [[ for k in f x -> { Kind = k } ]] })

  // TODO: Missing stuff with references
  // e.g. https://github.com/tpetricek/conf/blob/85ba506a56e299a6e2d8e63b8f5a13c687b1610e/src/app.fs#L372

  let getCommands state trigger = [
    let doc = state.DocumentState.CurrentDocument 
    let cursorSel = state.ViewState.CursorSelector
    let nd, trace = trace cursorSel doc |> Seq.head

    // Wrapping curent element in some ways
    yield command "las la-id-card" "Wrap element as a record field"
      ( P.char '<' <*>> tagHole <<*> P.char ' ' <*> fieldHole <<*> P.char '>' |> mapEd (fun (tag, fld) -> 
        WrapRecord(fld, tag, cursorSel) )) 
    yield command "las la-id-card" "Wrap element as an anonymous record field"
      ( P.char '<' <*>> tagHole <<*> P.char '>' |> mapEd (fun (tag) -> 
        WrapRecord(ffld "", tag, cursorSel) )) 
    yield command "las la-list" "Wrap element as a list item"
      ( P.char '[' <*>> tagHole <<*> P.char ']' |> mapEd (fun (tag) -> 
        WrapList(tag, cursorSel) )) 

    // Copy, paste, rename & save edits actions
    yield command "las la-trash" "Delete node at current location"
      ( P.keyword "!d" |> mapEd (fun (_) -> 
        Delete(cursorSel) ))
    match state.CommandState.CopySource with 
    | None -> ()
    | Some src ->
        yield command "las la-paste" "Paste copied node at current location"
          ( P.keyword "!v" |> mapEd (fun (_) -> 
            Copy(cursorSel, RefSource src) ))
    if not (List.isEmpty trace) && isRecord (fst (List.last trace)) then
        yield command "las la-i-cursor" "Rename field containing the current element"
          ( P.keyword "!r " <*>> fieldHole |> mapEd (fun (fld) ->
            RecordRenameField(cursorSel, fld) ))
    if not (state.HistoryState.SelectedEdits.IsEmpty) then 
        let recordedEds = 
          [ for i in Seq.sort state.HistoryState.SelectedEdits ->
              state.DocumentState.Edits.[i] ]
        yield command "las la-save" "Save selected edits in the document"
          ( P.keyword "!s " <*>> (P.hole "field" P.ident) |> mapEdg (fun (fld) ->
            [ if select [Field "saved-interactions"] doc = [] then
                yield RecordAdd([], "saved-interactions", ConstSource(Record("x-saved-interactions", [])))
              yield RecordAdd([Field "saved-interactions"], fld, ConstSource(List("x-event-handler", [])))
              for op in recordedEds ->
                ListAppend([Field "saved-interactions"; Field fld], ConstSource(represent op)) ] ))

    // Add field of some kind to a record
    if isRecord nd then 
      match state.CommandState.CopySource with
      | None -> ()
      | Some src ->
          yield command "las la-paste" "Add copied node to current record"
            ( fieldAssignment <<*> P.keyword "!v" |> mapEd (fun (fld) ->
              RecordAdd(cursorSel, ffld fld, RefSource(src)) ))
      yield command "las la-id-card" "Add record field to current record"
        ( fieldAssignment <*> recordTag |> mapEd (fun (fld, tag) ->
          RecordAdd(cursorSel, ffld fld, ConstSource(Record(tag, []))) ))
      yield command "las la-list" "Add list field to current record"
        ( fieldAssignment <*> listTag |> mapEd (fun (fld, tag) ->
          RecordAdd(cursorSel, ffld fld, ConstSource(List(tag, []))) ))
      yield command "las la-hashtag" "Add numerical field to current record"
        ( fieldAssignment <*> numHole |> mapEd (fun (fld, num) ->
          RecordAdd(cursorSel, ffld fld, ConstSource(Primitive(Number (int num)))) ))
      yield command "las la-font" "Add string field to current record"
        ( fieldAssignment <*> strHole |> mapEd (fun (fld, str) ->
          RecordAdd(cursorSel, ffld fld, ConstSource(Primitive(String str))) ))

    // Add item of some kind to a list
    if isList nd then 
      match state.CommandState.CopySource with
      | None -> ()
      | Some src ->
          yield command "las la-paste" "Add copied node to current list"
            ( anonAssignment <*>> P.keyword "!v" |> mapEd (fun _ ->
              ListAppend(cursorSel, RefSource(src)) ))
      yield command "las la-id-card" "Add record item to current list"
        ( anonAssignment <*>> recordTag |> mapEd (fun (tag) ->
          ListAppend(cursorSel, ConstSource(Record(tag, []))) ))
      yield command "las la-list" "Add list item to current list"
        ( anonAssignment <*>> listTag |> mapEd (fun (tag) ->
          ListAppend(cursorSel, ConstSource(List(tag, []))) ))
      yield command "las la-hashtag" "Add numerical item to current list"
        ( anonAssignment <*>> numHole |> mapEd (fun (num) ->
          ListAppend(cursorSel, ConstSource(Primitive(Number (int num)))) ))
      yield command "las la-font" "Add string item to current list"
        ( anonAssignment <*>> strHole |> mapEd (fun (str) ->
          ListAppend(cursorSel, ConstSource(Primitive(String str))) ))
    
    // Checks that current node has value / is non-empty
    match nd with 
    | Primitive(p) ->
        yield command "las la-spell-check" "Check node has the current value"
          ( P.keyword "*eq" |> mapEd (fun (str) ->
            Check(cursorSel, EqualsTo p) ))
    | _ -> ()
    match nd with 
    | Primitive(String(NonEmpty _) | Number _) ->
        yield command "las la-check-square" "Check node value is not empty"
          ( P.keyword "*ne" |> mapEd (fun (str) ->
            Check(cursorSel, NonEmpty) ))
    | _ -> ()

    // Built-in transformations of primitive values
    if isString nd || isNumber nd then
      for t in transformations do
        yield command "las la-at" (t.Label + " (built-in)")
          ( P.char '@' <*> P.keyword t.Key |> mapEd (fun _ ->
            PrimitiveEdit(cursorSel, t.Key) ))

    // Saved interactions - generate nested completions
    // (one for applying to cursor, one for applying to all marked)
    for t, ops in Helpers.getSavedInteractions doc do
      yield command "las la-at" ("Apply " + t + " to current (user)")
        ( P.keyword $"@{t}" |> P.map (fun _ -> 
            NestedRecommendation [
              for i, prefix in Seq.indexed (getTargetSelectorPrefixes ops) do 
                yield commandh "las la-at" (fun state -> [text "Using current as "; Helpers.renderSelector state trigger prefix])
                  ( P.keyword $"@{t} {string i}" |> mapEds (fun _ ->
                    [ Helpers.replacePrefixInEdits prefix cursorSel ops ] )) ]
        ))
      match state.ViewState.GeneralizedMarkersSelector with 
      | None -> ()
      | Some markerSel ->
          yield command "las la-at" ("Apply " + t + " to marked (user)")
            ( P.keyword $"@{t}*" |> P.map (fun _ -> 
                NestedRecommendation [
                  for i, prefix in Seq.indexed (getTargetSelectorPrefixes ops) do 
                    yield command "las la-at" ("Using current as " + Helpers.formatSelector prefix)
                      ( P.keyword $"@{t}* {string i}" |> mapEds (fun _ ->
                        [ for markerSel in expandWildcards markerSel doc ->
                            Helpers.replacePrefixInEdits prefix markerSel ops ] )) ]
            ))
  ]

  let parseCommand state = 
    let cmdState = state.CommandState
    let recm = cmdState.KnownRecommendations |> List.tryPick (fun cmd -> 
        match P.run cmd.Parser cmdState.Command with 
        | Parsed(ed, []) -> Some(ed)
        | _ -> None )
    match recm with 
    | None -> 
        let cmd, _ = cmdState.Recommendations.[cmdState.SelectedRecommendation]
        CompleteCommand(defaultArg (getFixedTemplatePrefix (P.getTemplate cmd.Parser)) "")
    | Some(r) -> r
    
  let scrollIntoView = function
    | Element(ns, tag, attr, c, _) -> 
        Element(ns, tag, attr, c, Some(fun el -> el.scrollIntoView(false)))
    | dom -> dom

  let renderCommand trigger state i entered c t = 
    let selected = i = state.CommandState.SelectedRecommendation          
    let el = 
      h?li [ 
        "class" => "" +? (selected, "selected") 
        "mouseover" =!> fun _ _ -> trigger(CommandEvent(SetRecommendation i))
        "click" =!> fun _ _ -> trigger(EnterCommand)
      ] [
        h?div [ "class" => "icon" ] [ h?i [ "class" => c.Icon ] [] ]
        h?div [ "class" => "details" ] [
          h?h4 [] [ c.Label state ]
          h?kbd [ ] [ 
            h?span ["class" => "entered"] [ text entered ]
            formatTemplate t ]
          ]
      ] 
    if selected then scrollIntoView el else el

  let renderCommandHelp trigger state = 
    let cmd = state.CommandState.Command
    h?div [ ] [
      h?div [ "id" => "cmd" ] [ text cmd ]
      h?ul [] [ 
        for i, (c, t) in Seq.indexed (state.CommandState.Recommendations) ->
          if cmd.StartsWith("?") then renderCommand trigger state i "" c t
          else renderCommand trigger state i cmd c t 
      ] 
    ]

  let renderAltHelp trigger = 
    h?div [ ] [
      h?ul [] [ 
        for sc in Shortcuts.shortcuts ->
          h?li [ 
            "click" =!> fun _ _ -> for evt in sc.Events do trigger(evt)
          ] [
            h?div [ "class" => "icon" ] [ h?i [ "class" => sc.IconCode ] [] ]
            h?div [ "class" => "details" ] [
              h?h4 [] [ text $"Alt + {sc.Key.ToUpper()}" ]
              h?kbd [] [ text sc.Header ]
            ]
          ] 
        ] 
    ]

  let renderContext state trigger =
    if state.CommandState.Command = "" && not state.CommandState.AltMenuDisplay then [] else
    let cur = Browser.Dom.document.getElementsByClassName("cursor")
    if cur.length = 0 then [] else
    let cursorRect = cur.[0].getBoundingClientRect()
    let left, top = cursorRect.left, cursorRect.bottom+20.0  
    let altMenu = state.CommandState.AltMenuDisplay
    [ h?div [ "id" => "ctx"; "class" => "" +? (altMenu, "altmenu"); "style" => $"left:{left}px;top:{top}px" ] [ 
        h?div [ "id" => "ctx-body" ] [ 
          if altMenu then renderAltHelp trigger
          else renderCommandHelp trigger state 
        ] 
    ] ]

  let updateRecommendations reset appstate trigger state = 
    let state = 
      if reset then 
        let cmds = getCommands appstate trigger
        { state with KnownRecommendations = cmds }
      else state
    match state.Command with
    | "" -> 
        { state with SelectedRecommendation = -1; Recommendations = [] }
    | StartsWith "?" query ->
        let query = query.ToLower()
        let recs = state.KnownRecommendations |> List.choose (fun c -> 
          if (innerText (c.Label appstate)).ToLower().Contains(query) then 
            Some(c, P.getTemplate c.Parser)
          else None )  
        { state with SelectedRecommendation = 0; Recommendations = recs }
    | cmd ->
        let recs = state.KnownRecommendations |> List.choose (fun c -> 
          match P.run c.Parser cmd with 
          | Parsed(_, []) -> Some(c, Empty)
          | Partial t -> Some(c, t)
          | _ -> None )
        { state with SelectedRecommendation = 0; Recommendations = recs }

  let chooseRecommendation state =
    let rcm, tmpl = state.Recommendations.[state.SelectedRecommendation]
    let cmd = getFixedTemplatePrefix tmpl |> Option.get
    let tmpl = match P.run rcm.Parser cmd with Partial t -> t | _ -> Empty
    { state with 
        SelectedRecommendation = 0; Recommendations = [ rcm, tmpl ]; 
          KnownRecommendations = [ rcm ]; Command = cmd }
    
  let update appstate trigger state = function
    | ToggleAltMenu alt ->
        { state with AltMenuDisplay = alt }
    | CancelCommand -> 
        { state with Command = "" }
    | BackspaceCommand -> 
        ( if state.Command.Length <= 1 then { state with Command = "" }
          else { state with Command = state.Command.[0 .. state.Command.Length-2] } )
        |> updateRecommendations false appstate trigger
    | TypeCommand c -> 
        { state with Command = state.Command + c } 
        |> updateRecommendations (state.Command = "") appstate trigger
    | NextRecommendation ->
        let idx = (state.SelectedRecommendation + 1) % state.Recommendations.Length
        { state with SelectedRecommendation = idx }
    | PreviousRecommendation ->
        let idx = (state.SelectedRecommendation - 1 + state.Recommendations.Length) % state.Recommendations.Length
        { state with SelectedRecommendation = idx }
    | SetRecommendation idx -> 
        { state with SelectedRecommendation = idx }    
    | CopyNode ->
        { state with CopySource = Some appstate.ViewState.CursorSelector } 
    
// --------------------------------------------------------------------------------------
// View and navigation
// --------------------------------------------------------------------------------------

module View = 
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

  let fixCursor doc state = 
    let locs = locations doc |> dict
    let rec loop ((curi, curm) as cur) =
      if locs.ContainsKey(cur) then cur, locs.[cur]
      else loop (curi.[0 .. curi.Length - 2], curm)
    let cursorLoc, cursorSel = loop state.CursorLocation
    { state with CursorSelector = cursorSel; CursorLocation = cursorLoc }

  let renderLocationInfo state = [
    let traces = trace state.ViewState.CursorSelector state.DocumentState.CurrentDocument |> List.ofSeq
    match traces with 
    | []-> yield h?span [] [ text "(invalid location)" ]
    | (nd, trc)::_ ->
      for nd, s in trc do
        yield h?span [] [
          match nd with 
          | Record(t, _) | List(t, _) -> yield h?strong [] [ text t ]
          | _ -> ()
          match s with 
          | Index i -> yield text $"[{i}]"
          | Tag t -> yield text $"[#{t}]"
          | All -> yield text $"[*]"
          | Field f when f.[0] = '=' -> yield text ""
          | Field f -> yield text ("." + f)
        ]
        yield h?i [ "class" => "la la-long-arrow-alt-right" ] []
      yield h?span [] [ 
        let pf = if snd state.ViewState.CursorLocation = After then "(after)" else "(before)" 
        match nd with 
        | Record(t, _) -> text $"{pf} record {t}"
        | List(t, _) -> text $"{pf} list {t}"
        | Primitive(String s) -> text $"{pf} string '{s}'"
        | Primitive(Number n) -> text $"{pf} number '{n}'"
        | Reference r -> text $"{pf} reference '{r}'"
      ]
    ]

  let rec update appstate state = function
    | AddMarker ->
        let marks = state.CursorSelector :: state.Markers
        let gen = Helpers.generalizeSelectors marks
        { state with Markers = marks; GeneralizedMarkersSelector = gen }
    | ClearMarkers ->
        { state with Markers = []; GeneralizedMarkersSelector = None }

    | ToggleViewSource ->
        match state.ViewSourceSelector with 
        | None -> { state with ViewSourceSelector = Some state.CursorSelector }
        | Some _ -> { state with ViewSourceSelector = None }
  
    | MoveCursor dir ->      
        let ncur, nsel = moveCursor appstate.DocumentState.CurrentDocument state.CursorLocation dir
        let state = { state with CursorLocation = ncur; CursorSelector = nsel }
        // Make sure the cursor is pointing to a visible thing
        let _, tr = trace nsel appstate.DocumentState.CurrentDocument |> Seq.exactlyOne
        match state.ViewSourceSelector with 
        | Some srcSel when includes srcSel nsel -> 
            // The current location is inside view source region
            state 
        | _ ->
            // If it is pointing to a hidden thing, move further
            let hidden = tr |> List.exists (function 
              | _, Field(s) when s.StartsWith("@") -> true
              | _, Field("saved-interactions") -> true
              | Record("input", _), _ -> true
              | Record("button", _), _ -> true
              | _ -> false)
            if hidden then update appstate state (MoveCursor dir)
            else state
  
// --------------------------------------------------------------------------------------
// Application - global event handling and rendering
// --------------------------------------------------------------------------------------

let updateDocument docState = 
  { docState with 
      CurrentDocument = 
        docState.Edits.[0 .. docState.EditIndex] |> applyHistory docState.Initial  
      FinalDocument = 
        docState.Edits |> applyHistory docState.Initial }


let rec tryEnterCommand trigger state = 
  match Commands.parseCommand state with
  | EditRecommendation(eds) -> 
      let doc = 
        { state.DocumentState with 
            EditIndex = state.DocumentState.Edits.Length + eds.Length - 1;
            Edits = state.DocumentState.Edits.Append eds }
      let viewState = View.fixCursor state.DocumentState.CurrentDocument state.ViewState
      { state with 
          ViewState = viewState
          DocumentState = doc |> updateDocument
          CommandState = { state.CommandState with Command = "" } } 
  | NestedRecommendation(opts) ->
      let cmdState = 
        { state.CommandState with KnownRecommendations = opts }
        |> Commands.updateRecommendations false state trigger
      { state with CommandState = cmdState } 
  | CompleteCommand prefix -> 
      if prefix.StartsWith(state.CommandState.Command) && prefix.Length > state.CommandState.Command.Length then 
        let complete = prefix.Substring(state.CommandState.Command.Length)
        { state with CommandState = Commands.update state trigger state.CommandState (TypeCommand complete) }
        |> tryEnterCommand trigger
      else state


let rec update state trigger e = 
  match e with 
  | ResetState s -> s
  | ViewEvent e -> { state with ViewState = View.update state state.ViewState e }
  | CommandEvent e -> { state with CommandState = Commands.update state trigger state.CommandState e }
  | HistoryEvent e -> { state with HistoryState = History.update state state.HistoryState e }

  | DocumentEvent e ->
      // Undo operation can break cursor location, so we fix it here
      // (this is a bit ugly, but it cannot be done in Doc.update)
      let docState = Document.update state state.DocumentState e |> updateDocument
      let viewState = View.fixCursor docState.CurrentDocument state.ViewState
      { state with DocumentState = docState; ViewState = viewState }

  | EnterCommand when state.CommandState.Command.StartsWith("?") ->
      { state with CommandState = Commands.chooseRecommendation state.CommandState } 
      |> tryEnterCommand trigger
  | EnterCommand -> 
      state |> tryEnterCommand trigger


let render demos trigger state = 
  h?div [] [
    h?header [] [ 
      yield h?strong [] [ text "Demo: "]
      for d, s in demos -> h?a [ "href" => "#"; "click" =!> fun _ _ -> trigger(ResetState s) ] [ text d ] 
    ]
    h?div [ "id" => "loc" ] (View.renderLocationInfo state)    
    h?div [ "id" => "main" ] [
      yield h?div [ "id" => "doc" ] [
        let doc = state.DocumentState.CurrentDocument // TODO: Restore... Matcher.applyMatchers state.CurrentDocument 
        yield Document.renderDocument state trigger doc
      ]
      yield! Commands.renderContext state trigger
      yield! History.renderHistory trigger state
    ]
    h?script [ "type" => "application/json"; "id" => "serialized" ] [
      let nodes = List.map (List.map represent) state.DocumentState.Edits.Groups
      text (Serializer.nodesToJsonString nodes)
    ]
  ]


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
//let ops = opsBaseCounter
//let ops = opsBaseCounter @ opsCounterInc @ opsCounterHndl

let hello = """[[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","greetings"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"ul","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings",0]}],["field","greeting"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","HeLlO woRlD!"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings",1]}],["field","greeting"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","ahOJ sVeTE!"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings",2]}],["field","greeting"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","HAlLo WElT!"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["greetings",3]}],["field","greeting"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","saLUt Le MonDE!"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","temp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"p","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp"]}],["field","value"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","hElLo wORLd!"]]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","first"],["id","span"],["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value"]}],["field","rest"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["temp","value","first"]}]]}]]},{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","first"]}],["op","take-first"]]},{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","first"]}],["op","upper"]]},{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","rest"]}],["op","skip-first"]]},{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","rest"]}],["op","lower"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","saved-interactions"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-saved-interactions","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions"]}],["field","normalize"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"x-event-handler","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","normalize"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","first"],["id","span"],["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value"]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","normalize"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value"]}],["field","rest"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["temp","value","first"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","normalize"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","first"]}],["op","take-first"]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","normalize"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","first"]}],["op","upper"]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","normalize"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","rest"]}],["op","skip-first"]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","normalize"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-primitive-edit","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp","value","rest"]}],["op","lower"]]}]]}]]}]]"""
let todo = """[[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","=vXYI2bHIj0yhbcNIbNuHfw=="],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Todo list demo"]]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","=i6AeAzX8J0OnGsLAlCn35w=="],["id","h1"],["target",{"kind":"list","tag":"x-selectors","nodes":["=vXYI2bHIj0yhbcNIbNuHfw=="]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","items"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"ul","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-updateid","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["id","inp"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"button","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","=8zRye0YNiEqYYqO6GWzDvg=="],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Add"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp"]}],["field","@value"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Do some work"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","saved-interactions"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-saved-interactions","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions"]}],["field","add-handler"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"x-event-handler","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","@click"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"reference","selectors":["saved-interactions","add-handler"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-check","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}],["cond",{"kind":"record","tag":"x-cond-nonempty","nodes":[]}]]}]]}]]}]]"""
let todo2 = """[[{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","=vXYI2bHIj0yhbcNIbNuHfw=="],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Todo list demo"]]}]]},{"kind":"record","tag":"x-edit-wraprec","nodes":[["tag","=i6AeAzX8J0OnGsLAlCn35w=="],["id","h1"],["target",{"kind":"list","tag":"x-selectors","nodes":["=vXYI2bHIj0yhbcNIbNuHfw=="]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","items"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"ul","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-updateid","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["id","inp"]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","add"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"button","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","=8zRye0YNiEqYYqO6GWzDvg=="],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Add"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp"]}],["field","@value"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","Do some work"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","saved-interactions"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-saved-interactions","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions"]}],["field","add-handler"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"x-event-handler","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["add"]}],["field","@click"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"reference","selectors":["saved-interactions","add-handler"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","add-handler"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-check","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}],["cond",{"kind":"record","tag":"x-cond-nonempty","nodes":[]}]]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]},{"kind":"record","tag":"x-check","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}],["cond",{"kind":"record","tag":"x-cond-nonempty","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","tmp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"li","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","done"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"input","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp","done"]}],["field","@type"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checkbox"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}],["field","label"],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["tmp"]}]]},{"kind":"record","tag":"x-check","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["inp","@value"]}],["cond",{"kind":"record","tag":"x-cond-nonempty","nodes":[]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["items",1,"done"]}],["field","@checked"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const","checked"]]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":[]}],["field","temp"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"ul","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp"]}],["src",{"kind":"record","tag":"x-src-ref","nodes":[["selector",{"kind":"list","tag":"x-selectors","nodes":["items",1]}]]}]]},{"kind":"record","tag":"x-check","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp",0,"done","@checked"]}],["cond",{"kind":"record","tag":"x-cond-equals","nodes":[["node","checked"]]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp",0]}]]},{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp"]}]]},{"kind":"record","tag":"x-edit-add","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions"]}],["field","remove-completed"],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"list","tag":"x-event-handler","nodes":[]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","remove-completed"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-check","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp",0,"done","@checked"]}],["cond",{"kind":"record","tag":"x-cond-equals","nodes":[["node","checked"]]}]]}]]}]]},{"kind":"record","tag":"x-edit-append","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["saved-interactions","remove-completed"]}],["src",{"kind":"record","tag":"x-src-node","nodes":[["const",{"kind":"record","tag":"x-edit-delete","nodes":[["target",{"kind":"list","tag":"x-selectors","nodes":["temp",0]}]]}]]}]]}]]"""

let readJson json = 
  let ops = { Groups = List.map (List.map unrepresent) (Serializer.nodesFromJsonString json) }
  let init = rcd "div"
  { DocumentState = { Initial = init; Edits = ops; EditIndex = ops.Length - 1; CurrentDocument = applyHistory init ops; FinalDocument = applyHistory init ops }
    ViewState = { CursorLocation = [], Before; CursorSelector = []; Markers = []; GeneralizedMarkersSelector = None; ViewSourceSelector = None }
    CommandState = { AltMenuDisplay = false; Command = ""; CopySource = None; SelectedRecommendation = -1; KnownRecommendations = []; Recommendations = [] }
    HistoryState = { HighlightedSelector = None; SelectedEdits = Set.empty; Display = false }
  }

let demos = 
  [ "hello", readJson hello
    "empty", readJson "[]"
    "todo", readJson todo
    "todo2", readJson todo2 ]

let _, state = List.head demos

let trigger, _, getState = createVirtualDomApp "out" state (render demos) update

Browser.Dom.window.onkeypress <- fun e -> 
  if (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" then
    e.preventDefault();
    trigger(CommandEvent(TypeCommand e.key))

Browser.Dom.window.onkeyup <- fun e -> 
  let state = getState()
  if e.key = "Alt" && state.CommandState.AltMenuDisplay then
    e.preventDefault(); trigger(CommandEvent(ToggleAltMenu false))

Browser.Dom.window.onkeydown <- fun e -> 
  let state = getState()
  if (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" then
    if e.ctrlKey then
      if e.key = "ArrowUp" && e.shiftKey then e.preventDefault(); trigger(HistoryEvent(ExtendSelection +1))
      if e.key = "ArrowDown" && e.shiftKey then e.preventDefault(); trigger(HistoryEvent(ExtendSelection -1))
      if e.key = "ArrowUp" then e.preventDefault(); trigger(DocumentEvent(MoveEditIndex +1))
      if e.key = "ArrowDown" then e.preventDefault(); trigger(DocumentEvent(MoveEditIndex -1))
    else
      if e.key = "Escape" then e.preventDefault(); trigger(CommandEvent(CancelCommand))
      if e.key = "Backspace" then e.preventDefault(); trigger(CommandEvent(BackspaceCommand))
      if e.key = "Enter" then e.preventDefault(); trigger(EnterCommand)
      if e.key = "ArrowRight" then e.preventDefault(); trigger(ViewEvent(MoveCursor Forward))
      if e.key = "ArrowLeft" then e.preventDefault(); trigger(ViewEvent(MoveCursor Backward))
      if e.key = "ArrowUp" then 
        if state.CommandState.Command = "" then e.preventDefault(); trigger(ViewEvent(MoveCursor Previous))
        else e.preventDefault(); trigger(CommandEvent(PreviousRecommendation))
      if e.key = "ArrowDown" then 
        if state.CommandState.Command = "" then e.preventDefault(); trigger(ViewEvent(MoveCursor Next))
        else e.preventDefault(); trigger(CommandEvent(NextRecommendation))

      if e.key = "Alt" && not state.CommandState.AltMenuDisplay then
        e.preventDefault(); trigger(CommandEvent(ToggleAltMenu true))

      for sc in Shortcuts.shortcuts do
        if e.altKey && e.key = sc.Key then 
          e.preventDefault()
          for evt in sc.Events do trigger(evt)