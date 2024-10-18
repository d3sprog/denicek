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
    FinalHash : int
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
    GeneralizedStructuralSelector : Selectors }

// (4) Command toolbox - state

type CommandRecommendationResult = 
  | EditRecommendation of Edit list list
  | NestedRecommendation of CommandRecommendation list
  | CompleteCommand of string
  
and CommandRecommendation = 
  { Icon : string
    Label : ApplicationState -> DomNode
    EditKind : SharedEditKind
    Parser : Parsec.Parser<CommandRecommendationResult> }

and CommandState =
  { AltMenuDisplay : bool
    Command : string 
    KnownRecommendations : CommandRecommendation list
    Recommendations : (CommandRecommendation * Parsec.Template) list
    SelectedRecommendation : int
    CopySource : Selectors option }

// (5) Demos - state

and DemoState = 
  { Demos : option<list<string * ApplicationState * list<string * EditList>>> }

// All the states grouped together

and ApplicationState = 
  { ViewState : ViewState  
    CommandState : CommandState
    DocumentState : DocumentState
    HistoryState : HistoryState 
    DemoState : DemoState }

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

// (4) Command toolbox - events
type CopySource = CurrentNode | MarkedNode

type CommandEvent = 
  | CancelCommand
  | BackspaceCommand
  | TypeCommand of string
  | PreviousRecommendation
  | NextRecommendation
  | SetRecommendation of int
  | CopyNode of CopySource  
  | ToggleAltMenu of bool

// (5) Demos - events

type DemoEvent = 
  | LoadDemos of list<string * ApplicationState * list<string * EditList>>

// All the events grouped together
// (EnterCommand is here because entering a command affects global application 
// state in too complex ways - it updates document, view, history, etc.)

type ApplicationEvent =  
  | ViewEvent of ViewEvent
  | HistoryEvent of HistoryEvent
  | CommandEvent of CommandEvent
  | DocumentEvent of DocumentEvent
  | ResetState of ApplicationState
  | DemoEvent of DemoEvent
  | EnterCommand  

// --------------------------------------------------------------------------------------
// General purpose helpers
// --------------------------------------------------------------------------------------

let (+?) s1 (b, s2) = if b then (s1 + " " + s2) else s1

module Helpers = 

  let (|InteractionNode|_|) = function
    | Record("x-interaction", 
        Patterns.ListFind "interactions" (List("x-interaction-list", ops)) & 
        Patterns.ListFind "historyhash" (Primitive(Number hash)) ) ->
        Some(Some (int hash), List.map unrepresent ops)
    | _ -> None

  let getSavedInteractions doc = 
    match select [Field "saved-interactions"] doc with 
    | [ Record("x-saved-interactions", saved) ] ->
        saved |> List.map (function 
          | k, InteractionNode(hist, ops) -> k, hist, ops
          | _ -> failwith "getSavedInteractions: Expected x-interaction" )
    | _ -> []

  let renderHistoryHash state trigger hist =
    h?a [
      "href" => "javascript:;"
      "click" =!> fun _ _ -> 
          match state.DocumentState.Edits.EditsByHash(hist) with 
          | Some eds -> trigger(DocumentEvent(SetEditIndex(eds.Length - 1)))
          | _ -> ()
    ] [
      text (string hist)
    ]

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

  let generalizeToStructuralSelector sels = 
    sels |> List.map (function Index _ | Tag _ -> All | s -> s)

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
  let generalizedSel state path = 
    matches state.ViewState.GeneralizedStructuralSelector path
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
          +? (generalizedSel state path, "gensel")
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
                    [Helpers.InteractionNode(histhash, ops) ]) when id.StartsWith "@" ->
                yield id.Substring(1) =!> fun _ e ->
                  e.preventDefault()
                  // Add saved edits to the original document state and merge them with 
                  // current state so that they can be updated to match new document schema
                  let handler = { Groups = [ops] }
                  // TODO: trigger(DocumentEvent(Evaluate(true)))
                  let baseeds = 
                    histhash 
                    |> Option.bind state.DocumentState.Edits.EditsByHash
                    |> Option.defaultValue state.DocumentState.Edits
                  trigger(DocumentEvent(MergeEdits(baseeds.Append handler)))
                  // TODO: trigger(DocumentEvent(Evaluate(true)))
                  // trigger(DocumentEvent(MoveEditIndex(System.Int32.MaxValue)))
            | _ -> ()
      | _ -> ()
      if tag = "input" then 
        yield "change" =!> fun el _ ->
          let el = unbox<Browser.Types.HTMLInputElement> el
          let ed = 
            if el.``type`` = "checkbox" && el.``checked`` then
              Value(RecordAdd(path, "@checked", Primitive(String "checked")))
            elif el.``type`` = "checkbox" && not el.``checked`` then
              Shared(ValueKind, RecordDelete(path, "@checked"))
            else
              Value(RecordAdd(path, "@value", Primitive(String el.value)))
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
          +? (generalizedSel state path, "gensel")
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
          if all then state.FinalDocument |> Eval.evaluateAll
          else state.FinalDocument |> Eval.evaluateDoc
        let nedits = state.Edits.Append edits // TODO: use mergeedits here?
        { state with Edits = nedits; EditIndex = nedits.Length-1 }
  
    | MergeEdits edits ->
        let edits = filterDisabledGroups state.Initial edits
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

  let renderEdit state trigger (i, ed) = 
    let render sk n fa sel args = 
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
          yield h?strong [] [ text (if sk = ValueKind then "v." + n else "s." + n) ]
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
    let renderv = render ValueKind
    match ed.Kind with 
    | Value(ListAppend(sel, nd)) -> renderv "append" "fa-at" sel ["node", formatNode state trigger nd]
    | Value(ListAppendFrom(sel, src)) -> renderv "appfrom" "fa-paperclip" sel ["node", Helpers.renderSelector state trigger src]
    | Value(PrimitiveEdit(sel, fn)) -> renderv "edit" "fa-solid fa-i-cursor" sel ["fn", text fn]
    | Value(RecordAdd(sel, f, nd)) -> renderv "addfield" "fa-plus" sel ["node", formatNode state trigger nd; "fld", text f]
    | Value(Check(sel, NonEmpty)) -> renderv "check" "fa-circle-check" sel ["cond", text "nonempty"]
    | Value(Check(sel, EqualsTo(Number n))) -> renderv "check" "fa-circle-check" sel ["=", text (string n)]
    | Value(Check(sel, EqualsTo(String s))) -> renderv "check" "fa-circle-check" sel ["=", text s]
    | Shared(sk, ListReorder(sel, perm)) -> render sk "reorder" "fa-list-ol" sel ["perm", text (string perm)]
    | Shared(sk, Copy(tgt, src)) -> render sk "copy" "fa-copy" tgt ["from", Helpers.renderSelector state trigger src]
    | Shared(sk, WrapRecord(id, tg, sel)) -> render sk "wraprec" "fa-regular fa-square" sel ["id", text id; "tag", text tg]
    | Shared(sk, WrapList(tg, sel)) -> render sk "wraplist" "fa-solid fa-list-ul" sel ["tag", text tg]
    | Shared(sk, UpdateTag(sel, t1, t2)) -> render sk "retag" "fa-code" sel ["t1", text t1; "t2", text t2]
    | Shared(sk, RecordRenameField(sel, fold, fnew)) -> render sk "updid" "fa-font" sel ["old", text fold; "new", text fnew]
    | Shared(sk, ListDelete(sel, i)) -> render sk "delitm" "fa-xmark" sel ["index", text (string i)]
    | Shared(sk, RecordDelete(sel, fld)) -> render sk "delfld" "fa-rectangle-xmark" sel ["fld", text fld]

  let renderHistory trigger state = 
    if not state.HistoryState.Display then [] else [
      h?div [ "id" => "edits" ] [
        let saved = Helpers.getSavedInteractions state.DocumentState.CurrentDocument
        if not (List.isEmpty saved) then 
          yield h?h3 [] [text "Saved interactions"]
          yield h?ul [] [
            for k, histhash, ops in saved ->
              h?li [] [ 
                yield h?p [] [ 
                  yield Helpers.renderSelector state trigger [Field "saved-interactions"; Field k] 
                  match histhash with 
                  | Some histhash -> 
                      yield text " (" 
                      yield Helpers.renderHistoryHash state trigger (int histhash)
                      yield text ")"
                  | _ -> ()
                ]
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
      Header = "Delete the current document node"
      IconCode = "las la-trash"
      Events = [ CommandEvent(CancelCommand); CommandEvent(TypeCommand "!x"); EnterCommand ] }
    { Key = "c"
      Header = "Copy the current document node"
      IconCode = "las la-copy"
      Events = [ CommandEvent(CopyNode CurrentNode) ] }
    { Key = "b"
      Header = "Copy marked document node(s)"
      IconCode = "las la-copy"
      Events = [ CommandEvent(CopyNode MarkedNode) ] }
    { Key = "v"
      Header = "Paste copied at the current node"
      IconCode = "las la-paste"
      Events = [ CommandEvent(CancelCommand); CommandEvent(TypeCommand "!v*"); EnterCommand ] }
    { Key = "w"
      Header = "Paste copied at marked nodes"
      IconCode = "las la-paste"
      Events = [ CommandEvent(CancelCommand); CommandEvent(TypeCommand "!v"); EnterCommand ] }
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

  // Ordinary single command
  let command sk i l p = { EditKind = sk; Icon = i; Label = (fun _ -> text l); Parser = p }
  // Command where the label is generated based on app state when rendering (needed for highlighting selectors)
  let commandh sk i l p = { EditKind = sk; Icon = i; Label = (fun s -> h?span [] (l s)); Parser = p }
      
  let tagHole = P.hole "tag" P.ident
  let fieldHole = P.hole "field" (P.ident <|> P.atIdent)
  let numHole = P.hole "num" P.num
  let strHole = P.hole "str" P.str
  
  // Parser for selectors 
  let selPart = 
    ((P.ident <|> P.atIdent <|> P.dollarIdent) |> P.map Field) <|>
    (P.char '*' |> P.map (fun _ -> All)) <|>
    (P.num |> P.map Index) <|>
    ((P.char '<' <*>> P.ident <<*> P.char '>') |> P.map Tag)
  let refHole = 
    (P.oneOrMoreEnd (P.char '/' <*>> P.hole "sel" selPart)) <|>
    (P.char '/' |> P.map (fun _ -> []))
        
  let recordTag = P.char '<' <*>> tagHole <<*> P.char '>'
  let listTag = P.char '[' <*>> fieldHole <<*> P.char ']'

  // When parsed, returns just a single edit
  let mapEd f = P.map (fun x -> EditRecommendation [[{ Kind = f x }]] )
  // When parsed, returns a sequence of edits
  let mapEdg f = P.map (fun x -> EditRecommendation [[ for k in f x -> { Kind = k } ]])
  // Returns potentially mutiple sequences of edits
  // (those have to be merged using the current as shared base)
  let mapEds f = P.map (fun x -> EditRecommendation(f x))

  let getCommands state trigger = [
    let VK, SK = ValueKind, StructuralKind
    let doc = state.DocumentState.FinalDocument 
    let cursorSel = state.ViewState.CursorSelector
    let genSel = state.ViewState.GeneralizedStructuralSelector
    let nd, ndTrace = trace cursorSel doc |> Seq.head

    // Wrapping element(s) in some ways
    yield command SK "las la-id-card" "Wrap marked elements as record field" 
      ( P.char '<' <*>> tagHole <<*> P.char ' ' <*> fieldHole <<*> P.keyword ">" |> mapEd (fun (tag, fld) -> 
        Shared(StructuralKind, WrapRecord(fld, tag, genSel)) )) 
    yield command SK "las la-list" "Wrap marked elements as list item" 
      ( P.char '[' <*>> tagHole <<*> P.keyword "]" |> mapEd (fun (tag) -> 
        Shared(StructuralKind, WrapList(tag, genSel)) )) 
    yield command VK "las la-id-card" "Wrap the current element as record field" 
      ( P.char '<' <*>> tagHole <<*> P.char ' ' <*> fieldHole <<*> P.keyword ">*" |> mapEd (fun (tag, fld) -> 
        Shared(ValueKind, WrapRecord(fld, tag, cursorSel)) )) 
    yield command VK "las la-list" "Wrap the current element as list item" 
      ( P.char '[' <*>> tagHole <<*> P.keyword "]*" |> mapEd (fun (tag) -> 
        Shared(ValueKind, WrapList(tag, cursorSel)) )) 
        
    // Rename field, update tag
    match nd with 
    | List(oldTag, _) | Record(oldTag, _) ->
        yield command SK "las la-code" "Update tag of marked elements"
          ( P.keyword "!t " <*>> tagHole |> mapEd (fun (newTag) ->
            Shared(StructuralKind, UpdateTag(genSel, oldTag, newTag)) ))
        yield command VK "las la-code" "Update tag of the current element"
          ( P.keyword "!t* " <*>> tagHole |> mapEd (fun (newTag) ->
            Shared(ValueKind, UpdateTag(cursorSel, oldTag, newTag)) ))
    | _ -> ()
    match ndTrace with 
    | Patterns.Last(_, Field fold) ->
        yield command SK "las la-i-cursor" "Rename fields containing marked elements" 
          ( P.keyword "!r " <*>> fieldHole |> mapEd (fun (fld) ->
            Shared(StructuralKind, RecordRenameField(List.dropLast genSel, fold, fld)) ))
        yield command VK "las la-i-cursor" "Rename field containing the current element" 
          ( P.keyword "!r* " <*>> fieldHole |> mapEd (fun (fld) ->
            Shared(ValueKind, RecordRenameField(List.dropLast cursorSel, fold, fld)) ))
    | _ -> ()

    // Reorder list items
    match List.rev cursorSel with
    | (Index i)::listSelRev ->
      let listSel = List.rev listSelRev
      let genListSel = Helpers.generalizeToStructuralSelector listSel
      let listLen = match selectSingle listSel doc with List(_, nds) -> nds.Length | _ -> 0
      if i > 0 then
        yield command SK "las la-caret-up" "Move marked list items up"
          ( P.keyword "!u" |> mapEd (fun _ ->
            let perm = [for j in 0 .. listLen - 1 -> if j = i-1 then i elif j = i then i-1 else j ]
            Shared(StructuralKind, ListReorder(listSel, perm)) ))
        yield command VK "las la-caret-up" "Move the current list item up"
          ( P.keyword "!u*" |> mapEd (fun _ ->
            let perm = [for j in 0 .. listLen - 1 -> if j = i-1 then i elif j = i then i-1 else j ]
            Shared(ValueKind, ListReorder(listSel, perm)) ))
      if i < listLen - 1 then
        yield command SK "las la-caret-down" "Move marked list items down"
          ( P.keyword "!d" |> mapEd (fun _ ->
            let perm = [for j in 0 .. listLen - 1 -> if j = i+1 then i elif j = i then i+1 else j ]
            Shared(StructuralKind, ListReorder(listSel, perm)) ))
        yield command VK "las la-caret-down" "Move the current list item down"
          ( P.keyword "!d*" |> mapEd (fun _ ->
            let perm = [for j in 0 .. listLen - 1 -> if j = i+1 then i elif j = i then i+1 else j ]
            Shared(ValueKind, ListReorder(listSel, perm)) ))
    | _ -> ()
    
    // Delete current or marked element(s)
    match ndTrace with 
    | Patterns.Last(_, Field fold) ->
        yield command SK "las la-trash" "Delete currently marked record fields" 
          ( P.keyword "!x" |> mapEd (fun (_) -> Shared(StructuralKind, RecordDelete(List.dropLast genSel, fold)) ))
        yield command VK "las la-trash" "Delete the currently selected record field" 
          ( P.keyword "!x*" |> mapEd (fun (_) -> Shared(ValueKind, RecordDelete(List.dropLast cursorSel, fold)) ))
    | Patterns.Last(_, Index idx) ->
        yield command SK "las la-trash" "Delete currently marked list items" 
          ( P.keyword "!x" |> mapEd (fun (_) -> Shared(StructuralKind, ListDelete(List.dropLast genSel, idx)) ))
        yield command VK "las la-trash" "Delete the currently selected list item" 
          ( P.keyword "!x*" |> mapEd (fun (_) -> Shared(ValueKind, ListDelete(List.dropLast cursorSel, idx)) ))
    | _ -> ()

    // Copy, paste & save edits actions
    match state.CommandState.CopySource with 
    | None -> ()
    | Some src ->
        yield command SK "las la-paste" "Paste copied at marked locations"
          ( P.keyword "!v" |> mapEd (fun (_) -> 
            Shared(StructuralKind, Copy(genSel, src)) ))
        yield command VK "las la-paste" "Paste copied at the current location"
          ( P.keyword "!v*" |> mapEd (fun (_) -> 
            Shared(ValueKind, Copy(cursorSel, src)) ))

    if not (state.HistoryState.SelectedEdits.IsEmpty) then 
        let recordedEds = 
          [ for i in Seq.sort state.HistoryState.SelectedEdits ->
              state.DocumentState.Edits.[i] ]
        yield command VK "las la-save" "Save selected edits in the document"
          ( P.keyword "!s " <*>> (P.hole "field" P.ident) |> mapEdg (fun (fld) ->
            [ if select [Field "saved-interactions"] doc = [] then
                yield Value(RecordAdd([], "saved-interactions", 
                  Record("x-saved-interactions", [])))
              yield Value(RecordAdd([Field "saved-interactions"], fld, 
                Record("x-interaction", [ 
                  "historyhash", Primitive(Number state.DocumentState.FinalHash); 
                  "interactions", List("x-interaction-list", []) ])))
              for op in recordedEds ->
                Value(ListAppend([Field "saved-interactions"; Field fld; Field "interactions"], 
                  represent op)) ] ))
             
    // The following are value edits regardless of to what they are applied
    // But it may be useful to apply them to all marked nodes. We use '+' in the notation 
    // instead of '*' to indicate this. (We may want to allow '+' for other commands..)
    for sel, sk, kind in [genSel, StructuralKind, MarkedNode; cursorSel, ValueKind, CurrentNode] do
      let cr, cl = 
        if kind = CurrentNode then "the current record", "the current list"
        else "marked records", "marked lists"
      let assignSymbol = if kind = CurrentNode then P.keyword "*=" else P.keyword "="
      let fieldAssignment = P.char ':' <*>> fieldHole <<*> assignSymbol
      let anonAssignment = P.char ':' <*> assignSymbol

      // Add field of some kind to a record
      if isRecord nd then 
        match state.CommandState.CopySource with
        | None -> ()
        | Some src ->
            yield command sk "las la-paste" ("Add copied node to " + cr)
              ( fieldAssignment <<*> P.keyword "!v" |> mapEdg (fun (fld) ->
                [ Value(RecordAdd(sel, fld, Primitive(String "(temp)"))) 
                  Shared(ValueKind, Copy(sel @ [Field fld], src)) ] ))
        yield command sk "las la-id-card" ("Add record field to " + cr)
          ( fieldAssignment <*> recordTag |> mapEd (fun (fld, tag) ->
            Value(RecordAdd(sel, fld, Record(tag, []))) ))
        yield command sk "las la-list" ("Add list field to " + cr)
          ( fieldAssignment <*> listTag |> mapEd (fun (fld, tag) ->
            Value(RecordAdd(sel, fld, List(tag, []))) ))
        yield command sk "las la-link" ("Add reference field to " + cr)
          ( fieldAssignment <*> refHole |> mapEd (fun (fld, ref) ->
            Value(RecordAdd(sel, fld, Reference(ref))) ))
        yield command sk "las la-hashtag" ("Add numerical field to " + cr)
          ( fieldAssignment <*> numHole |> mapEd (fun (fld, num) ->
            Value(RecordAdd(sel, fld, Primitive(Number (int num)))) ))
        yield command sk "las la-font" ("Add string field to " + cr)
          ( fieldAssignment <*> strHole |> mapEd (fun (fld, str) ->
            Value(RecordAdd(sel, fld, Primitive(String str))) ))

      // Add item of some kind to a list
      match nd with 
      | List(_, children) ->
        match state.CommandState.CopySource with
        | None -> ()
        | Some src ->
            yield command sk "las la-paste" ("Add copied node to " + cl)
              ( anonAssignment <*>> P.keyword "!v" |> mapEd (fun _ ->
                Value(ListAppendFrom(sel, src)) ))
        yield command sk "las la-id-card" ("Add record item to " + cl)
          ( anonAssignment <*>> recordTag |> mapEd (fun (tag) ->
            Value(ListAppend(sel, Record(tag, []))) ))
        yield command sk "las la-list" ("Add list item to " + cl)
          ( anonAssignment <*>> listTag |> mapEd (fun (tag) ->
            Value(ListAppend(sel, List(tag, []))) ))
        yield command sk "las la-hashtag" ("Add numerical item to " + cl)
          ( anonAssignment <*>> numHole |> mapEd (fun (num) ->
            Value(ListAppend(sel, Primitive(Number (int num)))) ))
        yield command sk "las la-font" ("Add string item to " + cl)
          ( anonAssignment <*>> strHole |> mapEd (fun (str) ->
            Value(ListAppend(sel, Primitive(String str))) ))
      | _ -> ()
      
    // Checks that current node has value / is non-empty
    match nd with 
    | Primitive(p) ->
        yield command VK "las la-spell-check" "Check node has the current value"
          ( P.keyword "*eq" |> mapEd (fun (str) ->
            Value(Check(cursorSel, EqualsTo p)) ))
    | _ -> ()
    match nd with 
    | Primitive(String(NonEmpty _) | Number _) ->
        yield command VK "las la-check-square" "Check node value is not empty"
          ( P.keyword "*ne" |> mapEd (fun (str) ->
            Value(Check(cursorSel, NonEmpty)) ))
    | _ -> ()

    // Built-in transformations of primitive values
    // (these are also only value edits, like RecordAdd/ListAppend above)
    for sel, sk, kind in [genSel, StructuralKind, MarkedNode; cursorSel, ValueKind, CurrentNode] do
      let lbl, pAst = 
        if kind = CurrentNode then " (current)", P.char '*' |> P.map ignore
        else " (marked)", P.unit () 
      if isString nd || isNumber nd then
        for t in transformations do
          yield command sk "las la-at" (t.Label + lbl)
            ( P.char '@' <*> P.keyword t.Key <*> pAst |> mapEd (fun _ ->
              Value(PrimitiveEdit(sel, t.Key)) )) 
              
    // Saved interactions - generate nested completions
    // (one for applying to cursor, one for applying to all marked)
    for t, _, ops in Helpers.getSavedInteractions doc do
      yield command SK "las la-at" ("Apply " + t + " to marked (user)")
        ( P.keyword $"@{t}" |> P.map (fun _ -> 
            NestedRecommendation [
              for i, prefix in Seq.indexed (getTargetSelectorPrefixes ops) do 
                yield commandh SK "las la-at" (fun state -> [text "Using current as "; Helpers.renderSelector state trigger prefix])
                  ( P.keyword $"@{t} {string i}" |> mapEds (fun _ ->
                    [ for markerSel in expandWildcards genSel doc ->
                        Helpers.replacePrefixInEdits prefix markerSel ops ] )) ]
        ))
      yield command VK "las la-at" ("Apply " + t + " to current (user)")
        ( P.keyword $"@{t}*" |> P.map (fun _ -> 
            NestedRecommendation [
              for i, prefix in Seq.indexed (getTargetSelectorPrefixes ops) do 
                yield commandh VK "las la-at" (fun state -> [text "Using current as "; Helpers.renderSelector state trigger prefix])
                  ( P.keyword $"@{t}* {string i}" |> mapEds (fun _ ->
                    [ Helpers.replacePrefixInEdits prefix cursorSel ops ] )) ]
        ))
  ]

  let parseCommand state = 
    let cmdState = state.CommandState
    let recm = cmdState.KnownRecommendations |> List.tryPick (fun cmd -> 
        match P.run cmd.Parser cmdState.Command with 
        | Parsed(ed, []) -> Some(ed)
        | _ -> None )
    match recm with 
    | None when cmdState.SelectedRecommendation = -1 -> 
        CompleteCommand("")
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
        "class" => "" +? (selected, "selected") +? (c.EditKind = StructuralKind, "structural") 
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
    | CopyNode(CurrentNode) ->
        { state with CopySource = Some appstate.ViewState.CursorSelector } 
    | CopyNode(MarkedNode) ->
        //{ state with CopySource = appstate.ViewState.GeneralizedMarkersSelector } 
        { state with CopySource = Some appstate.ViewState.GeneralizedStructuralSelector } 
    
// --------------------------------------------------------------------------------------
// View and navigation
// --------------------------------------------------------------------------------------

module View = 
  let updateStructuralSelector state = 
    let genSel = Helpers.generalizeToStructuralSelector state.CursorSelector
    { state with GeneralizedStructuralSelector = genSel }

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
    { state with CursorSelector = cursorSel; CursorLocation = cursorLoc } |> updateStructuralSelector

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
        let pf = if snd state.ViewState.CursorLocation = After then "(right)" else "(left)" 
        match nd with 
        | Record(t, _) -> text $"{pf} record {t}"
        | List(t, _) -> text $"{pf} list {t}"
        | Primitive(String s) -> text $"{pf} string '{s}'"
        | Primitive(Number n) -> text $"{pf} number '{n}'"
        | Reference r -> text $"{pf} reference '{r}'"
      ]
    ]

  let rec update appstate state = function
    | ToggleViewSource ->
        match state.ViewSourceSelector with 
        | None -> { state with ViewSourceSelector = Some state.CursorSelector }
        | Some _ -> { state with ViewSourceSelector = None }
  
    | MoveCursor dir ->      
        let ncur, nsel = moveCursor appstate.DocumentState.CurrentDocument state.CursorLocation dir
        let state = { state with CursorLocation = ncur; CursorSelector = nsel } |> updateStructuralSelector
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
// Demos
// --------------------------------------------------------------------------------------
  
module Demos = 
  let update appstate state = function
    | LoadDemos ds -> { Demos = Some ds }

  let renderDemos trigger state = h?div [] [
    h?header ["style" => "padding-bottom:0px"] [ 
      h?strong [] [ text "Tools:" ]
      h?a ["href" => "javascript:;"; "click" =!> fun _ _ -> 
        trigger(DocumentEvent(Evaluate(false))) ] [text "eval step"]
      h?a ["href" => "javascript:;"; "click" =!> fun _ _ -> 
        trigger(DocumentEvent(Evaluate(true))) ] [text "eval all"]
      h?label [] [ 
        h?input ["type" => "checkbox"; "class" => "alt-hints"; "checked" => "checked" ] []
        text "Alt hint enabled" 
      ]
    ]
    h?header [] [ 
      yield h?strong [] [ text "Demo: "]
      match state.DemoState.Demos with 
      | None ->
          yield text "Loading..."
      | Some demos -> 
          for d, s, alts in demos do
            yield h?a [ "href" => "#"; "click" =!> fun _ _ -> 
              let s = { s with DemoState = state.DemoState }
              trigger(ResetState s) ] [ text d ] 
            if not (List.isEmpty alts) then yield h?span ["class" => "alts"] [
              yield text " ("
              for i, (l, ops) in List.indexed alts do 
                if i <> 0 then yield text ", "
                yield h?a [ "href" => "#"; "click" =!> fun _ _ -> 
                  trigger(DocumentEvent(MergeEdits(ops))) ] [ text l ] 
              yield text ")"
            ]
    ]
  ]

// --------------------------------------------------------------------------------------
// Application - global event handling and rendering
// --------------------------------------------------------------------------------------

let updateDocument docState = 
  { docState with 
      CurrentDocument = 
        docState.Edits.[0 .. docState.EditIndex] |> applyHistory docState.Initial  
      FinalHash = 
        docState.Edits.Hash
      FinalDocument = 
        docState.Edits |> applyHistory docState.Initial }


let rec tryEnterCommand trigger state = 
  match Commands.parseCommand state with
  | EditRecommendation(eds) ->      
      // If we get multiple groups of edits, we append each to the end of the current
      // list of edits and merge them - otherwise they interact badly
      // (e.g. if we remove items at index 0,1,2..., the first edit changes indices)
      let addToCurrent eds = state.DocumentState.Edits.Append({ Groups = [eds] })
      let histories = List.map addToCurrent eds
      let merge docState eds = Document.update state docState (MergeEdits(eds))
      let docState = histories |> List.fold merge state.DocumentState
      let docState = docState |> updateDocument
      let cmdState = { state.CommandState with Command = ""; SelectedRecommendation = -1 }
      let viewState = View.fixCursor state.DocumentState.CurrentDocument state.ViewState
      { state with ViewState = viewState; DocumentState = docState; CommandState = cmdState } 

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
  | DemoEvent e -> { state with DemoState = Demos.update state state.DemoState e }

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

let render trigger state = 
  h?div [] [
    Demos.renderDemos trigger state 
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

let fromOperationsList ops = 
  let init = rcd "div"
  let ops = { Groups = ops }
  { DocumentState = { Initial = init; Edits = ops; EditIndex = ops.Length - 1; 
      CurrentDocument = init; FinalDocument = init; FinalHash = 0 } |> updateDocument
    ViewState = { CursorLocation = [], Before; CursorSelector = []; 
      // Markers = []; GeneralizedMarkersSelector = None; 
      GeneralizedStructuralSelector = []; ViewSourceSelector = None }
    CommandState = { AltMenuDisplay = false; Command = ""; CopySource = None;   
      SelectedRecommendation = -1; KnownRecommendations = []; Recommendations = [] }
    HistoryState = { HighlightedSelector = None; 
      SelectedEdits = Set.empty; Display = false }
    DemoState = { Demos = None }
  }

let initial = fromOperationsList []
let trigger, _, getState = createVirtualDomApp "out" initial render update


//let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
//let ops1 = merge (opsCore @ refactorListOps) (merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps))
//let ops = merge ops1 (opsCore @ opsBudget)
//let ops = merge (opsCore @ opsBudget) ops1

//let ops = opsCore @ opsBudget
//let ops = opsBaseCounter
//let ops = opsBaseCounter @ opsCounterInc @ opsCounterHndl

          // TODO: This needs to move into demos (and does not belong here anyway)
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ opsBudget))) ] [text "Add budget"]
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ opsBudget @ addSpeakerOps))) ] [text "Add speaker"]
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ fixSpeakerNameOps))) ] [text "Fix name"]
          //h?button ["click" =!> fun _ _ -> triggerDoc((MergeEdits(opsCore @ refactorListOps))) ] [text "Refacor list"]
          //h?button ["click" =!> fun _ _ -> trigger (MergeEdits(opsCore @ addTransformOps)) ] [text "Add transformers"]


open Browser.XMLHttpRequest

let asyncRequest file = 
  Async.FromContinuations(fun (cont, econt, ccont) -> 
    let req = XMLHttpRequest.Create()
    req.addEventListener("load", fun _ -> cont req.responseText)
    req.``open``("GET", file)
    req.send())


let readJsonOps json = 
  List.map (List.map unrepresent) (Serializer.nodesFromJsonString json) 

let readJson json = 
  readJsonOps json |> fromOperationsList

let startWithHandler op = Async.StartImmediate <| async {
  try do! op
  with e -> Browser.Dom.console.error(e.ToString()) }

let pbdCore = opsCore @ pbdAddInput

async { 
  let demos = [ "conf-base";"conf-add";"conf-table"; "hello-base";"hello-saved"; "todo-base" ]
  let! jsons = [ for d in demos -> asyncRequest $"/demos/{d}.json" ] |> Async.Parallel
  match jsons with 
  | [| confBase; confAdd; confTable; helloBase; helloSaved; todoBase |] ->
    let demos = 
      [ 
        "conf2", readJson confBase, [
          "add", { Groups = readJsonOps confAdd }
          "table", { Groups = readJsonOps confTable }
        ] 
        "hello", readJson helloBase, [
          "saved", { Groups = readJsonOps helloSaved }
        ]
        "conf", fromOperationsList [opsCore], [
          "ada", { Groups = [opsCore @ addSpeakerOps] }
          "rename", { Groups = [opsCore @ fixSpeakerNameOps] }
          "table", { Groups = [opsCore @ refactorListOps] }
          "budget", { Groups = [opsCore @ opsBudget ] }
        ]
        //"??", fromOperationsList (mergeHistories { Groups = [pbdCore @ refactorListOps] } { Groups = [pbdCore @ pbdAddFirstSpeaker] }).Groups, []
        "todo", readJson todoBase, []
        "empty", readJson "[]", []
        "counter", fromOperationsList [opsBaseCounter], []
        ]
    trigger (DemoEvent(LoadDemos demos))
  | _ -> failwith "wrong number of demos" }
|> startWithHandler

Browser.Dom.window.onkeypress <- fun e -> 
  let targetNotText = 
    (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" ||
    (unbox<Browser.Types.HTMLInputElement> e.target).``type`` <> "text"
  if targetNotText then
    e.preventDefault();
    trigger(CommandEvent(TypeCommand e.key))

Browser.Dom.window.onkeyup <- fun e -> 
  let state = getState()
  if e.key = "Alt" && state.CommandState.AltMenuDisplay then
    e.preventDefault(); trigger(CommandEvent(ToggleAltMenu false))

Browser.Dom.window.onkeydown <- fun e -> 
  let state = getState()
  let targetNotText = 
    (unbox<Browser.Types.HTMLElement> e.target).tagName <> "INPUT" ||
    (unbox<Browser.Types.HTMLInputElement> e.target).``type`` <> "text"

  if e.ctrlKey then
    if e.key = "ArrowUp" && e.shiftKey then e.preventDefault(); trigger(HistoryEvent(ExtendSelection +1))
    if e.key = "ArrowDown" && e.shiftKey then e.preventDefault(); trigger(HistoryEvent(ExtendSelection -1))
    if e.key = "ArrowUp" then e.preventDefault(); trigger(DocumentEvent(MoveEditIndex +1))
    if e.key = "ArrowDown" then e.preventDefault(); trigger(DocumentEvent(MoveEditIndex -1))
  else
    if e.key = "Escape" then e.preventDefault(); trigger(CommandEvent(CancelCommand))
    if e.key = "Backspace" && targetNotText then e.preventDefault(); trigger(CommandEvent(BackspaceCommand))
    if e.key = "Enter" && targetNotText  then e.preventDefault(); trigger(EnterCommand)
    if e.key = "ArrowRight" && targetNotText then e.preventDefault(); trigger(ViewEvent(MoveCursor Forward))
    if e.key = "ArrowLeft" && targetNotText then e.preventDefault(); trigger(ViewEvent(MoveCursor Backward))
    if e.key = "ArrowUp" then 
      if state.CommandState.Command = "" then e.preventDefault(); trigger(ViewEvent(MoveCursor Previous))
      else e.preventDefault(); trigger(CommandEvent(PreviousRecommendation))
    if e.key = "ArrowDown" then 
      if state.CommandState.Command = "" then e.preventDefault(); trigger(ViewEvent(MoveCursor Next))
      else e.preventDefault(); trigger(CommandEvent(NextRecommendation))

    let altHints () = (Browser.Dom.document.getElementsByClassName("alt-hints").[0] :?> Browser.Types.HTMLInputElement).``checked``
    if e.key = "Alt" && altHints () && not state.CommandState.AltMenuDisplay then
      e.preventDefault(); trigger(CommandEvent(ToggleAltMenu true))

    for sc in Shortcuts.shortcuts do
      if e.altKey && e.key = sc.Key then 
        e.preventDefault()
        for evt in sc.Events do trigger(evt)
