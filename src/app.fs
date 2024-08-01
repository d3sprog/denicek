module Tbd.App

open Tbd.Html
open Tbd.Doc
open Tbd.Demos

type State = 
  { Initial : Node 
    Edits : Edit list 
    //SelectedNode : string option
    HighlightedSelector : Selectors option
    //ControlsLocation : float * float
    //HistoryIndex : Map<string, int>
    Location : int 

    Cursor : Selectors
    Command : string option

    MacroRange : int option * int option
    }
  member x.CurrentDocument = 
    x.Edits.[0 .. x.Location]
    |> List.fold apply x.Initial
  member x.FinalDocument = 
    x.Edits
    |> List.fold apply x.Initial

type CursorMove =
  | Up | Down | Previous | Next

type Event = 
  | MoveCursor of CursorMove

  | StartMacro
  | EndMacro

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
  (*let handlers = 
    match nd with 
    | Record(_, nds) -> nds |> List.choose (function
        | id, Record("x-event-handler", edits) ->
            Some(id =!> fun _ _ ->
              let handler = [ for e in edits -> unrepresent e ]
              trigger(Evaluate(true))
              trigger(MergeEdits(state.Edits @ handler))
              trigger(Evaluate(true))
              trigger(Move(System.Int32.MaxValue))
            )
        | _ -> None)
    | _ -> []*)
  let attrs = [ 
    yield "id" => pid 
    yield "class" => 
      ( match state.HighlightedSelector with Some s when matches s path -> "hidoc " | _ -> "") + 
      //( if historyIndex > 0 then "historical " else "") +
      ( if matches state.Cursor path then "cursor " else "")
    //yield! handlers
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
        if op.IsSome then yield renderNode state trigger (path @ [Field "op"]) (pid ++ "op") op.Value
        else yield text "@"
        yield text "("
        for i, (f, a) in Seq.indexed args do
          if i <> 0 then yield text ", "
          yield text $"{f}="
          yield renderNode state trigger (path @ [Field f]) (pid ++ f) a
        yield text ")"
    | List(_, nds) -> 
        for i, a in Seq.indexed nds -> renderNode state trigger (path @ [Index i]) (pid ++ string i) a
    | Record(_, nds) -> 
        for f, a in nds -> renderNode state trigger (path @ [Field f]) (pid ++ f) a
    | Reference(sel) -> yield formatSelector state trigger sel
    | Primitive(String s) -> yield text s
    | Primitive(Number n) -> yield text (string n)        
  ]

  h?(tag) attrs body
    

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
  h?div [ "id" => "main" ] [
    yield h?div [ "id" => "doc" ] [
      let doc = state.CurrentDocument // Matcher.applyMatchers state.CurrentDocument 
      renderNode state trigger [] "" doc
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
    match state.Command with 
    | Some cmd -> 
        yield h?div [ "id" => "cmd" ] [
          h?p [ "class" => "input" ] [ text (if cmd = "" then "?" else cmd) ]
          let commands = [
            "wr", " [tag] [id] [list|object|apply]", "Wrap current element in a record" 
            "id", " [id]", "Change id of current element to 'id'"
            "an", " [fld] [num]", "Append number 'num' as a field 'fld' to the current list"
            "as", " [fld] [str]", "Append string 'str' as a field 'fld' to the current list"
            "ar", " [fld] [num|str]*", "Append reference (selector) as a field 'fld' to the currnet list"
            "ah", " [evt]", "Append recorded edits as handler for event 'evt'"
            "ms", "", "Start macro recording"
            "me", "", "End macro recording"
            "ev", "", "Evaluate all formulas"
          ]

          h?ul [] [
            for k, args, doc in commands ->
              h?li [] [ 
                h?span [ "class" => "sample"] [ h?kbd [] [ text k ]; text args ] 
                h?span [ "class" => "doc" ] [ text doc ]
              ]
          ]
        ]
    | _ -> ()
  ]

//let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
//let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
//let ops1 = merge (opsCore @ refactorListOps) (merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps))
//let ops = merge ops1 (opsCore @ opsBudget)
//let ops = merge (opsCore @ opsBudget) ops1

//let ops = opsCore @ opsBudget
let ops = opsCore 

//let ops = opsBaseCounter
//let ops = opsBaseCounter @ opsCounterInc @ opsCounterHndl
  
let state = 
  { Initial = rcd "div"
    HighlightedSelector = None
    Edits = ops
    //HistoryIndex = Map.empty
    //ControlsLocation = 0.0, 0.0
    //SelectedNode = None
    Location = ops.Length - 1 
    Cursor = []
    Command = None
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
    { state with Location = min (state.Edits.Length-1) state.Location }
  | Move d ->
    { state with Location = max 0 (min (state.Edits.Length - 1) (state.Location + d)) }
  | Show i ->
    { state with Location = i }


  | MoveCursor dir ->
    state (*
    let self = selectSingle state.Cursor state.CurrentDocument 
    let parentCur = List.truncate (state.Cursor.Length - 1) state.Cursor
    let parentNd () = selectSingle parentCur state.CurrentDocument
    let ret c = printfn "Cursor: %A" c; { state with Cursor = c } 
    match dir with 
    | Down -> 
        match self.Expression with 
        | Record(_, List, _::_) -> state.Cursor @ [Index 0] |> ret
        | Record(_, _, nd::_) -> state.Cursor @ [Field nd.ID] |> ret
        | _ -> state
    | _ when state.Cursor.Length = 0 -> state        
    | Up -> parentCur |> ret
    | Previous | Next -> 
        match parentNd().Expression, List.last state.Cursor with 
        | Record(_, List, ls), Index n ->
            if dir = Previous && n > 0 then parentCur @ [Index (n-1)] |> ret
            elif dir = Next && n < ls.Length-1 then parentCur @ [Index (n+1)] |> ret
            else state
        | Record(_, _, nds), Field f ->
            let n = nds |> List.findIndex (fun nd -> nd.ID = f)
            if dir = Previous && n > 0 then parentCur @ [Field (nds.[n-1].ID)] |> ret
            elif dir = Next && n < nds.Length-1 then parentCur @ [Field (nds.[n+1].ID)] |> ret
            else state
        | _ -> state
        *)
  | StartCommand -> { state with Command = Some "" }
  | CancelCommand -> { state with Command = None }
  | BackspaceCommand  -> 
      match state.Command with 
      | Some cmd -> { state with Command = Some cmd.[0 .. cmd.Length-2] }
      | _ -> state 
  | TypeCommand c -> 
      match state.Command with 
      | Some cmd -> { state with Command = Some(cmd + c) }
      | _ -> { state with Command = Some(c) }
  | EnterCommand -> 
      state
      (*
      match state.Command with 
      | Some cmd -> 
          let parseSel sel =
            [ for s in sel -> 
                match s, System.Int32.TryParse s with 
                | _, (true, n) -> Index n
                | "*", _ -> All
                | s, _ -> Field s ]
          let retEhEds eds = 
            let eds = [ for ed in eds -> { Kind = ed; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies = [] } ]
            { state with 
                Edits = merge state.Edits (state.Edits @ eds) 
                MacroRange = None, None
                Location = state.Edits.Length + eds.Length - 1; Command = None }
          let retEd ed = 
            let ed = { Kind = ed; CanDuplicate = true; IsEvaluated = false; Conditions = []; Dependencies = [] } 
            let mr = match state.MacroRange with Some s, _ -> Some s, Some (state.Edits.Length) | _ -> state.MacroRange
            { state with 
                Edits = merge state.Edits (state.Edits @ [ed]) 
                MacroRange = mr
                Location = state.Edits.Length; Command = None }

          let retOp op = 
            update { state with Command = None } op
          match List.ofSeq (cmd.Split(' ')) with 
          | "wr"::tag::id::(kind & ("list" | "object" | "apply"))::[] ->
              let kind = match kind with "list" -> List | "object" -> Object | "apply" -> Apply | _ -> failwith "impossible"
              WrapRecord(id, tag, kind, state.Cursor, false) |> retEd
          | "id"::id::[] ->
              RecordRenameField(state.Cursor, id) |> retEd
          | "an"::fld::num::[] ->
              ListAppend(state.Cursor, { ID = fld; Expression = Primitive(Number (int num)) }) |> retEd
          | "as"::fld::strs ->
              ListAppend(state.Cursor, { ID = fld; Expression = Primitive(String (String.concat " " strs)) }) |> retEd
          | "ar"::fld::sel ->
              ListAppend(state.Cursor, { ID = fld; Expression = Reference (parseSel sel) }) |> retEd
          | "ah"::evt::[] -> 
              let eds =
                match state.MacroRange with 
                | Some l, Some h -> state.Edits.[l .. h]
                | _ -> []
              [ yield ListAppend(state.Cursor, { ID = evt; Expression = Record("x-event-handler", List, []) }) 
                for op in eds ->
                  ListAppend(state.Cursor @ [Field evt], represent op) ]
              |> retEhEds
          | "ev"::[] ->
              Evaluate(true) |> retOp
          | "ms"::[] ->
              StartMacro |> retOp
          | "me"::[] ->
              EndMacro |> retOp
          | _ -> failwithf "EnterCommand: Unsupported command >>%A<<" cmd
          
      | _ -> state
      *)
    | EndMacro -> 
        match state.MacroRange with 
        | Some s, _ -> { state with MacroRange = Some s, Some (state.Edits.Length-1) }
        | _ -> state
    | StartMacro -> { state with MacroRange = Some (state.Edits.Length), Some (state.Edits.Length) }
(*
    "wr", " [tag] [id] [list|object|apply]", "Wrap current element in a record" 
    "id", " [id]", "Change id of current element to 'id'"
    "an", " [fld] [num]", "Append number 'num' as a field 'fld' to the current record"
    "ar", " [fld] [num|str|'*']+", "Append reference (selector) as a field 'fld' to the currnet record"
*)
  

let trigger, _ = createVirtualDomApp "out" state render update
//Browser.Dom.window.onclick <- fun e -> 
//  trigger(SelectNode None)

Browser.Dom.window.onkeypress <- fun e -> 
  if e.key = "!" then e.preventDefault(); trigger(StartCommand)
  else trigger(TypeCommand e.key)
  
Browser.Dom.window.onkeydown <- fun e -> 
  if e.ctrlKey then
    if e.key = "ArrowUp" then e.preventDefault(); trigger(Move +1)
    if e.key = "ArrowDown" then e.preventDefault(); trigger(Move -1)
  else
    Browser.Dom.console.log(e.key)
    if e.key = "Escape" then e.preventDefault(); trigger(CancelCommand)
    if e.key = "Backspace" then e.preventDefault(); trigger(BackspaceCommand)
    if e.key = "Enter" then e.preventDefault(); trigger(EnterCommand)
    if e.key = "ArrowUp" then e.preventDefault(); trigger(MoveCursor Previous)
    if e.key = "ArrowDown" then e.preventDefault(); trigger(MoveCursor Next)
    if e.key = "ArrowRight" then e.preventDefault(); trigger(MoveCursor Down)
    if e.key = "ArrowLeft" then e.preventDefault(); trigger(MoveCursor Up)


//trigger (MergeEdits(opsCore @ opsBudget))
//trigger (Evaluate true)
//trigger (Move 100000)
