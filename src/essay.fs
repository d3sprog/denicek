module Denicek.App.Essay

open Denicek.App
open Denicek
open Denicek.Html

type ReplayEvent<'AppEvent> =
  { Event : 'AppEvent
    Timeout : int } 

type ReplayState = 
  { Playing : bool
    StepIndex : int
    EventIndex : int }

type ReplayStep<'AppEvent, 'AppState> = 
  { Name : string
    InitialApplicationState : 'AppState
    Events : ReplayEvent<'AppEvent>[] }

type DemoState<'AppEvent, 'AppState> = 
  { DemoId : string
    InitialApplicationState : 'AppState 
    ApplicationState : 'AppState
    ReplaySteps : ReplayStep<'AppEvent, 'AppState>[]
    ReplayState : ReplayState }

type DemoEvent<'AppEvent> = 
  | ApplicationEvent of 'AppEvent
  | TogglePlay
  | PlayStep of bool
  | PreviousStep
  | NextStep
  | ResetDemo

// --------------------------------------------------------------------------------------
// UNIVERSAL - Rendering essay 
// --------------------------------------------------------------------------------------

module WebDemo = 
  
  let renderStep state step i g =
    let cls = if step > i then "done" elif step = i then "active" else ""
    let displ = if cls = "active" then "display:block" else "display:none"
    let el = Browser.Dom.document.getElementById(state.DemoId + "-" + g)
    if el = null then failwith $"Element {state.DemoId}-{g} not found!"
    el.setAttribute("style", displ)
    h?div [ "class" => "step " + cls ] [
      h?div [ "class" => "circle" ] [
        h?span [ "class" => "num" ] [ text (string (i+1)) ]
      ]
      h?div [ "class" => "label" ] [ text (g.Replace("-", " ")) ] 
    ]

  let renderStepper trigger state = 
    h?div ["class" => "stepper"] [
      let { Playing = running; StepIndex = step; EventIndex = i } = state.ReplayState
      yield h?div [ "class" => "step lbl" ] [ 
        if not running && i = state.ReplaySteps.[step].Events.Length && step = state.ReplaySteps.Length-1 then
          h?button ["disabled" => "disabled" ] [
            yield h?i ["class" => "las la-stop"] []
            yield text "done" ]
        elif not running && i = state.ReplaySteps.[step].Events.Length then
          h?button ["click" =!> fun _ _ -> trigger (PlayStep false) ] [
            yield h?i ["class" => "las la-angle-right"] []
            yield text "next" ]
        elif running then  
          h?button ["click" =!> fun _ _ -> trigger TogglePlay ] [
            yield h?i ["class" => "las la-pause"] []
            yield text "pause" ]
        else 
          h?button ["click" =!> fun _ _ -> trigger TogglePlay ] [
            yield h?i ["class" => "las la-caret-right"] []
            yield text "play" ]
      ]  
      yield h?div [ "class" => "step" ] [ 
        h?button ["title" => "Jump to the previous step"; "click" =!> fun _ _ -> trigger PreviousStep ] [
          h?i ["class" => "las la-angle-double-left"] []
        ]
      ]  
      yield h?div [ "class" => "step" ] [ 
        h?button ["title" => "Replay single event"; "click" =!> fun _ _ -> trigger (PlayStep false) ] [
          h?i ["class" => "las la-angle-right"] []
        ]
      ]  
      yield h?div [ "class" => "step" ] [ 
        h?button [ "title" => "Jump to the next step"; "click" =!> fun _ _ -> trigger NextStep ] [
          h?i ["class" => "las la-angle-double-right"] []
        ]
      ]  
      yield h?div [ "class" => "step lastbutton" ] [ 
        h?button [ "title" => "Reset the demo"; "click" =!> fun _ _ -> trigger ResetDemo ] [
          h?i ["class" => "las la-undo-alt"] []
        ]
      ]
      for i, s in Seq.indexed state.ReplaySteps do
        if i <> 0 then yield h?div ["class" => "line" ] []         
        yield renderStep state step i s.Name
    ]

  let webnicekRender trigger (state:Webnicek.ApplicationState) = [
    h?div [ "class" => "main" ] [
      yield h?div [ "class" => "doc" ] [
        let doc = state.DocumentState.CurrentDocument // TODO: Restore... Matcher.applyMatchers state.CurrentDocument 
        yield Webnicek.Document.renderDocument state trigger doc
      ]
      yield! Webnicek.Commands.renderContext id state trigger
      yield! Webnicek.History.renderHistory trigger state
    ]
    h?div [ "class" => "loc" ] [
      yield h?label [] [ text "Selected" ]
      yield h?i [] [ text "•" ] 
      yield! Webnicek.View.renderLocationInfo state
    ] ]

  let datnicekRender trigger (state:Datnicek.State) =
    [ Datnicek.render trigger state ]

  let render appRender trigger state = 
    h?div [] [
      renderStepper trigger state
      yield! appRender (ApplicationEvent >> trigger) state.ApplicationState
    ]

// --------------------------------------------------------------------------------------
// GENERIC - Update state on interaction
// --------------------------------------------------------------------------------------

  open Fable.Core.JsInterop

  let rec update appUpdate logAppEvent (state:DemoState<'AppEvent, 'AppState>) trigger evt = 
    let withRepl p s e st = { st with ReplayState = { Playing = p; StepIndex = s; EventIndex = e } }
    match evt with 
    | ResetDemo ->
        { state with ApplicationState = state.InitialApplicationState } |> withRepl false 0 0 

    | PreviousStep
    | NextStep ->
        let step = state.ReplayState.StepIndex
        let step = match evt with NextStep -> min (state.ReplaySteps.Length-1) (step+1) | _ -> max 0 (step-1)        
        { state with ApplicationState = state.ReplaySteps.[step].InitialApplicationState } |> withRepl false step 0

    | PlayStep auto when not auto || state.ReplayState.Playing ->
        let { StepIndex = step; EventIndex = i } = state.ReplayState
        let { Events = es; Name = g } = state.ReplaySteps.[step]
        if auto && state.ReplayState.EventIndex = es.Length then
          { state with ReplayState = { state.ReplayState with Playing = false } }
        elif state.ReplayState.EventIndex >= es.Length then
          let ns = (min (state.ReplaySteps.Length-1) (step + 1))
          { state with ApplicationState = state.ReplaySteps.[ns].InitialApplicationState } |> withRepl false ns 0
        else
          let stepEl = Browser.Dom.document.getElementById(state.DemoId + "-" + g)
          let speed = stepEl?dataset?speed
          let speed = match System.Double.TryParse(speed) with true, f -> f | _ -> 1.0
          if auto then Browser.Dom.window.setTimeout((fun () -> trigger (PlayStep true)), int (float es.[i].Timeout / speed)) |> ignore
          update appUpdate logAppEvent state trigger (ApplicationEvent es.[i].Event) |> withRepl auto step (i + 1)
    | PlayStep _ -> state
        
    | TogglePlay when not state.ReplayState.Playing ->
        let step = state.ReplayState.StepIndex
        if step < state.ReplaySteps.Length then
          let state = state |> withRepl true state.ReplayState.StepIndex state.ReplayState.EventIndex
          update appUpdate logAppEvent state trigger (PlayStep true)
        else state
    | TogglePlay -> 
        state |> withRepl false state.ReplayState.StepIndex state.ReplayState.EventIndex

    | ApplicationEvent evt ->
        logAppEvent evt
        let nst = appUpdate state.ApplicationState (ApplicationEvent >> trigger) evt
        { state with ApplicationState = nst }


// --------------------------------------------------------------------------------------
// WEBNICEK - Loading of replays from JSON
// --------------------------------------------------------------------------------------

module WebnicekLoader = 

  type ReplayJsonStep = {
    name : string
    merge : {| ``base``:string[]; ``with``:string[] |}
    before : string[]
    events : string[] 
  }
  type ReplayJson = { 
    steps : ReplayJsonStep[]
    events : {| name:string; events:obj[] |}[] 
  }

  let getTimeout prev evt =
    match prev, evt with
    | Some { Timeout = pt; Event = Webnicek.CommandEvent (Webnicek.TypeCommand _) }, 
        Webnicek.CommandEvent (Webnicek.TypeCommand _) -> max (pt - 15) 20
    | _, Webnicek.CommandEvent (Webnicek.TypeCommand _) -> 200
    | Some { Timeout = pt; Event = Webnicek.ViewEvent (Webnicek.MoveCursor _) }, 
        Webnicek.ViewEvent (Webnicek.MoveCursor _) -> max (pt - 15) 20
    | _, Webnicek.ViewEvent (Webnicek.MoveCursor _) -> 200
    | _ -> 600

  let preprocessReplay = 
    Array.scan (fun prev e -> Some { Event = e; Timeout = getTimeout prev e }) None
    >> Array.choose id
  
  let loadDemo data (id, url) : Async<string * ReplayStep<_, _>[]> = async { 
    let! demo = Webnicek.Loader.asyncRequest url
    let demo = Fable.Core.JS.JSON.parse(demo) |> unbox<ReplayJson>
    let eventsDb = dict [ for es in demo.events -> es.name, Webnicek.EventLogger.deserializeAppEvents es.events ]
    
    let replayEvents groups = 
      let initEdits = groups |> Array.collect (fun e -> eventsDb.[e]) 
      let init = {Webnicek.Loader.fromOperationsList [] with DemoState.Data = data }
      initEdits |> Array.fold (fun state e -> Webnicek.update state ignore e) init

    let loadStep (s:ReplayJsonStep) = 
      let events = s.events |> Array.collect (fun e -> eventsDb.[e]) |> preprocessReplay
      let state = 
        if unbox<obj> s.merge <> null then  
          let baseState = replayEvents s.merge.``base`` 
          let mergeState = replayEvents s.merge.``with`` 
          Webnicek.update baseState ignore 
            (Webnicek.DocumentEvent(Webnicek.MergeEdits(mergeState.DocumentState.DocumentEdits)))
        else
          replayEvents s.before
      { Name = s.name; Events = events; InitialApplicationState = state }
    return id, demo.steps |> Array.map loadStep
  }

  
// --------------------------------------------------------------------------------------
// DATNICEK - Loading of replays from JSON
// --------------------------------------------------------------------------------------

module DatnicekLoader = 

  type ReplayJsonStep = {
    name : string
    //merge : {| ``base``:string[]; ``with``:string[] |}
    before : string[]
    events : string[] 
  }
  type ReplayJson = { 
    steps : ReplayJsonStep[]
    events : {| name:string; events:obj[] |}[] 
  }

  let getTimeout evt =
    match evt with
    | Datnicek.SelectCell _ -> 1
    | Datnicek.GridRecommend(_, _, recs) when recs.Length = 0 -> 1
    | Datnicek.SelectCell _ 
    | Datnicek.GridRecommend _ -> 600
    | _ -> 300

  let preprocessReplay = Array.map (fun e -> { Event = e; Timeout = getTimeout e }) 
  
  let loadDemo data (id, url) : Async<string * ReplayStep<_, _>[]> = async { 
    let! demo = Webnicek.Loader.asyncRequest url
    let demo = Fable.Core.JS.JSON.parse(demo) |> unbox<ReplayJson>
    let eventsDb = dict [ for es in demo.events -> es.name, Datnicek.EventLogger.deserializeEvents es.events ]
    
    let replayEvents groups = 
      let initEdits = groups |> Array.collect (fun e -> eventsDb.[e]) 
      let init = { Datnicek.Loader.initialFromJson "[]" with DataFiles = data }
      initEdits |> Array.fold (fun state e -> Datnicek.update state ignore e) init

    let loadStep (s:ReplayJsonStep) = 
      let events = s.events |> Array.collect (fun e -> eventsDb.[e]) |> preprocessReplay
      let state = 
        //if unbox<obj> s.merge <> null then  
        //  let baseState = replayEvents s.merge.``base`` 
        //  let mergeState = replayEvents s.merge.``with`` 
        //  Webnicek.update baseState ignore 
        //    (Webnicek.DocumentEvent(Webnicek.MergeEdits(mergeState.DocumentState.DocumentEdits)))
        //else
          replayEvents s.before
      { Name = s.name; Events = events; InitialApplicationState = state }
    return id, demo.steps |> Array.map loadStep
  }

  
// --------------------------------------------------------------------------------------
// WEBNICEK - Browser integrfation
// --------------------------------------------------------------------------------------
  
module WebnicekDemos = 
  open WebnicekLoader
  open Fable.Core.JsInterop

  let findDemos () =
    let demos = Browser.Dom.document.getElementsByClassName("webnicek-demo")
    [ for i in 0 .. demos.length - 1 -> 
      demos.[i].id.Replace("-demo", ""), demos.[i]?dataset?file ]

  let loadData () = async { 
    let data = [ "avia.csv"; "rail.csv" ]
    let! csvs = [ for d in data -> Webnicek.Loader.asyncRequest $"/essay/{d}" ] |> Async.Parallel
    return Map.ofSeq (Seq.zip data (Seq.map Webnicek.Loader.readCsvWithHeading csvs)) }

  let startDemos logAppEvent = async {
    let! data = loadData()
    let! demos = findDemos() |> List.map (loadDemo data) |> Async.Parallel
    let activations = System.Collections.Generic.Dictionary<_, _>()
    for demoId, demoSteps in demos do
      let repl = { Playing = false; StepIndex = 0; EventIndex = 0 }
      let initialStep = demoSteps |> Array.find (fun s -> s.Name = "start")
      let initialAppState = initialStep.InitialApplicationState
      let initial = 
        { ApplicationState = initialAppState; InitialApplicationState = initialAppState
          ReplaySteps = demoSteps; ReplayState = repl; DemoId = demoId }
      let id = (demoId + "-demo")
      let trigger, _, getState = 
        createVirtualDomApp id initial 
          (WebDemo.render WebDemo.webnicekRender) 
          (WebDemo.update Webnicek.update logAppEvent)
      let activate () = 
        Log.log "essay" $"Activating '{demoId}'"
        Webnicek.Loader.setupHandlers (ApplicationEvent >> trigger) (fun () -> getState().ApplicationState)
      activations.Add(demoId, activate)
    return activations
  }

// --------------------------------------------------------------------------------------
// DATNICEK - Browser integrfation
// --------------------------------------------------------------------------------------
  
module DatnicekDemos = 
  open DatnicekLoader
  open Fable.Core.JsInterop

  let findDemos () =
    let demos = Browser.Dom.document.getElementsByClassName("datnicek-demo")
    [ for i in 0 .. demos.length - 1 -> 
      demos.[i].id.Replace("-demo", ""), demos.[i]?dataset?file ]

  let loadData () = async { 
    let data = [ "eurostat/avia.tsv" ]
    let! tsvs = [ for d in data -> Datnicek.Loader.asyncRequest $"/data/{d}" ] |> Async.Parallel
    return Map.ofSeq (Seq.zip data (Seq.map Datnicek.Loader.readTsv tsvs)) }

  let startDemos logAppEvent = async {
    let! data = loadData() 
    let! demos = findDemos() |> List.map (loadDemo data) |> Async.Parallel
    let demos = demos |> Array.map (fun (k, v) -> 
      k, v |> Array.map (fun s -> { s with InitialApplicationState.DataFiles = data }))
    let activations = System.Collections.Generic.Dictionary<_, _>()
    for demoId, demoSteps in demos do
      let repl = { Playing = false; StepIndex = 0; EventIndex = 0 }
      let initialStep = demoSteps |> Array.find (fun s -> s.Name = "start")
      let initialAppState = initialStep.InitialApplicationState 
      let initial = 
        { ApplicationState = initialAppState; InitialApplicationState = initialAppState
          ReplaySteps = demoSteps; ReplayState = repl; DemoId = demoId }
      let id = (demoId + "-demo")
      let trigger, _, getState = 
        createVirtualDomApp id initial 
          (WebDemo.render WebDemo.datnicekRender) 
          (WebDemo.update Datnicek.update logAppEvent)
      let activate () = 
        Log.log "essay" $"Activating '{demoId}'"
        Datnicek.Loader.setupHandlers (ApplicationEvent >> trigger) 
      activations.Add(demoId, activate)
    return activations
  }

// --------------------------------------------------------------------------------------
// WEBNICEK - Browser integrfation
// --------------------------------------------------------------------------------------

module Loader = 
  open Fable.Core.JsInterop

  let startWithHandlerAndCont cont op = 
    let op = async {
      try return! op
      with e -> Browser.Dom.console.error(e); return! raise e }
    Async.StartWithContinuations(op, cont, ignore, ignore)

  let displayChapter (activations:System.Collections.Generic.Dictionary<_, _>) =
    let hash = Browser.Dom.window.location.hash
    let current = if hash <> null && hash.StartsWith("#chapter") then hash.Substring(1) else "chapter1"
    Log.log "essay" $"Display chapter '{current}'"
    let chaps = Browser.Dom.document.getElementsByClassName("chapter")
    for i in 0 .. chaps.length - 1 do 
      chaps.[i].setAttribute("style", "display:none")
      Browser.Dom.document.getElementById(chaps.[i].id+"-link").className <- ""
    Browser.Dom.document.getElementById(current).setAttribute("style", "display:block;")
    Browser.Dom.document.getElementById(current+"-link").className <- "current"
    if activations.ContainsKey current then activations.[current] ()
    else Log.log "essay" $"Could not activate chapter '{current}'"

  let events = ResizeArray<obj>() 
  let logWebnicekEvent e = 
    let ejs = Webnicek.EventLogger.serializeAppEvent e
    events.Add(ejs)
  let logDatnicekEvent e = 
    let ejs = Datnicek.EventLogger.serializeEvent e
    events.Add(ejs)

  Browser.Dom.window?resetEventLog <- fun () -> events.Clear()
  Browser.Dom.window?getEventLog <- fun () -> Fable.Core.JS.JSON.stringify(events)

  let start () =
    let activations = System.Collections.Generic.Dictionary<_, _>()
    Browser.Dom.window.addEventListener("hashchange", fun e -> 
      Log.log "essay" $"Hash changed to '{Browser.Dom.window.location.hash}'." 
      displayChapter activations)
    WebnicekDemos.startDemos logWebnicekEvent  |> startWithHandlerAndCont (fun a -> 
      Log.log "essay" $"Initialized webnicek {List.ofSeq a.Keys}"
      for kv in a do activations.Add(kv.Key, kv.Value)
      displayChapter activations)
    DatnicekDemos.startDemos logDatnicekEvent  |> startWithHandlerAndCont (fun a -> 
      Log.log "essay" $"Initialized datnicek {List.ofSeq a.Keys}"
      for kv in a do activations.Add(kv.Key, kv.Value)
      displayChapter activations)
