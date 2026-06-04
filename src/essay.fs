module Denicek.App.Essay

open Denicek.App
open Denicek
open Denicek.Html

type ReplayEvent =
  { Event : Webnicek.ApplicationEvent 
    Timeout : int } 

type ReplayState = 
  { Playing : bool
    StepIndex : int
    EventIndex : int }

type ReplayStep = 
  { Name : string
    InitialApplicationState : Webnicek.ApplicationState 
    Events : ReplayEvent[] }

type DemoState = 
  { DemoId : string
    InitialApplicationState : Webnicek.ApplicationState 
    ApplicationState : Webnicek.ApplicationState 
    ReplaySteps : ReplayStep[]
    ReplayState : ReplayState }

type DemoEvent = 
  | ApplicationEvent of Webnicek.ApplicationEvent
  | TogglePlay
  | PlayStep of bool
  | PreviousStep
  | NextStep
  | ResetDemo


// --------------------------------------------------------------------------------------
// Rendering essay 
// --------------------------------------------------------------------------------------

module WebDemo = 
  
  let renderStep state step i g =
    let cls = if step > i then "done" elif step = i then "active" else ""
    let displ = if cls = "active" then "display:block" else "display:none"
    Browser.Dom.document.getElementById(state.DemoId + "-" + g).setAttribute("style", displ)
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

  let render id triggerDemo stateDemo = 
    let trigger = ApplicationEvent >> triggerDemo
    let state = stateDemo.ApplicationState
    h?div [] [
      renderStepper triggerDemo stateDemo
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
      ]
    ]

// --------------------------------------------------------------------------------------
// Update state on interaction
// --------------------------------------------------------------------------------------
  open Fable.Core.JsInterop

  let rec update appEvent (state:DemoState) trigger evt = 
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
          update appEvent state trigger (ApplicationEvent es.[i].Event) |> withRepl auto step (i + 1)
    | PlayStep _ -> state
        
    | TogglePlay when not state.ReplayState.Playing ->
        let step = state.ReplayState.StepIndex
        if step < state.ReplaySteps.Length then
          let state = state |> withRepl true state.ReplayState.StepIndex state.ReplayState.EventIndex
          update appEvent state trigger (PlayStep true)
        else state
    | TogglePlay -> 
        state |> withRepl false state.ReplayState.StepIndex state.ReplayState.EventIndex

    | ApplicationEvent evt ->
        appEvent evt
        let nst = Webnicek.update state.ApplicationState (ApplicationEvent >> trigger) evt
        { state with ApplicationState = nst }


// --------------------------------------------------------------------------------------
// Loading of replays from JSON
// --------------------------------------------------------------------------------------
module Loader = 

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
  
  let loadDemo (id, url) : Async<string * ReplayStep[]> = async { 
    let! demo = Webnicek.Loader.asyncRequest url
    let demo = Fable.Core.JS.JSON.parse(demo) |> unbox<ReplayJson>
    let eventsDb = dict [ for es in demo.events -> es.name, Webnicek.EventLogger.deserializeAppEvents es.events ]
    
    let replayEvents groups = 
      let initEdits = groups |> Array.collect (fun e -> eventsDb.[e]) 
      let init = Webnicek.Loader.fromOperationsList []
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
// Browser integrfation
// --------------------------------------------------------------------------------------
  open Fable.Core.JsInterop
    
  let findDemos () =
    let demos = Browser.Dom.document.getElementsByClassName("demo")
    [ for i in 0 .. demos.length - 1 -> demos.[i].id.Replace("-demo", ""), demos.[i]?dataset?file ]

  let startDemos appEvent =  async {
    let! demos = findDemos() |> List.map loadDemo |> Async.Parallel
    let activations = System.Collections.Generic.Dictionary<_, _>()
    for demoId, demoSteps in demos do
      let repl = { Playing = false; StepIndex = 0; EventIndex = 0 }
      let initialStep = demoSteps |> Array.find (fun s -> s.Name = "start")
      let initialAppState = initialStep.InitialApplicationState
      let initial = 
        { ApplicationState = initialAppState; InitialApplicationState = initialAppState
          ReplaySteps = demoSteps; ReplayState = repl; DemoId = demoId }
      let id = (demoId + "-demo")
      let trigger, _, getState = createVirtualDomApp id initial (WebDemo.render id) (WebDemo.update appEvent)
      let activate () = 
        Log.log "essay" $"Activating '{demoId}'"
        Webnicek.Loader.setupHandlers (ApplicationEvent >> trigger) (fun () -> getState().ApplicationState)
      activations.Add(demoId, activate)
    return activations
  }


  let startWithHandlerAndCont cont op = 
    let op = async {
      try return! op
      with e -> Browser.Dom.console.error(e); return! raise e }
    Async.StartWithContinuations(op, cont, ignore, ignore)

  let displayChapter (activations:ref<System.Collections.Generic.Dictionary<_, _>>) =
    let hash = Browser.Dom.window.location.hash
    let current = if hash <> null && hash.StartsWith("#chapter") then hash.Substring(1) else "chapter1"
    Log.log "essay" $"Display chapter '{current}'"
    let chaps = Browser.Dom.document.getElementsByClassName("chapter")
    for i in 0 .. chaps.length - 1 do 
      chaps.[i].setAttribute("style", "display:none")
      Browser.Dom.document.getElementById(chaps.[i].id+"-link").className <- ""
    Browser.Dom.document.getElementById(current).setAttribute("style", "display:block;")
    Browser.Dom.document.getElementById(current+"-link").className <- "current"
    activations.Value.[current] ()

  let events = ResizeArray<obj>() 

  let logAppEvent e = 
    let ejs = Webnicek.EventLogger.serializeAppEvent e
    events.Add(ejs)

  Browser.Dom.window?resetEventLog <- fun () -> events.Clear()
  Browser.Dom.window?getEventLog <- fun () -> Fable.Core.JS.JSON.stringify(events)

  let start () =
    let activations = ref (System.Collections.Generic.Dictionary<_, _>())
    Browser.Dom.window.addEventListener("hashchange", fun e -> 
      Log.log "essay" $"Hash changed to '{Browser.Dom.window.location.hash}'." 
      displayChapter activations)
    startDemos logAppEvent  |> startWithHandlerAndCont (fun a -> 
      Log.log "essay" $"Initialized ${List.ofSeq a.Keys}"
      activations.Value <- a; displayChapter activations)
