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

type DemoState = 
  { DemoId : string
    InitialApplicationState : Webnicek.ApplicationState 
    ApplicationState : Webnicek.ApplicationState 
    ReplayEventGroups : list<string * list<ReplayEvent>> 
    ReplayState : ReplayState }

type DemoEvent = 
  | ApplicationEvent of Webnicek.ApplicationEvent
  | TogglePlay
  | PlayStep of bool
  | PreviousStep
  | NextStep
  | ResetDemo


module WebnicekDemos = 
  
  let renderStep state step i g =
    let cls = if step > i then "done" elif step = i then "active" else ""
    let displ = if cls = "active" then "display:block" else "display:none"
    Browser.Dom.document.getElementById(state.DemoId + "-" + g).setAttribute("style", displ)
    h?div [ "class" => "step " + cls ] [
      h?div [ "class" => "circle" ] [
        h?span [ "class" => "num" ] [ text (string (i+1)) ]
      ]
      h?div [ "class" => "label" ] [ text g ] 
    ]

  let renderStepper trigger state = 
    h?div ["class" => "stepper"] [
      let { Playing = running; StepIndex = step } = state.ReplayState
      //let dis = if running then ["disabled" => "disabled"] else []
      yield h?div [ "class" => "step" ] [ 
        h?button ["click" =!> fun _ _ -> trigger PreviousStep ] [
          h?i ["class" => "las la-fast-backward"] []
        ]
      ]  
      yield h?div [ "class" => "step" ] [ 
        h?button ["click" =!> fun _ _ -> trigger TogglePlay ] [
          if running then  h?i ["class" => "las la-pause"] []
          else h?i ["class" => "las la-play"] []
        ]
      ]  
      yield h?div [ "class" => "step" ] [ 
        h?button ["click" =!> fun _ _ -> trigger (PlayStep false) ] [
          h?i ["class" => "las la-step-forward"] []
        ]
      ]  
      yield h?div [ "class" => "step" ] [ 
        h?button ["click" =!> fun _ _ -> trigger NextStep ] [
          h?i ["class" => "las la-fast-forward"] []
        ]
      ]  
      yield h?div [ "class" => "step lastbutton" ] [ 
        h?button ["click" =!> fun _ _ -> trigger ResetDemo ] [
          h?i ["class" => "las la-undo-alt"] []
        ]
      ]
      for i, (g, _) in Seq.indexed state.ReplayEventGroups do
        yield renderStep state step i g
        yield h?div ["class" => "line" ] []         
      yield renderStep state step state.ReplayEventGroups.Length "done"
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

  let loadDemo (id, url) = async { 
    let! demo = Webnicek.Loader.asyncRequest url
    let events = Fable.Core.JS.JSON.parse(demo) |> Webnicek.EventLogger.deserializeAppEvents
    return id, events
  }

  let dropMarkers events = 
    let rec (|ConsumeMarker|_|) = function
      | Webnicek.CommandEvent(Webnicek.TypeCommand _)::ConsumeMarker xs -> Some xs
      | Webnicek.EnterCommand::xs -> Some xs
      | _ -> None
    let rec loop acc xs = 
      match xs with
      | Webnicek.CommandEvent(Webnicek.TypeCommand "/")::ConsumeMarker xs -> loop acc xs
      | x::xs -> loop (x::acc) xs
      | [] -> List.rev acc
    loop [] events

  let getTimeout prev evt =
    match prev, evt with
    | Some prev, Webnicek.CommandEvent (Webnicek.TypeCommand _) -> 
        if prev.Timeout <= 150 then max (prev.Timeout - 10) 20 else 150
    | _ -> 600

  let preprocessReplay events = 
    events 
    |> List.groupByMarker "" (function 
      | Webnicek.DemoEvent(Webnicek.DefineMarker m) -> Some(m.Trim()) | _ -> None)
    |> List.map (fun (k, g) -> 
        let evts = 
          dropMarkers g 
          |> List.scan (fun prev e -> Some { Event = e; Timeout = getTimeout prev e }) None
          |> List.choose id
        k, evts)
    

  open Fable.Core.JsInterop

  let rec update (state:DemoState) trigger evt = 
    let withRepl p s e st = { st with ReplayState = { Playing = p; StepIndex = s; EventIndex = e } }
    match evt with 
    | ResetDemo ->
        { state with ApplicationState = state.InitialApplicationState } |> withRepl false 0 0 

    | PreviousStep
    | NextStep ->
        let step= state.ReplayState.StepIndex
        let step = match evt with NextStep -> min (state.ReplayEventGroups.Length-1) step | _ -> max -1 (step-2)
        let state = { state with ApplicationState = state.InitialApplicationState } |> withRepl false (step+1) 0
        state.ReplayEventGroups.[ 0 .. step ] |> List.fold (fun state (g, es) -> 
          es |> List.fold (fun st e -> update st trigger (ApplicationEvent e.Event)) state) state        

    | PlayStep auto when not auto || state.ReplayState.Playing ->
        let { StepIndex = step; EventIndex = i } = state.ReplayState
        let g, es = state.ReplayEventGroups.[step]
        let stepEl = Browser.Dom.document.getElementById(state.DemoId + "-" + g)
        let speed = stepEl?dataset?speed
        let speed = match System.Double.TryParse(speed) with true, f -> f | _ -> 1.0
        if state.ReplayState.EventIndex >= es.Length then
          state |> withRepl false (step + 1) 0
        else
          if auto then Browser.Dom.window.setTimeout((fun () -> trigger (PlayStep true)), int (float es.[i].Timeout / speed)) |> ignore
          update state trigger (ApplicationEvent es.[i].Event) |> withRepl auto step (i + 1)
    | PlayStep _ -> state
    
    | TogglePlay when not state.ReplayState.Playing ->
        let step = state.ReplayState.StepIndex
        if step < state.ReplayEventGroups.Length then
          let state = state |> withRepl true state.ReplayState.StepIndex state.ReplayState.EventIndex
          update state trigger (PlayStep true)
        else state

    | TogglePlay -> 
        state |> withRepl false state.ReplayState.StepIndex state.ReplayState.EventIndex

    | ApplicationEvent evt ->
        let nst = Webnicek.update state.ApplicationState (ApplicationEvent >> trigger) evt
        { state with ApplicationState = nst }  
    
  let findDemos () =
    let demos = Browser.Dom.document.getElementsByClassName("demo")
    [ for i in 0 .. demos.length - 1 -> demos.[i].id.Replace("-demo", ""), demos.[i]?dataset?file ]

  let start () =  async {
    let! demos = findDemos() |> List.map loadDemo |> Async.Parallel
    let activations = System.Collections.Generic.Dictionary<_, _>()
    for demoId, demoEvents in demos do
      // Apply the first group of edits automatically
      Log.log "essay" $"Setting up demo '{demoId}'."
      let initEdits, groups =
        match demoEvents |> List.ofArray |> preprocessReplay with 
        | (_, init)::groups -> init, groups
        | _ -> failwith "Missing initialization section"
      let initialAppState = Webnicek.Loader.fromOperationsList []
      let initialAppState = initEdits |> List.fold (fun state e -> Webnicek.update state ignore e.Event) initialAppState
      let repl = { Playing = false; StepIndex = 0; EventIndex = 0 }
      let initial = 
        { ApplicationState = initialAppState; InitialApplicationState = initialAppState
          ReplayEventGroups = groups; ReplayState = repl; DemoId = demoId }
      let id = (demoId + "-demo")
      let trigger, _, getState = createVirtualDomApp id initial (render id) update
      //trigger PlayDemo
      
      let activate () = 
        Log.log "essay" $"Activating '{demoId}'"
        Webnicek.Loader.setupHandlers (ApplicationEvent >> trigger) (fun () -> getState().ApplicationState)
      activations.Add(demoId, activate)
    return activations
  }

module Loader = 
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

  let start () =
    let activations = ref (System.Collections.Generic.Dictionary<_, _>())
    Browser.Dom.window.addEventListener("hashchange", fun e -> 
      Log.log "essay" $"Hash changed to '{Browser.Dom.window.location.hash}'." 
      displayChapter activations)
    WebnicekDemos.start ()  |> startWithHandlerAndCont (fun a -> 
      Log.log "essay" $"Initialized ${List.ofSeq a.Keys}"
      activations.Value <- a; displayChapter activations)
