module Denicek.App.Essay

open Denicek.App
open Denicek
open Denicek.Html

type ReplayEvent =
  { Event : Webnicek.ApplicationEvent 
    Timeout : int } 

type DemoState = 
  { DemoId : string
    ApplicationState : Webnicek.ApplicationState 
    ReplayState : bool * int
    ReplayEventGroups : list<string * list<ReplayEvent>> }

type DemoEvent = 
  | ApplicationEvent of Webnicek.ApplicationEvent
  | UpdateReplayState of bool * int
  | PlayDemo


module WebnicekDemos = 
  
  let renderStep state step i g =
    let cls = if step > i then "done" elif step = i then "active" else ""
    let displ = if cls = "active" then "display:block" else "display:none"
    Browser.Dom.document.getElementById(state.DemoId + "-" + g).setAttribute("style", displ)
    //Browser.Dom.console.log(state.DemoId + "-" + g)
    h?div [ "class" => "step " + cls ] [
      h?div [ "class" => "circle" ] [
        h?span [ "class" => "num" ] [ text (string (i+1)) ]
      ]
      h?div [ "class" => "label" ] [ text g ] 
    ]

  let renderStepper trigger state = 
    h?div ["class" => "stepper"] [
      let running, step = state.ReplayState
      let dis = if running then ["disabled" => "disabled"] else []
      yield h?div [ "class" => "step" ] [ 
        h?button (dis @ ["click" =!> fun _ _ -> trigger PlayDemo ]) [
          h?i ["class" => "las la-step-forward"] []
        ]
      ]  
      yield h?div [ "class" => "step lastbutton" ] [ 
        h?button (dis @ ["click" =!> fun _ _ -> trigger PlayDemo ]) [
          h?i ["class" => "las la-undo-alt"] []
        ]
      ]
      for i, (g, _) in Seq.indexed state.ReplayEventGroups do
        yield renderStep state step i g
        yield h?div ["class" => "line" ] []         
      yield renderStep state step state.ReplayEventGroups.Length "done"
    ]

  let render triggerDemo stateDemo = 
    let trigger = ApplicationEvent >> triggerDemo
    let state = stateDemo.ApplicationState
    h?div [] [
      h?div [ "class" => "loc" ] (Webnicek.View.renderLocationInfo state)    
      h?div [ "class" => "main" ] [
        yield h?div [ "class" => "doc" ] [
          let doc = state.DocumentState.CurrentDocument // TODO: Restore... Matcher.applyMatchers state.CurrentDocument 
          yield Webnicek.Document.renderDocument state trigger doc
        ]
        yield! Webnicek.Commands.renderContext state trigger
        yield! Webnicek.History.renderHistory trigger state
      ]
      renderStepper triggerDemo stateDemo
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
    |> List.groupByMarker "start" (function 
      | Webnicek.DemoEvent(Webnicek.DefineMarker m) -> Some(m.Trim()) | _ -> None)
    |> List.map (fun (k, g) -> 
        let evts = 
          dropMarkers g 
          |> List.scan (fun prev e -> Some { Event = e; Timeout = getTimeout prev e }) None
          |> List.choose id
        k, evts)
    

  open Fable.Core.JsInterop

  let update (state:DemoState) trigger evt = 
    match evt with 
    | UpdateReplayState(running, g) ->
        { state with ReplayState = (running, g) }

    | PlayDemo when not (fst state.ReplayState) ->
        let _, step = state.ReplayState
        async {   
          if step < state.ReplayEventGroups.Length then
            let g, es = state.ReplayEventGroups.[step]
            let stepEl = Browser.Dom.document.getElementById(state.DemoId + "-" + g)
            let speed = "100" // TESTING stepEl?dataset?speed
            let speed = match System.Double.TryParse(speed) with true, f -> f | _ -> 1.0
            for j, e in Seq.indexed es do 
              do! Async.Sleep(int (float e.Timeout / speed))
              trigger (ApplicationEvent e.Event)
            trigger (UpdateReplayState(false, step + 1))
        } |> Async.Start
        { state with ReplayState = (true, step) }

    | PlayDemo -> state

    | ApplicationEvent evt ->
        let nst = Webnicek.update state.ApplicationState (ApplicationEvent >> trigger) evt
        { state with ApplicationState = nst }  
    
  let findDemos () =
    let demos = Browser.Dom.document.getElementsByClassName("demo")
    [ for i in 0 .. demos.length - 1 -> demos.[i].id, demos.[i]?dataset?file ]

  let start () = Webnicek.Loader.startWithHandler <| async {
    let! demos = findDemos() |> List.map loadDemo |> Async.Parallel
    for demoId, demoEvents in demos do
      let groups = demoEvents |> List.ofArray |> preprocessReplay
      let initial = 
        { ApplicationState = Webnicek.Loader.fromOperationsList []; 
          ReplayEventGroups = groups; ReplayState = (false, 0); DemoId = demoId }
      let trigger, _, getState = createVirtualDomApp demoId initial render update
      trigger PlayDemo
      Webnicek.Loader.setupHandlers (ApplicationEvent >> trigger) (fun () -> getState().ApplicationState)
      ()
  }

module Loader = 
  let start () =
    WebnicekDemos.start ()
