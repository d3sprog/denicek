#if INTERACTIVE
#nowarn "3353"
#I "../src"
#load "utils.fs" "parsec.fs" "doc.fs" "represent.fs" "eval.fs" "demos.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd
open Tbd.Doc
open Tbd.Demos

let apply init ops = applyHistory init ops
let merge h1 h2 = mergeHistories IgnoreConflicts h1 h2 |> fst
let printEdits = List.iter (formatEdit >> printfn " - %s")
let selectTag sel doc = match select sel doc with [List(t, _)] | [Record(t, _)] -> Some t | _ -> None 

[<Tests>]
let evalTests =
  testList "interaction and evaluation" [    

    test "incrementing counter invalidates evalauted result" {
      let doc1 = applyHistory (rcd "div") (opsBaseCounter @ opsCounterInc)
      let evalOps = Eval.evaluateAll doc1
      let doc2 = applyHistory (rcd "div") (opsBaseCounter @ opsCounterInc @ evalOps)

      let mergedOps, _ = 
        mergeHistories RemoveConflicting 
          (opsBaseCounter @ opsCounterInc @ opsCounterInc) 
          (opsBaseCounter @ opsCounterInc @ evalOps)
      let doc3 = applyHistory (rcd "div") mergedOps

      doc2 |> selectTag (!/"/counter/value") |> equals (Some "x-evaluated")
      doc2 |> select (!/"/counter/value/result") |> equals [Primitive(Number 1.0)]

      doc3 |> selectTag (!/"/counter/value") |> equals (Some "x-formula")
      doc3 |> select (!/"/counter/value/result") |> equals []
    }

    test "adding speaker invalidates evaluated results" {
      let doc1 = applyHistory (rcd "div") (opsCore @ opsBudget)
      let evalOps = Eval.evaluateAll doc1
      let doc2 = applyHistory (rcd "div") (opsCore @ opsBudget @ evalOps)

      let mergedOps, _ = 
        mergeHistories RemoveConflicting 
          (opsCore @ opsBudget @ addSpeakerOps) 
          (opsCore @ opsBudget @ evalOps)
      let doc3 = applyHistory (rcd "div") mergedOps

      doc2 |> selectTag (!/"/ultimate/item") |> equals (Some "x-evaluated")
      doc2 |> select (!/"/ultimate/item/result") |> equals [Primitive(Number 3500.0)]
      doc3 |> selectTag (!/"/ultimate/item") |> equals (Some "x-formula")
      doc3 |> select (!/"/ultimate/item/result") |> equals []
    }

    // This is straightforwardly adding the wrapping interactions to the end of the list
    // (i.e. as if you were always doing this by hand repeatedly)
    test "counter can increment state" {
      let ops1 = opsBaseCounter 
      let doc1 = apply (rcd "div") ops1
      select [Field "counter"; Field "value"] doc1 |> equals [ Primitive(Number 0.0) ]
      
      let ops2 = ops1 @ opsCounterInc
      let doc2 = apply (rcd "div") ops2
      let ops3 = ops2 @ Eval.evaluateOne doc2
      let doc3 = apply (rcd "div") ops3
      select [Field "counter"; Field "value"; Field "result"] doc3 |> equals [ Primitive(Number 1.0) ]

      let ops4 = ops3 @ opsCounterInc
      let doc4 = apply (rcd "div") ops4
      let ops5 = ops4 @ Eval.evaluateOne doc4
      let doc5 = apply (rcd "div") ops5
      select [Field "counter"; Field "value"; Field "result"] doc5 |> equals [ Primitive(Number 2.0) ]
    }

    // A more interesting case is when we 'replay' past interactions, because then they are
    // appended onto a base (when they were saved) and are merged with current state
    // (clicking the 'Inc' button twice, merges the current ops with base @ replay twice)
    test "counter can merge increment operations" {
      let currentOps = opsBaseCounter @ opsCounterInc @ opsCounterHndl (opsBaseCounter @ opsCounterInc)
      let currentOps, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps (opsBaseCounter @ opsCounterInc @ opsCounterInc)
      let currentOps, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps (opsBaseCounter @ opsCounterInc @ opsCounterInc)

      let docUnevaluated = apply (rcd "div") currentOps
      let opsEvaluated = currentOps @ Eval.evaluateAll docUnevaluated
      let docEvaluated = apply (rcd "div") opsEvaluated
      select [Field "counter"; Field "value"; Field "result"] docEvaluated |> equals [ Primitive(Number 3.0) ]
    }

    // Even more elaborate case where we click, evaluate, click again, re-evaluate
    test "counter can invalidate after reevaluating" {
      let currentOps = 
        opsBaseCounter @ opsCounterInc @ opsCounterHndl (opsBaseCounter @ opsCounterInc)      
      let currentOps, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps (opsBaseCounter @ opsCounterInc @ opsCounterInc)
      let currentDoc = apply (rcd "div") currentOps
      
      let evalOps = Eval.evaluateAll currentDoc
      let evalHash = hashEditList 0 currentOps
      let currentDoc = apply (rcd "div") (currentOps @ evalOps)
      select (!/"/counter/value/result") currentDoc |> equals [Primitive(Number 2.0)]

      let currentOps, _ = 
        mergeHistories ConflictResolution.IgnoreConflicts
          currentOps (opsBaseCounter @ opsCounterInc @ opsCounterInc)
      let displayOps = Eval.updateDisplayEdits evalHash currentOps evalOps
      let currentDoc = apply (rcd "div") displayOps
      
      let evalOpsMore = Eval.evaluateAll currentDoc
      let finalDoc = apply (rcd "div") (displayOps @ evalOpsMore)
      select (!/"/counter/value/result") finalDoc |> equals [Primitive(Number 3.0)]
    }
  ]

  
[<Tests>]
let basicmergeTests =
  testList "basic merging" [
    test "merge rename" {
      let ops1 = [ uidS [Field "test"] "f1" "f2" ]
      let ops2 = [ uidS [Field "test"] "f1" "f3" ]
      merge ops1 ops2 |> equals [ uidS [Field "test"] "f1" "f2"; uidS [Field "test"] "f2" "f3" ]
      merge ops2 ops1 |> equals [ uidS [Field "test"] "f1" "f3"; uidS [Field "test"] "f3" "f2" ]
    }
  ]

[<Tests>]
let complexmergeTests =
  testList "complex merging" [    
    test "indexing merges with reordering" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = apply (rcd "div") ops2 
      doc1 |> equals doc2
    }

    test "refactoring merges with adding" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with name fix" {
      let ops1 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
      let doc2 = apply (rcd "div") ops2 
      doc1 |> equals doc2 
    }

    test "adding speaker directly and via temp is the same" {
      let ops1 = opsCore @ addSpeakerViaTempOps 
      let doc1 = apply (rcd "div") ops1 
      let ops2 = opsCore @ addSpeakerOps 
      let doc2 = apply (rcd "div") ops2 
      doc1 |> equals doc2 
    }

    test "refactoring merges with adding via temp" {
      let ops1 = merge (opsCore @ addSpeakerViaTempOps) (opsCore @ refactorListOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerViaTempOps) 
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with adding two speakers by PBD" {
      let pbdCore = opsCore @ pbdAddInput
      let ops1 = merge (pbdCore @ refactorListOps) (pbdCore @ pbdAddFirstSpeaker @ pbdAddAnotherSpeaker) 
      let doc1 = apply (rcd "div") ops1 
      let ops2 = merge (pbdCore @ pbdAddFirstSpeaker @ refactorListOps) (pbdCore @ pbdAddAnotherSpeaker)
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "adding budget merges with refactoring" {
      let ops1 = merge (opsCore @ refactorListOps) (opsCore @ opsBudget)
      let doc1 = apply (rcd "div") ops1
      let ops2 = merge (opsCore @ opsBudget) (opsCore @ refactorListOps)
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2 
    }
  ]




