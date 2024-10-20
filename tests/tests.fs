#if INTERACTIVE
#nowarn "3353"
#I "../src"
#load "utils.fs" "parsec.fs" "doc.fs" "represent.fs" "demos.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd.Doc
open Tbd.Demos

let apply init ops = applyHistory init ops
let printEdits = List.iter (formatEdit >> printfn " - %s")

(*
[<Tests>]
let evalTests =
  testList "evaluation" [    
    test "adding speaker invalidates evaluated results" {
      let doc = opsCore @ opsBudget |> List.fold apply (rcd "root" "div")
      let evalOps = evaluateAll doc |> List.ofSeq
      let ops1 = mergeHistories (opsCore @ opsBudget @ evalOps) (opsCore @ opsBudget @ addSpeakerOps)
      let postEvalOps = evaluateAll (applyAll ops1) |> List.ofSeq

      let r1 = applyAll (opsCore @ opsBudget @ evalOps) |> select [Field "ultimate"; Field "item"]
      match r1 with [{ Expression = Primitive(Number n) }] -> equals n 3500.0 | _ -> failtest "Expected primitive result" 
      
      let r2 = applyAll ops1 |> select [Field "ultimate"; Field "item"]
      match r2 with [{ Expression = Record(_, Apply, _) }] -> () | _ -> failtest "Expected unevaluated record"

      let r3 = applyAll (ops1 @ postEvalOps) |> select [Field "ultimate"; Field "item"]
      match r3 with [{ Expression = Primitive(Number n) }] -> equals n 4500.0 | _ -> failtest "Expected primitive result" 
    }
  ]
*)
(*
[<Tests>]
let tests =
  testList "interaction" [    
    test "counter can increment state" {
      let ops1 = opsBaseCounter 
      let doc1 = applyAll ops1
      select [Field "counter"; Field "value"] doc1 |> equals [ Primitive(Number 0.0) ]
      
      let ops2 = ops1 @ opsCounterInc
      let doc2 = applyAll ops2
      let ops3 = ops2 @ evaluateDoc doc2
      let doc3 = applyAll ops3
      select [Field "counter"; Field "value"] doc3 |> equals [ Primitive(Number 1.0) ]

      let ops4 = ops3 @ opsCounterInc
      let doc4 = applyAll ops4
      let ops5 = ops4 @ evaluateDoc doc4
      let doc5 = applyAll ops5
      select [Field "counter"; Field "value"] doc5 |> equals [ Primitive(Number 2.0) ]
    }
  ]
  *)
[<Tests>]
let basicmergeHistoriesTests =
  testList "basic merging" [
    test "mergeHistories rename" {
      let ops1 = [ uidS [Field "test"] "f1" "f2" ]
      let ops2 = [ uidS [Field "test"] "f1" "f3" ]
      mergeHistories ops1 ops2 |> equals [ uidS [Field "test"] "f1" "f2"; uidS [Field "test"] "f2" "f3" ]
      mergeHistories ops2 ops1 |> equals [ uidS [Field "test"] "f1" "f3"; uidS [Field "test"] "f3" "f2" ]
    }
  ]

[<Tests>]
let complexmergeHistoriesTests =
  testList "complex merging" [    
    test "indexing mergeHistoriess with reordering" {
      let ops1 = mergeHistories (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = mergeHistories (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = apply (rcd "div") ops2 
      doc1 |> equals doc2
    }

    test "refactoring mergeHistoriess with adding" {
      let ops1 = mergeHistories (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = mergeHistories (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "refactoring mergeHistoriess with name fix" {
      let ops1 = mergeHistories (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = mergeHistories (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
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

    test "refactoring mergeHistoriess with adding via temp" {
      let ops1 = mergeHistories (opsCore @ addSpeakerViaTempOps) (opsCore @ refactorListOps)
      let doc1 = apply (rcd "div") ops1 
      let ops2 = mergeHistories (opsCore @ refactorListOps) (opsCore @ addSpeakerViaTempOps) 
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2
    }

    test "refactoring mergeHistoriess with adding two speakers by PBD" {
      let pbdCore = opsCore @ pbdAddInput
      let ops1 = mergeHistories (pbdCore @ refactorListOps) (pbdCore @ pbdAddFirstSpeaker @ pbdAddAnotherSpeaker) 
      let doc1 = apply (rcd "div") ops1 
      let ops2 = mergeHistories (pbdCore @ pbdAddFirstSpeaker @ refactorListOps) (pbdCore @ pbdAddAnotherSpeaker)
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2
    }

    (*
    test "adding budget mergeHistoriess with refactoring" {
      let ops1 = mergeHistories (opsCore @ refactorListOps) (opsCore @ opsBudget)
      let doc1 = apply (rcd "div") ops1
      let ops2 = mergeHistories (opsCore @ opsBudget) (opsCore @ refactorListOps)
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2 
    }*)
  ]




