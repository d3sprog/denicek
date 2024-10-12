#if INTERACTIVE
#load "../src/utils.fs" "../src/parsec.fs" "../src/doc.fs" "../src/demos.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd.Doc
open Tbd.Demos

let merge ops1 ops2 = (mergeHistories { Groups = [ops1] } { Groups = [ops2] }).Groups |> List.collect id 
let apply init ops = applyHistory init { Groups = [ops] }

(*
[<Tests>]
let evalTests =
  testList "evaluation" [    
    test "adding speaker invalidates evaluated results" {
      let doc = opsCore @ opsBudget |> List.fold apply (rcd "root" "div")
      let evalOps = evaluateAll doc |> List.ofSeq
      let ops1 = merge (opsCore @ opsBudget @ evalOps) (opsCore @ opsBudget @ addSpeakerOps)
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
let mergeTests =
  testList "merging" [    
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

    (*
    test "adding budget merges with refactoring" {
      let ops1 = merge (opsCore @ refactorListOps) (opsCore @ opsBudget)
      let doc1 = apply (rcd "div") ops1
      let ops2 = merge (opsCore @ opsBudget) (opsCore @ refactorListOps)
      let doc2 = apply (rcd "div") ops2
      doc1 |> equals doc2 
    }*)
  ]




