#if INTERACTIVE
#load "../src/doc.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd.Doc
open Tbd.Demos

let applyAll = List.fold apply (rcd "div")
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

[<Tests>]
let mergeTests =
  testList "merging" [    
    test "indexing merges with reordering" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = applyAll ops1 
      let ops2 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = applyAll ops2 
      doc1 |> equals doc2
    }

    test "refactoring merges with adding" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = applyAll ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = applyAll ops2
      doc1 |> equals doc2
    }

    test "refactoring merges with name fix" {
      let ops1 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
      let doc1 = ops1 |> List.fold apply (rcd "div")
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
      let doc2 = ops2 |> List.fold apply (rcd "div")
      doc1 |> equals doc2 
    }

    test "adding budget merges with refactoring" {
      let ops1 = merge (opsCore @ refactorListOps) (opsCore @ opsBudget)
      let doc1 = ops1 |> List.fold apply (rcd "div")
      let ops2 = merge (opsCore @ opsBudget) (opsCore @ refactorListOps)
      let doc2 = ops2 |> List.fold apply (rcd "div")
      doc1 |> equals doc2 
    }
  ]




