#if INTERACTIVE
#load "../src/doc.fs"
let equals a b = a = b
#else
module Tbd.Tests
open Expecto
let equals a b = Expect.equal a b "Should equal"
#endif
open Tbd.Doc

let evaluate = List.fold apply (rcd "root" "div")

[<Tests>]
let tests =
  testList "merging" [
    
    test "Indexing merges with reordering" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
      let doc1 = evaluate ops1 
      let ops2 = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
      let doc2 = evaluate ops2 
      doc1 |> equals doc2
    }

    test "Refactoring merges with adding" {
      let ops1 = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
      let doc1 = evaluate ops1 
      let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
      let doc2 = evaluate ops2
      doc1 |> equals doc2
    }
  ]




let tC1() = 
  let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ refactorListOps)
  ops |> List.fold apply (rcd "root" "div")

let tC2() = 
  let ops = merge (opsCore @ refactorListOps) (opsCore @ fixSpeakerNameOps)
  ops |> List.fold apply (rcd "root" "div")

(*
open Fable.Jester
Jest.describe("basic selection works", fun () ->
    Jest.test("select field", fun () ->
        match select [Field "title"] doc with 
        | [{ Expression = Primitive(String s)}] ->
            Jest.expect(s).toEqual("Programming conference 2023")
        | _ -> failwith "expected single primitive string"
    )
)
*)