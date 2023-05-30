#if INTERACTIVE
#load "doc.fs"
#else
module Tbd.Tests
#endif
open Tbd.Doc

let tA1() = 
  let ops = merge (opsCore @ addSpeakerOps) (opsCore @ fixSpeakerNameOps)
  ops |> List.fold apply (rcd "root" "div")

let tA2() = 
  let ops = merge (opsCore @ fixSpeakerNameOps) (opsCore @ addSpeakerOps)
  ops |> List.fold apply (rcd "root" "div")

tA1() = tA2()
|> ignore



let tB1() = 
  let ops = merge (opsCore @ addSpeakerOps) (opsCore @ refactorListOps)
  ops |> List.fold apply (rcd "root" "div")

let tB2() = 
  let ops = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 
  ops |> List.fold apply (rcd "root" "div")



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