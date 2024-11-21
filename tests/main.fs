module Tbd.TestRunner
open Expecto
open Tbd.Tests
open Tbd.Demos

[<EntryPoint>]
let main argv =
    Tests.runTestsInAssemblyWithCLIArgs [] argv

    //Tests.runTestsWithCLIArgs [] argv referenceUpdateTests

    //let ops2 = merge (opsCore @ refactorListOps) (opsCore @ addSpeakerOps) 

    //0
