#load "doc.fs" "matcher.fs"
open Tbd.Doc
open Tbd.Matcher

let init =  rcd "root" "div"

let rendered = 
  opsCore @ refactorListOps
  |> List.fold apply init

// NOTE: Root ID does not appear in path

let pat =
  [
    add [] (rcd "head" "thead")
    add [ Field "head" ] (rcd "*" "td")
    add [ Field "head"; Field "*" ] (rcd "*" "x-hole")
    add [ Field "head"; Field "*"; Field "*" ] (rcd "td" "td")
    add [ Field "head"; Field "*"; Field "*"; Field "td" ] (rcd "mq" "marquee")
    add [ Field "head"; Field "*"; Field "*"; Field "td"; Field "mq" ] (rcd "" "x-match")
  ] |> List.fold apply (rcd "*" "table")

let tbl = select [Field "speakers"] rendered |> List.exactlyOne
matches tbl pat
