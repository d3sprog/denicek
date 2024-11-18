module Tbd.Represent
open Tbd.Doc
open Tbd.Patterns

// --------------------------------------------------------------------------------------
// Representing edits as nodes
// --------------------------------------------------------------------------------------
  
let (|Finds|_|) k (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue(k) with true, Primitive(String s) -> Some s | _ -> None
let (|Findrb|_|) (d:System.Collections.Generic.IDictionary<_, Node>) = 
  match d.TryGetValue("refs") with 
  | true, Primitive(String "update") -> Some(UpdateReferences)
  | true, Primitive(String "keep") -> Some(KeepReferences)
  | true, v -> failwith $"Findrb: expected 'update' or 'keep' but got '{v}'"
  | _ -> None
let rcd id kvp = Record(id, kvp)

let representRb = function
  | UpdateReferences -> "refs", Primitive(String "update")
  | KeepReferences -> "refs", Primitive(String "keep")

let representSel sel = 
  List("x-selectors", 
    [ for i, s in Seq.indexed sel ->
        match s with 
        | DotDot -> string i, Primitive(String "..")
        | All -> string i, Primitive(String "*")
        | Index n -> string i, Primitive(String ("#" + n))
        | Field f -> string i, Primitive(String f) ])

let unrepresentSel expr =
  match expr with 
  | List("x-selectors", sels) ->
      sels |> List.map (function 
        | _, Primitive(String "..") -> DotDot
        | _, Primitive(String "*") -> All 
        | _, Primitive(String s) when s.Length > 0 && s.[0] = '#' -> Index(s.Substring(1))
        | _, Primitive(String s) -> Field(s)
        | _ -> failwith "unrepresentSel: Invalid selector")
  | _ -> failwith $"unrepresentSel: Not a selector: {expr}"

let representStringList ns =
  List("x-string-list", [for i, s in Seq.indexed ns -> string i, Primitive(String s) ])

let unrepresentStringList nd =
  match nd with 
  | List("x-string-list", nds) ->
      nds |> List.sortBy (fst >> int) |> List.map (function 
        | _, Primitive(String s) -> s 
        | _ -> failwith "unrepresentStringList - Not a number") 
  | _ -> failwith $"unrepresentIntList - Invalid node {nd}"

let representCond cond = 
  match cond with 
  | EqualsTo(nd) -> [ "node", Primitive nd ] |> rcd "x-cond-equals"
  | NonEmpty -> [] |> rcd "x-cond-nonempty"

let unrepresentCond nd = 
  match nd with 
  | Record("x-cond-equals", Lookup(Find "node" (Primitive v))) -> EqualsTo(v)
  | Record("x-cond-nonempty", []) -> NonEmpty
  | _ -> failwith $"unrepresentCond - Invalid node {nd}"

let unrepresent nd = 
  // NOTE: This works if the 'match' is not wrapped inside another expression (e.g. let) otherwise
  // Fable creates 600MB JavaScript file (https://x.com/tomaspetricek/status/1845753585163731319)
  let ret ed = 
    let res = { Kind = ed; Dependencies = []; GroupLabel = ""; Disabled = false }
    match nd with 
    | Record(_, Lookup (Finds "hash" hash)) -> res, Some (System.Convert.ToInt32(hash, 16))
    | _ -> res, None
  match nd with
  // Value edits
  | Record("x-edit-add", Lookup (Find "target" sel & Finds "field" f & Find "node" nd)) ->
      RecordAdd(unrepresentSel sel, f, nd) |> ret
  | Record("x-edit-primitive", Lookup (Find "target" tgt & Finds "op" op & Finds "arg" arg)) ->
      PrimitiveEdit(unrepresentSel tgt, op, Some arg) |> ret
  | Record("x-edit-primitive", Lookup (Find "target" tgt & Finds "op" op)) ->
      PrimitiveEdit(unrepresentSel tgt, op, None) |> ret
  | Record("x-edit-updatetag", Lookup (Find "target" tgt & Finds "new" ntag)) ->
      UpdateTag(unrepresentSel tgt, ntag) |> ret
  // Shared edits
  | Record("x-edit-append", Lookup (Find "target" sel & Find "node" nd & Finds "index" i)) ->
      ListAppend(unrepresentSel sel, i, nd) |> ret
  | Record("x-edit-appendfrom", Lookup (Find "target" sel & Find "src" src & Finds "index" i)) ->
      ListAppendFrom(unrepresentSel sel, i, unrepresentSel src) |> ret
  | Record("x-edit-wraprec", Lookup(Findrb rb & Finds "tag" tag & Finds "fld" id & Find "target" target)) ->
      WrapRecord(rb, tag, id, unrepresentSel target) |> ret
  | Record("x-edit-renamefld", Lookup (Findrb rb & Find "target" sel & Finds "old" fold & Finds "new" fnew)) ->
      RecordRenameField(rb, unrepresentSel sel, fold, fnew) |> ret
  | Record("x-edit-copy", Lookup (Findrb rb & Find "target" tgt & Find "source" src)) ->
      Copy(rb, unrepresentSel tgt, unrepresentSel src) |> ret
  | Record("x-edit-listdelete", Lookup (Find "target" tgt & Finds "index" i)) ->
      ListDelete(unrepresentSel tgt, i) |> ret
  | Record("x-edit-recdelete", Lookup (Findrb rb & Find "target" tgt & Finds "field" fld)) ->
      RecordDelete(rb, unrepresentSel tgt, fld) |> ret
  | Record("x-edit-wraplist", Lookup (Findrb rb & Find "target" tgt & Finds "tag" tag & Finds "index" i)) ->
      WrapList(rb, tag, i, unrepresentSel tgt) |> ret
  | Record("x-edit-listreorder", Lookup (Find "target" tgt & Find "perm" perm)) ->
      ListReorder(unrepresentSel tgt, unrepresentStringList perm) |> ret
  | _ -> failwith $"unrepresent - Missing case for: {nd}"

let represent (hash:int option) op = 
  let ps v = Primitive(String v)
  let pn i = Primitive(Number i)
  let rcd k args = 
    match hash with 
    | Some hash -> rcd k (args @ ["hash", ps (hash.ToString("x"))])
    | None -> rcd k args
  match op.Kind with 
  // Value edits
  | RecordAdd(target, f, nd) ->
      rcd "x-edit-add" [ "target", representSel target; "field", ps f; "node", nd ]
  | PrimitiveEdit(target, op, None) ->
      rcd "x-edit-primitive" [ "target", representSel target; "op", ps op ]
  | PrimitiveEdit(target, op, Some arg) ->
      rcd "x-edit-primitive" [ "target", representSel target; "op", ps op; "arg", ps arg ]
  | UpdateTag(target, ntag) ->
      rcd "x-edit-updatetag" [ "target", representSel target; "new", ps ntag ]
  | ListAppend(target, n, nd) ->
      rcd "x-edit-append" [ "target", representSel target; "node", nd; "index", ps n ]
  | ListAppendFrom(target, n, src) ->
      rcd "x-edit-appendfrom" [ "target", representSel target; "src", representSel src; "index", ps n ]
  | ListDelete(target, i) ->
      rcd "x-edit-listdelete" [ "target", representSel target; "index", ps i ]
  | ListReorder(target, perm) ->
      rcd "x-edit-listreorder" [ "target", representSel target; "perm", representStringList perm ]
  // Structural edits
  | WrapRecord(rb, tag, id, target) ->
      rcd "x-edit-wraprec" [ "tag", ps tag; "fld", ps id; "target", representSel target; representRb rb ] 
  | RecordRenameField(rb, target, fold, fnew) ->
      rcd "x-edit-renamefld" [ "target", representSel target; "old", ps fold; "new", ps fnew; representRb rb ]
  | Copy(rb, target, source) ->
      rcd "x-edit-copy" [ "target", representSel target; "source", representSel source; representRb rb ]
  | RecordDelete(rb, target, fld) ->
      rcd "x-edit-recdelete" [ "target", representSel target; representRb rb; "field", ps fld ]
  | WrapList(rb, tag, n, target) ->
      rcd "x-edit-wraplist" [ "target", representSel target; "tag", ps tag; "index", ps n; representRb rb ]
