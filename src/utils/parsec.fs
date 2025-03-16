module Denicek.Parsec

// --------------------------------------------------------------------------------------
// Parser that can return partial match. If the start of the input can be parsed, this
// returns a "template" showing how the rest of the input should look in order to be
// fully parsed (used in the toolbox, to show completions)
// --------------------------------------------------------------------------------------

type Template = 
  | Fixed of string
  | Append of Template list
  | Hole of string
  | Repeat of Template * string
  | Empty 

type ParseResult<'T> = 
  | Parsed of 'T * char list 
  | Partial of Template
  | Failed

type Parser<'T> = Parser of (char list option -> ParseResult<'T>)

// --------------------------------------------------------------------------------------
// Parser primitives
// --------------------------------------------------------------------------------------

module P = 

  let simplify t = 
    let flatten ts = 
      ts |> List.collect (function Empty -> [] | Append(l) -> l | t -> [t])
    let rec concat accs acc ts = 
      match ts with 
      | Fixed(s)::ts -> concat (accs + s) acc ts
      | t::ts when accs.Length > 0 -> concat "" (t::Fixed(accs)::acc) ts
      | t::ts -> concat "" (t::acc) ts
      | [] when accs.Length > 0 -> List.rev (Fixed(accs)::acc)
      | [] -> List.rev acc
    match t with 
    | Append ts -> Append(concat "" [] (flatten ts))
    | _ -> t

  let pred t f = Parser(fun cs ->
    match cs with 
    | Some(c::cs) when f c -> Parsed(c, cs)
    | Some(_::_) -> Failed
    | Some [] | None -> Partial(t))

  let any = pred (Fixed "?") (fun _ -> true)
  let char c = pred (Fixed (string c)) ((=) c)
  let nonTagChar = pred (Fixed "?") (fun c -> c <> '<' && c <> '[' && c <> ']' && c <> '>')
  let nonSlashChar = pred (Fixed "?") (fun c -> c <> '/')

  let getTemplateRaw p = 
    match p None with Partial t -> t | _ -> failwith "getTemplate: Expected partial"
  let getTemplate (Parser p) = 
    getTemplateRaw p

  let orElse (Parser p1) (Parser p2) = Parser(fun cs ->
    match p1 cs with 
    | Parsed(r, cs) -> Parsed(r, cs)
    | Partial(t) ->
        match p2 cs with 
        | Parsed(r, cs) -> Parsed(r, cs)
        | _ -> Partial(t)
    | _ -> p2 cs )

  let andThen (Parser p1) (Parser p2) = Parser(fun cs -> 
    printfn $"P1={p1 cs}"
    match p1 cs with 
    | Parsed(r1, cs) ->
        match p2 (Some cs) with 
        | Parsed(r2, cs) -> Parsed((r1, r2), cs)
        | Partial(t) -> Partial(t)
        | Failed -> Failed
    | Partial(t1) -> 
        let t2 = getTemplateRaw p2
        Partial(simplify(Append [t1; t2]))
    | Failed -> Failed)

  let unit v = Parser(fun cs ->
    match cs with 
    | None -> Partial(Empty)
    | Some(cs) -> Parsed(v, cs))

  let mapRaw f (Parser p) = Parser(fun cs -> 
    match p cs with 
    | Parsed(r, cs) -> f r cs
    | Partial(t) -> Partial(t)
    | Failed -> Failed )

  let map f = mapRaw (fun r cs -> Parsed(f r, cs))

  let zeroOrMore (Parser p) = Parser(fun cs -> 
    let rec loop acc cs =
      match p (Some cs) with 
      | Partial _ | Failed -> Parsed(List.rev acc, cs)
      | Parsed(r, cs) -> loop (r::acc) cs
    match cs with 
    | None -> Partial(Repeat(getTemplateRaw p, "*"))
    | Some cs -> loop [] cs )

  let oneOrMore ((Parser pf) as p) = 
    zeroOrMore p |> mapRaw (fun r cs ->
      match r, cs with 
      | [], [] -> Partial(Repeat(getTemplate p, "+"))
      | [], cs -> 
          match pf (Some cs) with 
          | Parsed _ -> failwith "oneOrMore - should not happen"
          | Partial t -> Partial t
          | Failed -> Failed
      | _ -> Parsed(r, cs))

  let oneOrMoreEnd ((Parser pf) as p) = 
    zeroOrMore p |> mapRaw (fun r cs ->
      match r, cs with 
      | [], [] -> Partial(Repeat(getTemplate p, "+"))
      | r, [] -> Parsed(r, [])
      | _, cs -> 
          match pf (Some cs) with 
          | Parsed _ -> failwith "oneOrMore - should not happen"
          | Partial t -> Partial t
          | Failed -> Failed )

  let alphaNumeric =
    pred (Fixed "a") (fun c -> System.Char.IsLetterOrDigit(c))

  let letter =
    pred (Fixed "a") (fun c -> System.Char.IsLetter(c))

  let number =
    pred (Fixed "0") (fun c -> System.Char.IsNumber(c))

  let keyword s = 
    let rec loop cs = 
      match cs with 
      | [] -> unit []
      | c::cs -> andThen (char c) (loop cs) |> map (fun (v, vs) -> v::vs)
    loop (List.ofSeq s) |> map (fun _ -> s)

  let hole t (Parser p) = Parser(fun cs ->
    match p cs with 
    | Partial _ -> Partial(Hole t)
    | r -> r)

  let identChar = 
    orElse (orElse alphaNumeric (char '-')) (char '_')
  let ident = 
    oneOrMore identChar |> map (fun cs -> System.String(Array.ofSeq (cs)))
  let atIdent = 
    andThen (char '@') (zeroOrMore identChar) |> map (fun (c,cs) -> System.String(Array.ofSeq (c::cs)))
  let dollarIdent = 
    andThen (char '$') (zeroOrMore identChar) |> map (fun (c,cs) -> System.String(Array.ofSeq (c::cs)))

  let num = 
    oneOrMore number |> map (fun cs -> int(System.String(Array.ofSeq cs)))

  let nonTag = 
    oneOrMore nonTagChar |> map (fun cs -> System.String(Array.ofSeq cs))

  let nonSlash = 
    oneOrMore nonSlashChar |> map (fun cs -> System.String(Array.ofSeq cs))

  let str = 
    oneOrMore any |> map (fun cs -> System.String(Array.ofSeq cs))

  let run (Parser p) (s:string) = 
    p (Some (List.ofSeq s))

// --------------------------------------------------------------------------------------
// Operators
// --------------------------------------------------------------------------------------

module Operators = 
  open P
  
  let (<|>) p1 p2 = orElse p1 p2
  let (<*>) p1 p2 = andThen p1 p2
  let (<<*>) p1 p2 = andThen p1 p2 |> map fst
  let (<*>>) p1 p2 = andThen p1 p2 |> map snd
