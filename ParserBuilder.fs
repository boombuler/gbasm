﻿module ParserBuilder

open System;

type Position = {
    line : int
    column : int
}

type InputState = {
    lines : string[]
    position : Position 
}

let private initialPos = {line=0; column=0}

/// increment the column number
let private incrCol pos = 
    {pos with column=pos.column + 1}

/// increment the line number and set the column to 0
let private incrLine pos = 
    {line=pos.line + 1; column=0}

let fromStr str = 
    if String.IsNullOrEmpty(str) then
        {lines=[||]; position=initialPos}
    else
        let separators = [| "\r\n"; "\n" |]
        let lines = str.Split(separators, StringSplitOptions.None)
        {lines=lines; position=initialPos}

let private nextChar input =
    let linePos = input.position.line
    let colPos = input.position.column
    // three cases
    // 1) if line >= maxLine -> 
    // return EOF
    // 2) if col less than line length -> 
    // return char at colPos, increment colPos
    // 3) if col at line length -> 
    // return NewLine, increment linePos

    if linePos >= input.lines.Length then
        input, None
    else
        let currentLine = input.lines.[linePos]
        if colPos < currentLine.Length then
            let char = currentLine.[colPos]
            let newPos = incrCol input.position 
            let newState = {input with position=newPos}
            newState, Some char
        else 
            // end of line, so return LF and move to next line
            let newPos = incrLine input.position 
            if newPos.line < input.lines.Length then
                let char = '\n'
                let newState = {input with position=newPos}
                newState, Some char
            else 
                input, None

type ParserLabel = string
type ParserError = (ParserLabel*string*Position)

type Parser<'a, 'state> = {
    fn : (('state*InputState) -> Result<'a * ('state * InputState), ParserError>)
    label:  ParserLabel 
}

let EOF =
    let label = "EOF"
    let innerFn (s, input) =
        match nextChar input with
        | state, None -> Ok ((), (s, state))
        | _, Some ch ->     
            let err = sprintf "Unexpected '%c' expected EOF" ch
            Error (label,err, input.position)
    {fn=innerFn;label=label}

let satisfy predicate label =
    let innerFn (s, input) =
        match nextChar input with
        | _, None -> Error (label,"No more input", input.position)
        | newState, Some ch ->     
            if predicate ch then
                Ok (ch,(s, newState))
            else
                let err = sprintf "Unexpected '%c'" ch
                Error (label,err, input.position)
    {fn=innerFn;label=label}

let setLabel parser newLabel = 
    // change the inner function to use the new label
    let newInnerFn input = 
        let result = parser.fn input
        match result with
        | Ok s -> Ok s 
        | Error (_,err, pos) -> Error (newLabel,err, pos)
    {fn=newInnerFn; label=newLabel}
let ( <?> ) = setLabel

let run<'a, 's> (parser: Parser<'a,'s>) (input:('s*InputState)) =
    parser.fn input

let pChar expectedChar =
    let predicate ch = (ch = expectedChar) 
    let label = sprintf "%c" expectedChar 
    satisfy predicate label 

let private orParse parser1 parser2 =
    let label = sprintf "%s or %s" parser1.label parser2.label
    let innerParser inputChars =
        match run parser1 inputChars with
        | Ok result -> Ok result
        | Error (l1, e1, p1) -> 
            match run parser2 inputChars with
            | Ok result -> Ok result
            | Error (l2, e2, p2) ->
                if (p1.line > p2.line) || ((p1.line = p2.line) && (p1.column > p2.column)) then
                    Error (l1, e1, p1)
                else
                    Error (l2, e2, p2)
    {fn = innerParser; label = label}
let ( <|> ) = orParse

let private andParse parser1 parser2 = 
    let label = sprintf "%s and %s" parser1.label parser2.label
    let innerParser inputChars =
        match run parser1 inputChars with
        | Error msg -> Error msg
        | Ok (c1, remaining1) ->
            match run parser2 remaining1 with
            | Error msg -> Error msg
            | Ok (c2, remaining2) ->
                Ok ((c1, c2), remaining2)
    {fn=innerParser; label=label}
let ( .>>. ) = andParse

let terminatedList p1 p2 =
    let label = sprintf "multiple %s and then %s" p1.label p2.label
    let rec parseLoop resultSoFar inputChars =
        match run p1 inputChars with
        | Ok (result, rest) -> parseLoop (result::resultSoFar) rest
        | Error e -> 
            match run p2 inputChars with
            | Ok _ ->  Ok ((resultSoFar |> List.rev), inputChars)
            | Error _ -> Error e
    let innerParser = parseLoop []
    {fn=innerParser; label=label}
let ( *>>! ) = terminatedList

let mapState<'a,'b,'s> (mapFunc :('a*'s)->('b*'s)) (parser:Parser<'a, 's>) =
    let innerParser inputChars =
        match run parser inputChars with
        | Error msg -> Error msg
        | Ok (result, (s, re)) ->
            let (result, s) = mapFunc (result, s)
            Ok (result, (s, re))
    {fn=innerParser; label=parser.label}
let (|!>) p m = mapState m p

let map mapFunc parser =
    let innerParser inputChars =
        match run parser inputChars with
        | Error msg -> Error msg
        | Ok (result, remaining) ->
            Ok (mapFunc result, remaining)
    {fn=innerParser; label=parser.label}
let (|>>) p m = map m p




let (.>>) p1 p2 = 
    p1 .>>. p2 
    |>> fun (a,b) -> a

let (>>.) p1 p2 = 
    p1 .>>. p2 
    |>> fun (a,b) -> b

let apply funcAsParser paramAsParser =
    (funcAsParser .>>. paramAsParser)
    |>> fun (f, x) -> f x
let ( <*> ) = apply

let returnAsParser result =
    let label = sprintf "%A" result
    let innerParser inputChars =
        Ok (result, inputChars)
    {fn=innerParser; label=label}

let lift2 funcToLift paramAsParser1 paramAsParser2 =
    returnAsParser funcToLift <*> paramAsParser1 <*> paramAsParser2

let rec sequenceParsers parserList =
    let cons head rest = head :: rest
    let consAsParser = lift2 cons

    match parserList with
    | [] -> returnAsParser []
    | parser :: remainingParsers ->
        consAsParser parser (sequenceParsers remainingParsers)

let anyCharOf chars = chars |> List.map pChar |> List.reduce orParse

let opt parser fallback =
    let label = sprintf "optional %s" parser.label
    let innerParser inputChars = 
        match run parser inputChars with
        | Ok (result, rest) -> Ok (result, rest)
        | Error _ -> Ok (fallback, inputChars)
    {fn=innerParser; label=label}

let many parser =
    let label = sprintf "many %s" parser.label
    let rec parseLoop resultSoFar inputChars =
        match run parser inputChars with
        | Ok (result, rest) -> parseLoop (result::resultSoFar) rest
        | Error _ -> Ok ((resultSoFar|> List.rev), inputChars)
    let innerParser = parseLoop []
    {fn=innerParser; label=label}

let many1 parser =
    let label = sprintf "many %s but at least one" parser.label
    let innerParser input =
        match run (many parser) input with
        | Ok (list, remaining) -> 
            match list with 
            | [] -> 
                let (_, input) = input
                Error (label, "At least one element expected", input.position)
            | _ -> Ok (list, remaining)
        | Error (l, e, p) -> Error (l, e, p)
    {fn=innerParser; label=label}

let private pStringCore<'s> (pc: char->Parser<char, 's>) str =
    let charsToStr chars = System.String(List.toArray chars)
    let strToChars str = List.ofSeq str

    str
    |> strToChars
    |> List.map pc
    |> sequenceParsers
    |>> charsToStr
    <?> str


let pString<'s> = pStringCore<'s> pChar

let pCharCI c = 
    pChar (Char.ToLower(c)) <|> pChar (Char.ToUpper(c))

let pStringCI<'s> = pStringCore<'s> pCharCI

let testValue<'a, 's> (parser: Parser<'a,'s>) (test : 'a->string option) : Parser<'a,'s> =
    // change the inner function to use the new label
    let newInnerFn input = 
        let result = parser.fn input
        match result with
        | Ok (s, is) -> 
            match test s with
            | None -> Ok (s, is)
            | Some err -> 
                let (_, input) = input
                Error (parser.label, err, input.position)
        | Error e -> Error e
    {parser with fn=newInnerFn}

let (|?>) = testValue
