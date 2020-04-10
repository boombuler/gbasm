module AsmParser

open OpCodes
open Cartridge
open ParserBuilder
open System
open Microsoft.FSharp.Reflection
open PatchExpr
open Linker
open System.Text
open System.Text.RegularExpressions

let private charsToStr = List.toArray >> System.String

// Definition of an macro
type Macro = {
    Name: string
    Args: string list
    Body: string
}

// The parser state we carry around while parsing.
type ParserState = {
    Defines: Map<string, Operation list>
    GlobalLabel: string
    Header: CartridgeHeader
    Macros : Map<string, Macro>
}


// convert the macro back to text. Needed for nested macros.
let private macroStr m =
    let args = System.String.Join(", ", List.toArray m.Args)
    sprintf "MACRO %s %s %s MEND" m.Name args m.Body

type GetFileContentRequest = { currentFilePath: string; requestedFileName: string }
type GetFileContentResponse = { filePath: string; content: string }
type GetFileContent = GetFileContentRequest -> Result<GetFileContentResponse, string>

// create a forward parser.
let private forward<'a> (_: Unit) :  (Parser<'a, ParserState> * Parser<'a, ParserState> ref)  =
    let dummyParser : Parser<'a, ParserState> =
        let label = "Dummy"
        let innerParser (_, input) =
            Error (label, "Unfixed Forward Parser", input.position, Fail)
        {fn=innerParser; label=label}
    
    let fRef = ref dummyParser
    let f =
        let innerFn input = 
            run !fRef input 
        {fn=innerFn; label="unknown"}
    (f, fRef)

// tests the parsed value and may return some error message if the test fails
let private Assert test msg v = 
    match test v with
    | true -> None
    | false -> Some msg

// Keyword parser. Keywords are case insensitive return a fixed single value
let private kw str value =
    pStringCI str
    |>> fun _ -> value

// Parses a number. Either decimal or hexadecimal (with $ prefixed)
let private number =
    let digit =  anyCharOf (['0'..'9'] )
    let hexdigit = anyCharOf (['0'..'9'] @ ['A'..'F'] @ ['a'..'f'])
    let bindigit = anyCharOf(['0'..'1'])

    let underscore = many (pChar '_')
    let ignUnderscore p = underscore >>. p .>> underscore

    let decimal = 
        many1 (ignUnderscore digit)
        |>> charsToStr
        |>> Int32.Parse
    let hexDec =
        ((pChar '$') >>. many1 (ignUnderscore (hexdigit)))
        |>> charsToStr
        |>> fun s -> Convert.ToInt32(s, 16)
    let bin =
        ((pStringCI "0b") >>. many1 (ignUnderscore bindigit))
        |>> charsToStr
        |>> fun s -> Convert.ToInt32(s, 2)

    (bin <|> decimal <|> hexDec) <?> "number"

// Parses a single whitespace character
let private whitespaceChar = 
    let predicate = Char.IsWhiteSpace 
    let label = "whitespace"
    satisfy predicate label 

// reads many but at least one whitespace character.
let ws = 
    many1 whitespaceChar
    |>> ignore
    <?> "whitespace"

// parses comments, from ';' to the end of the line.
let lineComment = 
    (pChar ';') >>. many (satisfy (fun c -> c <> '\r' && c <> '\n') "Any")
    |>> ignore
    <?> "Comment"

// parses an identifier. Identifiers start with a letter or underscores and continue with letters or digits or underscores.
let private Identifier = 
    let underscore = pChar '_'
    let alpha = (satisfy Char.IsLetter "Letter") <|> underscore
    let alphaNum = (satisfy Char.IsLetterOrDigit "Letter or Digit") <|> underscore

    alpha .>>. (many alphaNum) 
    |>> fun (c, chars) -> System.String(c::chars |> List.toArray)
    <?> "Identifier"

// parses a local, global or fully qualified label name.
let private Label = 
    let localSymbol : Parser<SymbolName, ParserState> = 
        (pChar '.') >>. Identifier
        |!> fun (local, s)  -> { Global = s.GlobalLabel; Local = Some local }, s

    let qualifiedSymbol : Parser<SymbolName, ParserState> =
        Identifier .>> (pChar '.') .>>. Identifier
        |!> fun ((glob, l), s) -> {Global = glob; Local = Some l }, s

    let globalSymbol : Parser<SymbolName, ParserState> =
        Identifier
        |!> fun (glob, s) -> { Global = glob; Local = None }, s
    (localSymbol <|> qualifiedSymbol <|> globalSymbol) <?> "Label"

// skips all whitespaces and then invokes the given parser.
let skipWS p = 
    (many whitespaceChar) >>. p
    <?> p.label

// parses a single char surrounded by whitespaces.
let sym s = skipWS (pChar s) .>> (many whitespaceChar)

// parses an linker expression or calculation like 1+2 or HI(GlobalLabel)
let private expr : Parser<Operation list, ParserState> =
    let symbol = 
            Label
            |>> fun s -> SymAdr s
            <|> (kw "@@" CurAdr)
    let define =
        Identifier 
        |!> fun (i, s) -> Map.tryFind i s.Defines, s
        |?> Assert Option.isSome "Constant is not defined."
        |>> Option.defaultValue []

    let number = number |>> fun n -> [Push n]
    let number = number <|> define

    let fnCall fnName param = 
       (pStringCI fnName) .>> sym '(' >>. skipWS param .>> sym ')'
    let bankNo = 
        fnCall "BANK" symbol
        |>> fun s -> [s]

    
    let (func, funcRef) = forward ()
    let (multExpr, multExprRef) = forward ()
    let (addExpr, addExprRef) = forward ()

    let par = sym '(' >>. (skipWS addExpr) .>> sym ')'

    let value = 
        number <|> func <|> bankNo <|> (symbol |>> fun s -> [s]) <|> par

    let makeBinary left right chr (op: Operation) =
             (left .>> sym chr .>>. (skipWS right))
             |>> fun (a, b) -> a @ b @ [ op ]

    let makeMult = makeBinary value multExpr
    let makeAdd = makeBinary multExpr addExpr

    multExprRef :=         
        (makeMult '*' Mult) <|> (makeMult '&' BitAnd) <|> (makeMult '|' BitOr) <|> value

    addExprRef :=
        (makeAdd '+' Add) <|> (makeAdd '-' Sub) <|> multExpr
    
    funcRef := 
        ((fnCall "HI" addExpr) |>> fun x -> x @ [Hi])
        <|>((fnCall "LO" addExpr) |>> fun x -> x @ [Lo])

    addExpr <?> "Value"
 
// parses a word calculation
let private v_word =
    expr 
    |>> fun w -> Word.Calc w
// parses a word value for the assembler
let private val_nn = v_word |>> fun w -> NN w

// parses a byte calculation
let private v_byte = 
    expr 
    |>> fun w -> Byte.Calc w
// parses a byte value for the assembler
let private val_n = v_byte |>> fun b -> N b

// parses a singed byte caluclation
let private v_sbyte needsSign =
    let unsigned = expr |>> fun w -> SByte.Calc w

    let neg_signed = 
        pChar '-' >>. skipWS expr
        |>> (fun sb -> SByte.Calc (((Push 0)::sb)@[Sub]))

    let plus = pChar '+'
    if needsSign then
        neg_signed <|> (plus >>. skipWS unsigned)
    else
        neg_signed <|> ((opt plus '+') >>. skipWS unsigned)
// parses a signed byte value for the assembler
let private val_r needsSign = v_sbyte needsSign |>> fun b -> R b

// erturns the name of the given union.
let private unionName<'a> (itm: 'a) = 
    match FSharpValue.GetUnionFields(itm, typeof<'a>) with
    | case, _ -> case.Name
    | _ -> ""

// create a parser for each value of the given union which are combined by or
let private kwUnions<'a> (items :'a list) =
    items
    |> List.map (fun i -> kw (unionName<'a> i) i)
    |> List.reduce (<|>)

// parses a PUSH or POP opcode
let private op_PUSH_POP =
    let target = kwUnions [BC; DE; HL; AF]

    let push = 
        pStringCI "PUSH" >>. ws >>. must target 
        |>> (fun t -> PUSH t) <?> "PUSH"
    let pop = 
        pStringCI "POP" >>. ws >>. must target 
        |>> (fun t -> POP t) <?> "POP"
    [push; pop]

// parses a dereference of a 16 bit register.
let private derefR16 r = 
    let targetHL = pChar '[' >>. skipWS (kwUnions<Reg16> [r]) .>> sym ']'
    targetHL
    |>> fun a -> Deref (Reg a)
    <?> unionName r
// parses a dereference of the given parser
let private dref<'a> (p: Parser<'a, ParserState>) : Parser<'a, ParserState> =
    pChar '[' >>. skipWS p .>> sym ']'

// parses an single 8 bit register
let private r8 (r: Reg8) =
    kwUnions [r] 
    |>> (fun r -> R8 r)

// parses a single 16 bit register
let private r16 (r: Reg16) =
    kwUnions [r]
    |>> (fun r -> R16 r)

// parses BIT, SET and RES opcodes.
let private op_BIT_SET_RES =
    let num = 
        number
        |?> Assert (fun i -> i >= 0 && i < 8)  "Bit number must between 0 and 7"           
        |>> fun i -> byte i
   
    let targetR8 = 
        kwUnions [A;B;C;D;E;H;L]
        |>> fun x -> R8 x
    let targetHL = derefR16 HL
    let target =  targetR8 <|> targetHL

    [
        ("BIT", fun x -> BIT x)
        ("SET", fun x -> SET x)
        ("RES", fun x -> RES x)
    ]
    |> List.map (fun (s, c) -> (pStringCI s >>. ws >>. must (num .>> sym ',' .>>. skipWS target)) |>> c <?> s)
    
// parses ADC, SBC and SUB opcodes
let private op_ADC_SBC_SUB =
    let targetR8 = 
        kwUnions [A;B;C;D;E;H;L]
        |>> fun x -> R8 x
    let targetHL = derefR16 HL
    let targetNum = val_n
    let target =  targetR8 <|> targetHL <|> targetNum


    let makeParser (str, conv) =
        pStringCI str >>. ws >>. must (pCharCI 'A' >>. sym ',' >>. skipWS target)
        <?> str
        |>> conv
    [
        "ADC", fun x -> ADC (R8 A, x)
        "SBC", fun x -> SBC (R8 A, x)
        "SUB", fun x -> SUB (R8 A, x)
    ]
    |> List.map makeParser

// parses all the shifting opcodes.
let private op_ShiftOps =
    let targetR8 = 
        kwUnions [A;B;C;D;E;H;L]
        |>> fun x -> R8 x
    let targetHL = derefR16 HL
    let target =  targetR8 <|> targetHL

    [
        ("RLC",  fun x -> RLC  x)
        ("RRC",  fun x -> RRC  x)
        ("RL",   fun x -> RL   x)
        ("RR",   fun x -> RR   x)
        ("SLA",  fun x -> SLA  x)
        ("SRA",  fun x -> SRA  x)
        ("SRL",  fun x -> SRL  x)
        ("SWAP", fun x -> SWAP x)
        ("AND",  fun x -> AND x)
        ("OR",   fun x -> OR x)
        ("XOR",  fun x -> XOR x)
        ("CP",   fun x -> CP x)
    ]
    |> List.map (fun (s, c) -> 
        pStringCI s >>. ws >>. must target
        |>> c 
        <?> s
    ) 

// parses the RST opcodes
let private op_RST = 
    let validVector v = List.contains v [0x00; 0x08; 0x10; 0x18; 0x20; 0x28; 0x30; 0x38]
    let vec = 
        number
        |?> Assert validVector "Invalid Vector"
        |>> byte
    pStringCI "RST" >>. ws >>. must vec 
    |>> fun v -> RST v
    <?> "RST"

// parses a jump flag.
let private jumpFlag =
    [
        kw "NZ" Flag.nz
        kw "Z" Flag.z
        kw "NC" Flag.nc
        kw "C" Flag.c
    ]
    |> List.reduce (<|>)

// parses the RET opcode
let private op_RET =
    pStringCI "RET" >>. opt (ws >>. jumpFlag) Flag.Always
    |>> fun f -> RET f

// parses the ADD opcodes
let private op_ADD : Parser<OpCode,ParserState> = 
    let items = 
        [
            kw "HL" (R16 HL), ((kwUnions [BC; DE; HL; SP]) |>> fun r -> R16 r)
            kw "SP" (R16 SP), val_n
            kw "A" (R8 A),    (kwUnions [A; B; C; D; E; H; L] |>> fun r -> R8 r) <|> derefR16 HL <|> val_n
        ]
        |> List.map (fun (t, s) -> t .>> sym ',' .>>. skipWS s)
        |> List.reduce (<|>)

    pStringCI "ADD" >>. ws >>. must items
    <?> "ADD"
    |>> (fun dstSrc -> ADD dstSrc)

// parses the INC and DEC opcodes
let private op_INC_DEC =
    let targets = 
        (kwUnions [BC; DE; HL; SP] |>> fun r -> R16 r)
        <|> (kwUnions [A;B;C;D;E;H;L] |>> fun r -> R8 r)
        <|> (derefR16 HL)

    [
        "INC", fun r -> INC r
        "DEC", fun r -> DEC r
    ]
    |> List.map (fun (kw, c) -> (pStringCI kw >>. ws >>. must targets) <?> kw |>> c)

// parses the CALL opcode
let private op_CALL =
    let jumpFlag = jumpFlag .>> sym ','

    pStringCI "CALL" >>. ws >>. (opt jumpFlag Flag.Always) .>>. skipWS (must v_word)
    |>> fun (f, addr) -> CALL (f, addr)
    <?> "CALL"

// parses the JP opcode
let private op_JP =
    let jumpFlag = jumpFlag .>> sym ','

    let targets = ((derefR16 HL |>> fun r -> (Flag.Always, r)) <|> ((opt jumpFlag Flag.Always) .>>. skipWS val_nn))

    pStringCI "JP" >>. ws >>. must targets
    |>> fun (f, v) -> JP (f, v)
    <?> "JP"

// parses the JR opcode
let private op_JR =
    let jumpFlag = jumpFlag .>> sym ','
    pStringCI "JR" >>. ws >>. (opt jumpFlag Flag.Always) .>>. skipWS (must (v_sbyte false))
    |>> fun (f, v) -> JR (f, v)
    <?> "JR"

// parses the LDH opcode
let private op_LDH =
    let args = 
        [
            dref val_n, r8 A
            r8 A, dref val_n
            r8 A, dref (r8 C)
            dref (r8 C), r8 A
        ]
        |> List.map (fun (t, s) -> t .>> sym ',' .>>. skipWS s)
        |> List.reduce (<|>)

    pStringCI "LDH" >>. ws >>. must args 
    <?> "LDH"
    |>> fun (t, s) -> LDH (t, s)

// parses the LD opcode
let private op_LD = 
    let hlop str =
        let v = Deref (Reg HL)
        dref (pStringCI "HL" >>. (kw str v)) 

    let ld args = LD args
    let drefNN = (dref v_word) |>> fun n -> Deref (Addr n)

    let ldBVals aVal bVals = bVals |> List.map (fun b -> (aVal, b, ld))
    let r8s items = List.map r8 items

    let simpleSrcs = (val_n::(r8s [A;B;C;D;E;H;L]))
    let ldR8Default (regs: Reg8 list) = 
        let bVals = (derefR16 HL)::simpleSrcs         
        regs 
        |> List.map (fun r -> (ldBVals (r8 r) bVals))
        |> List.reduce List.append
    let sp_d = 
        let value = (val_r true)
        dref ((r16 SP) >>. skipWS value)

    let args : Parser<OpCode, ParserState> = 
        (
            [
                hlop "++", r8 A, (fun (a, b) -> LDI (a, b))
                hlop "--", r8 A, (fun (a, b) -> LDD (a, b))
                r8 A, hlop "++", (fun (a, b) -> LDI (a, b))
                r8 A, hlop "--", (fun (a, b) -> LDD (a, b))
                r8 A,           drefNN,         ld
                r8 A,           derefR16 BC,    ld
                r8 A,           derefR16 DE,    ld
                r16 BC,         val_nn,         ld
                r16 DE,         val_nn,         ld
                r16 HL,         val_nn,         ld
                r16 HL,         sp_d,           ld
                r16 SP,         val_nn,         ld
                r16 SP,         r16 HL,         ld
                drefNN,         r16 SP,         ld
                drefNN,         r8  A,          ld
                derefR16 BC,    r8  A,          ld
                derefR16 DE,    r8  A,          ld
            ] 
            @ ldBVals (derefR16 HL) simpleSrcs
            @ ldR8Default [A; B; C; D; E; H; L]
        )
        |> List.map (fun (a,b,c) -> (a .>> sym ',' .>>. skipWS b) |>> c)
        |> List.reduce (<|>)
    pStringCI "LD" >>. ws >>. must args 
    <?> "LD"

// parses Data values like fixed blobs of bytes and word or a dim size value.
let private dataExpr = 
    let numLst = 
        (must expr) .>>. (many (skipWS (pChar ',') >>. skipWS (must expr)))
        |>> fun (f, r) -> f::r

    let convertDS (x: Operation list) : Data option = 
        match PatchExpr.Run None (fun x -> None) x with
        | Ok x -> 
            let res = DS (uint16 x)
            Some res
        | Error _ -> None
    let ds = 
        let exprVal = 
            expr
            |>> convertDS
            |?> Assert Option.isSome "Expression must be constant"
            |>> Option.defaultValue (DS 0us)

        (pStringCI "DS") >>. ws >>. skipWS (must exprVal)
        <?> "DIM Size"
    let db = 
        (pStringCI "DB" >>. ws >>. (must numLst)) 
        |>> fun x -> DB (x |> List.map Byte.Calc) 
        <?> "DIM Bytes"
    let dw = 
        (pStringCI "DW" >>. ws >>. (must numLst)) 
        |>> fun x -> DW (x |> List.map Word.Calc) 
        <?> "DIM Words"
        
    ds <|> db <|> dw

// parses all possible opcodes
let private OpCode =
    let os op =
        pStringCI (unionName op)
        |>> fun _ -> op
    ([
        os NOP 
        os RLCA 
        os RRCA 
        os RLA 
        os RRA 
        os STOP 
        os HALT 
        os DAA 
        os CPL 
        os SCF 
        os CCF 
        os RETI 
        os EI 
        os DI 
        op_RST
        op_RET
        op_ADD
        op_CALL
        op_JP
        op_JR
        op_LDH
        op_LD
        (dataExpr |>> fun d -> Data d)
    ] @ op_BIT_SET_RES @ op_PUSH_POP @ op_ShiftOps @ op_ADC_SBC_SUB @ op_INC_DEC)    
    |> List.reduce (<|>)
    <?> "opcode"

// parses a label definition
let private LabelDef =
    let nonExp = 
        (Label .>> pChar ':') 
        |!> fun (x, s) -> Some {Name = x; Exported = false}, { s with GlobalLabel = x.Global }
    let exp = 
        (Label .>> pString "::") 
        |!> fun (x, s) -> Some {Name = x; Exported = true}, { s with GlobalLabel = x.Global }
    exp <|> nonExp 
    <?> "Label"

// parses an file include. and updates the the input state.
let private includeFile  (getFileContent: GetFileContent) : Parser<unit, ParserState> =
    let label = "include"
    let strChar = satisfy (fun c -> c <> '"') "char"
    let quotedStr = 
        pChar '"' >>. many strChar .>> pChar '"'
        <?> "string"
        |>> fun chars -> System.String(List.toArray chars)

    let includeDef = pStringCI "#INCLUDE" >>. must (ws >>. quotedStr)

    let rec checkRecursive state searchFN = 
        if state.position.fileName = searchFN then
            true
        else
            match state.parentState with
            | Some ps -> checkRecursive ps searchFN
            | None -> false

    let includeFile fn (is: InputState) : Result<InputState, string> = 
        let wantedFile = { currentFilePath = is.position.fileName; requestedFileName = fn }
        match getFileContent wantedFile with
        | Ok { filePath = fn; content = content } -> 
            match checkRecursive is fn with
            | true -> Error (sprintf "circular include of file %s" fn)
            | false -> 
                let newIS = fromFile fn content
                Ok {newIS with parentState = Some is}
        | Error e -> Error e


    let fn (ps, is) : Result<unit * (ParserState*InputState), ParserError> =
        match run includeDef (ps, is) with
        | Ok (incl, (ps, is)) -> 
            match includeFile incl is with
            | Ok newState -> Ok ((), (ps, newState))
            | Error e -> Error (label, e, is.position, Fail)
        | Error e -> Error e

    { fn = fn; label = label}

// parses a constant definition
let private define =
    (pStringCI "#SET") >>. ws >>. must (Identifier .>> sym '=' .>>. expr)
    |!> fun ((i, v), s) -> 
        let s = {s with Defines = Map.add i v s.Defines }
        ((), s)

// parses a macro definition
let private macroDef = 
    let (macro, macroRef) = forward ()

    
    let stopWord innerParser =
        let label = "macro content"
        let stopParser = pStringCI "MEND"

        let rec parseLoop resultSoFar inputChars =
            match run stopParser inputChars with
            | Ok (_, rest) -> Ok (List.rev resultSoFar, rest)
            | Error _ -> 
                match run innerParser inputChars with
                | Ok (res, rest) -> parseLoop (res::resultSoFar) rest
                | Error e -> Error e

        let innerParser = parseLoop []
        {fn=innerParser; label=label}
    
    
    let innerMacro = macro |>> macroStr
        
    let anyChar = 
        satisfy (fun _ -> true) "AnyChar"
        |>> fun c -> string c
    let text = 
        (innerMacro <|> anyChar) .>> opt lineComment ()

    
    let arg = (sym '%') >>. Identifier
    let args = arg .>>. many (sym ',' >>. arg) |>> fun (first, other) -> first::other
    

    macroRef := 
        (pStringCI "MACRO") >>. ws >>. must Identifier .>> ws .>>. (opt args []) .>>. must (stopWord text)    
        |>> fun ((name, args), body) -> 
            let body = System.String.Concat(List.toArray body)
            { Name = name; Args = args; Body = body }
    macro
    |!> fun (m, s) -> (), {s with Macros = Map.add m.Name m s.Macros }

// parses a macro call
let private macroCall =
    let argChr = satisfy (fun c -> c <> ',' && c <> '\n') "char"
    let arg = many1 argChr |>> charsToStr

    let args = 
        arg .>>. many (sym ',' >>. arg)
        |>> fun (a, aa) -> a::aa

    let expandMacro macro (args:string list) = 
        let replaceArg (body:string) (name:string, value:string) = 
            let pattern = sprintf @"(\%c%s(?=\W))" '%' (Regex.Escape name)
            Regex.Replace(body, pattern, value)

        if (List.length macro.Args) <> (List.length args) then
            Error (sprintf "Argument missmatch. Expected %d args got %d" (List.length macro.Args) (List.length args))
        else
            Ok (List.zip macro.Args args |> List.fold replaceArg macro.Body)
    let label = "macro call"

    let fn (ps, is) : Result<unit * (ParserState*InputState), ParserError> =
        match run (Identifier .>>. opt args []) (ps, is) with
        | Ok ((name, args), (ps, is)) -> 
            match Map.tryFind name ps.Macros with
            | Some macro -> 
                match expandMacro macro args with
                | Ok content ->
                    let macroName = sprintf "MACRO %s" macro.Name
                    let state = { (fromFile macroName content) with parentState = Some is }
                    Ok ((), (ps, state))
                | Error msg -> Error (macro.Name, msg, is.position, Fail) 
            | None -> Error  (label, (sprintf "unknown macro %s " name), is.position, Missmatch)
        | Error e -> Error e
    { fn = fn; label = label }

// parses the cartidge header values.
let private cartridge =
    
    let quotedASCII len = 
        let label = "ascii char"
        let asciiChar = satisfy (fun c -> c <= (char 127) && c <> '"') label
        let quote = 
            pString "\\\"" 
            |>> fun _ -> '"'
        let asciiChar = quote <|> asciiChar <?> label

        pChar '"' >>. many asciiChar .>> pChar '"'
        <?> sprintf "ascii-string (max length = %d)" len
        |>> fun chars -> System.String(List.toArray chars)
        |?> Assert (fun s -> s.Length <= len)  (sprintf "max string length = %d." len)

    let updateHeader upd = 
        mapState (fun (value, state) -> (value, {state with Header = (upd state.Header value) }))

    let headerFld name param upd =
        pStringCI name >>. ws >>. must param
        |> updateHeader upd
        |>> fun _ -> ()

    let bool = 
        [
            kw "ON"    true
            kw "TRUE"  true
            kw "YES"   true            
            kw "OFF"   false
            kw "FALSE" false
            kw "NO"    false
        ]
        |> List.reduce (<|>)

    let gbcFlag = 
        [
            kw "YES"        GBCFlag.GBCSupported
            kw "ON"         GBCFlag.GBCSupported
            kw "SUPPORTED"  GBCFlag.GBCSupported
            kw "TRUE"       GBCFlag.GBCSupported

            kw "NO"      GBCFlag.DMG
            kw "OFF"     GBCFlag.DMG
            kw "DMG"     GBCFlag.DMG
            kw "FALSE"   GBCFlag.DMG
            
            kw "ONLY"  GBCFlag.GBCOnly
            kw "FORCE" GBCFlag.GBCOnly
        ]
        |> List.reduce (<|>)

    let destination = bool |>> fun v -> if v then Destination.Japanese else Destination.NonJapanese

    let mbc = 
        let flag n = (opt (ws >>. kw n true) false)

        let romSize = 
            let value = 
                (Enum.GetValues(typeof<RomSize>) :?> (RomSize [])) |> Array.toList
                |> List.map (fun v -> kw (v.ToString().TrimStart('_')) v)
                |> List.reduce (<|>)
            opt (ws >>. value) RomSize._32k
            
            
        let ramSize = 
            let value = 
                (Enum.GetValues(typeof<RamSize>) :?> (RamSize [])) |> Array.toList
                |> List.map (fun v -> kw (v.ToString().TrimStart('_')) v)
                |> List.reduce (<|>)
            opt (ws >>. value) RamSize.None
        

        let details =
            flag "BAT" .>>. romSize .>>. ramSize
            |>> fun ((bat, rom), ram) -> { HasBattery = bat; RomSize = rom; RamSize = ram }

        let simple =
            pStringCI "NONE" >>. flag "BAT" .>>. flag "RAM" 
            |>> fun (bat, ram) -> Simple (ram, bat)
        
        let mbc1 = pStringCI "MBC1" >>. details |>> fun d -> MBC1 d
        let mbc2 = pStringCI "MBC2" >>. flag "BAT" .>>. romSize |>> fun (bat, rom) -> MBC2 (rom, bat)
        let mbc3 = pStringCI "MBC3" >>. details .>>. flag "TIMER" |>> fun d -> MBC3 d
        let mbc5 = pStringCI "MBC5" >>. details .>>. flag "RUMBLE" |>> fun d -> MBC5 d
        let mbc6 = pStringCI "MBC6" >>. details |>> fun d -> MBC6 d
        let mbc7 = pStringCI "MBC7" >>. details |>> fun d -> MBC7 d
        let mmm01 = pStringCI "MMM01" >>. details |>> fun d -> MBC6 d

        simple <|> mbc1 <|> mbc2 <|> mbc3 <|> mbc5 <|> mbc6 <|> mbc7 <|> mmm01


    let args = 
        [
            headerFld "TITLE"        (quotedASCII 11) (fun h v -> { h with Title = v })
            headerFld "MANUFACTURER" (quotedASCII 4)  (fun h v -> { h with ManufacturerCode = v })
            headerFld "GBC"          gbcFlag          (fun h v -> { h with GBC = v })
            headerFld "SGB"          bool             (fun h v -> { h with SGB = v })
            headerFld "LICENSEE"     number           (fun h v -> { h with LicenseeCode = uint16 v })
            headerFld "VERSION"      number           (fun h v -> { h with Version = byte v })
            headerFld "JAPANESE"     destination      (fun h v -> { h with Destination = v })
            headerFld "MBC"          mbc              (fun h v -> { h with CartridgeType = v })
        ]
        |> List.reduce (<|>)

    pStringCI "#CARTRIDGE." >>. must args

// parses comments and all the things that may appear "anywhere" like includes and defines.
let private commentsAndDefines getFileContent = many (skipWS (lineComment <|> macroDef <|> macroCall <|> define <|> cartridge <|> includeFile getFileContent)) <?> "Comments or Whitespaces"

// skip and process all comments etc.
let private skipCommentsAndDefines getFileContent p = commentsAndDefines getFileContent >>. skipWS p <?> p.label

// parses a optional label followed by an opcode.
let private Expression getFileContent : Parser<Expression, ParserState> =    
    let lbl = skipCommentsAndDefines getFileContent LabelDef <?> "Label"
    
    (opt lbl None) .>>. skipCommentsAndDefines getFileContent OpCode
    <?> "opcode"

// parses a linker section.
let private section getFileContent : Parser<Area*uint16 option*Expression list, ParserState> =
    let origin = 
        (ws >>. pCharCI '@' >>. skipWS number) |>> fun x -> Some (uint16 x)
    
    let rom = (pStringCI "ROM"  >>. skipWS number) |>> fun n -> Area.Rom n
    let ram = (pStringCI "WRAM" >>. skipWS number) |>> fun n -> Area.WRam n
    let ram = ram <|> kwUnions [Area.VRam; Area.HRam; Area.SRam; Area.OAM]

    let nonLBWS = satisfy (fun c -> (Char.IsWhiteSpace c) && c <> '\n') "nonlbws"
    let lb = (many nonLBWS) >>. pChar '\n'

    let sectDef h = 
        h .>>. (opt origin None) .>> lb .>>. must (many1 (Expression getFileContent))
        |>> fun ((a, o), ops) -> a,o, ops

    let romSect = sectDef rom
    let ramSect = sectDef ram

    let mainSect = 
        pStringCI "MAIN" >>. must (many1 (Expression getFileContent))
        |>> fun x -> (Area.Rom 0, Some 0x0100us, x)

    let sect = 
        romSect <|> ramSect <|> mainSect
        <?> "SECTION"

    (skipCommentsAndDefines getFileContent (pStringCI "SECTION")) >>. ws >>. must sect

// parses a range of section as long as the file has more content
let private sections getFileContent = 
    (section getFileContent) *>>! (skipCommentsAndDefines getFileContent EOF)

// parse the given file and return the sections and cartridge header.
let parse fileName (getFileContent: GetFileContent) : Result<CartridgeHeader * (Area*uint16 option*Expression list) list, string> = 
    let pState = { 
        Defines = Map.empty; 
        GlobalLabel = null; 
        Macros = Map.empty;
        Header = {
            Title = ""
            ManufacturerCode = ""
            GBC = GBCFlag.DMG
            LicenseeCode = 0us
            SGB = false
            CartridgeType = Simple (false, false)
            Destination = Destination.Japanese
            Version = 0uy
        }
    }

    match getFileContent { currentFilePath = ""; requestedFileName = fileName } with 
    | Error e -> Error e
    | Ok { filePath = fileName; content = mainContent} -> 
        (pState, fromFile fileName mainContent)
        |> run (sections getFileContent)
        |> fun r ->
            match r with
            | Ok (v, (ps, _)) -> Ok (ps.Header, v)
            | Error (label, err, pos, _) -> 
                let fn = System.IO.Path.GetFileName(pos.fileName)
                let posStr = sprintf "\"%s\" line %d column %d" fn (pos.line+1) (pos.column+1)
                let msg = sprintf "Error parsing %s at %s:\n%s" label posStr err
                Error msg
