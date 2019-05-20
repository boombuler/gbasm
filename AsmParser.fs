module AsmParser

open OpCodes
open ParserBuilder
open System
open Microsoft.FSharp.Reflection
open PatchExpr
open Linker

let private charsToStr = List.toArray >> System.String

type ParserState = {
    Defines: Map<string, Operation list>
    GlobalLabel: string
}

let private forward<'a> (_: Unit) :  (Parser<'a, ParserState> * Parser<'a, ParserState> ref)  =
    let dummyParser : Parser<'a, ParserState> =
        let label = "Dummy"
        let innerParser (_, input) =
            Error (label, "Unfixed Forward Parser", input.position)
        {fn=innerParser; label=label}
    
    let fRef = ref dummyParser
    let f =
        let innerFn input = 
            run !fRef input 
        {fn=innerFn; label="unknown"}
    (f, fRef)

let private Assert test msg v = 
    match test v with
    | true -> None
    | false -> Some msg

let private kw str value =
    pStringCI str
    |>> fun _ -> value

let private number =
    let digit =  anyCharOf (['0'..'9'] )
    let hexdigit = anyCharOf (['0'..'9'] @ ['A'..'F'] @ ['a'..'f'])

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
    decimal <|> hexDec

let private whitespaceChar = 
    let predicate = Char.IsWhiteSpace 
    let label = "whitespace"
    satisfy predicate label 

let ws = 
    many1 whitespaceChar
    |>> ignore

let lineComment = 
    (pChar ';') >>. many (satisfy (fun c -> c <> '\r' && c <> '\n') "Any")
    |>> ignore
    <?> "Comment"

let private Identifier = 
    let alpha = satisfy Char.IsLetter "Letter"
    let alphaNum = satisfy Char.IsLetterOrDigit "Letter or Digit"

    alpha .>>. (many alphaNum) 
    |>> fun (c, chars) -> System.String(c::chars |> List.toArray)
    <?> "Identifier"

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

let skipWS p = (many whitespaceChar) >>. p
let sym s = skipWS (pChar s) .>> (many whitespaceChar)

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
 
let private v_word =
    expr 
    |>> fun w -> Word.Calc w
let private val_nn = v_word |>> fun w -> NN w

let private v_byte = 
    expr 
    |>> fun w -> Byte.Calc w
let private val_n = v_byte |>> fun b -> N b

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
let private val_r needsSign = v_sbyte needsSign |>> fun b -> R b


let private unionName<'a> (itm: 'a) = 
    match FSharpValue.GetUnionFields(itm, typeof<'a>) with
    | case, _ -> case.Name
    | _ -> ""

let private kwUnions<'a> (items :'a list) =
    items
    |> List.map (fun i -> kw (unionName<'a> i) i)
    |> List.reduce (<|>)

let private op_PUSH_POP =
    let target = kwUnions [BC; DE; HL; AF]

    let push = 
        pStringCI "PUSH" >>. ws >>. target 
        |>> (fun t -> PUSH t) <?> "PUSH"
    let pop = 
        pStringCI "POP" >>. ws >>. target 
        |>> (fun t -> POP t) <?> "POP"
    [push; pop]

let private derefR16 r = 
    let targetHL = pChar '[' >>. skipWS (kwUnions<Reg16> [r]) .>> sym ']'
    targetHL
    |>> fun a -> Deref (Reg a)
    <?> unionName r

let private dref<'a> (p: Parser<'a, ParserState>) : Parser<'a, ParserState> =
    pChar '[' >>. skipWS p .>> sym ']'

let private r8 (r: Reg8) =
    kwUnions [r] 
    |>> (fun r -> R8 r)

let private r16 (r: Reg16) =
    kwUnions [r]
    |>> (fun r -> R16 r)

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
    |> List.map (fun (s, c) -> (pStringCI s >>. ws >>. num .>> sym ',' .>>. skipWS target) |>> c <?> s)
    
let private op_ADC_SBC_SUB =
    let targetR8 = 
        kwUnions [A;B;C;D;E;H;L]
        |>> fun x -> R8 x
    let targetHL = derefR16 HL
    let targetNum = val_n
    let target =  targetR8 <|> targetHL <|> targetNum


    let makeParser (str, conv) =
        pStringCI str >>. ws >>. pCharCI 'A' >>. sym ',' >>. skipWS target
        |>> conv
    [
        "ADC", fun x -> ADC (R8 A, x)
        "SBC", fun x -> SBC (R8 A, x)
        "SUB", fun x -> SUB (R8 A, x)
    ]
    |> List.map makeParser

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
        pStringCI s >>. ws >>. target
        |>> c 
        <?> s
    ) 

let private op_RST = 
    let validVector v = List.contains v [0x00; 0x08; 0x10; 0x18; 0x20; 0x28; 0x30; 0x38]
    let vec = 
        number
        |?> Assert validVector "Invalid Vector"
        |>> byte
    pStringCI "RST" >>. ws >>. vec 
    |>> fun v -> RST v
    <?> "RST"

let private jumpFlag =
    [
        kw "NZ" Flag.nz
        kw "Z" Flag.z
        kw "NC" Flag.nc
        kw "C" Flag.c
    ]
    |> List.reduce (<|>)

let private op_RET =
    pStringCI "RET" >>. opt (ws >>. jumpFlag) Flag.Always
    |>> fun f -> RET f

let private op_ADD : Parser<OpCode,ParserState> = 
    let items = 
        [
            kw "HL" (R16 HL), ((kwUnions [BC; DE; HL; SP]) |>> fun r -> R16 r)
            kw "SP" (R16 SP), val_n
            kw "A" (R8 A),    (kwUnions [A; B; C; D; E; H; L] |>> fun r -> R8 r) <|> derefR16 HL <|> val_n
        ]
        |> List.map (fun (t, s) -> t .>> sym ',' .>>. skipWS s)
        |> List.reduce (<|>)

    pStringCI "ADD" >>. ws >>. items
    |>> (fun dstSrc -> ADD dstSrc)

let private op_INC_DEC =
    let targets = 
        (kwUnions [BC; DE; HL; SP] |>> fun r -> R16 r)
        <|> (kwUnions [A;B;C;D;E;H;L] |>> fun r -> R8 r)
        <|> (derefR16 HL)

    [
        "INC", fun r -> INC r
        "DEC", fun r -> DEC r
    ]
    |> List.map (fun (kw, c) -> (pStringCI kw >>. ws >>. targets) |>> c)

let private op_CALL =
    let jumpFlag = jumpFlag .>> sym ','

    pStringCI "CALL" >>. (opt jumpFlag Flag.Always) .>>. skipWS v_word
    |>> fun (f, addr) -> CALL (f, addr)

let private op_JP =
    let jumpFlag = jumpFlag .>> sym ','

    let targets = ((derefR16 HL |>> fun r -> (Flag.Always, r)) <|> ((opt jumpFlag Flag.Always) .>>. skipWS val_nn))

    pStringCI "JP" >>. ws >>. targets
    |>> fun (f, v) -> JP (f, v)

let private op_JR =
    let jumpFlag = jumpFlag .>> sym ','
    pStringCI "JR" >>. ws >>. (opt jumpFlag Flag.Always) .>>. skipWS (v_sbyte false)
    |>> fun (f, v) -> JR (f, v)

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

    pStringCI "LDH" >>. ws >>. args 
    |>> fun (t, s) -> LDH (t, s)

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
    pStringCI "LD" >>. ws >>. args

let private dataExpr = 
    let numLst = 
        number .>>. (many (skipWS (pChar ',') >>. skipWS number))
        |>> fun (f, r) -> f::r

    let ds = 
        (pStringCI "DS") >>. ws >>. skipWS number 
        |>> fun x -> DS (uint16 x) 
        <?> "DIM Size"
    let db = 
        (pStringCI "DB" >>. ws >>. numLst) 
        |>> fun x -> DB (x |> List.map byte |> List.toArray) 
        <?> "DIM Bytes"
    let dw = 
        (pStringCI "DW" >>. ws >>. numLst) 
        |>> fun x -> DW (x |> List.map uint16 |> List.toArray) 
        <?> "DIM Words"
        
    ds <|> db <|> dw

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

let private LabelDef =
    let nonExp = 
        (Label .>> pChar ':') 
        |!> fun (x, s) -> Some {Name = x; Exported = false}, { s with GlobalLabel = x.Global }
    let exp = 
        (Label .>> pString "::") 
        |!> fun (x, s) -> Some {Name = x; Exported = true}, { s with GlobalLabel = x.Global }
    exp <|> nonExp 
    <?> "Label"



let private define =
    (pStringCI "#SET") >>. ws >>. Identifier .>> sym '=' .>>. expr
    |!> fun ((i, v), s) -> 
        let s = {s with Defines = Map.add i v s.Defines }
        ((), s)

let private comments = many (skipWS (lineComment <|> define)) <?> "Comments or Whitespaces"

let private skipComments p = comments >>. skipWS p
let private Expression : Parser<Expression, ParserState> =    
    let lbl = skipComments LabelDef <?> "Label"
    
    (opt lbl None) .>>. skipComments OpCode


let private section : Parser<Area*uint16 option*Expression list, ParserState> =
    let origin = 
        (ws >>. pCharCI '@' >>. skipWS number) |>> fun x -> Some (uint16 x)
    
    let rom = (pStringCI "ROM"  >>. skipWS number) |>> fun n -> Area.Rom n
    let ram = (pStringCI "WRAM" >>. skipWS number) |>> fun n -> Area.WRam n
    let ram = ram <|> kwUnions [Area.VRam; Area.HRam; Area.SRam; Area.OAM]

    let nonLBWS = satisfy (fun c -> (Char.IsWhiteSpace c) && c <> '\n') "nonlbws"
    let lb = (many nonLBWS) >>. pChar '\n'

    let sectDef h = 
        h .>>. (opt origin None) .>> lb .>>.  (many1 Expression)
        |>> fun ((a, o), ops) -> a,o, ops

    let romSect = sectDef rom
    let ramSect = sectDef ram

    let mainSect = 
        pStringCI "MAIN" >>. (many1 Expression)
        |>> fun x -> (Area.Rom 0, Some 0x0100us, x)

    let sect = romSect <|> ramSect <|> mainSect

    (skipComments (pStringCI "SECTION")) >>. ws >>. sect

let private sections = 
    section *>>! (skipComments EOF)
    

 

let parse str : Result<(Area*uint16 option*Expression list) list, string> = 
    let pState = { Defines = Map.empty; GlobalLabel = null }

    (pState, fromStr str)
    |> run sections
    |> fun r ->
        match r with
        | Ok (v, _) -> Ok v
        | Error (label, err, pos) -> 
            let posStr = sprintf "line %d column %d" (pos.line+1) (pos.column+1)
            let msg = sprintf "Error parsing %s at %s:\n%s" label posStr err
            Error msg
