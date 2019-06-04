module OpCodes

open PatchExpr

type Flag = 
    | Always = 0
    | z = 1
    | c = 2 
    | nz = 3
    | nc = 4



type Reg8  = A    | B | C | D | E | H | L
type Reg16 = AF   | BC    | DE    | HL    | SP

type Word = 
    | Calc of Operation list

type Byte = 
    | Calc of Operation list

type SByte = 
    | Calc of Operation list

type Deref =
    | Addr of Word
    | Reg of Reg16

type Val =
    | Deref of Deref
    | N of Byte
    | R8 of Reg8
    | NN of Word
    | R16 of Reg16
    | R of SByte


type Data =
    | DS of uint16
    | DB of Byte list
    | DW of Word list


type OpCode =
    | NOP
    | LD of dest:Val * src : Val
    | LDH of dest:Val * src : Val
    | INC of Val
    | DEC of Val
    | RLCA
    | RRCA
    | RLA
    | RRA
    | ADD of dest:Val * src : Val
    | ADC of dest:Val * src : Val
    | SUB of dest:Val * src : Val
    | SBC of dest:Val * src : Val
    | STOP
    | HALT
    | JR of Flag * SByte
    | LDI of dest:Val * src : Val
    | LDD of dest:Val * src : Val
    | DAA
    | CPL
    | SCF
    | CCF
    | AND of Val
    | XOR of Val
    | CP of Val
    | OR of Val
    | RET of Flag
    | RETI
    | EI
    | DI
    | POP of Reg16
    | PUSH of Reg16
    | JP of Flag * Val
    | CALL of Flag * Word
    | RST of byte
    | RLC of Val
    | RRC of Val
    | RL of Val
    | RR of Val
    | SLA of Val
    | SRA of Val
    | SRL of Val
    | SWAP of Val
    | BIT of (byte*Val)
    | RES of (byte*Val)
    | SET of (byte*Val)
    | Data of Data

type Label = { 
    Name:SymbolName; 
    Exported : bool
} 
type Expression = (Label option) * OpCode


let patchOperation (f: Operation list->Operation list) opCode =
    let patchSB (sb: SByte) : SByte =
        let (SByte.Calc c) = sb
        SByte.Calc (f c)
    let patchW (w: Word): Word =
        let (Word.Calc c) = w
        Word.Calc (f c)
    let patchB (b: Byte): Byte =
        let (Byte.Calc c) = b
        Byte.Calc (f c)
    let (~~) v =
        match v with 
        | Deref (Addr w) -> Deref (Addr (patchW w))
        | N b -> N (patchB b)
        | NN w -> NN (patchW w)
        | R sb -> R (patchSB sb)
        | v -> v

    match opCode with
    | LD (d,s) -> LD (~~d, ~~s)
    | LDH (d, s)-> LDH (~~d, ~~s)
    | INC v -> INC ~~v
    | DEC v -> DEC ~~v
    | ADD (d, s)-> ADD (~~d, ~~s)
    | ADC (d, s)-> ADC (~~d, ~~s)
    | SUB (d, s)-> SUB (~~d, ~~s)
    | SBC (d, s)-> SBC (~~d, ~~s)
    | JR (f, sb) -> JR (f, (patchSB sb))
    | LDI (d, s)-> LDI (~~d, ~~s)
    | LDD (d, s)-> LDD (~~d, ~~s)
    | AND v -> AND ~~v
    | XOR v -> XOR ~~v
    | CP v -> CP ~~v
    | OR v -> OR ~~v
    | JP (f, v) -> JP (f, ~~v)
    | CALL (f, v) -> CALL (f, patchW v)
    | RLC v -> RLC ~~v
    | RRC v -> RRC ~~v
    | RL v -> RL ~~v
    | RR v -> RR ~~v
    | SLA v -> SLA ~~v
    | SRA v -> SRA ~~v
    | SRL v -> SRL ~~v
    | SWAP v -> SWAP ~~v
    | BIT (b, v) -> BIT (b, ~~v)
    | RES (b, v) -> RES (b, ~~v)
    | SET (b, v) -> SET (b, ~~v)
    | x -> x