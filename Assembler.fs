module Assembler

open OpCodes
open Linker
open Utils
open Cartridge
open PatchExpr



let rec private fixRelativeExpr patch exp =
    match exp with
    | [] -> []
    | head::cons ->
        let hRes = patch head
        List.append hRes (fixRelativeExpr patch cons)

let private relExpr h = 
    match h with
    | SymAdr a -> [SymAdr a; CurAdr; Push 1; Add; Sub]
    | x -> [x]
let private patchCurAdr x = 
    match x with
    | CurAdr -> [CurAdr; Push 1; Sub]
    | x -> [x]

let private assembleOpCode opCode : Result<byte[] * Patch list, string> = 
    let s oc = Ok ([|byte oc|], [])
    let e oc = Ok ([|0xCBuy ;byte oc|], [])

    let fix = fixRelativeExpr patchCurAdr 

    let assembleData d : Result<byte[] * Patch list, string> = 
        match d with 
        | DB bytes -> 
            let data = Array.zeroCreate<byte> (List.length bytes)
            let patches = 
                bytes
                |> List.mapi (fun i exp -> 
                    let (Byte.Calc exp) = exp
                    { Offset = i; Size = BYTE; Expr = exp }
                )
            Ok (data, patches)
        | DW words -> 
            let data = Array.zeroCreate<byte> (2 * (List.length words))
            let patches = 
                words
                |> List.mapi (fun i exp -> 
                    let (Word.Calc exp) = exp
                    [ 
                        { Offset = (i*2); Size = BYTE; Expr = List.append exp [Lo] } 
                        { Offset = (i*2)+1; Size = BYTE; Expr = List.append (fix exp) [Hi] } 
                    ]
                )
                |> List.collect (fun p -> p)
            Ok (data, patches)
        | DS s -> Ok (Array.zeroCreate<byte> (int s), [])

    
    let sw oc p = 
        let (Word.Calc c) = p
        let patch = { Offset = 1; Size = WORD; Expr = (fix c) }
        Ok ([|byte oc; 0uy; 0uy|], [patch])

    let sb oc p = 
        let (Byte.Calc c) = p
        let patch = { Offset = 1; Size = BYTE; Expr = (fix c) }
        Ok ([|byte oc; 0uy|], [patch])

    let Sbyte patch oc p = 
        match p with
        | SByte.Calc c -> 
            let patch = { Offset = 1; Size = SBYTE; Expr = (patch (fix c)) }
            Ok ([|byte oc; 0uy|], [patch])

    let ss = Sbyte (fun c -> c)
    let rl = Sbyte (fixRelativeExpr relExpr)
        

    match opCode with 
    | Data d                           -> assembleData d
    | NOP                              -> s  0x00    // 00 NOP
    | LD ((R16 BC), NN v)              -> sw 0x01 v  // 01 LD BC, nn
    | LD (Deref (Reg BC), R8 A )       -> s  0x02    // 02 LD (BC), A
    | INC (R16 BC)                     -> s  0x03    // 03 INC BC
    | INC (R8 B)                       -> s  0x04    // 04 INC B
    | DEC (R8 B)                       -> s  0x05    // 05 DEC B
    | LD (R8 B, N v)                   -> sb 0x06 v  // 06 LD B, n
    | RLCA                             -> s  0x07    // 07 RLCA
    | LD (Deref (Addr v), R16 SP)      -> sw 0x08 v  // 08 LD (nn), SP
    | ADD (R16 HL, R16 BC)             -> s  0x09    // 09 ADD HL, BC
    | LD (R8 A, Deref (Reg BC))        -> s  0x0A    // 0A LD A, (BC)
    | DEC (R16 BC)                     -> s  0x0B    // 0B DEC BC
    | INC (R8 C)                       -> s  0x0C    // 0C INC C
    | DEC (R8 C)                       -> s  0x0D    // 0D DEC C
    | LD (R8 C, N v)                   -> sb 0x0E v  // 0E LD C, n
    | RRCA                             -> s  0x0F    // 0F RRC A
    | STOP                             -> s  0x10    // 10 STOP
    | LD (R16 DE, NN v)                -> sw 0x11 v  // 11 LD DE, nn
    | LD (Deref (Reg DE), R8 A)        -> s  0x12    // 12 LD (DE), A
    | INC (R16 DE)                     -> s  0x13    // 13 INC DE
    | INC (R8 D)                       -> s  0x14    // 14 INC D
    | DEC (R8 D)                       -> s  0x15    // 15 DEC D
    | LD (R8 D, N v)                   -> sb 0x16 v  // 16 LD D, n
    | RLA                              -> s  0x17    // 17 RLA
    | JR (Flag.Always, v)              -> rl 0x18 v  // 18 JR N
    | ADD (R16 HL, R16 DE)             -> s  0x19    // 19 ADD HL DE
    | LD (R8 A, Deref (Reg DE))        -> s  0x1A    // 1A LD A, (DE)
    | DEC (R16 DE)                     -> s  0x18    // 1B DEC DE
    | INC (R8 E)                       -> s  0x1C    // 1C INC E
    | DEC (R8 E)                       -> s  0x1D    // 1D DEC E
    | LD (R8 E, N v)                   -> sb 0x1E v  // 1E LD E, n
    | RRA                              -> s  0x1F    // 1F RRA
    | JR (Flag.nz, v)                  -> rl 0x20 v  // 20 JR NZ n
    | LD (R16 HL, NN v)                -> sw 0x21 v  // 21 LD HL, nn
    | LDI (Deref (Reg HL), R8 A)       -> s  0x22    // 22 LDI (HL), A
    | INC (R16 HL)                     -> s  0x23    // 23 INC HL
    | INC (R8 H)                       -> s  0x24    // 24 INC H
    | DEC (R8 H)                       -> s  0x25    // 25 DEC H
    | LD (R8 H, N v)                   -> sb 0x26 v  // 26 LD H, n
    | DAA                              -> s  0x27    // 27 DAA
    | JR (Flag.z, v)                   -> rl 0x28 v  // 28 JR Z, n
    | ADD (R16 HL, R16 HL)             -> s  0x29    // 29 ADD HL, HL
    | LDI (R8 A, Deref (Reg HL))       -> s  0x2A    // 2A LDI A, (HL)
    | DEC (R16 HL)                     -> s  0x2B    // 2B DEC HL
    | INC (R8 L)                       -> s  0x2C    // 2C INC L
    | DEC (R8 L)                       -> s  0x2D    // 2D DEC L
    | LD (R8 L, N v)                   -> sb 0x2E v  // 2E LD L, n
    | CPL                              -> s  0x2F    // 2F CPL
    | JR (Flag.nc, v)                  -> rl 0x30 v  // 30 JR NC, n
    | LD (R16 SP, NN v)                -> sw 0x31 v  // 31 LD SP, nn
    | LDD (Deref (Reg HL), R8 A)       -> s  0x32    // 32 LDD (HL), A
    | INC (R16 SP)                     -> s  0x33    // 33 INC SP
    | INC (Deref (Reg HL))             -> s  0x34    // 34 INC (HL)
    | DEC (Deref (Reg HL))             -> s  0x35    // 35 DEC (HL)
    | LD (Deref (Reg HL), N v)         -> sb 0x36 v  // 36 LD (HL), n
    | SCF                              -> s  0x37    // 37 SCF
    | JR (Flag.c, v)                   -> rl 0x38 v  // 38 JR C, n
    | ADD (R16 HL, R16 SP)             -> s  0x39    // 39 ADD HL, SP
    | LDD (R8 A, Deref (Reg HL))       -> s  0x3A    // 3A LDD A, (HL)
    | DEC (R16 SP)                     -> s  0x3B    // 3B DEC SP
    | INC (R8 A)                       -> s  0x3C    // 3C INC A
    | DEC (R8 A)                       -> s  0x3D    // 3D DEC A
    | LD (R8 A, N v)                   -> sb 0x3E v  // 3E LD A, n
    | CCF                              -> s  0x3F    // 3F CCF
    | LD (R8 B, R8 B)                  -> s  0x40    // 40 LD B, B
    | LD (R8 B, R8 C)                  -> s  0x41    // 41 LD B, C
    | LD (R8 B, R8 D)                  -> s  0x42    // 42 LD B, D
    | LD (R8 B, R8 E)                  -> s  0x43    // 43 LD B, E
    | LD (R8 B, R8 H)                  -> s  0x44    // 44 LD B, H
    | LD (R8 B, R8 L)                  -> s  0x45    // 45 LD B, L
    | LD (R8 B, Deref (Reg HL))        -> s  0x46    // 46 LD B, (HL)
    | LD (R8 B, R8 A)                  -> s  0x47    // 47 LD B, A
    | LD (R8 C, R8 B)                  -> s  0x48    // 48 LD C, B
    | LD (R8 C, R8 C)                  -> s  0x49    // 49 LD C, C
    | LD (R8 C, R8 D)                  -> s  0x4A    // 4A LD C, D
    | LD (R8 C, R8 E)                  -> s  0x4B    // 4B LD C, E
    | LD (R8 C, R8 H)                  -> s  0x4C    // 4C LD C, H
    | LD (R8 C, R8 L)                  -> s  0x4D    // 4D LD C, L
    | LD (R8 C, Deref (Reg HL))        -> s  0x4E    // 4E LD C, (HL)
    | LD (R8 C, R8 A)                  -> s  0x4F    // 4F LD C, A
    | LD (R8 D, R8 B)                  -> s  0x50    // 50 LD D, B
    | LD (R8 D, R8 C)                  -> s  0x51    // 51 LD D, C
    | LD (R8 D, R8 D)                  -> s  0x52    // 52 LD D, D
    | LD (R8 D, R8 E)                  -> s  0x53    // 53 LD D, E
    | LD (R8 D, R8 H)                  -> s  0x54    // 54 LD D, H
    | LD (R8 D, R8 L)                  -> s  0x55    // 55 LD D, L
    | LD (R8 D, Deref (Reg HL))        -> s  0x56    // 56 LD D, (HL)
    | LD (R8 D, R8 A)                  -> s  0x57    // 57 LD D, A
    | LD (R8 E, R8 B)                  -> s  0x58    // 58 LD E, B
    | LD (R8 E, R8 C)                  -> s  0x59    // 59 LD E, C
    | LD (R8 E, R8 D)                  -> s  0x5A    // 5A LD E, D
    | LD (R8 E, R8 E)                  -> s  0x5B    // 5B LD E, E
    | LD (R8 E, R8 H)                  -> s  0x5C    // 5C LD E, H
    | LD (R8 E, R8 L)                  -> s  0x5D    // 5D LD E, L
    | LD (R8 E, Deref (Reg HL))        -> s  0x5E    // 5E LD E, (HL)
    | LD (R8 E, R8 A)                  -> s  0x5F    // 5F LD E, A
    | LD (R8 H, R8 B)                  -> s  0x60    // 60 LD H, B
    | LD (R8 H, R8 C)                  -> s  0x61    // 61 LD H, C
    | LD (R8 H, R8 D)                  -> s  0x62    // 62 LD H, D
    | LD (R8 H, R8 E)                  -> s  0x63    // 63 LD H, E
    | LD (R8 H, R8 H)                  -> s  0x64    // 64 LD H, H
    | LD (R8 H, R8 L)                  -> s  0x65    // 65 LD H, L
    | LD (R8 H, Deref (Reg HL))        -> s  0x66    // 66 LD H, (HL)
    | LD (R8 H, R8 A)                  -> s  0x67    // 67 LD H, A
    | LD (R8 L, R8 B)                  -> s  0x68    // 68 LD L, B
    | LD (R8 L, R8 C)                  -> s  0x69    // 69 LD L, C
    | LD (R8 L, R8 D)                  -> s  0x6A    // 6A LD L, D
    | LD (R8 L, R8 E)                  -> s  0x6B    // 6B LD L, E
    | LD (R8 L, R8 H)                  -> s  0x6C    // 6C LD L, H
    | LD (R8 L, R8 L)                  -> s  0x6D    // 6D LD L, L
    | LD (R8 L, Deref (Reg HL))        -> s  0x6E    // 6E LD L, (HL)
    | LD (R8 L, R8 A)                  -> s  0x6F    // 6F LD L, A
    | LD (Deref (Reg HL), R8 B)        -> s  0x70    // 70 LD (HL), B
    | LD (Deref (Reg HL), R8 C)        -> s  0x71    // 71 LD (HL), C
    | LD (Deref (Reg HL), R8 D)        -> s  0x72    // 72 LD (HL), D
    | LD (Deref (Reg HL), R8 E)        -> s  0x73    // 73 LD (HL), E
    | LD (Deref (Reg HL), R8 H)        -> s  0x74    // 74 LD (HL), H
    | LD (Deref (Reg HL), R8 L)        -> s  0x75    // 75 LD (HL), L
    | HALT                             -> s  0x76    // 76 HALT
    | LD (Deref (Reg HL), R8 A)        -> s  0x77    // 77 LD (HL), A
    | LD (R8 A, R8 B)                  -> s  0x78    // 78 LD A, B
    | LD (R8 A, R8 C)                  -> s  0x79    // 79 LD A, C
    | LD (R8 A, R8 D)                  -> s  0x7A    // 7A LD A, D
    | LD (R8 A, R8 E)                  -> s  0x7B    // 7B LD A, E
    | LD (R8 A, R8 H)                  -> s  0x7C    // 7C LD A, H
    | LD (R8 A, R8 L)                  -> s  0x7D    // 7D LD A, L
    | LD (R8 A, Deref (Reg HL))        -> s  0x7E    // 7E LD A, (HL)
    | LD (R8 A, R8 A)                  -> s  0x7F    // 7F LD A, A
    | ADD (R8 A, R8 B)                 -> s  0x80    // 80 ADD A, B
    | ADD (R8 A, R8 C)                 -> s  0x81    // 81 ADD A, C
    | ADD (R8 A, R8 D)                 -> s  0x82    // 82 ADD A, D
    | ADD (R8 A, R8 E)                 -> s  0x83    // 83 ADD A, E
    | ADD (R8 A, R8 H)                 -> s  0x84    // 84 ADD A, H
    | ADD (R8 A, R8 L)                 -> s  0x85    // 85 ADD A, L
    | ADD (R8 A, Deref (Reg HL))       -> s  0x86    // 86 ADD A, (HL)
    | ADD (R8 A, R8 A)                 -> s  0x87    // 87 ADD A, A
    | ADC (R8 A, R8 B)                 -> s  0x88    // 88 ADC A, B
    | ADC (R8 A, R8 C)                 -> s  0x89    // 89 ADC A, C
    | ADC (R8 A, R8 D)                 -> s  0x8A    // 8A ADC A, D
    | ADC (R8 A, R8 E)                 -> s  0x8B    // 8B ADC A, E
    | ADC (R8 A, R8 H)                 -> s  0x8C    // 8C ADC A, H
    | ADC (R8 A, R8 L)                 -> s  0x8D    // 8D ADC A, L
    | ADC (R8 A, Deref (Reg HL))       -> s  0x8E    // 8E ADC A, (HL)
    | ADC (R8 A, R8 A)                 -> s  0x8F    // 8F ADC A, A
    | SUB (R8 A, R8 B)                 -> s  0x90    // 90 SUB A, B
    | SUB (R8 A, R8 C)                 -> s  0x91    // 91 SUB A, C
    | SUB (R8 A, R8 D)                 -> s  0x92    // 92 SUB A, D
    | SUB (R8 A, R8 E)                 -> s  0x93    // 93 SUB A, E
    | SUB (R8 A, R8 H)                 -> s  0x94    // 94 SUB A, H
    | SUB (R8 A, R8 L)                 -> s  0x95    // 95 SUB A, L
    | SUB (R8 A, Deref (Reg HL))       -> s  0x96    // 96 SUB A, (HL)
    | SUB (R8 A, R8 A)                 -> s  0x97    // 97 SUB A, A
    | SBC (R8 A, R8 B)                 -> s  0x98    // 98 SBC A, B
    | SBC (R8 A, R8 C)                 -> s  0x99    // 99 SBC A, C
    | SBC (R8 A, R8 D)                 -> s  0x9A    // 9A SBC A, D
    | SBC (R8 A, R8 E)                 -> s  0x9B    // 9B SBC A, E
    | SBC (R8 A, R8 H)                 -> s  0x9C    // 9C SBC A, H
    | SBC (R8 A, R8 L)                 -> s  0x9D    // 9D SBC A, L
    | SBC (R8 A, Deref (Reg HL))       -> s  0x9E    // 9E SBC A, (HL)
    | SBC (R8 A, R8 A)                 -> s  0x9F    // 9F SBC A, A
    | AND (R8 B)                       -> s  0xA0    // A0 AND B
    | AND (R8 C)                       -> s  0xA1    // A1 AND C
    | AND (R8 D)                       -> s  0xA2    // A2 AND D
    | AND (R8 E)                       -> s  0xA3    // A3 AND E
    | AND (R8 H)                       -> s  0xA4    // A4 AND H
    | AND (R8 L)                       -> s  0xA5    // A5 AND L
    | AND (Deref (Reg HL))             -> s  0xA6    // A6 AND (HL)
    | AND (R8 A)                       -> s  0xA7    // A7 AND A
    | XOR (R8 B)                       -> s  0xA8    // A8 XOR B
    | XOR (R8 C)                       -> s  0xA9    // A9 XOR C
    | XOR (R8 D)                       -> s  0xAA    // AA XOR D
    | XOR (R8 E)                       -> s  0xAB    // AB XOR E
    | XOR (R8 H)                       -> s  0xAC    // AC XOR H
    | XOR (R8 L)                       -> s  0xAD    // AD XOR L
    | XOR (Deref (Reg HL))             -> s  0xAE    // AE XOR (HL)
    | XOR (R8 A)                       -> s  0xAF    // AF XOR A
    | OR (R8 B)                        -> s  0xB0    // B0 OR B
    | OR (R8 C)                        -> s  0xB1    // B1 OR C
    | OR (R8 D)                        -> s  0xB2    // B2 OR D
    | OR (R8 E)                        -> s  0xB3    // B3 OR E
    | OR (R8 H)                        -> s  0xB4    // B4 OR H
    | OR (R8 L)                        -> s  0xB5    // B5 OR L
    | OR (Deref (Reg HL))              -> s  0xB6    // B6 OR (HL
    | OR (R8 A)                        -> s  0xB7    // B7 OR A
    | CP (R8 B)                        -> s  0xB8    // B8 CP B
    | CP (R8 C)                        -> s  0xB9    // B9 CP C
    | CP (R8 D)                        -> s  0xBA    // BA CP D
    | CP (R8 E)                        -> s  0xBB    // BB CP E
    | CP (R8 H)                        -> s  0xBC    // BC CP H
    | CP (R8 L)                        -> s  0xBD    // BD CP L
    | CP (Deref (Reg HL))              -> s  0xBE    // BE CP (HL
    | CP (R8 A)                        -> s  0xBF    // BF CP A
    | RET (Flag.nz)                    -> s  0xC0    // C0 RET NZ
    | POP BC                           -> s  0xC1    // C1 POP BC
    | JP (Flag.nz, NN v)               -> sw 0xC2 v  // C2 JP NZ, nn
    | JP (Flag.Always, NN v)           -> sw 0xC3 v  // C3 JP nn
    | CALL (Flag.nz, v)                -> sw 0xC4 v  // C4 CALL NZ, nn
    | PUSH BC                          -> s  0xC5    // C5 PUSH BC
    | ADD (R8 A, N v)                  -> sb 0xC6 v  // C6 ADD A, n
    | RST 0x00uy                       -> s  0xC7    // C7 RST 0
    | RET (Flag.z)                     -> s  0xC8    // C8 RET Z
    | RET (Flag.Always)                -> s  0xC9    // C9 RET
    | JP (Flag.z, NN v)                -> sw 0xCA v  // CA JP Z, nn
    | CALL (Flag.z, v)                 -> sw 0xCC v  // CC CALL Z, nn
    | CALL (Flag.Always, v)            -> sw 0xCD v  // CD CALL nn
    | ADC (R8 A, N v)                  -> sb 0xCE v  // CE ADC A, n
    | RST 0x08uy                       -> s  0xCF    // CF RST 8
    | RET (Flag.nc)                    -> s  0xD0    // D0 RET NC
    | POP DE                           -> s  0xD1    // D1 POP DE
    | JP (Flag.nc, NN v)               -> sw 0xD2 v  // D2 JP NC, nn
    | CALL (Flag.nc, v)                -> sw 0xD4 v  // D4 CALL NC, nn
    | PUSH DE                          -> s  0xD5    // D5 PUSH DE
    | SUB (R8 A, N v)                  -> sb 0xD6 v  // D6 SUB A, n
    | RST 0x10uy                       -> s  0xD7    // D7 RST 10
    | RET (Flag.c)                     -> s  0xD8    // D8 RET C
    | RETI                             -> s  0xD9    // D9 RETI
    | JP (Flag.c, NN v)                -> sw 0xDA v  // DA JP C, nn
    | CALL (Flag.c, v)                 -> sw 0xDC v  // DC CALL C, nn
    | SBC (R8 A, N v)                  -> sb 0xDE v  // DE SBC A, n
    | RST 0x18uy                       -> s  0xDF    // DF RST 18
    | LDH (N v, R8 A)                  -> sb 0xE0 v  // E0 LDH ($FF00+n), A
    | POP HL                           -> s  0xE1    // E1 POP HL
    | LDH (R8 C, R8 A)                 -> s  0xE2    // E2 LDH ($FF00+C), A
    | PUSH HL                          -> s  0xE5    // E5 PUSH HL
    | AND (N v)                        -> sb 0xE6 v  // E6 AND n
    | RST 0x20uy                       -> s  0xE7    // E7 RST 20
    | ADD (R16 SP, R v)                -> ss 0xE8 v  // E8 ADD SP, n
    | JP (Flag.Always, Deref (Reg HL)) -> s  0xE9    // E9 JP (HL)
    | LD (Deref (Addr v), R8 A)        -> sw 0xEA v  // EA LD (nn), A
    | XOR (N v)                        -> sb 0xEE v  // EE XOR n
    | RST 0x28uy                       -> s  0xEF    // EF RST 28
    | LDH (R8 A, N v)                  -> sb 0xF0 v  // F0 LDH A, ($FF00+n)
    | POP AF                           -> s  0xF1    // F1 POP AF
    | LDH (R8 A, R8 C)                 -> s  0xF2    // F2 LDH A, ($FF00+C)
    | DI                               -> s  0xF3    // F3 DI
    | PUSH AF                          -> s  0xF5    // F5 PUSH AF
    | OR (N v)                         -> sb 0xF6 v  // F6 OR n
    | RST 0x30uy                       -> s  0xF7    // F7 RST 30
    | LD (R16 HL, R v)                 -> ss 0xF8 v  // F8 LD HL, (SP+d)
    | LD (R16 SP, R16 HL)              -> s  0xF9    // F9 LD SP, HL
    | LD (R8 A, Deref (Addr v))        -> sw 0xFA v  // FA LD A, (nn)
    | EI                               -> s  0xFB    // FB EI
    | CP (N v)                         -> sb 0xFE v  // FE CP n
    | RST 0x38uy                       -> s  0xFF    // FF RST 38
    | RLC (R8 B)                       -> e  0x00    // 00 RLC B
    | RLC (R8 C)                       -> e  0x01    // 01 RLC C
    | RLC (R8 D)                       -> e  0x02    // 02 RLC D
    | RLC (R8 E)                       -> e  0x03    // 03 RLC E
    | RLC (R8 H)                       -> e  0x04    // 04 RLC H
    | RLC (R8 L)                       -> e  0x05    // 05 RLC L
    | RLC (Deref (Reg HL))             -> e  0x06    // 06 RLC (HL)
    | RLC (R8 A)                       -> e  0x07    // 07 RLC A
    | RRC (R8 B)                       -> e  0x08    // 08 RRC B
    | RRC (R8 C)                       -> e  0x09    // 09 RRC C
    | RRC (R8 D)                       -> e  0x0A    // 0A RRC D
    | RRC (R8 E)                       -> e  0x0B    // 0B RRC E
    | RRC (R8 H)                       -> e  0x0C    // 0C RRC H
    | RRC (R8 L)                       -> e  0x0D    // 0D RRC L
    | RRC (Deref (Reg HL))             -> e  0x0E    // 0E RRC (HL)
    | RRC (R8 A)                       -> e  0x0F    // 0F RRC A
    | RL (R8 B)                        -> e  0x10    // 10 RL B
    | RL (R8 C)                        -> e  0x11    // 11 RL C
    | RL (R8 D)                        -> e  0x12    // 12 RL D
    | RL (R8 E)                        -> e  0x13    // 13 RL E
    | RL (R8 H)                        -> e  0x14    // 14 RL H
    | RL (R8 L)                        -> e  0x15    // 15 RL L
    | RL (Deref (Reg HL))              -> e  0x16    // 16 RL (HL)
    | RL (R8 A)                        -> e  0x17    // 17 RL A
    | RR (R8 B)                        -> e  0x18    // 18 RR B
    | RR (R8 C)                        -> e  0x19    // 19 RR C
    | RR (R8 D)                        -> e  0x1A    // 1A RR D
    | RR (R8 E)                        -> e  0x1B    // 1B RR E
    | RR (R8 H)                        -> e  0x1C    // 1C RR H
    | RR (R8 L)                        -> e  0x1D    // 1D RR L
    | RR (Deref (Reg HL))              -> e  0x1E    // 1E RR (HL)
    | RR (R8 A)                        -> e  0x1F    // 1F RR A
    | SLA (R8 B)                       -> e  0x20    // 20 SLA B
    | SLA (R8 C)                       -> e  0x21    // 21 SLA C
    | SLA (R8 D)                       -> e  0x22    // 22 SLA D
    | SLA (R8 E)                       -> e  0x23    // 23 SLA E
    | SLA (R8 H)                       -> e  0x24    // 24 SLA H
    | SLA (R8 L)                       -> e  0x25    // 25 SLA L
    | SLA (Deref (Reg HL))             -> e  0x26    // 26 SLA (HL)
    | SLA (R8 A)                       -> e  0x27    // 27 SLA A
    | SRA (R8 B)                       -> e  0x28    // 28 SRA B
    | SRA (R8 C)                       -> e  0x29    // 29 SRA C
    | SRA (R8 D)                       -> e  0x2A    // 2A SRA D
    | SRA (R8 E)                       -> e  0x2B    // 2B SRA E
    | SRA (R8 H)                       -> e  0x2C    // 2C SRA H
    | SRA (R8 L)                       -> e  0x2D    // 2D SRA L
    | SRA (Deref (Reg HL))             -> e  0x2E    // 2E SRA (HL)
    | SRA (R8 A)                       -> e  0x2F    // 2F SRA A
    | SWAP (R8 B)                      -> e  0x30    // 30 SWAP B
    | SWAP (R8 C)                      -> e  0x31    // 31 SWAP C
    | SWAP (R8 D)                      -> e  0x32    // 32 SWAP D
    | SWAP (R8 E)                      -> e  0x33    // 33 SWAP E
    | SWAP (R8 H)                      -> e  0x34    // 34 SWAP H
    | SWAP (R8 L)                      -> e  0x35    // 35 SWAP L
    | SWAP (Deref (Reg HL))            -> e  0x36    // 36 SWAP (HL)
    | SWAP (R8 A)                      -> e  0x37    // 37 SWAP A
    | SRL (R8 B)                       -> e  0x38    // 38 SRL B
    | SRL (R8 C)                       -> e  0x39    // 39 SRL C
    | SRL (R8 D)                       -> e  0x3A    // 3A SRL D
    | SRL (R8 E)                       -> e  0x3B    // 3B SRL E
    | SRL (R8 H)                       -> e  0x3C    // 3C SRL H
    | SRL (R8 L)                       -> e  0x3D    // 3D SRL L
    | SRL (Deref (Reg HL))             -> e  0x3E    // 3E SRL (HL)
    | SRL (R8 A)                       -> e  0x3F    // 3F SRL A
    | BIT (0uy, R8 B)                  -> e  0x40    // 40 BIT 0, B
    | BIT (0uy, R8 C)                  -> e  0x41    // 41 BIT 0, C
    | BIT (0uy, R8 D)                  -> e  0x42    // 42 BIT 0, D
    | BIT (0uy, R8 E)                  -> e  0x43    // 43 BIT 0, E
    | BIT (0uy, R8 H)                  -> e  0x44    // 44 BIT 0, H
    | BIT (0uy, R8 L)                  -> e  0x45    // 45 BIT 0, L
    | BIT (0uy, Deref (Reg HL))        -> e  0x46    // 46 BIT 0, (HL)
    | BIT (0uy, R8 A)                  -> e  0x47    // 47 BIT 0, A
    | BIT (1uy, R8 B)                  -> e  0x48    // 48 BIT 1, B
    | BIT (1uy, R8 C)                  -> e  0x49    // 49 BIT 1, C
    | BIT (1uy, R8 D)                  -> e  0x4A    // 4A BIT 1, D
    | BIT (1uy, R8 E)                  -> e  0x4B    // 4B BIT 1, E
    | BIT (1uy, R8 H)                  -> e  0x4C    // 4C BIT 1, H
    | BIT (1uy, R8 L)                  -> e  0x4D    // 4D BIT 1, L
    | BIT (1uy, Deref (Reg HL))        -> e  0x4E    // 4E BIT 1, (HL)
    | BIT (1uy, R8 A)                  -> e  0x4F    // 4F BIT 1, A
    | BIT (2uy, R8 B)                  -> e  0x50    // 50 BIT 2, B
    | BIT (2uy, R8 C)                  -> e  0x51    // 51 BIT 2, C
    | BIT (2uy, R8 D)                  -> e  0x52    // 52 BIT 2, D
    | BIT (2uy, R8 E)                  -> e  0x53    // 53 BIT 2, E
    | BIT (2uy, R8 H)                  -> e  0x54    // 54 BIT 2, H
    | BIT (2uy, R8 L)                  -> e  0x55    // 55 BIT 2, L
    | BIT (2uy, Deref (Reg HL))        -> e  0x56    // 56 BIT 2, (HL)
    | BIT (2uy, R8 A)                  -> e  0x57    // 57 BIT 2, A
    | BIT (3uy, R8 B)                  -> e  0x58    // 58 BIT 3, B
    | BIT (3uy, R8 C)                  -> e  0x59    // 59 BIT 3, C
    | BIT (3uy, R8 D)                  -> e  0x5A    // 5A BIT 3, D
    | BIT (3uy, R8 E)                  -> e  0x5B    // 5B BIT 3, E
    | BIT (3uy, R8 H)                  -> e  0x5C    // 5C BIT 3, H
    | BIT (3uy, R8 L)                  -> e  0x5D    // 5D BIT 3, L
    | BIT (3uy, Deref (Reg HL))        -> e  0x5E    // 5E BIT 3, (HL)
    | BIT (3uy, R8 A)                  -> e  0x5F    // 5F BIT 3, A
    | BIT (4uy, R8 B)                  -> e  0x60    // 60 BIT 4, B
    | BIT (4uy, R8 C)                  -> e  0x61    // 61 BIT 4, C
    | BIT (4uy, R8 D)                  -> e  0x62    // 62 BIT 4, D
    | BIT (4uy, R8 E)                  -> e  0x63    // 63 BIT 4, E
    | BIT (4uy, R8 H)                  -> e  0x64    // 64 BIT 4, H
    | BIT (4uy, R8 L)                  -> e  0x65    // 65 BIT 4, L
    | BIT (4uy, Deref (Reg HL))        -> e  0x66    // 66 BIT 4, (HL)
    | BIT (4uy, R8 A)                  -> e  0x67    // 67 BIT 4, A
    | BIT (5uy, R8 B)                  -> e  0x68    // 68 BIT 5, B
    | BIT (5uy, R8 C)                  -> e  0x69    // 69 BIT 5, C
    | BIT (5uy, R8 D)                  -> e  0x6A    // 6A BIT 5, D
    | BIT (5uy, R8 E)                  -> e  0x6B    // 6B BIT 5, E
    | BIT (5uy, R8 H)                  -> e  0x6C    // 6C BIT 5, H
    | BIT (5uy, R8 L)                  -> e  0x6D    // 6D BIT 5, L
    | BIT (5uy, Deref (Reg HL))        -> e  0x6E    // 6E BIT 5, (HL)
    | BIT (5uy, R8 A)                  -> e  0x6F    // 6F BIT 5, A
    | BIT (6uy, R8 B)                  -> e  0x70    // 70 BIT 6, B
    | BIT (6uy, R8 C)                  -> e  0x71    // 71 BIT 6, C
    | BIT (6uy, R8 D)                  -> e  0x72    // 72 BIT 6, D
    | BIT (6uy, R8 E)                  -> e  0x73    // 73 BIT 6, E
    | BIT (6uy, R8 H)                  -> e  0x74    // 74 BIT 6, H
    | BIT (6uy, R8 L)                  -> e  0x75    // 75 BIT 6, L
    | BIT (6uy, Deref (Reg HL))        -> e  0x76    // 76 BIT 6, (HL)
    | BIT (6uy, R8 A)                  -> e  0x77    // 77 BIT 6, A
    | BIT (7uy, R8 B)                  -> e  0x78    // 78 BIT 7, B
    | BIT (7uy, R8 C)                  -> e  0x79    // 79 BIT 7, C
    | BIT (7uy, R8 D)                  -> e  0x7A    // 7A BIT 7, D
    | BIT (7uy, R8 E)                  -> e  0x7B    // 7B BIT 7, E
    | BIT (7uy, R8 H)                  -> e  0x7C    // 7C BIT 7, H
    | BIT (7uy, R8 L)                  -> e  0x7D    // 7D BIT 7, L
    | BIT (7uy, Deref (Reg HL))        -> e  0x7E    // 7E BIT 7, (HL)
    | BIT (7uy, R8 A)                  -> e  0x7F    // 7F BIT 7, A
    | RES (0uy, R8 B)                  -> e  0x80    // 80 RES 0, B
    | RES (0uy, R8 C)                  -> e  0x81    // 81 RES 0, C
    | RES (0uy, R8 D)                  -> e  0x82    // 82 RES 0, D
    | RES (0uy, R8 E)                  -> e  0x83    // 83 RES 0, E
    | RES (0uy, R8 H)                  -> e  0x84    // 84 RES 0, H
    | RES (0uy, R8 L)                  -> e  0x85    // 85 RES 0, L
    | RES (0uy, Deref (Reg HL))        -> e  0x86    // 86 RES 0, (HL)
    | RES (0uy, R8 A)                  -> e  0x87    // 87 RES 0, A
    | RES (1uy, R8 B)                  -> e  0x88    // 88 RES 1, B
    | RES (1uy, R8 C)                  -> e  0x89    // 89 RES 1, C
    | RES (1uy, R8 D)                  -> e  0x8A    // 8A RES 1, D
    | RES (1uy, R8 E)                  -> e  0x8B    // 8B RES 1, E
    | RES (1uy, R8 H)                  -> e  0x8C    // 8C RES 1, H
    | RES (1uy, R8 L)                  -> e  0x8D    // 8D RES 1, L
    | RES (1uy, Deref (Reg HL))        -> e  0x8E    // 8E RES 1, (HL)
    | RES (1uy, R8 A)                  -> e  0x8F    // 8F RES 1, A
    | RES (2uy, R8 B)                  -> e  0x90    // 90 RES 2, B
    | RES (2uy, R8 C)                  -> e  0x91    // 91 RES 2, C
    | RES (2uy, R8 D)                  -> e  0x92    // 92 RES 2, D
    | RES (2uy, R8 E)                  -> e  0x93    // 93 RES 2, E
    | RES (2uy, R8 H)                  -> e  0x94    // 94 RES 2, H
    | RES (2uy, R8 L)                  -> e  0x95    // 95 RES 2, L
    | RES (2uy, Deref (Reg HL))        -> e  0x96    // 96 RES 2, (HL)
    | RES (2uy, R8 A)                  -> e  0x97    // 97 RES 2, A
    | RES (3uy, R8 B)                  -> e  0x98    // 98 RES 3, B
    | RES (3uy, R8 C)                  -> e  0x99    // 99 RES 3, C
    | RES (3uy, R8 D)                  -> e  0x9A    // 9A RES 3, D
    | RES (3uy, R8 E)                  -> e  0x9B    // 9B RES 3, E
    | RES (3uy, R8 H)                  -> e  0x9C    // 9C RES 3, H
    | RES (3uy, R8 L)                  -> e  0x9D    // 9D RES 3, L
    | RES (3uy, Deref (Reg HL))        -> e  0x9E    // 9E RES 3, (HL)
    | RES (3uy, R8 A)                  -> e  0x9F    // 9F RES 3, A
    | RES (4uy, R8 B)                  -> e  0xA0    // A0 RES 4, B
    | RES (4uy, R8 C)                  -> e  0xA1    // A1 RES 4, C
    | RES (4uy, R8 D)                  -> e  0xA2    // A2 RES 4, D
    | RES (4uy, R8 E)                  -> e  0xA3    // A3 RES 4, E
    | RES (4uy, R8 H)                  -> e  0xA4    // A4 RES 4, H
    | RES (4uy, R8 L)                  -> e  0xA5    // A5 RES 4, L
    | RES (4uy, Deref (Reg HL))        -> e  0xA6    // A6 RES 4,(HL 
    | RES (4uy, R8 A)                  -> e  0xA7    // A7 RES 4, A
    | RES (5uy, R8 B)                  -> e  0xA8    // A8 RES 5, B
    | RES (5uy, R8 C)                  -> e  0xA9    // A9 RES 5, C
    | RES (5uy, R8 D)                  -> e  0xAA    // AA RES 5, D
    | RES (5uy, R8 E)                  -> e  0xAB    // AB RES 5, E
    | RES (5uy, R8 H)                  -> e  0xAC    // AC RES 5, H
    | RES (5uy, R8 L)                  -> e  0xAD    // AD RES 5, L
    | RES (5uy, Deref (Reg HL))        -> e  0xAE    // AE RES 5, (HL)
    | RES (5uy, R8 A)                  -> e  0xAF    // AF RES 5, A
    | RES (6uy, R8 B)                  -> e  0xB0    // B0 RES 6, B
    | RES (6uy, R8 C)                  -> e  0xB1    // B1 RES 6, C
    | RES (6uy, R8 D)                  -> e  0xB2    // B2 RES 6, D
    | RES (6uy, R8 E)                  -> e  0xB3    // B3 RES 6, E
    | RES (6uy, R8 H)                  -> e  0xB4    // B4 RES 6, H
    | RES (6uy, R8 L)                  -> e  0xB5    // B5 RES 6, L
    | RES (6uy, Deref (Reg HL))        -> e  0xB6    // B6 RES 6, (HL)
    | RES (6uy, R8 A)                  -> e  0xB7    // B7 RES 6, A
    | RES (7uy, R8 B)                  -> e  0xB8    // B8 RES 7, B
    | RES (7uy, R8 C)                  -> e  0xB9    // B9 RES 7, C
    | RES (7uy, R8 D)                  -> e  0xBA    // BA RES 7, D
    | RES (7uy, R8 E)                  -> e  0xBB    // BB RES 7, E
    | RES (7uy, R8 H)                  -> e  0xBC    // BC RES 7, H
    | RES (7uy, R8 L)                  -> e  0xBD    // BD RES 7, L
    | RES (7uy, Deref (Reg HL))        -> e  0xBE    // BE RES 7, (HL)
    | RES (7uy, R8 A)                  -> e  0xBF    // BF RES 7, A
    | SET (0uy, R8 B)                  -> e  0xC0    // C0 SET 0, B
    | SET (0uy, R8 C)                  -> e  0xC1    // C1 SET 0, C
    | SET (0uy, R8 D)                  -> e  0xC2    // C2 SET 0, D
    | SET (0uy, R8 E)                  -> e  0xC3    // C3 SET 0, E
    | SET (0uy, R8 H)                  -> e  0xC4    // C4 SET 0, H
    | SET (0uy, R8 L)                  -> e  0xC5    // C5 SET 0, L
    | SET (0uy, Deref (Reg HL))        -> e  0xC6    // C6 SET 0, (HL)
    | SET (0uy, R8 A)                  -> e  0xC7    // C7 SET 0, A
    | SET (1uy, R8 B)                  -> e  0xC8    // C8 SET 1, B
    | SET (1uy, R8 C)                  -> e  0xC9    // C9 SET 1, C
    | SET (1uy, R8 D)                  -> e  0xCA    // CA SET 1, D
    | SET (1uy, R8 E)                  -> e  0xCB    // CB SET 1, E
    | SET (1uy, R8 H)                  -> e  0xCC    // CC SET 1, H
    | SET (1uy, R8 L)                  -> e  0xCD    // CD SET 1, L
    | SET (1uy, Deref (Reg HL))        -> e  0xCE    // CE SET 1, (HL)
    | SET (1uy, R8 A)                  -> e  0xCF    // CF SET 1, A
    | SET (2uy, R8 B)                  -> e  0xD0    // D0 SET 2, B
    | SET (2uy, R8 C)                  -> e  0xD1    // D1 SET 2, C
    | SET (2uy, R8 D)                  -> e  0xD2    // D2 SET 2, D
    | SET (2uy, R8 E)                  -> e  0xD3    // D3 SET 2, E
    | SET (2uy, R8 H)                  -> e  0xD4    // D4 SET 2, H
    | SET (2uy, R8 L)                  -> e  0xD5    // D5 SET 2, L
    | SET (2uy, Deref (Reg HL))        -> e  0xD6    // D6 SET 2, (HL)
    | SET (2uy, R8 A)                  -> e  0xD7    // D7 SET 2, A
    | SET (3uy, R8 B)                  -> e  0xD8    // D8 SET 3, B
    | SET (3uy, R8 C)                  -> e  0xD9    // D9 SET 3, C
    | SET (3uy, R8 D)                  -> e  0xDA    // DA SET 3, D
    | SET (3uy, R8 E)                  -> e  0xDB    // DB SET 3, E
    | SET (3uy, R8 H)                  -> e  0xDC    // DC SET 3, H
    | SET (3uy, R8 L)                  -> e  0xDD    // DD SET 3, L
    | SET (3uy, Deref (Reg HL))        -> e  0xDE    // DE SET 3, (HL)
    | SET (3uy, R8 A)                  -> e  0xDF    // DF SET 3, A
    | SET (4uy, R8 B)                  -> e  0xE0    // E0 SET 4, B
    | SET (4uy, R8 C)                  -> e  0xE1    // E1 SET 4, C
    | SET (4uy, R8 D)                  -> e  0xE2    // E2 SET 4, D
    | SET (4uy, R8 E)                  -> e  0xE3    // E3 SET 4, E
    | SET (4uy, R8 H)                  -> e  0xE4    // E4 SET 4, H
    | SET (4uy, R8 L)                  -> e  0xE5    // E5 SET 4, L
    | SET (4uy, Deref (Reg HL))        -> e  0xE6    // E6 SET 4, (HL)
    | SET (4uy, R8 A)                  -> e  0xE7    // E7 SET 4, A
    | SET (5uy, R8 B)                  -> e  0xE8    // E8 SET 5, B
    | SET (5uy, R8 C)                  -> e  0xE9    // E9 SET 5, C
    | SET (5uy, R8 D)                  -> e  0xEA    // EA SET 5, D
    | SET (5uy, R8 E)                  -> e  0xEB    // EB SET 5, E
    | SET (5uy, R8 H)                  -> e  0xEC    // EC SET 5, H
    | SET (5uy, R8 L)                  -> e  0xED    // ED SET 5, L
    | SET (5uy, Deref (Reg HL))        -> e  0xEE    // EE SET 5, (HL)
    | SET (5uy, R8 A)                  -> e  0xEF    // EF SET 5, A
    | SET (6uy, R8 B)                  -> e  0xF0    // F0 SET 6, B
    | SET (6uy, R8 C)                  -> e  0xF1    // F1 SET 6, C
    | SET (6uy, R8 D)                  -> e  0xF2    // F2 SET 6, D
    | SET (6uy, R8 E)                  -> e  0xF3    // F3 SET 6, E
    | SET (6uy, R8 H)                  -> e  0xF4    // F4 SET 6, H
    | SET (6uy, R8 L)                  -> e  0xF5    // F5 SET 6, L
    | SET (6uy, Deref (Reg HL))        -> e  0xF6    // F6 SET 6, (HL)
    | SET (6uy, R8 A)                  -> e  0xF7    // F7 SET 6, A
    | SET (7uy, R8 B)                  -> e  0xF8    // F8 SET 7, B
    | SET (7uy, R8 C)                  -> e  0xF9    // F9 SET 7, C
    | SET (7uy, R8 D)                  -> e  0xFA    // FA SET 7, D
    | SET (7uy, R8 E)                  -> e  0xFB    // FB SET 7, E
    | SET (7uy, R8 H)                  -> e  0xFC    // FC SET 7, H
    | SET (7uy, R8 L)                  -> e  0xFD    // FD SET 7, L
    | SET (7uy, Deref (Reg HL))        -> e  0xFE    // FE SET 7, (HL)
    | SET (7uy, R8 A)                  -> e  0xFF    // FF SET 7, A
    | _ -> Error (sprintf "Invalid Operation: %A" opCode)

let private isRamArea a =
    match a with
    | Area.Rom _ -> false
    | _ -> true

let private isNonDataOC op =
    match op with
    | Data _ -> false
    | _ -> true

let assemble (section: (Area*uint16 option*Expression list)) : Result<Section, string> =
    let updatePatch off  (p: Patch) = 
        {p with Offset = p.Offset + off}

    let merge (state: (Symbol list*byte[]*Patch list)) (item: ((Label option)*byte[]*Patch list)) =
        let (syms, buf, patches) = state
        let (lbl, data, patch) = item
        let offset = buf.Length
        let buf = Array.append buf data

        let syms = 
            match lbl with
            | Some lbl -> 
                { Name = lbl.Name; Exported = lbl.Exported; Offset = uint16 offset } :: syms
            | None -> syms

        let patch = List.map (updatePatch offset) patch
        let patches = List.append patches patch
        (syms, buf, patches)
        
    let assemble (lbl, opCode) = 
        assembleOpCode opCode
        |> Result.map (fun (d, p) -> lbl, d, p)
    
    let buildSection area origin ((symbols:Symbol list), data, patches) =
        let rom = { 
                Data = data 
                Patches = patches 
            }
        let res = { 
            Origin= origin
            Length = (uint16 data.Length)
            Symbols = symbols 
            Area = area 
            Rom = Some rom
        }
        res

    let (area, origin, opCodes) = section

    let assemble codes = 
        codes
        |> List.map assemble
        |> CollectResults
        |> Result.map (List.fold merge (List.empty, Array.empty, List.empty))
        |> Result.map (buildSection area origin)

    let checkValidRam  =
        opCodes 
        |> List.toSeq
        |> Seq.map (fun (_, op) -> op)
        |> Seq.tryFind isNonDataOC 
        |> Option.isNone

    match isRamArea area, checkValidRam with
    | (true, false) -> Error "Only data definitions are allowed in RAM sections"
    | _ -> assemble opCodes
        