module Linker

open Cartridge
open PatchExpr
open System.IO
open Utils
open System
open System.Linq.Expressions

type Symbol = {
    Name: SymbolName     // the name of the symbol
    Offset: uint16       // the offset, relative to the containing section.
    Exported: bool       // the symbol is also usable by other sections.
}

type BankNo = int // Some Areas have multiple banks, which might be switched

type Area = 
    | Rom of BankNo   // The actual rom
    | WRam  of BankNo // Internal RAM
    | VRam            // Video RAM (Sprite Data)
    | HRam            // High-RAM (Zero Page RAM) which can be accessed faster then normal RAM
    | SRam            // Optional additional RAM from the cartridge.
    | OAM             // Object Attribute Memory (Some kind of special video RAM)

type PatchSize 
    = BYTE
    | SBYTE
    | WORD

type Patch = {
    Offset : int
    Size: PatchSize
    Expr: Operation list
}

type RomData = {
    Data: byte[]         // the actual data of the section. (only needed for rom sections.)
    Patches: Patch list  // Patches which are applied to the Data, once all sections are in place.
}

type Section = {
    Origin: uint16 option // a fixed location to put the section.
    Length: uint16        // the length of the section.
    Symbols: Symbol list  // Symbols which are provided by this section.
    Area: Area            // the area where this section should be located.
    Rom: RomData option   // Data and patches for any rom section.
}

type private AddressRange = {
    Address: uint16
    Length: uint16
}

type private Block = 
    | Available of AddressRange
    | Assigned of Section

type Writer = Stream -> unit

type LinkRes = {
    Rom: Writer
    Symbols: Writer
}

let private getBlocks (a:Area) : Block seq =
    let range f t =
        Available { 
            Address = f
            Length = (t+1us) - f
        }

    match a with 
    | Rom bn ->
        if bn = 0 then
            seq {
                yield range 0x0000us 0x0103us
                yield range 0x0150us 0x3FFFus
            }
        else
            seq { yield range 0x4000us 0x7FFFus }
    | WRam bn ->
        if bn = 0 then
            seq { yield range 0xC000us 0xCFFFus }
        else
            seq { yield range 0xD000us 0xDFFFus }
    | VRam -> seq { yield range 0x8000us 0x9FFFus }
    | HRam -> seq { yield range 0xFF80us 0xFFFEus }
    | SRam -> seq { yield range 0xA000us 0xBFFFus }
    | OAM -> seq { yield range 0xFE00us 0xFEFFus }

let private getBankNo (sec:Section) =
    match sec.Area with 
    | Rom no  -> no
    | WRam no -> no
    | _ -> 0

let private getSymbolAddress (symbols:Map<SymbolName, (Section*Symbol)>)  (symName:SymbolName) : (BankNo * uint16) option =
    let dat = Map.tryFind symName symbols

    let sectionOffset = 
        dat 
        |> Option.bind (fun (s, _) -> s.Origin)
    
    let addrMapper ((_:Section), (sym:Symbol)) (offset:uint16) = 
        sym.Offset + offset

    let addr = Option.map2 addrMapper dat sectionOffset
    let bank = Option.map (fun (s, _) ->getBankNo s) dat
    
    Option.map2 (fun a b -> (b, a)) addr bank
  
let private blockContains addr block =
    let (start, length) = 
        match block with
        | Available av -> av.Address, av.Length
        | Assigned sect -> 
            match sect.Origin with
            | None -> 0us, 0us
            | Some origin -> origin, sect.Length
    addr >= start && addr < (start + length)

let private assignSectionToBlock block section allBlocks = 
    let splitBlock (b: AddressRange) (s: Section) : Block list =
        let blocks = seq {
            let endAddr = s.Origin.Value + s.Length

            // block before the selected address
            yield Available {
                Address = b.Address
                Length = s.Origin.Value - b.Address
            }
            // the new assigned block
            yield Assigned s
            // the block behind the section
            yield Available {
                Address = endAddr
                Length = b.Length - endAddr
            }
        }
        let blockNotEmpty b = 
            match b with
            | Assigned s -> s.Length > 0us
            | Available a -> a.Length > 0us
        blocks 
        |> Seq.where blockNotEmpty
        |> Seq.toList


    allBlocks 
    |> List.except (Seq.singleton (Available block))
    |> List.append (splitBlock block section)

let private assignSection (blocks: Block list) (section: Section) =
    match section.Origin with 
    | Some origin ->
        let targetBlock = 
            blocks
            |> List.where (blockContains origin)
            |> List.where (blockContains (origin + (section.Length-1us)))
            |> List.tryHead
        match targetBlock with 
        | None -> Error (sprintf "Invalid address $%x" origin)
        | Some (Assigned _) -> Error (sprintf "address $%x already in use" origin)
        | Some (Available blk) -> 
            Ok (assignSectionToBlock blk section blocks)
    | None -> Ok blocks
    
let private assignUnassigned (sections: Section list) (blocks: Block list) : Result<Section list, string> = 
    let getBlockCandidates len blocks =
        blocks 
        |>List.choose (fun b -> 
            match b with
            | Available blk -> 
                if blk.Length > len then
                    Some blk
                else
                    None
            | Assigned _ -> None
        )

    let rec tryAssign (sections: Section list) (blocks: Block list)  : Result<Section list, string> = 
        match sections with
        | head::rest ->
            let candidates = getBlockCandidates head.Length blocks            
            let rec tryAssignToBlock (addrs: AddressRange list) (blocks: Block list) =
                match addrs with
                | addr::candidates ->
                    let head = {head with Origin = Some addr.Address }
                    let updatedBlocks = assignSectionToBlock addr head blocks
                    match tryAssign rest updatedBlocks with
                    | Ok list -> Ok (head :: list)
                    | Error _ -> tryAssignToBlock candidates blocks
                | [] -> Error "Unable to assign section to any address space."
            tryAssignToBlock candidates blocks
        | [] -> Ok sections

    let sections = 
        sections
        |> List.sortByDescending (fun s -> s.Length)

    tryAssign sections blocks

let private arrangeSectionsForArea (area, (sections: Section list)) = 
    let (assigned, unassigned) = 
        sections
        |> List.fold (fun (a, u) s -> 
            if s.Origin.IsSome then
                (s::a), u
            else
                a, (s::u)
        ) (List.empty, List.empty)


    let blocks = getBlocks area |> Seq.toList 
    let blocks = FoldResults assignSection blocks assigned
    
    blocks
    |> Result.bind (assignUnassigned unassigned)
    |> Result.map (List.append assigned)    

let private applyPatches (sects:Section list) :Result<Section list, string> = 
    let getExports (sect: Section) =
        sect.Symbols 
        |> List.where (fun s -> s.Exported)
        |> List.map (fun sym -> (sym.Name, (sect, sym)))

    let allExports = List.collect getExports sects

    let getSymbolMapForSec (sect:Section) =
        let locals = 
            sect.Symbols 
            |> List.map (fun s -> (s.Name, (sect, s)))
        
        (List.append locals allExports)
        |> List.distinctBy (fun (k, _) -> k)
        |> Map.ofList

    let applyPatches (sect: Section) = 
        match sect.Rom with
        | Some rom ->
            let getOffset = getSymbolAddress (getSymbolMapForSec sect)
            match sect.Origin with 
            | Some sectOff ->
                let rec applyNextPatch (patches: Patch list) =
                    match patches with
                    | [] -> Ok ()
                    | patch::patches ->
                        let writePatch value = 
                            match patch.Size with
                            | SBYTE -> 
                                if (value < -128) || (value > 127) then
                                    Error (sprintf "Value %d out of range" value)
                                else
                                    rom.Data.[patch.Offset] <- byte value
                                    applyNextPatch patches
                            | BYTE -> 
                                rom.Data.[patch.Offset] <- byte value
                                applyNextPatch patches
                            | WORD ->
                                let value = int16 value
                                rom.Data.[patch.Offset] <- byte value
                                rom.Data.[patch.Offset+1] <- byte (value>>>8)
                                applyNextPatch patches
                        

                        let curAdr = (int sectOff) + patch.Offset

                        PatchExpr.Run (Some (uint16 curAdr)) getOffset patch.Expr
                        |> Result.bind writePatch


                applyNextPatch rom.Patches
            | None -> Error "Section not placed"
        | None -> Ok ()

    let res = 
        sects 
        |> List.map applyPatches
        |> CollectResults
    match res with 
    | Ok _ -> Ok sects
    | Error e -> Error e
      
let private linkerResFromSections header (sections: Section list) =

    let symbolWriter : Writer =
        let rec writeSec (sections:Section list) (s:Stream) =
            match sections with
            | head:: rest ->
                let rb = getBankNo head
                let symName (s:Symbol) = 
                    match s.Name.Local with
                    | None -> s.Name.Global
                    | Some l -> sprintf "%s.%s" s.Name.Global l
                let symLine (s:Symbol) = sprintf "%03X:%04X %s\n" rb (head.Origin.Value + s.Offset) (symName s)
            
                do head.Symbols 
                |> List.sortBy (fun sym -> sym.Offset)
                |> List.map symLine
                |> List.map System.Text.Encoding.UTF8.GetBytes
                |> List.iter (fun buf -> s.Write(buf, 0, buf.Length))

                writeSec rest s
            | [] -> ()

        sections 
        |> List.sortBy (fun s -> s.Origin)
        |> writeSec

    let romWriter = 
        let getSectionAddr (bankNo:BankNo) (offset: uint16): int =
            let offset = int offset
            match bankNo with
            | 0 -> offset
            | x -> (0x4000 * (x-1)) + offset

        let rec fill toPos pos (s:Stream) =
            let buffSize = min (toPos - pos) 512
            match buffSize with
            | 0 -> ()
            | bs -> 
                let buf = Array.zeroCreate bs
                s.Write(buf, 0, buffSize)
                fill toPos (pos + buffSize) s

        let rec writePackets romSize pos (s:Stream) packets =
            match packets with
            | head :: cons -> 
                let (idx, data) = head
                let seek = idx - pos
                let buf = Array.zeroCreate(seek)
                s.Write(buf, 0, buf.Length)
                s.Write(data, 0, data.Length)
                writePackets romSize (idx+data.Length) s cons
            | [] -> fill romSize pos s

        let createWriter romBankCount (input: (int*byte[])list) (w: Stream) = 
            do input 
            |> List.sortBy (fun (i, _) -> i)
            |> writePackets romBankCount 0 w
        
        let addGlobalChecksum items =
            let cs = 
                items
                |> List.map (fun (_, x) -> Array.fold (fun cur n -> cur + (uint16 n)) 0us x)
                |> List.fold (fun cur n -> cur + (uint16 n)) 0us
            (GLOBALCHECK, [| (byte (cs >>> 8)); byte cs |])::items

        sections
        |> List.choose (fun s -> 
            match s.Rom with
            | Some rom -> 
                match s.Origin with
                | Some origin -> 
                    let bn = getBankNo s
                    Some ((getSectionAddr bn origin), rom.Data)
                | None -> None
            | None -> None
            )
        |> List.append (List.singleton (HEADERSTART, headerToBytes header))
        |> addGlobalChecksum
        |> createWriter (getRomSize header.CartridgeType)

    { 
        Rom = romWriter
        Symbols = symbolWriter
    }

let Link header (sections:Section list) : Result<LinkRes, string> =
    let clearInvalidRomData s = 
        match s.Area with
        | Rom _ -> s
        | _ -> { s with Rom = None }

    sections
    |> List.map clearInvalidRomData           // remove the rom data from non rom sections.
    |> List.groupBy (fun s-> s.Area)          // group by area
    |> List.map arrangeSectionsForArea
    |> CollectResults
    |> Result.map (List.collect (fun l -> l))
    |> Result.bind applyPatches
    |> Result.map (linkerResFromSections header)
