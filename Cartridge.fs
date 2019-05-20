module Cartridge

open System.Text

type GBCFlag = 
    | DMG = 0x00uy
    | GBCSupported = 0x80uy
    | GBCOnly = 0xC0uy

type RomSize = 
    | _32k = 0x00uy
    | _64k = 0x01uy
    | _128k = 0x02uy
    | _256k = 0x03uy
    | _512k = 0x04uy
    | _1m = 0x05uy
    | _2m = 0x06uy
    | _4m = 0x07uy
    | _8m = 0x08uy
    | _1m1k = 0x52uy
    | _1m2k = 0x53uy
    | _1m5k = 0x54uy

type RamSize = 
    | None = 0x00uy
    | _2k = 0x01uy
    | _8k = 0x02uy
    | _32k = 0x03uy
    | _128k = 0x04uy
    | _64k = 0x05uy


type MBCDetails = {
    RomSize: RomSize
    RamSize: RamSize
    HasBattery: bool
}

let HEADERSTART = 0x0104
let GLOBALCHECK = 0x014E

let LOGO = 
    [|
        0xCEuy; 0xEDuy; 0x66uy; 0x66uy; 0xCCuy; 0x0Duy; 0x00uy; 0x0Buy; 0x03uy; 0x73uy; 0x00uy; 0x83uy; 0x00uy; 0x0Cuy; 0x00uy; 0x0Duy; 
        0x00uy; 0x08uy; 0x11uy; 0x1Fuy; 0x88uy; 0x89uy; 0x00uy; 0x0Euy; 0xDCuy; 0xCCuy; 0x6Euy; 0xE6uy; 0xDDuy; 0xDDuy; 0xD9uy; 0x99uy; 
        0xBBuy; 0xBBuy; 0x67uy; 0x63uy; 0x6Euy; 0x0Euy; 0xECuy; 0xCCuy; 0xDDuy; 0xDCuy; 0x99uy; 0x9Fuy; 0xBBuy; 0xB9uy; 0x33uy; 0x3Euy; 
    |]
 

type CartridgeType =
    | Simple of HasRam:bool * HasBattery:bool
    | MBC1 of MBCDetails
    | MBC2 of RomSize * HasBattery:bool
    | MMM01 of MBCDetails
    | MBC3 of MBCDetails * HasTimer:bool
    | MBC5 of MBCDetails * HasRumble:bool
    | MBC6 of MBCDetails
    | MBC7 of MBCDetails
    
type Destination = 
    | Japanese = 0x00uy
    | NonJapanese = 0x01uy

type CartridgeHeader = {
    Title: string // 0134-0143
    ManufacturerCode: string // 013F-0142
    GBC: GBCFlag // 0143 
    LicenseeCode: uint16 // 0144-0145
    SGB: bool // 0146
    CartridgeType: CartridgeType // 0147-0149
    Destination: Destination // 014A 
    Version: byte // 014C 
}

let private copyTo (destA :byte[]) (srcA: byte[]) offset srcIdx =
    if srcA <> null && srcIdx >= 0 && srcIdx < srcA.Length then
        destA.[(offset - HEADERSTART)+srcIdx] <- srcA.[srcIdx]
    else
        ()

let private str len offset s : (int*int*byte[]) = 
    if System.String.IsNullOrEmpty s then
        (len, offset, null)
    else
        let s = s.ToUpperInvariant ()
        let len = min len s.Length
        let buf = Encoding.ASCII.GetBytes(s, 0, len)
        (len, offset, buf)

let private bv offset (b:byte) =
    let v = byte b
    (1, offset, [|v|])

let private word offset v =
    let v1 = byte v
    let v2 = byte (v >>> 8)
    (2, offset, [|v1; v2|])

let private getRomSizeType ct =
    match ct with 
    | Simple _       -> RomSize._32k
    | MBC1  det      -> det.RomSize
    | MBC2  (rs, _)  -> rs
    | MMM01 det      -> det.RomSize
    | MBC3  (det, _) -> det.RomSize
    | MBC5  (det, _) -> det.RomSize
    | MBC6  det      -> det.RomSize
    | MBC7  det      -> det.RomSize

let private getRamSize ct =
    match ct with 
    | Simple (false,_) -> RamSize.None
    | Simple (true, _) -> RamSize._8k
    | MBC1  det        -> det.RamSize
    | MBC2  _          -> RamSize.None
    | MMM01 det        -> det.RamSize
    | MBC3  (det, _)   -> det.RamSize
    | MBC5  (det, _)   -> det.RamSize
    | MBC6  det        -> det.RamSize
    | MBC7  det        -> det.RamSize

let private getMBCMarker ct =
    match ct with
    | Simple (false, _) -> 0x00uy
    | MBC1 {HasBattery = false; RamSize = RamSize.None } -> 0x01uy
    | MBC1 {HasBattery = false } -> 0x02uy
    | MBC1 _ -> 0x03uy
    | MBC2 (_, false) -> 0x05uy
    | MBC2 _ -> 0x06uy
    | Simple (true, false) -> 0x08uy
    | Simple (true, true) -> 0x09uy
    | MMM01 {RamSize = RamSize.None} -> 0x0Buy
    | MMM01 {HasBattery = false} -> 0x0Cuy
    | MMM01 _ -> 0x0Duy
    | MBC3 ({HasBattery=true; RamSize = RamSize.None}, true) -> 0x0Fuy
    | MBC3 ({HasBattery=true}, true) -> 0x10uy
    | MBC3 ({RamSize = RamSize.None},_) -> 0x11uy
    | MBC3 ({HasBattery=false},_) -> 0x12uy
    | MBC3 _ -> 0x13uy
    | MBC5 ({RamSize = RamSize.None}, false) -> 0x19uy
    | MBC5 ({HasBattery = false}, false) -> 0x1Auy
    | MBC5 ({HasBattery = true}, false) -> 0x1Buy
    | MBC5 ({RamSize = RamSize.None}, true) -> 0x1Cuy
    | MBC5 ({HasBattery = false}, true) -> 0x1Duy
    | MBC5 ({HasBattery = true}, true) -> 0x1Euy
    | MBC6 _ -> 0x20uy
    | MBC7 _ -> 0x22uy

let private cartridgeTypeToBytes (ct: CartridgeType) : byte[] =
    let res = [| 
        getMBCMarker ct; 
        byte (getRomSizeType ct); 
        byte (getRamSize ct) 
    |]
    res

let private calcCheckSum (buf: byte[]) : byte =
    seq {0x0134 .. 0x014C}
    |> Seq.map (fun x -> x-HEADERSTART)
    |> Seq.map (fun idx -> int (buf.[idx]))
    |> Seq.fold (fun state v -> state - v - 1) 0
    |> byte

let headerToBytes (h:CartridgeHeader) : byte[] =
    let result = Array.zeroCreate<byte>(0x4A)

    let copyTo (cnt, offset, data) =
        Seq.init cnt (fun x -> x)
        |> Seq.iter (copyTo result data offset)

    copyTo (48,    0x0104, LOGO)
    copyTo (str 16 0x0134  h.Title)
    copyTo (str  4 0x013F  h.ManufacturerCode)
    copyTo (bv     0x0143  (byte h.GBC))
    copyTo (word   0x0144  h.LicenseeCode)
    if h.SGB then
        copyTo (bv 0x0146  0x03uy)
    copyTo (3,     0x0147, cartridgeTypeToBytes h.CartridgeType)
    copyTo (bv     0x014A  (byte h.Destination))
    copyTo (bv     0x014B  0x33uy)
    copyTo (bv     0x014C  h.Version)
    copyTo (bv     0x014D (calcCheckSum result))
    result

let getRomSize ct =
    match getRomSizeType ct with
    | RomSize._32k -> 32 * 1024
    | RomSize._64k -> 64 * 1024
    | RomSize._128k -> 128 * 1024
    | RomSize._256k -> 256 * 1024
    | RomSize._512k -> 512 * 1024
    | RomSize._1m -> 1 * 1024 * 1024
    | RomSize._2m -> 2 * 1024 * 1024
    | RomSize._4m -> 4 * 1024 * 1024
    | RomSize._8m -> 8 * 1024 * 1024
    | RomSize._1m1k -> (1 * 1024 * 1024) + (1 * 1024)
    | RomSize._1m2k -> (1 * 1024 * 1024) + (2 * 1024)
    | RomSize._1m5k -> (1 * 1024 * 1024) + (5 * 1024)