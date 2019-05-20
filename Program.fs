// Learn more about F# at http://fsharp.org

open System
open PatchExpr
open Linker
open Cartridge
open Assembler
open OpCodes
open AsmParser
open Utils

type Options = {
    InputFile: string option
    RomFile: string option
    SymbolFile: string option
}

let parseArgs argv = 
    let options = { InputFile = None; RomFile = None; SymbolFile = None }

    let rec parseArg opt argv = 
        match argv with
        | [] -> Some opt
        | cur::next ->
            match cur with
            | "-o" ->
                match next with
                | fn::others -> parseArg { opt with RomFile = Some fn } others
                | _ -> None
            | "-s" ->
                match next with
                    | fn::others -> parseArg { opt with SymbolFile = Some fn } others
                    | _ -> None
            | fn ->
                parseArg { opt with InputFile = Some fn} next
    parseArg options argv

let showUsage () = 
    printf "Todo"


let assembleAndLink opt = 
    let header = {
        Title = "ToDo"
        ManufacturerCode = "FOO"
        GBC = GBCFlag.DMG
        LicenseeCode = 0us
        SGB = false
        CartridgeType = Simple (true, true) 
        Destination = Destination.NonJapanese
        Version = 0uy
    }


    if opt.InputFile.IsSome && System.IO.File.Exists(opt.InputFile.Value) then
        let input = System.IO.File.ReadAllText(opt.InputFile.Value)
        let assembleAll = List.map assemble >> CollectResults

        let writeFile (fn: string option) (w : Writer) =
            match fn with
            | Some fn -> 
                use f = System.IO.File.Create(fn)
                w f
            | None -> ()


        let res =
            parse input 
            |> Result.bind assembleAll
            |> Result.bind (Link header)
       
        match res with
        | Ok linkRes ->
            do writeFile opt.RomFile linkRes.Rom
            do writeFile opt.SymbolFile linkRes.Symbols
        | Error e -> 
            printf "Error: %s" e
        ()
    else
        printf "Error: Input file not found"
        showUsage ()

    ()


[<EntryPoint>]
let main argv =
    let opts = parseArgs (Array.toList argv)
    match opts with
    | Some o -> assembleAndLink o
    | None -> showUsage ()
    0 // return an integer exit code
