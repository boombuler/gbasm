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
    if opt.InputFile.IsSome && System.IO.File.Exists(opt.InputFile.Value) then
        let assembleAll = List.map assemble >> CollectResults

        let writeFile (fn: string option) (w : Writer) =
            match fn with
            | Some fn -> 
                use f = System.IO.File.Create(fn)
                w f
            | None -> ()

        let getFile req = 
            let basePath = 
                match req.currentFilePath with 
                | "" -> Environment.CurrentDirectory
                | currentFile -> System.IO.Path.GetDirectoryName(System.IO.Path.GetFullPath(currentFile))
            let fn = System.IO.Path.GetFullPath(req.requestedFileName, basePath)
            if System.IO.File.Exists(fn) then
                Ok { filePath = fn; content = System.IO.File.ReadAllText(fn) }
            else
                Error (sprintf "File %s does not exist" fn)
            

        let res =
            parse opt.InputFile.Value getFile
            |> Result.bind ( fun (h, sects) -> 
                match assembleAll sects with 
                | Ok res -> Link h res
                | Error e -> Error e
            )
       
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
