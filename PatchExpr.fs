module PatchExpr

open Utils
open System.Diagnostics

[<DebuggerDisplay("{Global}.{Local}")>]
type SymbolName = {
    Global: string
    Local: string option
}


type BankNo = int

type Operation = 
    | Push of int32
    | Add
    | Sub
    | Mult
    | BitAnd
    | BitOr
    | SymAdr of SymbolName
    | SymBank of SymbolName
    | CurAdr
    | Hi
    | Lo
    
let Run (curAdr:uint16) (getSymAdr: SymbolName -> (BankNo * uint16) option) (ops: Operation list) : Result<int, string> =
    let push v stack =     
        Ok (v::stack)

    let pop stack = 
        match stack with 
        | top::rest -> 
            Ok (top,rest)
        | [] -> Error "Stack is empty"

    let runOperation (stack: int list) (op: Operation)  =
        let binOp (op: int->int->int) = 
            match pop stack with
            | Ok (b, stack) -> 
                match pop stack with
                | Ok (a, stack) -> 
                    push (op a b) stack
                | Error e -> Error e
            | Error e -> Error e

        let unaryOp (op: int->int) =
            match pop stack with
            | Ok (v, stack) ->
                push (op v) stack
            | Error e -> Error e

        match op with
        | Push p -> push p stack
        | Add -> binOp (+)
        | Sub-> binOp (-)
        | Mult -> binOp (*)
        | BitAnd -> binOp (&&&)
        | BitOr -> binOp (|||)
        | SymAdr name -> 
            match getSymAdr name with
            | Some (_, addr) -> push (int addr) stack
            | None -> Error (sprintf "Unknown Symbol %A" name)
        | SymBank name ->
            match getSymAdr name with
            | Some (bank, _) -> push bank stack
            | None -> Error (sprintf "Unknown Symbol %A" name)
        | CurAdr ->
            push (int curAdr) stack
        | Hi -> unaryOp (fun v -> ((v>>>8)&&&0xFF))
        | Lo -> unaryOp (fun v -> v&&&0xFF)




    ops 
    |> FoldResults runOperation List.Empty
    |> Result.bind pop
    |> Result.map (fun (v, _) -> v)