module Utils

let CollectResults (l : Result<'T, 'e> list) : Result<'T list, 'e> =
    let folder value curList =
        match curList with 
        | Error e -> Error e
        | Ok lst ->
            match value with 
            | Error e -> Error e
            | Ok v -> Ok (v :: lst)
    List.foldBack folder l (Ok List.empty)

let FoldResults<'a, 'b, 'e> (f: 'b->'a->Result<'b,'e>) (start:'b) (items : 'a list) : Result<'b, 'e> =
    let rec walkitems s items =
        match items with
        | head::rest -> 
            let next = f s head
            match next with
            | Ok n -> walkitems n rest
            | x -> x
        | [] -> Ok s
    walkitems start items