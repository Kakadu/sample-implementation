type t = string -> int

let empty           = fun x     -> invalid_arg (Printf.sprintf "variable \"%s\" undefined" x)
let modify s name x = fun name' -> if name = name' then x else s name'