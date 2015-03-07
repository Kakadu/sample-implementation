module M = Map.Make (String)

type 'a t = 'a M.t

let empty           = M.empty
let modify s name x = M.add name x s
let get s name      = M.find name s

