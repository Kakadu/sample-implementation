module M = Map.Make (String)

type 'a t = 'a M.t

let empty           = M.empty
let modify s name x = M.add name x s
let get s name      = M.find name s

let html fa s = 
  let text = 
    "[" ^ 
    (GT.transform(GT.list) 
       (fun _ (x, v) -> Printf.sprintf "%s=%s" x (fa v)) 
       (new @GT.list[show]) 
       () 
       (M.bindings s)
    ) ^ 
    "]" 
  in
  HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" title=\"%s\"" text) 
    (View.string "s")

open Ostap.Util

ostap (
  parse[name][a]: p:list[ostap (name -"=" a)] {
    List.fold_left (fun m (n, v) -> M.add n v m) M.empty p
  }
)
