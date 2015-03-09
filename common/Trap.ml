module XHash = Hashtbl.Make (
  struct 
    type t
    let equal = (==)
    let hash = Hashtbl.hash 
  end
 )

let empty () = (XHash.create 1024 : HTMLHighlighting.interval XHash.t)
let attach : HTMLHighlighting.interval XHash.t -> 'a -> HTMLHighlighting.interval -> unit = fun t a i -> XHash.add t (Obj.magic a) i
let locate : HTMLHighlighting.interval XHash.t -> 'a -> HTMLHighlighting.interval = fun t a -> try XHash.find t (Obj.magic a) with Not_found -> HTMLHighlighting.none
