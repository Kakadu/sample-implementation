type pos      = int * int
type interval = pos * pos
type item     = interval * string * string
type request  = item list

let nop          = (0, 0)
let none         = (nop, nop)

let empty        = []
let add_item i r = i :: r

let error_item p = (p, p), "<span style=\"background-color:red\">", "</span>"
let subtree_item p1 p2 = (p1, p2), "<div style=\"background-color:lavender; display:inline\">", "</div>"

let perform r source =
  let decorated = Buffer.create 1024 in
  Buffer.add_string decorated "<pre class=\"inline\">";
  let opens, closes = List.fold_left 
    (fun (opens, closes) ((first_pos, last_pos), open_string, close_string) ->
       (first_pos, open_string)::opens,
       (last_pos, close_string)::closes
     ) ([], []) r
  in
  let compare ((l1, c1), _) ((l2, c2), _) = 
  let l = l1 - l2 in if l = 0 then c1 - c2 else l in
  let requests = List.sort compare opens, List.sort (fun a b -> - (compare a b)) closes in
  let newline (l, c) = (l+1, 1) in
  let newcol  (l, c) = (l, c+1) in
  let n = String.length source in
  let rec process (opens, closes) p i =
    if i < n then begin
      let x = source.[i] in
      let opens' = match opens with
      | [] -> []
      | (po, o)::tl ->
          if po = p then (Buffer.add_string decorated o; tl) else opens
      in
      Buffer.add_string decorated (HTML.escape (String.make 1 x));
      let closes' = match closes with
      | [] -> []
      | (pc, c)::tl ->
          if pc = p then (Buffer.add_string decorated c; tl) else closes
      in
      let p' = match source.[i] with
      | '\n' -> newline p
      | _ -> newcol p
      in
      process (opens', closes') p' (i+1)
    end
  in
  process requests (1, 1) 0;
  Buffer.add_string decorated "</pre>";
  Buffer.contents decorated


