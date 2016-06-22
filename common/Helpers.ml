type loc  = <loc : Ostap.Msg.Locator.t>
type poly = {f : 'a . 'a -> string}

class h = 
  let t = Trap.empty () in
  object 
    method reassign : 'a . 'a -> HTMLHighlighting.pos -> HTMLHighlighting.pos -> 'a =
      fun x p1 p2 -> Trap.attach t x (p1, p2); x

    method register : 'a . 'a -> loc -> loc -> 'a =
      fun x l r ->       
        let loc x =
          match x#loc with
          | Ostap.Msg.Locator.Point p -> p
          | _ -> HTMLHighlighting.nop
        in
        Trap.attach t x (loc l, let (l, c) = loc r in l, c-1); x

    method retrieve : 'a . 'a -> HTMLHighlighting.interval = fun x -> Trap.locate t x
  end


let highlighting () = new h

let interval cb (h : h) = {f = 
  fun t -> 
    if cb = "" then ""
    else  
      let ((x, y), (z, t)) = h#retrieve t in
      Printf.sprintf "onclick=\"%s ('%d', '%d', '%d', '%d')\"" cb x y z t 
}
      
ostap (
  loc[register][item]: l:($) x:item r:($) {
     register x l r
  }
)

class cname =
  object
    method cname name =
      String.uncapitalize (
        if name.[0] = '`' 
        then String.sub name 1 (String.length name - 1)
        else name
      )
      
  end

class ['a] wrap cb pretty =
  object
    method bullet = HTML.raw "&#8226;"
    method wrap (node : 'a) html =
      HTML.tag "attr" 
        ~attrs:(Printf.sprintf "%s style=\"cursor:pointer\" title=\"%s\"" (cb.f node) (pretty node)) 
         html
  end

let concat = List.fold_left (^) ""

let rec intersperse x = function 
| []    -> []
| [h]   -> [h]
| h::tl -> h :: x :: intersperse x tl

class names =
  let letters = Array.to_list (Array.init 26 (fun i -> String.make 1 (Char.chr (Char.code 'a' + i)))) in
  object (this)
    val words  = ref [""] 
    val buffer = ref []   
    val h      = Hashtbl.create 32
    method get : int -> string = fun i ->
      try Hashtbl.find h i with
	Not_found ->
	  let n = this#fresh_name in
	  Hashtbl.add h i n;
	  n      
    method fresh_name =
      match !buffer with
      | [] ->     
         let new_words =
           List.rev (
             List.fold_left (fun acc suffix -> 
               List.fold_left (fun acc prefix -> (prefix ^ suffix)::acc) acc letters
             ) 
             [] 
             !words
           )
         in
         words  := new_words;
         buffer := List.tl new_words;
         List.hd new_words
      | h::t -> buffer := t; h
  end
