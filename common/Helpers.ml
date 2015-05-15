type loc = <loc : Ostap.Msg.Locator.t>

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

let interval cb (h : h) t = 
  if cb = "" then ""
  else  
    let ((x, y), (z, t)) = h#retrieve t in
    Printf.sprintf "onclick=\"%s ('%d', '%d', '%d', '%d')\"" cb x y z t 
        
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
    method bullet = HTMLView.raw "(&#8226;)"
    method wrap (node : 'a) html =
      HTMLView.tag "attr" 
        ~attrs:(Printf.sprintf "%s style=\"cursor:pointer\" title=\"%s\"" (cb node) (pretty node)) 
         html
  end
