let highlighting () =
  let t = Trap.empty () in
  object 
    method register x l r = 
      let loc x =
         match x#loc with
         | Ostap.Msg.Locator.Point p -> p
         | _ -> HTMLHighlighting.nop
      in
      Trap.attach t x (loc l, let (l, c) = loc r in l, c-1); x
    method retrieve x = Trap.locate t x
    method reassign x p1 p2 = Trap.attach t x (p1, p2); x
  end

let interval cb h t = 
  if cb = "" then ""
  else  
    let ((x, y), (z, t)) = h t in
    Printf.sprintf "onclick=\"%s ('%d', '%d', '%d', '%d')\"" cb x y z t 
        
ostap (
  loc[register][item]: l:($) x:item r:($) {
     register x l r
  }
)

