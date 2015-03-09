let highlighting () =
  let t = Trap.empty () in
  object 
    method register x l r = 
      let loc x =
         match x#loc with
         | Ostap.Msg.Locator.Point p -> p
         | _ -> HTMLHighlighting.nop
      in
      Trap.attach t x (loc l, loc r); x
    method retrieve x = Trap.locate t x
  end
