open E

let parse source =
  (Js.Unsafe.coerce Dom_html.window)##highlight <- Js.wrap_callback (fun () -> Js.string "");
  let source = Js.to_string source in
  match E.toplevel source with
  | Checked.Ok p ->
      (Js.Unsafe.coerce Dom_html.window)##highlight <- Js.wrap_callback (
         fun x y z t -> 
           let to_int x = int_of_string (Js.to_string x) in
           let x, y, z, t = to_int x, to_int y, to_int z, to_int t in
           Js.string (HTMLHighlighting.perform [HTMLHighlighting.subtree_item (x, y) (z, t)] source)
      );
      (Js.Unsafe.coerce Dom_html.window)##vertical <- Js.wrap_callback (
         fun () -> Js.string (View.toString p#print)
      );
      Js.string (View.toString (p#ast "do_highlighting"))
      
  | Checked.Fail [msg] -> 
      let default = HTMLView.string (HTMLView.escape (Ostap.Msg.toString msg)) in
      let info = 
         match Ostap.Msg.loc msg with
         | Ostap.Msg.Locator.Point p ->
            let source = View.string (HTMLHighlighting.perform [HTMLHighlighting.error_item p] (source ^ " ")) in
            let string = HTMLView.string (Ostap.Msg.string msg) in
            HTMLView.seq [source; string]
         | _ -> default
      in
      Js.string (HTMLView.toHTML info)
      
  
let _ = 
  (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse



