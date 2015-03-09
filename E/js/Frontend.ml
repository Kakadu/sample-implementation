open E

let parse source =
  let source = Js.to_string source in
  match E.toplevel source with
  | Checked.Ok p ->
      Js.string (View.toString (p#ast ""))
  | Checked.Fail [msg] -> 
      let default = HTMLView.string (HTMLView.escape (Ostap.Msg.toString msg)) in
      let info = 
         match Ostap.Msg.loc msg with
         | Ostap.Msg.Locator.Point p ->
            let source = View.string (HTMLHighlighting.perform [HTMLHighlighting.error_item p] (source ^ "|")) in
            let string = HTMLView.string (Ostap.Msg.string msg) in
            HTMLView.seq [source; string]
         | _ -> default
      in
      Js.string (HTMLView.toHTML info)
      
  
let _ = 
  (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse



