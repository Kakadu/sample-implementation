open E

let parse source =
  let source = Js.to_string source in
  match E.toplevel source with
  | Checked.Ok p ->
      Js.string (View.toString p#print)
  | Checked.Fail [msg] -> 
      let default = HTMLView.string (HTMLView.escape (Ostap.Msg.toString msg)) in
      let info = 
         match Ostap.Msg.loc msg with
         | Ostap.Msg.Locator.Point (line, col) ->
            let source = View.string (HTMLHighlighting.perform [((line, col), (line, col)), "<font color=red>", "</font>"] source) in
            let string = HTMLView.string (Ostap.Msg.string msg) in
            HTMLView.seq [source; HTMLView.br; string]
         | _ -> default
      in
      Js.string (HTMLView.toHTML info)
      
  
let _ = 
  (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse


