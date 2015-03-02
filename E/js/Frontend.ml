open E

let parse source =
  match E.toplevel (Js.to_string source) with
  | Checked.Ok p ->
      Js.string (View.toString p#print)
  | Checked.Fail [msg] -> 
      Js.string (Printf.sprintf "Errors: %s\n" (Ostap.Msg.toString msg))

let _ = 
  (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse


