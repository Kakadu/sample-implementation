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
            let decorated = Buffer.create 256 in
            let l, c, newline, newcol, mark, marked =
              let l, c, f = ref 1, ref 1, ref false in
              (fun _ -> !l),
              (fun _ -> !c),
              (fun _ -> incr l; c := 1),
              (fun _ -> incr c),
              (fun _ -> f := true),
              (fun _ -> !f)
            in
            String.iter 
              (function 
	       | '\n' -> newline ()
               | x -> if l () = line then 
                      begin
                        if c () = col then Buffer.add_string decorated "<font color=red>";
                        Buffer.add_string decorated (HTMLView.escape (String.make 1 x));
                        if c () = col then begin
                          Buffer.add_string decorated "</font>";
                          mark ()
                        end
                      end;
                      newcol ()               
              ) source;            
            let string = HTMLView.string (Ostap.Msg.string msg) in
            let source = View.string (Buffer.contents decorated ^ if marked () then "" else "<font color=red>|</font>") in
            HTMLView.seq [source; HTMLView.br; string]
         | _ -> default
      in
      Js.string (HTMLView.toHTML info)
      
  
let _ = 
  (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse


