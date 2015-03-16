let proxy obj = fun (s : string) -> Js.to_string (Js.Unsafe.get obj (Js.string s))
  
let string_array sa =
  let a = jsnew Js.array_empty () in
  Array.iteri (fun i x -> Js.array_set a i (Js.string x)) sa;
  a

let highlighted_msg source msg =
  let default = HTMLView.string (HTMLView.escape (Ostap.Msg.toString msg)) in
  let info = 
    match Ostap.Msg.loc msg with
    | Ostap.Msg.Locator.Point p ->
        let source = View.string (HTMLHighlighting.perform [HTMLHighlighting.error_item p] (source ^ " ")) in
        let string = HTMLView.string (Ostap.Msg.string msg) in
        HTMLView.seq [source; string]
    | _ -> default
  in
  HTMLView.toHTML info

module Make (T : sig val toplevel : string -> (Toplevel.c, Ostap.Msg.t) Checked.t end) =
  struct

    let parse source =
      (Js.Unsafe.coerce Dom_html.window)##highlight <- Js.wrap_callback (fun () -> Js.string "");
      let source = Js.to_string source in
      match T.toplevel source with
      | Checked.Ok p ->
          (Js.Unsafe.coerce Dom_html.window)##highlight <- Js.wrap_callback (
             fun x y z t -> 
               let to_int x = int_of_string (Js.to_string x) in
               let x, y, z, t = to_int x, to_int y, to_int z, to_int t in
               Js.string (HTMLHighlighting.perform [HTMLHighlighting.subtree_item (x, y) (z, t)] source)
          );
          (Js.Unsafe.coerce Dom_html.window)##vertical <- Js.wrap_callback (
             fun () -> Js.string p#vertical
          );
          (Js.Unsafe.coerce Dom_html.window)##run <- Js.wrap_callback (
             fun id target navigate -> 
               let id, target, navigate = Js.to_string id, Js.to_string target, Js.to_string navigate in
               let wizard, callback = p#run "do_highlighting" in
               (Js.Unsafe.coerce Dom_html.window)##interpret <- Js.wrap_callback (
                  fun cr -> 
                    let root, tree = callback (proxy cr) in
                    string_array [|root; tree|]
               );
               let entry, code = HTMLView.Wizard.render id target navigate wizard in
               string_array [|entry; code|]
          );
          string_array [|"1"; p#ast "do_highlighting"|]
      
      | Checked.Fail [msg] -> string_array [|"0"; highlighted_msg source msg|]
  
    let _ = 
      (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse

  end



