let proxy obj = fun (s : string) -> Js.to_string (Js.Unsafe.get obj (Js.string s))
  
let string_array sa =
  let a = jsnew Js.array_empty () in
  Array.iteri (fun i x -> Js.array_set a i (Js.string x)) sa;
  a

let highlighted_msg source msg =
  match Ostap.Msg.loc msg with
  | Ostap.Msg.Locator.Point p ->
     HTMLHighlighting.perform [HTMLHighlighting.error_item p] (source ^ " "), HTML.escape (Ostap.Msg.string msg)
  | _ -> HTMLHighlighting.perform [] source, HTML.escape (Ostap.Msg.toString msg)

let setHTML elem str =
  let target = Js.Unsafe.fun_call (Js.Unsafe.variable "document.getElementById") [|Js.Unsafe.inject (Js.string elem)|] in
  target##innerHTML <- Js.string str

let js_nav nav i obj =
  Js.number_of_float (float_of_int (nav (int_of_float (Js.float_of_number i)) (proxy obj)))

let error page input source msg =
  let source, msg = highlighted_msg source msg in
  setHTML "runmsg" msg; 
  try setHTML (page#id input) source with Not_found _ -> ()

let show_results root tree descr =
  Js.Unsafe.fun_call (Js.Unsafe.variable "window.show_results") [|
    Js.Unsafe.inject (Js.string root); 
    Js.Unsafe.inject (Js.string tree); 
    Js.Unsafe.inject (Js.string (descr ^ ".pdf"))
  |]

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
             fun id target ->                
               let id, target  = Js.to_string id, Js.to_string target in
               let root        = p#run "do_highlighting" (object method results = show_results method error = error end) in
               let wizard, nav = Toplevel.Wizard.make id target "navigate" root in
               (Js.Unsafe.coerce Dom_html.window)##navigate <- Js.wrap_callback (js_nav nav);
               let entry, code = wizard#generate in
               string_array [|entry; code|]
          );
          string_array [|"1"; p#ast "do_highlighting"|]
      
      | Checked.Fail [msg] -> 
          let source, msg = highlighted_msg source msg in
          string_array [|"0"; msg; source|]
  
    let _ = 
      (Js.Unsafe.coerce Dom_html.window)##parse <- Js.wrap_callback parse

  end



