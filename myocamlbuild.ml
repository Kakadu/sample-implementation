open Ocamlbuild_plugin
open Command
open Printf

let ocamlfind_query pkg =
  let cmd = Printf.sprintf "ocamlfind query %s" (Filename.quote pkg) in
  Ocamlbuild_pack.My_unix.run_and_open cmd (fun ic ->
      printf "Getting Ocaml directory from command %s" cmd;
      input_line ic
    )

let _ = dispatch Ocamlbuild_js_of_ocaml.dispatcher

(* let _ = dispatch begin function *)
(*   | After_rules -> *)
(*      flag ["ocamldep"; "ocaml"; "use_gt_plugins"] *)
(*           (S [ A"syntax"; A"camlp5o" *)
(*              ; A"-ppopt"; A (ocamlfind_query "GT") *)
(*              ]) *)

(*   | _ -> () *)
(* end *)
