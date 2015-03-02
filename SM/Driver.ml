open Printf
open Ostap.Util
open Settings
open List
open Lazy

let _ =
  let options = 
    customize (empty ()) [
      "p", "print", String, Optional , "\t --- pretty-print file.";
      "r", "run"  , Switch, Mandatory, "\t --- run program.";
      "h", "help" , Switch, Mandatory, "\t --- show help on options."
    ]
    (fun _ -> [])
  in
  let _ :: args = Array.to_list Sys.argv in  
  printf "SM-interpreter/printer.\n";
  printf "(C) Dmitry Boulytchev, St.Petersburg State University, 2013-2015.\n\n";
  let fileOps = function 
  | Str f when f <> "" -> open_out f, close_out 
  | _ -> stdout, fun _ -> () 
  in
  let fromString p s =
    Ostap.Combinators.unwrap (p (new SM.Lexer.t s)) (fun x -> Checked.Ok x) 
      (fun (Some err) ->
         let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
         let m =  match m with `Msg m -> m | `Comment (s, _) -> Ostap.Msg.make s [||] loc in
         Checked.Fail [m]
      )
  in
  match options args with
  | Ok (conf, files) -> 
      (match conf.get "h" with Some _ -> printf "%s\n" (conf.help ()) | _ -> ());
      iter (fun file -> 
              let bf = match conf.get "b" with Some _ -> false | _ -> true in
              match fromString SM.parse (read file) with
              | Checked.Ok p -> 
                  (match conf.get "p" with                     
                   | None   -> ()
                   | Some f -> 
                       let ch, cf = fileOps f in
                       fprintf ch "%s\n" (SM.toString p);
                       cf ch;
                  );
                  (match conf.get "r" with
                   | None   -> ()
                   | Some _ -> ignore (SM.run p)
                  );
              | Checked.Fail [msg] -> eprintf "Errors: %s\n" (Ostap.Msg.toString msg)
           ) files
  | Warnings (conf, _, warnings) ->
      eprintf "Error parsing command-line arguments:\n";
      iter (fun s -> eprintf "   %s\n" s) warnings

