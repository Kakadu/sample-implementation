open Printf
open Ostap.Util
open Settings
open List
open Lazy

let _ =
  let options = 
    customize (empty ()) [
      "l", "level"  , Number, Optional , " [<language level>]\t --- set language level (0 --- default).";
      "p", "print"  , String, Optional , " [<output file>]\t --- pretty-print file.";
      "r", "run"    , Switch, Mandatory, "\t --- run program.";
      "g", "gen"    , String, Optional , " [<output file>]\t --- generate vertical representation.";
      "c", "compile", String, Optional , " [<output file>]\t --- compile to stack machine code.\n";
      "h", "help"   , Switch, Mandatory, "\t --- show help on options."
    ]
    (fun _ -> [])
  in
  let _ :: args = Array.to_list Sys.argv in  
  printf "L-interpreter/pretty-printer/evaluator.\n";
  printf "(C) Dmitry Boulytchev, St.Petersburg State University, 2013.\n\n";
  let fileOps = function 
  | Str f when f <> "" -> open_out f, close_out 
  | _ -> stdout, fun _ -> () 
  in
  let fromString p s =
    Ostap.Combinators.unwrap (p (new L.Lexer.t s)) (fun x -> Checked.Ok x) 
      (fun (Some err) ->
         let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
         let m =  match m with `Msg m -> m | `Comment (s, _) -> Ostap.Msg.make s [||] loc in
         Checked.Fail [m]
      )
  in
  match options args with
  | Ok (conf, files) -> 
      (match conf.get "h" with Some _ -> printf "%s\n" (conf.help ()) | _ -> ());
      let toplevels = [|
        L.Program.toplevel;
        Extensions.Arrays.Stmt.toplevel
      |]
      in
      let level = 
        match conf.get "l" with 
        | None -> 0 
        | Some (Int n) -> 
           if n >= 0 & n < Array.length toplevels 
           then n 
           else (eprintf "Invalid language level %d, defaulting to 0.\n" n; 0)
      in  
      let toplevel = toplevels.(level) in
      (try 
      iter (fun file -> 
              let bf = match conf.get "b" with Some _ -> false | _ -> true in
              match fromString toplevel#parse (read file) with
              | Checked.Ok p -> 
                  (match conf.get "p" with                     
                   | None   -> ()
                   | Some f -> 
                       let ch, cf = fileOps f in
                       fprintf ch "%s\n" (Ostap.Pretty.toString (toplevel#print p));
                       cf ch;
                  );
                  (match conf.get "g" with
                   | None -> ()
                   | Some f ->
                       let ch, cf = fileOps f in
                       List.iter (fun s -> fprintf ch "%s\n" s) (toplevel#code p); 
                       cf ch
                  );
                  (match conf.get "c" with
                   | None -> ()
                   | Some f ->
                       let ch, cf = fileOps f in
                       List.iter (fun s -> fprintf ch "%s" s) (toplevel#compile p); 
                       cf ch
                  );
                  (match conf.get "r" with
                   | None   -> ()
                   | Some _ -> ignore (toplevel#run p)
                  );
                  (match conf.get "m" with
                   | None   -> ()
                   | Some _ -> (* printf "%s\n" (Ostap.Pretty.toString (Print.stmt bf (Mix.stmt p))) *) (* TODO *) ()
                  )
              | Checked.Fail [msg] -> eprintf "Errors: %s\n" (Ostap.Msg.toString msg)
           ) files
      with Invalid_argument arg -> eprintf "Error: %s\n" arg
      )
  | Warnings (conf, _, warnings) ->
      eprintf "Error parsing command-line arguments:\n";
      iter (fun s -> eprintf "   %s\n" s) warnings

