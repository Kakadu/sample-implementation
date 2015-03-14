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
      "r", "run"    , String, Optional,  " [<output file>]\t --- run program.";
      "g", "gen"    , String, Optional , " [<output file>]\t --- generate vertical representation.";
      "c", "compile", String, Optional , " [<output file>]\t --- compile to stack machine code.\n";
      "h", "help"   , Switch, Mandatory, "\t --- show help on options."
    ]
    (fun _ -> [])
  in
  let _ :: args = Array.to_list Sys.argv in  
  printf "E-interpreter/pretty-printer/evaluator.\n";
  printf "(C) Dmitry Boulytchev, St.Petersburg State University, 2015.\n\n";
  let fileOps = function 
  | Str f when f <> "" -> open_out f, close_out 
  | _ -> stdout, fun _ -> () 
  in
  match options args with
  | Ok (conf, files) -> 
      (match conf.get "h" with Some _ -> printf "%s\n" (conf.help ()) | _ -> ());
      let toplevels = [|
        E.toplevel
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
              match toplevel (read file) with
              | Checked.Ok p -> 
                  (match conf.get "p" with                     
                   | None   -> ()
                   | Some f -> 
                       let ch, cf = fileOps f in
                       fprintf ch "%s\n" p#vertical;
                       cf ch;
                  );
                  (match conf.get "g" with
                   | None -> ()
                   | Some f ->
                       let ch, cf = fileOps f in
                       fprintf ch "%s" p#code; 
                       cf ch
                  );
                  (match conf.get "c" with
                   | None -> ()
                   | Some f ->
                       let ch, cf = fileOps f in
                       fprintf ch "%s" p#compile; 
                       cf ch
                  );
                  (match conf.get "r" with
                   | None   -> ()
                   | Some f -> 
                       let ch, cf = fileOps f in
                       fprintf ch 
                         "<html><head>%s%s</head><body onload=\"convertTree(document.getElementById(\"root\"), false)\"><div style=\"transform:scaleY(-1)\"><ul id=\"root\" class=\"mktree\">%s</ul></div><body></html>"
                         "<script type=\"text/javascript\" src=\"mktree.js\"></script>"
                         "<link rel=\"stylesheet\" href=\"mktree.css\" type=\"text/css\">"
                         p#run; 
                       cf ch
                  );
              | Checked.Fail [msg] -> eprintf "Errors: %s\n" (Ostap.Msg.toString msg)
           ) files
      with Invalid_argument arg -> eprintf "Error: %s\n" arg
      )
  | Warnings (conf, _, warnings) ->
      eprintf "Error parsing command-line arguments:\n";
      iter (fun s -> eprintf "   %s\n" s) warnings

