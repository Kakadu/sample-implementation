open GT

@type 'l t = 
    R 
  | W 
  | L  of string 
  | S  of string 
  | B  of (int -> int -> int) * string
  | E
  | C  of int
  | J  of 'l
  | JT of 'l
  | JF of 'l with show, html, map

module Lexer =
  struct

    let r = Ostap.Matcher.Token.repr

    ostap (
      label: x:LABEL {r x};
      ident: x:IDENT {r x};
      literal: x:LITERAL {int_of_string (r x)} 
    )

    class t s = 
      let skip = Ostap.Matcher.Skip.create [
                   Ostap.Matcher.Skip.whitespaces " \t"; 
                   Ostap.Matcher.Skip.nestedComment "(*" "*)";
                   Ostap.Matcher.Skip.lineComment "--"
                 ] 
      in
      let ident   = Re_str.regexp "[a-zA-Z_]\([a-zA-Z_0-9]\)*\\b"    in 
      let label   = Re_str.regexp "\\$\([a-zA-Z_0-9]\)+\\b" in
      let literal = Re_str.regexp "[0-9]+"                           in
      let newline = Re_str.regexp "[\n\r]+"                          in
      object (self)
        inherit Ostap.Matcher.t s 
        method skip p coord = skip s p coord
        method getIDENT     = self#get "identifier" ident
        method getLABEL     = self#get "label"      label
        method getLITERAL   = self#get "literal"    literal       
        method getNEWLINE   = self#get "newline"    newline  
      end

  end

exception No_label of string

let resolve p = 
  let symbols = ref [] in
  let p = Array.mapi (fun i (s, c) -> if s != "" then symbols := (s, i) :: !symbols; c) p in
  Array.map 
    (fun i -> 
       transform(t) 
  	 (fun _ i -> try List.assoc i !symbols with Not_found -> raise (No_label i)) 
	 new @map[t] 
	 () 
	 i
    ) 
    p

ostap (
  insn: "R"  {R} | 
        "W"  {W} | 
        "E"  {E} |
        "L"  x:!(Lexer.ident)   {L  x} |
        "S"  x:!(Lexer.ident)   {S  x} |
        "J"  l:!(Lexer.label)   {J  l} | 
        "JT" l:!(Lexer.label)   {JT l} | 
        "JF" l:!(Lexer.label)   {JF l} |
        "C"  x:!(Lexer.literal) {C  x} | 
        "B"  op:("+" | "-" | "*" | "/" | "%" | ">=" | ">" | "<=" | "<" | "==" | "!=" | "&&" | "||") {
           let op       = Lexer.r op in
           let ib f x y = if f x y then 1 else 0 in
           B (List.assoc op ["+" , (+);
                             "-" , (-);
                             "*" , ( * );
                             "/" , (/);
                             "%" , (mod);
                             ">" , ib (>);
                             "<" , ib (<);
                             ">=", ib (>=);
                             "<=", ib (<=);
                             "==", ib (==);
                             "!=", ib (!=);
                             "&&", (fun x y -> if x != 0 && y != 0 then 1 else 0);
                             "||", (fun x y -> if x != 0 || y != 0 then 1 else 0) 
                            ], op) 
        };
  line : l:(!(Lexer.label) -":")? i:insn {match l with Some l -> (l, i) | _ -> ("", i)};
  parse: NEWLINE? h:line t:(-NEWLINE line)* NEWLINE? EOF {resolve (Array.of_list (h::t))}
)

let toString i = 
  let b = Buffer.create 1024 in
  Array.iter (fun i ->
    Buffer.add_string b (transform(t) (fun _ i -> string_of_int i) (new @show[t]) () i);
    Buffer.add_string b "\n";
  ) i;
  Buffer.contents b

type env  = int list * (string -> int) * int

class interpret =
  object (this)
    inherit [int, env, int, env, env option] @t 
    method c_R (s, m, p) _ =
      Printf.printf "< "; 
      flush stdout;
      let y = int_of_string (input_line stdin) in
      Some (y::s, m, p+1)
    method c_W (x::s, m, p) _ = 
      Printf.printf "> %d\n" x; 
      flush stdout;
      Some (s, m, p+1)
    method c_L  (      s, m, p) _ x   = Some ((m x)::s, m, p+1)
    method c_S  (   y::s, m, p) _ x   = Some (s, State.modify m x y, p+1)
    method c_B  (y::z::s, m, p) _ f _ = Some ((f z y)::s, m, p+1)
    method c_E   _ _                  = None
    method c_C  (      s, m, p) _ n   = Some (n::s, m, p+1)
    method c_J  (      s, m, p) _ n   = Some (s, m, n.x)
    method c_JT (   x::s, m, p) _ n   = Some (s, m, if x != 0 then n.x else p+1)
    method c_JF (   x::s, m, p) _ n   = Some (s, m, if x  = 0 then n.x else p+1)   
  end

class debug callback =
  object (this)
    inherit interpret as super
    method c_R  c i     = callback i c; super#c_R  c i
    method c_W  c i     = callback i c; super#c_W  c i
    method c_L  c i x   = callback i c; super#c_L  c i x
    method c_S  c i x   = callback i c; super#c_S  c i x
    method c_B  c i x y = callback i c; super#c_B  c i x y
    method c_E  c i     = callback i c; super#c_E  c i 
    method c_C  c i x   = callback i c; super#c_C  c i x
    method c_J  c i x   = callback i c; super#c_J  c i x
    method c_JT c i x   = callback i c; super#c_JT c i x
    method c_JF c i x   = callback i c; super#c_JF c i x
  end

let interpret ii p =
  let rec inner (_, _, i) as conf  =
    match transform(t) (fun _ i -> i) ii conf p.(i) with
    | None      -> ()
    | Some conf -> inner conf
  in
  inner ([], State.empty, 0)

let run p = interpret (new interpret) p
  
