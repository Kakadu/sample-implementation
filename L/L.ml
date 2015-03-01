open GT
open Ostap.Pretty

let w p px x = if px < p then rboxed x else x 

let b l = hboxed  (listBySpaceBreak l)
let v l = hvboxed (listBySpaceBreak l)
let c l = cboxed  (vboxed (listByBreak l))

module Lexer =
  struct

    let r = Ostap.Matcher.Token.repr

    let keyword s = 
      try ignore (List.find (fun x -> x = s) ["while"; "do"; "if"; "then"; "else"; "skip"; "read"; "write"]);
          true
      with Not_found -> false

    ostap (
      ident: x:IDENT =>{not (keyword (r x))}=> {r x};
      literal: x:LITERAL {int_of_string (r x)} 
    )

    class t s = 
      let skip = Ostap.Matcher.Skip.create [
                   Ostap.Matcher.Skip.whitespaces " \n\t\r"; 
                   Ostap.Matcher.Skip.nestedComment "(*" "*)";
                   Ostap.Matcher.Skip.lineComment "--"
                 ] 
      in
      let ident   = Str.regexp "[a-zA-Z_]\([a-zA-Z_0-9]\)*\\b" in 
      let literal = Str.regexp "[0-9]+" in
      object (self)
        inherit Ostap.Matcher.t s 
        method skip p coord = skip s p coord
        method getIDENT     = self#get "identifier" ident
        method getLITERAL   = self#get "literal"    literal         
      end

    let fromString p s =
      Ostap.Combinators.unwrap (p (new t s)) (fun x -> Checked.Ok x) 
        (fun (Some err) ->
           let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
           let m =  match m with `Msg m -> m | `Comment (s, _) -> Ostap.Msg.make s [||] loc in
           Checked.Fail [m]
        )
  
  end

module Expr =
  struct

    @type 'self t = [  
        `Var   of string 
      | `Const of int
      | `Binop of (int -> int -> int) * string * 'self * 'self
    ]

    let prio = 
      let a = [
        "||", 3; 
        "&&", 4; 
        "==", 5; "!=", 5; "<=", 5; "<", 5; ">=", 5; ">", 5; 
        "+", 6; "-", 6; 
        "*", 7; "/", 7; "%", 7
      ] 
      in
      function `Binop (_, s, _, _) -> List.assoc s a | _ -> 8

    class ['self] eval =
      object (this)
        inherit ['self, int, State.t, int] @t
        method c_Var   s _ x       = s x
        method c_Const _ _ n       = n
        method c_Binop s _ f _ x y = f (x.fx s) (y.fx s)
      end

    class ['self] print =
      object (this)
        inherit ['self, printer * int, unit, printer * int] @t 
        method c_Var   _ e x = string x, prio ~:e
        method c_Const _ e x = int x, prio ~:e
        method c_Binop _ e _ op x y = 
          let x, px = x.fx () in
          let y, py = y.fx () in 
          let p = prio ~:e in b [w p px x; string op; w p py y], p
      end

    class ['self] code =
      object (this)
        inherit ['self, string list, unit, string list] @t
        method c_Var   _ _ x       = ["x"; x]
        method c_Const _ _ x       = ["!"; string_of_int x] 
        method c_Binop _ _ _ o x y = ["@"; o] @ List.flatten [x.fx (); y.fx ()]
      end

    let rec parse primary s =  
      let l = List.map (fun (s, t) -> ostap(- $(s)), fun x y -> `Binop (t, s, x, y)) in
      let ior  x y = abs x + abs y in
      let iand x y = abs (x * y) in
      let b f = fun x y -> if f x y then 1 else 0 in
      Ostap.Util.expr (fun x -> x) [|
        `Lefta, l ["||", ior];
        `Lefta, l ["&&", iand];
        `Nona , l ["==", b(=); "!=", b(<>); "<=", b(<=); "<", b(<); ">=", b(>=); ">", b(>)];
        `Lefta, l ["+" , ( +  ); "-" , (-)];
        `Lefta, l ["*" , ( *  ); "/" , (/ ); "%" , (mod)];
      |]
      (primary (parse primary))
      s

  end

module Stmt =
  struct

    @type ('self, 'e) t = [
        `Skip 
      | `Assign of string * 'e
      | `Read   of string
      | `Write  of 'e
      | `If     of 'e * 'self * 'self
      | `While  of 'e * 'self  
      | `Seq    of 'self * 'self 
    ] 

    class ['self, 'e] interpret =
      object (this)
        inherit ['self, State.t, 'e Expr.t, int, State.t, State.t] @t         
        method c_Skip s _ = s
        method c_Assign s _ x e = State.modify s x (e.fx s)
        method c_Read s _ x = 
          Printf.printf "%s < " x; 
          flush stdout;
          let y = int_of_string (input_line stdin) in
          State.modify s x y
        method c_Write s _ e = 
          Printf.printf "> %d\n" (e.fx s); 
          flush stdout;
          s
        method c_If s _ e s1 s2 = (if e.fx s = 0 then s2 else s1).fx s
        method c_While s t e s1 = if e.fx s = 0 
                                     then s 
                                     else s1.f s (`Seq (~:s1, ~:t))
        method c_Seq s _ s1 s2 = s2.fx (s1.fx s)
      end

    class ['self, 'e] print =
      object (this)
        inherit ['self, printer, 'e Expr.t, printer, unit, printer] @t
        method c_Skip   _ _       = string "skip"
        method c_Assign _ _ x e   = v [string x; string ":="; e.fx ()]
        method c_If     _ _ c x y = v [string "if"; c.fx (); v [string "then"; x.fx (); string "else"; y.fx ()]]
        method c_While  _ _ c x   = v [v [string "while"; c.fx ()]; v [string "do"; x.fx ()]]
        method c_Seq    _ _ x y   = c [seq [x.fx (); string ";"]; y.fx ()]
        method c_Read   _ _ x     = v [string "read"; rboxed (string x)]
        method c_Write  _ _ e     = v [string "write"; rboxed (e.fx ())]
      end

    class ['self, 'e] code =
      object (this)
        inherit ['self, string list, 'e, string list, unit, string list] @t
        method c_Skip   _ _       = ["s"]
        method c_Seq    _ _ x y   = ";" :: (x.fx ()) @ (y.fx ())
        method c_Assign _ _ x e   = "=" :: x :: (e.fx ())
        method c_While  _ _ c s   = "l" :: (c.fx ()) @ (s.fx ())
        method c_If     _ _ c x y = "i" :: (c.fx ()) @ (x.fx ()) @ (y.fx ())
        method c_Read   _ _ x     = ["r"; x]
        method c_Write  _ _ e     = "w" :: (e.fx ())
      end

    ostap (
      ident    : !(Lexer.ident);
      key[name]: @(name ^ "\\b" : name);
      parse[expr][stmt]: 
        x:ident ":=" e:expr                                                               {`Assign (x, e)}
      | key["skip"]                                                                       {`Skip}
      | key["read" ] "(" x:ident ")"                                                      {`Read x}
      | key["write"] "(" e:expr ")"                                                       {`Write e}
      | key["if"] c:expr key["then"] x:parse[expr][stmt] key["else"] y:parse[expr][stmt]  {`If (c, x, y)}
      | key["while"] c:expr key["do"] s:parse[expr][stmt]                                 {`While (c, s)}
      | -"{" -s:parse[expr][stmt] -";" seqs[s][expr][stmt] -"}"
      | stmt[parse expr stmt];                                                          
      seqs[acc][expr][stmt]: s:parse[expr][stmt] t:(-";" seqs[`Seq (acc, s)][expr][stmt])? {
        match t with Some t -> t | None -> `Seq (acc, s)
      }
    )

  end

module Compiler =
  struct

    let force                 = function `Maybe n -> `Yes n | `Yes n -> `Yes n
    let first l ((h::t) as p) = match l with `Yes n -> (Printf.sprintf "$%d:%s" n h) :: t | `No -> p
    let last  l p             = match l with `Yes n -> p @ [Printf.sprintf "\tJ $%d\n" n] | `Maybe _ -> p
    let frame f l p           = last l (first f p)

    module Expr =
      struct
        include Expr

        class ['e] compile =
          object (this)
            inherit ['e, string list, [`Yes of int | `No], string list] @t
            method c_Var   l _ x       = first l [Printf.sprintf "\tL %s\n" x]
            method c_Const l _ n       = first l [Printf.sprintf "\tC %d\n" n]
            method c_Binop l _ f o x y = (x.fx l) @ (y.fx `No) @ [Printf.sprintf "\tB %s\n" o]
          end
     
      end

    module Stmt =
      struct
        include Stmt

        type env = [`Yes of int | `No] * [`Yes of int | `Maybe of int] * int

        class ['self, 'e] compile =
          object (this)
            inherit ['self, string list * int, 'e Expr.t, string list, env, string list * int] @t
            method c_Skip (this, next, last) _  = 
              (match this, next with 
               | `No   , `Maybe n            -> []
               | `No   , `Yes   n            -> [Printf.sprintf "\tJ $%d\n" n]
               | `Yes n, (`Yes m | `Maybe m) -> [Printf.sprintf "$%d:\tJ $%d\n" n m]
              ), last
            method c_Seq ((this, next, last) as env) _ s1 s2 =
              match ~:s1 with
              | `Skip -> s2.fx env
              | _     -> match ~:s2 with
                         | `Skip -> s1.fx env
                         | _     ->
                             let s1', last'  = s1.fx (this, `Maybe (last+1), last+1) in
                             let s2', last'' = s2.fx (`Yes (last+1), next, last') in
                             s1' @ s2', last''
            method c_Assign ((this, next, l) as env) _ x e = 
              last next ((e.fx env) @ [Printf.sprintf "\tS %s\n" x]), l
            method c_Read (this, next, last) _ x = 
              frame this next ["\tR\n"; Printf.sprintf "\tS %s\n" x], last
            method c_Write ((this, next, l) as env) _ e = 
              last next ((e.fx env) @ ["\tW\n"]), l
            method c_If ((this, next, last) as env) _ e s1 s2 =
              let s2', last'  = s2.fx (`No, force next, last+1) in
              let s1', last'' = s1.fx (`Yes (last+1), next, last') in
              List.flatten [
                e.fx env; 
                [Printf.sprintf "\tJT $%d\n" (last+1)];
                s2';
                s1'
              ], last''
            method c_While ((this, next, last) as env) _ e s =
              let s', last' = s.fx (`Yes (last+2), `Maybe (last+1), last+2) in
              frame this next (List.flatten [[Printf.sprintf "\tJ $%d\n" (last+1)];
                                             s';
                                             e.fx (`Yes (last+1), next, last);
                                             [Printf.sprintf "\tJT $%d\n" (last+2)]
                                            ]), last'
          end

      end

    let compile p =
      let rec compile i p = 
        transform(Stmt.t)
          compile
          (fun (this, _, _) expr -> 
             let rec compile i e = transform(Expr.t) compile (new Expr.compile) i e in
             compile this expr
          )
          (new Stmt.compile)
          i
          p
      in
      let code, _ = compile (`No, `Maybe 0, 0) p in
      code @ ["$0:\tE\n"]

  end

module Program =
  struct

    type ('e, 's) t = ('s, ('e Expr.t)) Stmt.t
    
    ostap (
      expr : !(Expr.parse)[primary];
      parse: !(Stmt.parse)[expr][fun p -> p] -EOF;
      primary[p]:
        x:!(Lexer.ident)       {`Var   x}
      | i:!(Lexer.literal)     {`Const i}
      | -"(" p -")"
    )

    let print p =
      let rec self i p =
        transform(Stmt.t)
          self
          (fun _ e -> 
	    let rec self i e = transform(Expr.t) self (new Expr.print) i e in
	    fst (self () e)
	  )
          (new Stmt.print)
          i
          p
      in
      self () p

    let code p =
      let rec self i p =
        transform(Stmt.t)
          self
          (let rec self i e = transform(Expr.t) self (new Expr.code) i e in self)
          (new Stmt.code)
          i
          p
      in
      self () p

    let run p =
      let rec self i p =       
        transform(Stmt.t)
	  self
          (let rec self i e = transform(Expr.t) self (new Expr.eval) i e in self) 
          (new Stmt.interpret) 
          i
          p
      in
      self State.empty p

    let compile p = Compiler.compile p 

    let toplevel source =
      match Lexer.fromString parse source with
      | Checked.Ok p -> Checked.Ok (object 
                                      method print   = print   p
                                      method code    = code    p
                                      method run     = run     p
                                      method compile = compile p
                                    end)
      | Checked.Fail m -> Checked.Fail m
       
  end
