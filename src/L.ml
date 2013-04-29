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

    generic 'self t = 'self as [>  
        `Var   of [string] 
      | `Const of [int]
      | `Binop of [int -> int -> int] * [string] * 'self t * 'self t       
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
        inherit ['self, State.t, int] @t
        method m_Var   s _ x       = s x
        method m_Const _ _ n       = n
        method m_Binop s _ f _ x y = f (x.Generic.f s) (y.Generic.f s)
      end

    class ['self] print =
      object (this)
        inherit ['self, unit, printer * int] @t 
        method m_Var   _ e x = string x, prio e.Generic.x
        method m_Const _ e x = int x, prio e.Generic.x
        method m_Binop _ e _ op x y = 
          let x, px = x.Generic.f () in
          let y, py = y.Generic.f () in 
          let p = prio e.Generic.x in b [w p px x; string op; w p py y], p
      end

    class ['self] code =
      object (this)
        inherit ['self, unit, string list] @t
        method m_Var   _ _ x       = ["x"; x]
        method m_Const _ _ x       = ["!"; string_of_int x] 
        method m_Binop _ _ _ o x y = ["@"; o] @ List.flatten [x.Generic.f (); y.Generic.f ()]
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

    generic ('self, 'e) t = 'self as [>
        `Skip 
      | `Assign of [string] * 'e
      | `Read   of [string]
      | `Write  of 'e
      | `If     of 'e * ('self, 'e) t * ('self, 'e) t
      | `While  of 'e * ('self, 'e) t  
      | `Seq    of ('self, 'e) t * ('self, 'e) t 
    ]

    class ['self, 'e] interpret =
      object (this)
        inherit ['self, > 'e Expr.t, int, State.t, State.t] @t         
        method m_Skip s _ = s
        method m_Assign s _ x e = State.modify s x (e.Generic.f s)
        method m_Read s _ x = 
          Printf.printf "%s < " x; 
          flush stdout;
          let y = int_of_string (input_line stdin) in
          State.modify s x y
        method m_Write s _ e = 
          Printf.printf "> %d\n" (e.Generic.f s); 
          flush stdout;
          s
        method m_If s _ e s1 s2 = (if e.Generic.f s = 0 then s2 else s1).Generic.f s
        method m_While s t e s1 = if e.Generic.f s = 0 
                                     then s 
                                     else s1.Generic.g s (`Seq (s1.Generic.x, t.Generic.x))
        method m_Seq s _ s1 s2 = s2.Generic.f (s1.Generic.f s)
      end

    class ['self, 'e] print =
      object (this)
        inherit ['self, > 'e Expr.t, printer, unit, printer] @t
        method m_Skip   _ _       = string "skip"
        method m_Assign _ _ x e   = v [string x; string ":="; e.Generic.f ()]
        method m_If     _ _ c x y = v [string "if"; c.Generic.f (); v [string "then"; x.Generic.f (); string "else"; y.Generic.f ()]]
        method m_While  _ _ c x   = v [v [string "while"; c.Generic.f ()]; v [string "do"; x.Generic.f ()]]
        method m_Seq    _ _ x y   = c [seq [x.Generic.f (); string ";"]; y.Generic.f ()]
        method m_Read   _ _ x     = v [string "read"; rboxed (string x)]
        method m_Write  _ _ e     = v [string "write"; rboxed (e.Generic.f ())]
      end

    class ['self, 'e] code =
      object (this)
        inherit ['self, > 'e Expr.t, string list, unit, string list] @t
        method m_Skip   _ _       = ["s"]
        method m_Seq    _ _ x y   = ";" :: (x.Generic.f ()) @ (y.Generic.f ())
        method m_Assign _ _ x e   = "=" :: x :: (e.Generic.f ())
        method m_While  _ _ c s   = "l" :: (c.Generic.f ()) @ (s.Generic.f ())
        method m_If     _ _ c x y = "i" :: (c.Generic.f ()) @ (x.Generic.f ()) @ (y.Generic.f ())
        method m_Read   _ _ x     = ["r"; x]
        method m_Write  _ _ e     = "w" :: (e.Generic.f ())
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
            inherit ['e,[`Yes of int | `No], string list] @t
            method m_Var   l _ x       = first l [Printf.sprintf "\tL %s\n" x]
            method m_Const l _ n       = first l [Printf.sprintf "\tC %d\n" n]
            method m_Binop l _ f o x y = (x.Generic.f l) @ (y.Generic.f `No) @ [Printf.sprintf "\tB %s\n" o]
          end
     
      end

    module Stmt =
      struct
        include Stmt

        type env = [`Yes of int | `No] * [`Yes of int | `Maybe of int] * int

        class ['self, 'e] compile =
          object (this)
            inherit ['self, > 'e Expr.t, string list, env, string list * int] @t
            method m_Skip (this, next, last) _  = 
              (match this, next with 
               | `No   , `Maybe n            -> []
               | `No   , `Yes   n            -> [Printf.sprintf "\tJ $%d\n" n]
               | `Yes n, (`Yes m | `Maybe m) -> [Printf.sprintf "$%d:\tJ $%d\n" n m]
              ), last
            method m_Seq ((this, next, last) as env) _ s1 s2 =
              match s1.Generic.x with
              | `Skip -> s2.Generic.f env
              | _     -> match s2.Generic.x with
                         | `Skip -> s1.Generic.f env
                         | _     ->
                             let s1', last'  = s1.Generic.f (this, `Maybe (last+1), last+1) in
                             let s2', last'' = s2.Generic.f (`Yes (last+1), next, last') in
                             s1' @ s2', last''
            method m_Assign ((this, next, l) as env) _ x e = 
              last next ((e.Generic.f env) @ [Printf.sprintf "\tS %s\n" x]), l
            method m_Read (this, next, last) _ x = 
              frame this next ["\tR\n"; Printf.sprintf "\tS %s\n" x], last
            method m_Write ((this, next, l) as env) _ e = 
              last next ((e.Generic.f env) @ ["\tW\n"]), l
            method m_If ((this, next, last) as env) _ e s1 s2 =
              let s2', last'  = s2.Generic.f (`No, force next, last+1) in
              let s1', last'' = s1.Generic.f (`Yes (last+1), next, last') in
              List.flatten [
                e.Generic.f env; 
                [Printf.sprintf "\tJT $%d\n" (last+1)];
                s2';
                s1'
              ], last''
            method m_While ((this, next, last) as env) _ e s =
              let s', last' = s.Generic.f (`Yes (last+2), `Maybe (last+1), last+2) in
              frame this next (List.flatten [[Printf.sprintf "\tJ $%d\n" (last+1)];
                                             s';
                                             e.Generic.f (`Yes (last+1), next, last);
                                             [Printf.sprintf "\tJT $%d\n" (last+2)]
                                            ]), last'
          end

      end

    let compile p =
      let code, _ =
        Stmt.t.Generic.gcata 
          (fun (this, _, _) expr -> Expr.t.Generic.gcata (new Expr.compile) this expr)
          (new Stmt.compile)
          (`No, `Maybe 0, 0)
          p
      in
      code @ ["$0:\tE\n"]

  end

module Program =
  struct

    type ('e, 's) t = > ('s, (> 'e Expr.t)) Stmt.t
    
    ostap (
      expr : !(Expr.parse)[primary];
      parse: !(Stmt.parse)[expr][fun p -> p] -EOF;
      primary[p]:
        x:!(Lexer.ident)       {`Var   x}
      | i:!(Lexer.literal)     {`Const i}
      | -"(" p -")"
    )

    let print p =
      Stmt.t.Generic.gcata        
        (fun _ e -> fst (Expr.t.Generic.gcata (new Expr.print) () e))
        (new Stmt.print)
        ()
        p

    let code p =
      Stmt.t.Generic.gcata
        (Expr.t.Generic.gcata (new Expr.code))
        (new Stmt.code)
        ()
        p

    let run p =       
      Stmt.t.Generic.gcata 
        (Expr.t.Generic.gcata (new Expr.eval)) 
        (new Stmt.interpret) 
        State.empty 
        p

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
