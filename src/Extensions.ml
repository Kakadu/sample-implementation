module Quotations =
  struct
    
    generic 'self t = 'self as [> `H | `V]
 
    ostap (
      parse: !(L.Stmt.parse)[expr][stmt] -EOF;
      expr: !(L.Expr.parse)[primary];
      primary[p]:
        x:!(L.Lexer.ident)   {`Var   x}
      | i:!(L.Lexer.literal) {`Const i} 
      | quotation
      | -"(" p -")";      
      quotation: "@-" {`H} | "@|" {`V};
      stmt[p]: quotation
    )
    
  end

module Breaks =
  struct

    module Stmt =
      struct
        
        generic 'self t = 'self as [>
        | `Lambda
        | `Break 
        ]

        let (++) s = function `Lambda -> s | s' -> `Seq (s, s')

        class virtual ['self, 'a, 'b] t_t =
          object (self)
            method virtual m_Lambda : 'a -> ('a, 'self t, 'b) Generic.a -> 'b
            method virtual m_Break  : 'a -> ('a, 'self t, 'b) Generic.a -> 'b
          end

        class ['self, 'e] interpret =
          object (this)
            inherit ['self, ('self * 'self * State.t), State.t] t_t
            inherit ['self, 'e L.Expr.t, int, ('self * 'self * State.t), State.t] L.Stmt.t_t

            method m_Skip (k, b, s) t = t.Generic.g (`Lambda, b, s) k

            method m_Assign env t x e = 
              let k, b, s = env in 
              t.Generic.g (`Lambda, b, State.modify s x (e.Generic.f env)) k

            method m_Read (k, b, s) t x = 
              Printf.printf "%s < " x; 
              flush stdout;
              let y = int_of_string (input_line stdin) in
              t.Generic.g (`Lambda, b, State.modify s x y) k

            method m_Write env t e = 
              let k, b, s = env in
              Printf.printf "> %d\n" (e.Generic.f env); 
              flush stdout;
              t.Generic.g (`Lambda, b, s) k

            method m_If env t e s1 s2 = 
              let k, b, s = env in 
              (if e.Generic.f env = 0 then s2 else s1).Generic.f (k, b, s)

            method m_While env t e s1 = 
              let k, b, s = env in 
              if e.Generic.f env = 0 
              then t.Generic.g (`Lambda, b, s) k
              else s1.Generic.f (t.Generic.x ++ k, k, s) 

            method m_Seq (k, b, s) t s1 s2 =               
              s1.Generic.f (s2.Generic.x ++ k, b, s) 

            method m_Break (k, b, s) t = t.Generic.g (`Lambda, `Lambda, s) b

            method m_Lambda (k, b, s) t = s 
          end

      end

    ostap (
      parse: !(L.Stmt.parse)[L.Program.expr][fun p -> break p] -EOF;
      break[p]: "break" {`Break}
    )

    let interpret s = 
      let tr = new Stmt.interpret in
      let fe (_, _, s) e = L.Expr.t.Generic.gcata (new L.Expr.eval) s e in 
      L.Stmt.t.Generic.gcata_ext 
         (fun self acc s ->
            Stmt.t.Generic.gcata_ext (fun _ acc x -> self acc x) tr acc s
         ) 
         tr fe (`Lambda, `Lambda, State.empty) s 

    let toplevel source =
      match L.Lexer.fromString parse source with
      | Checked.Ok p -> Checked.Ok (object 
                                      method code    = invalid_arg "Method \"code\" is not supported for this language level."
                                      method run     = interpret p
                                      method compile = invalid_arg "Method \"compile\" is not supported for this language level."
                                      method print   = invalid_arg "Method \"print\" is not supported for this language level."
                                    end)
      | Checked.Fail m -> Checked.Fail m

  end

module Arrays =
  struct

    module Expr =
      struct

        open List

        generic 'self t = 'self as [>
          | `Array of ['self t list] 
          | `Elem  of 'self t * 'self t
        ]
  
        class virtual ['self, 'a, 'b] t_t =
          object (self)
            method virtual m_Array : 'a -> ('a, 'self t, 'b) Generic.a -> 'self t list -> 'b
            method virtual m_Elem  : 'a -> ('a, 'self t, 'b) Generic.a -> ('a, 'self t, 'b) Generic.a -> ('a,'self t, 'b) Generic.a -> 'b
          end

        class ['self] code =
          object (self)
            inherit ['self, unit, string list] t_t
            method m_Array _ t l = ["{}"; string_of_int (length l)] @ flatten (map (t.Generic.g ()) l) 
            method m_Elem  _ _ a i = ["[]"] @ a.Generic.f () @ i.Generic.f ()
          end

        class ['self] gcode =
          object (self)
            inherit ['self] L.Expr.code
            inherit ['self] code
          end

        let code e = 
          let tr = new gcode in 
          L.Expr.t.Generic.gcata_ext
             (fun self acc x -> 
                t.Generic.gcata_ext (fun _ acc x -> self acc x) tr acc x
             ) 
             tr 
             () 
             e

         type p = [ 'self L.Expr.closed_t | 'self closed_t ] as 'self

      end

    module Stmt =
      struct

        generic ('self, 'e) t = 'self as [>
          `ArrayAssn of 'e * 'e * 'e
        ]

        class virtual ['self, 'e, 'f, 'a, 'b] t_t =
          object (self)
            method virtual m_ArrayAssn : 'a -> ('a, ('self, 'e) t, 'b) Generic.a -> ('a, 'e, 'b) Generic.a -> ('a, 'e, 'b) Generic.a -> ('a, 'e, 'b) Generic.a -> 'b  
          end

        class ['self, 'e] code =
          object (self)
            inherit ['self, 'e, string list, unit, string list] t_t
            method m_ArrayAssn _ _ x i y = ["[]="] @ x.Generic.f () @ i.Generic.f () @ y.Generic.f ()
          end

        class ['self] gcode =
          object (self)
            inherit ['self, Expr.p] L.Stmt.code
            inherit ['self, Expr.p] code
          end

        ostap (
          parse: !(L.Stmt.parse)[expr][fun p -> arrassn expr p] -EOF;
          arrassn[expr][p]: 
            x:!(L.Lexer.ident) e:xboct[`Var x][expr] ":=" e3:expr { 
              match e with 
              | `Elem (e1, e2) -> `ArrayAssn (e1, e2, e3) 
              | `Var x -> `Assign (x, e3)
              | _ -> invalid_arg ""
          };
          expr : !(L.Expr.parse) [primary];
          primary[p]:
            -x:!(L.Lexer.ident) xboct[`Var x][p]
          | i:!(L.Lexer.literal) {`Const i}
          | -"{" -h:p -t:(-"," p)* -"}" xboct[`Array (h::t)][p]
          | -"(" -x:p -")" xboct[x][p];
          xboct[x][p]: -"[" -i:p -"]" xboct[`Elem(x, i)][p] | !(Ostap.Combinators.empty) {x}
        )

        let code s = 
          let tr = new gcode in
          let fe acc e = Expr.code e in 
          L.Stmt.t.Generic.gcata_ext 
             (fun self acc s ->
                t.Generic.gcata_ext (fun _ acc x -> self acc x) tr fe acc s
             ) 
             tr fe () s 

        let toplevel source =
          match L.Lexer.fromString parse source with
          | Checked.Ok p -> Checked.Ok (object 
                                          method code    = code p
                                          method run     = invalid_arg "Method \"run\" is not supported for this language level."
                                          method compile = invalid_arg "Method \"compile\" is not supported for this language level."
                                          method print   = invalid_arg "Method \"print\" is not supported for this language level."
                                        end)
          | Checked.Fail m -> Checked.Fail m

      end

  end