module Quotations =
  struct
    
    generic 'self t = 'sefl constraint [> `H | `V]
 
    ostap (
      parse: !(L.Stmt.parse)[expr][stmt] -EOF;
      expr: !(L.Expr.parse)[primary];
      primary[p]:
        x:!(L.Lexer.ident)   {`Var   x}
      | i:!(L.Lexer.literal) {`Const i} 
      | quotation
      | -"(" p -")";      
      quotation: "@-" {`H} | "@|" {`V};
      stmt[p]: quotation | p
    )
    
  end

module Arrays =
  struct

    module Expr =
      struct

        open List

        type 'self bt = [ `Array of 'self * 'self list | `Elem of 'self * 'self ]

        generic 'self t = 'self constraint [>
          | `Array of 'self t * ['self t list] 
          | `Elem  of 'self t * 'self t
        ]
  
        class virtual ['self, 'a, 'b] t_t =
          object (self)
            method virtual m_Array : 'a -> 'self t -> ('a, 'self t, 'b) Generic.a -> 'self t list -> 'b
            method virtual m_Elem  : 'a -> 'self t -> ('a, 'self t, 'b) Generic.a -> ('a,'self t, 'b) Generic.a -> 'b
          end

        class ['self] code =
          object (self)
            inherit ['self, unit, string list] t_t
            method m_Array _ _ t l = ["{}"; string_of_int (length l)] @ flatten (map (t.Generic.g ()) l) 
            method m_Elem  _ _ a i = ["[]"] @ a.Generic.f () @ i.Generic.f ()
          end

        class ['self] gcode =
          object (self)
            inherit ['self] L.Expr.code
            inherit ['self] code
          end

        let code e = 
          let tr = new gcode in 
          L.Expr.t.Generic.gcata 
             (fun self acc x -> 
                t.Generic.gcata (fun _ acc x -> self acc x) tr acc x
             ) 
             tr 
             () 
             e

         type p = [ 'self L.Expr.bt | 'self bt ] as 'self

      end

    module Stmt =
      struct

        generic ('self, 'e) t = 'self constraint [>
          `ArrayAssn of 'e * 'e * 'e
        ]

        class virtual ['self, 'e, 'f, 'a, 'b] t_t =
          object (self)
            method virtual m_ArrayAssn : 'a -> ('self, 'e) t -> ('a, 'e, 'b) Generic.a -> ('a, 'e, 'b) Generic.a -> ('a, 'e, 'b) Generic.a -> 'b  
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
          | -"{" -h:p -t:(-"," p)* -"}" xboct[`Array (h, h::t)][p]
          | -"(" -x:p -")" xboct[x][p];
          xboct[x][p]: -"[" -i:p -"]" xboct[`Elem(x, i)][p] | !(Ostap.Combinators.empty) {x}
        )

        let code s = 
          let tr = new gcode in
          let fe acc e = Expr.code e in 
          L.Stmt.t.Generic.gcata 
             (fun self acc s ->
                t.Generic.gcata (fun _ acc x -> self acc x) tr fe acc s
             ) 
             tr fe () s 

        let toplevel =
          object
            method parse     = parse
            method code    p = code p
            method run     _ = invalid_arg "Method \"run\" is not supported for this language level."
            method compile _ = invalid_arg "Method \"compile\" is not supported for this language level."
            method print   _ = invalid_arg "Method \"print\" is not supported for this language level."
          end

      end

  end