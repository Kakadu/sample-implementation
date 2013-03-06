module Quotations =
  struct
    
    generic 'self t = 'sefl constraint [> `H | `V]
 
    ostap (
      parse: !(L.Stmt.parse)[primary][stmt] -EOF;
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

(*
        generic t = [>
          | `Array of t Generic.list -- Wow!
          | `Elem  of t * t
        ]
  
        class virtual ['self, 'a, 'b] t_t =
          object (self)
            method virtual m_Array : 'a -> 'self t -> 'self t list -> 'b
            method virtual m_Elem : 'a -> 'self t -> ('a, 'self t, 'b) Generic.a -> ('a,'self t, 'b) Generic.a -> 'b
          end

        class ['self] code =
          object (self)
            inherit ['self, unit, string list] t_t
            method m_Array _ _ l =
            method m_Elem  _ _ 
          end
*)

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

      end

    module Stmt =
      struct

        generic ('self, 'e) t = 'self constraint [>
          `ArrayAssn of 'e * 'e * 'e
        ]
(*
        class virtual ['self, 'e, 'f, 'a, 'b] t_t =
          object (self)
            method virtual m_ArrayAssn : 
          end
  *)

      end

  end