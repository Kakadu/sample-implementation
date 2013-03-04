module Arrays =
  struct

    module Expr =
      struct
       
        generic t = [>
          | `Array of [t list]
          | `Elem  of t * t
        ]
  (*
        class virtual ['self, 'a, 'b] t_t =
          object (self)
            method virtual m_Array : 'a -> 'self t -> Generic.a
          end
*)
      end

    module Stmt =
      struct

        generic 'e t = [>
          `ArrayAssn of 'e * 'e * 'e
        ]

      end

  end