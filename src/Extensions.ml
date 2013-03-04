open L

let fromString p s =
    Ostap.Combinators.unwrap (p (new Lexer.t s)) (fun x -> Checked.Ok x) 
      (fun (Some err) ->
         let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
         let m =  match m with `Msg m -> m | `Comment (s, _) -> Ostap.Msg.make s [||] loc in
         Checked.Fail [m]
      )
  
module Quotations =
  struct
    
    generic t = [> `H | `V]
 
    ostap (
      parse: !(Stmt.parse)[primary][stmt] -EOF;
      primary[p]:
        x:!(Lexer.ident)   {`Var   x}
      | i:!(Lexer.literal) {`Const i} 
      | quotation
      | -"(" p -")";      
      quotation: "@-" {`H} | "@|" {`V};
      stmt[p]: quotation | p      
    )

    let Checked.Ok t = fromString parse "while (@-) do @-"    
    
  end

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