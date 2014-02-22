open GT

module Quotations =
  struct
    
    @type t = [ `H | `V] 
 
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
        
        @type ('self, 'e) st = [`Lambda | `Break | ('self, 'e) L.Stmt.t] 

        let (++) s = function `Lambda -> s | s' -> `Seq (s, s')

        class ['self, 'e] interpret =
          object (this)
            inherit ['self, State.t, 'e L.Expr.t, int, ('self * 'self * State.t), State.t] @st
            method c_Skip (k, b, s) t = t.t#self (`Lambda, b, s) k

            method c_Assign env t x e = 
              let k, b, s = env in 
              t.t#self (`Lambda, b, State.modify s x (e.fx env)) k

            method c_Read (k, b, s) t x = 
              Printf.printf "%s < " x; 
              flush stdout;
              let y = int_of_string (input_line stdin) in
              t.t#self (`Lambda, b, State.modify s x y) k

            method c_Write env t e = 
              let k, b, s = env in
              Printf.printf "> %d\n" (e.fx env); 
              flush stdout;
              t.t#self (`Lambda, b, s) k

            method c_If env t e s1 s2 = 
              let k, b, s = env in 
              (if e.fx env = 0 then s2 else s1).fx (k, b, s)

            method c_While env t e s1 = 
              let k, b, s = env in 
              if e.fx env = 0 
              then t.t#self (`Lambda, b, s) k
              else s1.fx ((`While (e.x, s1.x)) ++ k, k, s) 

            method c_Seq (k, b, s) t s1 s2 =               
              s1.fx (s2.x ++ k, b, s) 

            method c_Break (k, b, s) t = t.f (`Lambda, `Lambda, s) b

            method c_Lambda (k, b, s) t = s 
          end

      end

    ostap (
      parse: !(L.Stmt.parse)[L.Program.expr][fun p -> break p] -EOF;
      break[p]: "break" {`Break}
    )
    
    let interpret s = 
      let fe (_, _, s) e = 
        let rec eval i e = transform(L.Expr.t) eval (new L.Expr.eval) i e in
        eval s e
      in 
      let rec self i s = transform(Stmt.st) self fe (new Stmt.interpret) i s in
      self (`Lambda, `Lambda, State.empty) s

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

module Procedures =
  struct

    module Expr =
      struct

        open List

        @type 'self et = [`Call of string * 'self list]

        class ['self] code =
          object
            inherit ['self, string list, unit, string list] @et
            method c_Call _ expr name args = ["call"; name; string_of_int (length args)] @ flatten (map (expr.t#self ()) args)
          end

        open L.Lexer
        open Ostap.Util

        ostap (
          parse[expr]: f:ident "(" a:list[expr] ")" {`Call (f, a)}
        )

      end

    module Stmt =
      struct

        open List

        @type ('self, 'e) st = [
          `Proc of string * string list * string list * ['self]
        | `Call of string * ['e] * 'e list
        | `Ret  of ['e]
        ] 

        class ['self, 'e] code =
          object
            inherit ['self, string list, 'e, string list, unit, string list] @st
            method c_Proc _ stmt name args locals body = 
              let sl l = string_of_int (length l) :: l in
              ["proc"; name] @ (sl args) @ (sl locals) @ (body.fx ())
            method c_Call _ stmt name phony args = ["call"; name; string_of_int (length args)] @ flatten (map (phony.f ()) args)
            method c_Ret  _ _ e = "ret" :: (e.fx ())
          end

        open L.Lexer
        open Ostap.Util

        ostap (
          parse[expr][stmt]:
            "proc" name:ident 
                  "(" args:list[ident] ")" 
                  locals:(-"local" list[ident] -";")? 
                  body:stmt {
              `Proc (name, args, (match locals with Some l -> l | None -> []), body)
            }
          | "return" e:expr                           {`Ret e}
          | "call" name:ident "(" args:list[expr] ")" {`Call (name, hd args, args)}   
        )

      end

  end

module Arrays =
  struct

    module Expr =
      struct

        open List

        @type 'self aet = [
        | `Array of 'self list 
        | `Elem  of ['self] * ['self] 
        ]

        class ['self] code =
          object (self)
            inherit ['self, string list, unit, string list] @aet
            method c_Array _ t l = ["{}"; string_of_int (length l)] @ flatten (map (t.t#self ()) l) 
            method c_Elem  _ _ a i = ["[]"] @ a.fx () @ i.fx ()
          end

        @type 'self p = ['self L.Expr.t | 'self aet | 'self Procedures.Expr.et] 

        class ['self] gcode =
          object (self)
            inherit ['self, string list, unit, string list] @p
            inherit ['self] L.Expr.code
            inherit ['self] Procedures.Expr.code
            inherit ['self] code
          end

        let code e = 
          let rec self i s = transform(p) self (new gcode) i s in
          self () e

      end
   
    module Stmt =
      struct

        @type 'e ast = [`ArrayAssn of ['e] * ['e] * ['e]]

        class ['e] code =
          object (self)
            inherit ['e, string list, unit, string list] @ast
            method c_ArrayAssn _ _ x i y = ["[]="] @ x.fx () @ i.fx () @ y.fx ()
          end

        ostap (
          parse: !(L.Stmt.parse)[expr][fun p -> arrassn expr p] -EOF;
          arrassn[expr][p]: 
            !(Procedures.Stmt.parse)[expr][p]
          | x:!(L.Lexer.ident) e:xboct[`Var x][expr] ":=" e3:expr { 
              match e with 
              | `Elem (e1, e2) -> `ArrayAssn (e1, e2, e3) 
              | `Var x -> `Assign (x, e3)
              | _ -> invalid_arg ""
          };
          expr : !(L.Expr.parse) [primary];
          primary[p]:
            !(Procedures.Expr.parse)[expr]
          |  -x:!(L.Lexer.ident) xboct[`Var x][p]
          | i:!(L.Lexer.literal) {`Const i}
          | -"{" -h:p -t:(-"," p)* -"}" xboct[`Array (h::t)][p]
          | -"(" -x:p -")" xboct[x][p];
          xboct[x][p]: -"[" -i:p -"]" xboct[`Elem(x, i)][p] | !(Ostap.Combinators.empty) {x}
        )

        @type ('self, 'e) stmt = [('self, 'e) L.Stmt.t | 'e ast | ('self, 'e) Procedures.Stmt.st ] 

        class ['self, 'e] gcode =
          object (self)
            inherit ['self, string list, 'e, string list, unit, string list] @stmt
            inherit ['self, 'e] L.Stmt.code
            inherit ['self, 'e] Procedures.Stmt.code
            inherit ['e] code
          end

        let code s = 
          let rec self i s = transform(stmt) self (fun _ e -> Expr.code e) (new gcode) i s in
          self () s

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

