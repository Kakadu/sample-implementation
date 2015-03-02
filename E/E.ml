open Ostap.Pretty

let w p px x = if px < p then rboxed x else x 

let b l = hboxed  (listBySpaceBreak l)
let v l = hvboxed (listBySpaceBreak l)
let c l = cboxed  (vboxed (listByBreak l))

module Lexer =
  struct

    let r = Ostap.Matcher.Token.repr

    ostap (
      ident: x:IDENT {r x};
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

module State =
  struct

    type t = string -> int

    let empty = fun x-> invalid_arg (Printf.sprintf "variable \"%s\" undefined" x)
    let modify s name x = fun name' -> if name = name' then x else s name'

  end

open GT

module Expr =
  struct

    @type 'a t = [  
        `Var   of string 
      | `Const of int
      | `Binop of (int -> int -> int) * string * 'a * 'a
    ] with html, show, foldl

    let prio = 
      let a = [ 
        "&&", 4; 
        "==", 5; 
        "+" , 6;
        "/" , 7;
      ] 
      in
      function `Binop (_, s, _, _) -> List.assoc s a | _ -> 8

    class ['a] eval =
      object (this)
        inherit ['a, State.t, int, State.t, int] @t
        method c_Var   s _ x       = s x
        method c_Const _ _ n       = n
        method c_Binop s _ f _ x y = f (x.fx s) (y.fx s)
      end

    let primary p = ostap (
        x:!(Lexer.ident)   {`Var   x}
      | i:!(Lexer.literal) {`Const i}
      | -"(" p -")"
    ) 

    let rec parse s =  
      let l = List.map (fun (s, t) -> ostap(- $(s)), fun x y -> `Binop (t, s, x, y)) in
      let ior  x y = abs x + abs y in
      let iand x y = abs (x * y) in
      let b f = fun x y -> if f x y then 1 else 0 in
      Ostap.Util.expr (fun x -> x) [|
        `Lefta, l ["&&", iand];
        `Nona , l ["==", b(=)];
        `Lefta, l ["+" , ( +  )];
        `Lefta, l ["/" , (/ )];
      |]
      (primary parse)
      s

    let rec html e = transform(t) (fun _ -> html) (new @html[t]) () e
  end

let toplevel source =
  match Lexer.fromString Expr.parse source with
  | Checked.Ok p -> Checked.Ok (object 
                                  method print   = Expr.html p
                                  method code    = invalid_arg ""
                                  method run     = invalid_arg ""
                                  method compile = invalid_arg ""
                                end)
  | Checked.Fail m -> Checked.Fail m
