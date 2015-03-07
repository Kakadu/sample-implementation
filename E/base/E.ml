open Ostap.Pretty

let w p px x = if px < p then rboxed x else x 

let b l = hboxed  (listBySpaceBreak l)
let v l = hvboxed (listBySpaceBreak l)
let c l = cboxed  (vboxed (listByBreak l))

open GT

module Expr =
  struct

    module L = Lexer.Make (struct let keywords = [] end) 

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
        inherit ['a, int State.t, int, int State.t, int] @t
        method c_Var   s _ x       = State.get s x
        method c_Const _ _ n       = n
        method c_Binop s _ f _ x y = f (x.fx s) (y.fx s)
      end

    class ['a] html' =
      object (this)
        inherit ['a] @html[t]
      end

    class ['a] vertical =
      object (this)
        inherit ['a] @show[t]
        method c_Var _ _ x         = Printf.sprintf "x\n%s\n" x
        method c_Binop _ _ _ s x y = Printf.sprintf "*\n%s\n%s%s" s (x.GT.fx ()) (y.GT.fx ())
        method c_Const _ _ i       = Printf.sprintf "c\n%d\n" i
      end

    let primary p = ostap (
        x:!(L.ident)   {`Var   x}
      | i:!(L.literal) {`Const i}
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
    
    let rec html e = transform(t) (fun _ -> html) (new html') () e
    let rec vertical e = transform(t) (fun _ -> vertical) (new vertical) () e

    let parse = ostap (parse -EOF)
  end

let toplevel source =  
  match Expr.L.fromString Expr.parse source with
  | Checked.Ok p -> Checked.Ok (object 
                                  method ast     = Expr.html p 
                                  method print   = View.string (Expr.vertical p)
                                  method code    = invalid_arg ""
                                  method run     = invalid_arg ""
                                  method compile = invalid_arg ""
                                end)
  | Checked.Fail m -> Checked.Fail m
