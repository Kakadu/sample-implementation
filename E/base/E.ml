open Ostap.Pretty
open GT

module Expr =
  struct

    @type 'a t = [  
      | `Binop of (int -> int -> int) * string * 'a * 'a
    ] with html, show, foldl

    class ['a] eval =
      object (this)
        inherit ['a, int State.t, int, int State.t, int] @t
        method c_Binop s _ f _ x y = f (x.fx s) (y.fx s)
      end

    class ['a] vertical =
      object (this)
        inherit ['a] @t[show]
        method c_Binop _ _ _ s x y = Printf.sprintf "*\n%s\n%s%s" s (x.GT.fx ()) (y.GT.fx ())
      end
    
    let ior  x y = abs x + abs y 
    let iand x y = abs (x * y) 
    let b f      = fun x y -> if f x y then 1 else 0 

    let parse ops primary s = 
      let h = Helpers.highlighting () in
      let rec parse s =  
        let l = List.map 
          (fun (s, t) -> 
             ostap(- $(s)), 
             (fun x y -> 
                let (l, _), (_, r) = h#retrieve x, h#retrieve y in
                h#reassign (`Binop (t, s, x, y)) l r
             )
          ) 
        in
        Ostap.Util.expr (Helpers.loc h#register) (Array.map (fun (a, s) -> a, l s) ops)
        (primary parse)
        s
      in
      ostap (t:parse {t, h#retrieve}) s

  end

module SimpleExpr =
  struct

    module L = Lexer.Make (struct let keywords = [] end) 

    @type primary = [`Var of string | `Const of int] with html, show, foldl

    let parse s =
      let primary p = ostap (
           x:!(L.ident)   {`Var x}
        |  i:!(L.literal) {`Const i}
        |  -"(" p -")"  
        )
      in
      let entry s = 
        Expr.parse [|
          `Lefta, ["&&", Expr.iand]; 
          `Nona , ["==", Expr.b(=)]; 
          `Lefta, ["+", (+)]; 
          `Lefta, ["/", (/)]
        |] 
        primary s
      in
      ostap (entry -EOF) s;;

    @type 'a expr = ['a Expr.t | primary] with html, show, foldl

    class ['a] html cb =
      object (this)
        inherit ['a] @expr[html]
      end

    class ['a] vertical =
      object (this)
        inherit ['a] @expr[show]
        inherit ['a] Expr.vertical
        method c_Var _ _ x = Printf.sprintf "x\n%s\n" x
        method c_Const _ _ i = Printf.sprintf "c\n%d\n" i
      end

    class ['a] eval =
      object (this)
        inherit ['a] Expr.eval
        inherit ['a, int State.t, int, int State.t, int] @expr
        method c_Var s _ x = State.get s x
        method c_Const _ _ i = i
      end

    let rec html cb e = 
      HTMLView.li ~attrs:(cb e)
        (transform(expr) (fun _ -> html cb) (new html cb) () e)

    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e      

    let rec eval s e = transform(expr) eval (new eval) s e      

  end

let toplevel source =  
  match SimpleExpr.L.fromString SimpleExpr.parse source with
  | Checked.Ok (p, h) -> 
      Checked.Ok (
        let interval cb t = 
          if cb = "" 
          then ""
          else 
            let ((x, y), (z, t)) = h t in
            Printf.sprintf "onclick=\"%s ('%d', '%d', '%d', '%d')\"" cb x y z t 
        in
        object 
          method ast cb =             
            HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (SimpleExpr.html (interval cb) p)             
          method print   = View.string (SimpleExpr.vertical p)
          method code    = invalid_arg ""
          method run     = invalid_arg ""
          method compile = invalid_arg ""
        end
      )
  | Checked.Fail m -> Checked.Fail m
