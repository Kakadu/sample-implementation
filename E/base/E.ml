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

    let parse h ops primary s = 
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
      parse s

  end

module SimpleExpr =
  struct

    module L = Lexer.Make (struct let keywords = [] end) 

    @type primary = [`Var of string | `Const of int] with html, show, foldl

    let parse s =
      let h = Helpers.highlighting () in
      let primary p = ostap (
           x:!(L.ident)   {`Var x}
        |  i:!(L.literal) {`Const i}
        |  -"(" p -")"  
        )
      in
      let entry s = 
        Expr.parse h [|
          `Lefta, ["&&", Expr.iand]; 
          `Nona , ["==", Expr.b(=)]; 
          `Lefta, ["+", (+)]; 
          `Lefta, ["/", (/)]
        |] 
        primary s
      in
      ostap (e:entry -EOF {e, h#retrieve}) s;;

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

    let abbreviate_html cb = 
      let subtree = function
      | `Const i -> string_of_int i
      | `Var x -> x
      | _ -> "(&#8226;)"
      in
      function
      | `Const i -> HTMLView.tag "tt" (HTMLView.int i)
      | `Var   x -> HTMLView.tag "tt" (HTMLView.raw x)
      | `Binop (_, s, x, y) -> HTMLView.tag "tt" (HTMLView.raw (Printf.sprintf "%s %s %s" (subtree x) s (subtree y)))

    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e      

    let rec eval s e = transform(expr) eval (new eval) s e      

    module Semantics =
      struct
        
        let build ?(limit=(-1)) state e =
          Semantics.Deterministic.Tree.build ~limit:limit 
            (object 
               inherit [unit, int State.t, 'a expr as 'a, int] Semantics.Deterministic.step
                 method make env state expr =
                   match expr with
		   | `Binop (f, _, x, y) ->
                      Semantics.Deterministic.Subgoals (
                        [env, state, x; env, state, y],
                        (fun [x'; y'] -> Some (f x' y'))
                      )               
		   | `Var x -> (try Semantics.Deterministic.Just (State.get state x) with _ ->  Semantics.Deterministic.Nothing)
                   | `Const i -> Semantics.Deterministic.Just i
             end
            ) 
            () 
            state 
            e 

	let html tree =
          Semantics.Deterministic.Tree.html 
            (object 
               inherit Semantics.Deterministic.Tree.html_customizer
               method show_env   = false
               method over_width = 70
             end)
            (fun _ -> HTMLView.unit)
            (fun _ -> State.html string_of_int)
            (fun _ -> abbreviate_html (fun _ -> ""))
            (fun _ -> HTMLView.int) 
            tree

      end

  end

let toplevel =  
  Toplevel.make 
    (SimpleExpr.L.fromString SimpleExpr.parse)
    (fun (p, h) ->         
        object inherit Toplevel.c
            method ast cb = View.toString (
                              HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                                SimpleExpr.html (Helpers.interval cb h) p
                              )
                            )
            method vertical = SimpleExpr.vertical p
            method code     = invalid_arg ""
            method run      = View.toString (SimpleExpr.Semantics.html (SimpleExpr.Semantics.build State.empty p))
            method compile  = invalid_arg ""
          end
    )  

