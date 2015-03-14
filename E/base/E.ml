open Ostap.Pretty
open GT

module Expr =
  struct

    @type 'a t = [`Binop of (int -> int -> int) * string * 'a * 'a] with html, show, foldl

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

    module Semantics =
      struct
 
        module Deterministic =
          struct

            module BigStep =
              struct

                class virtual ['env, 'left, 'over, 'right, 'a] c =
                  object 
                    inherit ['a, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) Semantics.Deterministic.BigStep.case, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) Semantics.Deterministic.BigStep.case
                            ] @t
                  end

		class virtual ['a] standard =
                  object 
                    inherit [unit, int State.t, 'a, int, 'a] c 
                    method c_Binop (env, state, _) _ f _ x y =
                      Semantics.Deterministic.BigStep.Subgoals (
                        [env, state, x.GT.x; env, state, y.GT.x],
                        (fun [x'; y'] -> Some (f  x' y')),
                        "Binop"
                      )               	       
		  end

		class virtual ['a] with_env =
                  object 
                    inherit [int State.t, 'a, unit, int, 'a] c 
                    method c_Binop (state, _, _) _ f _ x y =
                      Semantics.Deterministic.BigStep.Subgoals (
                        [state, x.GT.x, (); state, y.GT.x, ()],
                        (fun [x'; y'] -> Some (f  x' y')),
                        "Binop"
                      )               	       
		  end

              end           

          end

      end

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

        module Deterministic = 
          struct        

            module BigStep =
              struct

                class virtual ['env, 'left, 'over, 'right, 'a] c =
                  object 
                    inherit ['a, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) Semantics.Deterministic.BigStep.case, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) Semantics.Deterministic.BigStep.case
                            ] @expr
                  end

                module Standard =
                  struct

   		    class ['a] step =
                      object 
                        inherit [unit, int State.t, 'a expr, int, 'a] c
                        inherit ['a] Expr.Semantics.Deterministic.BigStep.standard 
                        method c_Var (env, state, _) _ x = 
                          (try Semantics.Deterministic.BigStep.Just (State.get state x, "Var") with
                          | _ -> Semantics.Deterministic.BigStep.Nothing (Printf.sprintf "undefined variable \"%s\"" x, "Var")
                          )
                        method c_Const (env, stat, _) _ i = Semantics.Deterministic.BigStep.Just (i, "Const")
		      end

                    let rec step env state e = 
                      GT.transform(expr) (fun (env, state, _) e -> step env state e) (new step) (env, state, e) e

                    type env   = unit
                    type left  = int State.t
                    type over  = 'a expr as 'a
                    type right = int

                    let env_html   = HTMLView.unit
                    let left_html  = State.html string_of_int 
                    let over_html  = abbreviate_html (fun _ -> "")
                    let right_html = HTMLView.int

                    let customizer =
                      object 
                        inherit Semantics.Deterministic.BigStep.Tree.html_customizer
                        method show_env   = false
                        method over_width = 70
                      end

                  end

                module WithEnv =
                  struct

		    class ['a] step =
                      object 
                        inherit [int State.t, 'a expr, unit, int, 'a] c 
                        inherit ['a] Expr.Semantics.Deterministic.BigStep.with_env 
                        method c_Var (state, _, _) _ x = 
                          (try Semantics.Deterministic.BigStep.Just (State.get state x, "Var") with
                           | _ -> Semantics.Deterministic.BigStep.Nothing (Printf.sprintf "undefined variable \"%s\"" x, "Var")
                          )
                        method c_Const (state, _, _) _ i = Semantics.Deterministic.BigStep.Just (i, "Const")
		      end

                    type env   = int State.t
                    type left  = 'a expr as 'a
                    type over  = unit
                    type right = int

                    let env_html   = State.html string_of_int
                    let left_html  = abbreviate_html (fun _ -> "")
                    let over_html  = HTMLView.unit
                    let right_html = HTMLView.int

                    let rec step state e _ = 
                      GT.transform(expr) (fun (state, _, _) e -> step state e ()) (new step) (state, e, ()) e

                    let customizer =
                      object 
                        inherit Semantics.Deterministic.BigStep.Tree.html_customizer
                        method show_env    = true
                        method show_over   = false
                        method over_width  = 50 
                        method arrow_scale = 4
                      end

                  end                      

                module WithEnvT = Semantics.Deterministic.BigStep.Tree.Make (WithEnv)
                module StandardT = Semantics.Deterministic.BigStep.Tree.Make (Standard)

                let build ?(limit=(-1)) state e = Semantics.Deterministic.BigStep.Tree.build ~limit:limit Standard.step () state e 

                let html tree =
                  Semantics.Deterministic.BigStep.Tree.html 
                    (object 
                       inherit Semantics.Deterministic.BigStep.Tree.html_customizer
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
            method run      = (*View.toString (
                                SimpleExpr.Semantics.Deterministic.BigStep.StandardT.html (
                                  SimpleExpr.Semantics.Deterministic.BigStep.StandardT.build () State.empty p
                                )
                              )*)
                              View.toString (
                                SimpleExpr.Semantics.Deterministic.BigStep.WithEnvT.html (
                                  SimpleExpr.Semantics.Deterministic.BigStep.WithEnvT.build State.empty p ()
                                )
                              )           
            method compile  = invalid_arg ""
          end
    )  

