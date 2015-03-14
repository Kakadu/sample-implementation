open Ostap.Pretty
open GT

module type Domain =
 sig

   type t
   val op   : string -> t -> t -> t Semantics.opt
   val show : t -> string
   val html : t -> HTMLView.er

 end

module IntDomain (S : sig val strict : bool end) =
  struct

   type t = int

   exception NotABool 

   let op = 
     let b    f x y = if f x y then 1 else 0 in
     let lift f x y = try Semantics.Good (f x y) with NotABool -> Semantics.Bad "not a boolean value" in
     let ib = function 0 -> 0 | 1 -> 1 | _ -> raise NotABool in    
     function
     | "+"  -> lift (+)
     | "-"  -> lift (-)
     | "*"  -> if S.strict then lift ( * ) else lift (fun x y -> if x = 0 then 0 else x * y)
     | "/"  -> (fun x y -> if y = 0 then Semantics.Bad "division by zero" else Semantics.Good (x / y))
     | "%"  -> (fun x y -> if y = 0 then Semantics.Bad "division by zero" else Semantics.Good (x mod y))
     | "==" -> lift (b (=))
     | "!=" -> lift (b (<>))
     | "<=" -> lift (b (<=))
     | "<"  -> lift (b (<))
     | ">=" -> lift (b (>=))
     | ">"  -> lift (b (>))
     | "&&" -> if S.strict then lift (fun x y -> ib x * ib y) else lift (fun x y -> if ib x = 0 then 0 else ib y)
     | "||" -> if S.strict then lift (fun x y -> ib x + ib y) else lift (fun x y -> if ib x = 1 then 1 else ib y)

   let show = string_of_int
   let html = HTMLView.int

 end

module StrictInt    = IntDomain (struct let strict = true  end)
module NonStrictInt = IntDomain (struct let strict = false end)
 
module Expr =
  struct

    @type 'a t = [`Binop of string * 'a * 'a] with html, show, foldl

    class ['a] vertical =
      object (this)
        inherit ['a] @t[show]
        method c_Binop _ _ s x y = Printf.sprintf "*\n%s\n%s%s" s (x.GT.fx ()) (y.GT.fx ())
      end
    
    let hparse h ops primary s = 
      let rec parse s =  
        let l = List.map 
          (fun s -> 
             ostap(- $(s)), 
             (fun x y -> 
                let (l, _), (_, r) = h#retrieve x, h#retrieve y in
                h#reassign (`Binop (s, x, y)) l r
             )
          ) 
        in
        Ostap.Util.expr (Helpers.loc h#register) (Array.map (fun (a, s) -> a, l s) ops)
        (primary parse)
        s
      in
      parse s

    let parse ops primary s =
      let h = Helpers.highlighting () in
      ostap (e:hparse[h][ops][primary] -EOF {e, h#retrieve}) s

    module Semantics (D : Domain) =
      struct
 
        module Deterministic =
          struct

            module BigStep =
              struct

                module S = Semantics.Deterministic.BigStep

                class virtual ['env, 'left, 'over, 'right, 'a] c =
                  object 
                    inherit ['a, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case
                            ] @t
                  end

		class virtual ['a] standard =
                  object 
                    inherit [unit, D.t State.t, 'a, D.t, 'a] c 
                    method c_Binop (env, state, _) _ s x y =
                      S.Subgoals ([env, state, x.GT.x; env, state, y.GT.x], (fun [x'; y'] -> D.op s  x' y'), "Binop")               	       
		  end

		class virtual ['a] with_env =
                  object 
                    inherit [D.t State.t, 'a, unit, D.t, 'a] c 
                    method c_Binop (state, _, _) _ s x y =
                      S.Subgoals ([state, x.GT.x, (); state, y.GT.x, ()], (fun [x'; y'] -> D.op s  x' y'), "Binop")
		  end

              end           

          end

      end

  end

module SimpleExpr (C : sig val ops : ([`Nona | `Lefta | `Righta] * string list) array val keywords : string list end) =
  struct

    module L = Lexer.Make (C) 

    @type primary = [`Var of string | `Const of int] with html, show, foldl

    let hparse h s =
      let primary p = ostap (
           x:!(L.ident)   {`Var x}
        |  i:!(L.literal) {`Const i}
        |  -"(" p -")"  
        )
      in
      Expr.hparse h C.ops primary s

    let parse s =
      let h = Helpers.highlighting () in
      ostap (e:hparse[h] -EOF {e, h#retrieve}) s;;

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
      | `Binop (s, x, y) -> HTMLView.tag "tt" (HTMLView.raw (Printf.sprintf "%s %s %s" (subtree x) s (subtree y)))

    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e      

    module Semantics (D : Domain) (I : sig val from_int : int -> D.t end) =
      struct

        module Expr = Expr.Semantics (D)

        module Deterministic = 
          struct        

            module BigStep =
              struct

                module S = Semantics.Deterministic.BigStep

                class virtual ['env, 'left, 'over, 'right, 'a] c =
                  object 
                    inherit ['a, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case, 
                             'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case
                            ] @expr
                  end

                module Standard =
                  struct

   		    class ['a] step =
                      object 
                        inherit [unit, D.t State.t, 'a expr, D.t, 'a] c
                        inherit ['a] Expr.Deterministic.BigStep.standard 
                        method c_Var (env, state, _) _ x = 
                          (try S.Just (State.get state x, "Var") with
                          | _ -> S.Nothing (Printf.sprintf "undefined variable '%s'" x, "Var")
                          )
                        method c_Const (env, stat, _) _ i = S.Just (I.from_int i, "Const")
		      end

                    let rec step env state e = 
                      GT.transform(expr) (fun (env, state, _) e -> step env state e) (new step) (env, state, e) e

                    type env   = unit
                    type left  = D.t State.t
                    type over  = 'a expr as 'a
                    type right = D.t

                    let env_html   = HTMLView.unit
                    let left_html  = State.html D.show
                    let over_html  = abbreviate_html (fun _ -> "")
                    let right_html = D.html

                    let customizer =
                      object 
                        inherit S.Tree.html_customizer
                        method show_env   = false
                        method over_width = 70
                      end

                  end

                module WithEnv =
                  struct

		    class ['a] step =
                      object 
                        inherit [D.t State.t, 'a expr, unit, D.t, 'a] c 
                        inherit ['a] Expr.Deterministic.BigStep.with_env 
                        method c_Var (state, _, _) _ x = 
                          (try S.Just (State.get state x, "Var") with
                           | _ -> S.Nothing (Printf.sprintf "undefined variable \'%s\'" x, "Var")
                          )
                        method c_Const (state, _, _) _ i = S.Just (I.from_int i, "Const")
		      end

                    type env   = D.t State.t
                    type left  = 'a expr as 'a
                    type over  = unit
                    type right = D.t

                    let env_html   = State.html D.show
                    let left_html  = abbreviate_html (fun _ -> "")
                    let over_html  = HTMLView.unit
                    let right_html = D.html

                    let rec step state e _ = 
                      GT.transform(expr) (fun (state, _, _) e -> step state e ()) (new step) (state, e, ()) e

                    let customizer =
                      object 
                        inherit Semantics.Deterministic.BigStep.Tree.html_customizer
                        method show_env    = true
                        method show_over   = false
                        method over_width  = 50 
                        method arrow_scale = 3
                      end

                  end                      

                module WithEnvT = S.Tree.Make (WithEnv)
                module StandardT = S.Tree.Make (Standard)

                let build ?(limit=(-1)) state e = S.Tree.build ~limit:limit Standard.step () state e 

                let html tree =
                  S.Tree.html 
                    (object 
                       inherit S.Tree.html_customizer
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
  let module Expr = SimpleExpr (
    struct 
      let ops = [|`Lefta, ["&&"]; 
                  `Nona , ["=="];  
                  `Lefta, ["+" ]; 
                  `Lefta, ["/" ]
                |]
      let keywords = []
    end)
  in
  Toplevel.make 
    (Expr.L.fromString Expr.parse)
    (fun (p, h) ->         
        object inherit Toplevel.c
            method ast cb = View.toString (
                              HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                                Expr.html (Helpers.interval cb h) p
                              )
                            )
            method vertical = Expr.vertical p
            method code     = invalid_arg ""
            method run      = (*View.toString (
                                SimpleExpr.Semantics.Deterministic.BigStep.StandardT.html (
                                  SimpleExpr.Semantics.Deterministic.BigStep.StandardT.build () State.empty p
                                )
                              )*)
                              
                              let module S = Expr.Semantics (StrictInt)(struct let from_int x = x end) in
                              View.toString (
                                S.Deterministic.BigStep.WithEnvT.html (
                                  S.Deterministic.BigStep.WithEnvT.build State.empty p ()
                                )
                              )           
            method compile  = invalid_arg ""
          end
    )  

