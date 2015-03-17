open Ostap.Pretty
open GT
 
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

    module Semantics (D : Semantics.Domain) =
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
                      S.Subgoals ([env, state, x.GT.x; env, state, y.GT.x], (fun [x'; y'] -> S.opt_to_case "" (D.op s  x' y')), "Binop")
		  end

		class virtual ['a] with_env =
                  object 
                    inherit [D.t State.t, 'a, unit, D.t, 'a] c 
                    method c_Binop (state, _, _) _ s x y =
                      S.Subgoals ([state, x.GT.x, (); state, y.GT.x, ()], (fun [x'; y'] -> S.opt_to_case "" (D.op s  x' y')), "Binop")
		  end

              end           

          end

      end

  end

module SimpleExpr (L : Lexer.Sig)(C : sig val ops : ([`Nona | `Lefta | `Righta] * string list) array end) =
  struct

    module L = L

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

    class ['a] html =
      object (this)
        inherit ['a] @expr[html]
        inherit Helpers.cname
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
        (transform(expr) (fun _ -> html cb) (new html) () e)

    let abbreviate_html cb = 
      let wrap node html =
        HTMLView.tag "attr" ~attrs:(Printf.sprintf "%s style=\"cursor:pointer\"" (cb node)) html
      in
      let subtree = function
      | `Const i as node -> wrap node (HTMLView.raw (string_of_int i))
      | `Var   x as node -> wrap node (HTMLView.raw x)
      | node -> wrap node (HTMLView.raw "(&#8226;)")
      in
      function
      | `Const i as node  -> wrap node (HTMLView.tag "tt" (HTMLView.int i))
      | `Var   x as node -> wrap node (HTMLView.tag "tt" (HTMLView.raw x))
      | `Binop (s, x, y) as node -> 
          HTMLView.tag "tt" (HTMLView.seq [subtree x; wrap node (HTMLView.raw (Printf.sprintf " %s " s)); subtree y])

    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e      

    module TopSemantics = Semantics

    module Semantics (D : Semantics.Domain) (I : sig val from_int : int -> D.t end) (C : sig val cb : 'a expr as 'a -> string end) =
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
                    let over_html  = abbreviate_html C.cb
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
                    let left_html  = abbreviate_html C.cb
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
                    (fun _ -> abbreviate_html C.cb)
                    (fun _ -> HTMLView.int) 
                    tree

              end

          end

      end

    let eval_strict state e =
      let module Strict = Semantics (TopSemantics.StrictInt)(struct let from_int x = x end)(struct let cb _ = "" end) in
      match Strict.Deterministic.BigStep.WithEnvT.build state e () with
      | TopSemantics.Deterministic.BigStep.Tree.Node (_, _, _, r, _, _) -> r

    let eval_non_strict state e =
      let module NonStrict = Semantics (TopSemantics.NonStrictInt)(struct let from_int x = x end)(struct let cb _ = "" end) in  
      match NonStrict.Deterministic.BigStep.WithEnvT.build state e () with
      | TopSemantics.Deterministic.BigStep.Tree.Node (_, _, _, r, _, _) -> r

  end

let toplevel =  
  let module Expr = SimpleExpr 
   (Lexer.Make (struct let keywords = [] end))
   (struct 
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
            method run cb   = 
              let module Strict    = Expr.Semantics (Semantics.StrictInt)   (struct let from_int x = x end)(struct let cb = (Helpers.interval cb h) end) in
              let module NonStrict = Expr.Semantics (Semantics.NonStrictInt)(struct let from_int x = x end)(struct let cb = (Helpers.interval cb h) end) in  
              let wizard id target navigate =
                let w = HTMLView.Wizard.create id target navigate in
                w#page [
                  HTMLView.Wizard.flag   "strict";
                  HTMLView.Wizard.string "state"
                ];
		w
              in
              (wizard,
               fun c ->
                 let state = c "state" in
                 match Expr.L.fromString (ostap (!(State.parse)[Expr.L.ident][Expr.L.literal] -EOF)) state with
                 | Checked.Ok state ->
                   if c "strict" = "true" 
                   then
                     "root",
                     View.toString (
                       HTMLView.tag "div" ~attrs:"style=\"transform:scaleY(-1)\"" (
                         HTMLView.ul ~attrs:"id=\"root\" class=\"mktree\""
                           (Strict.Deterministic.BigStep.WithEnvT.html (
                              Strict.Deterministic.BigStep.WithEnvT.build state p ()
                           )
                     )))                                  
                   else
                     "root",
                     View.toString (
                       HTMLView.tag "div" ~attrs:"style=\"transform:scaleY(-1)\"" (
                         HTMLView.ul ~attrs:"id=\"root\" class=\"mktree\""
                           (NonStrict.Deterministic.BigStep.WithEnvT.html (
                              NonStrict.Deterministic.BigStep.WithEnvT.build state p ()
                           )
                     )))
		 | Checked.Fail [msg] -> "", Js_frontend.highlighted_msg state msg
              )
            method compile  = invalid_arg ""
          end
    )  

