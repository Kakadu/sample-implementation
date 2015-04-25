open Ostap.Pretty
open GT
 
module Expr =
  struct

    @type 'a t = [`Binop of string * 'a * 'a] with html, show, foldl

    class ['a] vertical =
      object (this)
        inherit ['a] @t[show]
        method c_Binop _ _ s x y = 
          Printf.sprintf "*\n%s\n%s%s" s (x.GT.fx ()) (y.GT.fx ())
      end
    
    let hparse (h : Helpers.h) ops primary s = 
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
        Ostap.Util.expr 
          (Helpers.loc (fun x l r -> h#register x (l :> Helpers.loc) (r :> Helpers.loc))) 
          (Array.map (fun (a, s) -> a, l s) ops)
          (primary parse)
          s
      in
      parse s

    let parse ops primary s =
      let h = Helpers.highlighting () in
      ostap (e:hparse[h][ops][primary] -EOF {e, h}) s

    module Semantics =
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

            module Strict (D : Semantics.Domain) =
              struct
                class virtual ['a] step =
                  object 
                    inherit [unit, D.t State.t, 'a, D.t, 'a] c 
                    method c_Binop (env, state, _) _ s x y =
                      S.Subgoals (
                        [env, state, x.GT.x; env, state, y.GT.x], 
                        (fun [x'; y'] -> S.opt_to_case "" (D.op s  x' y')), "Binop"
                      )
                  end
              end

            module NonStrict (D : Semantics.Domain) =
              struct
                class virtual ['a] step =
                  object 
                    inherit [unit, D.t State.t, 'a, D.t, 'a] c 
                    method c_Binop (env, state, _) _ s x y =
                      S.Subgoals (
                        [env, state, x.GT.x], 
                        (fun [x'] -> 
                           match D.dop s x' with 
                           | `Value   z -> S.opt_to_case "" z 
                           | `Curried f -> 
                             S.Subgoals (
                                [env, state, y.GT.x], 
                                (fun [y'] -> S.opt_to_case "" (f y')), 
                                ""
                             )
                        ), 
                        "Binop"
                      )
                  end
              end
        end
      end
  end

module SimpleExpr 
  (L : Lexer.Sig)
  (C : sig val ops : ([`Nona | `Lefta | `Righta] * string list) array end) =
  struct

    module L = L

    @type primary = [`Var of string | `Const of int] with html, show, foldl

    let nothing p x = p x

    let hparse h e s =
      let primary p = ostap (
           x:!(L.ident)   {`Var x}
        |  i:!(L.literal) {`Const i}
        |  -"(" p -")"  
        )
      in
      Expr.hparse h C.ops (e primary) s

    let parse e s =
      let h = Helpers.highlighting () in
      ostap (x:hparse[h][e] -EOF {x, h}) s;;

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
      | `Const i as node -> wrap node (HTMLView.tag "tt" (HTMLView.int i))
      | `Var   x as node -> wrap node (HTMLView.tag "tt" (HTMLView.raw x))
      | `Binop (s, x, y) as node -> 
          HTMLView.tag "tt" (
            HTMLView.seq [
              subtree x; 
              wrap node (HTMLView.raw (Printf.sprintf " %s " s)); 
              subtree y
            ]
          )

    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e      

    module TopSemantics = Semantics

    module Semantics (D : Semantics.Domain)
                     (I : sig val from_int : int -> D.t end) 
                     (C : sig val cb : 'a expr as 'a -> string end) =
      struct

        module S = Semantics.Deterministic.BigStep

        class virtual ['env, 'left, 'over, 'right, 'a] c =
          object 
            inherit ['a, 
                     'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case, 
                     'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case
                    ] @expr
          end

        class virtual ['a] base_step =
          object 
            inherit [unit, D.t State.t, 'a expr, D.t, 'a] c
            method c_Var (env, state, _) _ x = 
              (try S.Just (State.get state x, "Var") with
               | _ -> S.Nothing (Printf.sprintf "undefined variable '%s'" x, "Var")
              )
            method c_Const (env, stat, _) _ i = S.Just (I.from_int i, "Const")
          end

        module ENS = Expr.Semantics.BigStep.NonStrict(D)
        module ES  = Expr.Semantics.BigStep.Strict(D)
        
        class ['a] strict_step =
          object 
            inherit ['a] base_step
            inherit ['a] ES.step
          end

        class ['a] non_strict_step =
          object 
            inherit ['a] base_step
            inherit ['a] ENS.step
          end

        module Base =
          struct
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

        module Strict =
          struct
            module Tree = S.Tree.Make (
              struct
                include Base
                let rec step env state e = 
                  GT.transform(expr) (fun (env, state, _) e -> step env state e) (new strict_step) (env, state, e) e
              end
            )
          end

        module NonStrict =
          struct
            module Tree = S.Tree.Make (
              struct
                include Base
                let rec step env state e = 
                  GT.transform(expr) (fun (env, state, _) e -> step env state e) (new non_strict_step) (env, state, e) e
              end
            )
          end

      end

    let eval_strict state e =
      let module S = Semantics (TopSemantics.Int)(struct let from_int x = x end)(struct let cb _ = "" end) in
      match S.Strict.Tree.build () state e with
      | TopSemantics.Deterministic.BigStep.Tree.Node (_, _, _, r, _, _) -> r

    let eval_non_strict state e =
      let module S = Semantics (TopSemantics.Int)(struct let from_int x = x end)(struct let cb _ = "" end) in  
      match S.NonStrict.Tree.build () state e with
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
    (Expr.L.fromString (Expr.parse Expr.nothing))
    (fun (p, h) ->         
        object inherit Toplevel.c
            method ast cb = View.toString (
                              HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                                Expr.html (Helpers.interval cb h) p
                              )
                            )
            method vertical  = Expr.vertical p
            method run cb js = 
              let module S = Expr.Semantics (Semantics.NSInt)(struct let from_int x = x end)(struct let cb = (Helpers.interval cb h) end) in
              let state = ref State.empty in	      
              Toplevel.Wizard.Page ([
                  HTMLView.Wizard.flag "strict";
                  Toplevel.Wizard.div  "state"
               ], 
               [
                (fun page conf -> 
                  let st = conf "state" in
                  match Expr.L.fromString (ostap (!(State.parse)[Expr.L.ident][Expr.L.literal] -EOF)) st with
		  | Checked.Ok st -> 
                     state := st; 
                     true
		  | Checked.Fail [msg] ->                     
                     js#error page "state" st msg;
                     false
                ), 
                Toplevel.Wizard.Exit 
                  (fun conf ->
                    js#results "root"                   
		      (View.toString (
                         if conf "strict" = "true" 
                         then S.Strict.Tree.html "root" (S.Strict.Tree.build () !state p)
                         else S.NonStrict.Tree.html "root" (S.NonStrict.Tree.build () !state p)
		       )
                      )
                  )
               ]
              )
          end
    )

