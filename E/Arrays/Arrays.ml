open Ostap
open GT

module Expr = 
  struct

    module Base = E.LExpr (Lexer.Make (struct let keywords = [] end))

    @type 'a aexpr = [
      'a Base.expr 
    | `Indexed of 'a * 'a 
    | `Array   of 'a list
    ] with html, show, foldl

    let hparse h e s = 
      Base.hparse h 
	(fun p x ->            
	   ostap (
             base:(l:($)  "{" elems:!(Ostap.Util.list)[x] "}" r:($) {
                       h#register (`Array elems) (l :> Helpers.loc) (r :> Helpers.loc)
                     }
                   | !(e (p x)) 
                  ) 
             indices:(-"[" x -"]")* {
               List.fold_left (fun b i -> `Indexed (b, i)) base indices
             }
	  )
	) 
	s
    
    let parse e s = 
      let h = Helpers.highlighting () in
      ostap (x:hparse[h][e] -EOF {x, h}) s

    class ['a] pretty prio =
      object (this)
        inherit ['a, int, Pretty.printer, int, Pretty.printer] @aexpr
        inherit ['a] Base.pretty prio
        method c_Array _ v elems = 
	  Pretty.cboxed (Pretty.listByComma (List.map (v.GT.t#a Base.maxprio) elems))
        method c_Indexed _ _ base index = 
	  Pretty.seq [base.GT.fx Base.maxprio; Pretty.sboxed (index.GT.fx Base.maxprio)]
      end
  
    let pretty e = 
      let rec inner e = 
	transform(aexpr) (lift inner) (new pretty Base.prio) Base.maxprio e 
      in
      Pretty.toString (inner e)

    class ['a] html =
      object (this)
        inherit ['a] @aexpr[html]
        inherit ['a] Base.html
      end

    let rec html cb e =
      HTMLView.li ~attrs:(cb.Helpers.f e) (transform(aexpr) (fun _ -> html cb) (new html) () e)

    let cast f = fun x -> f (x :> 'a aexpr)

    class ['a] abbrev_html cb pretty =
      let w = new Helpers.wrap cb pretty in
      object (this)
        inherit ['a, bool, HTMLView.er, bool, HTMLView.er] @aexpr
        inherit ['a] Base.abbrev_html cb (cast pretty)
        method c_Indexed top v base index = 
	  w#wrap v.GT.x 
	    (if top 
	     then
	       HTMLView.seq [
                 base.GT.fx false;
	         HTMLView.tag "tt" (HTMLView.raw "[");
	         index.GT.fx false;
	         HTMLView.tag "tt" (HTMLView.raw "]");
               ]
	     else w#bullet
            )
        method c_Array top v elems = 
	  w#wrap v.GT.x
            (if top && List.length elems <= 1
             then
               HTMLView.seq (
                 HTMLView.tag "tt" (HTMLView.raw "{") ::
                 List.map (fun e -> v.GT.t#a false e) elems @
                 [HTMLView.tag "tt" (HTMLView.raw "}")]
	       )
             else w#bullet
            )
      end

    let abbreviate_html cb e = 
      let c = new abbrev_html cb pretty in
      let rec inner top e = transform(aexpr) inner c top e in
      inner true e

    module TopSemantics = Semantics

    module type A =
      sig
        include Base.I
        val make  : t list -> t      
        val index : t -> t -> t Semantics.opt
      end

    module Semantics (D : TopSemantics.Domain)
                     (A : A with type t = D.t)
                     (C : Base.C) =
      struct

        module BaseSemantics = Base.Semantics (D)(A)(C)

        module BigStep =
          struct
           
            module S = BaseSemantics.BigStep.S 

            class virtual ['env, 'left, 'over, 'right, 'a] c =
              object
                inherit ['a, 
                         'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case, 
                         'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case
                        ] @aexpr
              end

            class virtual ['a, 'b] base_step =
              object
                inherit [unit, D.t State.t, 'b, D.t, 'a] c
                method c_Array (env, state, _) x elems = 
                  S.Subgoals (
                    List.map (fun e -> env, state, e) elems, 
                    (fun elems -> S.Just (A.make elems, "")), 
                    "Array"
                  )
                method c_Indexed (env, state, _) x base index = 
                  S.Subgoals (
                    [env, state, base.GT.x; env, state, index.GT.x], 
                    (fun [base; index] -> S.opt_to_case "" (A.index base index)),
                    "Index"
                  )
              end
            
            class ['a, 'b] strict_step =
              object
                inherit ['a, 'b] BaseSemantics.BigStep.strict_step
                inherit ['a, 'b] base_step
              end

            class ['a, 'b] non_strict_step =
              object
                inherit ['a, 'b] BaseSemantics.BigStep.non_strict_step
                inherit ['a, 'b] base_step
              end

            module Base = BaseSemantics.BigStep.MakeBase (
              struct
                type over  = 'a aexpr as 'a
                let over_html  = abbreviate_html C.cb
              end
	    )

            module Strict =
              struct
                module Tree = S.Tree.Make (
                  struct
                    include Base
                    let rec step env state e =
                      GT.transform(aexpr)
                        (fun (env, state, _) e -> step env state e)
                        (new strict_step)
                        (env, state, e)
                        e
                  end
                )
              end

            module NonStrict =
              struct
                module Tree = S.Tree.Make (
                  struct
                    include Base
                    let rec step env state e =
                      GT.transform(aexpr)
                        (fun (env, state, _) e -> step env state e)
                        (new non_strict_step)
                        (env, state, e)
                        e
                  end
                )
              end

          end

        module SmallStep =
          struct
          end

      end

    module IntArrayA =
      struct

        type t = I of int | A of t list
            
        let op s x y =
          match x, y with
          | I x, I y -> TopSemantics.bind (TopSemantics.IntA.op s x y) (fun l -> Good (I l))
          | _  , _   -> Bad "not a scalar value"

        let rec show = function 
        | I x -> TopSemantics.IntA.show x
        | A a -> Printf.sprintf "{%s}" (Helpers.concat (Helpers.intersperse ", " (List.map show a)))

        let html = function
        | I x -> TopSemantics.IntA.html x
        | (A a) as x -> HTMLView.tag "attr" ~attrs:(Printf.sprintf "title=\"%s\"" (show x)) (HTMLView.raw "{&#8226;}")

        module Spec (S : sig val spec : (string * (int -> bool)) list end) =
          struct
            let spec = List.map (fun (s, f) -> s, function I x -> f x | _ -> false) S.spec
          end

        module D =
          struct

            let from_int x = I x
            let to_int = function 
            | I x -> TopSemantics.Good x 
            | _   -> TopSemantics.Bad "not a scalar value"

          end
            
      end

      module NSIntArray = TopSemantics.MakeDomain (IntArrayA)(IntArrayA.Spec (TopSemantics.NSIntSpec))
      module IntArray   = TopSemantics.MakeDomain (IntArrayA)(IntArrayA.Spec (TopSemantics.IntSpec))

  end

let toplevel =  
  Toplevel.make 
    (Expr.Base.L.fromString (Expr.parse Expr.Base.nothing))
    (fun (p, h) ->         
        object inherit Toplevel.c
            method ast cb = View.toString (
                              HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                                Expr.html (Helpers.interval cb h) p
                              )
                            )
            method vertical  = invalid_arg "" (* Expr.vertical p *)
            method run cb js = invalid_arg "" 
          end
    )


