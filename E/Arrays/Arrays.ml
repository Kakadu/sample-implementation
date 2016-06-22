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
      HTML.li ~attrs:(cb.Helpers.f e) (transform(aexpr) (fun _ -> html cb) (new html) () e)

    let cast f = fun x -> f (x :> 'a aexpr)

    class ['a] abbrev_html cb pretty =
      let w = new Helpers.wrap cb pretty in
      object (this)
        inherit ['a, bool, HTML.er, bool, HTML.er] @aexpr
        inherit ['a] Base.abbrev_html cb (cast pretty)
        method c_Indexed top v base index = 
	  w#wrap v.GT.x 
	    (if top 
	     then
	       HTML.seq [
                 base.GT.fx false;
	         HTML.tag "tt" (HTML.raw "[");
	         index.GT.fx false;
	         HTML.tag "tt" (HTML.raw "]");
               ]
	     else w#bullet
            )
        method c_Array top v elems = 
	  w#wrap v.GT.x
            (if top && List.length elems <= 1
             then
               HTML.seq (
                 HTML.tag "tt" (HTML.raw "{") ::
                 List.map (fun e -> v.GT.t#a false e) elems @
                 [HTML.tag "tt" (HTML.raw "}")]
	       )
             else HTML.seq [HTML.raw "{"; w#bullet; HTML.raw "}"]
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
        val make     : t list -> t      
        val index    : t -> t -> t Semantics.opt
        val of_value : t -> ('a aexpr as 'a) Semantics.opt
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
                type over = 'a aexpr as 'a
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

            module S = BigStep.S

            let rec is_value = function
            | `Const _     -> true 
	    | `Array elems -> List.fold_left (fun f e -> f && is_value e) true elems
	    | _            -> false

            class helper =
              object (this)
                inherit ['a aexpr as 'a, D.t] E.Expr.Semantics.SmallStep.helper
                method is_value = is_value
		method to_value e =
		  match e with
		  | `Const i     -> A.from_int i
                  | `Array elems -> A.make (List.map this#to_value elems)
		method of_value v = A.of_value v
              end

	    class virtual ['a, 'b] base_step h =
              object
                inherit [unit, D.t State.t, 'b, 'b, 'a] BigStep.c
                method c_Array (env, state, _) x elems =
                  let rec inner zip = function
		  | []    -> S.Just (`Array (List.rev zip), "Array")
		  | e::es ->
                      if h#is_value e 
                      then inner (e::zip) es
                      else 
                        S.Subgoals (
                          [env, state, e],
                          (fun [e'] -> S.Just (`Array (List.rev (e'::zip) @ es), "")),
                          "Array_Elem"
                        )
                  in
                  inner [] elems
                method c_Indexed (env, state, _) x base index =
                  if h#is_value base.GT.x
                  then if h#is_value index.GT.x
                       then 
                         let bv = h#to_value base.GT.x in
                         let iv = h#to_value index.GT.x in
                         S.opt_to_case "Indexed" (TopSemantics.bind (A.index bv iv) h#of_value)
                       else 
                         S.Subgoals (
                           [env, state, index.GT.x],
                           (fun [index'] -> S.Just (`Indexed (base.GT.x, index'), "")),
                           "Indexed_Index"
                         )                    
                  else 
                    S.Subgoals (
                      [env, state, base.GT.x],
                      (fun [base'] -> S.Just (`Indexed (base', index.GT.x), "")),
                      "Indexed_Base"
                    )
              end

            module ES  = E.Expr.Semantics.SmallStep.Strict(D)
            module ENS = E.Expr.Semantics.SmallStep.NonStrict(D)
        
            class ['a, 'b] strict_step =
              let h = new helper in
              object 
                inherit ['a, 'b] base_step h
                inherit ['a, 'b] BaseSemantics.SmallStep.base_step h
		inherit ['a] ES.step h
              end

            class ['a, 'b] non_strict_step =
              let h = new helper in
              object 
                inherit ['a, 'b] base_step h
                inherit ['a, 'b] BaseSemantics.SmallStep.base_step h
		inherit ['a] ENS.step h
              end

            module Base = BaseSemantics.SmallStep.MakeBase (
              struct
                type t = 'a aexpr as 'a
                let html = abbreviate_html C.cb
              end)

            module Strict = Semantics.Deterministic.SmallStep.Make (
              struct
                include Base
                let rec step env state e =
                  GT.transform(aexpr)
                    (fun (env, state, _) e -> step env state e)
                    (new strict_step)
                    (env, state, e)
                    e
                let rewrite env state e r = if is_value r then None else Some (env, state, r)
              end
            )

            module NonStrict = Semantics.Deterministic.SmallStep.Make (
              struct
                include Base
                let rec step env state e =
                  GT.transform(aexpr)
                    (fun (env, state, _) e -> step env state e)
                    (new non_strict_step)
                    (env, state, e)
                    e
                let rewrite env state e r = if is_value r then None else Some (env, state, r)
              end
            )

          end
      end
  end

module IntArrayA =
  struct

    type t = I of int | A of t list
            
    let op s x y =
      match x, y with
      | I x, I y -> Semantics.bind (Semantics.IntA.op s x y) (fun l -> Good (I l))
      | _  , _   -> Bad "not a scalar value"

    let rec show = function 
    | I x -> Semantics.IntA.show x
    | A a -> Printf.sprintf "{%s}" (Helpers.concat (Helpers.intersperse ", " (List.map show a)))

    let html = function
    | I x -> Semantics.IntA.html x
    | (A a) as x -> HTML.tag "attr" ~attrs:(Printf.sprintf "title=\"%s\"" (show x)) (HTML.raw "{&#8226;}")

    module Spec (S : sig val spec : (string * (int -> bool)) list end) =
      struct
        let spec = List.map (fun (s, f) -> s, function I x -> f x | _ -> false) S.spec
      end
            
  end

module D =
  struct

    type t = IntArrayA.t = I of int | A of t list

    let from_int x = I x
    let to_int = function 
    | I x -> Semantics.Good x 
    | _   -> Semantics.Bad "not a scalar value"

    let make elems = A elems
    let index base index =
      match base with
      | I _     -> Semantics.Bad "base value is not an array"
      | A elems -> 
         (match index with
          | I i -> 
            if i >= List.length elems 
            then Semantics.Bad "index value out of bounds" 
            else Semantics.Good (List.nth elems i)
	  | _ -> Semantics.Bad "index value not an integer"
	 )
    let rec of_value d =
      match d with
      | I i     -> Semantics.Good (`Const i)
      | A elems ->
          try Semantics.Good (`Array (List.map (fun e -> match of_value e with Semantics.Good v -> v) elems))
          with _ -> Semantics.Bad "not a value"
  end

module NSIntArray = Semantics.MakeDomain (IntArrayA)(IntArrayA.Spec (Semantics.NSIntSpec))
module IntArray = Semantics.MakeDomain (IntArrayA)(IntArrayA.Spec (Semantics.IntSpec))

let toplevel =  
  Toplevel.make 
    (Expr.Base.L.fromString (Expr.parse Expr.Base.nothing))
    (fun (p, h) ->         
       object inherit Toplevel.c
         method ast cb = View.toString (
                           HTML.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                             Expr.html (Helpers.interval cb h) p
                           )
                         )
         method vertical  = invalid_arg "" (* Expr.vertical p *)
         method run cb js = 
           let module NS = Expr.Semantics(NSIntArray)(D)(struct let cb = (Helpers.interval cb h) end) in
           let module S  = Expr.Semantics(IntArray  )(D)(struct let cb = (Helpers.interval cb h) end) in
           E.wizard 
             (object 
                method parse st = 
                  let ostap (
                     value: 
                       x:!(Expr.Base.L.literal)      {IntArrayA.I x} 
                     | "{" x:!(Util.list)[value] "}" {IntArrayA.A x}
                  )
		  in
		  Expr.Base.L.fromString (ostap (!(State.parse)[Expr.Base.L.ident][value] -EOF)) st
                method error = js#error
                method callback st conf =
		  let descr, tree =
                    if conf "type" = "bigstep"
                    then
                      if conf "strict" = "true" 
                      then "Arrays", S.BigStep.Strict.Tree.html "root" (S.BigStep.Strict.Tree.build () !st p)
                      else "Arrays", NS.BigStep.NonStrict.Tree.html "root" (NS.BigStep.NonStrict.Tree.build () !st p)
                    else 
		      if conf "strict" = "true"
		      then "Arrays", S.SmallStep.Strict.html "root" (S.SmallStep.Strict.build () !st p)
		      else "Arrays", NS.SmallStep.NonStrict.html "root" (NS.SmallStep.NonStrict.build () !st p)
		  in
                  js#results "root" (View.toString tree) descr
              end
             )
       end
    )


