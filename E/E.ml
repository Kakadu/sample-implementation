open Ostap
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

    class ['a] pretty prio =
      object (this)
        inherit ['a, int, Pretty.printer, int, Pretty.printer] @t
        method c_Binop p _ s x y = 
          let p' = prio s in          
          (if p' > p 
	   then (fun l -> Pretty.rboxed (Pretty.listBySpace l))
	   else Pretty.listBySpace
	  )
          [x.GT.fx p'; Pretty.string s; y.GT.fx p']
      end    

    class ['a] abbrev_html cb pretty =
      let w = new Helpers.wrap cb pretty in
      object (this)
        inherit ['a, bool, HTML.er, bool, HTML.er] @t
        method c_Binop top v s x y = 
          if top 
          then 
	    HTML.tag "tt" (
              HTML.seq [
                x.GT.fx false;
	        w#wrap v.GT.x (HTML.raw (Printf.sprintf " %s " s));
                y.GT.fx false;
	      ]
	    )
	  else w#wrap v.GT.x w#bullet
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

    module TopSemantics = Semantics

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
                        (fun [x'; y'] -> S.opt_to_case "" (D.op s  x' y')), 
		        "Binop"
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
                           | `Value   z -> S.Just (z, "Binop_Left")
                           | `Curried f -> 
                             S.Subgoals (
                                [env, state, y.GT.x], 
                                (fun [y'] -> S.opt_to_case "" (f y')), 
                                "Binop"
                             )
                        ), 
                        ""
                      )
                  end
              end

          end

        module SmallStep =
          struct

	    module S = BigStep.S

            class virtual ['e, 'v] helper =
              object
                method virtual is_value : 'e -> bool
                method virtual to_value : 'e -> 'v
                method virtual of_value : 'v -> 'e TopSemantics.opt
              end

            module Strict (D : Semantics.Domain) =
              struct
                class virtual ['a] step h =
                  object 
                    inherit [unit, D.t State.t, 'a, 'a, 'a] BigStep.c 
                    method c_Binop (env, state, _) _ s x y =
                      if h#is_value x.GT.x
                      then
                        if h#is_value y.GT.x
                        then 
                          S.opt_to_case 
			    "Binop" 
			    (Semantics.bind 
			       (D.op s (h#to_value x.GT.x) (h#to_value y.GT.x)) 
			       (fun x -> h#of_value x)
			    )
                        else 
                          S.Subgoals (
                            [env, state, y.GT.x], 
                            (fun [y'] -> S.Just (`Binop (s, x.GT.x, y'), "")), 
                            "Binop_Right"
                          )
                      else
                        S.Subgoals (
                          [env, state, x.GT.x], 
                          (fun [x'] -> S.Just (`Binop (s, x', y.GT.x), "")), 
                          "Binop_Left"
                        )
                  end
              end

            module NonStrict (D : Semantics.Domain) =
              struct
                class virtual ['a] step h =
                  object 
                    inherit [unit, D.t State.t, 'a, 'a, 'a] BigStep.c 
                    method c_Binop (env, state, _) _ s x y =
                      if h#is_value x.GT.x
                      then
                        (match D.dop s (h#to_value x.GT.x) with
			| `Value   z -> S.opt_to_case "Binop_Left_NS" (h#of_value z)
			| `Curried f ->
                            if h#is_value y.GT.x
                            then 
                              S.opt_to_case 
			        "Binop" 
			        (Semantics.bind 
			           (D.op s (h#to_value x.GT.x) (h#to_value y.GT.x)) 
                                   (fun x -> h#of_value x)
			        )
                            else 
                              S.Subgoals (
                                [env, state, y.GT.x], 
                                (fun [y'] -> S.Just (`Binop (s, x.GT.x, y'), "")), 
                                "Binop_Right"
                              )
                        )
                      else
                        S.Subgoals (
                          [env, state, x.GT.x], 
                          (fun [x'] -> S.Just (`Binop (s, x', y.GT.x), "")), 
                          "Binop_Left"
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

    class primary_abbrev_html cb pretty =
      let w = new Helpers.wrap cb pretty in
      object (this)       
        inherit [bool, HTML.er] @primary
        method c_Var   _ s x = w#wrap s.GT.x (HTML.tag "tt" (HTML.raw x))
        method c_Const _ s i = w#wrap s.GT.x (HTML.tag "tt" (HTML.int i))
      end
    
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

    let maxprio = Array.length C.ops 

    exception Index of int 

    let prio s =
      try 
	ignore (
	  Array.mapi 
	    (fun i (_, ops) -> 
	      try ignore (List.find (fun s' -> s' = s) ops); raise (Index i)
	      with Not_found -> ()
	    ) 
	    C.ops
        );
        maxprio
      with Index i -> i

    class ['a] pretty prio =
      object (this)
        inherit ['a, int, Pretty.printer, int, Pretty.printer] @expr
        inherit ['a] Expr.pretty prio
        method c_Var   _ _ x = Pretty.string x
        method c_Const _ _ i = Pretty.int i
      end

    let pretty e = 
      let rec inner e = transform(expr) (lift inner) (new pretty prio) maxprio e in
      Pretty.toString (inner e)
   
    class ['a] html =
      object (this)
        inherit ['a] @expr[html]
        inherit Helpers.cname
      end

    let rec html cb e = 
      HTML.li ~attrs:(cb.Helpers.f e) (transform(expr) (fun _ -> html cb) (new html) () e)

    let cast f = fun x -> f (x :> 'a expr)

    class ['a] abbrev_html cb pretty =
      object (this)
        inherit ['a, bool, HTML.er, bool, HTML.er] @expr
        inherit ['a] Expr.abbrev_html cb (cast pretty)
        inherit primary_abbrev_html cb (cast pretty)
      end

    let abbreviate_html cb e = 
      let c = new abbrev_html cb pretty in
      let rec inner top e = transform(expr) inner c top e in
      inner true e

    class ['a] vertical =
      object (this)
        inherit ['a] @expr[show]
        inherit ['a] Expr.vertical
        method c_Var _ _ x = Printf.sprintf "x\n%s\n" x
        method c_Const _ _ i = Printf.sprintf "c\n%d\n" i
      end

    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e      

    module TopSemantics = Semantics

    module type I = sig type t val from_int : int -> t val to_int : t -> int TopSemantics.opt end
    module type C = sig val cb : Helpers.poly end

    module Semantics (D : Semantics.Domain)
                     (I : I with type t = D.t) 
                     (C : C) =
      struct

        module BigStep =
          struct

            module S = TopSemantics.Deterministic.BigStep
            module EBS = Expr.Semantics.BigStep

            class virtual ['env, 'left, 'over, 'right, 'a] c =
              object 
                inherit ['a, 
                         'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case,
			 'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case] @expr
              end
            
            class virtual ['a, 'b] base_step =
              object 
                inherit [unit, D.t State.t, 'b, D.t, 'a] c
                method c_Var (env, state, _) _ x = 
                  (try S.Just (State.get state x, "Var") with
                   | _ -> S.Nothing (Printf.sprintf "undefined variable '%s'" x, "Var")
                  )
                method c_Const (env, stat, _) _ i = S.Just (I.from_int i, "Const")
              end

            module ENS = EBS.NonStrict(D)
            module ES  = EBS.Strict(D)
                    
            class ['a, 'b] strict_step =
              object 
                inherit ['a, 'b] base_step
                inherit ['a] ES.step
              end

            class ['a, 'b] non_strict_step =
              object 
                inherit ['a, 'b] base_step
                inherit ['a] ENS.step
              end

            module MakeBase (O : sig type over val over_html : over -> HTML.er end) =
              struct
                include O

                type env   = unit
                type left  = D.t State.t
                type right = D.t

                let env_html   = HTML.unit
                let left_html  = State.html D.show
                let right_html = D.html

                let customizer =
                  object 
                    inherit S.Tree.html_customizer
                    method show_env   = false
                    method over_width = 70
		    method arrow      = "&rArr;"
                  end
              end

            module Base = MakeBase (
	      struct 
                type over = 'a expr as 'a 
                let over_html = abbreviate_html C.cb
              end
	    ) 

            module Strict =
              struct
                module Tree = S.Tree.Make (
                  struct
                    include Base
                    let rec step env state e = 
                      GT.transform(expr) 
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
                      GT.transform(expr) 
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

            class helper =
              object
                inherit ['a expr as 'a, D.t] Expr.Semantics.SmallStep.helper
		method is_value e = match e with `Const _ -> true | _ -> false
                method to_value (`Const i) = I.from_int i
                method of_value i = TopSemantics.bind (I.to_int i) (fun i -> TopSemantics.Good (`Const i))
              end

            class virtual ['a, 'b] base_step h =
              object 
                inherit [unit, D.t State.t, 'b, 'b, 'a] BigStep.c
                method c_Var (env, state, _) _ x = 
                  (try S.opt_to_case "Var" (h#of_value (State.get state x)) with
                   | _ -> S.Nothing (Printf.sprintf "undefined variable '%s'" x, "Var")
                  )
                method c_Const (env, stat, _) _ i = S.opt_to_case "Const" (h#of_value (I.from_int i))
              end

            module ES  = Expr.Semantics.SmallStep.Strict(D)
            module ENS = Expr.Semantics.SmallStep.NonStrict(D)
        
            class ['a, 'b] strict_step =
              let h = new helper in
              object 
                inherit ['a, 'b] base_step h
                inherit ['a] ES.step h
              end

            class ['a, 'b] non_strict_step =
              let h = new helper in
              object 
                inherit ['a, 'b] base_step h
                inherit ['a] ENS.step h
              end
            
            module MakeBase (O : sig type t val html : t -> HTML.er end) =
              struct
                type env   = unit
                type left  = D.t State.t
                type over  = O.t
                type right = O.t

                let env_html   = HTML.unit
                let left_html  = State.html D.show
                let over_html  = O.html
                let right_html = O.html

                let customizer =
                  object 
                    inherit S.Tree.html_customizer
                    method show_env   = false
                    method over_width = 70
                  end
              end

            module Base = MakeBase (
              struct 
                type t = 'a expr as 'a 
                let html = abbreviate_html C.cb 
              end)

            module Strict = Semantics.Deterministic.SmallStep.Make (
              struct
                include Base
                let rec step env state e = 
                  GT.transform(expr) 
	            (fun (env, state, _) e -> step env state e) 
		    (new strict_step) 
		    (env, state, e) 
		    e
		let rewrite env state e = function `Const x -> None | e' -> Some (env, state, e')
              end
            )

            module NonStrict = Semantics.Deterministic.SmallStep.Make (
              struct
                include Base
                let rec step env state e = 
                  GT.transform(expr) 
	            (fun (env, state, _) e -> step env state e) 
		    (new non_strict_step) 
		    (env, state, e) 
		    e
		let rewrite env state e = function `Const x -> None | e' -> Some (env, state, e')
              end
            )

          end    

      end

    module DInt = 
      struct
        type t = TopSemantics.Int.t 

        let from_int x = x 
        let to_int   x = TopSemantics.Good x
      end

    let eval_strict state e =
      let module S = Semantics (TopSemantics.Int)(DInt)(struct let cb = {Helpers.f = fun _ -> ""} end) in
      match S.BigStep.Strict.Tree.build () state e with
      | TopSemantics.Deterministic.BigStep.Tree.Node (_, _, _, r, _, _) -> r

    let eval_non_strict state e =
      let module S = Semantics (TopSemantics.Int)(DInt)(struct let cb = {Helpers.f = fun _ -> ""} end) in  
      match S.BigStep.NonStrict.Tree.build () state e with
      | TopSemantics.Deterministic.BigStep.Tree.Node (_, _, _, r, _, _) -> r

  end

module LExpr (L : Lexer.Sig) = SimpleExpr 
  (L)
  (struct
     let ops = [|
        `Lefta, ["||"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
      |] 
   end)

let wizard context =
  let state = ref State.empty in	        
  Toplevel.Wizard.Page ([
    HTML.Wizard.flag  "strict";
    HTML.Wizard.combo "type" [
      HTML.raw "Big-Step"  , "bigstep"  , "selected=\"true\""; 
      HTML.raw "Small-Step", "smallstep", ""
    ];
    Toplevel.Wizard.div ~attrs:("style=\"width:200px\"") "state"
   ], 
   [
    (fun page conf -> 
       let st = conf "state" in
         match context#parse st with
         | Checked.Ok st -> 
             state := st; 
             true
         | Checked.Fail [msg] ->                     
             context#error page "state" st msg;
             false
    ), 
    Toplevel.Wizard.Exit (context#callback state)
   ]
  )

let toplevel =  
  let module Expr = LExpr (Lexer.Make (struct let keywords = [] end)) in
  Toplevel.make 
    (Expr.L.fromString (Expr.parse Expr.nothing))
    (fun (p, h) ->         
       object inherit Toplevel.c
         method ast cb = View.toString (
                           HTML.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                             Expr.html (Helpers.interval cb h) p
                           )
                         )
         method vertical  = Expr.vertical p
         method run cb js = 
           let module S = Expr.Semantics (Semantics.NSInt)(Expr.DInt)(struct let cb = (Helpers.interval cb h) end) in
           wizard 
             (object 
                method parse st = Expr.L.fromString (ostap (!(State.parse)[Expr.L.ident][Expr.L.literal] -EOF)) st
                method error = js#error
                method callback st conf =
		  let descr, tree =
                    if conf "type" = "bigstep"
                    then
                      if conf "strict" = "true" 
                      then "E_BS_S", S.BigStep.Strict.Tree.html "root" (S.BigStep.Strict.Tree.build () !st p)
                      else "E_BS_NS", S.BigStep.NonStrict.Tree.html "root" (S.BigStep.NonStrict.Tree.build () !st p)
                    else 
                      if conf "strict" = "true"
                      then "E_SS_S", S.SmallStep.Strict.html "root" (S.SmallStep.Strict.build () !st p)
                      else "E_SS_NS", S.SmallStep.NonStrict.html "root" (S.SmallStep.NonStrict.build () !st p)	              
		  in
                  js#results "root" (View.toString tree) descr
              end
             )
       end
    )

