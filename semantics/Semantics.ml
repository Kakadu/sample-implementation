@type 'a opt = Good of 'a | Bad of GT.string with html

let (>>=) x f =
  match x with Good x' -> f x' | Bad s -> Bad s

let bind = (>>=)

module type Algebra =
 sig

   type t
   val op   : string -> t -> t -> t opt
   val show : t -> string
   val html : t -> HTML.er

 end

module type Domain =
 sig

   include Algebra
   val dop : string -> t -> [`Value of t | `Curried of t -> t opt]

 end

module MakeDomain (A : Algebra) (S : sig val spec : (string * (A.t -> bool)) list end) =
 struct

   type t = A.t
 
   let show = A.show
   let html = A.html
  
   let dop s x =
     try
       let _, p = List.find (fun (s', _) -> s' = s) S.spec in
       if p x then `Value x else `Curried (A.op s x)
     with Not_found -> `Curried (A.op s x)

   let op s x y = 
     match dop s x with 
     | `Value   z -> Good z 
     | `Curried f -> f y

 end

module IntA =
  struct

   type t = int

   exception NotABool 

   let op = 
     let b    f x y = if f x y then 1 else 0 in
     let lift f x y = try Good (f x y) with NotABool -> Bad "not a boolean value" in
     let ib = function 0 -> 0 | 1 -> 1 | _ -> raise NotABool in    
     function
     | "+"  -> lift (+)
     | "-"  -> lift (-)
     | "*"  -> lift ( * ) 
     | "/"  -> (fun x y -> if y = 0 then Bad "division by zero" else Good (x / y))
     | "%"  -> (fun x y -> if y = 0 then Bad "division by zero" else Good (x mod y))
     | "==" -> lift (b (=))
     | "!=" -> lift (b (<>))
     | "<=" -> lift (b (<=))
     | "<"  -> lift (b (<))
     | ">=" -> lift (b (>=))
     | ">"  -> lift (b (>))
     | "&&" -> lift (fun x y -> ib x * ib y)
     | "||" -> lift (fun x y -> ib x + ib y)

   let show = string_of_int
   let html = HTML.int

 end

module NSIntSpec = struct let spec = ["*", (=) 0; "&&", (=) 0; "||", (=) 1] end
module IntSpec   = struct let spec = [] end

module NSInt = MakeDomain (IntA)(NSIntSpec)
module Int   = MakeDomain (IntA)(IntSpec)

module Deterministic =
  struct 

    module BigStep =
      struct

        type ('env, 'left, 'over, 'right) case = 
          Nothing  of string * string
        | Just     of 'right * string
        | Subgoals of ('env * 'left * 'over) list * ('right list -> ('env, 'left, 'over, 'right) case) * string	

	let rec unfold f = function
	| Subgoals (l, g, _) -> 
	    let l' =
	      List.map 
		(fun triple -> 
		  match f triple with
		  | Subgoals _ as s -> unfold f s
		  | x -> x
		) 
		l
	    in
	    (try g (List.map (function Just (r, _) -> r) l') with
	       Match_failure _ -> Nothing ("", "")
	    )
	| x -> x

        let opt_to_case rule = function
	| Good x     -> Just (x, rule)
	| Bad reason -> Nothing (reason, rule)

        module Tree =
          struct

            @type ('env, 'left, 'over, 'right) t = 
              Node of 'env * 'left * 'over * 'right opt * ('env, 'left, 'over, 'right) t GT.list * GT.string
            with html

            class html_customizer =
              object
                method show_env    = true
                method show_over   = true
                method show_rule   = true
                method arrow_scale = 5
                method arrow       = "&rarr;"
                method over_width  = 150
                method background  = "lavender"
              end

            let default_customizer = new html_customizer

            class ['env, 'left, 'over, 'right] custom_html customizer =
              object(this)
                inherit ['env, 'left, 'over, 'right] @t[html]
                method c_Node s orig env left over right subnodes rule =
                  let node = HTML.table ~attrs:(Printf.sprintf "style=\"background-color:%s;transform:scaleY(-1)\"" customizer#background) (
                      HTML.seq [ 
                        HTML.tr (
                          HTML.seq [
                            if customizer#show_env
                               then HTML.seq [
                                      HTML.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTML.tag "nobr" (env.GT.fx ()));
                                      HTML.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTML.raw "&vdash;")
                                    ]
                               else View.empty;
                            HTML.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTML.tag "nobr" (left.GT.fx ()));
                            if customizer#show_over 
                               then HTML.td ~attrs:(Printf.sprintf "width=\"%dpx\"align=\"center\"" customizer#over_width) 
                                      (HTML.tag "nobr" (over.GT.fx ()))
                               else HTML.td (HTML.raw "&nbsp;");
                            HTML.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" 
                              (match right with 
                              | Bad t -> HTML.raw (Printf.sprintf "<attr title=\"%s\"><font color=\"red\">&#8224;</font></attr>" t)
                              | Good r -> HTML.tag "nobr" (orig.GT.t#right () r)
                              );
                            if customizer#show_rule && rule <> ""
                               then HTML.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\" style=\"font-size:80%\"" 
                                      (HTML.tag "nobr" (HTML.raw ("&nbsp;(<i>by</i>&nbsp;[" ^ rule ^ "])")))
                               else View.empty
                          ]
                        );
                        HTML.tr (
                          HTML.td ~attrs:(Printf.sprintf "width=\"%dpx\"align=\"center\" valign=\"center\"" customizer#over_width) (
                            HTML.tag ~attrs:(Printf.sprintf "style=\"display:inline-block;transform:scale(%d,1)\"" customizer#arrow_scale)
                              "span" (HTML.raw customizer#arrow)
                          )
                        );
                        HTML.tr (HTML.td (HTML.raw "&nbsp;"))
                      ]
                    )
                  in
                  if List.length subnodes = 0 
                  then HTML.li node
                  else HTML.li (
                         HTML.seq [
                           node;
                           HTML.ul (
                             HTML.seq (
                               List.map 
                                 (GT.transform(t) orig.GT.t#env orig.GT.t#left orig.GT.t#over orig.GT.t#right this ()) 
                                 subnodes
                             )
                           )
                         ]
                       )              

              end

            let html id customizer env left over right tree = 
              HTML.tag "div" ~attrs:"style=\"transform:scaleY(-1)\"" (
                HTML.ul ~attrs:(Printf.sprintf "id=\"%s\" class=\"mktree\"" id)
                  (GT.transform(t) env left over right (new custom_html customizer) () tree)
              )

            exception SomeBad of string

            let build ?(limit=(-1)) step env left over =
              let rec inner i env left over =
                if i != 0 then 
                  match step env left over with
    	          | Nothing (reason, rule) -> Node (env, left, over, Bad reason, [], "")
                  | Just (right, rule) -> Node (env, left, over, Good right, [], rule)
                  | Subgoals (triples, fright, rule) ->
                      let rec process_subgoals subnodes subgoals subfun rule =
                        let define_rule r = if rule = "" then r else rule in
                        let subnodes' = List.map (fun (env', left', over') -> inner (i-1) env' left' over') subgoals in
			try
                          let rights = List.map (function 
                                                 | Node (_, _, _, Good r, _, _) -> r
				                 | Node (_, _, _, Bad t, _, _) -> raise (SomeBad t)
                                                ) subnodes'
                          in
                          match subfun rights with
	  	          | Just     (right  , rule)         -> Node (env, left, over, Good right, subnodes@subnodes', define_rule rule)
                          | Nothing  (reason , rule)         -> Node (env, left, over, Bad reason, subnodes@subnodes', "")
                          | Subgoals (triples, fright, rule) -> process_subgoals (subnodes@subnodes') triples fright (define_rule rule)
			with SomeBad t -> Node (env, left, over, Bad t, subnodes @ subnodes', "")
		      in
		      process_subgoals [] triples fright rule
                else Node (env, left, over, Bad "step limit reached", [], "")
              in
              inner limit env left over

              module Make (C : sig 

                                 type env
                                 type left
                                 type over
                                 type right

                                 val step : env -> left -> over -> (env, left, over, right) case

                                 val env_html   : env   -> HTML.viewer
                                 val left_html  : left  -> HTML.viewer
                                 val over_html  : over  -> HTML.viewer
                                 val right_html : right -> HTML.viewer

                                 val customizer : html_customizer

                               end
                          ) =
                struct
                  let build ?(limit=(-1)) = build ~limit:limit C.step
                  let html id = html id C.customizer (GT.lift C.env_html) (GT.lift C.left_html) (GT.lift C.over_html) (GT.lift C.right_html)		   
		  let build_html ?(limit=(-1)) env left over id = html id (build ~limit:limit env left over)
                end

          end    
      end

    module SmallStep =
      struct

        module Make (C : sig 
                           type env
                           type left
                           type over
                           type right

                           val step       : env -> left -> over -> (env, left, over, right) BigStep.case
                           val rewrite    : env -> left -> over -> right -> (env * left * over) option

                           val env_html   : env   -> HTML.viewer
                           val left_html  : left  -> HTML.viewer
                           val over_html  : over  -> HTML.viewer
                           val right_html : right -> HTML.viewer

                           val customizer : BigStep.Tree.html_customizer
                         end
                    ) =
          struct
            module T = BigStep.Tree.Make (C)

            let build ?(limit=(-1)) env left over =
              let rec inner n acc env left over = 
                if n = 0 then acc
                else 
		  let tree =  T.build env left over in
		  let acc  = tree :: acc in
		  match tree with
		  | BigStep.Tree.Node (env, left, over, Good right, _ , _) -> 
		      (match C.rewrite env left over right with
		       | Some (env', left', over') -> inner (n-1) acc env' left' over'
		       | None -> acc
		      )
		  | _ -> acc
              in
              List.rev (inner limit [] env left over)

	    let html id seq =
	      HTML.table ~attrs:(Printf.sprintf "id=\"%s\"" id) (
                HTML.seq (
                  List.mapi 
                    (fun i t -> 
		      (fun h -> 
			if i > 0 
			then HTML.seq [HTML.tr (HTML.td (HTML.raw "<hr>")); h]
		        else h                        
                      )
		      (HTML.tr (HTML.td (T.html (Printf.sprintf "__discard_%s_%d" id i) t))))
                    seq
	        )
              )
              
	    let build_html ?(limit=(-1)) env left over id = html id (build ~limit:limit env left over)

          end

      end

  end
