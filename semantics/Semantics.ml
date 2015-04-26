@type 'a opt = Good of 'a | Bad of GT.string with html

let (>>=) x f =
  match x with Good x' -> f x' | Bad s -> Bad s

let bind = (>>=)

module type Algebra =
 sig

   type t
   val op   : string -> t -> t -> t opt
   val show : t -> string
   val html : t -> HTMLView.er

 end

module type Domain =
 sig

   include Algebra
   val dop : string -> t -> [`Value of t opt | `Curried of t -> t opt]

 end

module MakeDomain (A : Algebra) (S : sig val spec : (string * (A.t -> bool)) list end) =
 struct

   type t = A.t
 
   let show = A.show
   let html = A.html
  
   let dop s x =
     try
       let _, p = List.find (fun (s', _) -> s' = s) S.spec in
       if p x then `Value (Good x) else `Curried (A.op s x)
     with Not_found -> `Curried (A.op s x)

   let op s x y = 
     match dop s x with 
     | `Value   z -> z 
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
   let html = HTMLView.int

 end

module NSInt = MakeDomain (IntA)(struct let spec = ["*", (=) 0; "&&", (=) 0; "||", (=) 1] end)
module Int   = MakeDomain (IntA)(struct let spec = [] end)

module Deterministic =
  struct 

    module BigStep =
      struct

        type ('env, 'left, 'over, 'right) case = 
          Nothing  of string * string
        | Just     of 'right * string
        | Subgoals of ('env * 'left * 'over) list * ('right list -> ('env, 'left, 'over, 'right) case) * string	

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
                method arrow_scale = 6
                method arrow       = "&rarr;"
                method over_width  = 150
                method background  = "lavender"
              end

            let default_customizer = new html_customizer

            class ['env, 'left, 'over, 'right] custom_html customizer =
              object(this)
                inherit ['env, 'left, 'over, 'right] @t[html]
                method c_Node s orig env left over right subnodes rule =
                  let node = HTMLView.table ~attrs:(Printf.sprintf "style=\"background-color:%s;transform:scaleY(-1)\"" customizer#background) (
                      HTMLView.seq [ 
                        HTMLView.tr (
                          HTMLView.seq [
                            if customizer#show_env
                               then HTMLView.seq [
                                      HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTMLView.tag "nobr" (env.GT.fx ()));
                                      HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTMLView.raw "&vdash;")
                                    ]
                               else View.empty;
                            HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTMLView.tag "nobr" (left.GT.fx ()));
                            if customizer#show_over 
                               then HTMLView.td ~attrs:(Printf.sprintf "width=\"%dpx\"align=\"center\"" customizer#over_width) 
                                      (HTMLView.tag "nobr" (over.GT.fx ()))
                               else HTMLView.td (HTMLView.raw "&nbsp;");
                            HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" 
                              (match right with 
                              | Bad t -> HTMLView.raw (Printf.sprintf "<attr title=\"%s\"><font color=\"red\">&#8224;</font></attr>" t)
                              | Good r -> HTMLView.tag "nobr" (orig.GT.t#right () r)
                              );
                            if customizer#show_rule && rule <> ""
                               then HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\" style=\"font-size:80%\"" 
                                      (HTMLView.tag "nobr" (HTMLView.raw ("&nbsp;(<i>by</i>&nbsp;[" ^ rule ^ "])")))
                               else View.empty
                          ]
                        );
                        HTMLView.tr (
                          HTMLView.td ~attrs:(Printf.sprintf "width=\"%dpx\"align=\"center\" valign=\"center\"" customizer#over_width) (
                            HTMLView.tag ~attrs:(Printf.sprintf "style=\"display:inline-block;transform:scale(%d,1)\"" customizer#arrow_scale)
                              "span" (HTMLView.raw customizer#arrow)
                          )
                        );
                        HTMLView.tr (HTMLView.td (HTMLView.raw "&nbsp;"))
                      ]
                    )
                  in
                  if List.length subnodes = 0 
                  then HTMLView.li node
                  else HTMLView.li (
                         HTMLView.seq [
                           node;
                           HTMLView.ul (
                             HTMLView.seq (
                               List.map 
                                 (GT.transform(t) orig.GT.t#env orig.GT.t#left orig.GT.t#over orig.GT.t#right this ()) 
                                 subnodes
                             )
                           )
                         ]
                       )              

              end

            let html id customizer env left over right tree = 
              HTMLView.tag "div" ~attrs:"style=\"transform:scaleY(-1)\"" (
                HTMLView.ul ~attrs:(Printf.sprintf "id=\"%s\" class=\"mktree\"" id)
                  (GT.transform(t) env left over right (new custom_html customizer) () tree)
              )

            exception SomeBad of string

            let build ?(limit=(-1)) step env left over =
              let rec inner i env left over =
                if i != 0 then 
                  match step env left over with
    	          | Nothing (reason, rule) -> Node (env, left, over, Bad reason, [], rule)
                  | Just (right, rule) -> Node (env, left, over, Good right, [], rule)
                  | Subgoals (triples, fright, rule) ->
                      let rec process_subgoals subnodes subgoals subfun =
                        let subnodes' = List.map (fun (env', left', over') -> inner (i-1) env' left' over') subgoals in
			try
                          let rights = List.map (function 
                                                 | Node (_, _, _, Good r, _, _) -> r
				                 | Node (_, _, _, Bad t, _, _) -> raise (SomeBad t)
                                                ) subnodes'
                          in
                          match subfun rights with
	  	          | Just     (right  , _)         -> Node (env, left, over, Good right, subnodes@subnodes', rule)
                          | Nothing  (reason , _)         -> Node (env, left, over, Bad reason, subnodes@subnodes', rule)
                          | Subgoals (triples, fright, _) -> process_subgoals (subnodes@subnodes') triples fright
			with SomeBad t -> Node (env, left, over, Bad t, subnodes @ subnodes', rule)
		      in
		      process_subgoals [] triples fright
                else Node (env, left, over, Bad "step limit reached", [], "")
              in
              inner limit env left over

              module Make (C : sig 

                                 type env
                                 type left
                                 type over
                                 type right

                                 val step : env -> left -> over -> (env, left, over, right) case

                                 val env_html   : env   -> HTMLView.er
                                 val left_html  : left  -> HTMLView.er
                                 val over_html  : over  -> HTMLView.er
                                 val right_html : right -> HTMLView.er

                                 val customizer : html_customizer

                               end
                          ) =
                struct
                  let build ?(limit=(-1)) = build ~limit:limit C.step
                  let html id = html id C.customizer (GT.lift C.env_html) (GT.lift C.left_html) (GT.lift C.over_html) (GT.lift C.right_html)
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

                           val step      : env -> left -> over -> (env, left, over, right) BigStep.case
                           val side_step : env -> left -> over -> right -> (env * left * over) option

                           val env_html   : env   -> HTMLView.er
                           val left_html  : left  -> HTMLView.er
                           val over_html  : over  -> HTMLView.er
                           val right_html : right -> HTMLView.er

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
		      (match C.side_step env left over right with
		       | Some (env', left', over') -> inner (n-1) acc env' left' over'
		       | None -> acc
		      )
		  | _ -> acc
              in
              List.rev (inner limit [] env left over)

	    let html id seq =
	      HTMLView.table ~attrs:(Printf.sprintf "id=\"%s\"" id) (
                HTMLView.tr (
                  HTMLView.seq (
                    List.mapi 
                      (fun i t -> HTMLView.td (T.html (Printf.sprintf "__discard_%s_%d" id i) t))
		      seq
	          )
	        )
              )
              
          end

      end

  end
