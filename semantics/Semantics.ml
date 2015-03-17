@type 'a opt = Good of 'a | Bad of GT.string with html

module type Domain =
 sig

   type t
   val op   : string -> t -> t -> t opt
   val show : t -> string
   val html : t -> HTMLView.er

 end

module IntDomain (S : sig val strict : bool end) =
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
     | "*"  -> if S.strict then lift ( * ) else lift (fun x y -> if x = 0 then 0 else x * y)
     | "/"  -> (fun x y -> if y = 0 then Bad "division by zero" else Good (x / y))
     | "%"  -> (fun x y -> if y = 0 then Bad "division by zero" else Good (x mod y))
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
                                      HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (env.GT.fx ());
                                      HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTMLView.raw "&vdash;")
                                    ]
                               else View.empty;
                            HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (left.GT.fx ());
                            if customizer#show_over 
                               then HTMLView.td ~attrs:(Printf.sprintf "width=\"%dpx\"align=\"center\"" customizer#over_width) (over.GT.fx ())
                               else HTMLView.td (HTMLView.raw "&nbsp;");
                            HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" 
                              (match right with 
                              | Bad t -> HTMLView.raw (Printf.sprintf "<attr title=\"%s\"><font color=\"red\">&#8224;</font></attr>" t)
                              | Good r -> orig.GT.t#right () r
                              );
                            if customizer#show_rule && rule <> ""
                               then HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\" style=\"font-size:80%\"" 
                                      (HTMLView.raw ("&nbsp;(<i>by</i>&nbsp;[" ^ rule ^ "])"))
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

            let html customizer env left over right tree = 
              GT.transform(t) env left over right (new custom_html customizer) () tree

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
                  let html = html C.customizer (GT.lift C.env_html) (GT.lift C.left_html) (GT.lift C.over_html) (GT.lift C.right_html)

                end

          end    
      end

  end
