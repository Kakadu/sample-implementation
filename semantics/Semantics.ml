module Deterministic =
  struct 

    module BigStep =
      struct

        type ('env, 'left, 'over, 'right) case = 
          Nothing  of string * string
        | Just     of 'right * string
        | Subgoals of ('env * 'left * 'over) list * ('right list -> 'right option) * string

        module Tree =
          struct

            @type ('env, 'left, 'over, 'right) t = 
              Node of 'env * 'left * 'over * 'right GT.option * ('env, 'left, 'over, 'right) t GT.list * GT.string
            | Limit 
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
                               else View.empty;
                            HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" 
                              (match right with 
                              | None   -> HTMLView.raw "<font color=\"red\">&#8224;</font>"
                              | Some r -> orig.GT.t#right () r
                              );
                            if customizer#show_rule
                               then HTMLView.td ~attrs:"rowspan=\"3\" align=\"center\" valign=\"center\"" (HTMLView.string ("[" ^ rule ^ "]"))
                               else View.empty
                          ]
                        );
                        HTMLView.tr (
                          HTMLView.td ~attrs:"align=\"center\" valign=\"center\"" (
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

            let build ?(limit=(-1)) step env left over =
              let rec inner i env left over =
                if i != 0 then 
                  match step env left over with
    	          | Nothing (reason, rule) -> Node (env, left, over, None, [], rule)
                  | Just (right, rule) -> Node (env, left, over, Some right, [], rule)
                  | Subgoals (triples, fright, rule) ->
                      let subnodes = List.map (fun (env', left', over') -> inner (i-1) env' left' over') triples in
                      let right    = 
                        try fright (List.map (function Node (_, _, _, Some r, _, _) -> r) subnodes)
                        with Match_failure _ -> None
                      in
                      Node (env, left, over, right, subnodes, rule)
                else Limit
              in
              inner limit env left over

          end    
      end

  end
