module Deterministic =
  struct 

    type ('env, 'left, 'over, 'right) case = 
      Nothing 
    | Just     of 'right 
    | Subgoals of ('env * 'left * 'over) list * ('right list -> 'right option)

    class ['env, 'left, 'over, 'right] step =
      object
        method make : 'env -> 'left -> 'over -> ('env, 'left, 'over, 'right) case = fun _ _ _ -> Nothing
      end

    module Tree =
      struct

        @type ('env, 'left, 'over, 'right) t = 
          Node of 'env * 'left * 'over * 'right GT.option * ('env, 'left, 'over, 'right) t GT.list 
        | Limit 
        with html

        let build ?(limit=(-1)) step env left over =
          let rec inner i env left over =
            if i < limit then 
              match step#make env left over with
	      | Nothing -> Node (env, left, over, None, [])
              | Just right -> Node (env, left, over, Some right, [])
              | Subgoals (triples, fright) ->
                  let subnodes = List.map (fun (env', left', over') -> inner (i+1) env' left' over') triples in
                  let right    = 
                    try fright (List.map (function Node (_, _, _, Some r, _) -> r) subnodes)
                    with Match_failure _ -> None
                  in
                  Node (env, left, over, right, subnodes)
            else Limit
          in
          inner 0 env left over

      end    

  end
