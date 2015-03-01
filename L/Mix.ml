open List
open Printf

module S = Set.Make (String)

let empty = object 
              method get x = `E (`Var x) 
              method known = S.empty
            end

let putS s x z = object
                   method get y = if y = x then z else s#get y
                   method known = 
                     match z with 
                     | `I _ -> S.add x s#known
                     | `E _ -> S.remove x s#known
                 end

let reify s = 
  S.fold (fun x acc -> `Seq (`Assign (x, match s#get x with `I i -> `Const i | _ -> invalid_arg "wow, bad..."), acc)) s#known `Skip

let rec expr s = function
| `Const i -> `I i
| `Var   x -> s#get x
| `Binop ((op, f), x, y) -> 
    match expr s x, expr s y with
    | `I x, `I y -> `I (f x y)
    | `I x, `E y -> `E (`Binop ((op, f), `Const x, y))
    | `E x, `I y -> `E (`Binop ((op, f), x, `Const y))
    | `E x, `E y -> `E (`Binop ((op, f), x, y))


let stmt s =
  let rec stmt s = function
  | `Assign (x, e)    -> (match expr s e with 
                          | (`I _) as e -> putS s x e, `Skip
                          | `E e        -> putS s x (`E (`Var x)), `Assign (x, e)
                         )

  | `While (c, x) as w -> stmt s (`If (c, `Seq (x, w), `Skip))

  | `If (c, x, y) as i -> 
                         (match expr s c with
                          | `I c -> stmt s (if c <> 0 then x else y)
                          | `E e -> empty, `Seq (reify s, i)
                         )

  | `Seq    (x, y)    -> let s' , x' = stmt s  x in 
                         let s'', y' = stmt s' y in
                         s'', `Seq (x', y')
 
  | `Read    x        -> printf "%s < " x; 
                         flush stdout;
                         let i = input_line stdin in
                         if i = "_" 
                         then putS s x (`E (`Var x))         , `Read x
                         else putS s x (`I (int_of_string i)), `Skip

  | `Write   e        -> s, `Write (match expr s e with `I i -> `Const i | `E e -> e)
  | `Skip             -> s, `Skip
  in
  snd (stmt empty s)