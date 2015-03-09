open Ostap.Pretty

let w p px x = if px < p then rboxed x else x 

let b l = hboxed  (listBySpaceBreak l)
let v l = hvboxed (listBySpaceBreak l)
let c l = cboxed  (vboxed (listByBreak l))

open GT

module Expr =
  struct

    module L = Lexer.Make (struct let keywords = [] end) 

    @type 'a t = [  
        `Var   of string 
      | `Const of int
      | `Binop of (int -> int -> int) * string * 'a * 'a
    ] with html, show, foldl

    let prio = 
      let a = [ 
        "&&", 4; 
        "==", 5; 
        "+" , 6;
        "/" , 7;
      ] 
      in
      function `Binop (_, s, _, _) -> List.assoc s a | _ -> 8

    class ['a] eval =
      object (this)
        inherit ['a, int State.t, int, int State.t, int] @t
        method c_Var   s _ x       = State.get s x
        method c_Const _ _ n       = n
        method c_Binop s _ f _ x y = f (x.fx s) (y.fx s)
      end

    class ['a] html' cb =
      object (this)
        inherit ['a] @t[html]
        method attribute (t : 'a t) = cb t
      end

    class ['a] vertical =
      object (this)
        inherit ['a] @t[show]
        method c_Var _ _ x         = Printf.sprintf "x\n%s\n" x
        method c_Binop _ _ _ s x y = Printf.sprintf "*\n%s\n%s%s" s (x.GT.fx ()) (y.GT.fx ())
        method c_Const _ _ i       = Printf.sprintf "c\n%d\n" i
      end
    
    let rec html cb e = 
      HTMLView.li ~attrs:(cb e)
        (transform(t) (fun _ -> html cb) (new html' cb) () e)

    let rec vertical e = transform(t) (fun _ -> vertical) (new vertical) () e

    let parse s = 
      let h = Helpers.highlighting () in
      let primary p = ostap (
          l:($) x:!(L.ident)   r:($) {h#register (`Var x) l r}
        | l:($) i:!(L.literal) r:($) {h#register (`Const i) l r}
        | l:($) "(" x:p ")"    r:($) {h#register x l r}
      ) 
      in
      let rec parse s =  
        let l = List.map 
          (fun (s, t) -> 
             ostap(- $(s)), 
             (fun x y -> 
                let (l, _), (_, r) = h#retrieve x, h#retrieve y in
                h#reassign (`Binop (t, s, x, y)) l r
             )
          ) 
        in
        let ior  x y = abs x + abs y in
        let iand x y = abs (x * y) in
        let b f = fun x y -> if f x y then 1 else 0 in
        Ostap.Util.expr (Helpers.loc h#register) [|
          `Lefta, l ["&&", iand];
          `Nona , l ["==", b(=)];
          `Lefta, l ["+" , ( +  )];
          `Lefta, l ["/" , (/ )];
        |]
        (primary parse)
        s
      in
      ostap (t:parse EOF {t, h#retrieve}) s

  end

let toplevel source =  
  match Expr.L.fromString Expr.parse source with
  | Checked.Ok (p, h) -> 
      Checked.Ok (
        let interval cb t = 
          if cb = "" 
          then ""
          else 
            let ((x, y), (z, t)) = h t in
            Printf.sprintf "onclick=\"%s ('%d', '%d', '%d', '%d')\"" cb x y z t 
        in
        object 
          method ast cb =             
            HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" 
              (*HTMLView.li ~attrs:(interval cb p*) 
                 (Expr.html (interval cb) p)
             (* *)
          method print    = View.string (Expr.vertical p)
          method code     = invalid_arg ""
          method run      = invalid_arg ""
          method compile  = invalid_arg ""
        end
      )
  | Checked.Fail m -> Checked.Fail m
