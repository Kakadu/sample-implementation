open GT

module Lexer = Lexer.Make (
    struct 
      let keywords = ["while"; "do"; "if"; "then"; "else"; "skip"; "read"; "write"] 
    end
  )

module Expr =
  struct

    @type primary = [`Var of string | `Const of int] with html, show, foldl

    let parse h s =
      let primary p = ostap (
         x:!(Lexer.ident)   {`Var x}
        |  i:!(Lexer.literal) {`Const i}
        |  -"(" p -")"  
        )
      in         
      E.Expr.parse h [|
        `Lefta, ["||", E.Expr.ior];
        `Lefta, ["&&", E.Expr.iand];
        `Nona , ["==", E.Expr.b(=); "!=", E.Expr.b(<>); "<=", E.Expr.b(<=); "<", E.Expr.b(<); ">=", E.Expr.b(>=); ">", E.Expr.b(>)];
        `Lefta, ["+" , ( + ); "-" , (-)];
        `Lefta, ["*" , ( * ); "/" , (/); "%" , (mod)];
      |] 
      primary s;;

    @type 'a expr = ['a E.Expr.t | primary] with html, show, foldl

    class ['a] html cb =
      object (this)
        inherit ['a] @expr[html]
      end

    class ['a] vertical =
      object (this)
        inherit ['a] @expr[show]
        inherit ['a] E.Expr.vertical
        method c_Var _ _ x = Printf.sprintf "x\n%s\n" x
        method c_Const _ _ i = Printf.sprintf "c\n%d\n" i
      end

    class ['a] eval =
      object (this)
        inherit ['a] E.Expr.eval
        inherit ['a, int State.t, int, int State.t, int] @expr
        method c_Var s _ x = State.get s x
        method c_Const _ _ i = i
      end

    let rec html cb e = 
      HTMLView.li ~attrs:(cb e)
        (transform(expr) (fun _ -> html cb) (new html cb) () e)
    let rec vertical e = transform(expr) (fun _ -> vertical) (new vertical) () e 
    let rec eval s e = transform(expr) eval (new eval) s e      

  end

module Stmt =
  struct

    @type ('self, 'e) t = [
        `Skip 
      | `Assign of string * 'e
      | `Read   of string
      | `Write  of 'e
      | `If     of 'e * 'self * 'self
      | `While  of 'e * 'self  
      | `Seq    of 'self * 'self 
    ] with html, show

    class ['self, 'e] vertical =
      object (this)
        inherit ['self, 'e] @t[show]
        method c_Skip   _ _       = "s"
        method c_Seq    _ _ x y   = Printf.sprintf ";\n%s%s" (x.fx ()) (y.fx ())
        method c_Assign _ _ x e   = Printf.sprintf "=\n%s\n%s" x (e.fx ())
        method c_While  _ _ c s   = Printf.sprintf "l\n%s%s" (c.fx ()) (s.fx ())
        method c_If     _ _ c x y = Printf.sprintf "i\n%s%s%s" (c.fx ()) (x.fx ()) (y.fx ())
        method c_Read   _ _ x     = Printf.sprintf "r\n%s\n" x
        method c_Write  _ _ e     = Printf.sprintf "w\n%s" (e.fx ())
      end

    let parse h expr s = 
      let ostap (
        ident    : !(Lexer.ident);
        key[name]: @(name ^ "\\b" : name);
        parse: 
          l:($) x:ident ":=" e:expr                                      r:($) {h#register (`Assign (x, e)) l r}
        | l:($) key["skip"]                                              r:($) {h#register (`Skip) l r}
        | l:($) key["read" ] "(" x:ident ")"                             r:($) {h#register (`Read x) l r}
        | l:($) key["write"] "(" e:expr ")"                              r:($) {h#register (`Write e) l r}
        | l:($) key["if"] c:expr key["then"] x:parse key["else"] y:parse r:($) {h#register (`If (c, x, y)) l r}
        | l:($) key["while"] c:expr key["do"] s:parse                    r:($) {h#register (`While (c, s)) l r}
        | l:($) "{" s:parse ";" ss:seqs[s] "}"                           r:($) {h#register ss l r};
        seqs[acc]: l:($) s:parse t:(-";" seqs[let (p1, _), (_, p2) = h#retrieve acc, h#retrieve s in h#reassign (`Seq (acc, s)) p1 p2])? r:($) {
          h#register (match t with Some t -> t | None -> `Seq (acc, s)) l r
        }
      )
      in
      parse s

  end

module Program =
  struct
    
    let parse s = 
      let hp = Helpers.highlighting () in
      let he = Helpers.highlighting () in
      let parse s = Stmt.parse hp (Expr.parse he) s in
      ostap (p:parse -EOF {p, hp#retrieve, he#retrieve}) s

    let rec html cbp cbe p = 
      HTMLView.li ~attrs:(cbp p)
        (transform(Stmt.t) (fun _ -> html cbp cbe) (fun _ -> Expr.html cbe) (new @Stmt.t[html]) () p)

    let rec vertical p = transform(Stmt.t) (fun _ -> vertical) (fun _ -> Expr.vertical) (new Stmt.vertical) () p

  end

let toplevel source =  
  match Lexer.fromString Program.parse source with
  | Checked.Ok (p, hp, he) -> 
      Checked.Ok (
        let interval cb h t = 
          if cb = "" 
          then ""
          else 
            let ((x, y), (z, t)) = h t in
            Printf.sprintf "onclick=\"%s ('%d', '%d', '%d', '%d')\"" cb x y z t 
        in
        object 
          method ast cb =             
            HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (Program.html (interval cb hp) (interval cb he) p)
          method print   = View.string (Program.vertical p)
          method code    = invalid_arg ""
          method run     = invalid_arg ""
          method compile = invalid_arg ""
        end
      )
  | Checked.Fail m -> Checked.Fail m
