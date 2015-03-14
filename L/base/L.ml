open GT

module Lexer = Lexer.Make (
    struct 
      let keywords = ["while"; "do"; "if"; "then"; "else"; "skip"; "read"; "write"] 
    end
  )

module Expr = E.SimpleExpr (
   struct

     let ops = [|
        `Lefta, ["||"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
      |] 

     let keywords = ["while"; "do"; "if"; "then"; "else"; "skip"; "read"; "write"] 

   end
  )

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

    class ['self, 'e] html =
      object
        inherit ['self, 'e] @t[html]
        inherit Helpers.cname as helped
        method cname name =
          match helped#cname name with
          | "assign" -> ":="
          | "seq"    -> ";"
          | name     -> name
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
      let parse s = Stmt.parse hp (Expr.hparse he) s in
      ostap (p:parse -EOF {p, hp#retrieve, he#retrieve}) s

    let rec html cbp cbe p = 
      HTMLView.li ~attrs:(cbp p)
        (transform(Stmt.t) (fun _ -> html cbp cbe) (fun _ -> Expr.html cbe) (new Stmt.html) () p)

    let rec vertical p = transform(Stmt.t) (fun _ -> vertical) (fun _ -> Expr.vertical) (new Stmt.vertical) () p

  end

let toplevel =  
  Toplevel.make
    (Lexer.fromString Program.parse)
    (fun (p, hp, he) ->
       object 
          method ast cb = View.toString (
                            HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                              Program.html (Helpers.interval cb hp) (Helpers.interval cb he) p
                            )
                          )
          method vertical = Program.vertical p
          method code     = invalid_arg ""
          method run      = invalid_arg ""
          method compile  = invalid_arg ""
        end
    )
