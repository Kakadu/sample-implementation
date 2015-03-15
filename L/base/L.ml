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

    class ['self, 'e] html'  =
      let wrap node html = html in
      object inherit ['self, 'e] @t[html]
        method c_Skip   _ node       = wrap node (HTMLView.tag "tt" (HTMLView.raw "skip"))
        method c_Assign _ node x e   = wrap node (HTMLView.tag "tt" (HTMLView.seq [HTMLView.raw x; HTMLView.raw " := "; e.GT.fx ()]))
        method c_Write  _ node e     = wrap node (HTMLView.tag "tt" (HTMLView.seq [HTMLView.raw "write ("; e.GT.fx (); HTMLView.raw ")"]))
        method c_Read   _ node x     = wrap node (HTMLView.tag "tt" (HTMLView.seq [HTMLView.raw "read ("; HTMLView.raw x; HTMLView.raw ")"]))
        method c_Seq    _ node s1 s2 = wrap node (HTMLView.tag "tt" (HTMLView.seq [s1.GT.fx (); HTMLView.raw " ; "; s2.GT.fx ()]))
        method c_While  _ node e s   = wrap node (HTMLView.tag "tt" (HTMLView.seq [HTMLView.raw "while "; e.GT.fx (); HTMLView.raw " do "; s.GT.fx ()]))
        method c_If     _ node e s1 s2 = wrap node (HTMLView.tag "tt" (HTMLView.seq [HTMLView.raw "if "; e.GT.fx (); HTMLView.raw " then "; s1.GT.fx (); HTMLView.raw " else "; s2.GT.fx ()]))

      end

    let rec abbreviate_html cb fe stmt = 
      let wrap node html =
        HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" %s" (cb node)) html
      in
      GT.transform(t) 
         (fun _ stmt -> wrap stmt (HTMLView.raw "S"))
         (GT.lift fe)
         (new html') 
         ()
         stmt

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

    module Semantics (D : Semantics.Domain)(B : sig val boolean : D.t -> [`True | `False | `NonBoolean] end) =
      struct

        module Deterministic =
          struct

            module BigStep =
              struct

                module S = Semantics.Deterministic.BigStep

                class virtual ['env, 'left, 'over, 'right, 'self, 'e] c =
                  object 
                    inherit ['self, 'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case, 
                             'e,    'env * 'left * 'over, ('env * 'right * D.t) Semantics.opt,
                                    'env * 'left * 'over, ('env, 'left, 'over, 'right) S.case
                            ] @t
                  end

                module Standard =
                  struct

                    type conf = D.t State.t * D.t GT.list * D.t GT.list

                    let conf_html (s, i, o) = 
                      let show l = GT.transform(GT.list) (GT.lift D.show) (new @GT.list[show]) () l in
                      HTMLView.seq [
                        HTMLView.raw "(";
                        State.html D.show s;
                        HTMLView.raw ",";
                        HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" title=\"[%s]\"" (show i)) (HTMLView.raw "i");
                        HTMLView.raw ",";
                        HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" title=\"[%s]\"" (show o)) (HTMLView.raw "o");
                        HTMLView.raw ")"
		      ]

   		    class ['self, 'e] step =
                      let expr e inh f =
                        match e.GT.fx inh with
			| Semantics.Good (_, _, d) -> f d
                        | Semantics.Bad reason -> S.Nothing (reason, "")
                      in
                      object 
                        inherit [unit, conf, ('self, 'e) t, conf, 'self, 'e] c
                        method c_Skip (_, conf, _) _ = S.Just (conf, "Skip")

                        method c_Seq  (e, conf, _) _ s1 s2 = 
                          S.Subgoals ([e, conf, s1.GT.x; e, conf, s2.GT.x], (fun [_; s2'] -> Semantics.Good s2') , "Seq")

                        method c_Assign ((_, (s, i, o), _) as inh) _ x e = 
                          expr e inh (fun d -> S.Just ((State.modify s x d, i, o), "Assn")) 

                        method c_Read (_, (s, i, o), _) _ x =
                          match i with
			  | []    -> S.Nothing ("empty input", "")
                          | y::i' -> S.Just ((s, i', o), "Read")

                        method c_Write ((_, (s, i, o), _) as inh) _ e =
                          expr e inh (fun d -> S.Just ((s, i, o@[d]), "Write")) 

                        method c_If ((env, conf, _) as inh) _ e s1 s2 =
                          expr e inh (fun d -> 
                            match B.boolean d with
			    | `True  -> S.Subgoals ([env, conf, s1.GT.x], (fun [s1'] -> Semantics.Good s1'), "If-True")
			    | `False -> S.Subgoals ([env, conf, s2.GT.x], (fun [s2'] -> Semantics.Good s2'), "If-False")
			    |  _     -> S.Nothing  ("not a boolean value", "")
                          )

                        method c_While ((env, conf, _) as inh) _ e s =
                          expr e inh (fun d ->
                            match B.boolean d with
			    | `True  -> S.Just (conf, "While-False")
                            | `False -> S.Just (conf, "While-False")
                            |  _     -> S.Nothing  ("not a boolean value", "")
                          )

		      end

                    let rec step fe env conf stmt = 
                      GT.transform(t) (fun (env, conf, _) stmt -> step fe env conf stmt) fe (new step) (env, conf, stmt) stmt

                    module Instantiate 
                        (E : sig 
                               type expr 
                               val eval : unit * conf * (('a, expr) t as 'a) -> expr -> (unit * conf * D.t) Semantics.opt 
                               val html : expr -> HTMLView.er
                             end
                         )
                        (C : sig val cb : ('a, E.expr) t as 'a -> string end) =
                      struct

                        type env   = unit
                        type left  = conf
                        type over  = ('a, E.expr) t as 'a
                        type right = conf

                        let env_html     = HTMLView.unit
                        let left_html    = conf_html
                        let over_html  s = abbreviate_html C.cb E.html s
                        let right_html   = conf_html

                        let step = step E.eval

                        let customizer =
                          object 
                            inherit S.Tree.html_customizer
                            method show_env   = false
                            method over_width = 70
                          end
                      end

                  end

              end

          end

      end

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

    module Semantics = Stmt.Semantics (Semantics.StrictInt)(struct let boolean = function 1 -> `True | 0 -> `False | _ -> `NonBoolean end) 

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
         method run (hcb : string) = 
              let module S = Program.Semantics.Deterministic.BigStep.Standard.Instantiate 
                (struct 
                   type expr  = 'a Expr.expr as 'a 

                   let eval ((), ((s, _, _) as c), _) e = 
                      match Expr.eval_strict s e with 
		      | Semantics.Good d      -> Semantics.Good ((), c, d)
                      | Semantics.Bad  reason -> Semantics.Bad reason

                   let html e = HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" %s" (Helpers.interval hcb he e))
                                  (HTMLView.raw "e")
                 end)
                (struct let cb = Helpers.interval hcb hp  end) 
              in
              let module T = Semantics.Deterministic.BigStep.Tree.Make (S) in
              let wizard =
                let p0 = [                  
                  HTMLView.Wizard.Page.Item.make "input" (HTMLView.Wizard.Page.Item.String "");
                ] 
                in
                [p0]
              in
              (wizard,
               fun c ->
                 let input = c "input" in
                 match Lexer.fromString (ostap (!(Ostap.Util.list0)[Lexer.literal] -EOF)) input with
                 | Checked.Ok input ->
                     "root",
                     View.toString (
                       HTMLView.tag "div" ~attrs:"style=\"transform:scaleY(-1)\"" (
                         HTMLView.ul ~attrs:"id=\"root\" class=\"mktree\""
                           (T.html (T.build () (State.empty, input, []) p)
                     )))
		 | Checked.Fail [msg] -> "", Js_frontend.highlighted_msg input msg
              )

         method vertical = Program.vertical p
         method code     = invalid_arg ""
         method compile  = invalid_arg ""
       end
    )
