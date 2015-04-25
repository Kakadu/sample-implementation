open GT

module Lexer = Lexer.Make (
    struct 
      let keywords = ["while"; "do"; "if"; "then"; "else"; "skip"; "read"; "write"] 
    end
  )

module Expr = E.SimpleExpr 
  (Lexer)
  (struct
     let ops = [|
        `Lefta, ["||"];
        `Lefta, ["&&"];
        `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
        `Lefta, ["+" ; "-"];
        `Lefta, ["*" ; "/"; "%"];
      |] 
   end)

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
    ] with html, show, map

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

    class ['self, 'e] html' =
      object inherit ['self, 'e] @t[html]
        method c_Skip   _ _         = HTMLView.raw "skip"
        method c_Assign _ _ x e     = HTMLView.seq [HTMLView.raw x; HTMLView.raw " := "; e.GT.fx ()]
        method c_Write  _ _ e       = HTMLView.seq [HTMLView.raw "write ("; e.GT.fx (); HTMLView.raw ")"]
        method c_Read   _ _ x       = HTMLView.seq [HTMLView.raw "read ("; HTMLView.raw x; HTMLView.raw ")"]
        method c_Seq    _ _ s1 s2   = HTMLView.seq [s1.GT.fx (); HTMLView.raw " ; "; s2.GT.fx ()]
        method c_While  _ _ e s     = HTMLView.seq [HTMLView.raw "while "; e.GT.fx (); HTMLView.raw " do "; s.GT.fx ()]
        method c_If     _ _ e s1 s2 = HTMLView.seq [HTMLView.raw "if "; 
                                                    e.GT.fx (); 
                                                    HTMLView.raw " then "; 
                                                    s1.GT.fx (); 
                                                    HTMLView.raw " else "; 
                                                    s2.GT.fx ()
                                      ]
      end

    let parse (h : Helpers.h) expr s = 
      let ostap (
        ident    : !(Lexer.ident);
        key[name]: @(name ^ "\\b" : name);
        parse: 
          l:($) x:ident ":=" e:expr                                      r:($) {h#register (`Assign (x, e)) (l :> Helpers.loc) (r :> Helpers.loc)}
        | l:($) key["skip"]                                              r:($) {h#register (`Skip) (l :> Helpers.loc) (r :> Helpers.loc)}
        | l:($) key["read" ] "(" x:ident ")"                             r:($) {h#register (`Read x) (l :> Helpers.loc) (r :> Helpers.loc)}
        | l:($) key["write"] "(" e:expr ")"                              r:($) {h#register (`Write e) (l :> Helpers.loc) (r :> Helpers.loc)}
        | l:($) key["if"] c:expr key["then"] x:parse key["else"] y:parse r:($) {h#register (`If (c, x, y)) (l :> Helpers.loc) (r :> Helpers.loc)}
        | l:($) key["while"] c:expr key["do"] s:parse                    r:($) {h#register (`While (c, s)) (l :> Helpers.loc) (r :> Helpers.loc)}
        | -"{" seqs -"}";
        seqs: l:($) s:parse ss:(-";" seqs)? r:($) {match ss with None -> s | Some ss -> h#register (`Seq (s, ss)) (l :> Helpers.loc) (r :> Helpers.loc)}
      )
      in
      parse s

    module Semantics (D : Semantics.Domain)(B : sig val boolean : D.t -> [`True | `False | `NonBoolean] end) =
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
                      S.Subgoals ([e, conf, s1.GT.x], (fun [s1'] -> S.Subgoals ([e, s1', s2.GT.x], (fun [s2'] -> S.Just (s2', "")), "")), "Seq")

                    method c_Assign ((_, (s, i, o), _) as inh) _ x e = 
                      expr e inh (fun d -> S.Just ((State.modify s x d, i, o), "Assn")) 

                    method c_Read (_, (s, i, o), _) _ x =
                      match i with
		      | []    -> S.Nothing ("empty input", "")
                      | y::i' -> S.Just ((State.modify s x y, i', o), "Read")

                    method c_Write ((_, (s, i, o), _) as inh) _ e =
                      expr e inh (fun d -> S.Just ((s, i, o@[d]), "Write")) 

                    method c_If ((env, conf, _) as inh) _ e s1 s2 =
                      expr e inh 
                        (fun d -> 
                           match B.boolean d with
		   	   | `True  -> S.Subgoals ([env, conf, s1.GT.x], (fun [s1'] -> S.Just (s1', "")), "If-True")
			   | `False -> S.Subgoals ([env, conf, s2.GT.x], (fun [s2'] -> S.Just (s2', "")), "If-False")
			   |  _     -> S.Nothing  ("not a boolean value", "")
                         )

                    method c_While ((env, conf, _) as inh) w e s =
                      expr e inh 
                        (fun d ->
                           match B.boolean d with
			   | `True  -> S.Subgoals (
                                         [env, conf, s.GT.x], 
                                         (fun [s'] -> S.Subgoals ([env, s', w.GT.x], (fun [s''] -> S.Just (s'', "")), "")), 
                                         "While-True"
                                       )
                           | `False -> S.Just    (conf, "While-False")
                           |  _     -> S.Nothing ("not a boolean value", "")
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
                    let right_html   = conf_html   
                    let over_html  s = 
		      let wrap node html =
			HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" %s" (C.cb node)) html
		      in
		      wrap s
			(GT.transform(t) 
			   (fun _ stmt -> wrap stmt (HTMLView.raw "&#8226;"))
			   (GT.lift E.html)
			   (new html') 
			   ()
			   s
			)
  
                    let step = step E.eval

                    let customizer =
                      object 
                        inherit S.Tree.html_customizer
                        method show_env   = false
                        method over_width = 100
                      end
                  end

              end

            module CPS =
              struct

		@type ('self, 'e) k = [`L | ('self, 'e) t] with html, show

                class ['self, 'e] html =
                  object 
                    inherit ['self, 'e] @k[html]
                    inherit ['self, 'e] html'
                    method c_L _ _ = HTMLView.raw "&Lambda;"
                  end                       

                type conf = Standard.conf

		let (++) x y = 
		  match x, y with
		  | `L, _  -> y
		  | _ , `L -> x
		  | _      -> `Seq (x, y)

                let conf_html = Standard.conf_html

                class ['self, 'e] step =
                  let expr e inh f =
                    match e.GT.fx inh with
		    | Semantics.Good (_, _, d) -> f d
                    | Semantics.Bad reason -> S.Nothing (reason, "")
                  in
		  let return [conf'] = S.Just (conf', "") in
                  object 
                    inherit [('self, 'e) k, conf, ('self, 'e) k, conf, 'self, 'e] c
                    inherit ['self, ('self, 'e) k * conf * ('self, 'e) k, (('self, 'e) k, conf, ('self, 'e) k, conf) S.case, 
                             'e   , ('self, 'e) k * conf * ('self, 'e) k, (('self, 'e) k * conf * D.t) Semantics.opt,
                                    ('self, 'e) k * conf * ('self, 'e) k, (('self, 'e) k, conf, ('self, 'e) k, conf) S.case
                            ] @k

		    method c_L (k, conf, _) s = 
                      match k with 
		      | `L -> S.Just (conf, "&Lambda;-&Lambda;-CPS") 
		      |  _ -> S.Subgoals ([`L, conf, k], return, "&Lambda;-CPS")

                    method c_Skip (k, conf, _) _ = S.Subgoals ([`L, conf, k], return , "Skip-CPS")

                    method c_Assign ((k, (s, i, o), _) as inh) _ x e = 
                      expr e inh (fun d -> S.Subgoals ([`L, (State.modify s x d, i, o), k], return, "Assn-CPS"))

                    method c_Read (k, (s, i, o), _) _ x =
                      match i with
		      | []    -> S.Nothing ("empty input", "")
                      | y::i' -> S.Subgoals ([`L, (State.modify s x y, i', o), k], return, "Read-CPS")

                    method c_Write ((k, (s, i, o), _) as inh) _ e =
                      expr e inh (fun d -> S.Subgoals ([`L, (s, i, o@[d]), k], return, "Write-CPS")) 

                    method c_Seq (k, conf, _) _ s1 s2 = S.Subgoals ([s2.GT.x ++ k, conf, s1.GT.x], return, "Seq-CPS")

                    method c_If ((k, conf, _) as inh) _ e s1 s2 =
                      expr e inh 
                        (fun d -> 
                           match B.boolean d with
		   	   | `True  -> S.Subgoals ([k, conf, s1.GT.x], return, "If-True-CPS")
			   | `False -> S.Subgoals ([k, conf, s2.GT.x], return, "If-False-CPS")
			   |  _     -> S.Nothing  ("not a boolean value", "")
                         )

                    method c_While ((k, conf, _) as inh) w e s =
                      expr e inh 
                        (fun d ->
                           match B.boolean d with
			   | `True  -> S.Subgoals ([`While (e.GT.x, s.GT.x) ++ k, conf, s.GT.x], return, "While-True-CPS" )
                           | `False -> S.Subgoals ([`L, conf, k], return, "While-False-CPS")
                           |  _     -> S.Nothing  ("not a boolean value", "")
                        )

		  end

                let rec step fe env conf stmt = 
                  GT.transform(k) 
                    (fun (env, conf, _) stmt -> step fe env conf stmt) 
                    fe 
                    (new step) 
                    (env, conf, stmt) 
                    stmt

                module Instantiate 
                    (E : sig 
                           type expr 
                           val eval : (('a, expr) k as 'a) * conf * (('a, expr) k as 'a) -> expr -> 
                                      ((('a, expr) k as 'a) * conf * D.t) Semantics.opt 
                           val html : expr -> HTMLView.er
                         end
                     )
                    (C : sig val cb : ('a, E.expr) k as 'a -> string end) =
                  struct
                    type env   = ('a, E.expr) k as 'a
                    type left  = conf
                    type over  = ('a, E.expr) k as 'a
                    type right = conf

                    let env_html s =
   	              let wrap node html =
			HTMLView.tag "attr" 
                          ~attrs:(Printf.sprintf "style=\"cursor:pointer\" %s"   
                          (C.cb node)) 
                          html
		      in
		      wrap s
			(GT.transform(k) 
			   (fun _ stmt -> wrap stmt (HTMLView.raw "&#8226;"))
			   (GT.lift E.html)
			   (new html) 
			   ()
			   s
			)
  
                    let left_html  = conf_html
                    let over_html  = env_html
                    let right_html = conf_html

                    let step = step E.eval

                    let customizer =
                      object 
                        inherit S.Tree.html_customizer
                        method show_env   = true
                        method over_width = 100
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
      let parse s = Stmt.parse hp (Expr.hparse he Expr.nothing) s in
      ostap (p:parse -EOF {p, hp, he}) s

    let rec html cbp cbe p = 
      HTMLView.li ~attrs:(cbp p)
        (transform(Stmt.t) 
           (fun _ -> html cbp cbe) 
           (fun _ -> Expr.html cbe) 
           (new Stmt.html) 
           () 
           p
        )

    let rec vertical p = 
      transform(Stmt.t) 
        (fun _ -> vertical) 
        (fun _ -> Expr.vertical) 
        (new Stmt.vertical) 
        () 
        p

    module Semantics = Stmt.Semantics 
      (Semantics.Int)
      (struct 
         let boolean = function 1 -> `True | 0 -> `False | _ -> `NonBoolean 
       end
      ) 

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
         method run hcb (js : Toplevel.js) = 
           let module E = 
             struct 
               type expr  = 'a Expr.expr as 'a 

               let eval (k, ((s, _, _) as c), _) e = 
                 match Expr.eval_strict s e with 
                 | Semantics.Good d      -> Semantics.Good (k, c, d)
                 | Semantics.Bad  reason -> Semantics.Bad reason

               let html e = 
                 HTMLView.tag "attr" ~attrs:(Printf.sprintf "style=\"cursor:pointer\" %s" (Helpers.interval hcb he e))
                   (match e with 
	            | `Const i -> HTMLView.raw (string_of_int i)
                    | `Var   x -> HTMLView.raw x
		    | _        -> HTMLView.raw "&#8226;"
                   )
              end
	   in
           let module S    = Program.Semantics.BigStep.Standard.Instantiate (E)(struct let cb = Helpers.interval hcb hp end) in
           let module CPS  = Program.Semantics.BigStep.CPS     .Instantiate (E)(struct let cb = Helpers.interval hcb hp end) in
           let module TS   = Semantics.Deterministic.BigStep.Tree.Make (S  ) in
           let module TCPS = Semantics.Deterministic.BigStep.Tree.Make (CPS) in
           let input = ref []   in
           let depth = ref (-1) in
           Toplevel.Wizard.Page (
             [                             
              HTMLView.Wizard.radio "Type" [HTMLView.raw "normal", "normal", "checked=\"true\""; HTMLView.raw "CPS", "CPS", ""]; 
              Toplevel.Wizard.div "Input stream";
              Toplevel.Wizard.div ~default:"-1" "Tree depth"
             ],
             [(fun page conf ->
                let stream' = conf "Input stream" in
                let depth'  = conf "Tree depth"   in
                match Lexer.fromString (ostap (!(Ostap.Util.list0)[Lexer.literal] -EOF)) stream',
                      Lexer.fromString (ostap (s:"-"? n:!(Lexer.literal) -EOF {match s with Some _ -> -(n) | _ -> n})) depth'
                with
                | Checked.Ok input'', Checked.Ok depth'' -> input := input''; depth := depth''; true
                | Checked.Fail [msg], _ -> js#error page "Input stream" stream' msg; false
                | _, Checked.Fail [msg] -> js#error page "Tree depth" depth' msg; false
              ),
              Toplevel.Wizard.Exit 
                (fun conf ->
		  js#results 
                    "root"
                     (View.toString (
                        if conf "Type" = "normal"
                        then TS.html "root" (TS.build ~limit:!depth () (State.empty, !input, []) p)
                        else
		          TCPS.html "root" (
		            TCPS.build 
                              ~limit:!depth 
                              `L 
                              (State.empty, !input, []) 
                              (p :> ('a, 'b Expr.expr as 'b) Program.Semantics.BigStep.CPS.k as 'a)
		          )
                     )
                     )
                )
	     ]
           )
         method vertical = Program.vertical p
       end
    )
