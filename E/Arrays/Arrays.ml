open Ostap.Pretty
open GT

module Expr = 
  struct

    module Base = E.SimpleExpr    
	(Lexer.Make (struct let keywords = [] end))
	(struct 
	  let ops = [|
            `Lefta, ["||"];
            `Lefta, ["&&"];
            `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
            `Lefta, ["+" ; "-"];
            `Lefta, ["*" ; "/"; "%"];
	  |] 
	 end)

    @type 'a aexpr = [
      'a Base.expr 
    | `Indexed of 'a * 'a 
    | `Array   of 'a list
    ] with html, show, foldl

    let hparse h e s = 
      Base.hparse h 
	(fun p x ->            
	   ostap (
             base:(l:($)  "{" elems:!(Ostap.Util.list)[x] "}" r:($) {
                       h#register (`Array elems) (l :> Helpers.loc) (r :> Helpers.loc)
                     }
                   | !(e (p x)) 
                  ) 
             indices:(-"[" x -"]")* {
               List.fold_left (fun b i -> `Indexed (b, i)) base indices
             }
	  )
	) 
	s
    
    let parse e s = 
      let h = Helpers.highlighting () in
      ostap (x:hparse[h][e] -EOF {x, h}) s

    class ['a] html =
      object (this)
        inherit ['a] @aexpr[html]
        inherit ['a] Base.html
      end

    let rec html cb e =
      HTMLView.li ~attrs:(cb e) (transform(aexpr) (fun _ -> html cb) (new html) () e)

    let cast f = fun x -> f (x :> 'a aexpr)

    class ['a] abbrev_html cb pretty =
      let w = new Helpers.wrap cb pretty in
      object (this)
        inherit ['a, bool, HTMLView.er, bool, HTMLView.er] @aexpr
        inherit ['a] Base.abbrev_html (cast cb) (cast pretty)
        method c_Indexed top v base index = 
	  w#wrap v.GT.x 
	    (if top 
	     then
	       HTMLView.seq [
                 base.GT.fx false;
	         HTMLView.tag "tt" (HTMLView.raw "[");
	         index.GT.fx false;
	         HTMLView.tag "tt" (HTMLView.raw "]");
               ]
	     else w#bullet
            )
        method c_Array top v elems = 
	  w#wrap v.GT.x
            (if top && List.length elems <= 1
             then
               HTMLView.seq (
                 HTMLView.tag "tt" (HTMLView.raw "{") ::
                 List.map (fun e -> v.GT.t#a false e) elems @
                 [HTMLView.tag "tt" (HTMLView.raw "}")]
	       )
             else w#bullet
            )
      end

  end

let toplevel =  
  Toplevel.make 
    (Expr.Base.L.fromString (Expr.parse Expr.Base.nothing))
    (fun (p, h) ->         
        object inherit Toplevel.c
            method ast cb = View.toString (
                              HTMLView.ul ~attrs:"id=\"ast\" class=\"mktree\"" (
                                Expr.html (Helpers.interval cb h) p
                              )
                            )
            method vertical  = invalid_arg "" (* Expr.vertical p *)
            method run cb js = invalid_arg "" 
(*
              let module S = Expr.Semantics (Semantics.NSInt)(Expr.DInt)(struct let cb = (Helpers.interval cb h) end) in
              let state = ref State.empty in	      
              Toplevel.Wizard.Page ([
                  HTMLView.Wizard.flag  "strict";
                  HTMLView.Wizard.combo "type" [
                    HTMLView.raw "Big-Step"  , "bigstep"  , "selected=\"true\""; 
                    HTMLView.raw "Small-Step", "smallstep", ""
                  ];
                  Toplevel.Wizard.div   "state"
               ], 
               [
                (fun page conf -> 
                   let st = conf "state" in
                   match Expr.L.fromString (ostap (!(State.parse)[Expr.L.ident][Expr.L.literal] -EOF)) st with
		   | Checked.Ok st -> 
                      state := st; 
                      true
		   | Checked.Fail [msg] ->                     
                      js#error page "state" st msg;
                      false
                ), 
                Toplevel.Wizard.Exit 
                  (fun conf ->
                     js#results "root"                   
		       (View.toString (
                          if conf "type" = "bigstep"
                          then
                            if conf "strict" = "true" 
                            then S.BigStep.Strict.Tree.html "root" (S.BigStep.Strict.Tree.build () !state p)
                            else S.BigStep.NonStrict.Tree.html "root" (S.BigStep.NonStrict.Tree.build () !state p)
                          else S.SmallStep.Strict.html "root" (S.SmallStep.Strict.build () !state p)
		        )
                       )
                  )
               ]
              )
*)
          end
    )


