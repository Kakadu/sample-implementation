module type Sig =
  sig

    class t :
      string ->
      object ('a)
        method col        : int
        method coord      : Ostap.Msg.Coord.t
        method get        : string -> Re_str.regexp -> ('a, Ostap.Matcher.Token.t, Ostap.Reason.t) Ostap.Types.result
        method getEOF     : ('a, Ostap.Matcher.Token.t, Ostap.Reason.t) Ostap.Types.result
        method getIDENT   : ('a, Ostap.Matcher.Token.t, Ostap.Reason.t) Ostap.Types.result
        method getLITERAL : ('a, Ostap.Matcher.Token.t, Ostap.Reason.t) Ostap.Types.result
        method line       : int
        method loc        : Ostap.Msg.Locator.t
        method look       : string -> ('a, Ostap.Matcher.Token.t, Ostap.Reason.t) Ostap.Types.result
        method pos        : int
        method prefix     : int -> string
        method regexp     : string -> string -> ('a, Ostap.Matcher.Token.t, Ostap.Reason.t) Ostap.Types.result
        method skip       : int -> Ostap.Msg.Coord.t -> [ `Failed of Ostap.Msg.t | `Skipped of int * Ostap.Msg.Coord.t ]
      end

    val ident :
      (< getIDENT : ('a, Ostap.Matcher.Token.t, 'b)
                    Ostap.Types.result;
         .. >
       as 'a) ->
      ('a, string, 'b) Ostap.Types.result

    val literal :
      (< getLITERAL : ('a, Ostap.Matcher.Token.t, 'b)
                      Ostap.Types.result;
         .. >
       as 'a) ->
      ('a, int, 'b) Ostap.Types.result

    val fromString :
      (t ->
       ('a, 'b,
        < retrieve : [> `First of int ] ->
                     [> `Desc ] ->
                     (Ostap.Msg.Locator.t *
                      [< `Comment of string * 'c | `Msg of Ostap.Msg.t ]
                      list)
                     list;
          .. >)
       Ostap.Types.result) ->
      string -> ('b, Ostap.Msg.t) Checked.t

  end

module Make (K : sig val keywords : string list end) =
  struct

    let r = Ostap.Matcher.Token.repr

    let is_keyword =
      let module S = Set.Make (String) in
      let s = List.fold_left (fun s k -> S.add k s) S.empty K.keywords in
      (fun i -> S.mem i s)

    open Ostap
    ostap (
      ident  : x:IDENT =>{not (is_keyword (r x))}=> {r x};
      literal: x:LITERAL {int_of_string (r x)}
    )

    class t s =
      let skip = Ostap.Matcher.Skip.create [
                   Ostap.Matcher.Skip.whitespaces " \n\t\r";
                   Ostap.Matcher.Skip.nestedComment "(*" "*)";
                   Ostap.Matcher.Skip.lineComment "--"
                 ]
      in

      let ident   = Re_str.regexp "[a-zA-Z_]\([a-zA-Z_0-9]\)*\\b" in
      let literal = Re_str.regexp "-?[0-9]+" in
      object (self)
        inherit Ostap.Matcher.t s
        method skip p coord = skip s p coord
        method getIDENT     = self#get "identifier" ident
        method getLITERAL   = self#get "literal"    literal
      end

    exception Error of Ostap.Msg.t

    let fromString p s =
      try
        Ostap.Combinators.unwrap (p (new t s)) (fun x -> Checked.Ok x)
          (fun (Some err) ->
             let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
             let m =  match m with `Msg m -> m | `Comment (s, _) -> Ostap.Msg.make s [||] loc in
             Checked.Fail [m]
          )
      with Error m -> Checked.Fail [m]

  end
