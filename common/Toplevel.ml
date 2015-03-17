open Checked

class virtual c =
  object
    method virtual ast      : string -> string
    method virtual vertical : string
    method virtual run      : string -> ((string ->string -> string -> HTMLView.Wizard.t) * (( string -> string) -> string * string))

    method code    = ""
    method compile = ""
  end

let make parse body source = parse source -?-> body
