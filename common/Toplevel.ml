open Checked

class c =
  object
    method ast   (_:string)  = ""
    method vertical          = ""
    method code              = ""
    method run               = ""
    method compile           = ""
  end

let make parse body source = parse source -?-> body
