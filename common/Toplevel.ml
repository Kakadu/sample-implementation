open Checked

class c =
  object
    method ast   (_:string)  = ""
    method vertical          = ""
    method code              = ""
    method run               = ([] : HTMLView.Wizard.t)
    method compile           = ""
  end

let make parse body source = parse source -?-> body
