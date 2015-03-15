open Checked

class c =
  object
    method ast   (_:string)  = ""
    method vertical          = ""
    method code              = ""
    method run   (_:string)  = (([] : HTMLView.Wizard.t), (fun (o: string -> string) -> "", ""))
    method compile           = ""
  end

let make parse body source = parse source -?-> body
