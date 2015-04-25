open Checked

type proxy = string -> string

module Wizard =
  struct

    type node = 
    | Page of (HTMLView.Wizard.page -> HTMLView.Wizard.page) list * ((HTMLView.Wizard.page -> proxy -> bool) * node) list
    | Exit of (proxy -> unit)

    let div ?(attrs="") = HTMLView.Wizard.div ~attrs:(Printf.sprintf "%s class=\"editablediv\"" attrs)

    let make id target navigate (Page (inputs, decisions)) as root =
      let w = HTMLView.Wizard.create id target navigate in
      let i =
        let i = ref 0 in
        (fun () -> let k = !i in incr i; k)
      in
      let rec inner nav index (inputs, decisions) =
        let page = w#page inputs in
        let decisions' = List.map (function 
	                           | (_, Page _) as d -> i  (), d
				   | (_, Exit _) as d -> index, d
                                  ) decisions in
        let nav' i obj = 
          if i = index 
          then 
            try 
              let next,( _, node) = List.find (fun (_, (test, _)) -> test page obj) decisions' in
              (match node with Exit f -> f obj | _ -> ());
              next
            with Not_found -> -1
          else nav i obj
	in
        List.fold_left 
          (fun nav (i, (_, node)) -> 
	     match node with
	     | Page (inp, dec)  -> inner nav i (inp, dec)
	     | Exit _ -> nav
          ) nav' decisions'
      in
      w, inner (fun i _ -> i) 0 (inputs, decisions)

  end
class type js =
  object
    method error   : HTMLView.Wizard.page -> string -> string -> Ostap.Msg.t -> unit
    method results : string -> string -> unit
  end

class virtual c =
  object
    method virtual ast      : string -> string
    method virtual vertical : string
    method virtual run      : string -> js -> Wizard.node
  end

let make parse body source = parse source -?-> body
