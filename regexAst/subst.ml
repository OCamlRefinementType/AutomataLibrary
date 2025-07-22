open ParseTree
open Zutils
open Prop

let subst_sevent (_x : string) f { op; vs; phi } =
  let phi =
    if List.exists (fun x -> String.equal x.x _x) vs then phi
    else subst_prop _x f phi
  in
  { op; vs; phi }

let subst_rich_regex (_x : string) f (regex : 't sevent rich_regex) :
    't sevent rich_regex =
  Mapf.map_rich_regex (subst_sevent _x f) regex

let subst_sevent_instance x y z = subst_f_to_instance subst_sevent x y z

let subst_rich_regex_instance y z sevent =
  subst_f_to_instance subst_rich_regex y z sevent

(* let subst_regex_instance y z sevent = subst_f_to_instance subst_regex y z sevent *)
