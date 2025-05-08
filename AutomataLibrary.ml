include Language
include Sfa
module QcFa = QcFa

(* module Desymbolic = Desymbolic *)
(* module Rawdesym = Rawdesym *)
open Zutils
open SFA

let realize_sregex (checker : Nt.t sevent -> bool) (r : CharSet.t regex) =
  let fa = compile_regex_to_dfa r in
  let fa = minimize @@ dfa_realize checker fa in
  dfa_to_reg fa
