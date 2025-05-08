open Language
open Sfa
open Zutils
open SFA
open QCheck.Gen
open Prop

let tv = "v"#:Nt.int_ty

let mk_lt l1 l2 =
  (AAppOp
     ( "<"#:(Nt.construct_arr_tp ([ Nt.int_ty; Nt.int_ty ], Nt.bool_ty)),
       [ l1#:Nt.int_ty; l2#:Nt.int_ty ] ))#:Nt.bool_ty

let tv_lt n = Lit (mk_lt (AVar tv) (AC (I n)))
let tv_gt n = Lit (mk_lt (AC (I n)) (AVar tv))
let op_phi_to_se op phi = { op; vs = [ tv ]; phi }
let space_list = List.map (fun op -> op_phi_to_se op mk_true) [ "a"; "b" ]
let space = CharSet.of_list space_list

(* open Zdatatype *)

let int_space = [ 0; 1; 2; 3; 4; 5 ]
let int_domain = [ -1; 0; 1; 2; 3; 4; 5; 6 ]

let prop_gen =
  frequency
    [
      (1, pure mk_true);
      (1, pure mk_false);
      (2, map tv_lt (oneofl int_space));
      (2, map tv_gt (oneofl int_space));
      ( 1,
        map2
          (fun x y -> And [ tv_lt x; tv_gt y ])
          (oneofl int_space) (oneofl int_space) );
    ]

let se_gen =
  frequency
    [
      (1, map (op_phi_to_se "a") prop_gen); (1, map (op_phi_to_se "b") prop_gen);
    ]

let se_to_regex x = MultiChar (CharSet.singleton x)

let regex_ternimal_gen =
  frequency [ (1, pure Empty); (1, pure Eps); (10, map se_to_regex se_gen) ]

let regex_one_arg_gen g =
  frequency
    [ (1, map (fun x -> Star x) g); (1, map (fun x -> Comple (space, x)) g) ]

let regex_two_arg_gen g1 g2 =
  frequency
    [
      (1, map2 (fun r1 r2 -> Alt (r1, r2)) g1 g2);
      (1, map2 (fun r1 r2 -> Seq [ r1; r2 ]) g1 g2);
      (1, map2 (fun r1 r2 -> Inters (r1, r2)) g1 g2);
    ]

let regex_gen =
  sized_size (int_bound 4)
  @@ fix (fun self n ->
         match n with
         | 0 -> regex_ternimal_gen
         | _ ->
             frequency
               [
                 (1, regex_ternimal_gen);
                 (3, regex_one_arg_gen @@ self (n - 1));
                 (4, regex_two_arg_gen (self (n / 2)) (self (n / 2)));
               ])

(* let string_gen = *)
(*   list (map2 (fun op v -> (op, v)) (oneofl [ "a"; "b" ]) (oneofl int_domain)) *)

(* let string_gen_from_regex_random (r : CharSet.t regex) = *)
(*   map (fun l -> *)
(*       if is_match (fun a b -> C.compare a b == 0) r l then (true, l) *)
(*       else (false, l)) *)
(*   @@ sized_size (int_bound 10) *)
(*   @@ fix (fun self n -> *)
(*          match n with *)
(*          | 0 -> pure [] *)
(*          | _ -> map2 (fun hd tl -> hd :: tl) (oneofl space_list) (self (n - 1))) *)
