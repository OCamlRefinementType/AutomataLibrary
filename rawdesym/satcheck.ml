open Sugar
open Prop
open Zdatatype
open Common

let blist_to_prop (bl : bool list) int2lit =
  let blT, blF =
    map2 (List.map fst)
    @@ List.partition snd
    @@ List.mapi (fun i b -> (i, b)) bl
  in
  let blT, blF =
    map2
      (List.map (fun i -> lit_to_prop @@ IntMap.find "never" int2lit i))
      (blT, blF)
  in
  let blF = List.map (fun p -> Not p) blF in
  And (blT @ blF)

let safe_check_sat_bool prop =
  let () = _assert [%here] "never" @@ List.is_empty (fv_prop prop) in
  Prover.check_sat_bool prop

let check_sat_fact { global_vars; desym_map; event_tyctx; _ }
    { global_fact; local_fact } =
  let global_prop = blist_to_prop global_fact desym_map.global_int2lit in
  let () =
    _assert [%here] "never"
    @@ Prover.check_sat_bool (smart_exists global_vars global_prop)
  in
  let do_local_fact op bl_set =
    let local_vars = StrMap.find "never" event_tyctx op in
    let int2lit = StrMap.find "never" desym_map.local_int2lit op in
    let check_sat local_prop =
      let prop =
        smart_forall global_vars @@ smart_exists local_vars
        @@ smart_implies global_prop local_prop
      in
      safe_check_sat_bool prop
    in
    BlistSet.filter (fun bl -> check_sat @@ blist_to_prop bl int2lit) bl_set
  in
  let local_fact = StrMap.mapi do_local_fact local_fact in
  { global_fact; local_fact }
