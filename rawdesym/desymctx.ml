open Sugar
open Prop
open Zdatatype
open Fa
open Common
open SFA
open Desymeval

let mk_fvec_from_ftab ftab =
  let len = List.length ftab in
  let l = List.init (pow 2 len) (fun i -> IntBinary.int_to_bin (len, i)) in
  BlistSet.of_list l

let init_fact prop { global_ftab; local_ftab; desym_map; _ } =
  let global_fact = mk_fvec_from_ftab global_ftab in
  let global_fact =
    BlistSet.filter
      (fun bl ->
        let m = align_map (desym_map.global_lit2int, Array.of_list bl) in
        desym_eval_prop m prop)
      global_fact
  in
  let global_fact =
    if BlistSet.cardinal global_fact == 1 then BlistSet.choose global_fact
    else
      _die_with [%here]
        "the global prop contains multipel global feature vectors"
  in
  let local_fact = StrMap.map mk_fvec_from_ftab local_ftab in
  { global_fact; local_fact }

let mk_desym_map (global_ftab, local_ftab) =
  let mk_map =
    List.fold_lefti
      (fun (lit2int, int2lit) i lit ->
        (LitMap.add lit i lit2int, IntMap.add i lit int2lit))
      (LitMap.empty, IntMap.empty)
  in
  let global_lit2int, global_int2lit = mk_map global_ftab in
  let local_lit2int = StrMap.map (fun l -> fst @@ mk_map l) local_ftab in
  let local_int2lit = StrMap.map (fun l -> snd @@ mk_map l) local_ftab in
  { global_lit2int; global_int2lit; local_lit2int; local_int2lit }

let get_in_regex (get_in_chars, union, empty) =
  let rec aux r =
    match r with
    | Empty | Eps -> empty
    | MultiChar cs -> get_in_chars cs
    | Alt (r1, r2) | Inters (r1, r2) -> union (aux r1) (aux r2)
    | Seq rs -> List.fold_right (fun r -> union (aux r)) rs empty
    | Comple (cs, r) ->
        let fv1 = get_in_chars cs in
        let fv2 = aux r in
        union fv1 fv2
    | Star r -> aux r
  in
  aux

let get_global_vars_in_char { vs; phi; _ } =
  let vs = TVSet.of_list vs in
  let fvs = fv_prop phi in
  let fvs = List.filter (fun x -> not (TVSet.mem x vs)) fvs in
  TVSet.of_list fvs

let get_global_vars_in_chars cs =
  CharSet.fold (fun c -> TVSet.union (get_global_vars_in_char c)) cs TVSet.empty

let get_global_vars_in_reg =
  get_in_regex (get_global_vars_in_chars, TVSet.union, TVSet.empty)

let get_constant_in_char { phi; _ } = ConstSet.of_list @@ get_consts phi

let get_constant_in_chars cs =
  CharSet.fold
    (fun c -> ConstSet.union (get_constant_in_char c))
    cs ConstSet.empty

let get_constant_in_reg =
  get_in_regex (get_constant_in_chars, ConstSet.union, ConstSet.empty)

let get_constant_in_char { phi; _ } = LitSet.of_list @@ get_lits phi

let get_lits_in_chars cs =
  CharSet.fold (fun c -> LitSet.union (get_constant_in_char c)) cs LitSet.empty

let get_lits_in_reg =
  get_in_regex (get_lits_in_chars, LitSet.union, LitSet.empty)

let mybuild_euf vars =
  let vars = List.map (fun lit -> lit #: (lit_to_nt lit)) vars in
  let space = Hashtbl.create 10 in
  let () =
    List.iter
      (fun { x; ty } ->
        match Hashtbl.find_opt space ty with
        | None -> Hashtbl.add space ty [ x ]
        | Some l -> Hashtbl.replace space ty (x :: l))
      vars
  in
  let aux ty vars =
    let pairs = List.combination_l vars 2 in
    let pairs =
      List.filter
        (function [ x; y ] -> compare_lit Nt.compare_nt x y > 0 | _ -> false)
        pairs
    in
    let eqlits =
      List.map
        (fun l ->
          match l with [ x; y ] -> mk_lit_eq_lit ty x y | _ -> _die [%here])
        pairs
    in
    eqlits
  in
  let res =
    Hashtbl.fold
      (fun ty vars res ->
        if
          List.length vars > 1 && not (Nt.equal_nt ty (Nt.Ty_uninter "Bytes.t"))
        then aux ty vars @ res
        else res)
      space []
  in
  res

let mk_ftab if_add_lt (vars : (Nt.nt, string) typed list) (cs : constant list) =
  (* Remove boolean constants *)
  let bvars, vars =
    List.partition (fun x -> Nt.equal_nt x.ty Nt.Ty_bool) vars
  in
  let cs = List.filter (function B _ -> false | _ -> true) cs in
  let lits = List.map (fun x -> AVar x) vars @ List.map (fun x -> AC x) cs in
  let () =
    Pp.printf "@{<bold>lits:@} %s\n" (List.split_by_comma layout_lit lits)
  in
  let additional =
    if if_add_lt then
      let int_lits =
        List.filter (fun lit -> Nt.equal_nt Nt.Ty_int @@ lit_to_nt lit) lits
      in
      let () =
        Pp.printf "@{<bold>int lits:@} %s\n"
          (List.split_by_comma layout_lit int_lits)
      in
      let pairs = List.combination_l int_lits 2 in
      let ltlits =
        let lt = ">" #: Nt.(construct_arr_tp ([ Ty_int; Ty_int ], Ty_bool)) in
        List.map
          (fun l ->
            match l with
            | [ x; y ] -> AAppOp (lt, [ x #: Nt.Ty_int; y #: Nt.Ty_int ])
            | _ -> _die [%here])
          pairs
      in
      let () =
        Pp.printf "@{<bold>ltlits:@} %s\n"
          (List.split_by_comma layout_lit ltlits)
      in
      ltlits
    else []
  in
  let res = List.map (fun x -> AVar x) bvars @ mybuild_euf lits @ additional in
  res

let mk_desym_ctx tyctx event_tyctx (gprop, r) =
  let event_tyctx = Typectx.ctx_to_map event_tyctx in
  let gavrs = TVSet.of_list @@ fv_prop gprop in
  let global_vars =
    List.of_seq @@ TVSet.to_seq (TVSet.union gavrs @@ get_global_vars_in_reg r)
  in
  let if_add_lt =
    match Typectx.get_opt tyctx ">" with None -> false | Some _ -> true
  in
  let constants = List.of_seq @@ ConstSet.to_seq @@ get_constant_in_reg r in
  let global_ftab = mk_ftab if_add_lt global_vars constants in
  let local_ftab =
    StrMap.map
      (fun local_vars ->
        let ftab = mk_ftab if_add_lt (global_vars @ local_vars) constants in
        let local_vars_id = List.map _get_x local_vars in
        let ftab =
          List.filter
            (fun lit ->
              not
                (List.is_empty
                @@ List.interset String.equal local_vars_id (fv_lit_id lit)))
            ftab
        in
        ftab)
      event_tyctx
  in
  let desym_map = mk_desym_map (global_ftab, local_ftab) in
  { global_vars; event_tyctx; global_ftab; local_ftab; desym_map }

(* type desym_fact = { *)
(*   global_fact : bool *)
(*   event_tyctx : (Nt.nt, string) typed list Typectx.ctx; *)
(*   event_ftab : LitSet.t StrMap.t; *)
(* } *)
