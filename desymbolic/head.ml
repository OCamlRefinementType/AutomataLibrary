open Zutils
open Prop
open Zdatatype
open Fa
open Myconfig

type features = Nt.t lit array

type head = {
  global_features : features;
  local_features : ((Nt.t, string) typed list * features) StrMap.t;
}

let pprint_tab m =
  if Array.length m == 0 then Pp.printf "Empty\n"
  else
    Array.iteri (fun idx lit -> Pp.printf "@{%i@}: %s, " idx (layout_lit lit)) m;
  Pp.printf "\n"

let pprint_head { global_features; local_features } =
  let () = Pp.printf "[global_features]:" in
  let () = pprint_tab global_features in
  let () = Pp.printf "[local_features]:\n" in
  let () =
    StrMap.iter
      (fun op (_, m) ->
        let () = Pp.printf "[%s]: " op in
        pprint_tab m)
      local_features
  in
  ()

(* let dummy = *)
(*   let t = mk_p_abstract_ty "tSeqNbr" in *)
(*   AAppOp *)
(*     ( "<" #: (Nt.construct_arr_tp ([ t; t ], Nt.Ty_bool)), *)
(*       [ (AVar "seqNbr" #: t) #: t; (AVar "id1" #: t) #: t ] ) *)

let litlist_to_tab (vs, l) =
  (* let l = *)
  (*   if List.exists (fun x -> Nt.equal_nt x.ty (mk_p_abstract_ty "tSeqNbr")) vs then *)
  (*     dummy :: l *)
  (*   else l *)
  (* in *)
  let l' = List.slow_rm_dup eq_lit l in
  let () =
    _log "desymbolic" @@ fun _ ->
    Pp.printf "litlist_to_tab: %s ---> %s\n"
      (List.split_by_comma layout_lit l)
      (List.split_by_comma layout_lit l')
  in
  (vs, Array.of_list l')

let build_partial_one partial_func vars =
  let tys, _ = Nt.destruct_arr_tp partial_func.ty in
  let ty = List.nth tys 0 in
  let vars = List.filter (fun lit -> Nt.equal_nt lit.ty ty) vars in
  let pairs = List.combination_l vars 2 in
  let plits = List.map (fun l -> AAppOp (partial_func, l)) pairs in
  plits

let build_partial partial_funcs vars =
  List.concat @@ List.map (fun f -> build_partial_one f vars) partial_funcs

let get_partail_op lits =
  let lits = List.concat @@ StrMap.to_value_list @@ StrMap.map snd lits in
  let aux = function
    | AAppOp (f, l) when not (String.equal f.x "==") -> (
        match l with [ a; b ] when Nt.equal_nt a.ty b.ty -> Some f | _ -> None)
    | _ -> None
  in
  let res = List.filter_map aux lits in
  List.slow_rm_dup (fun a b -> String.equal a.x b.x) res

let make_tab addtional_global_args regex =
  let g = gather_regex regex in
  (* let num_lits = num_lits g in *)
  (* let () = record_max stat_max_lits num_lits in *)
  let { global_lits; local_lits } = g in
  let () =
    _log "desymbolic" @@ fun _ ->
    Printf.printf "global_lits: %s\n"
      (List.split_by_comma layout_lit global_lits)
  in
  let () =
    _log "desymbolic" @@ fun _ ->
    StrMap.iter
      (fun op (_, m) ->
        Pp.printf "[%s]: %s\n" op (List.split_by_comma layout_lit m))
      local_lits
  in
  let global_args =
    StrMap.map
      (fun (local_vars, lits) ->
        (* let () = Printf.printf "local_vars: %s\n" (layout_qvs local_vars) in *)
        (* let () = *)
        (*   Printf.printf "lits: %s\n" (List.split_by_comma layout_lit lits) *)
        (* in *)
        let local_vars = List.map (fun x -> x.x) local_vars in
        let args = List.concat @@ List.map get_op_args lits in
        let args =
          List.filter
            (fun lit ->
              match List.interset String.equal local_vars (fv_lit_id lit.x) with
              | [] -> true
              | _ -> false)
            args
        in
        args)
      local_lits
  in
  (* let () = Printf.printf "regex: %s\n" (layout_symbolic_regex regex) in *)
  let global_args = List.concat @@ StrMap.to_value_list global_args in
  let global_args =
    List.slow_rm_dup
      (fun x y -> eq_lit x.x y.x)
      (global_args @ addtional_global_args)
  in
  (* let () = *)
  (*   _log "desymbolic" @@ fun _ -> *)
  (*   Printf.printf "global_args: %s\n" *)
  (*     (List.split_by_comma *)
  (*        (fun x -> Sexplib.Sexp.to_string @@ sexp_of_lit Nt.sexp_of_t x.x) *)
  (*        global_args) *)
  (* in *)
  let () =
    _log "desymbolic" @@ fun _ ->
    Printf.printf "global_args: %s\n"
      (List.split_by_comma (fun x -> layout_lit x.x) global_args)
  in
  (* let () = _die [%here] in *)
  let euf_constraints = build_euf global_args in
  let pops = get_partail_op local_lits in
  (* let () = *)
  (*   Env.show_log "desymbolic" @@ fun _ -> *)
  (*   Printf.printf "pops: %s\n" *)
  (*   @@ List.split_by_comma (fun x -> Op.to_string x.x) pops *)
  (* in *)
  let partial_constraints = build_partial pops global_args in
  let global_features =
    Array.of_list
    @@ List.slow_rm_dup (fun x y -> eq_lit x y)
    @@ global_lits @ euf_constraints @ partial_constraints
  in
  let local_features = StrMap.map litlist_to_tab local_lits in
  (* let () = *)
  (*   StrMap.iter *)
  (*     (fun op (_, tab) -> *)
  (*       Printf.printf "[%s]:\n" op; *)
  (*       pprint_tab tab) *)
  (*     local_features *)
  (* in *)
  let res = { global_features; local_features } in
  res

let filter_aviable_features checker (vs, features) =
  let f lit =
    let prop_pos = Lit lit #: Nt.Ty_bool in
    let prop_neg = Not prop_pos in
    checker (vs, prop_pos) && checker (vs, prop_neg)
  in
  Array.of_list @@ List.filter f @@ Array.to_list features

let refine_head checker { global_features; local_features } =
  let global_features = filter_aviable_features checker ([], global_features) in
  let local_features =
    StrMap.map
      (fun (vs, lits) -> (vs, filter_aviable_features checker (vs, lits)))
      local_features
  in
  { global_features; local_features }

let ctx_ctx_init qvs regex =
  let qvs = List.map (fun v -> (AVar v) #: v.ty) qvs in
  let tab = make_tab qvs regex in
  let () = _log "desymbolic" @@ fun _ -> pprint_head tab in
  tab
