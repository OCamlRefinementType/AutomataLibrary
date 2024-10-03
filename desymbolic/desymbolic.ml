include Head
open Zdatatype
open Prop
open Fa
open Zutils
open Myconfig

let partial_evaluate_lit global_tab lit =
  match Hashtbl.find_opt global_tab lit.x with
  | Some b -> { x = AC (B b); ty = Nt.Ty_bool }
  | None -> lit

let partial_evaluate_prop global_tab prop =
  let rec aux prop =
    match prop with
    | Lit lit -> Lit (partial_evaluate_lit global_tab lit)
    | Implies (a, b) -> Implies (aux a, aux b)
    | Ite (a, b, c) -> Ite (aux a, aux b, aux c)
    | Not a -> Not (aux a)
    | And es -> And (List.map aux es)
    | Or es -> Or (List.map aux es)
    | Iff (a, b) -> Iff (aux a, aux b)
    | Forall _ | Exists _ -> _die [%here]
  in
  aux prop

let models_lit tab lit =
  (* let () = *)
  (*   Printf.printf "%s\n" *)
  (*   @@ List.split_by_comma layout_lit *)
  (*   @@ List.of_seq @@ Hashtbl.to_seq_keys tab *)
  (* in *)
  match Hashtbl.find_opt tab lit.x with
  | Some b -> b
  | None -> _failatwith [%here] (spf "tab_models_lit(%s)" (layout_lit lit.x))

let models_prop m prop =
  let rec aux prop =
    match prop with
    | Lit { x = AC (B b); _ } -> b
    | Lit lit -> models_lit m lit
    | Implies (a, b) -> (not (aux a)) || aux b
    | Ite (a, b, c) -> if aux a then aux b else aux c
    | Not a -> not (aux a)
    | And es -> List.for_all aux es
    | Or es -> List.exists aux es
    | Iff (a, b) -> aux (Implies (a, b)) && aux (Implies (b, a))
    | Forall _ | Exists _ -> _die [%here]
  in
  aux prop

let partial_evaluate_sevent global_tab se =
  (* let open NRegex in *)
  match se with
  | GuardEvent _ ->
      _die [%here] (* if models_prop global_tab phi then AnyA else EmptyA *)
  | EffEvent { op; vs; phi } ->
      let phi = partial_evaluate_prop global_tab phi in
      Atomic (EffEvent { op; vs; phi })

let partial_evaluate_regex global_tab regex =
  (* let () = *)
  (*   Pp.printf "@{<bold>regex before:@} %s\n" (layout_symbolic_regex regex) *)
  (* in *)
  let rec aux regex =
    match regex with
    | Extension _ | SyntaxSugar _ | RExpr _ -> _die [%here]
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | EmptyA | EpsilonA -> regex
    | Atomic se -> partial_evaluate_sevent global_tab se
    | MultiAtomic ses ->
        MultiAtomic
          (List.map
             (fun x ->
               match partial_evaluate_sevent global_tab x with
               | Atomic e -> e
               | _ -> _die [%here])
             ses)
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA t -> StarA (aux t)
    | DComplementA { atoms; body } -> DComplementA { atoms; body = aux body }
  in
  let res = aux regex in
  res

let desymbolic_sevent dts se =
  match se with
  | GuardEvent _ -> _die [%here]
  | EffEvent { op; phi; _ } ->
      let local_m = StrMap.find "desymbolic_sevent" dts op in
      let mts =
        List.filter_map
          (fun (idx, local_tab) ->
            if models_prop local_tab phi then Some idx else None)
          local_m
      in
      let mts = List.map (fun local_embedding -> (op, local_embedding)) mts in
      mts

(* NOTE: the None indicate the empty set *)
let desymbolic_local dts regex =
  let rec aux regex =
    match regex with
    | Extension _ | SyntaxSugar _ | RExpr _ -> _die [%here]
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | Atomic se -> labels_to_multiatomic @@ desymbolic_sevent dts se
    | MultiAtomic se ->
        labels_to_multiatomic @@ List.concat_map (desymbolic_sevent dts) se
    | LorA (t1, t2) -> LorA (aux t1, aux t2)
    | LandA (t1, t2) -> LandA (aux t1, aux t2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA t -> StarA (aux t)
    | DComplementA { atoms; body } ->
        let atoms =
          List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b)
          @@ List.concat_map (desymbolic_sevent dts) atoms
        in
        DComplementA { atoms; body = aux body }
  in
  let res = aux regex in
  (* let () = *)
  (*   Env.show_log "regex_simpl" @@ fun _ -> *)
  (*   Pp.printf "@{<bold>regex after:@} %s\n" (reg_to_string res) *)
  (* in *)
  (* let res = simp res in *)
  (* let () = *)
  (*   Env.show_log "regex_simpl" @@ fun _ -> *)
  (*   Pp.printf "@{<bold>regex simpl:@} %s\n" (reg_to_string res) *)
  (* in *)
  res

(* let desymbolic_under_global (global_embedding, global_m, dts) regex = *)
(*   let regex' = partial_evaluate_regex global_m regex in *)
(*   desymbolic_local global_embedding dts regex' *)

(* let desymbolic tab regex = *)
(*   List.map (fun tab -> desymbolic_under_global tab regex) tab *)

let dts_to_backward_dts dt =
  StrMap.map
    (fun l ->
      List.fold_right
        (fun (idx, tab) -> IntMap.add idx (Mapping.tab_to_prop tab))
        l IntMap.empty)
    dt

let mk_backward_mapping_aux { local_features; _ } local op ids =
  let vs, features = StrMap.find "die" local_features op in
  let local_m = StrMap.find "die" local op in
  (* let () = *)
  (*   Printf.printf "op = %s; vs = %s\n" op *)
  (*     (List.split_by_comma (fun x -> x.x) vs) *)
  (* in *)
  let phi = Mapping.mk_simp_local_prop features local_m ids in
  EffEvent { op; vs; phi }
(* let props = List.map (IntMap.find "die" local_m) ids in *)
(* EffEvent { op; vs; phi = Or props } *)

let mk_backward_mapping head local (es : DesymFA.CharSet.t) =
  let m =
    DesymFA.CharSet.fold
      (fun (op, id) ->
        StrMap.update op (function
          | None -> Some [ id ]
          | Some l -> Some (id :: l)))
      es StrMap.empty
  in
  let m = StrMap.mapi (mk_backward_mapping_aux head local) m in
  SFA.CharSet.of_list @@ StrMap.to_value_list m

let mk_original_backward_mapping head local (es : DesymFA.CharSet.t) =
  let m =
    DesymFA.CharSet.fold
      (fun (op, id) ->
        let vs, features = StrMap.find "die" head.local_features op in
        let local_m = StrMap.find "die" local op in
        let phi = Mapping.get_local_prop features local_m id in
        let se = EffEvent { op; vs; phi } in
        SFA.CharSet.add se)
      es SFA.CharSet.empty
  in
  m

type mode = UnionFA | OriginalFA

let desymbolic mode checker (qvs, srl) =
  let head = ctx_ctx_init qvs srl in
  let head = refine_head checker head in
  (* let () = Env.show_log "desymbolic" @@ fun _ -> Head.pprint_head head in *)
  let dts = Mapping.mk_mt_tab checker head in
  let () =
    _log "desymbolic" @@ fun _ ->
    Pp.printf "@{<bold>regex before:@} %s\n" (layout_symbolic_regex srl)
  in
  let automata =
    List.map
      (fun (_, global, local) ->
        let srl = partial_evaluate_regex global srl in
        let global_prop = Mapping.tab_to_prop global in
        let () =
          _log "desymbolic" @@ fun _ ->
          Pp.printf "@{<bold>Under global prop:@} %s\n"
            (layout_prop global_prop)
        in
        let () =
          _log "desymbolic" @@ fun _ ->
          Pp.printf "@{<bold>regex simpl:@} %s\n" (layout_symbolic_regex srl)
        in
        let automaton = desymbolic_local local srl in
        let () =
          _log "desymbolic" @@ fun _ ->
          Pp.printf "\n@{<bold>After Desymbolic:@}\n%s\n"
            (layout_desym_regex automaton)
        in
        let automaton = simp_regex DesymLabel.equal automaton in
        let () =
          _log "desymbolic" @@ fun _ ->
          Pp.printf "\n@{<bold>After Simplication:@}\n%s\n"
            (layout_desym_regex automaton)
        in
        let backward_maping =
          match mode with
          | UnionFA -> mk_backward_mapping head local
          | OriginalFA -> mk_original_backward_mapping head local
        in
        (global_prop, backward_maping, automaton))
      dts
  in
  automata

(* let desymbolic_qregex checker qregex = *)
(*   let head = ctx_ctx_init (get_regex_from_qregex qregex) in *)
(*   (\* let () = Env.show_log "desymbolic" @@ fun _ -> Head.pprint_head head in *\) *)
(*   let dts = Mapping.mk_mt_tab checker head in *)
(*   let srl' = map_qregex_body (desymbolic_local dts) qregex in *)
(*   let backward_maping = mk_backward_mapping head (dts_to_backward_dts dts) in *)
(*   (backward_maping, srl') *)

let desymbolic_reg mode ctx checker (vs, reg) =
  let () =
    _log "desymbolic" @@ fun _ ->
    Pp.printf "\n@{<bold>Input:@}\n%s\n" (layout_symbolic_regex reg)
  in
  let reg = desugar ctx reg in
  let () =
    _log "desymbolic" @@ fun _ ->
    Pp.printf "\n@{<bold>After Desugar:@}\n%s\n" (layout_symbolic_regex reg)
  in
  let reg = delimit_context delimit_cotexnt_se reg in
  let () =
    _log "desymbolic" @@ fun _ ->
    Pp.printf "\n@{<bold>After Delimit Context@}:\n%s\n"
      (layout_symbolic_regex reg)
  in
  desymbolic mode checker (vs, reg)

let desymbolic_regspec mode ctx checker (vs, reg) =
  let reg = desymbolic_reg mode ctx checker (vs, reg) in
  (vs, reg)

let regspec_to_sfa mode ctx m =
  let vs, reg =
    (desymbolic_regspec mode ctx)
      (fun (_, prop) -> Prover.check_sat_bool prop)
      m
  in
  (* let () = Printf.printf " zz?: %s\n" @@ layout_symbolic_regex reg in *)
  let module DFA = DesymFA in
  let f (global_prop, bmap, reg) =
    let fa = DFA.compile_regex_to_dfa reg in
    (* let () = Pp.printf "\n@{<bold>To DFA:@}\n%s\n" (DFA.layout_dfa fa) in *)
    let sfa = SFA.from_desym_dfa bmap fa in
    (* let () = Pp.printf "\n@{<bold>Back To SFA:@}\n%s\n" (SFA.layout_dfa sfa) in *)
    (global_prop, sfa)
  in
  (vs, List.map f reg)
