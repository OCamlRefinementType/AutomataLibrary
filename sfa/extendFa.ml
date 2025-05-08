open Zutils
open Language
open Common
open BasicFa

module MakeExtendAutomata (AB : ALPHABET) = struct
  include MakeBasicAutomata (AB)

  (** realize *)
  let compact_ss (ss_next : CharSet.t StateMap.t StateMap.t) =
    StateMap.map (StateMap.map AB.compact_set) ss_next

  let dfa_compact (dfa : dfa) =
    { dfa with next = ss_next_to_next @@ compact_ss @@ dfa_next_to_ss_next dfa }

  let dfa_realize (char_realizable_checker : C.t -> bool) (dfa : dfa) =
    let ss = compact_ss @@ dfa_next_to_ss_next dfa in
    let ss =
      StateMap.filter_map
        (fun _ m ->
          Some
            (StateMap.filter_map
               (fun _ s -> Some (CharSet.filter char_realizable_checker s))
               m))
        ss
    in
    { dfa with next = ss_next_to_next ss }

  (** Complete *)

  let layout_set s =
    let open Zdatatype in
    List.split_by_comma C.layout @@ List.of_seq @@ CharSet.to_seq s

  let complete_nfa (ctx : CharSet.t) (nfa : nfa) =
    (* Add a dummy node to complete the nfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      nfa_iter_states
        (fun state ->
          let () = update_max state in
          let m = nfa.next#->state in
          let m' = CharSet.of_seq @@ fst @@ Seq.split @@ CharMap.to_seq m in
          let ctx' = AB.subtract_set ctx m' in
          (* let () = *)
          (*   Printf.printf "(%s) - (%s) = (%s)\n" (layout_set ctx) *)
          (*     (layout_set m') (layout_set ctx') *)
          (* in *)
          CharSet.iter (fun c -> point_to_dummy_node (state, c)) ctx')
        nfa
    in
    (* reverse the nfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      nfa
    else
      match !max_state with
      | None -> _die [%here]
      | Some s' ->
          let char_map =
            CharSet.fold (fun c -> nfa_charmap_insert c s') ctx CharMap.empty
          in
          let next' = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c -> StateSet.fold (fun s -> nfa_next_insert s c s'))
              dummy_transitions next'
          in
          {
            start = nfa.start;
            finals = nfa.finals;
            next = nfa_union_next nfa.next next';
          }

  let complete_dfa (ctx : CharSet.t) (dfa : dfa) =
    (* Add a dummy node to complete the dfa, where we just record the transitions to this node. *)
    let max_state = ref None in
    let update_max s =
      match !max_state with
      | None -> max_state := Some (Int.add s 1)
      | Some n -> if s >= n then max_state := Some (Int.add s 1) else ()
    in
    let dummy_transitions = Hashtbl.create 1000 in
    let point_to_dummy_node (s, c) =
      (* let () = *)
      (*   Printf.printf "### --%s-->%s\n" (C.layout c) (Int.to_string s) *)
      (* in *)
      match Hashtbl.find_opt dummy_transitions c with
      | None -> Hashtbl.add dummy_transitions c (StateSet.singleton s)
      | Some ss -> Hashtbl.replace dummy_transitions c (StateSet.add s ss)
    in
    let () =
      dfa_iter_states
        (fun state ->
          let () = update_max state in
          let m = dfa.next#->state in
          let m' = CharSet.of_seq @@ fst @@ Seq.split @@ CharMap.to_seq m in
          let ctx' = AB.subtract_set ctx m' in
          (* let () = *)
          (*   Printf.printf "(%s) - (%s) = (%s)\n" (layout_set ctx) *)
          (*     (layout_set m') (layout_set ctx') *)
          (* in *)
          CharSet.iter (fun c -> point_to_dummy_node (state, c)) ctx')
        dfa
    in
    (* reverse the dfa *)
    if Hashtbl.length dummy_transitions == 0 then (* already complete *)
      dfa
    else
      match !max_state with
      | None -> _die [%here]
      | Some s' ->
          let char_map =
            CharSet.fold (fun c -> dfa_charmap_insert c s') ctx CharMap.empty
          in
          let next' = StateMap.add s' char_map StateMap.empty in
          let next' =
            Hashtbl.fold
              (fun c -> StateSet.fold (fun s -> dfa_next_insert s c s'))
              dummy_transitions next'
          in
          {
            start = dfa.start;
            finals = dfa.finals;
            next = dfa_union_next dfa.next next';
          }

  let intersect_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    let dfa1 = normalize_dfa dfa1 in
    let dfa2 = normalize_dfa dfa2 in
    let num2 = num_states_dfa dfa2 in
    let mk_p (n1 : state) (n2 : state) = Int.add n2 @@ Int.mul num2 n1 in
    let fst_p p = Int.div p num2 in
    let snd_p p = Int.rem p num2 in
    let seen = Hashtbl.create 1000 in
    let tbl = ref StateMap.empty in
    let update_tbl (s, c, d) =
      tbl :=
        StateMap.update s
          (function
            | None -> Some (CharMap.singleton c d)
            | Some charmap -> Some (CharMap.add c d charmap))
          !tbl
    in
    let rec visit state =
      if not (Hashtbl.mem seen state) then
        let () = Hashtbl.add seen state () in
        let charmap1 = dfa1.next#->(fst_p state) in
        let charmap2 = dfa2.next#->(snd_p state) in
        CharMap.iter
          (fun c1 d1 ->
            CharMap.iter
              (fun c2 d2 ->
                match C.char_inter c1 c2 with
                | None -> ()
                | Some c ->
                    let d = mk_p d1 d2 in
                    update_tbl (state, c, d);
                    visit d)
              charmap2)
          charmap1
    in
    let start = mk_p dfa1.start dfa2.start in
    let () = visit start in
    let finals =
      StateSet.fold
        (fun s1 ->
          StateSet.fold (fun s2 -> StateSet.add (mk_p s1 s2)) dfa2.finals)
        dfa1.finals StateSet.empty
    in
    let res = { start; finals; next = !tbl } in
    res
end
