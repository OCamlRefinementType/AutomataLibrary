open Common
open Zutils
open Zdatatype

module MakeBasicAutomata (C : CHARAC) = struct
  module CharMap = Map.Make (C)
  module CharSet = Set.Make (C)

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type nfa = {
    start : StateSet.t;
    finals : StateSet.t;
    next : transitions StateMap.t;
  }

  type dfa = {
    start : state;
    finals : StateSet.t;
    next : d_transition StateMap.t;
  }

  let _get_next next m =
    match StateMap.find_opt m next with
    | Some res -> res
    | None -> CharMap.empty

  let ( #-> ) = _get_next

  let nfa_find_states sym (nfa : nfa) m =
    try CharMap.find sym nfa.next #-> m with Not_found -> StateSet.empty

  let _iter_to_fold (type a b c) (iter : (c -> unit) -> a -> unit) :
      (c -> b -> b) -> a -> b -> b =
   fun f container init ->
    let v = ref init in
    iter (fun s -> v := f s !v) container;
    !v

  let nfa_iter_states (f : state -> unit) (nfa : nfa) : unit =
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        f state;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> visit) nfa.next #-> state)
    and visit states = StateSet.iter apply states in
    visit nfa.start

  let dfa_iter_states (f : state -> unit) (dfa : dfa) : unit =
    let seen = Hashtbl.create 10 in
    let rec apply state =
      if not (Hashtbl.mem seen state) then (
        f state;
        Hashtbl.add seen state ();
        CharMap.iter (fun _ -> apply) dfa.next #-> state)
    in
    apply dfa.start

  let nfa_iter_transitions (f : state * C.t * state -> unit) (nfa : nfa) : unit
      =
    nfa_iter_states
      (fun s ->
        CharMap.iter
          (fun (c : C.t) -> StateSet.iter (fun (dst : state) -> f (s, c, dst)))
          nfa.next #-> s)
      nfa

  let dfa_iter_transitions (f : state * C.t * state -> unit) (dfa : dfa) : unit
      =
    dfa_iter_states
      (fun s ->
        CharMap.iter (fun (c : C.t) dst -> f (s, c, dst)) dfa.next #-> s)
      dfa

  let nfa_fold_states (type a) : (state -> a -> a) -> nfa -> a -> a =
   fun f container init ->
    let v = ref init in
    nfa_iter_states (fun s -> v := f s !v) container;
    !v

  let dfa_fold_states (type a) : (state -> a -> a) -> dfa -> a -> a =
   fun f container init ->
    let v = ref init in
    dfa_iter_states (fun s -> v := f s !v) container;
    !v

  let nfa_fold_transitions (type a) :
      (state * C.t * state -> a -> a) -> nfa -> a -> a =
   fun f container init ->
    let v = ref init in
    nfa_iter_transitions (fun s -> v := f s !v) container;
    !v

  let dfa_fold_transitions (type a) :
      (state * C.t * state -> a -> a) -> dfa -> a -> a =
   fun f container init ->
    let v = ref init in
    dfa_iter_transitions (fun s -> v := f s !v) container;
    !v

  let layout_nfa (nfa : nfa) =
    let res =
      Printf.sprintf "\nstarts: %s\n" (layout_states Int.to_string nfa.start)
    in
    let res =
      Printf.sprintf "%sfinals: %s\n" res
        (layout_states Int.to_string nfa.finals)
    in
    let res =
      nfa_fold_transitions
        (fun (s, c, d) res ->
          Printf.sprintf "\t%s--[%s]-->%s\n%s" (Int.to_string s) (C.layout c)
            (Int.to_string d) res)
        nfa res
    in
    res ^ "\n"

  let layout_dfa (dfa : dfa) =
    (* let open Zdatatype in *)
    let res = Printf.sprintf "\nstarts: %s\n" (Int.to_string dfa.start) in
    let res =
      Printf.sprintf "%sfinals: %s\n" res
        (layout_states Int.to_string dfa.finals)
    in
    let res =
      dfa_fold_transitions
        (fun (s, c, d) res ->
          Printf.sprintf "\t%s--[%s]-->%s\n%s" (Int.to_string s) (C.layout c)
            (Int.to_string d) res)
        dfa res
    in
    res ^ "\n"

  let nfa_charmap_insert (c : C.t) (d : state) (charmap : StateSet.t CharMap.t)
      =
    CharMap.update c
      (function
        | None -> Some (StateSet.singleton d)
        | Some ss -> Some (StateSet.add d ss))
      charmap

  let dfa_charmap_insert (c : C.t) (d : state) (charmap : state CharMap.t) =
    CharMap.update c
      (function
        | None -> Some d
        | Some d' when not (Int.equal d d') -> _die [%here]
        | Some d' -> Some d')
      charmap

  let nfa_next_insert (s : state) (c : C.t) (d : state) next =
    StateMap.update s
      (function
        | None -> Some (CharMap.singleton c (StateSet.singleton d))
        | Some charmap -> Some (nfa_charmap_insert c d charmap))
      next

  let dfa_next_insert (s : state) (c : C.t) (d : state) next =
    StateMap.update s
      (function
        | None -> Some (CharMap.singleton c d)
        | Some charmap -> Some (dfa_charmap_insert c d charmap))
      next

  let nfa_next_map_state renaming (nfa : nfa) =
    nfa_fold_transitions
      (fun (s, c, d) ->
        let s = renaming s in
        let d = renaming d in
        nfa_next_insert s c d)
      nfa StateMap.empty

  let dfa_next_map_state renaming (dfa : dfa) =
    dfa_fold_transitions
      (fun (s, c, d) ->
        let s = renaming s in
        let d = renaming d in
        dfa_next_insert s c d)
      dfa StateMap.empty

  let nfa_next_map_c renaming (nfa : nfa) =
    nfa_fold_transitions
      (fun (s, c, d) -> nfa_next_insert s (renaming c) d)
      nfa StateMap.empty

  let dfa_next_map_c renaming (dfa : dfa) =
    dfa_fold_transitions
      (fun (s, c, d) -> dfa_next_insert s (renaming c) d)
      dfa StateMap.empty

  let nfa_map_state map_state (nfa : nfa) : nfa =
    let next = nfa_next_map_state map_state nfa in
    {
      start = StateSet.map map_state nfa.start;
      finals = StateSet.map map_state nfa.finals;
      next;
    }

  let dfa_map_state map_state (dfa : dfa) : dfa =
    let next = dfa_next_map_state map_state dfa in
    {
      start = map_state dfa.start;
      finals = StateSet.map map_state dfa.finals;
      next;
    }

  let nfa_map_c map_state (nfa : nfa) : nfa =
    let next = nfa_next_map_c map_state nfa in
    { start = nfa.start; finals = nfa.finals; next }

  let dfa_map_c map_state (dfa : dfa) : dfa =
    let next = dfa_next_map_c map_state dfa in
    { start = dfa.start; finals = dfa.finals; next }

  let force_nfa ({ start; finals; next } : dfa) : nfa =
    {
      start = StateSet.singleton start;
      finals;
      next = StateMap.map (CharMap.map StateSet.singleton) next;
    }

  let normalize_nfa (nfa : nfa) : nfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = nfa_iter_states (fun s -> do_state_renaming s) nfa in
    let f s =
      (* NOTE: if there is unreachable final states, maps to 0 *)
      match StateMap.find_opt s !state_naming with
      | Some s' -> s'
      | None -> _default_init_state
    in
    nfa_map_state f nfa

  let normalize_dfa (dfa : dfa) : dfa =
    let state_naming = ref StateMap.empty in
    let next_state = ref _default_init_state in
    let incr () =
      let res = !next_state in
      next_state := Int.add 1 !next_state;
      res
    in
    let do_state_renaming s =
      match StateMap.find_opt s !state_naming with
      | Some _ -> ()
      | None -> state_naming := StateMap.add s (incr ()) !state_naming
    in
    let () = dfa_iter_states (fun s -> do_state_renaming s) dfa in
    let f s =
      (* NOTE: if there is unreachable final states, maps to 0 *)
      match StateMap.find_opt s !state_naming with
      | Some s' -> s'
      | None -> _default_init_state
    in
    dfa_map_state f dfa

  let num_states_nfa (nfa : nfa) = nfa_fold_states (fun _ x -> x + 1) nfa 0
  let num_states_dfa (dfa : dfa) = dfa_fold_states (fun _ x -> x + 1) dfa 0

  let num_transition_nfa (nfa : nfa) =
    nfa_fold_transitions (fun _ x -> x + 1) nfa 0

  let num_transition_dfa (dfa : dfa) =
    dfa_fold_transitions (fun _ x -> x + 1) dfa 0

  let mk_disjoint_multi_nfa (nfa : nfa list) =
    let nfa = List.map normalize_nfa nfa in
    let _, nfa =
      List.fold_left
        (fun (sum, res) (nfa : nfa) ->
          (sum + num_states_nfa nfa, res @ [ nfa_map_state (( + ) sum) nfa ]))
        (0, []) nfa
    in
    nfa

  let mk_disjoint_multi_dfa (dfa : dfa list) =
    let dfa = List.map normalize_dfa dfa in
    let _, dfa =
      List.fold_left
        (fun (sum, res) (dfa : dfa) ->
          (sum + num_states_dfa dfa, res @ [ dfa_map_state (( + ) sum) dfa ]))
        (0, []) dfa
    in
    dfa

  let mk_disjoint_nfa (nfa1, nfa2) =
    match mk_disjoint_multi_nfa [ nfa1; nfa2 ] with
    | [ nfa1; nfa2 ] -> (nfa1, nfa2)
    | _ -> _die [%here]

  let mk_disjoint_dfa (dfa1, dfa2) =
    match mk_disjoint_multi_dfa [ dfa1; dfa2 ] with
    | [ dfa1; dfa2 ] -> (dfa1, dfa2)
    | _ -> _die [%here]

  let nfa_union_charmap c1 c2 =
    CharMap.union (fun _ s1 s2 -> Some (StateSet.union s1 s2)) c1 c2

  let dfa_union_charmap c1 c2 = CharMap.union (fun _ _ _ -> _die [%here]) c1 c2

  let nfa_union_next next1 next2 =
    StateMap.union (fun _ m1 m2 -> Some (nfa_union_charmap m1 m2)) next1 next2

  let dfa_union_next next1 next2 =
    StateMap.union (fun _ m1 m2 -> Some (dfa_union_charmap m1 m2)) next1 next2

  (** Complete *)

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
          let m = nfa.next #-> state in
          CharSet.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
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
          let m = dfa.next #-> state in
          CharSet.iter
            (fun c ->
              match CharMap.find_opt c m with
              | None -> point_to_dummy_node (state, c)
              | Some _ -> ())
            ctx)
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

  let flat_map f ss =
    StateSet.fold (fun s -> StateSet.union (f s)) ss StateSet.empty

  let nextss curs sym nfa = flat_map (nfa_find_states sym nfa) curs

  let nfa_accept (nfa : nfa) inp =
    let rec step cur = function
      | [] -> StateSet.(not (is_empty (inter cur nfa.finals)))
      | c :: cs -> step (nextss cur c nfa) cs
    in
    step nfa.start inp

  let dfa_accept (dfa : dfa) inp =
    let rec step cur = function
      | [] -> StateSet.mem cur dfa.finals
      | c :: cs -> (
          match CharMap.find_opt c dfa.next #-> cur with
          | None -> false
          | Some s' -> step s' cs)
    in
    step dfa.start inp

  (** next mapping of dfa can be rewritten into another form. *)

  let dfa_next_to_ss_next next =
    dfa_fold_transitions
      (fun (s, c, d) ->
        StateMap.update s (function
          | None -> Some (StateMap.singleton d (CharSet.singleton c))
          | Some m ->
              Some
                (StateMap.update d
                   (function
                     | None -> Some (CharSet.singleton c)
                     | Some cs -> Some (CharSet.add c cs))
                   m)))
      next StateMap.empty

  let ss_next_to_next (ss_next : CharSet.t StateMap.t StateMap.t) =
    StateMap.fold
      (fun s ->
        StateMap.fold (fun d -> CharSet.fold (fun c -> dfa_next_insert s c d)))
      ss_next StateMap.empty

  (** Regex *)

  open RegexTree

  let rec seq_unfold = function
    | Seq l -> List.concat_map seq_unfold l
    | Eps -> []
    | _ as r -> [ r ]

  let smart_seq l =
    let l = seq_unfold (Seq l) in
    if List.exists (function Empty -> true | _ -> false) l then Empty
    else match l with [] -> Eps | [ x ] -> x | _ -> Seq l

  let smart_alt a b =
    match (a, b) with
    | Empty, _ -> b
    | _, Empty -> a
    | MultiChar c1, MultiChar c2 -> MultiChar (CharSet.union c1 c2)
    | _, _ -> Alt (a, b)

  let smart_alt_list l = List.left_reduce [%here] smart_alt (Empty :: l)

  let smart_inter a b =
    match (a, b) with
    | Empty, _ -> Empty
    | _, Empty -> Empty
    | MultiChar c1, MultiChar c2 -> MultiChar (CharSet.inter c1 c2)
    | _, _ -> Inters (a, b)

  let smart_star r = match r with Empty -> Empty | Eps -> Eps | r -> Star r

  (** Deriviate *)

  let rec emptiness (r : CharSet.t raw_regex) =
    match r with
    | Empty -> true
    | Eps -> false
    | MultiChar cs -> CharSet.is_empty cs
    | Seq l -> List.exists emptiness l
    | Inters (r1, r2) -> emptiness r1 || emptiness r2
    | Alt (r1, r2) -> emptiness r1 && emptiness r2
    | Comple _ -> _die_with [%here] "should remove all comple"
    | Star _ -> false

  let rec nullable (r : CharSet.t raw_regex) =
    match r with
    | Empty -> false
    | Eps -> true
    | MultiChar _ -> false
    | Seq l -> List.for_all nullable l
    | Inters (r1, r2) -> nullable r1 && nullable r2
    | Alt (r1, r2) -> nullable r1 || nullable r2
    | Comple (_, r) -> not (nullable r)
    | Star _ -> true

  let brzozowski_derivative_char (f : 'a -> C.t -> bool) (char : 'a)
      (r : CharSet.t raw_regex) =
    let rec aux = function
      | Empty -> Empty
      | Eps -> Empty
      | MultiChar cs -> if CharSet.exists (f char) cs then Eps else Empty
      | Seq l ->
          let rec iter res = function
            | [] -> res
            | r :: l ->
                let res = smart_seq (aux r :: l) :: res in
                if nullable r then iter res l else res
          in
          smart_alt_list (iter [] l)
      | Inters (r1, r2) -> smart_inter (aux r1) (aux r2)
      | Alt (r1, r2) -> smart_alt (aux r1) (aux r2)
      | Comple (cs, r) -> Comple (cs, aux r)
      | Star r -> smart_seq [ aux r; Star r ]
    in
    aux r

  let brzozowski_derivative (f : 'a -> C.t -> bool) (r : CharSet.t raw_regex) l
      =
    let rec aux r = function
      | [] -> r
      | u :: l -> aux (brzozowski_derivative_char f u r) l
    in
    aux r l

  let is_match (f : 'a -> C.t -> bool) (r : CharSet.t raw_regex) l =
    nullable (brzozowski_derivative f r l)
end
