open Zutils
open Zdatatype
open Regex

module type FINITE_AUTOMATA = sig
  include ALPHABET

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

  val ( #-> ) : 'a CharMap.t StateMap.t -> StateSet.elt -> 'a CharMap.t
end

module MakeBasicAutomata (AB : ALPHABET) = struct
  include AB

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

  (** Build an NFA by reversing a DFA, inverting transition arrows,
    turning finals states into start states, and the start state into
    the final state *)
  let reverse (dfa : dfa) : nfa =
    let next =
      dfa_fold_transitions
        (fun (s, c, t) -> nfa_next_insert t c s)
        dfa StateMap.empty
    in
    { start = dfa.finals; finals = StateSet.singleton dfa.start; next }

  (** Available transitions from a set of states *)
  let nfa_transitions states (nfa : nfa) =
    StateSet.fold
      (fun s m ->
        let m' = nfa.next #-> s in
        nfa_union_charmap m m')
      states CharMap.empty
end
