open Common
open Zutils
open Regex
open BasicFa

module MakeAutomata (C : CHARAC) = struct
  module EpsC = struct
    type t = C.t option

    let layout = function None -> "none" | Some c -> C.layout c

    (* HACK: dummy imp *)
    let delimit_cotexnt_char (_, c) = [ c ]

    let compare c1 c2 =
      match (c1, c2) with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some c1, Some c2 -> C.compare c1 c2
  end

  module EpsFA = MakeBasicAutomata (EpsC)
  module C = MakeC (C)
  include MakeBasicAutomata (C)
  module CharSet = Set.Make (C)
  open Zdatatype

  type raw_regex = CharSet.t RegexTree.raw_regex

  let raw_regex_to_str_regex r =
    let par = spf "\\(%s\\)" in
    let rec aux = function
      | Empty -> "∅"
      | Eps -> "ε"
      | MultiChar cs ->
          par (List.split_by "\\|" C.layout @@ List.of_seq @@ CharSet.to_seq cs)
      | Alt (r1, r2) -> par @@ spf "%s\\|%s" (aux r1) (aux r2)
      | Inters (r1, r2) -> par @@ spf "%s&%s" (aux r1) (aux r2)
      | Comple (cs, r2) ->
          par @@ spf "%s-%s" (aux (Star (MultiChar cs))) (aux r2)
      | Seq rs -> List.split_by "" aux rs
      | Star r -> spf "%s*" @@ par (aux r)
    in
    "^" ^ aux r ^ "$"

  let layout_raw_regex r =
    let par = spf "(%s)" in
    let rec aux = function
      | Empty -> "∅"
      | Eps -> "ε"
      | MultiChar cs ->
          par (List.split_by "|" C.layout @@ List.of_seq @@ CharSet.to_seq cs)
      | Alt (r1, r2) -> par @@ spf "%s | %s" (aux r1) (aux r2)
      | Inters (r1, r2) -> par @@ spf "%s & %s" (aux r1) (aux r2)
      | Comple (cs, r2) ->
          par @@ spf "%s - %s" (aux (Star (MultiChar cs))) (aux r2)
      | Seq rs -> List.split_by "" aux rs
      | Star r -> spf "%s*" @@ par (aux r)
    in
    aux r

  let force_eps_nfa (nfa : nfa) : EpsFA.nfa =
    {
      start = nfa.start;
      finals = nfa.finals;
      next =
        nfa_fold_transitions
          (fun (s, c, d) m -> EpsFA.nfa_next_insert s (Some c) d m)
          nfa StateMap.empty;
    }

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

  (** Available transitions from a set of states *)
  let eps_nfa_transitions states (nfa : EpsFA.nfa) =
    let tab = Hashtbl.create 10 in
    let rec visit rest trans =
      match rest with
      | [] -> (StateSet.of_seq @@ Hashtbl.to_seq_keys tab, trans)
      | s :: rest -> (
          match Hashtbl.find_opt tab s with
          | Some _ -> visit rest trans
          | None ->
              let () = Hashtbl.add tab s () in
              let m = EpsFA.(nfa.next #-> s) in
              let rest', m =
                EpsFA.CharMap.fold
                  (fun c s' (rest', m) ->
                    match c with
                    | None -> (StateSet.elements s' @ rest', m)
                    | Some c -> (rest', CharMap.add c s' m))
                  m ([], CharMap.empty)
              in
              visit (rest' @ rest) (nfa_union_charmap trans m))
    in
    visit (StateSet.elements states) CharMap.empty

  (** Remove eps via the powerset construction *)
  let eps_determinize : EpsFA.nfa -> dfa =
    let module M = Map.Make (StateSet) in
    fun nfa ->
      let fresh =
        let r = ref (_default_init_state : int) in
        fun () ->
          r := Int.succ !r;
          !r
      in
      let rec build states (map, ts, finals) =
        let states, tsn = eps_nfa_transitions states nfa in
        match M.find states map with
        | state -> (state, map, ts, finals)
        | exception Not_found ->
            let state = fresh () in
            let finals =
              if not (StateSet.is_empty (StateSet.inter states nfa.finals)) then
                StateSet.add state finals
              else finals
            in
            let map = M.add states state map in
            let map, ts, finals =
              CharMap.fold
                (fun c ss (map, ts, finals) ->
                  let dst, map, ts, finals = build ss (map, ts, finals) in
                  let ts = dfa_next_insert state c dst ts in
                  (map, ts, finals))
                tsn (map, ts, finals)
            in
            (state, map, ts, finals)
      in
      let start, _, trans, finals =
        build nfa.start (M.empty, StateMap.empty, StateSet.empty)
      in
      { start; finals; next = trans }

  (** Conversion to DFA via the powerset construction *)
  let determinize : nfa -> dfa =
    let module M = Map.Make (StateSet) in
    fun nfa ->
      let fresh =
        let r = ref (_default_init_state : int) in
        fun () ->
          r := Int.succ !r;
          !r
      in
      let rec build states (map, ts, finals) =
        match M.find states map with
        | state -> (state, map, ts, finals)
        | exception Not_found ->
            let state = fresh () in
            let finals =
              if not (StateSet.is_empty (StateSet.inter states nfa.finals)) then
                StateSet.add state finals
              else finals
            in
            let map = M.add states state map in
            let tsn = nfa_transitions states nfa in
            let map, ts, finals =
              CharMap.fold
                (fun c ss (map, ts, finals) ->
                  let dst, map, ts, finals = build ss (map, ts, finals) in
                  let ts = dfa_next_insert state c dst ts in
                  (map, ts, finals))
                tsn (map, ts, finals)
            in
            (state, map, ts, finals)
      in

      let start, _, trans, finals =
        build nfa.start (M.empty, StateMap.empty, StateSet.empty)
      in
      normalize_dfa { start; finals; next = trans }

  (** Brzozowski's DFA minimization algorithm:
    reverse DFA to build an NFA and determinize, then do the same again *)
  let minimize g = determinize (reverse (determinize (reverse g)))

  (** Complement *)

  (* let complete_dfa (ctx : CharSet.t) (dfa : dfa) = *)
  (*   determinize @@ complete_nfa ctx @@ force_nfa dfa *)

  let swap_dfa (dfa : dfa) : dfa =
    let finals =
      dfa_fold_states
        (fun s res ->
          if StateSet.mem s dfa.finals then res else StateSet.add s res)
        dfa StateSet.empty
    in
    { start = dfa.start; finals; next = dfa.next }

  let swap_nfa (nfa : nfa) : nfa =
    let finals =
      nfa_fold_states
        (fun s res ->
          if StateSet.mem s nfa.finals then res else StateSet.add s res)
        nfa StateSet.empty
    in
    { start = nfa.start; finals; next = nfa.next }

  let complement_dfa (ctx : CharSet.t) (dfa : dfa) =
    swap_dfa @@ complete_dfa ctx dfa

  let complement_nfa (ctx : CharSet.t) (nfa : nfa) =
    swap_nfa @@ complete_nfa ctx nfa

  let complement_eps_nfa (ctx : CharSet.t) (eps_nfa : EpsFA.nfa) =
    force_eps_nfa @@ force_nfa @@ complement_dfa ctx (eps_determinize eps_nfa)

  (** binary operations *)
  let union_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    let nfa1, nfa2 = mk_disjoint_nfa (nfa1, nfa2) in
    {
      start = StateSet.union nfa1.start nfa2.start;
      finals = StateSet.union nfa1.finals nfa2.finals;
      next = nfa_union_next nfa1.next nfa2.next;
    }

  let union_eps_nfa (nfa1 : EpsFA.nfa) (nfa2 : EpsFA.nfa) : EpsFA.nfa =
    let nfa1, nfa2 = EpsFA.mk_disjoint_nfa (nfa1, nfa2) in
    {
      start = StateSet.union nfa1.start nfa2.start;
      finals = StateSet.union nfa1.finals nfa2.finals;
      next = EpsFA.nfa_union_next nfa1.next nfa2.next;
    }

  let union_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    minimize @@ determinize @@ union_nfa (force_nfa dfa1) (force_nfa dfa2)

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
        let charmap1 = dfa1.next #-> (fst_p state) in
        let charmap2 = dfa2.next #-> (snd_p state) in
        CharMap.iter
          (fun c d1 ->
            match CharMap.find_opt c charmap2 with
            | None -> ()
            | Some d2 ->
                let d = mk_p d1 d2 in
                update_tbl (state, c, d);
                visit d)
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
    minimize res

  let intersect_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    force_nfa @@ intersect_dfa (determinize nfa1) (determinize nfa2)

  let intersect_eps_nfa (nfa1 : EpsFA.nfa) (nfa2 : EpsFA.nfa) : EpsFA.nfa =
    force_eps_nfa @@ force_nfa
    @@ intersect_dfa (eps_determinize nfa1) (eps_determinize nfa2)

  let concat_eps_nfa (nfa1 : EpsFA.nfa) (nfa2 : EpsFA.nfa) : EpsFA.nfa =
    let eps_nfa1, eps_nfa2 = EpsFA.mk_disjoint_nfa (nfa1, nfa2) in
    let next = EpsFA.nfa_union_next eps_nfa1.next eps_nfa2.next in
    let next =
      StateSet.fold
        (fun final ->
          StateSet.fold (EpsFA.nfa_next_insert final None) eps_nfa2.start)
        eps_nfa1.finals next
    in
    let eps_nfa : EpsFA.nfa =
      { start = eps_nfa1.start; finals = eps_nfa2.finals; next }
    in
    eps_nfa

  let _concat_nfa (nfa1 : nfa) (nfa2 : nfa) : dfa =
    let eps_nfa = concat_eps_nfa (force_eps_nfa nfa1) (force_eps_nfa nfa2) in
    minimize (eps_determinize eps_nfa)

  let concat_nfa (nfa1 : nfa) (nfa2 : nfa) : nfa =
    force_nfa (_concat_nfa nfa1 nfa2)

  let concat_dfa (dfa1 : dfa) (dfa2 : dfa) : dfa =
    _concat_nfa (force_nfa dfa1) (force_nfa dfa2)

  let kleene_eps_nfa (nfa : EpsFA.nfa) : EpsFA.nfa =
    let nfa = EpsFA.normalize_nfa nfa in
    let num = EpsFA.num_states_nfa nfa in
    let new_start = num in
    let new_final = num + 1 in
    let next =
      StateSet.fold (EpsFA.nfa_next_insert new_start None) nfa.start nfa.next
    in
    let next = EpsFA.nfa_next_insert new_start None new_final next in
    let next =
      StateSet.fold
        (fun final -> EpsFA.nfa_next_insert final None new_start)
        nfa.finals next
    in
    let next =
      StateSet.fold
        (fun final -> EpsFA.nfa_next_insert final None new_final)
        nfa.finals next
    in
    let eps_nfa : EpsFA.nfa =
      {
        start = StateSet.singleton new_start;
        finals = StateSet.singleton new_final;
        next;
      }
    in
    eps_nfa

  let _kleene_nfa (nfa : nfa) : dfa =
    let eps_nfa : EpsFA.nfa = kleene_eps_nfa (force_eps_nfa nfa) in
    minimize (eps_determinize eps_nfa)

  let kleene_nfa (nfa : nfa) : nfa = force_nfa (_kleene_nfa nfa)
  let kleene_dfa (dfa : dfa) : dfa = _kleene_nfa (force_nfa dfa)

  let multi_char_dfa (cs : CharSet.t) : dfa =
    let start = _default_init_state in
    let final = start + 1 in
    let next =
      CharSet.fold (fun c -> dfa_next_insert start c final) cs StateMap.empty
    in
    { start; finals = StateSet.singleton final; next }

  let multi_char_nfa (cs : CharSet.t) : nfa = force_nfa (multi_char_dfa cs)

  let multi_char_eps_nfa (cs : CharSet.t) : EpsFA.nfa =
    force_eps_nfa (multi_char_nfa cs)

  let filter_nfa_ (f : C.t -> bool) (nfa : nfa) =
    let next =
      nfa_fold_transitions
        (fun (s, c, d) next ->
          let res = f c in
          (* let () = Printf.printf "Keep: %s? %b\n" (C.layout c) res in *)
          if res then EpsFA.nfa_next_insert s (Some c) d next
          else EpsFA.nfa_next_insert s None d next)
        nfa StateMap.empty
    in
    let eps_nfa =
      ({ start = nfa.start; finals = nfa.finals; next } : EpsFA.nfa)
    in
    minimize @@ eps_determinize eps_nfa

  let filter_nfa (f : C.t -> bool) (nfa : nfa) = force_nfa (filter_nfa_ f nfa)
  let filter_dfa (f : C.t -> bool) (dfa : dfa) = filter_nfa_ f (force_nfa dfa)

  (** Regex*)

  let eps_lit_dfa =
    {
      start = _default_init_state;
      finals = StateSet.singleton _default_init_state;
      next = StateMap.empty;
    }

  let eps_lit_nfa : nfa = force_nfa eps_lit_dfa
  let eps_lit_eps_nfa : EpsFA.nfa = force_eps_nfa eps_lit_nfa

  let emp_lit_dfa : dfa =
    {
      start = _default_init_state;
      finals = StateSet.empty;
      next = StateMap.empty;
    }

  let rec compile_raw_regex_to_eps_nfa (r : raw_regex) : EpsFA.nfa option =
    let res =
      match r with
      | Empty -> None
      | Eps -> Some eps_lit_eps_nfa
      | MultiChar cs ->
          if CharSet.is_empty cs then None else Some (multi_char_eps_nfa cs)
      | Alt (r1, r2) -> (
          match
            (compile_raw_regex_to_eps_nfa r1, compile_raw_regex_to_eps_nfa r2)
          with
          | None, r2 -> r2
          | r1, None -> r1
          | Some r1, Some r2 -> Some (union_eps_nfa r1 r2))
      | Inters (r1, r2) -> (
          match
            (compile_raw_regex_to_eps_nfa r1, compile_raw_regex_to_eps_nfa r2)
          with
          | None, _ | _, None -> None
          | Some r1, Some r2 -> Some (intersect_eps_nfa r1 r2))
      | Comple (cs, r) -> (
          match compile_raw_regex_to_eps_nfa r with
          | None -> compile_raw_regex_to_eps_nfa (Star (MultiChar cs))
          | Some r -> Some (complement_eps_nfa cs r))
      | Seq [] -> None
      | Seq rs ->
          let rs' = List.filter_map compile_raw_regex_to_eps_nfa rs in
          if List.length rs' < List.length rs then None
          else Some (List.left_reduce [%here] concat_eps_nfa rs')
      | Star r -> (
          match compile_raw_regex_to_eps_nfa r with
          | None -> Some eps_lit_eps_nfa
          | Some r -> Some (kleene_eps_nfa r))
    in
    (* let () = Printf.printf "Compile %s to\n" (layout_raw_regex r) in *)
    (* let () = *)
    (*   Printf.printf "%s\n" *)
    (*     (match res with *)
    (*     | None -> "{}" *)
    (*     | Some res -> layout_dfa @@ eps_determinize res) *)
    (* in *)
    res

  let compile_raw_regex_to_dfa (r : raw_regex) : dfa =
    match compile_raw_regex_to_eps_nfa r with
    | None -> emp_lit_dfa
    | Some r -> eps_determinize r

  let rec seq_unfold = function
    | Seq l -> List.concat_map seq_unfold l
    | Eps -> []
    | _ as r -> [ r ]

  let seq l =
    let l = seq_unfold (Seq l) in
    if List.exists (function Empty -> true | _ -> false) l then Empty
    else match l with [] -> Eps | [ x ] -> x | _ -> Seq l

  let alt a b =
    match (a, b) with
    | Empty, _ -> b
    | _, Empty -> a
    | MultiChar c1, MultiChar c2 -> MultiChar (CharSet.union c1 c2)
    | _, _ -> Alt (a, b)

  let alt_list l = List.left_reduce [%here] alt (Empty :: l)
  let mk_repeat (n, r) = seq (List.init n (fun _ -> r))
  (* match n with *)
  (* | 0 ->  *)
  (* let rec aux (n, r) = *)
  (*   match n with *)
  (*   | 0 -> Eps *)
  (*   | 1 -> r *)
  (*   | _ when n > 1 -> seq r (aux (n - 1, r)) *)
  (*   | _ -> _die_with [%here] "invalid repeat" *)
  (* in *)
  (* aux (n, r) *)

  let regex_to_raw (regex : ('t, C.t) regex) : raw_regex =
    (* let regex = Regex.to_nnf regex in *)
    let rec aux (regex : ('t, C.t) regex) : raw_regex =
      match regex with
      | Extension _ | SyntaxSugar _ | RExpr _ -> failwith "die"
      | LandA (r1, r2) -> Inters (aux r1, aux r2)
      | DComplementA { atoms; body } -> Comple (CharSet.of_list atoms, aux body)
      | RepeatN (n, r) -> mk_repeat (n, aux r)
      | MultiAtomic l -> MultiChar (CharSet.of_list l)
      | EmptyA -> Empty
      | EpsilonA -> Eps
      | Atomic c -> MultiChar (CharSet.singleton c)
      | LorA (r1, r2) -> Alt (aux r1, aux r2)
      | SeqA rs -> Seq (List.map aux rs)
      | StarA r -> Star (aux r)
    in
    let res = aux regex in
    (* let () = Printf.printf "\t\tregex: %s\n" (layout_raw_regex res) in *)
    res

  let compile_regex_to_dfa (r : ('t, C.t) regex) : dfa =
    compile_raw_regex_to_dfa @@ regex_to_raw r

  (** automata to regex *)

  type regex_lit =
    | EqEps
    | EqEmp
    | EqChar of CharSet.t
    | EqVar of int
    | EqSeq of (regex_lit * regex_lit)
    | EqOr of regex_lit list
    | EqStar of regex_lit

  let rec layout_regex_lit = function
    | EqEps -> layout_raw_regex Eps
    | EqEmp -> layout_raw_regex Empty
    | EqChar r -> layout_raw_regex (MultiChar r)
    | EqVar x -> string_of_int x
    | EqSeq (x, y) -> spf "%s %s" (layout_regex_lit x) (layout_regex_lit y)
    | EqOr l -> List.split_by " + " layout_regex_lit l
    | EqStar x -> spf "(%s)*" (layout_regex_lit x)

  (* let smart_eq_or a b= *)
  (*   match (a, b) with *)
  (*   | EqEmp, _ -> b *)
  (*   | _, EqEmp -> a *)
  (*   | _, _ -> EqOr (a, b) *)

  let mk_equation s ss_next =
    let m = StateMap.filter_map (fun _ -> StateMap.find_opt s) ss_next in
    let eq =
      StateMap.fold (fun s' cs eq -> EqSeq (EqChar cs, EqVar s') :: eq) m []
    in
    (StateMap.mem s m, eq)

  let layout_equations l =
    List.iter
      (fun (s, eq) -> Printf.printf "%i := %s" s (layout_regex_lit eq))
      l

  let mk_equations (dfa : dfa) =
    let ss_next = dfa_next_to_ss_next dfa in
    let l =
      dfa_fold_states
        (fun s l ->
          let _, eq = mk_equation s ss_next in
          let eq = if s == dfa.start then EqOr (EqEps :: eq) else EqOr eq in
          (s, eq) :: l)
        dfa []
    in
    let () = layout_equations l in
    ()

  let del_in_ss_next s ss_next =
    let self_m =
      match StateMap.find_opt s ss_next with
      | None -> _die [%here]
      | Some m -> m
    in
    let self_char =
      match StateMap.find_opt s self_m with None -> Eps | Some c -> Star c
    in
    let smart_update s r =
      StateMap.update s (function None -> Some r | Some r' -> Some (alt r r'))
    in
    let ss_next =
      StateMap.map
        (fun m ->
          StateMap.fold
            (fun s' r' m' ->
              if s != s' then smart_update s' r' m'
              else
                StateMap.fold
                  (fun s'' r'' -> smart_update s'' (seq [ r'; self_char; r'' ]))
                  self_m m')
            m StateMap.empty)
        ss_next
    in
    ss_next

  let print_ss_next ss_next =
    StateMap.iter
      (fun s ->
        StateMap.iter (fun s' r ->
            Printf.printf "%i --[%s]--> %i\n" s (layout_raw_regex r) s'))
      ss_next

  let dfa_to_reg (dfa : dfa) =
    let dfa = normalize_dfa dfa in
    if StateSet.cardinal dfa.finals == 0 then Empty
    else
      let n = num_states_dfa dfa in
      let ss_next = dfa_next_to_ss_next dfa in
      let new_start = n in
      let new_final = n + 1 in
      let ss_next =
        StateMap.map (StateMap.map (fun cs -> MultiChar cs)) ss_next
      in
      let ss_next =
        StateMap.add new_start (StateMap.singleton dfa.start Eps) ss_next
      in
      let ss_next =
        StateSet.fold
          (fun s ->
            StateMap.update s (function
              | None -> Some (StateMap.singleton new_final Eps)
              | Some m -> Some (StateMap.add new_final Eps m)))
          dfa.finals ss_next
      in
      (* let () = print_ss_next ss_next in *)
      let rec loop i ss_next =
        (* let () = Printf.printf "Work on %i\n" i in *)
        (* let () = print_ss_next ss_next in *)
        if i == n then ss_next else loop (i + 1) (del_in_ss_next i ss_next)
      in
      let ss_next = loop 0 ss_next in
      let res =
        match StateMap.find_opt new_start ss_next with
        | None -> _die [%here]
        | Some m -> (
            match StateMap.find_opt new_final m with
            | None -> _die [%here]
            | Some r -> r)
      in
      res

  let raw_regex_to_union_normal_form f (regex : raw_regex) =
    let rec aux regex =
      match regex with
      | Empty | Inters _ | Comple _ ->
          let () =
            Printf.printf "(%s) should be optimized\n" (layout_raw_regex regex)
          in
          _die [%here]
      | Eps -> [ [] ]
      | MultiChar c -> [ List.map (fun c -> MultiChar c) (f c) ]
      | Alt (c1, c2) -> aux c1 @ aux c2
      | Seq l ->
          List.fold_right
            (fun choices res ->
              List.map (fun (x, y) -> x @ y) @@ List.cross (aux choices) res)
            l [ [] ]
          (* let l = List.map aux l in *)
          (* let l = List.map List.concat @@ List.onchoose_list_list l in *)
          (* l *)
      | Star r -> [ [ Star r ] ]
    in
    aux regex

  let union_normal_form_to_raw_regex ll =
    List.left_reduce [%here] alt @@ List.map (fun l -> Seq l) ll

  let omit_layout_symbolic_trace rs =
    List.split_by "; "
      (function Star _ -> "□*" | _ as r -> layout_raw_regex r)
      rs

  let layout_symbolic_trace rs = List.split_by "; " layout_raw_regex rs

  let layout_union_normal_form rs =
    let rs = List.mapi (fun i s -> (i, s)) rs in
    List.split_by "\n\n"
      (fun (i, tr) -> spf "[%i]: %s" i (layout_symbolic_trace tr))
      rs

  let is_empty_raw_regex = function Empty -> true | _ -> false

  let raw_reg_map f reg =
    let rec aux = function
      | Empty -> Empty
      | Eps -> Eps
      | MultiChar cs -> MultiChar (f cs)
      | Alt (r1, r2) -> Alt (aux r1, aux r2)
      | Inters (r1, r2) -> Inters (aux r1, aux r2)
      | Comple (cs, r2) -> Comple (f cs, aux r2)
      | Seq rs -> Seq (List.map aux rs)
      | Star r -> Star (aux r)
    in
    aux reg
end
