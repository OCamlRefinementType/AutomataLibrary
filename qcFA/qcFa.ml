open Gen
open Sfa

(* open Zutils *)
open CharAutomata

type fa = DFA of dfa | NFA of nfa | REGEX of (string * Str.regexp)

let string_of_charlist str = String.of_seq @@ List.to_seq str

let accept (fa : fa) (str : C.t list) =
  match fa with
  | DFA dfa -> dfa_accept dfa str
  | NFA nfa -> nfa_accept nfa str
  | REGEX (_, r) -> Str.string_match r (string_of_charlist str) 0

let layout (fa : fa) =
  match fa with
  | DFA dfa -> layout_dfa dfa
  | NFA nfa -> layout_nfa nfa
  | REGEX (r, _) -> r ^ "\n"

let test_regex_fa_3 (times : int) (regex : CharSet.t regex) =
  let fa = DFA (compile_regex_to_dfa regex) in
  let strs =
    QCheck.Gen.generate ~n:times (string_gen_from_regex_random regex)
  in
  let total = List.length strs in
  let () = Printf.printf "generated %i cases under %i times\n" total times in
  List.fold_left
    (fun res (b, str) ->
      res
      &&
      let b' = accept fa str in
      if b != b' then
        let () = Printf.printf "For regex:\n%s\n" (layout_regex regex) in
        let () = Printf.printf "error: %s\n" (string_of_charlist str) in
        let () = Printf.printf "fa says: %b, but should be %b\n" b' b in
        let () = Printf.printf "fa:\n%s\n" (layout fa) in
        false
      else true)
    true strs

let test_regex_fa (times : int) (regex : CharSet.t regex) =
  let fa = DFA (compile_regex_to_dfa regex) in
  let strs =
    List.filter_map (fun n -> n)
    @@ QCheck.Gen.generate ~n:times (string_gen_from_regex regex)
  in
  let total = List.length strs in
  let () = Printf.printf "generated %i cases under %i times\n" total times in
  List.fold_left
    (fun res str ->
      res
      &&
      if not (accept fa str) then
        let () = Printf.printf "For regex:\n%s\n" (layout_regex regex) in
        let () = Printf.printf "error: %s\n" (string_of_charlist str) in
        false
      else true)
    true strs

let test_fa_1 (f : bool -> bool -> bool) (times : int) (fa1 : fa) (fa2 : fa) =
  let strs = QCheck.Gen.generate ~n:times string_gen in
  List.fold_left
    (fun res str ->
      res
      &&
      let b1 = accept fa1 str in
      let b2 = accept fa2 str in
      if not (f b1 b2) then
        let () = Printf.printf "error: %s\n" (string_of_charlist str) in
        let () = Printf.printf "[f1 accept: %b]\n%s\n" b1 (layout fa1) in
        let () = Printf.printf "[f2 accept: %b]\n%s\n" b2 (layout fa2) in
        false
      else true)
    true strs

let test_fa_2 (f : bool -> bool -> bool -> bool) (times : int) (fa1 : fa)
    (fa2 : fa) (fa3 : fa) =
  let strs = QCheck.Gen.generate ~n:times string_gen in
  List.fold_left
    (fun res str ->
      res
      &&
      let b1 = accept fa1 str in
      let b2 = accept fa2 str in
      let b3 = accept fa3 str in
      if not (f b1 b2 b3) then
        let () = Printf.printf "error: %s\n" (string_of_charlist str) in
        let () = Printf.printf "fa1 accept: %b\n" b1 in
        let () = Printf.printf "fa2 accept: %b\n" b2 in
        let () = Printf.printf "fa3 accept: %b\n" b3 in
        false
      else true)
    true strs

let test_fa_equal = test_fa_1 ( == )
let test_fa_complement = test_fa_1 ( != )
let test_fa_intersection = test_fa_2 (fun a b c -> c == (a && b))
let test_fa_union = test_fa_2 (fun a b c -> c == (a || b))

let qc_test_compile_regex_to_dfa_1 (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  List.fold_left
    (fun res r ->
      res
      &&
      let () = Printf.printf "testing %s\n" (layout_regex r) in
      if test_regex_fa times r then true
      else
        let () = Printf.printf "testing %s\n" (layout_regex r) in
        false)
    true regexs

let qc_test_compile_regex_to_dfa_3 (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  List.fold_left
    (fun res r ->
      res
      &&
      let () = Printf.printf "testing %s\n" (layout_regex r) in
      if test_regex_fa_3 times r then true
      else
        let () = Printf.printf "testing %s\n" (layout_regex r) in
        false)
    true regexs

let qc_test_compile_regex_to_dfa_2 (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  List.fold_left
    (fun res r ->
      res
      &&
      let () = Printf.printf "testing %s\n" (layout_regex r) in
      let fa = DFA (compile_regex_to_dfa r) in
      let r' = REGEX (layout_regex r, Str.regexp (regex_to_str_regex r)) in
      let b = test_fa_equal times r' fa in
      if not b then Printf.printf "Error: %s != ?\n" (layout_regex r);
      b)
    true regexs

let qc_test_fa_equal_trans f (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  List.fold_left
    (fun res r ->
      res
      &&
      let () = Printf.printf "testing %s\n" (layout_regex r) in
      let dfa = compile_regex_to_dfa r in
      let fa1 = DFA dfa in
      let fa2 = DFA (f dfa) in
      test_fa_equal times fa1 fa2)
    true regexs

let qc_test_fa_minimalize = qc_test_fa_equal_trans minimize
let qc_test_fa_normalize = qc_test_fa_equal_trans normalize_dfa
let qc_test_fa_complete = qc_test_fa_equal_trans (complete_dfa space)

let qc_test_fa_complement (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  List.fold_left
    (fun res r ->
      res
      &&
      let () = Printf.printf "testing %s\n" (layout_regex r) in
      let dfa = compile_regex_to_dfa r in
      let fa1 = DFA dfa in
      let fa2 = DFA (complement_dfa space dfa) in
      test_fa_complement times fa1 fa2)
    true regexs

let qc_test_compile_complement_2 (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  let regexs = List.map (fun r -> Comple (space, r)) regexs in
  List.fold_left
    (fun res r ->
      res
      &&
      let () = Printf.printf "testing %s\n" (layout_regex r) in
      let fa = DFA (compile_regex_to_dfa r) in
      let r' =
        REGEX (regex_to_str_regex r, Str.regexp (regex_to_str_regex r))
      in
      let b = test_fa_equal times r' fa in
      if not b then Printf.printf "Error: %s != ?\n" (layout_regex r);
      b)
    true regexs

let qc_test_fa_intersection (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  let rec aux = function
    | [] | [ _ ] -> true
    | r1 :: r2 :: rs ->
        let () =
          Printf.printf "testing %s and %s \n" (layout_regex r1)
            (layout_regex r2)
        in
        let dfa1 = compile_regex_to_dfa r1 in
        let dfa2 = compile_regex_to_dfa r2 in
        let dfa3 = intersect_dfa dfa1 dfa2 in
        if test_fa_intersection times (DFA dfa1) (DFA dfa2) (DFA dfa3) then
          aux rs
        else false
  in
  aux regexs

let qc_test_fa_union (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  let rec aux = function
    | [] | [ _ ] -> true
    | r1 :: r2 :: rs ->
        let () =
          Printf.printf "testing %s and %s \n" (layout_regex r1)
            (layout_regex r2)
        in
        let dfa1 = compile_regex_to_dfa r1 in
        let dfa2 = compile_regex_to_dfa r2 in
        let dfa3 = union_dfa dfa1 dfa2 in
        if test_fa_union times (DFA dfa1) (DFA dfa2) (DFA dfa3) then aux rs
        else false
  in
  aux regexs

let qc_test_dfa_to_regex (num_regex : int) (times : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  let rec loop rs =
    match rs with
    | [] -> true
    | r :: rs ->
        let dfa = compile_regex_to_dfa r in
        let r' = dfa_to_reg (minimize dfa) in
        let dfa' = compile_regex_to_dfa r' in
        let () = Printf.printf "r: %s\n" (layout_regex r) in
        let () = Printf.printf "r': %s\n" (layout_regex r') in
        if test_fa_equal times (DFA dfa) (DFA dfa') then loop rs else false
  in
  loop regexs

let check_emp (dfa : dfa) = StateSet.is_empty (minimize dfa).finals

let check_eq (dfa1 : dfa) (dfa2 : dfa) =
  let dfa1' = complement_dfa space dfa1 in
  let dfa2' = complement_dfa space dfa2 in
  check_emp (intersect_dfa dfa1 dfa2') && check_emp (intersect_dfa dfa1' dfa2)

let check_eq_regex (r1 : CharSet.t regex) (r2 : CharSet.t regex) =
  check_eq (compile_regex_to_dfa r1) (compile_regex_to_dfa r2)

let qc_test_dfa_to_regex_2 (num_regex : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  let rec loop rs =
    match rs with
    | [] -> true
    | r :: rs ->
        let dfa = compile_regex_to_dfa r in
        let r' = dfa_to_reg (minimize dfa) in
        let dfa' = compile_regex_to_dfa r' in
        let () = Printf.printf "r: %s\n" (layout_regex r) in
        let () = Printf.printf "r': %s\n" (layout_regex r') in
        if check_eq dfa dfa' then loop rs else false
  in
  loop regexs

let qc_test_dfa_to_unf_2 (num_regex : int) =
  let regexs = QCheck.Gen.generate ~n:num_regex regex_gen in
  let rec loop rs =
    match rs with
    | [] -> true
    | r :: rs ->
        let r' =
          union_normal_form_to_regex
          @@ regex_to_union_normal_form (fun c -> [ c ]) r
        in
        let () = Printf.printf "r: %s\n" (layout_regex r) in
        let () = Printf.printf "r': %s\n" (layout_regex r') in
        if check_eq_regex r r' then loop rs else false
  in
  loop regexs

(* let%test _ = qc_test_dfa_to_regex 1000 100 *)
(* let%test _ = qc_test_dfa_to_unf_2 200 *)
(* let%test _ = qc_test_dfa_to_regex_2 100 *)

(* let%test _ = qc_test_compile_complement_2 10 30 *)
(* let%test _ = qc_test_fa_complement 10 30 *)
let%test _ = qc_test_compile_regex_to_dfa_3 200 30
(* let%test _ = *)
(*   let r = *)
(*     Seq *)
(*       [ *)
(*         Comple *)
(*           (space, Seq [ Eps; MultiChar (CharSet.of_list [ 'a'; 'b'; 'd' ]) ]); *)
(*         Inters (MultiChar (CharSet.of_list [ 'b'; 'c' ]), Eps); *)
(*         MultiChar (CharSet.of_list [ 'b'; 'd' ]); *)
(*       ] *)
(*   in *)
(*   let () = Printf.printf "r: %s\n" @@ layout_regex r in *)
(*   let fa = DFA (compile_regex_to_dfa r) in *)
(*   let () = Printf.printf "fa:\n%s\n" (layout fa) in *)
(*   let str = List.of_seq @@ String.to_seq "bdbdbbbccd" in *)
(*   let () = Printf.printf "r match: %b\n" (is_match Char.equal r str) in *)
(*   let () = Printf.printf "fa accept: %b\n" (accept fa str) in *)
(*   test_regex_fa_3 10000 r *)

(* let%test _ = *)
(*   let dfa = compile_regex_to_dfa (Seq [Mul]) in *)

open Sgen
open Prop
open SFA

let _do_test r =
  let fa = compile_regex_to_dfa r in
  let r' = dfa_to_reg fa in
  let fa = dfa_realize (fun { phi; _ } -> Prover.check_sat_bool phi) fa in
  (* let () = Printf.printf "fa:\n%s\n\n" (layout_dfa fa) in *)
  let fa = normalize_dfa fa in
  (* let () = Printf.printf "fa:\n%s\n\n" (layout_dfa fa) in *)
  (* let () = failwith "end" in *)
  let r'' = dfa_to_reg fa in
  let () = Printf.printf "original:\n%s\n" (layout_regex r) in
  let () = Printf.printf "minimalize:\n%s\n" (layout_regex r') in
  let () = Printf.printf "realize:\n%s\n\n" (layout_regex r'') in
  ()

let testcase () =
  let regexs = QCheck.Gen.generate ~n:10 regex_gen in
  let () = List.iter _do_test regexs in
  false

let testcase1 () =
  let r =
    star
      (MultiChar
         (CharSet.of_list
            [ op_phi_to_se "a" mk_false; op_phi_to_se "a" mk_true ]))
  in
  let regexs = [ r ] in
  let () = List.iter _do_test regexs in
  false

let testcase2 () =
  let r = MultiChar (CharSet.of_list [ op_phi_to_se "a" mk_false ]) in
  let regexs = [ r ] in
  let () = List.iter _do_test regexs in
  false
