open Sugar
open Prop
open Zdatatype
open Fa
open Common
open SFA

let align_map (lit2int, barray) = LitMap.map (fun i -> barray.(i)) lit2int

let desym_eval_lit m lit =
  match LitMap.find_opt lit m with
  | None ->
      let () =
        LitMap.iter (fun l b -> Printf.printf "%s ==> %b\n" (layout_lit l) b) m
      in
      _failatwith [%here]
        (spf "cannot find assignment of lit(%s)" (layout_lit lit))
  | Some b -> b

let desym_eval_prop m =
  let rec aux = function
    | Lit { x = AC (B b); _ } -> b
    | Lit lit -> desym_eval_lit m lit.x
    | Implies (a, b) -> (not (aux a)) || aux b
    | Ite (a, b, c) -> if aux a then aux b else aux c
    | Not a -> not (aux a)
    | And es -> List.for_all aux es
    | Or es -> List.exists aux es
    | Iff (a, b) -> aux (Implies (a, b)) && aux (Implies (b, a))
    | Forall _ | Exists _ -> _die [%here]
  in
  aux

let desym_eval_se desym_map { global_fact; local_fact } { op; phi; _ } =
  let global_m =
    align_map (desym_map.global_lit2int, Array.of_list global_fact)
  in
  let local_fact_set = StrMap.find "never" local_fact op in
  let local_lit2int = StrMap.find "never" desym_map.local_lit2int op in
  let local_fact_set =
    BlistSet.filter
      (fun local_fact ->
        let local_m = align_map (local_lit2int, Array.of_list local_fact) in
        let m = LitMap.union (fun _ _ _ -> _die [%here]) global_m local_m in
        desym_eval_prop m phi)
      local_fact_set
  in
  let local_id_set =
    BlistSet.fold
      (fun bl -> DesymFA.CharSet.add (op, snd @@ IntBinary.bin_to_int bl))
      local_fact_set DesymFA.CharSet.empty
  in
  local_id_set

let desym_eval_chars desym_map fact cs =
  CharSet.fold
    (fun c -> DesymFA.CharSet.union (desym_eval_se desym_map fact c))
    cs DesymFA.CharSet.empty

let desym_eval_regex desym_map fact =
  let rec aux r =
    match r with
    | Empty -> Empty
    | Eps -> Eps
    | MultiChar cs ->
        let cs = desym_eval_chars desym_map fact cs in
        if DesymFA.CharSet.is_empty cs then Empty else MultiChar cs
    | Alt (r1, r2) -> DesymFA.smart_alt (aux r1) (aux r2)
    | Inters (r1, r2) -> DesymFA.smart_alt (aux r1) (aux r2)
    | Seq rs -> DesymFA.smart_seq (List.map aux rs)
    | Comple (cs, r) ->
        let cs = desym_eval_chars desym_map fact cs in
        Comple (cs, aux r)
    | Star r -> smart_star @@ aux r
  in
  aux
