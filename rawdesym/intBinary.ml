open Sugar

let int_to_bool x = if x == 1 then true else false

let rec int_to_bin (n, x) =
  match (n, x) with
  | 0, 0 -> []
  | 0, _ -> _die [%here]
  | _, _ ->
      let n = n - 1 in
      let r = int_to_bool (x mod 2) in
      let x = x / 2 in
      r :: int_to_bin (n, x)

let bool_to_int b = if b then 1 else 0

let rec bin_to_int l =
  match l with
  | [] -> (0, 0)
  | h :: l ->
      let n, x = bin_to_int l in
      (n + 1, bool_to_int h + (2 * x))

let%test "t1" =
  let len = 5 in
  let test_cases = List.init (pow 2 len) (fun x -> x) in
  List.for_all
    (fun i ->
      let len', i' = bin_to_int @@ int_to_bin (len, i) in
      len == len' && i == i')
    test_cases

let%test "t2" =
  let len = 5 in
  let rec f n =
    match n with
    | 0 -> [ [] ]
    | _ -> List.concat_map (fun c -> [ true :: c; false :: c ]) @@ f (n - 1)
  in
  let test_cases = f len in
  List.for_all
    (fun l ->
      let l' = int_to_bin @@ bin_to_int l in
      List.equal Bool.equal l l')
    test_cases
