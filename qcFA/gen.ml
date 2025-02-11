open Sfa
open Zutils
open CharAutomata
open QCheck.Gen

let space_list = [ 'a'; 'b'; 'c'; 'd' ]
let space = CharSet.of_list space_list

open Zdatatype

let rec n2set (l : 'a list) n =
  let res =
    match (l, n) with
    | [], 0 -> []
    | [], _ -> _die [%here]
    | x :: l, _ -> if n mod 2 == 0 then n2set l (n / 2) else x :: n2set l (n / 2)
  in
  (* let () = *)
  (*   Printf.printf "n2set (%s) %i = %s\n" *)
  (*     (List.split_by_comma (spf "%c") l) *)
  (*     n *)
  (*     (List.split_by_comma (spf "%c") res) *)
  (* in *)
  res

let list_nonempty_subset_gen (space : 'a list) =
  let total = pow 2 (List.length space) in
  map (fun n -> n2set space n) @@ int_range 1 (total - 1)

let nonempty_subset_gen =
  map CharSet.of_list (list_nonempty_subset_gen space_list)

let regex_ternimal_gen =
  frequency
    [
      (1, pure Empty);
      (1, pure Eps);
      (2, map (fun x -> MultiChar x) nonempty_subset_gen);
    ]

let regex_one_arg_gen g =
  frequency
    [
      (1, map (fun x -> Star x) g);
      (* (1, map2 (fun s x -> Comple (s, x)) nonempty_subset_gen g); *)
      (1, map (fun x -> Comple (space, x)) g);
    ]

let regex_two_arg_gen g1 g2 =
  frequency
    [
      (1, map2 (fun r1 r2 -> Alt (r1, r2)) g1 g2);
      (1, map2 (fun r1 r2 -> Seq [ r1; r2 ]) g1 g2);
      (1, map2 (fun r1 r2 -> Inters (r1, r2)) g1 g2);
    ]

let basic_regex_gen =
  sized_size (int_bound 8)
  @@ fix (fun self n ->
         match n with
         | 0 -> map (fun x -> MultiChar x) nonempty_subset_gen
         | _ ->
             frequency
               [
                 (1, map (fun x -> MultiChar x) nonempty_subset_gen);
                 (1, map (fun x -> Star x) @@ self (n - 1));
                 ( 1,
                   map2
                     (fun r1 r2 -> Alt (r1, r2))
                     (self (n / 2))
                     (self (n / 2)) );
                 ( 1,
                   map2
                     (fun r1 r2 -> Seq [ r1; r2 ])
                     (self (n / 2))
                     (self (n / 2)) );
               ])

let regex_gen =
  sized_size (int_bound 8)
  @@ fix (fun self n ->
         match n with
         | 0 -> regex_ternimal_gen
         | _ ->
             frequency
               [
                 (1, regex_ternimal_gen);
                 (3, regex_one_arg_gen @@ self (n - 1));
                 (4, regex_two_arg_gen (self (n / 2)) (self (n / 2)));
               ])

let string_gen = list (oneofl space_list)

let string_gen_from_regex (r : CharSet.t regex) =
  let rec aux r =
    match r with
    | Empty -> pure None
    | Eps -> pure (Some [])
    | MultiChar l -> (
        match List.of_seq @@ CharSet.to_seq l with
        | [] -> pure None
        | l -> map (fun c -> Some [ c ]) (oneofl l))
    | Alt (r1, r2) -> frequency [ (1, aux r1); (1, aux r2) ]
    | Seq rs ->
        let f r1 r2 =
          map2
            (fun r1 r2 ->
              match (r1, r2) with
              | Some r1, Some r2 -> Some (r1 @ r2)
              | _, _ -> None)
            r1 r2
        in
        List.left_reduce [%here] f @@ List.map aux rs
    | Star r ->
        frequency
          [
            (1, pure None);
            (1, aux r);
            (1, aux (Seq [ r; r ]));
            (1, aux (Seq [ r; r; r ]));
          ]
    | Inters _ | Comple _ -> _die [%here]
  in
  aux r

let string_gen_from_regex_random (r : CharSet.t regex) =
  map (fun l ->
      if is_match (fun a b -> C.compare a b == 0) r l then (true, l)
      else (false, l))
  @@ sized_size (int_bound 10)
  @@ fix (fun self n ->
         match n with
         | 0 -> pure []
         | _ -> map2 (fun hd tl -> hd :: tl) (oneofl space_list) (self (n - 1)))
