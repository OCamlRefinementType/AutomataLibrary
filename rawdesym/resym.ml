(* open Sugar *)
open Zdatatype
open Fa
open Common
open SFA

let resym_se { desym_map; event_tyctx; _ } (op, i) =
  let ftab = StrMap.find "never" desym_map.local_int2lit op in
  let vs = StrMap.find "never" event_tyctx op in
  let bl = IntBinary.int_to_bin (IntMap.cardinal ftab, i) in
  let phi = Satcheck.blist_to_prop bl ftab in
  { op; vs; phi }

let resym_chars ctx cs =
  DesymFA.CharSet.fold (fun c -> CharSet.add (resym_se ctx c)) cs CharSet.empty

let resym_regex ctx =
  let rec aux r =
    match r with
    | Empty -> Empty
    | Eps -> Eps
    | MultiChar cs ->
        let cs = resym_chars ctx cs in
        if CharSet.is_empty cs then Empty else MultiChar cs
    | Alt (r1, r2) -> smart_alt (aux r1) (aux r2)
    | Inters (r1, r2) -> smart_alt (aux r1) (aux r2)
    | Seq rs -> DesymFA.smart_seq (List.map aux rs)
    | Comple (cs, r) ->
        let cs = resym_chars ctx cs in
        Comple (cs, aux r)
    | Star r -> smart_star @@ aux r
  in
  aux
