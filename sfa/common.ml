open Zutils
open Language

type state = int

module StateSet = Set.Make (Int)
module Int64Set = Set.Make (Int64)
module StateMap = Map.Make (Int)

let _default_init_state = 0

open Zdatatype

let layout_states f s =
  List.split_by_comma f @@ List.of_seq @@ StateSet.to_seq s

module MakeEpsC (C : CHARAC) = struct
  type t = CEps | CC of C.t [@@deriving ord]

  let _nop = "_______eps"
  let layout = function CEps -> "eps" | CC c -> C.layout c
  let get_name = function CEps -> _nop | CC c -> C.get_name c

  let char_union se1 se2 =
    match (se1, se2) with
    | CEps, CEps -> Some CEps
    | CC c1, CC c2 ->
        let* c = C.char_union c1 c2 in
        Some (CC c)
    | _, _ -> None

  let char_inter se1 se2 =
    match (se1, se2) with
    | CEps, CEps -> Some CEps
    | CC c1, CC c2 ->
        let* c = C.char_inter c1 c2 in
        Some (CC c)
    | _, _ -> None

  let char_subtract c1 c2 =
    match (c1, c2) with
    | CC c1, CC c2 ->
        let* c = C.char_subtract c1 c2 in
        Some (CC c)
    | _, _ -> None
end
