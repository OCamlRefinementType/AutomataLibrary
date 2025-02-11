open Zutils

type state = int

module StateSet = Set.Make (Int)
module Int64Set = Set.Make (Int64)
module StateMap = Map.Make (Int)

module type CHARAC = sig
  include Map.OrderedType

  val layout : t -> string
  val char_union : t -> t -> t option
  val char_inter : t -> t -> t option
  val char_subtract : t -> t -> t option
  val get_name : t -> string
  (* val delimit_cotexnt_char : t list option * t -> t list *)
end

module type ALPHABET = sig
  module C : CHARAC
  module CharMap : Map.S with type key = C.t
  module CharSet : Set.S with type elt = C.t
  include CHARAC

  type char_idx

  val init_char_map : unit -> char_idx
  val add_char_to_map : char_idx -> C.t -> unit
  val id2c : char_idx -> Int64.t -> C.t
  val c2id : char_idx -> C.t -> Int64.t
  val char_union_to_set : C.t -> CharSet.t -> CharSet.t
  val compact_set : CharSet.t -> CharSet.t
  val subtract_set : CharSet.t -> CharSet.t -> CharSet.t
end

let _default_init_state = 0

open Zdatatype

let layout_states f s =
  List.split_by_comma f @@ List.of_seq @@ StateSet.to_seq s

module MakeAlphabet (C : CHARAC) = struct
  module C = C
  module CharMap = Map.Make (C)
  module CharSet = Set.Make (C)
  include C

  type char_idx = {
    __id2c : (Int64.t, C.t) Hashtbl.t;
    __c2id : (C.t, Int64.t) Hashtbl.t;
    __counter : Int64.t ref;
  }

  let __incr __counter =
    let res = !__counter in
    __counter := Int64.add res 1L;
    res

  let init_char_map () : char_idx =
    {
      __counter = ref 0L;
      __c2id = Hashtbl.create 1000;
      __id2c = Hashtbl.create 1000;
    }

  let add_char_to_map { __counter; __c2id; __id2c } (c : C.t) =
    match Hashtbl.find_opt __c2id c with
    | None ->
        let id = __incr __counter in
        Hashtbl.add __c2id c id;
        Hashtbl.add __id2c id c
    | Some _ -> ()

  let id2c { __id2c; _ } = Hashtbl.find __id2c
  let c2id { __c2id; _ } = Hashtbl.find __c2id

  let _force_char_union c1 c2 =
    match C.char_union c1 c2 with
    | None -> _failatwith [%here] "die"
    | Some c -> c

  let _update (c : C.t) =
    StrMap.update (C.get_name c) (function
      | None -> Some c
      | Some c' -> Some (_force_char_union c' c))

  let compact_set (s : CharSet.t) =
    let m = CharSet.fold _update s StrMap.empty in
    StrMap.fold (fun _ -> CharSet.add) m CharSet.empty

  let char_union_to_set (c : C.t) (s : CharSet.t) =
    let m = CharSet.fold _update s StrMap.empty in
    let m = _update c m in
    StrMap.fold (fun _ -> CharSet.add) m CharSet.empty

  let char_subtract_char_from_set (c : C.t) (s : CharSet.t) =
    CharSet.filter_map (fun c' -> C.char_subtract c' c) s

  let subtract_set (s1 : CharSet.t) (s2 : CharSet.t) =
    CharSet.fold char_subtract_char_from_set s2 s1
end

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

module CharC = struct
  include Char

  let layout x = spf "%c" x
  let get_name = layout
  let char_union c1 c2 = if Char.equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if Char.equal c1 c2 then None else Some c1
end

module StringC = struct
  include String

  let layout x = x
  let get_name = layout
  let char_union c1 c2 = if String.equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if String.equal c1 c2 then None else Some c1
end

module Int64C = struct
  include Int64

  let layout = to_string
  let get_name = layout
  let char_union c1 c2 = if Int64.equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if Int64.equal c1 c2 then None else Some c1
end

module DesymLabel = struct
  type t = string * int [@@deriving eq, ord]

  let layout (op, id) = op ^ ":" ^ string_of_int id
  let get_name = layout
  let char_union c1 c2 = if equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if equal c1 c2 then None else Some c1
end

open Sv
open To_sevent

module SymLabel = struct
  type t = Nt.nt sevent [@@deriving eq, ord]

  let layout se = layout_se se
  let get_name se = se.op

  let char_union se1 se2 =
    let open Prop in
    if String.equal se1.op se2.op then
      Some { se1 with phi = smart_or [ se1.phi; se2.phi ] }
    else None

  let char_inter se1 se2 =
    let open Prop in
    if String.equal se1.op se2.op then
      Some { se1 with phi = smart_and [ se1.phi; se2.phi ] }
    else None

  let char_subtract se1 se2 =
    let open Prop in
    if String.equal se1.op se2.op then
      Some { se1 with phi = smart_add_to se1.phi (smart_not se2.phi) }
    else Some se1
end
