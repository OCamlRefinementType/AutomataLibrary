open Zutils
open Zdatatype
open Character

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
