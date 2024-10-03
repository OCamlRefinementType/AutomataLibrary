type state = int

module StateSet = Set.Make (Int)
module StateMap = Map.Make (Int)

module type CHARAC = sig
  include Map.OrderedType

  val layout : t -> string
  val delimit_cotexnt_char : t list option * t -> t list
end

module type CHARACTER = sig
  include CHARAC

  type char_idx

  val layout : t -> string
  val init_char_map : unit -> char_idx
  val add_char_to_map : char_idx -> t -> unit
  val id2c : char_idx -> Int64.t -> t
  val c2id : char_idx -> t -> Int64.t
end

module type FINITE_AUTOMATA = sig
  module C : CHARACTER
  module CharMap : Map.S with type key = C.t
  module CharSet : Set.S with type elt = C.t

  type transitions = StateSet.t CharMap.t
  type d_transition = state CharMap.t

  type raw_regex =
    | Empty : raw_regex (* L = { } *)
    | Eps : raw_regex (* L = {ε} *)
    | MultiChar : CharSet.t -> raw_regex
    | Alt : raw_regex * raw_regex -> raw_regex
    | Inters : raw_regex * raw_regex -> raw_regex
    | Comple : CharSet.t * raw_regex -> raw_regex
    | Seq : raw_regex list -> raw_regex
    | Star : raw_regex -> raw_regex

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

let _default_init_state = 0

open Zdatatype

let layout_states f s =
  List.split_by_comma f @@ List.of_seq @@ StateSet.to_seq s

module MakeC (C : CHARAC) = struct
  open C

  type char_idx = {
    __id2c : (Int64.t, t) Hashtbl.t;
    __c2id : (t, Int64.t) Hashtbl.t;
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

  let add_char_to_map { __counter; __c2id; __id2c } (c : t) =
    match Hashtbl.find_opt __c2id c with
    | None ->
        let id = __incr __counter in
        Hashtbl.add __c2id c id;
        Hashtbl.add __id2c id c
    | Some _ -> ()

  let id2c { __id2c; _ } = Hashtbl.find __id2c
  let c2id { __c2id; _ } = Hashtbl.find __c2id

  include C
end
