type state = int

let _default_init_state = 0

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
