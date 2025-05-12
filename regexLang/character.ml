open Zutils
open RegexAst

module type CHARAC = sig
  include Map.OrderedType

  val layout : t -> string
  val display : t -> string
  val char_union : t -> t -> t option
  val char_inter : t -> t -> t option
  val char_subtract : t -> t -> t option
  val get_name : t -> string
  (* val delimit_cotexnt_char : t list option * t -> t list *)
end

module CharC = struct
  include Char

  let layout x = spf "%c" x
  let display = layout
  let get_name = layout
  let char_union c1 c2 = if Char.equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if Char.equal c1 c2 then None else Some c1
end

module StringC = struct
  include String

  let layout x = x
  let display = layout
  let get_name = layout
  let char_union c1 c2 = if String.equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if String.equal c1 c2 then None else Some c1
end

module Int64C = struct
  include Int64

  let layout = to_string
  let display = layout
  let get_name = layout
  let char_union c1 c2 = if Int64.equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if Int64.equal c1 c2 then None else Some c1
end

module DesymLabel = struct
  type t = string * int [@@deriving eq, ord]

  let layout (op, id) = op ^ ":" ^ string_of_int id
  let display = layout
  let get_name = layout
  let char_union c1 c2 = if equal c1 c2 then Some c1 else None
  let char_inter = char_union
  let char_subtract c1 c2 = if equal c1 c2 then None else Some c1
end

module SymLabel = struct
  type t = Nt.nt sevent [@@deriving eq, ord]

  let layout se = Frontend.layout_sevent se
  let display se = Frontend.display_sevent se
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
