open Sexplib.Std
open Zutils
open Zdatatype
open Prop

let default_ret_fd = "vret"

(** We need to defined vs according to the type of op *)

type 't sevent = { op : string; vs : ('t, string) typed list; phi : 't prop }
[@@deriving sexp, show, eq, ord]

let _fill_sevent_with_record_ty loc { op; vs; phi } record_ty =
  if List.length vs != 0 then _die loc
  else
    let fds = Nt.as_record loc record_ty in
    { op; vs = fds; phi }

let mk_top_sevent loc (op : string) record_type =
  _fill_sevent_with_record_ty loc { op; vs = []; phi = mk_true } record_type

let show_sevent regex = show_sevent (fun _ _ -> ()) regex

type 'a rich_regex =
  | MultiAtomic of 'a list
  | EmptyA
  | EpsilonA
  | LorA of 'a rich_regex * 'a rich_regex
  | LandA of 'a rich_regex * 'a rich_regex
  | SeqA of 'a rich_regex list
  | StarA of 'a rich_regex
  | DComplementA of { atoms : 'a list; body : 'a rich_regex }
  | RepeatN of int * 'a rich_regex
  (* Syntax Sugar *)
  | SetMinusA of 'a rich_regex * 'a rich_regex
  | CtxOp of { op_names : string list; body : 'a rich_regex }
  (* Extension *)
  | AnyA
  | ComplementA of 'a rich_regex
  | Ctx of { atoms : 'a list; body : 'a rich_regex }
[@@deriving sexp, show, eq, ord]

type 'c regex =
  | Empty : 'c regex (* L = { } *)
  | Eps : 'c regex (* L = {ε} *)
  | MultiChar : 'c -> 'c regex
  | Alt : 'c regex * 'c regex -> 'c regex
  | Inters : 'c regex * 'c regex -> 'c regex
  | Comple : 'c * 'c regex -> 'c regex
  | Seq : 'c regex list -> 'c regex
  | Star : 'c regex -> 'c regex
[@@deriving sexp, show, eq, ord]
