open Sexplib.Std
open Prop
open Zutils
include Sevent

type ('t, 'a) rich_regex =
  | EmptyA
  | EpsilonA
  | Atomic of 'a
  | LorA of ('t, 'a) rich_regex * ('t, 'a) rich_regex
  | LandA of ('t, 'a) rich_regex * ('t, 'a) rich_regex
  | SeqA of ('t, 'a) rich_regex list
  | StarA of ('t, 'a) rich_regex
  | DComplementA of { atoms : 'a list; body : ('t, 'a) rich_regex }
  | MultiAtomic of 'a list
  | RepeatN of int * ('t, 'a) rich_regex
  (* Syntax Sugar *)
  | SetMinusA of ('t, 'a) rich_regex * ('t, 'a) rich_regex
  | CtxOp of { op_names : string list; body : ('t, 'a) rich_regex }
  (* Extension *)
  | AnyA
  | ComplementA of ('t, 'a) rich_regex
  | Ctx of { atoms : 'a list; body : ('t, 'a) rich_regex }
  (* RExpr *)
  | RVar of ('t, string) typed
  | RConst of constant
  | Repeat of string * ('t, 'a) rich_regex
  | RApp of { func : ('t, 'a) rich_regex; arg : ('t, 'a) rich_regex }
  | RLet of {
      lhs : ('t, string) typed;
      rhs : ('t, 'a) rich_regex;
      body : ('t, 'a) rich_regex;
    }
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

(** map/iter function *)
let map_label_in_rich_regex (f : 'a -> 'b) (regex : ('t, 'a) rich_regex) :
    ('t, 'b) rich_regex =
  let rec aux regex =
    match regex with
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | Atomic c -> Atomic (f c)
    | MultiAtomic cs -> MultiAtomic (List.map f cs)
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA r -> StarA (aux r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms = List.map f atoms; body = aux body }
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | AnyA -> AnyA
    | ComplementA r -> ComplementA (aux r)
    | Ctx { atoms; body } -> Ctx { atoms = List.map f atoms; body = aux body }
    | CtxOp { op_names; body } -> CtxOp { op_names; body = aux body }
    | SetMinusA (r1, r2) -> SetMinusA (aux r1, aux r2)
    | RVar x -> RVar x
    | RConst c -> RConst c
    | Repeat (x, r) -> Repeat (x, aux r)
    | RApp { func; arg } -> RApp { func = aux func; arg = aux arg }
    | RLet { lhs; rhs; body } -> RLet { lhs; rhs = aux rhs; body = aux body }
  in
  aux regex

let iter_label_in_rich_regex (type a t) (f : a -> unit)
    (regex : (t, a) rich_regex) : unit =
  let _ = map_label_in_rich_regex f regex in
  ()

let map_label_in_regex (f : 'a -> 'b) (regex : 'a regex) : 'b regex =
  let rec aux regex =
    match regex with
    | Empty -> Empty
    | Eps -> Eps
    | MultiChar c -> MultiChar (f c)
    | Alt (r1, r2) -> Alt (aux r1, aux r2)
    | Inters (r1, r2) -> Inters (aux r1, aux r2)
    | Seq rs -> Seq (List.map aux rs)
    | Star r -> Star (aux r)
    | Comple (domain, r) -> Comple (f domain, aux r)
  in
  aux regex

let iter_label_in_regex (type a) (f : a -> unit) (regex : a regex) : unit =
  let _ = map_label_in_regex f regex in
  ()

(** smart operators *)

open Sugar
open Zdatatype

let mk_all = StarA AnyA

let lorA l =
  match l with
  | [] -> EmptyA
  | _ -> List.left_reduce [%here] (fun x y -> LorA (x, y)) l

let landA l =
  match l with
  | [] -> mk_all
  | _ -> List.left_reduce [%here] (fun x y -> LandA (x, y)) l

let complementA regex =
  match regex with ComplementA r -> r | _ -> ComplementA regex

(* let intersect_rich loc l = *)
(*   match l with *)
(*   | [] -> _failatwith loc "die" *)
(*   | hd :: tl -> List.fold_left (fun a b -> LandA (a, b)) hd tl *)

let rec seq_unfold = function
  | Seq l -> List.concat_map seq_unfold l
  | Eps -> []
  | _ as r -> [ r ]

let seq l =
  let l = seq_unfold (Seq l) in
  if List.exists (function Empty -> true | _ -> false) l then Empty
  else match l with [] -> Eps | [ x ] -> x | _ -> Seq l

let alt l =
  match l with
  | [] -> Eps
  | hd :: tl -> List.fold_left (fun a b -> Alt (a, b)) hd tl

let inters loc l =
  match l with
  | [] -> _failatwith loc "die"
  | hd :: tl -> List.fold_left (fun a b -> Inters (a, b)) hd tl

let omit_show_rich_regex regex =
  show_rich_regex (fun _ _ -> ()) (fun _ _ -> ()) regex
