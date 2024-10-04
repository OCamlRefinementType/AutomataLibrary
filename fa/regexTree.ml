open Sexplib.Std
open Zutils
open Zdatatype
open Prop

(** TODO: make a functor *)

type q_in_regex =
  | RForall of Nt.nt
  | RExists of Nt.nt
  | RPi of Nt.nt
  | RForallC of constant
  | RExistsC of constant
[@@deriving sexp, show, eq, ord]

type ('t, 'a) regex =
  | EmptyA
  | EpsilonA
  | Atomic of 'a
  | LorA of ('t, 'a) regex * ('t, 'a) regex
  | LandA of ('t, 'a) regex * ('t, 'a) regex
  | SeqA of ('t, 'a) regex list
  | StarA of ('t, 'a) regex
  | DComplementA of { atoms : 'a list; body : ('t, 'a) regex }
  | MultiAtomic of 'a list
  | RepeatN of int * ('t, 'a) regex
  (* the rest of feilds are disallowed after basic type checking *)
  | SyntaxSugar of ('t, 'a) regex_sugar
  | Extension of ('t, 'a) regex_extension
  | RExpr of ('t, 'a) regex_expr

and ('t, 'a) regex_extension =
  (* eliminate by delimited contex *)
  | AnyA
  | ComplementA of ('t, 'a) regex
  | Ctx of { atoms : 'a list; body : ('t, 'a) regex }

and ('t, 'a) regex_sugar =
  (* eliminate by desugar *)
  | SetMinusA of ('t, 'a) regex * ('t, 'a) regex
  | CtxOp of { op_names : string list; body : ('t, 'a) regex }

and ('t, 'a) regex_expr =
  (* eliminate by intrepret *)
  | RVar of ('t, string) typed
  | RConst of constant
  | RRegex of ('t, 'a) regex
  | QFRegex of {
      qv : ((q_in_regex, string) typed[@bound]);
      body : ('t, 'a) regex;
    }
  | Repeat of string * ('t, 'a) regex
  | RApp of { func : ('t, 'a) regex; arg : ('t, 'a) regex_expr }
    (* the arg can only be constants/vars *)
  | RLet of {
      lhs : ('t, string) typed;
      rhs : ('t, 'a) regex_expr;
      body : ('t, 'a) regex;
    }
[@@deriving sexp, show, eq, ord]

type 'c raw_regex =
  | Empty : 'c raw_regex (* L = { } *)
  | Eps : 'c raw_regex (* L = {ε} *)
  | MultiChar : 'c -> 'c raw_regex
  | Alt : 'c raw_regex * 'c raw_regex -> 'c raw_regex
  | Inters : 'c raw_regex * 'c raw_regex -> 'c raw_regex
  | Comple : 'c * 'c raw_regex -> 'c raw_regex
  | Seq : 'c raw_regex list -> 'c raw_regex
  | Star : 'c raw_regex -> 'c raw_regex
[@@deriving sexp, show, eq, ord]

(* type 'c raw_regex = *)
(*   | Empty : 'c raw_regex *)
(*   | Eps : 'c raw_regex *)
(*   | Char : 'c -> 'c raw_regex *)
(*   | Alt : 'c raw_regex * 'c raw_regex -> 'c raw_regex *)
(*   | Seq : 'c raw_regex * 'c raw_regex -> 'c raw_regex *)
(*   | Star : 'c raw_regex -> 'c raw_regex *)
(* [@@deriving sexp, show, eq, ord] *)

(** ast_builder *)

let mk_reg_func args r =
  List.fold_right
    (fun arg body ->
      match arg.ty with
      | Nt.Ty_unknown -> _die_with [%here] "the arguments must be typed"
      | ty -> RExpr (QFRegex { qv = arg.x #: (RForall ty); body }))
    args r

let rec map_label_in_regex (f : 'a -> 'b) (regex : ('t, 'a) regex) :
    ('t, 'b) regex =
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
    | Extension r -> Extension (map_label_in_regex_extension f r)
    | SyntaxSugar r -> SyntaxSugar (map_label_in_regex_sugar f r)
    | RExpr r -> RExpr (map_label_in_regex_expr f r)
  in
  aux regex

and map_label_in_regex_extension (f : 'a -> 'b)
    (regex : ('t, 'a) regex_extension) : ('t, 'b) regex_extension =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (map_label_in_regex f r)
  | Ctx { atoms; body } ->
      Ctx { atoms = List.map f atoms; body = map_label_in_regex f body }

and map_label_in_regex_sugar (f : 'a -> 'b) (regex : ('t, 'a) regex_sugar) :
    ('t, 'b) regex_sugar =
  match regex with
  | CtxOp { op_names; body } ->
      CtxOp { op_names; body = map_label_in_regex f body }
  | SetMinusA (r1, r2) ->
      SetMinusA (map_label_in_regex f r1, map_label_in_regex f r2)

and map_label_in_regex_expr (f : 'a -> 'b) (regex : ('t, 'a) regex_expr) :
    ('t, 'b) regex_expr =
  let rec aux regex =
    match regex with
    | RRegex r -> RRegex (map_label_in_regex f r)
    | Repeat (x, r) -> Repeat (x, map_label_in_regex f r)
    | RVar x -> RVar x
    | RConst c -> RConst c
    | QFRegex { qv; body } -> QFRegex { qv; body = map_label_in_regex f body }
    | RApp { func; arg } ->
        RApp { func = map_label_in_regex f func; arg = aux arg }
    | RLet { lhs; rhs; body } ->
        RLet { lhs; rhs = aux rhs; body = map_label_in_regex f body }
  in
  aux regex

let iter_label_in_regex (type a t) (f : a -> unit) (regex : (t, a) regex) : unit
    =
  let _ = map_label_in_regex f regex in
  ()

let _smart_inter loc (l : ('a, 'b) regex list) =
  match l with
  | [] -> Sugar._failatwith loc "die"
  | hd :: tl -> List.fold_left (fun a b -> LandA (a, b)) hd tl

let rec normalize_regex (regex : ('t, 'a) regex) : ('t, 'b) regex =
  let rec aux regex =
    match regex with
    | EmptyA | EpsilonA | Atomic _ -> regex
    | MultiAtomic [ c ] -> Atomic c
    | MultiAtomic _ -> regex
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA r -> StarA (aux r)
    | DComplementA { atoms; body } -> DComplementA { atoms; body = aux body }
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | Extension r -> Extension (normalize_regex_extension r)
    | SyntaxSugar r -> SyntaxSugar (normalize_regex_sugar r)
    | RExpr (RRegex r) -> aux r
    | RExpr r -> RExpr (normalize_regex_expr r)
  in
  aux regex

and normalize_regex_extension (regex : ('t, 'a) regex_extension) :
    ('t, 'b) regex_extension =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (normalize_regex r)
  | Ctx { atoms; body } -> Ctx { atoms; body = normalize_regex body }

and normalize_regex_sugar (regex : ('t, 'a) regex_sugar) : ('t, 'b) regex_sugar
    =
  match regex with
  | CtxOp { op_names; body } -> CtxOp { op_names; body = normalize_regex body }
  | SetMinusA (r1, r2) -> SetMinusA (normalize_regex r1, normalize_regex r2)

and normalize_regex_expr (regex : ('t, 'a) regex_expr) : ('t, 'b) regex_expr =
  let rec aux regex =
    match regex with
    | RRegex (RExpr r) -> aux r
    | RRegex r -> RRegex (normalize_regex r)
    | Repeat (x, r) -> Repeat (x, normalize_regex r)
    | RVar x -> RVar x
    | RConst c -> RConst c
    | QFRegex { qv; body } -> QFRegex { qv; body = normalize_regex body }
    | RApp { func; arg } -> RApp { func = normalize_regex func; arg = aux arg }
    | RLet { lhs; rhs; body } ->
        RLet { lhs; rhs = aux rhs; body = normalize_regex body }
  in
  aux regex

(** aux *)

let mk_all = StarA (Extension AnyA)

let mk_union_regex l =
  match l with
  | [] -> EmptyA
  | _ -> List.left_reduce [%here] (fun x y -> LorA (x, y)) l

let mk_inter_regex l =
  match l with
  | [] -> mk_all
  | _ -> List.left_reduce [%here] (fun x y -> LorA (x, y)) l
