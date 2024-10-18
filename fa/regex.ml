open Zutils
open Zdatatype
open Prop

include RegexTree
(** ast_builder *)

let smart_negate = function
  | Extension (ComplementA r) -> r
  | _ as r -> Extension (ComplementA r)

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

let omit_show_regex regex = show_regex (fun _ _ -> ()) (fun _ _ -> ()) regex

let rec rexpr_to_lit = function
  | RConst c -> Some (AC c)
  | RVar var -> Some (AVar var)
  | RRegex (RExpr r) -> rexpr_to_lit r
  | _ -> None

let _subst_se name (m : ('t, 't sevent) regex_expr) se =
  (* let () = *)
  (*   Printf.printf "\tsubst %s --> %s in %s\n" name *)
  (*     (omit_show_regex (RExpr m)) *)
  (*     (omit_show_regex (Atomic se)) *)
  (* in *)
  match rexpr_to_lit m with
  | Some lit -> subst_sevent_instance name lit se
  | None -> se

let rec subst_regex regex name (m : ('t, 't sevent) regex_expr) =
  let rec aux regex =
    match regex with
    | EmptyA | EpsilonA -> regex
    | Atomic se -> Atomic (_subst_se name m se)
    | RepeatN (n, r) -> RepeatN (n, subst_regex r name m)
    | MultiAtomic ses -> MultiAtomic (List.map (_subst_se name m) ses)
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA r -> StarA (aux r)
    | DComplementA { atoms; body } ->
        DComplementA
          { atoms = List.map (_subst_se name m) atoms; body = aux body }
    | Extension r -> Extension (subst_regex_extension r name m)
    | SyntaxSugar r -> SyntaxSugar (subst_regex_sugar r name m)
    | RExpr r -> RExpr (subst_regex_expr r name m)
  in
  aux regex

and subst_regex_extension regex name (m : ('t, 't sevent) regex_expr) =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (subst_regex r name m)
  | Ctx { atoms; body } ->
      Ctx
        {
          atoms = List.map (_subst_se name m) atoms;
          body = subst_regex body name m;
        }

and subst_regex_sugar regex name (m : ('t, 't sevent) regex_expr) :
    ('t, 'b) regex_sugar =
  match regex with
  | CtxOp { op_names; body } ->
      CtxOp { op_names; body = subst_regex body name m }
  | SetMinusA (r1, r2) ->
      SetMinusA (subst_regex r1 name m, subst_regex r2 name m)

and subst_regex_expr regex name (m : ('t, 't sevent) regex_expr) :
    ('t, 'b) regex_expr =
  let rec aux regex =
    match regex with
    | RRegex r -> RRegex (subst_regex r name m)
    | Repeat (x, r) when String.equal name x -> (
        match rexpr_to_lit m with
        | Some (AVar y) -> Repeat (y.x, subst_regex r name m)
        | Some (AC (I n)) -> RRegex (RepeatN (n, subst_regex r name m))
        | _ -> Repeat (x, subst_regex r name m))
    | Repeat (x, r) -> Repeat (x, subst_regex r name m)
    | RVar x -> if String.equal x.x name then m else RVar x
    | RConst c -> RConst c
    | QFRegex { qv; body } ->
        let qv =
          match qv.ty with
          | RForall ty when String.equal name @@ Nt.layout ty ->
              let c = match m with RConst c -> c | _ -> _die [%here] in
              qv.x #: (RForallC c)
          | RExists ty when String.equal name @@ Nt.layout ty ->
              let c = match m with RConst c -> c | _ -> _die [%here] in
              qv.x #: (RExistsC c)
          | _ -> qv
        in
        if String.equal qv.x name then regex
        else QFRegex { qv; body = subst_regex body name m }
    | RApp { func; arg } ->
        RApp { func = subst_regex func name m; arg = aux arg }
    | RLet { lhs; rhs; body } ->
        RLet { lhs; rhs = aux rhs; body = subst_regex body name m }
  in
  aux regex

let labels_to_multiatomic ls =
  let ls = List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) ls in
  match ls with [] -> EmptyA | [ e ] -> Atomic e | _ -> MultiAtomic ls

let ses_to_regex = function
  | [] -> EmptyA
  | [ s ] -> Atomic s
  | ss -> MultiAtomic ss

open Typectx
(** eliminate syntax sugar *)

let rec desugar ctx regex =
  match regex with
  | RExpr (RRegex r) -> desugar ctx r
  | RExpr _ ->
      let () = Printf.printf "%s\n" (omit_show_regex regex) in
      _failatwith [%here]
        (spf "should be eliminated: %s" (omit_show_regex regex))
  | Extension r -> Extension (desugar_regex_extension ctx r)
  | SyntaxSugar (SetMinusA (r1, r2)) ->
      desugar ctx
        (LandA (desugar ctx r1, Extension (ComplementA (desugar ctx r2))))
  | SyntaxSugar (CtxOp { op_names; body }) ->
      let atoms =
        List.map
          (fun op_name ->
            match get_opt ctx op_name with
            | None ->
                _failatwith [%here] (spf "event(%s) is not declared" op_name)
            | Some ty -> mk_top_sevent op_name ty)
          op_names
      in
      desugar ctx (Extension (Ctx { atoms; body }))
  | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
  | LorA (r1, r2) -> (
      match (desugar ctx r1, desugar ctx r2) with
      | EmptyA, r2 -> r2
      | r1, EmptyA -> r1
      | r1, r2 -> LorA (r1, r2))
  | LandA (r1, r2) -> (
      match (desugar ctx r1, desugar ctx r2) with
      | EmptyA, _ | _, EmptyA -> EmptyA
      | r1, r2 -> LandA (r1, r2))
  | RepeatN (n, r) -> RepeatN (n, desugar ctx r)
  | SeqA rs -> SeqA (List.map (desugar ctx) rs)
  | StarA r -> StarA (desugar ctx r)
  | DComplementA { atoms; body } ->
      DComplementA { atoms; body = desugar ctx body }

and desugar_regex ctx r = desugar ctx r

and desugar_regex_extension ctx regex =
  match regex with
  | AnyA -> AnyA
  | ComplementA r -> ComplementA (desugar_regex ctx r)
  | Ctx { atoms; body } -> Ctx { atoms; body = desugar_regex ctx body }

(** eliminate extension *)
let delimit_context (regex : ('t, 'a) regex) : ('t, 'a) regex =
  let ctx, regex =
    match regex with
    | Extension (Ctx { atoms; body }) -> (Some atoms, body)
    | _ -> (None, regex)
  in
  let force_ctx = function
    | None ->
        _failatwith [%here]
          "the regex need to be quantified with a context of chars."
    | Some ctx -> ctx
  in
  let rec aux ctx regex =
    match regex with
    | RExpr _ | SyntaxSugar _ -> _die_with [%here] "should be eliminated"
    | Extension (ComplementA EmptyA) -> StarA (MultiAtomic (force_ctx ctx))
    | Extension (ComplementA EpsilonA) ->
        SeqA
          [ MultiAtomic (force_ctx ctx); StarA (MultiAtomic (force_ctx ctx)) ]
    | Extension (ComplementA r) ->
        DComplementA { atoms = force_ctx ctx; body = aux ctx r }
    | Extension AnyA -> MultiAtomic (force_ctx ctx)
    | Extension (Ctx { atoms; body }) ->
        let atoms =
          List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) atoms
        in
        aux (Some atoms) body
    | Atomic e -> Atomic e
    | MultiAtomic es -> ses_to_regex es
    | EmptyA | EpsilonA -> regex
    | RepeatN (n, r) -> RepeatN (n, aux ctx r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms; body = aux (Some atoms) body }
    | LorA (r1, r2) -> LorA (aux ctx r1, aux ctx r2)
    | LandA (r1, r2) -> LandA (aux ctx r1, aux ctx r2)
    | SeqA rs -> SeqA (List.map (aux ctx) rs)
    | StarA r -> StarA (aux ctx r)
  in
  aux ctx regex

let gather_regex regex =
  let rec aux regex m =
    match regex with
    | RExpr _ | SyntaxSugar _ | Extension _ ->
        _die_with [%here] "should be eliminated"
    | RepeatN (_, r) -> aux r m
    | EmptyA -> m
    | EpsilonA -> m
    | Atomic se -> gather_se m se
    | LorA (t1, t2) -> aux t1 @@ aux t2 m
    | LandA (t1, t2) -> aux t1 @@ aux t2 m
    | SeqA rs -> List.fold_right aux rs m
    | StarA t -> aux t m
    | MultiAtomic se -> List.fold_left gather_se m se
    | DComplementA { atoms; body } ->
        let m = List.fold_left gather_se m atoms in
        aux body m
  in
  aux regex (gathered_lits_init ())

let lift_function e =
  let rec aux f r =
    match r with
    | RExpr (RRegex r) -> aux f r
    | RExpr (QFRegex { qv; body }) -> (
        match qv.ty with
        | RForall _ | RPi _ -> None
        | _ -> aux (fun body -> RExpr (QFRegex { qv; body = f body })) body)
    | _ as r -> Some (f, r)
  in
  aux (fun x -> x) e

let regex_is_function e : bool =
  let rec aux r =
    match r with
    | RExpr (RRegex r) -> aux r
    | RExpr (QFRegex { qv; body }) -> (
        match qv.ty with RForall _ | RPi _ -> true | _ -> aux body)
    | _ -> false
  in
  aux e

(* let mk_sevent_from_se = function *)
(*   | EffEvent { op; phi; vs } as e -> *)
(*       if String.equal op "all" then GuardEvent { vs; phi } else e *)
(*   | _ -> _die [%here] *)

let rec mk_lorA = function
  | [] -> EmptyA
  | [ r ] -> r
  | r :: rs -> LorA (r, mk_lorA rs)

let rec mk_landA = function
  | [] -> Extension AnyA
  | [ r ] -> r
  | r :: rs -> LandA (r, mk_landA rs)

(* let mk_sevents_from_ses ses = *)
(*   let all_events, or_events = *)
(*     List.partition (function EffEvent _ -> true | GuardEvent _ -> false) *)
(*     @@ List.map mk_sevent_from_se ses *)
(*   in *)
(*   let all_events = List.map (fun e -> Atomic e) all_events in *)
(*   mk_lorA (ses_to_regex or_events :: all_events) *)

let simp_regex (eq : 'a -> 'a -> bool) (regex : ('t, 'a) regex) =
  let mk_multiatom ses =
    (* let () = *)
    (*   Printf.printf "%i = len(%s)\n" (List.length ses) *)
    (*     (omit_show_regex (MultiAtomic ses)) *)
    (* in *)
    let ses = List.slow_rm_dup eq ses in
    match ses with [] -> EmptyA | _ -> MultiAtomic ses
  in
  let rec aux regex =
    (* let () = Printf.printf "simp: %s\n" @@ omit_show_regex regex in *)
    match regex with
    | RExpr _ | SyntaxSugar _ | Extension _ ->
        _die_with [%here] "should be eliminated"
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | Atomic se -> mk_multiatom [ se ]
    | MultiAtomic se -> mk_multiatom se
    | LorA (r1, r2) -> (
        match (aux r1, aux r2) with
        | EmptyA, r | r, EmptyA -> r
        | MultiAtomic r1, MultiAtomic r2 -> aux (MultiAtomic (r1 @ r2))
        | r1, r2 -> LorA (r1, r2))
    | LandA (r1, r2) -> (
        match (aux r1, aux r2) with
        | EmptyA, _ | _, EmptyA -> EmptyA
        | MultiAtomic r1, MultiAtomic r2 ->
            aux (MultiAtomic (List.interset eq r1 r2))
        | r1, r2 -> LandA (r1, r2))
    | SeqA rs -> (
        match
          List.filter (function EpsilonA -> false | _ -> true)
          @@ List.map aux rs
        with
        | [] -> EpsilonA
        | rs -> SeqA rs)
    | StarA r -> (
        match aux r with
        | EmptyA -> EpsilonA
        | EpsilonA -> EpsilonA
        | r -> StarA r)
    | DComplementA { atoms; body } -> (
        let atoms = List.slow_rm_dup eq atoms in
        let any_r = mk_multiatom atoms in
        match aux body with
        | EmptyA -> StarA any_r
        | EpsilonA -> LorA (any_r, SeqA [ any_r; StarA any_r ])
        | body -> DComplementA { atoms; body })
  in
  aux regex
