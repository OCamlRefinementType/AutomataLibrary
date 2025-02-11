open Ast

(** reduction *)

let rich_regex_reduce_expr regex =
  let rec aux regex =
    match regex with
    | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA r -> StarA (aux r)
    | DComplementA { atoms; body } -> DComplementA { atoms; body = aux body }
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | AnyA -> AnyA
    | ComplementA r -> ComplementA (aux r)
    | Ctx { atoms; body } -> Ctx { atoms; body = aux body }
    | CtxOp { op_names; body } -> CtxOp { op_names; body = aux body }
    | SetMinusA (r1, r2) -> SetMinusA (aux r1, aux r2)
    | RVar _ | RConst _ | Repeat _ | RApp _ | RLet _ -> failwith "unimp"
  in
  aux regex

open Typectx
open Zutils
open Zdatatype

let rich_regex_desugar ctx regex =
  let rec desugar regex =
    match regex with
    | RVar _ | RConst _ | Repeat _ | RApp _ | RLet _ -> failwith "never"
    | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
    | LorA (r1, r2) -> (
        match (desugar r1, desugar r2) with
        | EmptyA, r2 -> r2
        | r1, EmptyA -> r1
        | r1, r2 -> LorA (r1, r2))
    | LandA (r1, r2) -> (
        match (desugar r1, desugar r2) with
        | EmptyA, _ | _, EmptyA -> EmptyA
        | r1, r2 -> LandA (r1, r2))
    | RepeatN (n, r) -> RepeatN (n, desugar r)
    | SeqA rs -> SeqA (List.map desugar rs)
    | StarA r -> StarA (desugar r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms; body = desugar body }
    | AnyA -> AnyA
    | ComplementA r -> ComplementA (desugar r)
    | Ctx { atoms; body } -> Ctx { atoms; body = desugar body }
    (* NOTE: Desugar *)
    | SetMinusA (r1, r2) ->
        desugar (LandA (desugar r1, ComplementA (desugar r2)))
    | CtxOp { op_names; body } ->
        let atoms =
          List.map
            (fun op_name ->
              match get_opt ctx op_name with
              | None ->
                  _failatwith [%here] (spf "event(%s) is not declared" op_name)
              | Some ty -> mk_top_sevent op_name ty)
            op_names
        in
        desugar (Ctx { atoms; body })
  in
  desugar regex

let rich_regex_deextension (regex : ('t, 'a) rich_regex) : ('t, 'a) rich_regex =
  let ctx, regex =
    match regex with
    | Ctx { atoms; body } -> (Some atoms, body)
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
    | RVar _ | RConst _ | Repeat _ | RApp _ | RLet _ ->
        _die_with [%here] "should be eliminated"
    | SetMinusA _ | CtxOp _ -> _die_with [%here] "should be eliminated"
    | EmptyA | EpsilonA | Atomic _ | MultiAtomic _ -> regex
    | RepeatN (n, r) -> RepeatN (n, aux ctx r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms; body = aux (Some atoms) body }
    | LorA (r1, r2) -> LorA (aux ctx r1, aux ctx r2)
    | LandA (r1, r2) -> LandA (aux ctx r1, aux ctx r2)
    | SeqA rs -> SeqA (List.map (aux ctx) rs)
    | StarA r -> StarA (aux ctx r)
    (* NOTE: Deliminate context *)
    | ComplementA EmptyA -> StarA (MultiAtomic (force_ctx ctx))
    | ComplementA EpsilonA ->
        SeqA
          [ MultiAtomic (force_ctx ctx); StarA (MultiAtomic (force_ctx ctx)) ]
    | ComplementA r -> DComplementA { atoms = force_ctx ctx; body = aux ctx r }
    | AnyA -> MultiAtomic (force_ctx ctx)
    | Ctx { atoms; body } ->
        let atoms =
          List.slow_rm_dup (fun a b -> 0 == Stdlib.compare a b) atoms
        in
        aux (Some atoms) body
  in
  aux ctx regex

(** gather *)

open Prop

let gather_rich_regex regex =
  let m = ref (gathered_lits_init ()) in
  iter_label_in_rich_regex (fun se -> m := gather_se !m se) regex

let gather_regex regex =
  let m = ref (gathered_lits_init ()) in
  iter_label_in_regex (fun se -> m := gather_se !m se) regex

(** Simp *)

let simp_regex (eq : 'a -> 'a -> bool) (regex : ('t, 'a) rich_regex) =
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
    | RVar _ | RConst _ | Repeat _ | RApp _ | RLet _ ->
        _die_with [%here] "should be eliminated"
    | SetMinusA _ | CtxOp _ -> _die_with [%here] "should be eliminated"
    | AnyA | ComplementA _ | Ctx _ -> _die_with [%here] "should be eliminated"
    | EmptyA | EpsilonA | Atomic _ -> regex
    | MultiAtomic se -> mk_multiatom se
    | RepeatN (n, r) -> RepeatN (n, aux r)
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
