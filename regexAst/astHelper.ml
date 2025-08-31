open ParseTree
open Zutils
open Zdatatype
open Prop

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

let omit_show_rich_regex regex = show_rich_regex (fun _ _ -> ()) regex

let op_to_top_sevent event_ctx op =
  let record_type = Typectx._get_force [%here] event_ctx op in
  let fds = Nt.as_record [%here] record_type in
  { op; vs = fds; phi = mk_true }

let rich_regex_desugar event_ctx regex =
  let force_ctx = function
    | None ->
        _failatwith [%here]
          "the regex need to be quantified with a context of chars."
    | Some ctx -> ctx
  in
  let rec aux ctx regex =
    match regex with
    | CtxOp { op_names; body } ->
        let atoms = List.map (op_to_top_sevent event_ctx) op_names in
        aux ctx (Ctx { atoms; body })
    | SetMinusA (r1, r2) ->
        let r1, r2 = map2 (aux ctx) (r1, r2) in
        let r2' = DComplementA { atoms = force_ctx ctx; body = r2 } in
        LandA (r1, r2')
    | EmptyA | EpsilonA | MultiAtomic _ -> regex
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
    | Ctx { atoms; body } -> aux (Some atoms) body
  in
  aux None regex

let simp_rich_regex (eq : 'a -> 'a -> bool) (regex : 'a rich_regex) =
  let mk_multiatom ses =
    (* let () = *)
    (*   Printf.printf "%i = len(%s)\n" (List.length ses) *)
    (*     (omit_show_regex (MultiAtomic ses)) *)
    (* in *)
    let ses = List.slow_rm_dup eq ses in
    match ses with [] -> EmptyA | _ -> MultiAtomic ses
  in
  let rec aux regex =
    match regex with
    | SetMinusA _ | CtxOp _ -> _die_with [%here] "should be eliminated"
    | AnyA | ComplementA _ | Ctx _ -> _die_with [%here] "should be eliminated"
    | EmptyA | EpsilonA -> regex
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
