open Ast

(* open Frontend *)
open Zutils
open PropTypecheck
open Typectx
open Zdatatype

type t = Nt.t

let _log = Myconfig._log_preprocess

type basic_typing_ctx = { event_ctx : Nt.nt ctx; ctx : Nt.nt ctx }

let mk_basic_typing_ctx = { event_ctx = emp; ctx = emp }

let constraint_sevent_type_check bctx (bc : BC.bc) { op; vs; phi } =
  if List.length vs != 0 then _die [%here]
  else
    let record_type = _get_force [%here] bctx.event_ctx op in
    let fds = Nt.as_record [%here] record_type in
    let ctx' = add_to_rights bctx.ctx fds in
    let bc, phi = constraint_prop_type_check ctx' bc phi in
    (bc, { op; vs = fds; phi })

let multi_constraint_sevent_type_check bctx (bc : BC.bc) ses =
  List.fold_left
    (fun (bc, res) se ->
      let bc, se = constraint_sevent_type_check bctx bc se in
      (bc, res @ [ se ]))
    (bc, []) ses

let constraint_rich_regex_type_check bctx (bc : BC.bc)
    (r : Nt.t sevent rich_regex) =
  let rec aux bc rregex =
    match rregex with
    | EpsilonA -> (bc, EpsilonA)
    | EmptyA -> (bc, EmptyA)
    | MultiAtomic ses ->
        let bc, ses = multi_constraint_sevent_type_check bctx bc ses in
        (bc, MultiAtomic ses)
    | LorA (r1, r2) ->
        let bc, r1 = aux bc r1 in
        let bc, r2 = aux bc r2 in
        (bc, LorA (r1, r2))
    | LandA (r1, r2) ->
        let bc, r1 = aux bc r1 in
        let bc, r2 = aux bc r2 in
        (bc, LandA (r1, r2))
    | SeqA rs ->
        let bc, rs = aux_list bc rs in
        (bc, SeqA rs)
    | StarA r ->
        let bc, r = aux bc r in
        (bc, StarA r)
    | DComplementA { atoms; body } ->
        let bc, atoms = multi_constraint_sevent_type_check bctx bc atoms in
        let bc, body = aux bc body in
        (bc, DComplementA { atoms; body })
    | RepeatN (n, r) ->
        let _ = Sugar._assert [%here] "" (n >= 0) in
        let bc, r = aux bc r in
        (bc, RepeatN (n, r))
    | ComplementA r ->
        let bc, r = aux bc r in
        (bc, ComplementA r)
    | AnyA -> (bc, AnyA)
    | Ctx { atoms; body } ->
        let bc, atoms = multi_constraint_sevent_type_check bctx bc atoms in
        let bc, body = aux bc body in
        (bc, Ctx { atoms; body })
    | CtxOp { op_names; body } ->
        let bc, body = aux bc body in
        (bc, CtxOp { op_names; body })
    | SetMinusA (r1, r2) ->
        let bc, r1 = aux bc r1 in
        let bc, r2 = aux bc r2 in
        (bc, SetMinusA (r1, r2))
  and aux_list bc l =
    List.fold_left
      (fun (bc, res) se ->
        let bc, se = aux bc se in
        (bc, res @ [ se ]))
      (bc, []) l
  in
  aux bc r

let solve bc =
  let open BC in
  let solution = Normalty.type_unification StrMap.empty bc.cs in
  match solution with
  | None -> _die_with [%here] "raw term normal type error"
  | Some sol ->
      Pp.printf "@{<bold>Solution:@}\n%s\n"
        (List.split_by_comma (fun (x, ty) -> spf "%s -> %s" x (Nt.layout ty))
        @@ StrMap.to_kv_list sol);
      sol

let rich_symbolic_regex_type_check event_ctx ctx r =
  let bctx = { event_ctx; ctx } in
  let bc, r = constraint_rich_regex_type_check bctx (BC.empty []) r in
  let sol = solve bc in
  let r = map_rich_regex (map_sevent (Nt.msubst_nt sol)) r in
  (* let () = Pp.printf "@{<bold>Before subst:@}\n%s\n" (layout_typed_raw_term term) in *)
  r
