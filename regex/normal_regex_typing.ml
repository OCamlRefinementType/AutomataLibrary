open Zutils

(* open PropTypecheck *)
open Typectx
open Ast

type t = Nt.t

(* NOTE: a variable can appear both in sevent and top-level *)
let add_var ctx x =
  {
    ctx with
    regex_tyctx = add_to_right ctx.regex_tyctx x;
    tyctx = add_to_right ctx.tyctx x;
  }

let bi_regex_check (label_check : regex_ctx -> 'a -> 'b) (ctx : regex_ctx)
    (regex : (t, 'a) rich_regex) : (t, 'b) rich_regex =
  let rec aux ctx regex : (t, 'b) rich_regex =
    match regex with
    | RVar _ | RConst _ | Repeat _ | RApp _ | RLet _ ->
        _die_with [%here] "unimp"
    | EpsilonA -> EpsilonA
    | EmptyA -> EmptyA
    | Atomic se -> Atomic (label_check ctx se)
    | MultiAtomic se -> MultiAtomic (List.map (label_check ctx) se)
    | LorA (t1, t2) -> LorA (aux ctx t1, aux ctx t2)
    | LandA (t1, t2) -> LandA (aux ctx t1, aux ctx t2)
    | SeqA rs -> SeqA (List.map (aux ctx) rs)
    | StarA t -> StarA (aux ctx t)
    | DComplementA { atoms; body } ->
        DComplementA
          { atoms = List.map (label_check ctx) atoms; body = aux ctx body }
    | RepeatN (n, r) ->
        let _ = Sugar._assert [%here] "" (n >= 0) in
        RepeatN (n, aux ctx r)
    | ComplementA t -> ComplementA (aux ctx t)
    | AnyA -> AnyA
    | Ctx { atoms; body } ->
        Ctx { atoms = List.map (label_check ctx) atoms; body = aux ctx body }
    | CtxOp { op_names; body } -> CtxOp { op_names; body = aux ctx body }
    | SetMinusA (t1, t2) -> SetMinusA (aux ctx t1, aux ctx t2)
  in
  aux ctx regex

(* and bi_expr_check ctx = function *)
(*   | RRegex r -> *)
(*       let r = aux ctx r in *)
(*       (RRegex r.x) #: r.ty *)
(*   | RConst c -> (RConst c) #: (infer_constant c) *)
(*   | RVar x -> *)
(*       let x = bi_typed_id_infer ctx.regex_tyctx x in *)
(*       (RVar x) #: x.ty *)
(*   | RApp { func; arg } -> *)
(*       let f = aux ctx func in *)
(*       let argty, resty = *)
(*         match f.ty with *)
(*         | Nt.Ty_arrow (t1, t2) -> (t1, t2) *)
(*         | _ -> *)
(*             let () = *)
(*               Printf.printf "RApp: %s : %s\n" *)
(*                 (To_regex.layout_symbolic_regex f.x) *)
(*                 (Nt.layout f.ty) *)
(*             in *)
(*             let () = *)
(*               Printf.printf "%s doesn't have function type\n" *)
(*                 (To_regex.layout_symbolic_regex func) *)
(*             in *)
(*             _failatwith [%here] "wrong application" *)
(*       in *)
(*       (\* let () = *\) *)
(*       (\*   Printf.printf "%s\n" *\) *)
(*       (\*     (layout_symbolic_regex (RExpr (RApp { func; arg }))) *\) *)
(*       (\* in *\) *)
(*       let arg = bi_expr_check ctx arg in *)
(*       let _ = Nt._type_unify [%here] arg.ty argty in *)
(*       (RApp { func = f.x; arg = arg.x }) #: resty *)
(*   | RLet { lhs; rhs; body } -> *)
(*       let rhs = bi_expr_check ctx rhs in *)
(*       let lhs = lhs.x #: rhs.ty in *)
(*       let body = aux (add_var ctx lhs) body in *)
(*       (RLet { lhs; rhs = rhs.x; body = body.x }) #: body.ty *)
(*   | Repeat (x, r) -> (Repeat (x, _get_x @@ aux ctx r)) #: Nt.Ty_unit *)
(*   | QFRegex { qv; body } -> ( *)
(*       match qv.ty with *)
(*       | RForall ty -> *)
(*           let qv = qv.x #: ty in *)
(*           let body = aux (add_var ctx qv) body in *)
(*           let retty = Nt.mk_arr qv.ty body.ty in *)
(*           (QFRegex { qv = qv.x #: (RForall qv.ty); body = body.x }) #: retty *)
(*       | RExists ty -> *)
(*           let qv = qv.x #: ty in *)
(*           let body = aux (add_var ctx qv) body in *)
(*           let retty = Nt.mk_arr qv.ty body.ty in *)
(*           (QFRegex { qv = qv.x #: (RExists qv.ty); body = body.x }) #: retty *)
(*       | RPi ty -> *)
(*           let qv = qv.x #: ty in *)
(*           let body = aux ctx body in *)
(*           let retty = Nt.mk_arr (ty_set qv.ty) body.ty in *)
(*           (QFRegex { qv = qv.x #: (RPi qv.ty); body = body.x }) #: retty *)
(*       | RForallC c -> *)
(*           let body = aux ctx body in *)
(*           (QFRegex { qv = qv.x #: (RForallC c); body = body.x }) #: body.ty *)
(*       | RExistsC c -> *)
(*           let body = aux ctx body in *)
(*           (QFRegex { qv = qv.x #: (RExistsC c); body = body.x }) #: body.ty) *)
(* in *)
(* aux ctx regex *)

let bi_symbolic_regex_check = bi_regex_check bi_sevent_check

let bi_str_regex_check (ctx : regex_ctx) regex =
  bi_regex_check (fun _ x -> x) ctx regex

let mk_regex_ctx (event_tyctx, tyctx) =
  { event_tyctx; regex_tyctx = emp; tyctx }
