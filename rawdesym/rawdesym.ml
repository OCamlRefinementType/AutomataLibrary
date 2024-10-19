open Sugar
open Zdatatype
open Fa
open Common
open Desymeval
include Desymctx
include Resym
open DesymFA

let do_desym desym_ctx (gprop, r) =
  let fact = init_fact gprop desym_ctx in
  let fact = Satcheck.check_sat_fact desym_ctx fact in
  let r = desym_eval_regex desym_ctx.desym_map fact r in
  r

(* let check_emptiness desym_ctx (gprop, r) = *)
(*   let r' = do_desym desym_ctx (gprop, r) in *)
(*   DesymFA.emptiness r' *)

let do_normalize_desym_regex (rawreg : raw_regex) =
  dfa_to_reg @@ minimize @@ compile_raw_regex_to_dfa rawreg

let normalize_desym_regex (rawreg : raw_regex) =
  (* let () = Pp.printf "@{<bold>start@}: %s\n" (layout_raw_regex rawreg) in *)
  let rec aux rawreg =
    match rawreg with
    | Empty | Eps | MultiChar _ -> rawreg
    | Alt (r1, r2) -> smart_alt (aux r1) (aux r2)
    | Comple (cs1, Comple (cs2, r)) ->
        let () =
          Pp.printf "@{<bold>double comp@}: %s\n" (layout_raw_regex rawreg)
        in
        let cs1 = CharSet.filter (fun c -> not (CharSet.mem c cs2)) cs1 in
        if CharSet.is_empty cs1 then aux r else Alt (Star (MultiChar cs1), aux r)
    | Comple (cs, r) -> (
        match aux r with
        | Star (MultiChar cs') ->
            let () =
              Pp.printf "@{<bold>opt comple1@}: %s\n" (layout_raw_regex rawreg)
            in
            let cs'' = CharSet.filter (fun c -> not (CharSet.mem c cs')) cs in
            Star (MultiChar cs'')
        | _ as r ->
            let () =
              Pp.printf "@{<bold>opt comple fail@}: %s\n" (layout_raw_regex r)
            in
            do_normalize_desym_regex rawreg)
    | Inters _ ->
        let () =
          Pp.printf "@{<bold>opt inters@}: %s\n" (layout_raw_regex rawreg)
        in
        do_normalize_desym_regex rawreg
    | Seq l -> smart_seq (List.map aux l)
    | Star r -> smart_star (do_normalize_desym_regex r)
  in
  aux rawreg

let normalize_symbolic_rawregex tyctx event_tyctx (gprop, r) =
  let desym_ctx = mk_desym_ctx tyctx event_tyctx (gprop, r) in
  let r' = do_desym desym_ctx (gprop, r) in
  let r' = normalize_desym_regex r' in
  resym_regex desym_ctx r'

(* let check_symbolic_rewregex_emptiness tyctx event_tyctx (gprop, r) = *)
(*   let desym_ctx = mk_desym_ctx tyctx event_tyctx r in *)
(*   let r' = do_desym desym_ctx (gprop, r) in *)
(*   emptiness r' *)

(* open Prop *)

(* let serialize tyctx event_tyctx (gprop, r) = *)
(*   let open Sexplib.Std in *)
(*   let sexp_of_qv = sexp_of_typed Nt.sexp_of_nt sexp_of_string in *)
(*   let s1 = *)
(*     sexp_of_list sexp_of_qv @@ Typectx.ctx_to_list tyctx in *)
(*   let s2 = *)
(*     sexp_of_list (sexp_of_typed (sexp_of_list sexp_of_qv) sexp_of_string) @@ Typectx.ctx_to_list event_tyctx in *)
(*   let s3 = sexp_of_prop Nt.sexp_of_nt gprop in *)
(* let s4 = sexp_of_raw_regex (se) *)

let desymbolic_symbolic_rewregex tyctx event_tyctx (gprop, r) =
  let desym_ctx = mk_desym_ctx tyctx event_tyctx (gprop, r) in
  let r' = do_desym desym_ctx (gprop, r) in
  (desym_ctx, r')
