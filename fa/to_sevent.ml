open Zutils
open OcamlParser
open Oparse
open Parsetree
open Zdatatype
open RegexTree
open Prop

let tpEvent str = spf "⟨%s⟩" str

let pprint = function
  | { op; phi; _ } ->
      if is_true phi then tpEvent op
      else tpEvent @@ spf "%s %s | %s" op default_e (layout_prop phi)

let layout_se = pprint
let layout = pprint
(* let tpEventRaw str = spf "<%s>" str *)

let pprintRaw = function
  | { op; phi; _ } ->
      tpEvent @@ spf "%s %s | %s" op default_e (layout_propRaw phi)

let layout_se_precise = pprintRaw

let get_opopt expr =
  match string_to_op_opt (get_denote expr) with
  | Some (DtConstructor op) -> Some (String.uncapitalize_ascii op)
  | _ -> None

let get_op expr = match get_opopt expr with Some x -> x | None -> _die [%here]

let get_self ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt#:(Nt.core_type_to_t ty)
  | _ ->
      let () = Printf.printf "\nct: %s\n" (Oparse.string_of_core_type ct) in
      _die_with [%here] ""

let vars_phi_sevent_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], prop_of_expr expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let desugar_sevent expr =
  match expr.pexp_desc with
  | Pexp_tuple [ e; ephi ] ->
      let phi = prop_of_expr ephi in
      let x = typed_id_of_expr e in
      if String.equal x.x default_e then _die [%here];
      (x.ty, phi)
  | _ -> _die [%here]

let sevent_of_expr_aux expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) -> (
      (* symbolic operator event *)
      let op = String.uncapitalize_ascii @@ longid_to_id op in
      match vars_phi_sevent_of_expr e with
      | [ { x; ty = event_ty } ], phi when String.equal x default_e ->
          { op; event_ty; phi }
      | _ -> _failatwith [%here] (string_of_expression e))
  | _ ->
      let () =
        Printf.printf "unknown symbolic event: %s\n"
        @@ Pprintast.string_of_expression expr
      in
      _die [%here]

let sevent_of_expr expr =
  let rty = sevent_of_expr_aux expr in
  (* let rty = normalize_name rty in *)
  (* let () = Printf.printf "ZZ: %s\n" (pprint_rty rty) in *)
  rty

let of_expr = sevent_of_expr
