open Zutils
open OcamlParser
open Parsetree
open Zdatatype
open Prop
open Sv

let tpEvent str = spf "⟨%s⟩" str

let pprint = function
  | { op; phi; vs } ->
      if is_true phi then tpEvent op
      else
        tpEvent
        @@ spf "%s %s | %s" op
             (List.split_by " " (fun x -> x.x) vs)
             (layout_prop phi)

let layout_se = pprint
let layout = pprint
let tpEventRaw str = spf "<%s>" str

let pprintRaw = function
  | { op; phi; vs } ->
      tpEventRaw
      @@ spf "%s %s | %s" op
           (List.split_by " " (fun x -> x.x) vs)
           (layout_propRaw phi)

let layout_se_precise = pprintRaw

let get_opopt expr =
  match string_to_op_opt (get_denote expr) with
  | Some (DtConstructor op) -> Some (String.uncapitalize_ascii op)
  | _ -> None

let get_op expr = match get_opopt expr with Some x -> x | None -> _die [%here]

let get_self ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Nt.core_type_to_t ty)
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
  | Pexp_tuple es ->
      let es, ephi =
        match List.last_destruct_opt es with
        | Some (es, ephi) -> (es, ephi)
        | None -> _die [%here]
      in
      let phi = prop_of_expr ephi in
      let es =
        List.map
          (fun e ->
            let x = typed_id_of_expr e in
            match get_denoteopt e with
            | None -> (x, None)
            | Some "d" ->
                let open Nt in
                let arg = untyped @@ Rename.unique "x" in
                let arg' = untyped @@ AVar arg in
                let x = untyped @@ AVar x in
                let lit = AAppOp (untyped "==", [ arg'; x ]) in
                (arg, Some (Lit lit #: Ty_bool))
            | _ -> _die [%here])
          es
      in
      let args = List.map fst es in
      let phis =
        List.fold_left
          (fun res (_, prop) ->
            match prop with None -> res | Some prop -> prop :: res)
          [ phi ] es
      in
      (args, And phis)
  | _ -> ([], prop_of_expr expr)

let sevent_of_expr_aux expr =
  match expr.pexp_desc with
  | Pexp_construct (op, Some e) ->
      (* symbolic operator event *)
      let op = String.uncapitalize_ascii @@ longid_to_id op in
      let vs, phi = desugar_sevent e in
      { op; vs; phi }
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

let locally_rename_se ctx = function
  | { op; phi; _ } ->
      let vs =
        match List.find_opt (fun x -> String.equal op x.x) ctx with
        | None -> _die_with [%here] (spf "cannot find type of %s" op)
        | Some vs -> vs.ty
      in
      { op; vs; phi }
