open Zutils
open OcamlParser

(* open Oparse *)
open Parsetree
open Zdatatype
open RegexAst
open Sugar
open Prop

let tpEvent str = spf "⟨%s⟩" str
let display_tpEvent str = spf "[%s]" str

let layout_sevent { op; phi; vs } =
  if is_true phi && Myconfig.get_bool_option "show_sevent_fds" then tpEvent op
  else
    let fds =
      if Myconfig.get_bool_option "show_sevent_fds" then
        List.split_by " " (fun x -> x.x) vs ^ " "
      else ""
    in
    tpEvent @@ spf "%s %s| %s" op fds (layout_prop phi)

let display_sevent { op; phi; vs } =
  if is_true phi then op
  else
    let fds =
      if Myconfig.get_bool_option "show_sevent_fds" then
        List.split_by " " (fun x -> x.x) vs ^ " "
      else ""
    in
    display_tpEvent @@ spf "%s %s| %s" op fds (layout_propRaw phi)

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
  | Pexp_tuple es ->
      (* NOTE: now we don't recommand to manually define local feilds *)
      let es, ephi =
        match List.last_destruct_opt es with
        | Some (es, ephi) -> (es, ephi)
        | None -> _die [%here]
      in
      let phi = prop_of_expr ephi in
      let args = List.map (fun e -> typed_id_of_expr e) es in
      (args, phi)
  | _ -> ([], prop_of_expr expr)

let sevent_of_expr expr =
  let se =
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
  in
  (* let rty = normalize_name rty in *)
  (* let () = Printf.printf "ZZ: %s\n" (pprint_rty rty) in *)
  se

let rich_regex_of_expr label_of_expr expr =
  let parse_labels a =
    match a.pexp_desc with
    | Pexp_array es -> List.map label_of_expr es
    | _ -> [ label_of_expr a ]
  in
  let parse_ids a =
    match a.pexp_desc with
    | Pexp_array es -> List.map id_of_expr es
    | _ -> _die_with [%here] "expected an array of names "
  in
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_apply (func, args) -> (
        match (id_of_expr_opt func, List.map snd args) with
        | Some "starA", [ e1 ] -> StarA (aux e1)
        | Some "not", [ e1 ] -> ComplementA (aux e1)
        | Some "||", [ a; b ] -> LorA (aux a, aux b)
        | Some "-", [ a; b ] -> SetMinusA (aux a, aux b)
        | Some "&&", [ a; b ] -> LandA (aux a, aux b)
        | Some "ctx", [ a; b ] ->
            let atoms = parse_labels a in
            Ctx { atoms; body = aux b }
        | Some "ctxOp", [ a; b ] ->
            let op_names = parse_ids a in
            CtxOp { op_names; body = aux b }
        | Some "range", [ a ] ->
            let atoms = parse_labels a in
            MultiAtomic atoms
        | Some "parallel", [ a ] ->
            let atoms = parse_labels a in
            let interleaving = List.permutation atoms in
            let mk l =
              SeqA
                (mk_all
                :: List.concat_map (fun x -> [ MultiAtomic [ x ]; mk_all ]) l)
            in
            let interleaving = List.map mk interleaving in
            lorA interleaving
        | Some "repeat", [ a; b ] -> (
            let lit = lit_of_expr a in
            let r = aux b in
            match lit with
            | AC (I i) -> RepeatN (i, r)
            | _ ->
                _die_with [%here]
                @@ spf "unknown repeat %s" (Pprintast.string_of_expression expr)
            )
        | _, _ -> _die [%here])
    | Pexp_sequence _ -> SeqA (parse_seq expr)
    | Pexp_ident id -> (
        let id = longid_to_id id in
        match id with
        | "epsilonA" -> EpsilonA
        | "emptyA" -> EmptyA
        | "anyA" -> AnyA
        | "allA" -> mk_all
        | _ -> _die [%here])
    | _ -> MultiAtomic [ label_of_expr expr ]
  and parse_seq expr =
    match expr.pexp_desc with
    | Pexp_sequence (a, b) ->
        let l1, l2 = map2 parse_seq (a, b) in
        l1 @ l2
    | _ -> [ aux expr ]
  in
  aux expr

let rec pprint_aux layout_label = function
  | EmptyA -> ("∅", true)
  | EpsilonA -> ("ϵ", true)
  | MultiAtomic atoms -> (
      match atoms with
      | [ x ] -> (layout_label x, true)
      | _ -> (spf "[%s]" (List.split_by " " layout_label atoms), true))
  | LorA (a1, a2) ->
      ( spf "%s%s%s" (p_pprint layout_label a1) "∪" (p_pprint layout_label a2),
        false )
  | LandA (a1, a2) ->
      ( spf "%s%s%s" (p_pprint layout_label a1) "∩" (p_pprint layout_label a2),
        false )
  | SeqA rs -> (List.split_by "•" (p_pprint layout_label) rs, false)
  | StarA a -> (spf "%s*" (p_pprint layout_label a), true)
  | DComplementA { atoms; body } ->
      ( spf "Ctx[%s]{%sᶜ}"
          (List.split_by " " layout_label atoms)
          (p_pprint layout_label body),
        true )
  | RepeatN (x, r) -> (spf "repeat[%i]{%s}" x (p_pprint layout_label r), true)
  | ComplementA a -> (spf "%sᶜ" (p_pprint layout_label a), true)
  | AnyA -> (".", true)
  | Ctx { atoms; body } ->
      ( spf "Ctx[%s]{%s}"
          (List.split_by " " layout_label atoms)
          (p_pprint layout_label body),
        true )
  | CtxOp { op_names; body } ->
      ( spf "Ctx[%s]{%s}"
          (List.split_by " " (fun x -> x) op_names)
          (p_pprint layout_label body),
        true )
  | SetMinusA (a1, a2) ->
      (spf "%s\\%s" (p_pprint layout_label a1) (p_pprint layout_label a2), false)

and p_pprint layout_label a =
  let str, is_p = pprint_aux layout_label a in
  if is_p then str else spf "(%s)" str

let layout_rich_expr layout_label r = fst (pprint_aux layout_label r)
let layout_rich_str_regex regex = layout_rich_expr (fun x -> x) regex
let layout_rich_symbolic_regex regex = layout_rich_expr layout_sevent regex
(* let layout_desym_regex regex = layout Nt.layout DesymLabel.layout regex *)

let rich_str_regex_of_expr = rich_regex_of_expr id_of_expr
let rich_symbolic_regex_of_expr = rich_regex_of_expr sevent_of_expr
