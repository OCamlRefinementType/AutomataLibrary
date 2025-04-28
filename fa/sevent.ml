open Sexplib.Std
open Zutils
open Zdatatype
open Prop

let default_ret = "ret"
let default_e = "e"

type 't sevent = { op : string; event_ty : Nt.nt; phi : 't prop }
[@@deriving sexp, show, eq, ord]

let _get_sevent_fields { op; event_ty; phi } =
  (op, Nt.get_record_types event_ty, phi)

let _get_sevent_name p =
  let res, _, _ = _get_sevent_fields p in
  res

let show_sevent regex = show_sevent (fun _ _ -> ()) regex

(* fv *)

let fv sevent =
  match sevent with
  | { phi; _ } ->
      List.filter (fun x -> not (String.equal x.x default_e)) (fv_prop phi)

let subst_sevent (y : string) f sevent =
  match sevent with
  | { op; event_ty; phi } ->
      if String.equal y default_e then { op; event_ty; phi }
      else { op; event_ty; phi = subst_prop y f phi }

let subst_sevent_instance y z sevent =
  subst_f_to_instance subst_sevent y z sevent

let mk_top_sevent (op : string) event_ty = { op; event_ty; phi = mk_true }

let gather_se { global_lits; local_lits } sevent =
  (* let () = Env.show_log "gather" @@ fun _ -> Printf.printf ">>>>> gather:\n" in *)
  match sevent with
  | { op; phi; event_ty } ->
      let lits = get_lits phi in
      let is_contain_local_free lit =
        List.exists (String.equal default_e) (fv_lit_id lit)
      in
      let llits, glits = List.partition is_contain_local_free lits in
      (* let () = Printf.printf "vs: %s\n" (layout_qvs vs) in *)
      (* let () = *)
      (*   Printf.printf "glits: %s\n" *)
      (*     (List.split_by_comma Lit.layout_sexp_lit glits) *)
      (* in *)
      (* let () = *)
      (*   Printf.printf "llits: %s\n" *)
      (*     (List.split_by_comma Lit.layout_sexp_lit llits) *)
      (* in *)
      (* let () = _die [%here] in *)
      let local_lits =
        StrMap.update op
          (fun l ->
            match l with
            | None -> Some ([ default_e#:event_ty ], llits)
            | Some (_, l) -> Some ([ default_e#:event_ty ], l @ llits))
          local_lits
      in
      let global_lits = global_lits @ glits in
      { global_lits; local_lits }

let and_prop_to_se p = function
  | { op; phi; event_ty } -> { op; phi = smart_add_to p phi; event_ty }
