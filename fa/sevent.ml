open Sexplib.Std
open Zutils
open Zdatatype
open Prop

type 't sevent = { op : string; vs : ('t, string) typed list; phi : 't prop }
[@@deriving sexp, show, eq, ord]

let _get_sevent_fields { op; vs; phi } = (op, vs, phi)

let _get_sevent_name p =
  let res, _, _ = _get_sevent_fields p in
  res

let show_sevent regex = show_sevent (fun _ _ -> ()) regex

(* fv *)

let fv sevent =
  match sevent with
  | { vs; phi; _ } ->
      Zdatatype.List.substract (typed_eq String.equal) ([] @ fv_prop phi) vs

let subst_sevent (y : string) f sevent =
  match sevent with
  | { op; vs; phi } ->
      if List.exists (fun x -> String.equal x.x y) vs then { op; vs; phi }
      else { op; vs; phi = subst_prop y f phi }

let subst_sevent_instance y z sevent =
  subst_f_to_instance subst_sevent y z sevent

let mk_top_sevent (op : string) vs =
  (* let argsty = List.map snd @@ Nt.get_record_types ty in *)
  (* let vs = vs_names (List.length argsty) in *)
  (* let vs = List.map (fun (x, ty) -> x #: ty) @@ List.combine vs argsty in *)
  (* let vs = (__server_feild #: server_type) :: vs in *)
  (* normalize_name @@ *)
  { op; vs; phi = mk_true }

let gather_se { global_lits; local_lits } sevent =
  (* let () = Env.show_log "gather" @@ fun _ -> Printf.printf ">>>>> gather:\n" in *)
  match sevent with
  | { op; phi; vs } ->
      let lits = get_lits phi in
      let vs' = List.map (fun x -> x.x) vs in
      let is_contain_local_free lit =
        match List.interset String.equal vs' @@ fv_lit_id lit with
        | [] -> false
        | _ -> true
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
            | None -> Some (vs, llits)
            | Some (_, l) -> Some (vs, l @ llits))
          local_lits
      in
      let global_lits = global_lits @ glits in
      { global_lits; local_lits }

let and_prop_to_se p = function
  | { op; phi; vs } -> { op; phi = smart_add_to p phi; vs }

(* let delimit_cotexnt_se = function *)
(*   | Some ctx, GuardEvent { phi; _ } -> List.map (and_prop_to_se phi) ctx *)
(*   | _, r -> [ r ] *)
