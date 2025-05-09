open Zutils
open Translation
open Visualize
open Backend
include BasicFa
include Regex

(* module MakeA (C : CHARAC) = struct *)
(*   module AB = MakeAlphabet (MakeC (C)) *)
(*   module Tmp = MakeAutomataRegex (AB) *)
(*   include MakeAutomataDot (Tmp) *)
(*   include Tmp *)
(* end *)

module MakeAA (C : CHARAC) = struct
  module AB = MakeAlphabet (C)
  module Tmp = MakeAutomataRegex (AB)
  include MakeAutomataDot (Tmp)
  include Tmp

  let _tmp_dot_path = ".tmp.dot"

  let index_regex (regex : CharSet.t regex) : AB.char_idx =
    let m = AB.init_char_map () in
    let () = iter_label_in_regex (CharSet.iter (AB.add_char_to_map m)) regex in
    m

  let to_index_regex (m : AB.char_idx) (regex : CharSet.t regex) :
      Int64Set.t regex =
    map_label_in_regex
      (fun s ->
        CharSet.fold (fun c -> Int64Set.add (AB.c2id m c)) s Int64Set.empty)
      regex

  let from_index_regex (m : AB.char_idx) (regex : Int64Set.t regex) :
      CharSet.t regex =
    map_label_in_regex
      (fun s ->
        Int64Set.fold (fun c -> CharSet.add (AB.id2c m c)) s CharSet.empty)
      regex

  open Core

  let save_dfa_as_digraph sfa filename =
    Format.fprintf
      (Format.formatter_of_out_channel @@ Out_channel.create filename)
      "%a@." format_digraph
      (digraph_of_nfa (force_nfa sfa))

  let display_dfa sfa =
    let () = save_dfa_as_digraph sfa _tmp_dot_path in
    let () = Out_channel.(flush stdout) in
    (* let () = UnixLabels.sleep 1 in *)
    (* let ch = Core_unix.open_process_out "ls" in *)
    (* Core_unix.(close_process_out ch) *)
    Core_unix.(
      close_process_out @@ open_process_out
      @@ spf "cat %s | dot -Tpng | imgcat" _tmp_dot_path)
end

module CharAutomata = MakeAA (CharC)
module StrAutomata = MakeAA (StringC)
module IdAutomata = MakeAA (Int64C)

module DesymFA = struct
  include MakeAA (DesymLabel)
  open Zdatatype

  let unify_charset_by_op cs =
    let m =
      CharSet.fold
        (fun (op, id) ->
          StrMap.update op (function
            | None -> Some (StateSet.singleton id)
            | Some s -> Some (StateSet.add id s)))
        cs StrMap.empty
    in
    let add_op op s =
      StateSet.fold (fun id -> CharSet.add (op, id)) s CharSet.empty
    in
    StrMap.fold (fun op m res -> add_op op m :: res) m []

  let do_normalize_desym_regex (rawreg : CharSet.t regex) =
    (* let () = Printf.printf "Desym Reg: %s\n" (layout_desym_regex goal.reg) in *)
    (* let () = *)
    (*   Printf.printf "Desym Raw Reg%s\n" (DesymFA.layout_raw_regex rawreg) *)
    (* in *)
    (* let () = Printf.printf "%s\n" (DesymFA.layout_dfa fa) in *)
    dfa_to_reg @@ minimize @@ compile_regex_to_dfa rawreg

  let normalize_desym_regex (rawreg : CharSet.t regex) =
    let rec aux rawreg =
      match rawreg with
      | Empty | Eps | MultiChar _ -> rawreg
      | Alt (r1, r2) -> alt (aux r1) (aux r2)
      | Comple (cs, Star (MultiChar cs')) ->
          let cs'' = CharSet.filter (fun c -> not (CharSet.mem c cs')) cs in
          star (MultiChar cs'')
      | Inters _ | Comple _ -> do_normalize_desym_regex rawreg
      | Seq l -> seq (List.map aux l)
      | Star r -> Star (do_normalize_desym_regex r)
    in
    aux rawreg
end

open Prop

module SFA = struct
  include MakeAA (SymLabel)
  open Zdatatype

  let raw_regex_to_regex regex =
    let rec aux = function
      | Empty -> EmptyA
      | Eps -> EpsilonA
      | MultiChar cs -> MultiAtomic (List.of_seq @@ CharSet.to_seq cs)
      | Alt (r1, r2) -> LorA (aux r1, aux r2)
      | Inters (r1, r2) -> LandA (aux r1, aux r2)
      | Comple (cs, r2) ->
          DComplementA
            { atoms = List.of_seq @@ CharSet.to_seq cs; body = aux r2 }
      | Seq rs -> SeqA (List.map aux rs)
      | Star r -> StarA (aux r)
    in
    aux regex

  let omit_layout_raw_regex regex =
    layout_symbolic_regex @@ raw_regex_to_regex regex

  let unionify_sevent (dfa : dfa) =
    let ss_next = dfa_next_to_ss_next dfa in
    let f cs =
      let m =
        CharSet.fold
          (fun se ->
            let { op; vs; phi } = se in
            StrMap.update op (function
              | None -> Some (vs, phi)
              | Some (_, phi') -> Some (vs, smart_or [ phi; phi' ])))
          cs StrMap.empty
      in
      StrMap.fold
        (fun op (vs, phi) -> CharSet.add { op; vs; phi })
        m CharSet.empty
    in
    let ss_next = StateMap.map (StateMap.map f) ss_next in
    let next = ss_next_to_next ss_next in
    let sfa = { start = dfa.start; finals = dfa.finals; next } in
    (* let () = Pp.printf "\n@{<bold>before normalize:@}\n%s\n" (layout_dfa sfa) in *)
    normalize_dfa sfa

  let from_desym_dfa (f : DesymFA.CharSet.t -> CharSet.t) (dfa : DesymFA.dfa) :
      dfa =
    let ss_next = DesymFA.dfa_next_to_ss_next dfa in
    let ss_next = StateMap.map (StateMap.map f) ss_next in
    let next = ss_next_to_next ss_next in
    let sfa = { start = dfa.start; finals = dfa.finals; next } in
    (* let () = Pp.printf "\n@{<bold>before normalize:@}\n%s\n" (layout_dfa sfa) in *)
    normalize_dfa sfa

  let rename_sevent event_ctx (dfa : dfa) =
    let f = function
      | { op; vs; phi } ->
          let vs' =
            match StrMap.find_opt event_ctx op with
            | Some (Nt.Ty_record l) -> l
            | None -> _die_with [%here] (spf "die: None on %s" op)
            | Some ty -> _die_with [%here] (spf "die: %s" (Nt.layout ty))
          in
          (* let () = *)
          (*   Printf.printf "vs: %s\n" *)
          (*   @@ List.split_by_comma *)
          (*        (fun x -> spf "%s:%s" x.x (Nt.layout x.ty)) *)
          (*        vs *)
          (* in *)
          (* let () = *)
          (*   Printf.printf "vs': %s\n" *)
          (*   @@ List.split_by_comma *)
          (*        (fun x -> spf "%s:%s" x.x (Nt.layout x.ty)) *)
          (*        vs' *)
          (* in *)
          let phi' =
            List.fold_right
              (fun (v, v') -> subst_prop_instance v.x (AVar v'))
              (List.combine vs vs') phi
          in
          { op; vs = vs'; phi = phi' }
    in
    dfa_map_c f dfa

  let unify_se cs =
    let m =
      CharSet.fold
        (fun se m ->
          match se with
          | { op; vs; phi } ->
              StrMap.update op
                (function
                  | None -> Some (vs, phi)
                  | Some (vs', phi') -> Some (vs', smart_or [ phi; phi' ]))
                m)
        cs StrMap.empty
    in
    StrMap.fold
      (fun op (vs, phi) -> CharSet.add { op; vs; phi })
      m CharSet.empty

  let unify_raw_regex reg = raw_reg_map unify_se reg
end

let symbolic_dfa_to_event_name_dfa (dfa : SFA.dfa) =
  let open StrAutomata in
  let next =
    SFA.dfa_fold_transitions
      (fun (st, ch, dest) -> nfa_next_insert st (_get_sevent_name ch) dest)
      dfa StateMap.empty
  in
  let nfa : nfa =
    { start = StateSet.singleton dfa.start; finals = dfa.finals; next }
  in
  normalize_dfa @@ determinize nfa
