open Zutils
open Translation
open Backend
include Common
include BasicFa
include Regex
include To_regex

module MakeAutomataDot (FA : FINITE_AUTOMATA) = struct
  open FA
  module CharSet = Set.Make (C)

  let edge_name s =
    match CharSet.cardinal s with
    | 0 -> "{}"
    | 1 -> C.layout (CharSet.choose s)
    | _ ->
        "{" ^ String.concat " " (List.map C.layout (CharSet.elements s)) ^ "}"

  let digraph_of_nfa : nfa -> Digraph.t =
   fun (nfa : nfa) ->
    let states = Hashtbl.create 10 in
    let edges = Hashtbl.create 10 in
    let make_node =
      let counter = ref 0 in
      fun n ->
        let name = string_of_int !counter in
        incr counter;
        let node = Digraph.Node.make ~id:name in
        let shape =
          if StateSet.mem n nfa.finals then "doublecircle" else "circle"
        in
        Digraph.Node.with_attrs node [ ("shape", shape) ]
    in
    let add_edge source c target =
      Hashtbl.replace edges (source, target)
      @@
      match Hashtbl.find edges (source, target) with
      | exception Not_found -> CharSet.singleton c
      | set -> CharSet.add c set
    in
    let rec step state =
      (* Accumulate nodes and edges, using the states/edges tables as
         'seen lists' to ensure each node and edge is only visited once *)
      if not (Hashtbl.mem states state) then (
        Hashtbl.add states state (make_node state);
        CharMap.iter
          (fun c targets ->
            StateSet.iter
              (fun target ->
                add_edge state c target;
                step target)
              targets)
          nfa.next #-> state)
    in
    StateSet.iter step nfa.start;
    (* Empty node to the left of the start state *)
    let input =
      Digraph.Node.with_attrs (Digraph.Node.make ~id:"")
        [ ("shape", "none"); ("width", "0") ]
    in
    (* Initial empty digraph *)
    let dg =
      Digraph.with_node
        (Digraph.with_attrs Digraph.empty [ ("rankdir", "LR") ])
        input
    in
    (* Add the state nodes *)
    let dg =
      Hashtbl.fold (fun _ node dg -> Digraph.with_node dg node) states dg
    in
    (* Add the initial edges *)
    let dg =
      StateSet.fold
        (fun s dg -> Digraph.with_edge dg (input, Hashtbl.find states s))
        nfa.start dg
    in
    (* Add the other edges *)
    Hashtbl.fold
      (fun (source, target) s dg ->
        Digraph.with_edge dg
          ~attrs:[ ("label", edge_name s); ("fontsize", "10") ]
          (Hashtbl.find states source, Hashtbl.find states target))
      edges dg
end

module MakeA (C : CHARAC) = struct
  module Tmp = MakeAutomata (MakeC (C))
  include MakeAutomataDot (Tmp)
  include Tmp
end

module MakeAA (C : CHARAC) = struct
  include MakeA (C)

  let _tmp_dot_path = ".tmp.dot"

  let index_regex (regex : ('t, C.t) regex) : C.char_idx =
    let m = C.init_char_map () in
    let () = iter_label_in_regex (C.add_char_to_map m) regex in
    m

  let to_index_regex (m : C.char_idx) (regex : ('t, C.t) regex) :
      ('t, Int64.t) regex =
    map_label_in_regex (C.c2id m) regex

  let from_index_regex (m : C.char_idx) (regex : ('t, Int64.t) regex) :
      ('t, C.t) regex =
    map_label_in_regex (C.id2c m) regex

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
module DesymFA = MakeAA (DesymLabel)
open Prop

module SeventLabel = struct
  type t = Nt.t sevent

  let compare = compare_sevent (fun _ _ -> 0)
  let layout = pprintRaw
  let delimit_cotexnt_char = delimit_cotexnt_se
end

module DRegexLabel = struct
  type t = (Nt.t, DesymLabel.t) regex

  let compare = compare_regex (fun _ _ -> 0) DesymLabel.compare
  let layout = layout_desym_regex
  let delimit_cotexnt_char = _die_with [%here] "never"
end

module DRegexFA = struct
  include MakeAA (DRegexLabel)
end

module SFA = struct
  include MakeAA (SeventLabel)
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

  let unionify_sevent (dfa : dfa) =
    let ss_next = dfa_next_to_ss_next dfa in
    let f cs =
      let m =
        CharSet.fold
          (fun se ->
            let op, vs, phi = _get_sevent_fields [%here] se in
            StrMap.update op (function
              | None -> Some (vs, phi)
              | Some (_, phi') -> Some (vs, smart_add_to phi phi')))
          cs StrMap.empty
      in
      StrMap.fold
        (fun op (vs, phi) -> CharSet.add (EffEvent { op; vs; phi }))
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
      | GuardEvent _ -> _die [%here]
      | EffEvent { op; vs; phi } ->
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
          EffEvent { op; vs = vs'; phi = phi' }
    in
    dfa_map_c f dfa
end

let symbolic_dfa_to_event_name_dfa (dfa : SFA.dfa) =
  let open StrAutomata in
  let next =
    SFA.dfa_fold_transitions
      (fun (st, ch, dest) ->
        nfa_next_insert st (_get_sevent_name [%here] ch) dest)
      dfa StateMap.empty
  in
  let nfa : nfa =
    { start = StateSet.singleton dfa.start; finals = dfa.finals; next }
  in
  normalize_dfa @@ determinize nfa

module RegexTypecheck = Normal_regex_typing

let bi_symbolic_regex_check = Normal_regex_typing.bi_symbolic_regex_check
let bi_str_regex_check = Normal_regex_typing.bi_str_regex_check
let mk_regex_ctx = Normal_regex_typing.mk_regex_ctx
