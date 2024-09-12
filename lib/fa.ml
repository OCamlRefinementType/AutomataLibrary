open Common
open Zutils
open Translation
open Backend
include BasicFa
include Regex

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

module CharC = struct
  include Char

  let layout x = spf "%c" x
  let delimit_cotexnt_char (_, c) = [ c ]
end

module StringC = struct
  include String

  let layout x = x
  let delimit_cotexnt_char (_, c) = [ c ]
end

module Int64C = struct
  include Int64

  let layout = to_string
  let delimit_cotexnt_char (_, c) = [ c ]
end

module DesymLabel = struct
  type t = string * int

  let compare (a : t) (b : t) = Stdlib.compare a b
  let layout (op, id) = op ^ ":" ^ string_of_int id
  let delimit_cotexnt_char (_, c) = [ c ]
  let eq (s1, i1) (s2, i2) = String.equal s1 s2 && Int.equal i1 i2
end

module CharAutomata = MakeAA (CharC)
module StrAutomata = MakeAA (StringC)
module IdAutomata = MakeAA (Int64C)
module DesymFA = MakeAA (DesymLabel)
