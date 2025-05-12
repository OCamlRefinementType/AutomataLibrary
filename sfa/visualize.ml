open BasicFa
open Common
open Backend

module MakeAutomataDot (FA : FINITE_AUTOMATA) = struct
  open FA
  module CharSet = Set.Make (C)

  let edge_name s =
    match CharSet.cardinal s with
    | 0 -> "{}"
    | 1 -> C.display (CharSet.choose s)
    | _ ->
        "{" ^ String.concat " " (List.map C.display (CharSet.elements s)) ^ "}"

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
          nfa.next#->state)
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
