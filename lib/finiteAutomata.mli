open Common
module C : CHARACTER
module CharMap : Map.S with type key = C.t
module CharSet : Set.S with type elt = C.t

type transitions = StateSet.t CharMap.t
type d_transition = state CharMap.t

type raw_regex =
  | Empty : raw_regex (* L = { } *)
  | Eps : raw_regex (* L = {ε} *)
  | MultiChar : CharSet.t -> raw_regex
  | Alt : raw_regex * raw_regex -> raw_regex
  | Inters : raw_regex * raw_regex -> raw_regex
  | Comple : CharSet.t * raw_regex -> raw_regex
  | Seq : raw_regex * raw_regex -> raw_regex
  | Star : raw_regex -> raw_regex

type nfa = {
  start : StateSet.t;
  finals : StateSet.t;
  next : transitions StateMap.t;
}

type dfa = {
  start : state;
  finals : StateSet.t;
  next : d_transition StateMap.t;
}

val ( #-> ) : 'a CharMap.t StateMap.t -> StateSet.elt -> 'a CharMap.t
