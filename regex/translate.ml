open Ast

open Zutils
(** translate *)

let rich_regex_to_regex (f : 'a list -> 'b) (regex : (Nt.t, 'a) rich_regex) :
    'b regex =
  let rec aux regex =
    match regex with
    | RVar _ | RConst _ | Repeat _ | RApp _ | RLet _ ->
        _die_with [%here] "should be eliminated"
    | SetMinusA _ | CtxOp _ -> _die_with [%here] "should be eliminated"
    | AnyA | ComplementA _ | Ctx _ -> _die_with [%here] "should be eliminated"
    | EmptyA -> Empty
    | EpsilonA -> Eps
    | Atomic c -> MultiChar (f [ c ])
    | MultiAtomic cs -> MultiChar (f cs)
    | LorA (r1, r2) -> Alt (aux r1, aux r2)
    | LandA (r1, r2) -> Inters (aux r1, aux r2)
    | SeqA rs -> Seq (List.map aux rs)
    | StarA r -> Star (aux r)
    | DComplementA { atoms; body } -> Comple (f atoms, aux body)
    | RepeatN (0, _) -> Eps
    | RepeatN (1, r) -> aux r
    | RepeatN (n, r) ->
        let r = aux r in
        seq (List.init n (fun _ -> r))
  in
  aux regex

let regex_to_rich_regex (f : 'b -> 'a list) (regex : 'b regex) :
    (Nt.t, 'a) rich_regex =
  let rec aux regex =
    match regex with
    | Empty -> EmptyA
    | Eps -> EpsilonA
    | MultiChar c -> MultiAtomic (f c)
    | Alt (r1, r2) -> LorA (aux r1, aux r2)
    | Inters (r1, r2) -> LandA (aux r1, aux r2)
    | Seq rs -> SeqA (List.map aux rs)
    | Star r -> StarA (aux r)
    | Comple (atoms, body) -> DComplementA { atoms = f atoms; body = aux body }
  in
  aux regex
