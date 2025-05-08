open ParseTree
open Zutils
open Prop

let map_sevent (f : 't -> 's) { op; vs; phi } =
  let vs = List.map (fun x -> x#=>f) vs in
  let phi = map_prop f phi in
  { op; vs; phi }

let map_rich_regex (f : 'a -> 'b) (regex : 'a rich_regex) : 'b rich_regex =
  let rec aux regex =
    match regex with
    | EmptyA -> EmptyA
    | EpsilonA -> EpsilonA
    | MultiAtomic cs -> MultiAtomic (List.map f cs)
    | LorA (r1, r2) -> LorA (aux r1, aux r2)
    | LandA (r1, r2) -> LandA (aux r1, aux r2)
    | SeqA rs -> SeqA (List.map aux rs)
    | StarA r -> StarA (aux r)
    | DComplementA { atoms; body } ->
        DComplementA { atoms = List.map f atoms; body = aux body }
    | RepeatN (n, r) -> RepeatN (n, aux r)
    | AnyA -> AnyA
    | ComplementA r -> ComplementA (aux r)
    | Ctx { atoms; body } -> Ctx { atoms = List.map f atoms; body = aux body }
    | CtxOp { op_names; body } -> CtxOp { op_names; body = aux body }
    | SetMinusA (r1, r2) -> SetMinusA (aux r1, aux r2)
  in
  aux regex

let iter_label_in_rich_regex (type a) (f : a -> unit) (regex : a rich_regex) :
    unit =
  let _ = map_rich_regex f regex in
  ()

let map_regex (f : 'a -> 'b) (regex : 'a regex) : 'b regex =
  let rec aux = function
    | Empty -> Empty
    | Eps -> Eps
    | MultiChar c -> MultiChar (f c)
    | Alt (r1, r2) -> Alt (aux r1, aux r2)
    | Inters (r1, r2) -> Inters (aux r1, aux r2)
    | Comple (c, r) -> Comple (f c, aux r)
    | Seq cs -> Seq (List.map aux cs)
    | Star r -> Star (aux r)
  in
  aux regex

let iter_label_in_regex (type a) (f : a -> unit) (regex : a regex) : unit =
  let _ = map_regex f regex in
  ()
