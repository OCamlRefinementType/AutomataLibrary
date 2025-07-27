open ParseTree
open Zutils
open Prop
open Zdatatype

let fv_t_p_expr = typed_fv_lit
let substract_fvs l1 l2 = List.substract (typed_eq String.equal) l1 l2
let fv_sevent { vs; phi; _ } = substract_fvs (fv_prop phi) vs

let fv_rich_regex (fv : 'a -> ('t, string) typed list) (regex : 'a rich_regex) =
  let rm_dup = List.slow_rm_dup (fun x y -> String.equal x.x y.x) in
  let rec aux regex =
    match regex with
    | EmptyA | EpsilonA | AnyA -> []
    | MultiAtomic cs -> rm_dup @@ List.concat_map fv cs
    | LorA (r1, r2) | LandA (r1, r2) | SetMinusA (r1, r2) -> aux r1 @ aux r2
    | SeqA rs -> rm_dup @@ List.concat_map aux rs
    | StarA r | ComplementA r | RepeatN (_, r) | CtxOp { body = r; _ } -> aux r
    | DComplementA { atoms; body } | Ctx { atoms; body } ->
        aux body @ List.concat_map fv atoms
  in
  aux regex

let fv_regex (fv : 'a -> ('t, string) typed list) (regex : 'a regex) =
  let rm_dup = List.slow_rm_dup (fun x y -> String.equal x.x y.x) in
  let rec aux = function
    | Empty | Eps -> []
    | MultiChar c -> fv c
    | Alt (r1, r2) | Inters (r1, r2) -> aux r1 @ aux r2
    | Comple (c, r) -> fv c @ aux r
    | Seq cs -> rm_dup @@ List.concat_map aux cs
    | Star r -> aux r
  in
  aux regex
