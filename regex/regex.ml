include Ast
include AstAux
include To_regex
include Normal_regex_typing
include Translate
open Sugar
open Zdatatype

module MakeRegex (AB : ALPHABET) = struct
  open AB

  type reg = CharSet.t regex

  let alt a b =
    match (a, b) with
    | Empty, _ -> b
    | _, Empty -> a
    | MultiChar c1, MultiChar c2 -> MultiChar (CharSet.union c1 c2)
    | _, _ -> Alt (a, b)

  let alt_list l = List.left_reduce [%here] alt (Empty :: l)

  let inter a b =
    match (a, b) with
    | Empty, _ -> Empty
    | _, Empty -> Empty
    | MultiChar c1, MultiChar c2 -> MultiChar (CharSet.inter c1 c2)
    | _, _ -> Inters (a, b)

  let star r =
    match r with Empty -> Empty | Eps -> Eps | Star r -> Star r | r -> Star r

  let regex_to_str_regex r =
    let par = spf "\\(%s\\)" in
    let rec aux = function
      | Empty -> "∅"
      | Eps -> "ε"
      | MultiChar cs ->
          par (List.split_by "\\|" C.layout @@ List.of_seq @@ CharSet.to_seq cs)
      | Alt (r1, r2) -> par @@ spf "%s\\|%s" (aux r1) (aux r2)
      | Inters (r1, r2) -> par @@ spf "%s&%s" (aux r1) (aux r2)
      | Comple (cs, r2) ->
          par @@ spf "%s-%s" (aux (Star (MultiChar cs))) (aux r2)
      | Seq rs -> List.split_by "" aux rs
      | Star r -> spf "%s*" @@ par (aux r)
    in
    "^" ^ aux r ^ "$"

  (** Deriviate *)

  let rec emptiness (r : CharSet.t regex) =
    match r with
    | Empty -> true
    | Eps -> false
    | MultiChar cs -> CharSet.is_empty cs
    | Seq l -> List.exists emptiness l
    | Inters (r1, r2) -> emptiness r1 || emptiness r2
    | Alt (r1, r2) -> emptiness r1 && emptiness r2
    | Comple _ -> _die_with [%here] "should remove all comple"
    | Star _ -> false

  let rec nullable (r : CharSet.t regex) =
    match r with
    | Empty -> false
    | Eps -> true
    | MultiChar _ -> false
    | Seq l -> List.for_all nullable l
    | Inters (r1, r2) -> nullable r1 && nullable r2
    | Alt (r1, r2) -> nullable r1 || nullable r2
    | Comple (_, r) -> not (nullable r)
    | Star _ -> true

  let brzozowski_derivative_char (f : 'a -> C.t -> bool) (char : 'a)
      (r : CharSet.t regex) =
    let rec aux = function
      | Empty -> Empty
      | Eps -> Empty
      | MultiChar cs -> if CharSet.exists (f char) cs then Eps else Empty
      | Seq l ->
          let rec iter res = function
            | [] -> res
            | r :: l ->
                let res = seq (aux r :: l) :: res in
                if nullable r then iter res l else res
          in
          alt_list (iter [] l)
      | Inters (r1, r2) -> inter (aux r1) (aux r2)
      | Alt (r1, r2) -> alt (aux r1) (aux r2)
      | Comple (cs, r) ->
          if CharSet.exists (f char) cs then Comple (cs, aux r) else Empty
      | Star r -> seq [ aux r; Star r ]
    in
    aux r

  let brzozowski_derivative (f : 'a -> C.t -> bool) (r : CharSet.t regex) l =
    let rec aux r = function
      | [] -> r
      | u :: l -> aux (brzozowski_derivative_char f u r) l
    in
    aux r l

  let is_match (f : 'a -> C.t -> bool) (r : CharSet.t regex) l =
    nullable (brzozowski_derivative f r l)

  let layout_charset cs =
    let par = spf "\\(%s\\)" in
    par (List.split_by "\\|" C.layout @@ List.of_seq @@ CharSet.to_seq cs)

  let to_rich_regex r =
    regex_to_rich_regex (fun c -> List.of_seq @@ CharSet.to_seq c) r

  let of_rich_regex r = rich_regex_to_regex CharSet.of_list r
  let layout_regex r = layout_regex () C.layout (to_rich_regex r)
end
