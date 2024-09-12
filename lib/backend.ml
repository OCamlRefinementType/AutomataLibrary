(* Representation of DOT graphs, and conversion from NFAs to DOT

   The DOT specification is here:
   https://graphviz.gitlab.io/_pages/doc/info/lang.html

   The code here supports a slightly restricted subset without
   subgraphs, multi-node edges, or "ports". *)

module Digraph : sig
  type t

  module Node : sig
    type t

    val make : id:string -> t
    val with_attrs : t -> (string * string) list -> t
  end

  val empty : t
  val with_name : t -> string -> t
  val with_node : t -> Node.t -> t
  val with_edge : t -> ?attrs:(string * string) list -> Node.t * Node.t -> t
  val with_attrs : t -> (string * string) list -> t
  val format : Format.formatter -> t -> unit
end = struct
  type id = string
  type attr = id * id

  let format_attrs formatter = function
    | [] -> ()
    | attrs ->
        Format.fprintf formatter "[@ @[";
        List.iter
          (fun (k, v) -> Format.fprintf formatter "%S@ =@ %S;" k v)
          attrs;
        Format.fprintf formatter "]@]"

  module Node = struct
    type t = id * attr list

    let make ~id = (id, [])
    let with_attrs (id, attrs) attrs' = (id, attrs @ attrs')

    let format formatter (id, attrs) =
      Format.fprintf formatter "%a@ %S" format_attrs attrs id

    let id (id, _) = id
  end

  type stmt =
    | Node of Node.t
    | Edge of Node.t * Node.t * attr list
    | Attr of id * id

  type t = id option * stmt list

  let empty = (None, [])

  let with_attrs (id, stmts) attrs =
    (id, stmts @ List.map (fun (k, v) -> Attr (k, v)) attrs)

  let with_node (id, stmts) node = (id, stmts @ [ Node node ])

  let with_edge (id, stmts) ?attrs (n1, n2) =
    match attrs with
    | None -> (id, stmts @ [ Edge (n1, n2, []) ])
    | Some attrs -> (id, stmts @ [ Edge (n1, n2, attrs) ])

  let with_name (_, s) n = (Some n, s)

  let format_stmt formatter = function
    | Node node -> Format.fprintf formatter "node@ @[%a@]" Node.format node
    | Edge (n1, n2, attrs) ->
        Format.fprintf formatter "@[@[%S@ ->@ %S@]@ %a@]" (Node.id n1)
          (Node.id n2) format_attrs attrs
    | Attr (k, v) -> Format.fprintf formatter "@[%S@ =@ %S@];" k v

  let format formatter (id, stmts) =
    let pr fmt = Format.fprintf formatter fmt in
    (match id with
    | None -> pr "@[digraph {@\n"
    | Some id -> pr "@]digraph %S{@[" id);
    List.iter (pr "@ @ @[%a@]@\n" format_stmt) stmts;
    pr "}@]"
end

type digraph = Digraph.t

let format_digraph = Digraph.format
