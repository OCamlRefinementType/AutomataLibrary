open Ast
open Zdatatype

(** types in P lang is shown in a different way from our types. *)
let rec layout_pnt t =
  let open Nt in
  let rec aux = function
    | Ty_constructor (name, [ ty ]) when String.equal name "set" ->
        spf "set[%s]" (aux ty)
    | Ty_constructor (name, [ ty ]) when String.equal name "seq" ->
        spf "seq[%s]" (aux ty)
    | Ty_constructor (name, [ ty ]) when String.equal name "ref" -> aux ty
    | Ty_constructor (name, [ ty1; ty2 ]) when String.equal name "map" ->
        spf "map[%s, %s]" (aux ty1) (aux ty2)
    | Ty_tuple ts when List.length ts > 1 ->
        spf "(%s)" @@ List.split_by ", " aux ts
    | Ty_record l -> (
        match l with
        | [] -> "" (* _die_with [%here] "bad record" *)
        | x :: _ when String.equal x.x "0" ->
            let l = List.map _get_ty l in
            spf "(%s)" @@ List.split_by ", " layout_pnt l
        | _ ->
            spf "(%s)"
            @@ List.split_by ", "
                 (fun { x = a; ty = b } -> layout_pnt_typed a b)
                 l)
    | _ as t -> layout t
  in
  aux t

and layout_pnt_typed str x =
  match x with Nt.Ty_unit -> str | _ -> spf "%s: %s" str (layout_pnt x)

let layout_pnt_typed_var x =
  (* let () = Printf.printf "print tvar %s\n" x.x in *)
  spf "%s: %s" x.x (layout_pnt x.ty)

let layout_p_wapper_decl = function
  | WrapperEnum { enum_name; elems } ->
      spf "enum %s {\n%s\n}" enum_name
        (List.split_by ",\n" (spf "    %s") elems)
  | WrapperTypeAlias { type_name; alias_type } ->
      spf "type %s = %s;" type_name (layout_pnt alias_type)
  | WrapperEventDecl { event_name; event_type = Nt.Ty_record [] } ->
      spf "event %s;" event_name
  | WrapperEventDecl { event_name; event_type } ->
      spf "event %s: %s;" event_name (layout_pnt event_type)
  | WrapperMachineDecl { machine_name; _ } ->
      spf "type %s = %s;" machine_name "machine"
  | WrapperSpecEventDecl { event_name; spec_event_type; _ } ->
      spf "event %s: %s;" event_name (layout_pnt spec_event_type)
  | ReqResp _ -> ""
  | Dummy -> _die [%here]

let layout_p_wapper_decls l =
  let l = List.filter (function Dummy -> false | _ -> true) l in
  List.split_by "\n" layout_p_wapper_decl l

let layout_const = function
  | PBool b -> string_of_bool b
  | PInt i -> string_of_int i
  | PStr str -> spf "\"%s\"" str
  | PHalt -> "halt"
  | PError -> "error"
  | PRandomBool -> "$"
  | PUnit -> ""
  | PDefault nt -> spf "default(%s)" (layout_pnt nt)
(* | _ -> _die_with [%here] "unimp" *)

let mk_indent n str = spf "%s%s" (String.init (n * 2) (fun _ -> ' ')) str
let mk_indent_line n str = spf "%s%s\n" (String.init (n * 2) (fun _ -> ' ')) str

let mk_indent_semicolon_line n str =
  spf "%s%s;\n" (String.init (n * 2) (fun _ -> ' ')) str

let rec layout_p_expr ctx n = function
  | PThis -> "this"
  | PNull -> "null"
  | Pid id -> id.x
  | PConst c -> layout_const c
  | PApp { pfunc = { x = "add_set"; _ }; args = [ e1; e2 ] } ->
      spf "%s += (%s)"
        (layout_typed_p_expr ctx 0 e1)
        (layout_typed_p_expr ctx 0 e2)
  | PApp { pfunc; args }
    when List.exists (String.equal pfunc.x) p_infix_operator -> (
      match args with
      | [ e1; e2 ] ->
          spf "(%s %s %s)"
            (layout_typed_p_expr ctx 0 e1)
            pfunc.x
            (layout_typed_p_expr ctx 0 e2)
      | _ -> _die [%here])
  | PApp { pfunc; args } ->
      spf "%s(%s)" pfunc.x (List.split_by ", " (layout_typed_p_expr ctx 0) args)
  | PRecord l -> (
      match l with
      | [] -> _die [%here]
      | [ (name, b) ] when String.equal name "0" ->
          spf "(%s,)" (layout_typed_p_expr ctx 0 b)
      | [ (a, b) ] -> spf "(%s = %s,)" a (layout_typed_p_expr ctx 0 b)
      | (name, _) :: _ when String.equal name "0" ->
          spf "(%s)"
            (List.split_by ", "
               (fun (_, b) -> spf "%s" (layout_typed_p_expr ctx 0 b))
               l)
      | _ ->
          spf "(%s)"
            (List.split_by ", "
               (fun (a, b) -> spf "%s = %s" a (layout_typed_p_expr ctx 0 b))
               l))
  | PField { record; field } ->
      (* spf "(%s).%s" (layout_typed_p_expr ctx 0 record) field *)
      spf "%s.%s" (layout_typed_p_expr ctx 0 record) field
  | PAccess { container; index } ->
      spf "%s[%s]"
        (layout_typed_p_expr ctx 0 container)
        (layout_typed_p_expr ctx 0 index)
  | PDeref e -> layout_typed_p_expr ctx n e (* P don't show the dereference *)
  | PAssign { lvalue; rvalue } ->
      spf "%s = %s"
        (layout_typed_p_expr ctx 0 lvalue)
        (layout_typed_p_expr ctx 0 rvalue)
  | PSeq { rhs; body } ->
      let rhs = layout_typed_p_expr ctx n rhs in
      spf "%s;\n%s" rhs (mk_indent n @@ layout_typed_p_expr ctx n body)
  | PSend { dest; event_name; payload } ->
      spf "send %s, %s, %s"
        (layout_typed_p_expr ctx 0 dest)
        event_name
        (layout_typed_p_expr ctx 0 payload)
  | PReturn { x = PConst PHalt; _ } -> spf "raise halt"
  | PReturn { x = PConst PError; _ } -> spf "goto %s" error_state_name
  | PReturn e ->
      (* let () = Printf.printf "return %s\n" (layout_sexp_p_expr e.x) in *)
      spf "return %s" (layout_typed_p_expr ctx n e)
  | PGoto state -> spf "goto %s" state
  | PBreak -> "break"
  | ForeachSet { elem; set; body } ->
      let head =
        spf "foreach (%s in %s) {" elem.x (layout_typed_p_expr ctx 0 set)
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s" head
        (mk_indent_semicolon_line (n + 1)
        @@ layout_typed_p_expr ctx (n + 1) body)
        last
  | ForeachMap { key; map; body } ->
      let head =
        spf "foreach (%s in keys(%s)) {" key.x (layout_typed_p_expr ctx 0 map)
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s" head
        (mk_indent_semicolon_line (n + 1)
        @@ layout_typed_p_expr ctx (n + 1) body)
        last
  | PIf { condition; tbranch; fbranch = None } ->
      let head = spf "if (%s) {" (layout_typed_p_expr ctx 0 condition) in
      let tbranch =
        mk_indent_semicolon_line (n + 1)
        @@ layout_typed_p_expr ctx (n + 1) tbranch
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s" head tbranch last
  | PIf { condition; tbranch; fbranch = Some fbranch } ->
      let head = spf "if (%s) {" (layout_typed_p_expr ctx 0 condition) in
      let tbranch =
        mk_indent_semicolon_line (n + 1)
        @@ layout_typed_p_expr ctx (n + 1) tbranch
      in
      let mid = mk_indent n "} else {" in
      let fbranch =
        mk_indent_semicolon_line (n + 1)
        @@ layout_typed_p_expr ctx (n + 1) fbranch
      in
      let last = mk_indent n "}" in
      spf "%s\n%s%s\n%s%s" head tbranch mid fbranch last
  | PPrintf (format, es) ->
      spf "print format(\"%s\", %s)" format
        (List.split_by ", " (layout_typed_p_expr ctx 0) es)
  | PLet _ -> _die_with [%here] "unimp"

and layout_typed_p_expr ctx n { x; ty } =
  match (x, ty) with
  | PConst (PInt i), Nt.Ty_constructor (name, []) -> (
      match get_opt ctx.abstract_tyctx name with
      | None -> layout_p_expr ctx n x
      | Some (CEnumType { enum_elems; _ }) -> List.nth enum_elems i
      | _ -> layout_p_expr ctx n x)
  | _, _ -> layout_p_expr ctx n x

let layout_p_func_ ctx if_omit n { params; local_vars; body } =
  let params_str = List.split_by ", " layout_pnt_typed_var params in
  let local_vars_str =
    List.split_by ""
      (fun x ->
        mk_indent_semicolon_line (n + 1)
        @@ spf "var %s" @@ layout_pnt_typed_var x)
      local_vars
  in
  let head =
    if if_omit && List.length params == 0 then " {\n"
    else layout_pnt_typed (spf "(%s)" params_str) body.ty ^ " {\n"
  in
  let last = mk_indent_line n "}" in
  spf "%s%s%s%s" head local_vars_str
    (mk_indent_semicolon_line (n + 1) (layout_typed_p_expr ctx (n + 1) body))
    last

let layout_p_func ctx = layout_p_func_ ctx false

let layout_state_label = function
  | Hot -> "hot"
  | Cold -> "cold"
  | Start -> "start"

let layout_func_label = function
  | Plain -> "plain"
  | Entry -> "entry"
  | Exit -> "exit"
  | Listen name -> spf "on %s do" name

let layout_p_state ctx n { name; state_label; state_body } =
  let prefix = List.split_by " " layout_state_label state_label in
  let state_body_str =
    List.split_by ""
      (fun (l, f) ->
        (* let () = *)
        (*   Printf.printf "print state function %s\n" *)
        (*     (layout_p_func_ true (n + 1) f) *)
        (* in *)
        mk_indent_line (n + 1)
        @@ spf "%s %s" (layout_func_label l.x)
             (layout_p_func_ ctx true (n + 1) f))
      state_body
  in
  let head = mk_indent_line n @@ spf "%s state %s {" prefix name in
  let last = mk_indent_line n "}" in
  spf "%s%s%s" head state_body_str last

let layout_p_machine ctx n { name; local_vars; local_funcs; states } =
  let local_funcs_str =
    List.split_by ""
      (fun (x, f) ->
        (* let () = Printf.printf "print local function %s\n" x.x in *)
        mk_indent (n + 1) @@ spf "fun %s %s" x.x (layout_p_func ctx (n + 1) f))
      local_funcs
  in
  let local_vars_str =
    List.split_by ""
      (fun x ->
        mk_indent_semicolon_line (n + 1)
        @@ spf "var %s" @@ layout_pnt_typed_var x)
      local_vars
  in
  let states_str = List.split_by "" (layout_p_state ctx (n + 1)) states in
  let head = mk_indent_line n @@ spf "machine %s {" name in
  let last = mk_indent_line n "}" in
  spf "%s%s%s%s%s" head local_vars_str states_str local_funcs_str last

let layout_global_function ctx n (name, f) =
  mk_indent_line n @@ spf "fun %s %s" name.x (layout_p_func ctx n f)

let p_primitive_types = [ "tTime" ]

let layout_item ctx = function
  | PEnumDecl (name, elems) ->
      let first = spf "enum %s {" name in
      let es =
        match List.last_destruct_opt @@ List.mapi (fun i a -> (i, a)) elems with
        | None -> _die [%here]
        | Some (es, (i, e)) ->
            let es = List.map (fun (i, e) -> spf "    %s = %i," e i) es in
            let e = spf "    %s = %i" e i in
            es @ [ e ]
      in
      let last = "}" in
      String.concat "\n" ((first :: es) @ [ last ]) ^ "\n"
  | PPrimFuncDecl _ -> ""
  | PTypeDecl x ->
      if List.exists (String.equal x.x) p_primitive_types then ""
      else
        mk_indent_semicolon_line 0 @@ spf "type %s = %s" x.x (layout_pnt x.ty)
  | PEventDecl x -> (
      match x.ty with
      | Nt.Ty_unit -> mk_indent_semicolon_line 0 @@ spf "event %s" x.x
      | _ ->
          let type_name_x =
            String.mapi (fun i c -> if 0 == i then 't' else c) x.x
          in
          let str =
            mk_indent_semicolon_line 0
            @@ spf "type %s = %s" type_name_x (layout_pnt x.ty)
          in
          str ^ mk_indent_semicolon_line 0
          @@ spf "event %s: %s" x.x (layout_pnt x.ty))
  | PMachine m -> layout_p_machine ctx 0 m
  | PGlobalFunc (name, f) -> layout_global_function ctx 0 (name, f)

let layout_p_program ctx prog = List.split_by "" (layout_item ctx) prog
