include RegexAst
include Frontend
include Basic_typing
include Character
include Alphabet
include Regex
(* open Zutils *)

(* let _ctxs = ref None *)
(* let _log = Myconfig._log_preprocess *)
(* let predefined_files = [ "basic_typing.ml" ] *)

(* let load_ctxs () = *)
(*   match !_ctxs with *)
(*   | Some ctxs -> ctxs *)
(*   | None -> *)
(*       let prim_path = Myconfig.get_prim_path () in *)
(*       let items = *)
(*         List.concat_map *)
(*           (fun file -> parse_plang (spf "%s/%s" prim_path.predefined_path file)) *)
(*           predefined_files *)
(*       in *)
(*       let decls, items = Type_alias.item_inline [] items in *)
(*       let bctx, _ = p_items_type_check mk_basic_typing_ctx items in *)
(*       let res = (decls, bctx) in *)
(*       _ctxs := Some res; *)
(*       res *)

(* let load_bctx () = *)
(*   let _, bctx = load_ctxs () in *)
(*   bctx *)

(* let load_alias () = *)
(*   let alias, _ = load_ctxs () in *)
(*   alias *)

(* let preproress (alias, event_ctx, ctx) source_file = *)
(*   let items = parse_plang source_file in *)
(*   let _, items = Type_alias.item_inline (load_alias ()) items in *)
(*   let bctx, items = p_items_type_check (load_bctx ()) items in *)
(*   (\* let () = *\) *)
(*   (\*   Pp.printf "@{<bold>alias:@}\n%s\n" (Type_alias.layout_alias (load_alias ())) *\) *)
(*   (\* in *\) *)
(*   (\* let () = _die [%here] in *\) *)
(*   (bctx, items) *)
