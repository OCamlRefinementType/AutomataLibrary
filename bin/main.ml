open AutomataLibrary
open Core
open Zutils

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let inv =
  "(starA (anyA - Req (id == lc));\n\
  \   Req (id == lc);\n\
  \   starA (anyA - Req (id == lc)))\n\
  \  || starA (anyA - Req (id == lc))"

let raw_to_ctx l =
  Typectx.ctx_from_list
  @@ List.map
       ~f:(fun x ->
         x.x#:(Nt.core_type_to_t @@ OcamlParser.Oparse.parse_core_type x.ty))
       l

let test () =
  let ctx = raw_to_ctx [ "=="#:"'a -> 'a -> bool"; "lc"#:"machine" ] in
  let event_ctx =
    raw_to_ctx [ "req"#:"<id: machine>"; "rsp"#:"<id: machine>" ]
  in
  let sfa =
    rich_symbolic_regex_of_expr @@ OcamlParser.Oparse.parse_expression inv
  in
  let sfa = rich_symbolic_regex_type_check event_ctx ctx sfa in
  let () = Pp.printf "@{<bold>sfa:@}\n%s\n" (layout_rich_symbolic_regex sfa) in
  let ectx =
    List.map ~f:(fun x -> mk_top_sevent [%here] x.x x.ty)
    @@ Typectx.ctx_to_list event_ctx
  in
  let sfa = rich_regex_desugar (Ctx { atoms = ectx; body = sfa }) in
  let () = Pp.printf "@{<bold>sfa:@}\n%s\n" (layout_rich_symbolic_regex sfa) in
  let sfa = SFA.rich_regex_to_regex sfa in
  let () = Pp.printf "@{<bold>sfa:@}\n%s\n" (SFA.layout_regex sfa) in
  let dfa = SFA.minimize @@ SFA.compile_regex_to_dfa sfa in
  let reg = SFA.dfa_to_reg dfa in
  let () = Pp.printf "@{<bold>reg:@}\n%s\n" (SFA.layout_regex reg) in
  let res = SFA.display_dfa @@ SFA.minimize @@ SFA.compile_regex_to_dfa sfa in
  ()

let inline () =
  let _ = SFA.inline_test () in
  ()

let zero_param message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        in
        let () = Myconfig.meta_config_path := config_file in
        f)
  in
  (message, cmd)

let one_param_file message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        and source_file = anon ("source_code_file" %: regular_file) in
        let () = Myconfig.meta_config_path := config_file in
        f source_file)
  in
  (message, cmd)

let commands =
  Command.group ~summary:"Poirot"
    [
      (* one_param_file "test" test; *)
      zero_param "test" test;
      zero_param "inline" inline;
      zero_param "qcheck" (fun () ->
          let b = QcFa.testcase in
          ())
      (* one_param_file "type-check" type_check; *);
    ]

let () = Command_unix.run commands

(* QcFa.testcase () *)
