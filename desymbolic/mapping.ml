open Zutils
open Prop
open Zdatatype
open Myconfig
open Head

let __log = _log "desym_mapping"

module Predictable = struct
  type lit = Nt.t Prop.lit
  type prop = Nt.t Prop.prop

  let mk_true = mk_true
  let mk_false = mk_false
  let mk_lit lit = Lit lit #: Nt.Ty_bool
  let mk_ite cond bencht benchf = Ite (Lit cond #: Nt.Ty_bool, bencht, benchf)
  let mk_and = smart_add_to
  let mk_or l1 l2 = smart_or [ l1; l2 ]
  let mk_not p = Not p
  let layout_lit = layout_lit
  let layout_prop = layout_prop
end

module DT = Dtree.Dt.F (Predictable)

type mt_tabs = (int * (Nt.t lit, bool) Hashtbl.t) list

type all_mt_tabs = {
  global_tab : mt_tabs;
  local_tabs : mt_tabs StrMap.t IntMap.t;
}

type all_dt = { global_dt : DT.t; local_dts : DT.t StrMap.t IntMap.t }

let all_to_tab { global_features; local_features } { global_dt; local_dts } =
  let global_tab = DT.dt_to_paths (global_features, global_dt) in
  let local_tabs =
    IntMap.map
      (fun m ->
        StrMap.mapi
          (fun op x ->
            let local_feature = StrMap.find "all_to_tab" local_features op in
            DT.dt_to_paths (snd local_feature, x))
          m)
      local_dts
  in
  (* let local_tabs = IntMap.to_value_list local_tabs in *)
  { global_tab; local_tabs }

let tab_to_prop tab =
  let res =
    Hashtbl.fold
      (fun lit b res ->
        let lit = lit #: Nt.Ty_bool in
        if b then Lit lit :: res else Not (Lit lit) :: res)
      tab []
  in
  smart_and res

let print_opt_stat (num, test_num) features =
  let total_fv = Sugar.pow 2 (Array.length features) in
  __log @@ fun _ ->
  Printf.printf "valid(%i/%i); cost(%i/%i = %f)\n" num total_fv test_num
    total_fv
    (float_of_int test_num /. float_of_int total_fv)

let print_local_fv gidx (op, features) l =
  List.iter
    (fun (idx, tab) ->
      let pos, neg =
        Array.fold_left
          (fun (pos, neg) lit ->
            if Hashtbl.find tab lit then (lit :: pos, neg) else (pos, lit :: neg))
          ([], []) features
      in
      let () =
        __log @@ fun _ ->
        Printf.printf "%s_%i_%i:: POS [%s]  NEG [%s]\n" op gidx idx
          (List.split_by_comma layout_lit pos)
          (List.split_by_comma layout_lit neg)
      in
      ())
    l

let print_global_fv features l =
  List.iter
    (fun (idx, tab) ->
      let pos, neg =
        Array.fold_left
          (fun (pos, neg) lit ->
            if Hashtbl.find tab lit then (lit :: pos, neg) else (pos, lit :: neg))
          ([], []) features
      in
      let () =
        __log @@ fun _ ->
        Printf.printf "global_%i:: POS [%s]  NEG [%s]\n" idx
          (List.split_by_comma layout_lit pos)
          (List.split_by_comma layout_lit neg)
      in
      ())
    l

let mk_mt_tab sat_solver { global_features; local_features } =
  (* let local_features_array = *)
  (*   StrMap.map (fun (_, features) -> Array.of_list features) local_features *)
  (* in *)
  let () =
    __log @@ fun _ ->
    Printf.printf "[Global DT]:\n";
    Head.pprint_tab global_features
  in
  let test_num, global_dt =
    DT.init_pruned_dt (fun prop -> sat_solver ([], prop)) global_features
  in
  let global_tab = DT.dt_to_paths (global_features, global_dt) in
  let () =
    __log @@ fun _ ->
    Printf.printf "[Global DT]\n";
    print_opt_stat (List.length global_tab, test_num) global_features
  in
  let () = print_global_fv global_features global_tab in
  let local_dts =
    StrMap.mapi
      (fun op (vs, features) ->
        let () =
          __log @@ fun _ ->
          Printf.printf "[%s DT]:\n" op;
          Head.pprint_tab features
        in
        let test_num, dt =
          DT.init_pruned_dt (fun prop -> sat_solver (vs, prop)) features
        in
        let () =
          __log @@ fun _ ->
          Printf.printf "[%s DT]\n" op;
          print_opt_stat (0, test_num) features
        in
        (vs, dt))
      local_features
  in
  let dts =
    List.map
      (fun (idx, tab) ->
        let prop = tab_to_prop tab in
        let dts =
          StrMap.mapi
            (fun op (vs, dt) ->
              let features = snd @@ StrMap.find "mk_mt_tab" local_features op in
              let () =
                __log @@ fun _ ->
                Printf.printf "[Refine %s DT] [Under]:%s\n" op
                  (layout_prop prop);
                Head.pprint_tab features
              in
              let test_num, dt =
                DT.refine_dt_under_prop
                  (fun local_prop -> sat_solver (vs, local_prop))
                  prop (features, dt)
              in
              let dt = DT.dt_to_paths (features, dt) in
              let () =
                __log @@ fun _ ->
                Printf.printf "[Refine %s DT]\n" op;
                print_opt_stat (List.length dt, test_num) features
              in
              let () = print_local_fv 0 (op, features) dt in
              dt)
            local_dts
        in
        (idx, tab, dts))
      global_tab
  in
  dts

let get_local_prop features local_m id =
  let tab = IntMap.of_seq @@ List.to_seq local_m in
  let path = IntMap.find "die" tab id in
  let bl = DT.path_to_pos features path in
  smart_and
  @@ List.mapi
       (fun idx b ->
         let p = Lit features.(idx) #: Nt.Ty_bool in
         if b then p else Not p)
       bl

let mk_simp_local_prop features local_m ids =
  let tab = IntMap.of_seq @@ List.to_seq local_m in
  let paths = List.map (IntMap.find "die" tab) ids in
  match Array.length features with
  | 0 -> (
      match paths with
      | [] -> mk_false
      | _ ->
          mk_true
          (* _die_with [%here] *)
          (* (spf "len(paths) = %i" (List.length paths)) *))
  | _ -> DT.classify_as_prop features (List.map (DT.path_to_pos features) paths)
