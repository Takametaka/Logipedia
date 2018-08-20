open Basic
open Term
open Entry
open Parser
open Rule
open Ast
open Coq
open Matita
open Lean
open Pvs

let err_msg fmt =
  Format.eprintf "%s" ("\027[31m" ^ "ERROR" ^ "\027[m");
  Format.eprintf fmt

let system : Systems.system ref = ref (Export.(`Pvs))

let set_export s =
  let open Export in
  system := Systems.system_of_string s

let handle_entry md e =
  match e with
  | Decl (lc, id, st, ty) -> (
    match Env.declare lc id st ty with
    | OK () -> Compile.compile_declaration (mk_name md id) ty
    | Err e -> Errors.fail_env_error e )
  | Def (lc, id, opaque, Some ty, te) -> (
      let define = if opaque then Env.define_op else Env.define in
      match define lc id te (Some ty) with
      | OK () -> Compile.compile_definition (mk_name md id) ty te
      | Err e -> Errors.fail_env_error e )
  | Def _ -> failwith "Definition without types are not supported"
  | Rules _ -> failwith "Rules are not part of the sttforall logic"
  | _ -> failwith "Commands are not supported"

let handle_entry_dep md e =
  match e with
  | Decl (lc, id, st, ty) -> (
    match Env.declare lc id st ty with
    | OK () -> Sttfa.compile_declaration (mk_name md id) ty
    | Err e -> Errors.fail_env_error e )
  | Def (lc, id, opaque, Some ty, te) -> (
      let define = if opaque then Env.define_op else Env.define in
      match define lc id te (Some ty) with
      | OK () -> Sttfa.compile_definition (mk_name md id) ty te
      | Err e -> Errors.fail_env_error e )
  | Def _ -> failwith "Definition without types are not supported"
  | Rules _ -> failwith "Rules are not part of the sttforall logic"
  | _ -> failwith "Commands are not supported"

let export_file file ast system =
  let basename = try Filename.chop_extension file with _ -> file in
  let (module M:Export.E) = Export.of_system system in
  let stt_file = basename ^ "." ^ M.extension in
  let oc = open_out stt_file in
  let fmt = Format.formatter_of_out_channel oc in
  M.print_ast fmt basename ast ;
  close_out oc

let run_on_file to_bdd file =
  let md = Env.init file in
  Confluence.initialize () ;
  let input = open_in file in
    let entries = Parser.parse_channel md input in
    close_in input ;
    begin
      let items = List.map (handle_entry md) entries in
      let dep = List.fold_left
          (fun dep e -> QSet.union dep (Dep.dep_of_entry md e)) QSet.empty entries in
      let ast = {md = string_of_mident md; dep; items} in
      Confluence.finalize () ;
      if not (Env.export ()) then
        Errors.fail dloc "Fail to export module '%a'." pp_mident md;
      let (module M:Export.E) = Export.of_system !system in
      if !system <> `Sttfa then
        export_file file ast !system;
      begin
        if to_bdd then
          if !system = `Sttfa then
            begin
              let md = Env.init file in
              List.iter (handle_entry_dep md) entries
            end
          else
            M.print_bdd ast
      end;
    end

let _ =
  let to_bdd = ref false in
  let options =
    Arg.align
      [ ("-I", Arg.String Basic.add_path, " Add folder to Dedukti path") ;
        ("--export", Arg.String set_export, " Set exporting system") ;
        ("--export-bdd", Arg.Set to_bdd, " Set bdd") ;
      ]
  in
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [OPTION]... [FILE]...\n" in
  let usage = usage ^ "Available options:" in
  let files =
    let files = ref [] in
    Arg.parse options (fun f -> files := f :: !files) usage ;
    List.rev !files
  in
  try List.iter (run_on_file !to_bdd) files with
  | Parse_error (loc, msg) ->
    let l, c = of_loc loc in
    err_msg "Parse error at (%i,%i): %s@." l c msg ;
    exit 1
  | Failure err ->
      err_msg "Failure: %s@." err;
      exit 2
  | Sys_error err ->
      err_msg "System error: %s@." err;
      exit 3
  | Exit -> exit 4