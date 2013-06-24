(********************************************************
   This file is part of jStar
        src/jimplefront/jstar.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Debug
open Format

(* TODO(rgrig): Don't open these. *)
open Jparsetree
open Jimple_global_types
open Psyntax

module J = Jparsetree
module JG = Jimple_global_types
module PA = ParserAst
module PS = Psyntax

let program_file_name = ref ""
let logic_file_name = ref "logic"
let spec_file_name = ref "specs"
let absrules_file_name = ref "abs"
let eclipse_mode = ref false
let specs_template_mode = ref false

let jimple_files = ref []
let topl_files = ref []
let spec_files = ref [] (* TODO(rgrig): Not used yet, but should. *)
let rule_files = ref [] (* TODO(rgrig): Not used yet, but should. *)
let set_file fn =
  let ts =
    [ ".jimple", jimple_files
    ; ".topl", topl_files
    ; ".spec", spec_files
    ; ".rules", rule_files ] in
  let rec record = function
    | [] -> eprintf "@[@{<b>WARNING@}: %s has unknown extension. Ignoring.@." fn
    | (suffix, ref) :: ts ->
        if Filename.check_suffix fn suffix then ref =:: fn else record ts in
  record ts

let arg_list =
  Config.args_default
  @ [ "-a", Arg.Set_string absrules_file_name, "abstraction rules file"
    ; "-e", Arg.Set eclipse_mode, "run in eclipse"
    ; "-l", Arg.Set_string logic_file_name, "logic file"
    ; "-s", Arg.Set_string spec_file_name, "specs file"
    ; "-t", Arg.Set specs_template_mode, "create empty specs template" ]
let () = Config.check_arg_specs arg_list


let parse_program program_file_name =
  let ch =
    try
      open_in program_file_name
    with Sys_error s -> failwith s in
  let program = Jparser.file Jlexer.token (Lexing.from_channel ch) in
  close_in_noerr ch;
  program

(* After ‘new’, replace ‘specialinvoke’ (of ‘<init>’) by ‘virtualinvoke’. *)
(* PRE: Assumes that ‘specialinvoke’s come immediately after ‘new’. *)
let preprocess_jimple (JFile (a, b, c, d, e, f)) =
  let statements = function
    | JG.DOS_stm (JG.Assign_stmt (x, J.New_simple_exp y), _) as new_
      :: JG.DOS_stm
        ( JG.Invoke_stmt
          ( J.Invoke_nostatic_exp
            ( J.Special_invoke
            , b
            , ((J.Method_signature (c1, c2, J.Identifier_name "<init>", c4))
              as c)
            , d))
        , p2)
      :: _
      ->
        assert (x = J.Var_name b && y = J.Class_name c1);
        [ new_
        ; JG.DOS_stm
          ( JG.Invoke_stmt (J.Invoke_nostatic_exp (J.Virtual_invoke, b, c, d))
          , p2) ]
    | JG.DOS_stm
      ( JG.Invoke_stmt (J.Invoke_nostatic_exp (J.Special_invoke, _, _, _))
      , _) :: _ -> []
    | x :: _ -> [x]
    | [] -> [] in
  let body = option_map (fun (xs, b) -> (tails xs >>= statements, b)) in
  let member = function
    | JG.Method (a, b, c, d, e, f, g, h, i)
        -> JG.Method (a, b, c, d, e, body f, List.map body g, body h, body i)
    | x -> x in
  JG.JFile (a, b, c, d, e, List.map member f)

let make_logic_for_one_program spec_list logic program =
       let Jimple_global_types.JFile(_,_,class_name,_,_,_) = program in
       let logic = Javaspecs.augmented_logic_for_class class_name spec_list logic in
       let logic = Javaspecs.add_common_apf_predicate_rules spec_list logic in
       (* Axioms use the "subtype" and "objsubtype" relation - see jlogic.ml *)
       let logic = Javaspecs.add_subtype_and_objsubtype_rules spec_list logic in

       (* Exports clause treatment *)
       let (logic_with_where_pred_defs,implications) = Javaspecs.logic_and_implications_for_exports_verification class_name spec_list logic in
       if safe then
	 Classverification.verify_exports_implications
	     implications
	     (Sepprover.convert_logic logic_with_where_pred_defs);
	 (* Since where predicates are local to the exports clause, we discard them after exports clause verification *)

       let logic = Javaspecs.add_exported_implications_to_logic spec_list logic in
       if log log_logic then (
	 fprintf
	    logf
	    "@[<2>Augmented logic sequent rules%a@."
	    (pp_list Psyntax.pp_sequent_rule) logic.seq_rules);
       (* End of exports clause treatment *)

       (* Axioms clause treatment *)
       let axiom_map = Javaspecs.spec_file_to_axiom_map spec_list in
       let implications = Javaspecs.implications_for_axioms_verification class_name axiom_map in
       if safe then
	 Classverification.verify_axioms_implications
	    class_name
	    program
	    implications
	    axiom_map
	    (Sepprover.convert_logic logic);
       let logic = Javaspecs.add_axiom_implications_to_logic spec_list logic in
       logic
       (*let _ = Prover.pprint_sequent_rules logic in*)
       (* End of axioms clause treatment *)


let main () =
  let usage_msg =
    Printf.sprintf "usage: %s [options] <jimple_programs>" Sys.argv.(0) in
  Arg.parse arg_list set_file usage_msg;
  if !Config.verbosity >= 2 then
    printf "@[Files to analyze: %a@." (pp_list_sep " " pp_string) !jimple_files;

  prof_phase "parse_program jimple";
  let programs = List.map parse_program !jimple_files in
  prof_phase "preprocess_jimple";
  let programs = List.map preprocess_jimple programs in
  if !specs_template_mode then begin
    if log log_phase then
      fprintf logf "@[<4>Creating empty specs template for class@.@.";
    List.iter Mkspecs.print_specs_template programs
  end else (
    if !Config.smt_run then Smt.smt_init();
    (* Load abstract interpretation plugins *)
    List.iter (fun file_name -> Plugin_manager.load_plugin file_name) !Config.abs_int_plugins;

    let parse x fn = System.parse_file Parser.file Lexer.token fn x in
    let add_rule logic = function
      | PA.Rule r -> PS.add_rule logic r
      | _ -> failwith "INTERNAL" in
    prof_phase "parse rules";
    let logic =
      List.fold_left add_rule PS.empty_logic
        (Load.load ~path:Cli_utils.logic_dirs (parse "logic") !logic_file_name)
    in
    let abs_rules =
      List.fold_left add_rule PS.empty_logic
        (Load.load ~path:Cli_utils.abs_dirs (parse "abs") !absrules_file_name)
    in
    let parse fn =
      System.parse_file Jparser.spec_file Jlexer.token fn "specs" in
    prof_phase "parse specs";
    let specs =
      Load.load ~path:Cli_utils.specs_dirs parse !spec_file_name in
    prof_phase "synthesize rules from program";
    let logic =
      List.fold_left (make_logic_for_one_program specs) logic programs in
    prof_phase "init compile jimple -> core";
    let logic_inner = Sepprover.convert_logic logic in
    let abs_rules_inner = Sepprover.convert_logic abs_rules in
    let cores = Classverification.compile_jimple programs specs logic_inner abs_rules_inner in
    prof_phase "topl preprocessing";
    let cores = ToplPreprocessor.instrument_procedures cores in
    let topls = ToplPreprocessor.read_properties !topl_files in
    let topls = List.map ToplPreprocessor.parse_values topls in
    let topl_monitor = ToplPreprocessor.compile programs topls in
    let question =
      { Core.q_procs = topl_monitor @ cores
      ; q_rules = logic
      ; q_infer = !Config.use_abduction
      ; q_name = "jstar_question_for_corestar" } in
    prof_phase "symbolic execution";
    if Symexec.verify question
    then printf "@[@{<g> OK@}@."
    else printf "@[@{<b>NOK@}@.";
    prof_phase "shutting down")

let () =
  System.set_signal_handlers ();
  let mf = {
    mark_open_tag = (function
      | "b" -> System.terminal_red (* bad *)
      | "g" -> System.terminal_green (* good *)
      | _ -> assert false);
    mark_close_tag = (fun _ -> System.terminal_white);
    print_open_tag = (fun _ -> ());
    print_close_tag = (fun _ -> ())} in
  set_formatter_tag_functions mf;
  pp_set_formatter_tag_functions err_formatter mf;
  set_tags true; pp_set_tags err_formatter true;
  (*try*) main ()
  (*with Failure s -> eprintf "@{<b>FAILED:@} %s@." s*)
