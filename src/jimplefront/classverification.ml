(********************************************************
   This file is part of jStar
        src/jimplefront/classverification.ml
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
open Javaspecs
open Jimple_global_types
open Printing
open Spec_def
open Support_symex
open System

module J = Jparsetree
module JG = Jimple_global_types

let is_class_abstract jimple_file =
	let Jimple_global_types.JFile(modifiers,_,_,_,_,_) = jimple_file in
	List.mem Jparsetree.Abstract modifiers

let is_interface jimple_file =
	match jimple_file with
		| Jimple_global_types.JFile(_,Jparsetree.InterfaceFile,_,_,_,_) -> true
		| _ -> false

let parent_classes_and_interfaces (jfile : Jimple_global_types.jimple_file) =
	let Jimple_global_types.JFile(_,_,_,parent_classes,parent_interfaces,_) = jfile in
	parent_classes @ parent_interfaces  (* stephan mult inh *)

let implies_opt logic f1o f2 = 
  option true (fun f1 -> Prover.is_entailment logic f1 f2) f1o

let verify_exports_implications implications logic_with_where_pred_defs = 
  List.iter
    (fun implication ->
      let name,antecedent,consequent = implication in
      if Prover.is_entailment logic_with_where_pred_defs antecedent consequent then
        (if log log_exec then printf "@{<g> OK@}: exported implication %s@." name)
      else
        printf "@{<b>NOK@}: exported implication %s@." name)
    implications

(* Check both proof obligations (Implication and Parent consistency) for each axiom in 'implications'. *)
let verify_axioms_implications class_name jimple_file implications axiom_map logic =
  let abstract_class_or_interface =
    is_class_abstract jimple_file || is_interface jimple_file in
  let parents = parent_classes_and_interfaces jimple_file in
  let conjunct = Jlogic.mk_type Support_syntax.this_var class_name in
  List.iter (fun implication ->
      let name,antecedent,consequent = implication in
      (* We first tackle the Implication proof obligation if the class is not abstract or an interface. *)
      if not abstract_class_or_interface then (
        let antecedent =
          Expression.mk_star conjunct antecedent in
        let m = sprintf "implication verification of axiom %s" name in
        if Prover.is_entailment logic antecedent consequent then
          (if log log_logic then printf "@{<g> OK@}: %s@." m)
        else
          printf "@{<b>NOK@}: %s@." m);
      (* Then we tackle the Parent consistency proof obligation *)
      List.iter (fun parent ->
          let parent_name = (Pprinter.class_name2str parent) in
          try
            let p_antecedent,p_consequent =
              AxiomMap.find (parent,name) axiom_map in
            (* We must verify
                 (antecedent=>consequent) => (p_antecedent=>p_consequent)
               which is equivalent to
                 (p_antecedent => p_consequent) \/
                 ((p_antecedent => antecedent) /\ (consequent => p_consequent))
             *)
            let m =
              sprintf "axiom %s consistent with parent %s" name parent_name in
            if Prover.is_entailment logic p_antecedent p_consequent ||
                (Prover.is_entailment logic p_antecedent antecedent &&
                Prover.is_entailment logic consequent p_consequent) then
              (if log log_logic then printf "@{<g>OK@}: %s@." m)
            else
              (* Note that P\/Q may be valid even if P and Q are not! *)
              (* TODO(rgrig): Try to not approximate the condition. *)
              printf "@{<b>POSSIBLY NOK@}: %s@." m;
          with Not_found -> () (* TODO(rgrig): Should this print something? *)
      ) parents
  ) implications



let verify_methods_dynamic_dispatch_behavioral_subtyping_inheritance
  j_of_cname
  sspecs dspecs
  logic
  abslogic : unit =

  (* TODO: Each method has sspec. *)
  (* TODO: Each method has body iff has dspec. *)

  (* Check: If a method has dspec, then it refines sspec. *)
  prof_phase "dynamic vs static spec check";
  let d_refines_s msig (ds, dsp) =
    let cname, _, mname, _ = msig in
    let ss, _ =
      (try MethodMap.find msig sspecs with Not_found -> assert false) in
    if Javaspecs.refines_this cname logic ss ds then (
      if log log_exec then
        fprintf logf "Dynamic and static specs of %a are consistent.@."
            Jparsetree.pp_name mname)
    else
      (let et =
        sprintf "Dynamic and static specs of %s disagree."
          (Pprinter.name2str mname) in
      printf "@{<b>WARNING@}: %s@." et; pp_json_location_opt dsp et "") in
  MethodMap.iter d_refines_s dspecs;

  (* If a method has sspec, then it must refine each sspec of methods that
  it overrides. *)
  prof_phase "static spec inheritance check";
  let s_refines_ancestors msig (ss, ss_pos) =
    let seen = HashSet.create 0 in
    let check (cnc, (sc, _)) (cnp, (sp, sp_pos)) =
      let _, _, mn, _ = msig in
      if Javaspecs.refines logic sc sp then (
        if log log_exec then
          fprintf logf "OK: %a#%a <: %a#%a@."
              Jparsetree.pp_class_name cnc
              Jparsetree.pp_name mn
              Jparsetree.pp_class_name cnp
              Jparsetree.pp_name mn)
      else
        let et = sprintf "%s#%s not <: %s#%s"
          (Pprinter.class_name2str cnc) (Pprinter.name2str mn)
          (Pprinter.class_name2str cnp) (Pprinter.name2str mn) in
        (printf "@{<b>WARNING@}: %s@." et; pp_json_location_opt sp_pos et "") in
    let rec dfs cn =
      let parents = try
          let j = Hashtbl.find j_of_cname cn in
          parent_classes_and_interfaces j
        with Not_found -> (eprintf "@[<2>@{<b>WARNING@}: Class %a is missing,@ \
          so I don't know what it extends/implements.@ I'm assuming nothing.@."
          J.pp_class_name cn; []) in
      let s_refines parent =
        if not (HashSet.mem seen parent) then begin
          HashSet.add seen parent;
          let msig_p = (let _, b, c, d = msig in (parent, b, c, d)) in
          try check (cn, (ss, ss_pos)) (parent, MethodMap.find msig_p sspecs)
          with Not_found -> dfs parent
        end in
      List.iter s_refines parents in
    let cn, _, _, _ = msig in
    dfs cn in
  MethodMap.iter s_refines_ancestors sspecs


let compile_jimple js specs logic abs =
  prof_phase "split specs";
  let sspecs, dspecs = Javaspecs.spec_file_to_method_specs specs in
  let convert_spec (spec, l) = (Core.TripleSet.of_list spec, l) in
  let sspecs_inner = Javaspecs.MethodMap.map convert_spec sspecs in
  let dspecs_inner = Javaspecs.MethodMap.map convert_spec dspecs in
  prof_phase "init spec checks";
  let j_by_name =
    Misc.hash_of_list
      (fun x->x)
      (fun _ _ -> failwith "Duplicated class.") (* TODO(rgrig): nicer error/exc *)
      (function (JG.JFile (_,_,cn,_,_,_)) -> Some cn)
      (fun x-> Some x)
      js in
  verify_methods_dynamic_dispatch_behavioral_subtyping_inheritance
    j_by_name
    sspecs_inner
    dspecs_inner
    logic
    abs;
  prof_phase "actual compile jimple -> core";
  Translatejimple.compile (Hashtbl.find j_by_name) js sspecs dspecs
