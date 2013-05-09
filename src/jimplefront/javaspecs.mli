(********************************************************
   This file is part of jStar
        src/jimplefront/javaspecs.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val append_rules :
  Psyntax.logic -> Psyntax.sequent_rule list -> Psyntax.logic
val apf :
  string -> Vars.var -> (string * Psyntax.args) list -> Psyntax.pform_at list
val augmented_logic_for_class :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val remove_duplicates : 'a list -> 'a list
val parent_classes_and_interfaces :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Jparsetree.class_name list
val logic_with_where_pred_defs :
  (string * Psyntax.VarMap.key list * Psyntax.pform) list ->
  Psyntax.logic -> Psyntax.logic
val logic_and_implications_for_exports_verification :
  Jparsetree.class_name ->
  Spec_def.class_spec list ->
  Psyntax.logic -> Psyntax.logic * Spec_def.named_implication list
val add_exported_implications_to_logic :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
module AxiomMap : Map.S with type key = Jparsetree.class_name * string
type axiom_map = (Psyntax.pform * Psyntax.pform) AxiomMap.t
val spec_file_to_axiom_map :
  Spec_def.class_spec list -> (Psyntax.pform * Psyntax.pform) AxiomMap.t
val implications_for_axioms_verification :
  Jparsetree.class_name ->
  (Psyntax.pform * Psyntax.pform) AxiomMap.t ->
  Spec_def.named_implication list
module AxiomMap2 : Map.S with type key = Jparsetree.class_name
type axiom_map2 = Spec_def.named_implication list AxiomMap2.t
val add_axiom_implications_to_logic :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val is_interface : Jparsetree.class_name -> Spec_def.class_spec list -> bool
module MethodMap : Map.S with type key = Jparsetree.method_signature
module MethodSet : Set.S with type elt = Jparsetree.method_signature
type methodSpecs = (Core.ast_triple * Printing.source_location option) MethodMap.t
val emptyMSpecs : methodSpecs
val spec_list_to_spec : Core.ast_triple list -> Core.ast_triple
val spec_file_to_method_specs :
  Spec_def.class_spec list -> methodSpecs * methodSpecs
val add_common_apf_predicate_rules :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val add_subtype_and_objsubtype_rules :
  Spec_def.class_spec list -> Psyntax.logic -> Psyntax.logic
val refinement_this :
  Psyntax.logic
  -> Core.ast_triple
  -> Core.ast_triple
  -> Jparsetree.class_name
  -> bool
