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
  Calculus.t -> Calculus.t -> Calculus.t
val apf :
  string -> Z3.Expr.expr -> (string * Z3.Expr.expr) list -> Z3.Expr.expr
val augmented_logic_for_class :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Calculus.t -> Calculus.t
val remove_duplicates : 'a list -> 'a list
val parent_classes_and_interfaces :
  Jparsetree.class_name ->
  Spec_def.class_spec list -> Jparsetree.class_name list
val logic_with_where_pred_defs :
  (string * Corestar_std.StringMap.key list * Z3.Expr.expr) list ->
  Calculus.t -> Calculus.t
val logic_and_implications_for_exports_verification :
  Jparsetree.class_name ->
  Spec_def.class_spec list ->
  Calculus.t -> Calculus.t * Spec_def.named_implication list
val add_exported_implications_to_logic :
  Spec_def.class_spec list -> Calculus.t -> Calculus.t
module AxiomMap : Map.S with type key = Jparsetree.class_name * string
type axiom_map = (Z3.Expr.expr * Z3.Expr.expr) AxiomMap.t
val spec_file_to_axiom_map :
  Spec_def.class_spec list -> (Z3.Expr.expr * Z3.Expr.expr) AxiomMap.t
val implications_for_axioms_verification :
  Jparsetree.class_name ->
  (Z3.Expr.expr * Z3.Expr.expr) AxiomMap.t ->
  Spec_def.named_implication list
module AxiomMap2 : Map.S with type key = Jparsetree.class_name
type axiom_map2 = Spec_def.named_implication list AxiomMap2.t
val add_axiom_implications_to_logic :
  Spec_def.class_spec list -> Calculus.t -> Calculus.t
val is_interface : Jparsetree.class_name -> Spec_def.class_spec list -> bool
module MethodMap : Map.S with type key = Jparsetree.method_signature
module MethodSet : Set.S with type elt = Jparsetree.method_signature
type methodSpecs
  = (Core.triple list * Printing.source_location option) MethodMap.t
val emptyMSpecs : methodSpecs
val spec_file_to_method_specs :
  Spec_def.class_spec list -> methodSpecs * methodSpecs
val add_common_apf_predicate_rules :
  Spec_def.class_spec list -> Calculus.t -> Calculus.t
val add_subtype_and_objsubtype_rules :
  Spec_def.class_spec list -> Calculus.t -> Calculus.t
val refines
  : Calculus.t
  -> Core.spec
  -> Core.spec
  -> bool
val refines_this
  : Jparsetree.class_name
  -> Calculus.t
  -> Core.spec
  -> Core.spec
  -> bool
