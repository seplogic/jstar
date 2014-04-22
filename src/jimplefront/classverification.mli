(********************************************************
   This file is part of jStar
        src/jimplefront/classverification.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val is_interface : Jimple_global_types.jimple_file -> bool
val parent_classes_and_interfaces :
  Jimple_global_types.jimple_file -> Jparsetree.class_name list
val verify_exports_implications :
  (string * Z3.Expr.expr * Z3.Expr.expr) list -> Calculus.t -> unit
val verify_axioms_implications :
  Jparsetree.class_name ->
  Jimple_global_types.jimple_file ->
  (string * Z3.Expr.expr * Z3.Expr.expr) list ->
  (Z3.Expr.expr * Z3.Expr.expr) Javaspecs.AxiomMap.t -> Calculus.t -> unit
val compile_jimple :
  Jimple_global_types.jimple_file list (* jimples *)
    -> Spec_def.class_spec list (* specs *)
    -> Calculus.t (* logic *)
    -> Abstraction.t (* abs *)
    -> Core.ast_procedure list
