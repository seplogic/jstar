(********************************************************
   This file is part of jStar
        src/jimple_syntax/spec_def.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

type fldlist = (string * Z3.Expr.expr) list

type methodspec =
    Dynamic of Jparsetree.method_signature_short * Core.triple list *
      Printing.source_location option
  | Static of Jparsetree.method_signature_short * Core.triple list *
      Printing.source_location option
type methodspecs = methodspec list
type apf_define = string * Z3.Expr.expr * fldlist * Z3.Expr.expr * bool
type apf_defines = apf_define list
type named_implication = string * Z3.Expr.expr * Z3.Expr.expr
type exportLocal_predicate = string * Z3.Expr.expr list * Z3.Expr.expr
type exports_clause =
    (named_implication list * exportLocal_predicate list) option
type axioms_clause = named_implication list option
type class_spec = {
  class_or_interface : Jparsetree.j_file_type;
  classname : Jparsetree.class_name;
  extends : Jparsetree.extends_clause;
  implements : Jparsetree.implements_clause;
  apf : apf_defines;
  exports : exports_clause;
  axioms : axioms_clause;
  methodspecs : methodspecs;
}
val pp_class_spec : class_spec pretty_printer
