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

type fldlist = (string * Expression.t) list

type methodspec =
    Dynamic of Jparsetree.method_signature_short * Core.triple list *
      Printing.source_location option
  | Static of Jparsetree.method_signature_short * Core.triple list *
      Printing.source_location option
type methodspecs = methodspec list
type apf_define = string * Vars.var * fldlist * Expression.t * bool
type apf_defines = apf_define list
type named_implication = string * Expression.t * Expression.t
type exportLocal_predicate = string * Vars.var list * Expression.t
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
val pp_class_spec : Format.formatter -> class_spec -> unit
