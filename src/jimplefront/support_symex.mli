(********************************************************
   This file is part of jStar
        src/jimplefront/support_symex.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val default_for : Jparsetree.j_type -> Jparsetree.name -> Expression.t (* Psyntax.args *)
val signature2args : Jparsetree.signature -> Expression.t (* Psyntax.args *)
val name2args : Jparsetree.name -> Expression.t (* Psyntax.args *)
val variable2var : Jparsetree.variable -> Vars.var
val var2args : Vars.var -> Expression.t (* Psyntax.args *)
val negate : Jparsetree.expression -> Jparsetree.expression
val this_var_name : string
val parameter : int -> string
val mk_this : Vars.var
val make_field_signature :
  Jparsetree.class_name ->
  Jparsetree.j_type -> Jparsetree.name -> Jparsetree.signature
