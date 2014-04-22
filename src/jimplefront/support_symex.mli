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


val default_for : Jparsetree.j_type -> Jparsetree.name -> Z3.Expr.expr
val signature2args : Jparsetree.signature -> Z3.Expr.expr
val name2args : Jparsetree.name -> Z3.Expr.expr
val var2args : Z3.Expr.expr -> Z3.Expr.expr
val negate : Jparsetree.expression -> Jparsetree.expression
val make_field_signature :
  Jparsetree.class_name ->
  Jparsetree.j_type -> Jparsetree.name -> Jparsetree.signature
