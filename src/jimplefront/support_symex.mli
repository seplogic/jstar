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


val default_for : Jparsetree.j_type -> Jparsetree.name -> Expression.t
val signature2args : Jparsetree.signature -> Expression.t
val name2args : Jparsetree.name -> Expression.t
val var2args : Expression.t -> Expression.t
val negate : Jparsetree.expression -> Jparsetree.expression
val this_var_name : string
val parameter : int -> string
val mk_this : Expression.t
val make_field_signature :
  Jparsetree.class_name ->
  Jparsetree.j_type -> Jparsetree.name -> Jparsetree.signature
