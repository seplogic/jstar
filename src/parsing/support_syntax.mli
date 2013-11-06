(********************************************************
   This file is part of jStar
        src/parsing/support_syntax.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val uop_to_prover_arg : Jparsetree.unop -> string
val bop_to_prover_arg : Jparsetree.binop -> string
val bop_to_prover_pred :
  Jparsetree.binop -> Expression.t -> Expression.t -> Expression.t
val parameter : int -> string
val parameter_var : int -> Expression.t
val this_var_name : string
val this_var : Expression.t
val res_var_name : string
val res_var : Expression.t
