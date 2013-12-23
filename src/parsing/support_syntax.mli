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

val mk_1 : Jparsetree.unop -> Expression.t -> Expression.t
val mk_2 : Jparsetree.binop -> Expression.t -> Expression.t -> Expression.t

val mk_succ : Expression.t -> Expression.t

val this_var_name : string
val this_var : Expression.t
