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

val mk_1 : Jparsetree.unop -> Z3.Expr.expr -> Z3.Expr.expr
val mk_2 : Jparsetree.binop -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr

val mk_succ : Z3.Expr.expr -> Z3.Expr.expr

val this_var_name : string
val this_var : Z3.Expr.expr
