(********************************************************
   This file is part of jStar
        src/jimplefront/jlogic.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val class2args : Jparsetree.class_name -> Z3.Expr.expr 
val mk_pointsto : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_static_pointsto : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_subtype1 : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val objtype_name : string
val mk_type1 : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_type : Z3.Expr.expr -> Jparsetree.class_name -> Z3.Expr.expr
val mk_type_all : Z3.Expr.expr -> Jparsetree.j_base_type -> Z3.Expr.expr
val objtype : Z3.Expr.expr -> string -> Z3.Expr.expr
val mk_objsubtyp1 : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_objsubtyp : Z3.Expr.expr -> Jparsetree.class_name -> Z3.Expr.expr
val mk_statictyp1 : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr
val mk_statictyp : Z3.Expr.expr -> Jparsetree.class_name -> Z3.Expr.expr
