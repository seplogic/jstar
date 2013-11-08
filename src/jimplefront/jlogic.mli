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


val class2args : Jparsetree.class_name -> Expression.t 
val mk_pointsto : Expression.t -> Expression.t -> Expression.t -> Expression.t
val mk_static_pointsto : Expression.t -> Expression.t -> Expression.t
val mk_subtype1 : Expression.t -> Expression.t -> Expression.t
val objtype_name : string
val mk_type1 : Expression.t -> Expression.t -> Expression.t
val mk_type : Expression.t -> Jparsetree.class_name -> Expression.t
val mk_type_all : Expression.t -> Jparsetree.j_base_type -> Expression.t
val objtype : Expression.t -> string -> Expression.t
val mk_objsubtyp1 : Expression.t -> Expression.t -> Expression.t
val mk_objsubtyp : Expression.t -> Jparsetree.class_name -> Expression.t
val mk_statictyp1 : Expression.t -> Expression.t -> Expression.t
val mk_statictyp : Expression.t -> Jparsetree.class_name -> Expression.t
