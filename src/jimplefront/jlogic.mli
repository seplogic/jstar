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


val class2args : Jparsetree.class_name -> Psyntax.args
val mk_pointsto :
  Psyntax.args -> Psyntax.args -> Psyntax.args -> Psyntax.form
val mk_subtype1 : Psyntax.args -> Psyntax.args -> Psyntax.form
val objtype_name : string
val mk_type1 : Psyntax.args -> Psyntax.args -> Psyntax.form
val mk_type : Psyntax.args -> Jparsetree.class_name -> Psyntax.form
val mk_type_all :
  Psyntax.args -> Jparsetree.j_base_type -> Psyntax.form
val objtype : Vars.var -> string -> Psyntax.form
val mk_objsubtyp1 : Psyntax.args -> Psyntax.args -> Psyntax.pform_at
val mk_objsubtyp : Psyntax.args -> Jparsetree.class_name -> Psyntax.pform_at
val mk_statictyp1 : Psyntax.args -> Psyntax.args -> Psyntax.form
val mk_statictyp : Psyntax.args -> Jparsetree.class_name -> Psyntax.form
