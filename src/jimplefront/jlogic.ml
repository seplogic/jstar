(********************************************************
   This file is part of jStar
        src/jimplefront/jlogic.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* TODO: Don't open these. *)
open Pprinter
open Support_syntax
open Jimple_global_types

module U = Untyped

let class2args cl =
  Syntax.mk_string_const (class_name2str cl)

(* create n.si|->e *)
let mk_pointsto n si e =
  U.mk_papp "field" [n; si; e]

(* create si|->e *)
let static_var = U.mk_pgvar "static"
let mk_static_pointsto = mk_pointsto static_var

(* create cl1 <: cl2 *)
let mk_subtype1 = U.mk_p2 "subtype"
let mk_subtype cl1 cl2 = mk_subtype1 (class2args cl1) (class2args cl2)


let base_type2args ty =
  Syntax.mk_string_const (Pprinter.j_base_type2str ty)

(* create var : cl   (precise type not static type) *)
let objtype_name = "type"
let mk_type1 = U.mk_p2 objtype_name
let mk_type var cl = mk_type1 var (class2args cl)
let mk_type_all var cl = mk_type1 var (base_type2args cl)

let objtype receiver classname =
  mk_type1 receiver (Syntax.mk_string_const classname)


(* create var <: cl  (is a subtype of) *)
let mk_objsubtyp1 = U.mk_p2 "objsubtype"
let mk_objsubtyp var cl = mk_objsubtyp1 var (class2args cl)

(* create var </: cl  (is not a subtype of) *)
let mk_objnotsubtyp var cl =
  U.mk_p2 "notobjsubtype" var (class2args cl)

(* create var statictype cl *)
let mk_statictyp1 = U.mk_p2 "statictype"
let mk_statictyp var cl = mk_statictyp1 var (class2args cl)
