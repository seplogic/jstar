(********************************************************
   This file is part of jStar
        src/parsing/support_syntax.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

module J = Jparsetree
module JG = Jimple_global_types
module U = Untyped

(* TODO: Replace these by Z3 counterparts. *)
let mk_2 = function
  | J.And -> U.mk_2 "!jstar_and"
  | J.Or -> U.mk_2 "!jstar_or"
  | J.Xor -> U.mk_2 "!jstar_xor"
  | J.Mod -> U.mk_2 "!jstar_mod"
  | J.Cmp -> U.mk_2 "!jstar_cmp"
  | J.Cmpg -> U.mk_2 "!jstar_cmpg"
  | J.Cmpl -> U.mk_2 "!jstar_cmpl"
  | J.Cmpeq -> Syntax.mk_eq
  | J.Cmpne -> (fun a b -> Syntax.mk_distinct [a; b])
  | J.Cmpgt -> U.mk_p2 "!jstar_gt"
  | J.Cmpge -> U.mk_p2 "!jstar_ge"
  | J.Cmplt -> U.mk_p2 "!jstar_lt"
  | J.Cmple -> U.mk_p2 "!jstar_le"
  | J.Shl -> U.mk_2 "!jstar_shiftl"
  | J.Shr -> U.mk_2 "!jstar_shiftr"
  | J.Ushr -> U.mk_2 "!jstar_ushiftr"
  | J.Plus -> U.mk_2 "!jstar_plus"
  | J.Minus -> U.mk_2 "!jstar_minus"
  | J.Mult -> U.mk_2 "!jstar_mult"
  | J.Div -> U.mk_2 "!jstar_div"

let mk_1 = function
  | J.Lengthof -> U.mk_1 "!jstar_length_of"
  | J.Neg -> mk_2 J.Minus (Syntax.mk_int_const "0")

let mk_succ e =
  mk_2 J.Plus e (Syntax.mk_int_const "1")

(* constant name for "this" object *)
let this_var_name  = "@this:"
let this_var = Syntax.mk_int_plvar this_var_name

