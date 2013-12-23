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

module Expr = Expression
module J = Jparsetree
module JG = Jimple_global_types

let mk_2 = function
  | J.And -> Expr.mk_2 "!jstar_and" (* TODO: Perhaps add [Prover.mk_and] *)
  | J.Or -> Expr.mk_or
  | J.Xor -> Expr.mk_2 "!jstar_xor"
  | J.Mod -> Expr.mk_2 "!jstar_mod"
  | J.Cmp -> Expr.mk_2 "!jstar_cmp"
  | J.Cmpg -> Expr.mk_2 "!jstar_cmpg"
  | J.Cmpl -> Expr.mk_2 "!jstar_cmpl"
  | J.Cmpeq -> Expr.mk_eq
  | J.Cmpne -> Expr.mk_neq
  | J.Cmpgt -> Expr.mk_2 "!corestar_gt"
  | J.Cmpge -> Expr.mk_2 "!corestar_ge"
  | J.Cmplt -> Expr.mk_2 "!corestar_lt"
  | J.Cmple -> Expr.mk_2 "!corestar_le"
  | J.Shl -> Expr.mk_2 "!jstar_shiftl"
  | J.Shr -> Expr.mk_2 "!jstar_shiftr"
  | J.Ushr -> Expr.mk_2 "!jstar_ushiftr"
  | J.Plus -> Expr.mk_2 "!corestar_plus"
  | J.Minus -> Expr.mk_2 "!corestar_minus"
  | J.Mult -> Expr.mk_2 "!jstar_mult"
  | J.Div -> Expr.mk_2 "!corestar_div"
  (* TODO: It's weird that corestar has corestar_div but not corestar_mult *)

let mk_1 = function
  | J.Lengthof -> Expr.mk_1 "!jstar_length_of"
  | J.Neg -> mk_2 J.Minus (Expr.mk_int_const "0")

let mk_succ e =
  mk_2 J.Plus e (Expr.mk_int_const "1")

(* constant name for "this" object *)
let this_var_name  = "@this:"
let this_var = Expression.mk_var this_var_name
