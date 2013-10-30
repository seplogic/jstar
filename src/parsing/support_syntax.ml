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

open Jparsetree
(* open Psyntax *)
open Jimple_global_types

let bop_to_prover_arg = function
      |	And -> "builtin_and"
      | Or -> "builtin_or"
      | Xor -> "builtin_xor"
      | Mod -> "builtin_mod"
      | Cmp -> "builtin_cmp"
      | Cmpg -> "builtin_cmpg"
      | Cmpl -> "builtin_cmpl"
      | Cmpeq -> "builtin_eq"
      | Cmpne -> "builtin_ne"
      | Cmpgt -> "builtin_gt"
      | Cmpge -> "builtin_ge"
      | Cmplt -> "builtin_lt"
      | Cmple -> "builtin_le"
      | Shl -> "builtin_shiftl"
      | Shr -> "builtin_shiftr"
      | Ushr -> "builtin_ushiftr"
      | Plus -> "builtin_plus"
      | Minus -> "builtin_minus"
      | Mult -> "builtin_mult"
      | Div -> "builtin_div"

let bop_to_prover_pred bop i1 i2 =
	(* TODO: are there a standard identifiers for GT etc? *)
  match bop with
  | Cmpeq -> Expression.mk_eq i1 i2
  | Cmpne -> Expression.mk_neq i1 i2
  | Cmpgt -> Expression.mk_2 "GT" i1 i2
  | Cmplt -> Expression.mk_2 "LT" i1 i2
  | Cmpge -> Expression.mk_2 "GE" i1 i2
  | Cmple -> Expression.mk_2 "LE" i1 i2
  | _ -> Printf.printf "\n\n Operation %s not supported. Abort!" (Pprinter.binop2str bop);
      assert false (* ddino: many other cases should be filled in *)


let parameter n = "@parameter"^(string_of_int n)^":"
let parameter_var n = Expression.mk_var (parameter n)


(* constant name for "this" object *)
let this_var_name  = "@this:"
let this_var = Expression.mk_var this_var_name

let res_var_name = "$res"
let res_var = Expression.mk_var res_var_name
