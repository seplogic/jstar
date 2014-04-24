(* HACK. TO REMOVE.
  At the moment jStar is untyped, but coreStar requires sorts. This module
  provides an interface that adds some dumb types (mostly int and bool), just
  so I can compile the damn thing for now.

  NOTE: Things that simply forward to [Syntax] are here so that we look at them
  later when we add sorts properly to jstar. *)

open Corestar_std
open Printf

module S = Syntax

let int_function n op =
  let arg_sort = ListH.replicate n S.int_sort in
  Z3.FuncDecl.mk_func_decl_s S.z3_ctx op arg_sort S.int_sort

let mk_1 op = S.mk_1 (int_function 1 op)
let mk_2 op = S.mk_2 (int_function 2 op)

let mk_app op xs = S.mk_n (int_function (List.length xs) op) xs

let mk_lvar = S.mk_int_lvar
let mk_pgvar = S.mk_int_pgvar
let mk_plvar = S.mk_int_plvar
let mk_tpat = S.mk_int_tpat

let parameter = sprintf "@parameter%d:"
  (* NOTE:
  Must correspond to how jimple names parameters in the body of methods. *)
let return = sprintf "$r%d"
