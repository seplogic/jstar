open Corestar_std
open Printf

module U = Untyped

let s = Syntax.mk_string_const

let call_event p = s& sprintf "call_$$_%s" p
let return_event p = s& sprintf "return_$$_%s" p

let global = U.mk_pgvar
