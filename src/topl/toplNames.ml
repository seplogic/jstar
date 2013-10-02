open Corestar_std
open Printf

let s = Expression.mk_string_const

let call_event p = s& sprintf "call_$$_%s" p
let return_event p = s& sprintf "return_$$_%s" p

let global n = sprintf "%s_%s" CoreOps.global_prefix n
