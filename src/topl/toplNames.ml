open Corestar_std
open Printf

let s = Psyntax.mkString

let call_event p = s& sprintf "call_$$_%s" p
let return_event p = s& sprintf "return_$$_%s" p
