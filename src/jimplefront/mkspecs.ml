(********************************************************
   This file is part of jStar
        src/jimplefront/mkspecs.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Format

module JG = Jimple_global_types
module PP = Pprinter

let pp_spec cname f = function
  | JG.Method (modl, jty,n, pars, tc, rc, ocs, ec, body) ->
      let pp_of x2str f x = pp_string f (x2str x) in (* HACK *)
      fprintf f "@\n@[<2>spec %a %s(@[%a@])@ static : {} {};@]"
        (pp_of PP.j_type2str) jty
        (PP.name2str n)
        (pp_list_sep ", " (pp_of PP.parameter2str)) pars
  | _ -> ()


let rec print_specs_template (JG.JFile (_, _, cname, _, _, ml)) =
  fprintf std_formatter "@[@[<2>class %s {%a@]@\n}@\n@]"
    (PP.class_name2str cname)
    (pp_list (pp_spec cname)) ml

