(********************************************************
   This file is part of jStar
        src/jimplefront/support_symex.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Config
open Jparsetree
open Support_syntax
open Jimple_global_types


(* given a variable it returns its key to use in the table *)
let variable2key v = Pprinter.variable2str v



(* ============== Conversion facilities ================ *)

(*
  default value for type
  returns fresh exists var with n as its name base if
   it doesn't know what to do.
*)
let default_for ty n = failwith "TODO"
  (* try (                                                                                                                                    *)
  (*   match ty with                                                                                                                          *)
  (*     Void -> assert false                                                                                                                 *)
  (*   | Non_void jty -> (                                                                                                                    *)
	(* match jty with                                                                                                                           *)
	(* | Base (jbt,arraylist) -> (                                                                                                              *)
	(*     match jbt,arraylist with                                                                                                             *)
	(*       Class_name _, _                                                                                                                    *)
	(*     | Null_type, _                                                                                                                       *)
	(*     | _, _::_ -> Arg_op("nil",[])                                                                                                        *)
	(*     | Int,_                                                                                                                              *)
	(*     | Char,_                                                                                                                             *)
	(*     | Short,_                                                                                                                            *)
	(*     | Byte,_                                                                                                                             *)
	(*     | Long,_ -> Arg_op("numeric_const",[Arg_string("0")])                                                                                *)
	(*     | Float,_                                                                                                                            *)
	(*     | Double,_ -> Arg_var(Vars.freshe_str (Pprinter.name2str n))                                                                         *)
	(*     | Boolean,_ -> Arg_op("false",[])                                                                                                    *)
	(*    )                                                                                                                                     *)
	(* | _ -> Arg_op("nil",[])                                                                                                                  *)
  (*      )                                                                                                                                   *)
  (*  )                                                                                                                                       *)
  (* with Assert_failure (e,i,j) -> Printf.printf "Default for failed on type %s.\n" (Pprinter.j_type2str ty); raise (Assert_failure(e,i,j) ) *)


let signature2args si = 
  Syntax.mk_string_const (Pprinter.signature2str si) 


let name2args n = failwith "TODO"
  (* match n with                                         *)
  (* | Quoted_name s                                      *)
  (* | Identifier_name s -> Arg_var(Vars.concretep_str s) *)


let identifier2args s = failwith "TODO"
    (* Arg_var(Vars.concretep_str s) *)


let reference2args r = (* not sure we need this. Maybe we need reference2PPred*)
  match r with
  |Array_ref (id,im) -> assert false
  |Field_local_ref(n,si) -> assert false
  |Field_sig_ref(si) -> assert false

(* for the moment only few cases are done of this. Need to be extended *)
let expression2args e =  failwith "TODO"
  (* match e with                                                                                 *)
  (* | New_simple_exp ty -> assert false                                                          *)
  (* | New_array_exp (nv_ty,fad) -> assert false                                                  *)
  (* | New_multiarray_exp (ty,adl) -> assert false                                                *)
  (* | Cast_exp (nv_ty,im) -> assert false                                                        *)
  (* | Instanceof_exp (im,nv_ty) -> assert false                                                  *)
  (* | Binop_exp (bop,im1,im2) ->                                                                 *)
  (*     Arg_op(bop_to_prover_arg bop                                                             *)
	(* ,   [im1; im2] )                                                                             *)
  (* | Unop_exp (uop,im) -> assert false                                                          *)
  (* | Invoke_exp ie -> assert false                                                              *)
  (* | Immediate_exp im -> im                                                                     *)
  (* | Reference_exp r -> reference2args r (* do we need this translation of better to PPred???*) *)


let var2args x =  failwith "TODO"
  (* Arg_var x *)


let immediate2var e =  failwith "TODO"
  (* match e with        *)
  (*   Arg_var v -> v    *)
  (* | _ -> assert false *)


(* ==============  printing facilities  ======================= *)
let form2str f =
	Corestar_std.string_of Syntax.pp_expr f

(* this is not used or exported from the module, thus commented out (nikos g) *)
(* let print_formset s fs=  *)
  (* Format.printf "@\n%s@  [ @[%a@]@ ]@."                                                                *)
  (*   s                                                                                                  *)
  (*   (fun ppf -> List.iter (fun f ->Format.fprintf ppf "@[%a@]@\n " Sepprover.string_inner_form f )) fs *)


(* =============   end printing facilities ==================== *)




let negate e =
  match e with
  | Binop_exp (Cmpeq,i1,i2) -> Binop_exp (Cmpne,i1,i2)
  | Binop_exp (Cmpne,i1,i2) -> Binop_exp (Cmpeq,i1,i2)
  | Binop_exp (Cmpgt,i1,i2) -> Binop_exp (Cmple,i1,i2)
  | Binop_exp (Cmplt,i1,i2) -> Binop_exp (Cmpge,i1,i2)
  | Binop_exp (Cmpge,i1,i2) -> Binop_exp (Cmplt,i1,i2)
  | Binop_exp (Cmple,i1,i2) -> Binop_exp (Cmpgt,i1,i2)
  | _ -> assert false (* ddino: many other cases should be filled in *)

(* ================= misc functions =============== *)







let get_class_name_from_signature si =
  match si with
  | Method_signature (c,_,_,_) -> c
  | Field_signature (c,_,_) ->c


let signature_get_name si =
  match si with
  | Method_signature (_,_,n,_) -> n
  | Field_signature (_,_,n) -> n


let invoke_exp_get_signature ie =
  match ie with
  | Invoke_nostatic_exp(_, _, si, _) -> si
  | Invoke_static_exp(si,_) -> si

let make_field_signature  cname ty n =
  Field_signature(cname,ty,n)


