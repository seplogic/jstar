(********************************************************
   This file is part of jStar
        src/jimplefront/translatejimple.ml
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

(* TODO(rgrig): Don't open these. *)
open Jimple_global_types
open Spec_def
open Support_symex
open Javaspecs

module C = Core
module J = Jparsetree
module JG = Jimple_global_types
module SS = Support_syntax
module U = Untyped

(* global variables *)
let curr_static_methodSpecs: Javaspecs.methodSpecs ref = ref Javaspecs.emptyMSpecs
let curr_dynamic_methodSpecs: Javaspecs.methodSpecs ref = ref Javaspecs.emptyMSpecs


let fresh_label =
  let label_ref = ref 0 in
  fun () ->
    label_ref := !label_ref + 1;
    Printf.sprintf "gen_%i" !label_ref

(* retrieve static spec of a method from table of specs*)
let get_static_spec si =
  match si with
  | J.Method_signature ms ->
      (try
	      match (MethodMap.find ms !curr_static_methodSpecs) with
  		      | (spec, pos) -> Some spec
      with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false

(* retrieve dynamic spec of a method from table of specs*)
let get_dynamic_spec si =
  match si with
  | J.Method_signature ms ->
      (try
          match (MethodMap.find ms !curr_dynamic_methodSpecs) with
              | (spec, pos) -> Some spec
       with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false



let get_spec  (iexp: Jparsetree.invoke_expr) =  failwith "TODO get_spec"
  (* let spec =                                                                                       *)
  (*   match iexp with                                                                                *)
  (*   | Invoke_nostatic_exp (Virtual_invoke,_,si,_)                                                  *)
  (*   | Invoke_nostatic_exp (Interface_invoke,_,si,_) ->                                             *)
	(* (match get_dynamic_spec si with                                                                  *)
	(*   Some spec -> spec                                                                              *)
	(* | None ->                                                                                        *)
  (*     failwith ("I need dynamic specs for " ^ (Pprinter.signature2str si)))                        *)
  (*   | Invoke_nostatic_exp (Special_invoke,_,si,_)                                                  *)
  (*   | Invoke_static_exp (si,_) ->                                                                  *)
	(* (match get_static_spec si with                                                                   *)
	(*   Some spec -> spec                                                                              *)
	(* | None ->                                                                                        *)
  (*     failwith ("I need static specs for " ^ (Pprinter.signature2str si)))                         *)
  (* in                                                                                               *)
  (* match iexp with                                                                                  *)
  (* | Invoke_nostatic_exp (Virtual_invoke,n,_,il)                                                    *)
  (* | Invoke_nostatic_exp (Interface_invoke,n,_,il)                                                  *)
  (* | Invoke_nostatic_exp (Special_invoke,n,_,il) ->                                                 *)
  (*     (* TODO(rgrig): Huh? [this] is the first argument in most implementations. *)                *)
  (*     (* Make "this" be the final parameter, i.e. subst @this: for @parametern: *)                 *)
  (*     let subst = Psyntax.add (mk_this) (Arg_var (mk_parameter (List.length il))) Psyntax.empty in *)
  (*     let n = string_of J.pp_name n in                                                             *)
  (*     (List.map (sub_triple subst) spec, il @ [PS.mkPVar n])                                       *)
  (* | Invoke_static_exp (si,il) ->                                                                   *)
  (*     spec,il                                                                                      *)


let msig2str cn rt mn ps =
  Pprinter.class_name2str cn
  ^ "."
  ^ Pprinter.name2str mn
  ^ "$$"
  ^ (Pprinter.list2str Pprinter.parameter2str ps "$$")
  ^ "$$"
  ^ Pprinter.j_type2str rt

let get_name  (iexp: Jparsetree.invoke_expr) =
  match iexp with
  | J.Invoke_nostatic_exp (J.Virtual_invoke,_,si,il)
  | J.Invoke_nostatic_exp (J.Interface_invoke,_,si,il)
  | J.Invoke_nostatic_exp (J.Special_invoke,_,si,il)
  | J.Invoke_static_exp (si,il) ->
      let n = match si with
	| J.Method_signature (cn,rt,mn,ps) -> msig2str cn rt mn ps
	| J.Field_signature (cn,_,fn) -> failwith "INTERNAL: cannot invoke a field"
      in n,il

let retvar_term =
  U.mk_plvar "$r"

(* make terms/predicates related to the array representation *) (* {{{ *)
let mk_array a i j v = 
  U.mk_app "array" [a; i; j; v]

let mk_zero = function
  | J.Base (J.Boolean, _)
  | J.Base (J.Byte, _)
  | J.Base (J.Char, _)
  | J.Base (J.Short, _)
  | J.Base (J.Int, _)
  | J.Base (J.Long, _)
  | J.Base (J.Float, _)
  | J.Base (J.Double, _)
      -> Syntax.mk_int_const "0"
  | J.Base _
  | J.Quoted _
  | J.Ident_NVT _
  | J.Full_ident_NVT _
      -> Syntax.mk_0 "nil"

let mk_array_get av i v = 
  U.mk_app "array_get" [av; i; v]
let mk_array_set av i v =
  U.mk_app "array_set" [av; i; v] 

(* }}} *)

let var_of_jname = function J.Quoted_name s | J.Identifier_name s -> s

let mk_asgn asgn_rets pre post asgn_args =
  let asgn_spec = (* NOTE: jimple exprs have no side-effects *)
    C.TripleSet.singleton
      { Core.pre; post; modifies = []; in_vars = []; out_vars = [] } in
  C.Assignment_core { C.asgn_rets; asgn_args; asgn_spec }

let mk_asgn_jname rets =
  mk_asgn (List.map (U.mk_plvar @@ var_of_jname) rets)

let mk_alloc j_of_name v = function
  | J.Class_name c ->
      let fs =
        try Methdec.get_list_fields (j_of_name c)
        with Not_found -> begin
          if !Config.verbosity >= 4 then
            eprintf "@{<b>WARNING@}: Class %s is undefined."
              (Pprinter.class_name2str c);
          []
        end in
      let keep_nonvoid (_, ty, n) = match ty with
        | J.Void -> eprintf "@{<b>WARNING:@} Weird jimple (a8uydb8)"; []
        | J.Non_void ty -> [(ty, n)] in
      let fs = fs >>= keep_nonvoid in
      let pto (ty, n) =
        let fn = signature2args (J.Field_signature (c, (J.Non_void ty), n)) in
        Jlogic.mk_pointsto v fn (mk_zero ty) in
      Syntax.mk_big_star (List.map pto fs)
  | _ -> Syntax.mk_emp

let rec translate_assign_stmt j_of_name e f =
  (* The assignment e:=f is treated as the sequence $temp:=f; e:=$temp. This way,
  there are fewer types of assignments to consider because $temp is guaranteed
  to be a program variable. Yes, $temp holds values of any type, and gets
  overwritten often. *)
  let emp = Syntax.mk_emp in
  let ( @* ) = Syntax.mk_star in
  let ( @= ) = Syntax.mk_eq in
  (* NOTE: If $temp does not occur in expression f,
    then { } $temp := f { $temp = f } *)
  let temp_pvar = U.mk_plvar "$temp" in
  let temp_lvar = Syntax.freshen temp_pvar in
  let check_ft ft =
    let rec bad e =
      Syntax.expr_equal e temp_pvar
      || Syntax.on_app (c1 (List.exists bad)) e in
    assert (not (bad ft));
    ft in
  let skip = mk_asgn [] emp emp [] in
  [ begin match f with
    | J.Binop_exp (name, x, y) ->
        let ft = check_ft (SS.mk_2 name x y) in
        mk_asgn [temp_pvar] emp (temp_pvar @= ft) []
    | J.Cast_exp (_,t) (* fallthru *)
    | J.Immediate_exp t ->
        mk_asgn [temp_pvar] emp (temp_pvar @= check_ft t) []
    | J.Instanceof_exp (_, _) -> failwith "TODO sd9qa8dj"
    | J.Invoke_exp ie ->
        let call_name, call_args = get_name ie in
        let call_rets = [ temp_pvar ] in
        C.Call_core { C.call_name; call_rets; call_args }
    | J.New_array_exp (t, sz) -> skip
        (* TODO: Fix array implementation.
        let int_zero = mk_zero (J.Base (J.Int, [])) in
        let t_zero = mk_zero t in
        let wt = mk_v "new_array" in
        ([], wt, mk_array wt int_zero sz t_zero) *)
    | J.New_multiarray_exp (_, _) -> failwith "TODO d2mwoi98j"
    | J.New_simple_exp ty ->
        let post =
          Jlogic.mk_type_all temp_pvar ty @* mk_alloc j_of_name temp_pvar ty in
        mk_asgn [] emp post []
    | J.Reference_exp (J.Array_ref (a, i)) -> skip
        (* TODO Fix array implementation.
        let wt = mk_v "elem_val" in
        let at = Syntax.mk_var a in
        let pre = mk_array at i (SS.mk_succ i) wt in
        ([mk_asgn [] pre emp []], wt, pre * mk_array_get at i wt) *)
    | J.Reference_exp (J.Field_local_ref (n, si))  ->
        let n = U.mk_pgvar (var_of_jname n) in
        let p = Jlogic.mk_pointsto n (signature2args si) temp_lvar in
        mk_asgn [temp_pvar] p (p @* (temp_pvar @= temp_lvar)) []
    | J.Reference_exp (J.Field_sig_ref si) ->
        let p = Jlogic.mk_static_pointsto (signature2args si) temp_lvar in
        mk_asgn [temp_pvar] p (p @* (temp_pvar @= temp_lvar)) []
    | J.Unop_exp (name, x) ->
        let ft = check_ft (SS.mk_1 name x) in
        mk_asgn [temp_pvar] emp (temp_pvar @= ft) []
  end ]
  @ [ let rt = retvar_term in
    begin match e with
    | J.Var_name n -> mk_asgn_jname [n] emp (rt @= temp_pvar) []
    | J.Var_ref (J.Array_ref (a, i)) -> skip
        (* TODO: Fix array implementation. *)
    | J.Var_ref (J.Field_local_ref (n, si)) ->
        let n = U.mk_pgvar (var_of_jname n) in
        let pre = Jlogic.mk_pointsto n (signature2args si) temp_lvar in
        let post = Jlogic.mk_pointsto n (signature2args si) temp_pvar in
        mk_asgn [] pre post []
    | J.Var_ref (J.Field_sig_ref _) -> failwith "TODO pcmw9ijef"
  end ]

let assume_core b =
  match b with
  | J.Binop_exp (op,i1,i2) -> mk_asgn [] Syntax.mk_emp (SS.mk_2 op i1 i2) []
  | _ -> assert false


let jimple_statement2core_statement j_of_name s =
  if !Config.verbosity >= 4 then begin
    printf "@[<2>Translating jimple statement@\n%s@\n@]"
      (Pprinter.statement2str s)
  end;
  let oops m =
    eprintf "@[@{<b>TODO@}: translate jimple statement %s.@ \
      Treating as skip for now.@." m; [] in
  match s with
  | Label_stmt l -> [C.Label_stmt_core l]
  | Breakpoint_stmt -> oops "breakpoint"
  | Entermonitor_stmt i -> oops "entermonitor"
  | Exitmonitor_stmt i -> oops "exitmonitor"
  | Tableswitch_stmt (i,cl) -> oops "tableswitch"
  | Lookupswitch_stmt(i,cl) -> oops "lookupswitch"
  | Identity_stmt(nn,id,_)  (* TODO(rgrig): use type, don't ignore. *)
  | Identity_no_type_stmt(nn,id) ->
      (* nn := id: LinkedList   ---> nn:={emp}{return=param0}(id) *)
      let id'= U.mk_plvar id in
      let post = Syntax.mk_eq retvar_term id' in
      [mk_asgn_jname [nn] Syntax.mk_emp post []]
  | Assign_stmt(v,e) ->
      translate_assign_stmt j_of_name v e
  | If_stmt(b,l) ->
      let l1 = fresh_label () in
      let l2 = fresh_label () in
      [ C.Goto_stmt_core [l1; l2]
      ; C.Label_stmt_core l1
      ; assume_core b
      ; C.Goto_stmt_core [l]
      ; C.Label_stmt_core l2
      ; assume_core (negate b) ]
  | Goto_stmt ls ->
      [C.Goto_stmt_core ls]
  | Nop_stmt ->
      [C.Nop_stmt_core]
  | Ret_stmt(i)  (* return i ---->  ret_var:=i  or as nop operation if it does not return anything*)
  | Return_stmt(i) ->
      (match i with
       | None -> [C.End]
       | Some e' ->
            (* ddino: should [p0] be a fresh program variable? *)
           let p0 = U.mk_plvar (U.parameter 0) in
           let post= Syntax.mk_eq retvar_term p0 in
         [mk_asgn [] Syntax.mk_emp post [e']; C.End]
      )
  | Throw_stmt _ ->
      failwith "INTERNAL: At this point catch clauses aren't available anymore."
  | Invoke_stmt (e) ->
      let call_name, call_args = get_name e in
      [C.Call_core { C.call_name; call_rets = []; call_args }]
  | Spec_stmt asgn -> [ C.Assignment_core asgn ]

(* ================   ==================  *)



exception Contained

(*
recognise if md describes a init method. At the moment it only uses the name. But
maybe we should use a stronger condition
*)
let is_init_method md = Pprinter.name2str md.name_m ="<init>"

let methdec2signature_str dec =
  msig2str dec.class_name dec.ret_type dec.name_m dec.params

let params_of_methdec m =
  let f i _ ps = U.parameter (i + 1) :: ps in (* TODO: handle type/sort *)
  let ps = ListH.foldri f m.JG.params [] in
  List.map U.mk_plvar ps

let rets_of_methdec _ =
  [ U.mk_plvar (U.return 0) ] (* TODO: handle type/sort. *)

let jimple_stmts2core j_of_name stms =
  let do_one_stmt (stmt_jimple, source_pos) =
    let s = jimple_statement2core_statement j_of_name stmt_jimple in
    if !Config.verbosity >= 4 then
      printf "@[<2>@\ninto the core statement:@\n%a@\n@]"
      (pp_list_sep "; " CoreOps.pp_statement) s;
      s (* here we throw away the source position -- might want to restore it for nice error messages *)
  in
  stms >>= do_one_stmt

(* returns a triple (m,initial_formset, final_formset)*)
let get_spec_for m fields cname = []
(* TODO: Reimplement. *)
  (* let this = mk_this in                                                                   *)
  (* let rec make_this_fields fl=                                                            *)
  (*   match fl with                                                                         *)
  (*   |[] -> []                                                                             *)
  (*   | Field(mol,ty,n)::fl' ->                                                             *)
	(* let e = Support_symex.default_for ty n in                                               *)
	(* let si=make_field_signature cname ty n in                                               *)
	(* pconjunction (mk_pointsto (var2args this) (signature2args si) e) (make_this_fields fl') *)
  (*   | _ -> assert false                                                                   *)
  (* in                                                                                      *)
  (* let class_this_fields=make_this_fields fields in                                        *)

  (* let msi = Methdec.get_msig m cname in                                                   *)
  (* let spec =                                                                              *)
  (*   try                                                                                   *)
  (*     match (MethodMap.find msi !curr_static_methodSpecs) with                            *)
  (*       | (spec, pos) -> spec                                                             *)
  (*   with  Not_found ->                                                                    *)
  (*     failwith ("Cannot find spec for method " ^ methdec2signature_str m)                 *)
  (* in                                                                                      *)
  (* let f triple =                                                                          *)
  (*   let triple = logical_vars_to_prog triple in                                           *)
  (*   if is_init_method m then (* we treat <init> in a special way*)                        *)
  (*     { triple with Core.pre = pconjunction triple.Core.pre class_this_fields }           *)
  (*   else triple in                                                                        *)
  (* List.map f spec                                                                         *)


let conjoin_with_res_true (assertion : Z3.Expr.expr) : Z3.Expr.expr =
  failwith "TODO conjoin_with_res_true"
	 (* pconjunction assertion (mkEQ(resvar_term, PS.mkNumericConst "1")) *)

let get_dyn_spec_for m fields cname = failwith "TODO get_dyn_spec_for"
        (* let msi = Methdec.get_msig m cname in                                    *)
        (* (* First the the method's dynamic spec *)                                *)
        (* let dynspec =                                                            *)
        (*         try                                                              *)
        (*           	match (MethodMap.find msi !curr_dynamic_methodSpecs) with    *)
        (*             	| (spec, pos) -> spec                                      *)
        (*         with Not_found ->                                                *)
        (*           failwith                                                       *)
        (*               ("Cannot find spec for method " ^ methdec2signature_str m) *)
        (* in                                                                       *)
        (* List.map logical_vars_to_prog dynspec                                    *)


(* module LcalMap =          *)
(* 	Map.Make (struct        *)
(* 		type t = string       *)
(* 		let compare = compare *)
(* 	end)                    *)

(* type local_map = Psyntax.args list AxiomMap.t *)
(* type local_map = Z3.Expr.expr (* Psyntax.args *) list Javaspecs.AxiomMap.t *)

(*
A jimple method body contains a list of local variable declarations.
One rule is generated for every type appearing in the list.
Example: for type T, suppose v1...vn are all the variables declared of type T.
Then the following rule is generated for T:

rule static_type_T:
 | |- !statictype(?x,"T")
if
 | |- ?x=v1
or
 | |- ?x=v2
...
or
 | |- ?x=vn
*)
let jimple_locals2stattype_rules _ = []
(* TODO: Reimplement. Probably important. *)
  (* (locals : local_var list) : sequent_rule list =                        *)
	(* let localmap = ref (LocalMap.empty) in                                 *)
	(* let _ = List.iter (fun (atype,name) ->                                 *)
	(* 	match atype with                                                     *)
	(* 		| Some t ->                                                        *)
	(* 				let var = name2args name in                                    *)
	(* 				let typ = Pprinter.j_type2str t in                             *)
	(* 				(try                                                           *)
	(* 					let vars = LocalMap.find typ (!localmap) in                  *)
	(* 					localmap := LocalMap.add typ (var :: vars) (!localmap)       *)
	(* 				with Not_found ->                                              *)
	(* 					localmap := LocalMap.add typ [var] (!localmap)               *)
	(* 				)                                                              *)
	(* 		| None -> ()                                                       *)
	(* ) locals in                                                            *)
	(* let x = Arg_var (Vars.fresha ()) in                                    *)
	(* LocalMap.fold (fun typ vars rules ->                                   *)
	(* 	         let premise : (Psyntax.psequent list list) =                *)
	(*                    List.map (fun var -> [ PS.mk_psequent               *)
	(*                                             mkEmpty mkEmpty            *)
	(*                                             (mkEQ(x,var)) ]) vars in   *)
	(* 	mk_seq_rule (                                                        *)
	(* 	  PS.mk_psequent mkEmpty mkEmpty (mk_statictyp1 x (Arg_string typ)), *)
	(* 		premise,                                                           *)
	(* 		"static_type_"^typ                                                 *)
	(* 	) :: rules                                                           *)
	(* ) (!localmap) []                                                       *)

let add_if_called_proc acc stmt =
  match stmt with
    | C.Call_core c -> HashSet.add acc c.C.call_name
    | _ -> ()

let called_procs_from_body acc body =
   List.iter (add_if_called_proc acc) body

let called_procs_from_proc acc proc =
  match proc.C.proc_body with
    | Some b -> called_procs_from_body acc b
    | None -> ()

let remove_proc acc proc =
  HashSet.remove acc proc.C.proc_name

let dummy_proc n =
  { C.proc_name = n
  ; proc_spec = C.TripleSet.create 0
  ; proc_ok = true
  ; proc_body = None
  ; proc_rules = { C.calculus = []; abstraction = [] }
  ; proc_params = []
  ; proc_rets = [] }

let add_dummy_procs xs =
  let h = HashSet.create 1 in
  List.iter (called_procs_from_proc h) xs;
  List.iter (remove_proc h) xs;
  xs@(HashSet.fold (fun x y -> dummy_proc x :: y) h [])

let compile_method j_of_name cname fields m =
  let proc_name = methdec2signature_str m in
  let proc_body =
    if Methdec.has_body m
    then Some (jimple_stmts2core j_of_name m.bstmts)
    else None in
  let proc_spec = Core.TripleSet.of_list (get_spec_for m fields cname) in
  let proc_rules =
    { Core.calculus = jimple_locals2stattype_rules m.locals
    ; abstraction = [] } in
  let proc_params = params_of_methdec m in
  let proc_rets = rets_of_methdec m in
  { C.proc_name
  ; proc_spec
  ; proc_body
  ; proc_rules
  ; proc_ok = true
  ; proc_params
  ; proc_rets }

let compile_class j_of_name jimple =
  let cname = Methdec.get_class_name jimple in
  (* get the method declarations - See make_methdec in methdec.ml *)
  let mdl = Methdec.make_methdecs_of_list cname (Methdec.get_list_methods jimple) in
  let fields = Methdec.get_list_fields jimple in
  (* Adding specification position for init method statements if they do not have their own *)
  List.iter (fun m ->
               if is_init_method m then
                 let mb = List.map (fun (statement, pos) ->
                                      match pos with
                                      | None ->
                                          let msi = Methdec.get_msig m cname in
                                          let spec_pos =
                                            try
                                              match (MethodMap.find msi !curr_static_methodSpecs) with
                                              | (spec, pos) -> pos
                                            with Not_found ->
                                              try
                                                match (MethodMap.find msi !curr_dynamic_methodSpecs) with
                                                | (spec, pos) -> pos
                                              with  Not_found -> None in
                                          (statement, spec_pos)
                                      | Some _ -> (statement, pos)
                                   ) m.bstmts in
                 m.bstmts <- mb
            ) mdl;
  List.map (compile_method j_of_name cname fields) mdl

(* NOTE(rgrig): I don't handle the code-based requires/ensures. To be
deprecated, IMO. *)
let compile j_of_name js sspecs dspecs =
  curr_static_methodSpecs := sspecs;
  curr_dynamic_methodSpecs := dspecs;
  add_dummy_procs (js >>= compile_class j_of_name)
