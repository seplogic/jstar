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
open Psyntax
open Jlogic
open Jimple_global_types
open Jparsetree
open Spec_def
open Specification
open Vars
open Support_symex
open Javaspecs
open Spec

module C = Core

(* global variables *)
let curr_static_methodSpecs: Javaspecs.methodSpecs ref = ref Javaspecs.emptyMSpecs
let curr_dynamic_methodSpecs: Javaspecs.methodSpecs ref = ref Javaspecs.emptyMSpecs


let fresh_label =
  let label_ref = ref 0 in
  fun () ->
    label_ref := !label_ref + 1;
    Printf.sprintf "gen_%i" !label_ref




(* create the variable for a  parameter *)
let mk_parameter n =
  let p=parameter n in
  let v=Vars.concretep_str p in
  v

(* retrieve static spec of a method from table of specs*)
let get_static_spec si =
  match si with
  | Method_signature ms ->
      (try
	      match (MethodMap.find ms !curr_static_methodSpecs) with
  		      | (spec, pos) -> Some spec
      with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false

(* retrieve dynamic spec of a method from table of specs*)
let get_dynamic_spec si =
  match si with
  | Method_signature ms ->
      (try
          match (MethodMap.find ms !curr_dynamic_methodSpecs) with
              | (spec, pos) -> Some spec
       with Not_found -> None)
  | _ -> (* this routine is supposed to be called only with method signature*)
      assert false



let get_spec  (iexp: Jparsetree.invoke_expr) =
  let spec =
    match iexp with
    | Invoke_nostatic_exp (Virtual_invoke,_,si,_)
    | Invoke_nostatic_exp (Interface_invoke,_,si,_) ->
	(match get_dynamic_spec si with
	  Some spec -> spec
	| None ->
      failwith ("I need dynamic specs for " ^ (Pprinter.signature2str si)))
    | Invoke_nostatic_exp (Special_invoke,_,si,_)
    | Invoke_static_exp (si,_) ->
	(match get_static_spec si with
	  Some spec -> spec
	| None ->
      failwith ("I need static specs for " ^ (Pprinter.signature2str si)))
  in
  match iexp with
  | Invoke_nostatic_exp (Virtual_invoke,n,_,il)
  | Invoke_nostatic_exp (Interface_invoke,n,_,il)
  | Invoke_nostatic_exp (Special_invoke,n,_,il) ->
      (* Make "this" be the final parameter, i.e. subst @this: for @parametern: *)
      let subst = Psyntax.add (mk_this) (Arg_var (mk_parameter (List.length il))) Psyntax.empty in
      sub_spec subst spec,(il@[Immediate_local_name(n)])
  | Invoke_static_exp (si,il) ->
      spec,il


let get_name  (iexp: Jparsetree.invoke_expr) =
  match iexp with
  | Invoke_nostatic_exp (Virtual_invoke,_,si,il)
  | Invoke_nostatic_exp (Interface_invoke,_,si,il)
  | Invoke_nostatic_exp (Special_invoke,_,si,il) 
  | Invoke_static_exp (si,il) ->
      let n = match si with
	| Method_signature (cn,_,mn,ps) -> Pprinter.class_name2str cn ^ "." ^ Pprinter.name2str mn ^ "$$" ^ (Pprinter.list2str Pprinter.parameter2str ps "$$") 
	| Field_signature (cn,_,fn) -> Pprinter.class_name2str cn ^  "." ^ Pprinter.name2str fn 
            (* nikos: should this case ever be reached? *) 
      in n,il



let retvar_term = Arg_var(SpecOp.ret_v1)

(* make terms related to array representation *) (* {{{ *)
let mk_array a i j v =
  [P_SPred ( "array", [a; i; j; v] )]

let mk_zero x = Immediate_constant (match x with
  | Base (Boolean, _)
  | Base (Byte, _)
  | Base (Char, _)
  | Base (Short, _)
  | Base (Int, _) -> Int_const (Positive, 0)
  | Base (Long, _) -> Int_const_long (Positive, 0)
  | Base (Float, _)
  | Base (Double, _) -> Float_const (Positive, 0.0)
  | Base _ | Quoted _ | Ident_NVT _ |  Full_ident_NVT _ ->
      Null_const)

let mk_succ n =
  Arg_op ("builtin_plus", [n; Arg_op ("numeric_const", [Arg_string "1"])])

let mk_array_get av i v =
  [P_PPred ("array_get", [av; i; v])]
let mk_array_set av i v =
  Arg_op ("array_set", [av; i; v])

(* }}} *)

let mk_asgn rets pre post args =
  let asgn_rets = List.map (fun v -> variable2var (Var_name v)) rets in
  let asgn_args = List.map immediate2args args in
  let asgn_spec = HashSet.singleton { Spec.pre; post } in
  C.Assignment_core { C.asgn_rets; asgn_args; asgn_spec }

(* TODO: Pattern match separately on [v] and [e], not on [(v, e)], and
  handle all cases. *)
(* TODO(rgrig): The encoding of an assignment x:=e *should* be
  x:={}{$ret1=$arg1}(e) rather than x:={}{$ret1=e}(); low priority, though. *)
let rec translate_assign_stmt  (v:Jparsetree.variable) (e:Jparsetree.expression) =
  match v, e with
  | Var_ref (Field_local_ref (n,si)), Immediate_exp e'  ->
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      (* execute  n.si=e' --> _:={param0.si|->-}{param0.si|->param1 * return=x'}(n,e') *)
      let p0 = immediate2args (Immediate_local_name(n)) in (* ddino: should it be a fresh program variable? *)
      let p1 = immediate2args e' in
      let pre=mk_pointsto p0 (signature2args si) pointed_to_var in
      let post=mk_pointsto p0 (signature2args si) p1 in
      mk_asgn [] pre post []
  | Var_ref (Array_ref (a,i)), Immediate_exp e' ->
      let e_var = Arg_var (freshe ()) in
      let a = Arg_var (Vars.concretep_str a) in
      let i = immediate2args i in
      let pre = mk_array a i (mk_succ i) e_var in
      let new_value = mk_array_set e_var i (immediate2args e') in
      let post = mk_array a i (mk_succ i) new_value in
      mk_asgn [] pre post []
  | Var_name v, Immediate_exp e' ->
      (* execute  v=e' --> v:={emp}{return=param0}(e') *)
      let post= mkEQ(retvar_term,immediate2args e') in
      mk_asgn [v] [] post []
  | Var_name v, Reference_exp (Field_local_ref (n,si))  ->
      (* execute v=n.si --> v:={param0.si|->z}{param0.si|->z * return=z}(n)*)
      let e_var = freshe() in
      let pointed_to_var = Arg_var (e_var) in
      let x = (immediate2args (Immediate_local_name(n))) in
      let pre=mk_pointsto x (signature2args si) pointed_to_var in
      let post=pconjunction (mkEQ(retvar_term,pointed_to_var)) (mk_pointsto x (signature2args si) pointed_to_var) in
      mk_asgn [v] pre post []
  | Var_name v, Reference_exp (Array_ref (a, i)) ->
      let e_var = Arg_var (freshe ()) in
      let a = Arg_var (Vars.concretep_str a) in
      let i = immediate2args i in
      let pre = mk_array a i (mk_succ i) e_var in
      let post = pconjunction pre (mk_array_get e_var i retvar_term) in
      mk_asgn [v] pre post []
  | Var_name v, New_simple_exp ty ->
      (* execute v=new(ty)
	 The rest of the job will be performed by the invocation to specialinvoke <init>
      *)
      let post = mk_type_all retvar_term ty in
      mk_asgn [v] [] post []
  | Var_name v, Binop_exp(name,x,y)->
      let args = Arg_op(Support_syntax.bop_to_prover_arg name, [immediate2args x;immediate2args y]) in
      let post= mkEQ(retvar_term,args) in
      mk_asgn [v] [] post []
  | Var_name v, Cast_exp (_,e') -> (* TODO : needs something for the cast *)
      translate_assign_stmt (Var_name v) (Immediate_exp(e'))
  | Var_name v , Invoke_exp ie ->
      let call_name, param = get_name ie in
      let call_rets = [variable2var (Var_name v)] in
      let call_args = List.map immediate2args param in
      C.Call_core { C.call_name; call_rets; call_args }
  | Var_name v, New_array_exp (t, sz) ->
      let int_zero = immediate2args (mk_zero (Base (Int, []))) in
      let t_zero = immediate2args (mk_zero t) in
      let sz = immediate2args sz in
      let post = mk_array retvar_term int_zero sz t_zero in
      mk_asgn [v] [] post []
  | _ -> failwith "TODO"

let assert_core b =
  match b with
  | Binop_exp (op,i1,i2) ->
      let b_pred = Support_syntax.bop_to_prover_pred op (immediate2args i1) (immediate2args i2) in
      mk_asgn [] [] b_pred []
  | _ -> assert false


let jimple_statement2core_statement s : Core.ast_core list =
  if !Config.verbosity >= 4 then begin
    let s = Pprinter.statement2str s in
    printf "@[<2>Translating jimple statement@\n%s@\n@]" s
  end;
  match s with
  | Label_stmt l -> [C.Label_stmt_core l]
  | Breakpoint_stmt -> assert false
  | Entermonitor_stmt i -> assert false
  | Exitmonitor_stmt i -> assert false
  | Tableswitch_stmt (i,cl) -> assert false
  | Lookupswitch_stmt(i,cl) -> assert false
  | Identity_stmt(nn,id,ty) ->
      (* nn := id: LinkedLisr   ---> nn:={emp}{return=param0}(id)*)
      let id'=Immediate_local_name(Identifier_name(id)) in
      let post= mkEQ(retvar_term,immediate2args id') in
      [mk_asgn [nn] [] post []]
  | Identity_no_type_stmt(n,i) -> assert false
  | Assign_stmt(v,e) ->
      [translate_assign_stmt v e]
  | If_stmt(b,l) ->
      let l1 = fresh_label () in
      let l2 = fresh_label () in
      [ C.Goto_stmt_core [l1; l2]
      ; C.Label_stmt_core l1
      ; assert_core b
      ; C.Goto_stmt_core [l]
      ; C.Label_stmt_core l2
      ; assert_core (negate b) ]
  | Goto_stmt(l) ->
      [C.Goto_stmt_core([l])]
  | Nop_stmt ->
      [C.Nop_stmt_core]
  | Ret_stmt(i)  (* return i ---->  ret_var:=i  or as nop operation if it does not return anything*)
  | Return_stmt(i) ->
      (match i with
       | None -> [C.Nop_stmt_core]
       | Some e' ->
	 let p0 = Arg_var(mk_parameter 0) in (* ddino: should it be a fresh program variable? *)
	 let post= mkEQ(retvar_term,p0) in
         [mk_asgn [] [] post [e']; C.End]
      )
  | Throw_stmt(i) -> failwith "TODO(rgrig): must use exception handlers table"
  | Invoke_stmt (e) ->
      let call_name, param = get_name e in
      let call_args = List.map immediate2args param in
      [C.Call_core { C.call_name; call_rets = []; call_args }]
  | Spec_stmt (asgn_rets, asgn_spec) ->
      let asgn_spec = HashSet.singleton asgn_spec in
      [C.Assignment_core { C.asgn_rets; asgn_args = []; asgn_spec }]

(* ================   ==================  *)



exception Contained

(*
recognise if md describes a init method. At the moment it only uses the name. But
maybe we should use a stronger condition
*)
let is_init_method md = Pprinter.name2str md.name_m ="<init>"


let methdec2signature_str dec =
  Pprinter.class_name2str dec.class_name ^ "." ^ Pprinter.name2str dec.name_m ^ "$$" ^ (Pprinter.list2str Pprinter.parameter2str dec.params "$$")



let jimple_stmts2core stms =
  let do_one_stmt (stmt_jimple, source_pos) =
    let s=jimple_statement2core_statement stmt_jimple in
    if !Config.verbosity >= 4 then
      printf "@[<2>@\ninto the core statement:@\n%a@\n@]"
      (pp_list_sep "; " CoreOps.pp_ast_core) s;
      s (* here we throw away the source position -- might want to restore it for nice error messages *)
  in
  List.flatten (List.map do_one_stmt stms)

(* returns a triple (m,initial_formset, final_formset)*)
let get_spec_for m fields cname=
  let this = mk_this in
  let rec make_this_fields fl=
    match fl with
    |[] -> []
    | Field(mol,ty,n)::fl' ->
	let e = Support_symex.default_for ty n in
	let si=make_field_signature cname ty n in
	pconjunction (mk_pointsto (var2args this) (signature2args si) e) (make_this_fields fl')
    | _ -> assert false
  in
  let class_this_fields=make_this_fields fields in

  let msi = Methdec.get_msig m cname in
  let spec=
    try
      match (MethodMap.find msi !curr_static_methodSpecs) with
        | (spec, pos) -> spec
    with  Not_found ->
      failwith ("Cannot find spec for method " ^ methdec2signature_str m)
  in
  let spec = logical_vars_to_prog spec in
  if is_init_method m then (* we treat <init> in a special way*)
    { spec with Spec.pre = pconjunction spec.Spec.pre class_this_fields }
  else spec


let resvar_term = Arg_var(Support_syntax.res_var)

let conjoin_with_res_true (assertion : Psyntax.pform) : Psyntax.pform =
	 pconjunction assertion (mkEQ(resvar_term,Support_symex.constant2args (Int_const (Positive, 1))))

let get_requires_clause_spec_for m fields cname =
        let msi = Methdec.get_msig m cname in
        (* First the the method's dynamic spec *)
        let dynspec =
                try
                  	match (MethodMap.find msi !curr_dynamic_methodSpecs) with
                        | (spec, pos) -> spec
                with Not_found ->
                        failwith ("Cannot find spec for method " ^ methdec2signature_str m)
        in
        let dynspec = logical_vars_to_prog dynspec in
        (* Now construct the desired spec *)
        {
                pre=dynspec.pre;
                post=conjoin_with_res_true (dynspec.pre);
        }

let get_dyn_spec_for m fields cname =
        let msi = Methdec.get_msig m cname in
        (* First the the method's dynamic spec *)
        let dynspec =
                try
                  	match (MethodMap.find msi !curr_dynamic_methodSpecs) with
                    	| (spec, pos) -> spec
                with Not_found ->
                  failwith
                      ("Cannot find spec for method " ^ methdec2signature_str m)
        in
        logical_vars_to_prog dynspec


module LocalMap =
	Map.Make (struct
		type t = string
		let compare = compare
	end)

type local_map = Psyntax.args list AxiomMap.t

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
let jimple_locals2stattype_rules (locals : local_var list) : sequent_rule list =
	let localmap = ref (LocalMap.empty) in
	let _ = List.iter (fun (atype,name) ->
		match atype with
			| Some t ->
					let var = name2args name in
					let typ = Pprinter.j_type2str t in
					(try
						let vars = LocalMap.find typ (!localmap) in
						localmap := LocalMap.add typ (var :: vars) (!localmap)
					with Not_found ->
						localmap := LocalMap.add typ [var] (!localmap)
					)
			| None -> ()
	) locals in
	let x = Arg_var (Vars.fresha ()) in
	LocalMap.fold (fun typ vars rules ->
		let premise : (Psyntax.psequent list list) = List.map (fun var -> [mkEmpty,mkEmpty,mkEQ(x,var),mkEmpty]) vars in
		mk_seq_rule (
			(mkEmpty,mkEmpty,[mk_statictyp1 x (Arg_string typ)],mkEmpty),
			premise,
			"static_type_"^typ
		) :: rules
	) (!localmap) []

let add_static_type_info logic locals : Psyntax.logic =
	let rules = jimple_locals2stattype_rules locals in
	Javaspecs.append_rules logic rules



let verify_jimple_file
    (f : Jimple_global_types.jimple_file)
    (lo : logic)
    (abs_rules : logic)
    (sspecs: Javaspecs.methodSpecs)
    (dspecs: Javaspecs.methodSpecs) :
    unit =
  curr_static_methodSpecs:=sspecs;
  curr_dynamic_methodSpecs:=dspecs;
  let cname=Methdec.get_class_name f in
  (* get the method declarations - See make_methdec in methdec.ml *)
  let mdl =  Methdec.make_methdecs_of_list cname (Methdec.get_list_methods f) in
  (* get the fields *)
  let fields = Methdec.get_list_fields f in

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

  (* generate method bodies in ast_core format *)
  let xs =
    List.map (fun m ->
               let sig_str = methdec2signature_str m in
               let body = if Methdec.has_body m then jimple_stmts2core m.bstmts else [] in
  (*
		   let requires = if Methdec.has_requires_clause m then jimple_stmts2core m.req_stmts else [] in
               let old_clause = List.map (fun o -> jimple_stmts2core o) m.old_stmts_list in
               let ensures = if Methdec.has_ensures_clause m then jimple_stmts2core m.ens_stmts else [] in
  *)
	       let spec = HashSet.singleton(get_spec_for m fields cname) in 
               let l = add_static_type_info lo m.locals in
		 { C.proc_name = sig_str; proc_spec = spec; proc_body = Some body; proc_rules = l } 
  ) mdl in 

  (* verify globally *)
  ignore
    (Symexec.verify
      { C.q_procs = xs
      ; q_rules = lo
      ; q_infer = true
      ; q_name = "jstar_question" });
(* TODO(rgrig): [q_name] should depend on the names of files being processed. *)

  (* Print using core function *)
  let my_file =  Pervasives.open_out "printhis" in
  Corestar_std.pp_list CoreOps.pp_ast_question (Format.formatter_of_out_channel my_file) xs;
  Pervasives.close_out my_file;  

(* nikos: These extra verifications should be restored at some point?
   
   List.iter (fun (m,sig_str,body,req,old,ens) -> 
                  (* verify the body only if the method is non-abstract *)
                  if Methdec.has_body m then
	            (*let _ = Prover.pprint_sequent_rules l in*)
                  (* verify the requires clause if present *)
                  if Methdec.has_requires_clause m then
                    let spec = get_requires_clause_spec_for m fields cname in
	            let l = add_static_type_info lo m.req_locals in
                    ignore (Symexec.verify (sig_str^" requires clause") req spec l abs_rules);
                  (* verify the ensures clause if present *)
                  if Methdec.has_ensures_clause m then
                    let spec = get_dyn_spec_for m fields cname in
                    let l = add_static_type_info lo m.ens_locals in
                    let frames = List.map (fun o -> Symexec.get_frame o spec.pre l abs_rules) old in
                    ignore (Symexec.verify_ensures (sig_str^" ensures clause") ens spec.post conjoin_with_res_true frames l abs_rules)
            ) xs;
*)

  
