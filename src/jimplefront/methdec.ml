(********************************************************
   This file is part of jStar
        src/jimplefront/methdec.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   jStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)



(* Manage methdec infos for a file *)

open Corestar_std
open Format

module J = Jparsetree
module JG = Jimple_global_types
module U = Untyped

let make_methdec mos cname ty n pars tc (rlocs,rstms) ostmss (elocs,estms) (locs,b)  =
{
  JG.modifiers= mos;
  class_name = cname;
  ret_type=ty;
  name_m= n;
  params= pars;
  locals = locs;
  th_clause=tc;
  req_locals = rlocs;
  req_stmts=rstms;
  old_stmts_list = ostmss;
  ens_locals = elocs;
  ens_stmts = estms;
  bstmts=b
}

let get_list_methods f =
  match f with
  | JG.JFile (_,_,_,_,_, meml) -> List.filter (fun a -> match a with
					    |JG.Field _ -> false
					    |JG.Method _ -> true) meml

let get_list_member f =
  match f with
  | JG.JFile (_,_,_,_,_, meml) -> meml

let get_list_fields (JG.JFile (_,_,_,_,_, ms)) =
  let f = function
    | JG.Field (modifier, ty, name) -> [(modifier, ty, name)]
    | _ -> [] in
  ms >>= f

let get_class_name f =
  match f with
  | JG.JFile(_,_,cn,_,_,_) ->cn


let get_locals b =
  match b with
  | None -> []
  | Some body ->
      let dec_or_stmt_list = fst body in
      let dos=List.map (fun a -> match a with
		   |JG.DOS_dec (J.Declaration (t,nl)) -> List.map (fun n -> (t,n)) nl
		   | _ -> [] ) dec_or_stmt_list
      in List.flatten dos



(* helpers for [encode_exceptions] *) (* {{{ *)

type ee_state =
  { ee_froms : (J.label_name, J.catch_clause list) Hashtbl.t
  ; ee_tos : (J.label_name, J.catch_clause list) Hashtbl.t
  ; ee_type : (J.label_name, J.class_name) Hashtbl.t
  ; ee_scope : J.catch_clause HashSet.t
  ; ee_seen : J.catch_clause HashSet.t }

let ee_init_state xs ys =
  let m = List.length xs in
  let n = List.length ys in
  { ee_froms = Hashtbl.create m
  ; ee_tos = Hashtbl.create m
  ; ee_type = Hashtbl.create m
  ; ee_scope = HashSet.create n
  ; ee_seen = HashSet.create n }

let ee_hash_catchers state cs =
  let hash_catcher c =
    let hash h label c =
      let cs = (try Hashtbl.find h label with Not_found -> []) in
      Hashtbl.replace h label (c :: cs) in
    hash state.ee_froms c.J.catch_from c;
    hash state.ee_tos c.J.catch_to c;
    begin try
      let t = Hashtbl.find state.ee_type c.J.catch_with in
      if t <> c.J.catch_exception then begin
        eprintf
          "@[<2>@{ERROR@}: I, jStar, don't handle exception handlers for@ \
          multiple classes.@ Is this even valid jimple?@ Anyway, I'll keep@ \
          going, but you'd better not trust what I say next.@."
      end
    with Not_found ->
      Hashtbl.add state.ee_type c.J.catch_with c.J.catch_exception end in
  List.iter hash_catcher cs

let ee_update_in_scope state label =
  let to_add = (try Hashtbl.find state.ee_froms label with Not_found -> []) in
  let to_del = (try Hashtbl.find state.ee_tos label with Not_found -> []) in
  let check mem c =
    HashSet.add state.ee_seen c;
    if HashSet.mem state.ee_scope c <> mem then begin
      if !Config.verbosity >= 2 then
        eprintf "@[@{<b>WARNING@}: weird jimple: repeated label?. @."
    end in
  List.iter (check false) to_add;
  List.iter (check true) to_del;
  List.iter (HashSet.add state.ee_scope) to_add;
  List.iter (HashSet.remove state.ee_scope) to_del

(* NOTE: This name is used by the error handlers in jimple. Don't change. *)
let ee_excvar_name = "@caughtexception"
let ee_excvar_jimp = J.Var_name (J.Identifier_name ee_excvar_name)
let ee_excvar_form =
  U.mk_plvar ee_excvar_name

let ee_encode_label state label =
  let s = JG.Label_stmt label in
  try
    let t = Hashtbl.find state.ee_type label in
    let type_ok = Jlogic.mk_statictyp ee_excvar_form t in
    let assume_type =
      JG.Spec_stmt
        { Core.asgn_rets = []
        ; asgn_rets_formal = []
        ; asgn_args = []
        ; asgn_args_formal = []
        ; asgn_spec = CoreOps.mk_assume type_ok } in
    [ s; assume_type ]
  with Not_found -> [s]

let ee_encode_throw state e =
  let withs =
    HashSet.fold (fun c xs -> c.J.catch_with :: xs) state.ee_scope [] in
  [ JG.Assign_stmt (ee_excvar_jimp, J.Immediate_exp e)
  ; JG.Goto_stmt withs ]

let ee_check_post state =
  if !Config.verbosity >= 2 then begin
    if HashSet.length state.ee_scope <> 0 then
      eprintf "@[@{<b>WARNING@}: scope of error handler doesn't end.@."
  end

(* }}} *)
let encode_exceptions xs ys =
  let state = ee_init_state xs ys in
  ee_hash_catchers state ys;
  let map_stmt f (a, b) = List.map (fun a -> (a, b)) (f a) in
  let process_statement = function
    | JG.Label_stmt label ->
        ee_update_in_scope state label;
        ee_encode_label state label
    | JG.Throw_stmt v -> ee_encode_throw state v
    | s -> [s] in
  let xs = xs >>= map_stmt process_statement in
  ee_check_post state;
  xs

let make_stmts_list =
  let get_statement = function
    | JG.DOS_stm s -> Some s
    | _ -> None in
  let body (xs, ys) =
    let xs = map_option get_statement xs in
    encode_exceptions xs ys in
  option [] body
  (* TODO(rgrig): I kept the empty body default from previous code, but it's
  highly dubious. *)

let member2methdec cname m =
  match m with
  | JG.Method(mo,t,n,p,thc,rc,ocs,ec,mb) ->
      let rlocs=get_locals rc in
      let rstmts=make_stmts_list rc in
      let ostmts_list= List.map make_stmts_list ocs in
      let elocs=get_locals ec in
      let estms=make_stmts_list ec in
      let locs=get_locals mb in
      let bstmts= make_stmts_list mb in
      Some(make_methdec mo cname t n p thc (rlocs,rstmts) ostmts_list (elocs,estms) (locs,bstmts))
  | _ -> None



let make_methdecs_of_list cname meml =
  map_option (member2methdec cname) meml


let get_msig m cname =
  (cname,m.JG.ret_type,m.JG.name_m,m.JG.params)

let has_body m =
        List.for_all ((<>) J.Abstract) m.JG.modifiers

let has_requires_clause m =
        m.JG.req_stmts <> []

let has_ensures_clause m =
        m.JG.ens_stmts <> []

(* ========================  ======================== *)
