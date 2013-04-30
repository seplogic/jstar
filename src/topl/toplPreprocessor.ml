(* modules *) (* {{{ *)
open Corestar_std
open Debug
open Format

module C = Core
module A = Topl.PropAst
module JG = Jimple_global_types

(* }}} *)
(* used to communicate between conversion and instrumentation *) (* {{{ *)
type method_ =  (* TODO: Use [PropAst.event_tag] instead? *)
  { method_name : string
  ; method_arity : int }

(* }}} *)
(* representation of automata in Java *) (* {{{ *)

(*
  The instrumenter has three phases:
    - convert the topl property to the topl monitor
    - convert high-level patterns (java/jimple regex)
      to low-level ones (lists of corestar procedure names, esentially)
    - generate specs that encode the behavior of the monitor
  A pattern like "c.m()" in the property matches method m in all classes that
  extend c (including c itself). For efficiency, the Java automaton does not
  know anything about inheritance. While the bytecode is instrumented all the
  methods m in classes extending c get unique identifiers and the pattern
  "c.m()" is mapped to the set of those identifiers.

  The (first) conversion
    - goes from edge list to adjacency list
    - glues all input properties into one
    - normalizes method patterns (by processing "using prefix", ... )
    - collects all patterns
 *)

(* shorthands for old types, those that come from prop.mly *)
type property = (string, string) A.t
type tag_guard = A.pattern A.tag_guard

(* small functions that help handling automata *) (* {{{ *)
let get_vertices p =
  let f acc t = t.A.source :: t.A.target :: acc in
  "start" :: "error" :: List.fold_left f [] p.A.transitions

(* }}} *)
let generate_checkers out_dir p =
  failwith "XXX"
  (*
  check_automaton p;
  let (/) = Filename.concat in
  U.cp_r (Config.topl_dir/"src"/"topl") out_dir;
  let topl_dir = out_dir/"topl" in
  let o n =
    let c = open_out (topl_dir/("Property." ^ n)) in
    let f = formatter_of_out_channel c in
    (c, f) in
  let (jc, j), (tc, t) = o "java", o "text" in
  let sc = open_out (topl_dir/"Property.strings") in
  let index = mk_pp_index p in
  fprintf j "@[%a@." pp_constants_table index;
  pp_strings_nonl sc index;
  fprintf t "@[%a@." (pp_automaton index) p;
  List.iter close_out_noerr [jc; tc; sc];
  ignore (Sys.command
    (Printf.sprintf
      "javac -sourcepath %s %s"
      (U.command_escape out_dir)
      (U.command_escape (topl_dir/"Property.java")))) *)

(* }}} *)
(* conversion to Java representation *) (* {{{ *)

let index_for_var ifv v =
  try
    Hashtbl.find ifv v
  with Not_found ->
    let i = Hashtbl.length ifv in
      Hashtbl.replace ifv v i; i

let transform_tag_guard ptags tg =
  Hashtbl.replace ptags tg []; tg

let transform_value_guard ifv = function
  | A.Variable (v, i) -> A.Variable (index_for_var ifv v, i)
  | A.Constant (c, i) -> A.Constant (c, i)

let transform_guard ifv ptags {A.tag_guard=tg; A.value_guards=vgs} =
  { A.tag_guard = transform_tag_guard ptags tg
  ; A.value_guards = List.map (transform_value_guard ifv) vgs }

let transform_condition ifv (store_var, event_index) =
  let store_index = index_for_var ifv store_var in
    (store_index, event_index)

let transform_action ifv a = List.map (transform_condition ifv) a

let transform_label ifv ptags {A.guard=g; A.action=a} =
  { A.guard = transform_guard ifv ptags g
  ; A.action = transform_action ifv a }

  (*
let transform_properties ps =
  let vs p = p |> get_vertices |> List.map (fun v -> (p, v)) in
  let iov = to_ints (ps >>= vs) in
  let mk_vd (p, v) =
    { vertex_property = p
    ; vertex_name = v
    ; outgoing_transitions = [] } in
  let full_p =
    { vertices = inverse_index mk_vd iov
    ; observables = Hashtbl.create 0
    ; pattern_tags = Hashtbl.create 0
    ; event_names = Hashtbl.create 0 } in
  let add_obs_tags p =
    let obs_tag =
      { A.event_type = None
      ; A.method_name = p.A.observable
      ; A.method_arity = (0, None) } in
    Hashtbl.replace full_p.pattern_tags obs_tag [];
    Hashtbl.replace full_p.observables p obs_tag in
  List.iter add_obs_tags ps;
  let add_transition vi t =
    let vs = full_p.vertices in
    let ts = vs.(vi).outgoing_transitions in
    vs.(vi) <- { vs.(vi) with outgoing_transitions = t :: ts } in
  let ifv = Hashtbl.create 0 in (* variable, string -> integer *)
  let pe p {A.source=s;A.target=t;A.labels=ls} =
    let s = Hashtbl.find iov (p, s) in
    let t = Hashtbl.find iov (p, t) in
    let ls = List.map (transform_label ifv full_p.pattern_tags) ls in
    add_transition s {steps=ls; target=t} in
  List.iter (fun p -> List.iter (pe p) p.A.transitions) ps;
  full_p
*)

(* }}} *)
(* bytecode instrumentation *) (* {{{ *)

(*
let does_method_match
  ({ method_name=mn; method_arity=ma }, mt)
  { A.event_type=t; A.method_name=re; A.method_arity=(amin, amax) }
=
  let bamin = amin <= ma in
  let bamax = option true ((<=) ma) amax in
  let bt = option true ((=) mt) t in
  let bn = A.pattern_matches re mn in
  let r = bamin && bamax  && bt && bn in
  if log log_mm then begin
    printf "@\n@[<2>%s " (if r then "✓" else "✗");
    printf "(%a, %s, %d)@ matches (%a, %s, [%d..%a])@ gives (%b, %b, (%b,%b))@]"
      A.pp_event_type mt mn ma
      (pp_option A.pp_event_type) t
      re.A.p_string
      amin
      (pp_option pp_int) amax
      bt bn bamin bamax
  end;
  r

let get_tag x =
  let cnt = ref (-1) in
  fun t (mns, ma) mn ->
    let en = (* event name *)
      fprintf str_formatter "%a %s" A.pp_event_type t mn;
      flush_str_formatter () in
    let fp p acc =
      let cm mn = does_method_match ({method_name=mn; method_arity=ma}, t) p in
      if List.exists cm mns then p :: acc else acc in
    let fpk p _ = fp p in
    let fpv _ = fp in
    if Hashtbl.fold fpv x.observables [] <> [] then begin
      match Hashtbl.fold fpk x.pattern_tags [] with
        | [] -> None
        | ps ->
            incr cnt;
            let at p =
              let ts = Hashtbl.find x.pattern_tags p in
              (* printf "added tag %d\n" !cnt; *)
              Hashtbl.replace x.pattern_tags p (!cnt :: ts);
              Hashtbl.replace x.event_names !cnt en in
            List.iter at ps;
            Some !cnt
    end else None
*)

(* }}} *)
(* specialize monitor *) (* {{{ *)
let get_ancestors h c =
  let cs = Hashtbl.create 0 in
  let rec ga c =
    if not (Hashtbl.mem cs c) then begin
      Hashtbl.add cs c ();
      let parents = try Hashtbl.find h c with Not_found -> [] in
      List.iter ga parents
    end in
  ga c;
  Hashtbl.fold (fun c _ cs -> c :: cs) cs []

let mk_full_method_name c mn = failwith "XXX"
(*  name_of_class c ^ "." ^ mn *)

let get_overrides h c m =
  let ancestors = get_ancestors h c in
  let qualify c =  mk_full_method_name c m.method_name in
  (List.map qualify ancestors, m.method_arity)

let compute_inheritance js =
  let h = Hashtbl.create 0 in
  let record_jimple (JG.JFile (_, _, cn, xs, ys, _)) =
    let cn = Pprinter.class_name2str cn in
    let zs = List.map Pprinter.class_name2str (xs @ ys) in
    Hashtbl.replace h cn zs in
  List.iter record_jimple js;
  h

let hash_of_list key value xs =
  let h = Hashtbl.create (List.length xs) in
  let one x = match key x, value x with
    | None, _ | _, None -> ()
    | Some k, Some v -> assert (not (Hashtbl.mem h k)); Hashtbl.add h k v in
  List.iter one xs;
  h

let hash_by_names =
  let key_of_class (JG.JFile (_, _, cn, _, _, _)) = Some cn in
  let val_of_class (JG.JFile (_, _, cn, xs, ys, ms)) =
    let key_of_member = function
      | JG.Field _ -> None
      | JG.Method (_, _, mn, ps, _, _, _, _, _) -> Some (mn, List.length ps) in
    let val_of_member = function
      | JG.Field _ -> None
      | JG.Method (_, rt, mn, ps, _, _, _, _, _)
          -> Some (Translatejimple.msig2str cn rt mn ps) in
    Some (hash_of_list key_of_member val_of_member ms, xs @ ys) in
  hash_of_list key_of_class val_of_class

let get_overrides cn mn arity =
  failwith "XXX"

let collect_patterns m =
  failwith "XXX"

let specialize_monitor js m =
  let index = hash_by_names js in
  let patterns = collect_patterns m in
  failwith "TODO: from jimple patterns to core proc_name lists; inheritance"

(* }}} *)
(* Instrument procedures code *) (* {{{ *)

let par_proc : (string,(int*int)) Hashtbl.t = Hashtbl.create 100

let rec get_call_stm stml =
  match stml with
  | [] -> []
  | C.Call_core p ::stml' -> C.Call_core p::get_call_stm stml'
  | _::stml' -> get_call_stm stml'

let do_call_stm c_stm =
  match c_stm with
  | C.Call_core c ->
      let num_rets =List.length c.C.call_rets in
      let num_args =List.length c.C.call_args in
      (try
        let (r,a)=Hashtbl.find par_proc c.C.call_name in
        Hashtbl.replace par_proc c.C.call_name (max num_rets r, max num_args a)
      with _ -> Hashtbl.add par_proc c.C.call_name (num_rets,num_args))
  | _ -> assert false

let compute_args procs =
  let call_statements = List.flatten (List.map (fun p -> match p.C.proc_body with
                                  |None -> []
                                  |Some b -> get_call_stm b ) procs) in
  List.iter do_call_stm call_statements


let wrap_ret_args a = CoreOps.return_var a

let wrap_call_args a =  Psyntax.Arg_var( CoreOps.parameter_var a)

let rec iter_wrap w n =
  if n>=0 then
    w n:: iter_wrap w (n-1)
  else []

let get_call_rets p =
  let n= fst (Hashtbl.find par_proc p.C.proc_name) in
  iter_wrap wrap_ret_args n

let get_call_args p =
  let n= snd (Hashtbl.find par_proc p.C.proc_name) in
  iter_wrap wrap_call_args n

let make_call_to_proc p =
  Psyntax.Arg_var(Vars.concretep_str ("call_"^p.C.proc_name))::get_call_args p

let make_ret_from_proc p =
  [Psyntax.Arg_var(Vars.concretep_str ("ret_"^p.C.proc_name))]

let make_instrumented_proc_pair p =
  let proc' = {C.proc_name=p.C.proc_name^"_I"; proc_spec=p.C.proc_spec; proc_body=p.C.proc_body; proc_rules=p.C.proc_rules} in
  let emit_call = {C.call_name = "emit";
                  C.call_rets =[];
                  C.call_args = make_call_to_proc p } in
  let call_p' = {C.call_name = p.C.proc_name^"_I"; call_rets = get_call_rets p; call_args = get_call_args p} in
  let emit_ret = {C.call_name = "emit";
                 call_rets =[];
                 call_args = make_ret_from_proc p } in
  let proc_body = Some ([C.Call_core emit_call; C.Call_core call_p' ; C.Call_core emit_ret])  in
  let proc = {C.proc_name=p.C.proc_name; proc_spec=HashSet.create 0; proc_body; proc_rules=Psyntax.empty_logic} in
  [proc; proc']

let instrument_procedures ps =
  ps >>= make_instrumented_proc_pair

(* End instrument procedures code *) (* }}} *)
(* main *) (* {{{ *)

let read_properties fs =
  fs |> List.map Topl.Helper.parse >>= List.map (fun x -> x.A.ast)

let construct_monitor ts =
  failwith "TODO: edge list to adj list and other rep stuff"

let build_core_monitor m =
  failwith "TODO: from ToplMonitor.automaton to Core.ast_procedure list"

let compile js ts =
  let monitor = construct_monitor ts in
  let monitor = specialize_monitor js monitor in
  build_core_monitor monitor

(* }}} *)
