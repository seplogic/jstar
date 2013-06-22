(* modules *) (* {{{ *)
open Corestar_std
open Debug
open Format

module C = Core
module A = Topl.PropAst
module J = Jparsetree
module JG = Jimple_global_types
module TM = ToplMonitor
module TN = ToplNames

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

(* }}} *)
(* small functions that help handling automata *) (* {{{ *)
let get_vertices p =
  let f acc t = t.A.source :: t.A.target :: acc in
  "start" :: "error" :: List.fold_left f [] p.A.transitions

(* }}} *)
(* conversion to ToplMonitor representation *) (* {{{ *)
let convert_guard guard =
  let convert = function
    | A.Variable (vr, i) -> TM.EqReg (i, vr)
    | A.Constant (vl, i) -> TM.EqCt (i, vl) in
  TM.And (List.map convert guard.A.value_guards)

let convert_action = List.fold_left (fun m (k, v) -> TM.VMap.add k v m) TM.VMap.empty

let convert_event_time = function
  | Some A.Call -> TM.Call_time
  | Some A.Return -> TM.Return_time
  | None -> TM.Any_time

let print_pro_transition t s =
  let print_l l = 
    let tg = l.A.guard.A.tag_guard in
    let event_type = match tg.A.event_type with
      | Some A.Call -> "call "
      | Some A.Return -> "return "
      | None -> "" in
    Format.printf "- %smethod: %s\n" event_type tg.A.method_name.A.p_string in
  Format.printf "Pro_transition (%s) from %s to %s with %d labels:\n" s t.A.source t.A.target
    (List.length t.A.labels);
  List.iter print_l t.A.labels

let prefix_vertex p v = p.A.name ^ v

let convert_transition p t : (A.pattern list * int option) TM.transition =
  (* debug *) Format.printf "\n Calling convert_transition\n";
  (* debug *) print_pro_transition t "CV";
  let convert_label l =
    let guard = convert_guard l.A.guard in
    let action = convert_action l.A.action in
    let p_arity = snd l.A.guard.A.tag_guard.A.method_arity in
    let p_mname = [l.A.guard.A.tag_guard.A.method_name; p.A.observable] in
    let pattern = (p_mname, p_arity) in
    let event_time = convert_event_time l.A.guard.A.tag_guard.A.event_type in
    let observables = { TM.event_time; pattern } in
    { TM.guard; action; observables } in
  let retn = { TM.steps = List.map convert_label t.A.labels
             ; TM.target = prefix_vertex p t.A.target } in
  (* debug *) Format.printf "-> After conversion: %d steps\n" (List.length retn.TM.steps);
  retn 

let construct_monitor ts =
  let convert_prop p =
    (* debug *) List.iter (fun t -> print_pro_transition t "p") p.A.transitions;
    let add_v v (vs, starts, errors) =
      let pv = prefix_vertex p v  in
      let new_vs = TM.VSet.add pv vs in
      if v = "start" then new_vs, TM.VSet.add pv starts, errors
      else if v = "error" then new_vs, starts, TM.VMap.add pv p.A.message errors
      else starts, new_vs, errors in
    let collect_transition (vs, ts, starts, errors) t =
      let new_vs, new_starts, new_errors = (vs,starts,errors) |> add_v t.A.source |> add_v t.A.target in
      let transition = convert_transition p t in
      let new_source = prefix_vertex p t.A.source in 
      let outgoing = try TM.VMap.find new_source ts with Not_found -> [] in
      let new_ts = TM.VMap.add new_source (transition::outgoing) ts in
      new_vs, new_ts, new_starts, new_errors in
    let vertices, transitions, start_vertices, errors =
      List.fold_left
	collect_transition
	(TM.VSet.empty, TM.VMap.empty, TM.VSet.empty, TM.VMap.empty)
	p.A.transitions in
    { TM.vertices = vertices
    ; TM.start_vertices = start_vertices
    ; TM.error_messages = errors
    ; TM.transitions = transitions } in
  let map_union m1 m2 = TM.VMap.merge (fun _ a b -> match a, b with Some _, _ -> a | None, Some _ -> b | _ -> None) m1 m2 in
  let collect_prop acc p =
    let ap = convert_prop p in
    { TM.vertices = TM.VSet.union acc.TM.vertices ap.TM.vertices
    ; TM.start_vertices = TM.VSet.union acc.TM.start_vertices ap.TM.start_vertices
    ; TM.error_messages = map_union acc.TM.error_messages ap.TM.error_messages
    ; TM.transitions = map_union acc.TM.transitions ap.TM.transitions } in
  List.fold_left collect_prop TM.empty_automaton ts

(* }}} *)
(* parse values *) (* {{{ *)
let parse_values topl =
  let pv_v v = Jparser.jargument Jlexer.token & Lexing.from_string v in
  let pv_vg = function
    | A.Variable _ as vg -> vg
    | A.Constant (v, i) -> A.Constant (pv_v v, i) in
  let pv_guard g =
    { g with A.value_guards = List.map pv_vg g.A.value_guards } in
  let pv_label l = { l with A.guard = pv_guard l.A.guard } in
  let pv_transition t = { t with A.labels = List.map pv_label t.A.labels } in
  { topl with A.transitions = List.map pv_transition topl.A.transitions }

(* }}} *)
(* specialize monitor *) (* {{{ *)
let mk_hl_name cn mn =
  Printf.sprintf "%s.%s" cn mn

(* RET: cname -> (((hl_mname * arity) -> ll_mname list) * extends list) *)
let hash_by_names =
  let key_of_class (JG.JFile (_, _, cn, _, _, _)) =
    Some (string_of J.pp_class_name cn) in
  let val_of_class (JG.JFile (_, _, cn, xs, ys, ms)) =
    let key_of_method = function
      | JG.Field _ -> None
      | JG.Method (first, _, mn, ps, _, _, _, _, _) ->
        Some (string_of J.pp_name mn,  (if (List.mem J.Static first) then 0 else 1) + (List.length ps)) in
    let val_of_method = function
      | JG.Field _ -> None
      | JG.Method (_, rt, mn, ps, _, _, _, _, _) ->
          Some (Translatejimple.msig2str cn rt mn ps) in
    let one x = [x] in
    let zs = List.map (string_of J.pp_class_name) (xs @ ys) in
    Some (Misc.hash_of_list one cons key_of_method val_of_method ms, zs) in
  Misc.hash_of_list (fun x -> x) undefined key_of_class val_of_class

let get_overrides index cn mn arity =
  let seen = HashSet.create 0 in
  let empty = Hashtbl.create 0 in
  let rec f acc cn =
    if not (HashSet.mem seen cn) then begin
      HashSet.add seen cn;
      let mh, parents =
        (try Hashtbl.find index cn with Not_found -> empty, []) in
      let acc =
        if Hashtbl.mem mh (mn, arity) then mk_hl_name cn mn :: acc else acc in
      List.fold_left f acc parents
    end else acc in
  f [] cn

let collect_patterns m =
  let h = Hashtbl.create 0 in
  let cp_ev e = Hashtbl.replace h e.TM.pattern [] in
  let cp_step s = cp_ev s.TM.observables in
  let cp_transition t = List.iter cp_step t.TM.steps in
  let cp_vertex _ = List.iter cp_transition in
  TM.VMap.iter cp_vertex m.TM.transitions;
  h

let print_automaton a s =
  let print_t t = Format.printf "- transition to %s in %d steps\n" t.TM.target (List.length t.TM.steps) in
  let print_v v ts = Format.printf "\n PreProc %s Vertex: %s with %d transitions\n" s v (List.length ts); List.iter
    print_t ts in
  TM.VMap.iter print_v a.TM.transitions

let map_patterns h m =
  (* debug *) print_automaton m "map_patterns";
  let mp_ev e = { e with TM.pattern = Hashtbl.find h e.TM.pattern } in
  let mp_step s = { s with TM.observables = mp_ev s.TM.observables } in
  let mp_transition t = { t with TM.steps = List.map mp_step t.TM.steps } in
  let mp_vertex = List.map mp_transition in
  { m with TM.transitions = TM.VMap.map mp_vertex m.TM.transitions }

let specialize_monitor js m =
  (* debug *) print_automaton m "specialize_monitor";
  let index = hash_by_names js in
  let patterns = collect_patterns m in
  let process_class cname (ms_index, _) =
    (* debug *) Hashtbl.iter (fun (x,i) ys -> 
      Format.printf "Print in class %s: (%s,%d)\n" cname x i;
      List. iter (Format.printf "=> %s\n") ys) ms_index;
    let process_method (hl_name, arity) ll_mns =
      let overrides = get_overrides index cname hl_name arity in
      let process_pattern p old_ll_mns acc =
        let p_rs, p_arity = p in
        let log_pattern_match a b = let r = A.pattern_matches a b in printf "@[%s =?= %s is %b@\n@]" a.A.p_string b r; r in
        let name_matches mn = List.for_all (flip log_pattern_match mn) p_rs in
        (* debug *) Format.printf "-> Doing an arity check: %d and %d for hl_name: %s\n" (option (-1) (fun x->x) p_arity) arity hl_name;
        let resolve_none = match p_arity with
          | Some x -> (arity = x) 
          | None -> true in
        if resolve_none && List.exists name_matches overrides 
        then (p, ll_mns @ old_ll_mns) :: acc
        else acc in 
      let updates = Hashtbl.fold process_pattern patterns [] in
      List.iter (fun (p, vs) -> Hashtbl.replace patterns p vs) updates in
    Hashtbl.iter process_method ms_index in
  Hashtbl.iter process_class index;
  map_patterns patterns m

(* }}} *)
(* Instrument procedures code *) (* {{{ *)

let compute_arg_counts ps =
  let h = Hashtbl.create 0 in
  let get name = (try Hashtbl.find h name with Not_found -> (0, 0)) in
  let set name args rets =
    let old_args, old_rets = get name in
    Hashtbl.replace h name (max args old_args, max rets old_rets) in
  let statement = function
    | C.Call_core c ->
        let args = List.length c.C.call_args in
        let rets = List.length c.C.call_rets in
        set c.C.call_name args rets
    | _ -> () in
  let body = option () (List.iter statement) in
  let proc p = body p.C.proc_body in
  List.iter proc ps;
  (fst @@ get, snd @@ get)


let iter_wrap w n =
  let rec f acc i =
    if i<0 then List.rev acc
    else f (w i :: acc) (i-1)
  in f [] (n-1)

let wrap_ret_arg a = CoreOps.return_var a
let wrap_call_arg a = Psyntax.mkVar (CoreOps.parameter_var a)

let make_instrumented_proc_pair (get_arg_cnt, get_ret_cnt) p =
  let proc' = {C.proc_name=p.C.proc_name^"_I"; proc_spec=p.C.proc_spec; proc_body=p.C.proc_body; proc_rules=p.C.proc_rules} in
  let call_args = iter_wrap wrap_call_arg (get_arg_cnt p.C.proc_name) in
  let call_rets = iter_wrap wrap_ret_arg (get_ret_cnt p.C.proc_name) in
  let emit_call =
    { C.call_name = "emit_$$"
    ; call_rets =[]
    ; call_args = TN.call_event p.C.proc_name :: call_args } in
  let call_p' = { C.call_name = p.C.proc_name^"_I"; call_rets; call_args } in
  let emit_ret =
    { C.call_name = "emit_$$"
    ; call_rets = []
    ; call_args = [ TN.return_event p.C.proc_name ] } in (* TODO(rgrig): return values *)
  let proc_body = Some ([C.Call_core emit_call; C.Call_core call_p' ; C.Call_core emit_ret])  in
  let proc = {C.proc_name=p.C.proc_name; proc_spec=HashSet.create 0; proc_body; proc_rules=Psyntax.empty_logic} in
  [proc; proc']

let instrument_procedures ps =
  let arg_counts = compute_arg_counts ps in
  ps >>= make_instrumented_proc_pair arg_counts

(* End instrument procedures code *) (* }}} *)
(* Add emit and friends *) (* {{{ *)

(* this procedure expects the event to be emitted, and the condition for the assert statement *)
let emit_proc a pv =
  let e_sz = Array.length pv.ToplSpecs.queue.(0) in
  let call_args = iter_wrap wrap_call_arg e_sz in
  let call_enqueue = {C.call_name = "enqueue_$$"; C.call_rets=[]; call_args} in
  let call_step = {C.call_name = "step_$$"; C.call_rets=[]; C.call_args=[]} in
  let errors = TM.VMap.fold (fun k _ acc -> k :: acc) a.TM.error_messages [] in
  let f = errors >>= (fun e -> Psyntax.mkNEQ(pv.ToplSpecs.state, Psyntax.mkString e)) in
  let asgn_assert = { C.asgn_rets=[]; asgn_args=[]; asgn_spec = HashSet.singleton {C.pre=f; post=f} } in
  let emit_body =Some ([C.Call_core call_enqueue; C.Call_core call_step; C.Assignment_core asgn_assert]) in
  { C.proc_name = "emit_$$"; C.proc_spec = (HashSet.create 0); C.proc_body = emit_body;
    C.proc_rules = Psyntax.empty_logic }

let step_proc a pv =
  let proc_spec = ToplSpecs.get_specs_for_step a pv in
  { C.proc_name = "step_$$"; proc_spec; proc_body=None; C.proc_rules=Psyntax.empty_logic }

let enqueue_proc pv =
  let proc_spec = ToplSpecs.get_specs_for_enqueue pv in
  { C.proc_name = "enqueue_$$"; proc_spec; proc_body=None; C.proc_rules=Psyntax.empty_logic }

let build_core_monitor m =
   let pv = ToplSpecs.init_TOPL_program_vars m in
   [ emit_proc m pv; step_proc m pv; enqueue_proc pv ]

(* End emit and friends *) (* }}} *)
(* main *) (* {{{ *)

let read_properties fs =
  (* debug *) List.iter (Format.printf "= Initial input: %s\n") fs;
  let retn = fs |> List.map Topl.Helper.parse >>= List.map (fun x -> x.A.ast) in
  (* debug *) List.iter (fun x -> 
    List.iter (fun t -> print_pro_transition t "RP") x.A.transitions) retn;
  retn 

let compile js ts =
  (* debug *) List.iter (fun x -> 
    List.iter (fun t -> print_pro_transition t "Compile") x.A.transitions) ts;
  let monitor = construct_monitor ts in
  (* debug *) print_automaton monitor "after_construct";
  let monitor = specialize_monitor js monitor in
  build_core_monitor monitor

(* }}} *)
