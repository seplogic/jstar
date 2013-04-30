open Corestar_std

module PS = Psyntax
module TM = ToplMonitor

(* TODO(rgrig): Use the more high-level functions in [Psyntax] if possible. *)

type toplPVars =
  { state : PS.args
  ; store : PS.args TM.RMap.t
  ; size : PS.args
  ; queue : PS.args array array }
  (* INV: Each [PS.args] above should be [Arg_var _]. *)

let list_mapi f l =
  let i = ref(-1) in List.map (fun a -> f (incr i; !i) a) l

let rec range i j = (* [i; i+1; ...; j-1] *)
  if i >= j then [] else i :: range (i + 1) j

let wrap_call_arg a = PS.mkVar( CoreOps.parameter_var a)

let get_specs_for_enqueue pv =
  let q_sz = Array.length pv.queue in
  let e_sz = Array.length pv.queue.(0) in
  let specs = HashSet.create 0 in
  for i = 0 to q_sz - 1 do begin
    let e = pv.queue.(i) in
    let pre = [PS.P_EQ(pv.size, PS.mkArgint i)] in
    let post =
      let cp i = PS.P_EQ (e.(i), wrap_call_arg i) in
      PS.P_EQ (pv.size, PS.mkArgint (i+1))
      :: List.map cp (range 0 e_sz) in
    HashSet.add specs { Core.pre; post }
  end done;
  specs

let max_label_length_for_vertex ll =
  List.fold_right (fun l m -> max m (List.length l.TM.steps)) ll 0

let max_label_length a =
  TM.VMap.fold (fun _ tl n -> max n (max_label_length_for_vertex tl)) a.TM.transitions 0

let max_arg a =
  let map_max f xs = xs |> List.map f |> List.fold_left max 0 in
  let rec max_arg_guard = function
    | TM.EqCt (i, _) | TM.EqReg (i, _) -> i
    | TM.Not g -> max_arg_guard g
    | TM.And gs -> map_max max_arg_guard gs
    | TM.True -> 0 in
  let max_arg_action a = TM.RMap.fold (fun _ -> max) a 0 in
  let max_arg_step s =
    max (max_arg_guard s.TM.guard) (max_arg_action s.TM.action) in
  let max_arg_trans t = map_max max_arg_step t.TM.steps in
  let max_arg_vertex _ ts y = max y (map_max max_arg_trans ts) in
  TM.VMap.fold max_arg_vertex a.TM.transitions 0

let make_event_queue m n =
  let mk_name i j = Printf.sprintf "queue_event_%d_position_%d" i j in
  Array.init m
    (fun i -> Array.init n (fun j ->
      PS.Arg_var (Vars.concretep_str (mk_name i j))))

let mk_terms prefix set =
  let f s = StringMap.add s (PS.Arg_var (Vars.concretep_str (prefix^s))) in
  StringSet.fold f set StringMap.empty

let rec get_regs_from_guard s = function
  | TM.EqReg (_, r) -> StringSet.add r s
  | TM.Not g -> get_regs_from_guard s g
  | TM.And gs -> List.fold_left get_regs_from_guard s gs
  | _ -> s

let get_regs_from_action =
  TM.RMap.fold (fun r _ s -> StringSet.add r s)

let make_registers a =
  mk_terms "register_"
  (TM.VMap.fold (fun _ tl m ->
    List.fold_left (fun m1 tr ->
      List.fold_left (fun m2 st ->
        let m3 = get_regs_from_guard m2 st.TM.guard in
        get_regs_from_action st.TM.action m3) m1 tr.TM.steps ) m tl ) a.TM.transitions
        StringSet.empty)

(* Create a set of logical variables corresponding to the store. Each such set is indexed
   with the transition j examined, and the step i inside the transition. The value -1 for j
   means a logical copy common to all transitions from a given vertex. *)
let make_logical_copy_of_store st i j =
  let mk_name =
    let t = if j < 0 then "" else Printf.sprintf "_trans_%d" j in
    fun r -> Printf.sprintf "log_register_%s_%d%s" r i t in
  let mk_var r = r |> mk_name |> Vars.concretee_str |> PS.mkVar in
  TM.RMap.mapi (fun r _ -> mk_var r) st

let store_eq st l_st =
  TM.RMap.fold (fun r v f -> PS.P_EQ (v, TM.VMap.find r l_st) :: f) st []

let init_TOPL_program_vars a =
  let st = PS.mkVar(Vars.concretep_str "current_automaton_state") in
  let sr = make_registers a in
  let sz = PS.mkVar(Vars.concretep_str "current_queue_list_size") in
  let e = make_event_queue (max_label_length a) (2 + max_arg a) in
  { state=st; store=sr; size=sz; queue=e }

let make_logical_copy_of_queue e =
  let mM = Array.length e in
  let nN = Array.length e.(0) in
  let el = Array.make_matrix mM nN (PS.mkString("dummy")) in
  let ef = ref [] in
  let set_el i j = el.(i).(j)
    <- PS.Arg_var(Vars.concretee_str ("log_queue_"^(string_of_int i)^"_"^(string_of_int j))) in
  let set_ef i j x = ef =:: PS.P_EQ(x,el.(i).(j)) in
  Array.iteri (fun i x -> Array.iteri (fun j eij -> set_el i j; set_ef i j eij) x) e;
  (el, !ef)

let logical_dequeue e el n =
  let ef = ref [] in
  for i = 0 to (Array.length e)-n-1 do
    for j = 0 to (Array.length e.(0)) do ef =:: PS.P_EQ(e.(i).(j),el.(i+n).(j))
    done;
  done;
  !ef

(* Returns a list with all non-empty subsets of {0,...,n-1} *)
let index_subsets n =
  let xs = ref([IntSet.empty]) in
  for i = 0 to n-1 do
    xs := (List.map (function x -> IntSet.add i x) !xs) @ !xs
  done;
  List.tl !xs

(* TODO(rgrig): Move to [Psyntax]? *)
let rec simplify_pform xs =
  let xs = xs >>= simplify_pform_at in
  if List.mem PS.P_False xs then [PS.P_False] else xs
and simplify_pform_at = function
  | PS.P_Or (x, y) ->
      (match (simplify_pform x, simplify_pform y) with
        | [], _ | _, [] -> []
        | [PS.P_False], z | z, [PS.P_False] -> z
        | x, y -> [PS.P_Or (x, y)])
  | PS.P_EQ _ as x -> [x]
  | PS.P_NEQ _ as x -> [x]
  | _ -> failwith "Internal: simplification of and/or with true/false"

let rec negate_specs_it (f:PS.pform) : PS.pform_at =
    match f with
      | [] -> PS.P_False
      | z :: fs ->
        (match z with
          | PS.P_EQ(x,y) -> PS.P_Or([PS.P_NEQ(x,y)], [negate_specs_it fs])
          | PS.P_NEQ(x,y) -> PS.P_Or([PS.P_EQ(x,y)], [negate_specs_it fs])
          | PS.P_PPred(_,_) -> failwith "Negation called for PPred!"
          | PS.P_SPred(_,_) -> failwith "Negation called for SPred!"
          | PS.P_Wand(_,_) -> failwith "Negation called for Wand!"
          | PS.P_Or(x,y) -> PS.P_Or([(negate_specs_it x); (negate_specs_it y)], [negate_specs_it fs])
          | PS.P_Septract(_,_) -> failwith "Negation called for Septract!"
          | PS.P_False -> failwith "Internal negation loop reached False!")

(* Performs a rather unsophisticated negation of pforms built out of PS.P_EQ,PS.P_NEQ,PS.P_False and PS.P_Or *)
let negate_pforms (f:PS.pform) : PS.pform =
  let f' = simplify_pform f in
  let f'' = match f' with
      | [PS.P_False] -> []
      | _ -> [negate_specs_it f']
  in simplify_pform f''

(* Returns a pform given guard gd, assuming that value i of each event is stored in
   e.(i+1) in event queue *)
let rec guard_conditions gd e st =
  match gd with
    | TM.True -> []
    | TM.EqCt (i,v) -> PS.mkEQ (e.(i+1), v)
    | TM.EqReg (i,r) -> PS.mkEQ (e.(i+1), TM.RMap.find r st)
    | TM.Not g -> negate_pforms (guard_conditions g e st)
    | TM.And gs -> gs >>= (fun g -> guard_conditions g e st)

let obs_conditions e { TM.event_time; pattern } =
  let ev_name proc_name = PS.mkString (Printf.sprintf "Call_$$_%s" proc_name) in
  let proc_cond proc_name = PS.mkEQ (e.(0), ev_name proc_name) in
  PS.mkBigOr (List.map proc_cond pattern)

(* Conditions for e being satisfied by (st,s) and leading to st' *)
let step_conditions e st st' s =
  let gd = s.TM.guard in
  let ac = s.TM.action in
  let ev_cond = obs_conditions e s.TM.observables in
  let gd_cond = guard_conditions gd e st in
  let ac_cond = TM.VMap.fold (fun r v f ->
    if (TM.RMap.mem r ac) then (PS.P_EQ(v, e.(TM.RMap.find r ac))::f)
    else (PS.P_EQ(v, TM.VMap.find r st)::f)) st' [] in
  simplify_pform (ev_cond @ gd_cond @ ac_cond)

let pDeQu n pv el =
  let m = Array.length pv.queue in
  PS.P_EQ(pv.size, PS.mkArgint (m-n)) :: (logical_dequeue pv.queue el n)

let trans_pre_and_post pv el l_sr0 j t =
  let st = t.TM.steps in
  let tg = t.TM.target in
  let len = List.length st in
  let sr = pv.store in
  let l_sr =  Array.init (len+1) ( fun i ->
    if i=0 then l_sr0 else make_logical_copy_of_store sr i j ) in
  let pre = List.flatten (list_mapi (fun i s ->
      step_conditions pv.queue.(i) l_sr.(i) l_sr.(i+1) s) st) in
  let post = [PS.P_EQ(pv.state, PS.Arg_string(tg))]
    @ (store_eq sr l_sr.(len)) @ (pDeQu len pv el) in (pre,post)


(* Given a set of indices k, negate all formulas in l whose index appears in k,
   and leave all other formulas intact *)
let sign_pres k l =
  list_mapi (fun i x -> if (IntSet.mem i k) then x else negate_pforms x) l

(* Given a set of indices k, P-Or all formulas in l whose index appears in k *)
let sign_POr_posts k xs =
  let xs = list_mapi (fun i x -> if (IntSet.mem i k) then x else PS.mkFalse) xs in
  PS.mkBigOr xs

let get_specs_for_vertex t pv v s =
  let tl = (try TM.VMap.find v t with Not_found -> []) in
  let pAt = [PS.P_EQ(pv.state, PS.Arg_string v)] in
  (* let m = max_label_length_for_vertex tl in *)
  (* Qud below is defined differently than in the notes: in order to avoid the burden of
     trying to express e.(size-1).(0) = #, we just pad with #'s at the end of the main method. *)
  let (el,ef) = make_logical_copy_of_queue pv.queue in
  let mM = Array.length pv.queue in
  let pQud = PS.P_EQ(pv.size, PS.mkArgint mM) :: ef in
  let l_sr0 = make_logical_copy_of_store pv.store 0 (-1) in
  let pInit = store_eq pv.store l_sr0 in
  let (pAllSats,pAllPosts) = List.split (list_mapi (trans_pre_and_post pv el l_sr0) tl) in
  let s_skip =
    let pre = pAt @ pInit @ pQud @ List.flatten (sign_pres IntSet.empty pAllSats) in
    let post = pAt @ pInit @ (pDeQu 1 pv el) in
    [{ Core.pre; post }] in
  let subs = index_subsets (List.length tl) in
  let s_regular = List.map
    ( fun k ->
      let pre = pAt @ pInit @ pQud @ List.flatten (sign_pres k pAllSats) in
      let post = sign_POr_posts k pAllPosts in
      { Core.pre; post }) subs in
  s_regular @ s_skip @ s

let get_specs_for_step a pv =
  HashSet.of_list (TM.VSet.fold (get_specs_for_vertex a.TM.transitions pv) a.TM.vertices [])
