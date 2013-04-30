open Corestar_std
open Psyntax
open ToplMonitor

type toplPVars =
    { state : Psyntax.args;
      store : Psyntax.args RMap.t;
      size : Psyntax.args;
      queue : Psyntax.args array array }
(* Can I specify that the above should be Arg_vars of PVars? *)

let list_mapi f l =
  let i = ref(-1) in List.map (fun a -> f (incr i; !i) a) l

let arg_from_event ev =
  let x = match ev.event_time with
    | Call_time -> "Call_$$_"^ev.proc_name
    | Return_time -> "Return_$$_"^ev.proc_name in
  Psyntax.Arg_string x

(*
let enqueue_letter_specs lt pv =
  let mM = Array.length pv.queue in
  let ev = lt.event in
  let vs = lt.data in
  let specs = ListH.init mM (fun i ->
    let e = pv.queue.(i) in
    let pre = [P_EQ(pv.size, Psyntax.mkArgint i)] in
    let post = [P_EQ(e.(0), arg_from_event ev); P_EQ(pv.size, Psyntax.mkArgint
    (i+1))]
      @ (list_mapi (fun i v -> P_EQ(e.(i+1), v)) vs) in
    { Core.pre = pre; post = post }) in
  HashSet.of_list specs
*)

let rec range i j = (* [i; i+1; ...; j-1] *)
  if i = j then [] else i :: range (i + 1) j

let enqueue_specs pv =
  let q_sz = Array.length pv.queue in
  let e_sz = Array.length pv.queue.(0) in
  let specs = HashSet.create 0 in
  for i = 0 to q_sz - 1 do begin
    let e = pv.queue.(i) in
    let pre = [P_EQ(pv.size, Psyntax.mkArgint i)] in
    let post =
      let cp i = P_EQ (e.(i), Arg_var (CoreOps.parameter_var i)) in
      P_EQ (pv.size, Psyntax.mkArgint (i+1))
      :: List.map cp (range 0 e_sz) in
    HashSet.add specs { Core.pre; post }
  end done;
  specs

let max_label_length_for_vertex ( ll:transition list ) =
  List.fold_right (fun l m -> max m (List.length l.steps)) ll 0

let max_label_length ( a:automaton ) =
  VMap.fold (fun _ tl n -> max n (max_label_length_for_vertex tl)) a.transitions 0

let max_arg a =
  let map_max f xs = xs |> List.map f |> List.fold_left max 0 in
  let rec max_arg_guard = function
    | EqCt (i, _) | EqReg (i, _) -> i
    | Not g -> max_arg_guard g
    | And gs -> map_max max_arg_guard gs
    | True -> 0 in
  let max_arg_action a = RMap.fold (fun _ -> max) a 0 in
  let max_arg_step s = max (max_arg_guard s.guard) (max_arg_action s.action) in
  let max_arg_trans t = map_max max_arg_step t.steps in
  let max_arg_vertex _ ts y = max y (map_max max_arg_trans ts) in
  VMap.fold max_arg_vertex a.transitions 0

let make_event_queue m n =
  let mk_name i j = Printf.sprintf "queue_event_%d_position_%d" i j in
  Array.init m
    (fun i -> Array.init n (fun j ->
      Psyntax.Arg_var (Vars.concretep_str (mk_name i j))))

let mk_terms prefix set =
  let f s = StringMap.add s (Psyntax.Arg_var (Vars.concretep_str (prefix^s))) in
  StringSet.fold f set StringMap.empty

let rec get_regs_from_guard s = function
    | EqReg(_,r) -> StringSet.add r s
    | Not(g) -> get_regs_from_guard s g
    | And(gl) -> List.fold_left get_regs_from_guard s gl
    | _ -> s

let get_regs_from_action =
  RMap.fold (fun r _ s -> StringSet.add r s)

let make_registers ( a:automaton ) =
  mk_terms "register_"
  (VMap.fold (fun _ tl m ->
    List.fold_left (fun m1 tr ->
      List.fold_left (fun m2 st ->
        let m3 = get_regs_from_guard m2 st.guard in
        get_regs_from_action st.action m3) m1 tr.steps ) m tl ) a.transitions
        StringSet.empty)

(* Create a set of logical variables corresponding to the store. Each such set is indexed
   with the transition j examined, and the step i inside the transition. The value -1 for j
   means a logical copy common to all transitions from a given vertex. *)
let make_logical_copy_of_store st i j =
  if j = -1 then 
  RMap.mapi (fun r _ -> Psyntax.Arg_var(Vars.concretee_str (Printf.sprintf
                                                              "log_register_%s_%d" r i))) st
  else RMap.mapi (fun r _ -> Psyntax.Arg_var(Vars.concretee_str (Printf.sprintf
                                                              "log_register_%s_%d_trans_%d" r i j))) st

let store_eq st l_st =
  RMap.fold (fun r v f -> P_EQ(v,(VMap.find r l_st)) :: f) st []

let init_TOPL_program_vars a =
  let st = Psyntax.Arg_var(Vars.concretep_str "current_automaton_state") in
  let sr = make_registers a in
  let sz = Psyntax.Arg_var(Vars.concretep_str "current_queue_list_size") in
  let e = make_event_queue (max_label_length a) (2 + max_arg a) in
  { state=st; store=sr; size=sz; queue=e }

let make_logical_copy_of_queue e =
  let mM = Array.length e in
  let nN = Array.length e.(0) in
  let el = Array.make_matrix mM nN (Psyntax.Arg_string("dummy")) in
  let ef = ref [] in
  let set_el i j = el.(i).(j)
    <- Psyntax.Arg_var(Vars.concretee_str ("log_queue_"^(string_of_int i)^"_"^(string_of_int j))) in
  let set_ef i j x = ef =:: P_EQ(x,el.(i).(j)) in
  Array.iteri (fun i x -> Array.iteri (fun j eij -> set_el i j; set_ef i j eij) x) e;
  (el, !ef)

let logical_dequeue e el n =
  let ef = ref [] in
  for i = 0 to (Array.length e)-n-1 do
    for j = 0 to (Array.length e.(0)) do ef =:: P_EQ(e.(i).(j),el.(i+n).(j))
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
(*
(* Removes all pfroms [] and [P_False] apart from those at top level *)
let rec remove_true_and_false (f:Psyntax.pform) : Psyntax.pform =
  if List.mem P_False f then [P_False] else
    match f with
      | [] -> []
      | P_Or(x,y) :: tl -> (
            let x' = remove_true_and_false x in
            match x' with
              | [] -> remove_true_and_false tl
              | [P_False] -> remove_true_and_false (y@tl)
              | _ -> let y' = remove_true_and_false y in
                     match y' with
                       | [] -> remove_true_and_false tl
                       | [P_False] -> x' @ (remove_true_and_false tl)
                       | _ -> P_Or(x',y') :: (remove_true_and_false tl) )
      | P_EQ(x,y) :: tl -> P_EQ(x,y) :: (remove_true_and_false tl)
      | P_NEQ(x,y) :: tl -> P_NEQ(x,y) :: (remove_true_and_false tl)
      | P_PPred(_,_) :: _ -> failwith "Elimination called for PPred!"
      | P_SPred(_,_) :: _ -> failwith "Elimination called for SPred!"
      | P_Wand(_,_) :: _ -> failwith "Elimination called for Wand!"
      | P_Septract(_,_) :: _ -> failwith "Elimination called for Septract!"
      | P_False :: _ -> failwith "Intrenal elimination loop reached False!"
*)

let rec simplify_pform xs =
  let xs = xs >>= simplify_pform_at in
  if List.mem P_False xs then [P_False] else xs
and simplify_pform_at = function
  | P_Or (x, y) ->
      (match (simplify_pform x, simplify_pform y) with
        | [], _ | _, [] -> []
        | [P_False], z | z, [P_False] -> z
        | x, y -> [P_Or (x, y)])
  | P_EQ _ as x -> [x]
  | P_NEQ _ as x -> [x]
  | _ -> failwith "Internal: simplification of and/or with true/false"

let rec negate_specs_it (f:Psyntax.pform) : Psyntax.pform_at =
    match f with
      | [] -> P_False
      | z :: fs ->
        (match z with
          | P_EQ(x,y) -> P_Or([P_NEQ(x,y)], [negate_specs_it fs])
          | P_NEQ(x,y) -> P_Or([P_EQ(x,y)], [negate_specs_it fs])
          | P_PPred(_,_) -> failwith "Negation called for PPred!"
          | P_SPred(_,_) -> failwith "Negation called for SPred!"
          | P_Wand(_,_) -> failwith "Negation called for Wand!"
          | P_Or(x,y) -> P_Or([(negate_specs_it x); (negate_specs_it y)], [negate_specs_it fs])
          | P_Septract(_,_) -> failwith "Negation called for Septract!"
          | P_False -> failwith "Internal negation loop reached False!")

(* Performs a rather unsophisticated negation of pforms built out of P_EQ,P_NEQ,P_False and P_Or *)
let negate_pforms (f:Psyntax.pform) : Psyntax.pform =
  let f' = simplify_pform f in
  let f'' = match f' with
      | [P_False] -> []
      | _ -> [negate_specs_it f']
  in simplify_pform f''

(* Returns a pform given guard gd, assuming that value i of each event is stored in
   e.(i+1) in event queue *)
let rec guard_conditions gd e st =
  match gd with
    | True -> []
    | EqCt(i,v) -> [P_EQ(e.(i+1), v)]
    | EqReg(i,r) -> [P_EQ(e.(i+1), RMap.find r st)]
    | Not(g') -> negate_pforms (guard_conditions g' e st)
    | And(gl) -> gl >>= (fun g -> guard_conditions g e st)


(* Conditions for e being satisfied by (st,s) and leading to st' *)
let step_conditions e st st' (s:step) =
  let gd = s.guard in
  let ac = s.action in
  let one_ev_cond ev cond = [P_Or ([P_EQ(e.(0), arg_from_event ev)], cond)] in
  let ev_cond = ESet.fold one_ev_cond s.observable_events [P_False] in
  let gd_cond = guard_conditions gd e st in
  let ac_cond = VMap.fold (fun r v f ->
    if (RMap.mem r ac) then (P_EQ(v, e.(RMap.find r ac))::f)
    else (P_EQ(v, VMap.find r st)::f)) st' [] in
  simplify_pform (ev_cond @ gd_cond @ ac_cond)

let pDeQu n pv el =
  let m = Array.length pv.queue in
  P_EQ(pv.size, Psyntax.mkArgint (m-n)) :: (logical_dequeue pv.queue el n)

let trans_pre_and_post pv el l_sr0 j t =
  let st = t.steps in
  let tg = t.target in
  let len = List.length st in
  let sr = pv.store in
  let l_sr =  Array.init (len+1) ( fun i ->
    if i=0 then l_sr0 else make_logical_copy_of_store sr i j ) in
  let pre = List.flatten (list_mapi (fun i s ->
      step_conditions pv.queue.(i) l_sr.(i) l_sr.(i+1) s) st) in
  let post = [P_EQ(pv.state, Psyntax.Arg_string(tg))]
    @ (store_eq sr l_sr.(len)) @ (pDeQu len pv el) in (pre,post)


(* Given a set of indices k, negate all formulas in l whose index appears in k,
   and leave all other formulas intact *)
let sign_pres k l =
  list_mapi (fun i x -> if (IntSet.mem i k) then x else negate_pforms x) l

(* Given a set of indices k, P-Or all formulas in l whose index appears in k *)
let sign_POr_posts k xs =
  let xs = list_mapi (fun i x -> if (IntSet.mem i k) then x else [P_False]) xs in
  let xs = List.fold_left (fun acc x -> P_Or ([acc], x)) P_False xs in
  simplify_pform_at xs

let get_specs_for_vertex t pv v s =
  let tl = (try VMap.find v t with Not_found -> []) in
  let pAt = [P_EQ(pv.state, Psyntax.Arg_string v)] in
  (* let m = max_label_length_for_vertex tl in *)
  (* Qud below is defined differently than in the notes: in order to avoid the burden of
     trying to express e.(size-1).(0) = #, we just pad with #'s at the end of the main method. *)
  let (el,ef) = make_logical_copy_of_queue pv.queue in
  let mM = Array.length pv.queue in
  let pQud = P_EQ(pv.size, Psyntax.mkArgint mM) :: ef in
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

(*
let get_specs_for_skip tl v pv = []

let get_specs_for_vertex t pv v s =
  let trans_list = (try VMap.find v t with Not_found -> []) in
  (get_specs_for_regular trans_list v pv) @ (get_specs_for_skip trans_list v pv)
  @ s
*)

let get_specs_for_step a pv =
  HashSet.of_list (VSet.fold (get_specs_for_vertex a.transitions pv) a.vertices [])
