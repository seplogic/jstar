open Corestar_std
open Psyntax
open ToplMonitor

type toplPVars = 
    { state : Psyntax.args;
      store : Psyntax.args VMap.t;
      size : Psyntax.args;
      queue : Psyntax.args array array }
(* Can I specify that the above should be Arg_vars of PVars? *)

let list_mapi f l =
  let i = ref(0) in List.map (function a -> f (let j = !i in i:=j+1; j) a) l

let arg_from_event ev =
  let x = match ev.event_time with
    | Call_time -> "Call_$$_"^ev.proc_name
    | Return_time -> "Return_$$_"^ev.proc_name in
  Psyntax.Arg_string(x)

let enqueue_letter_specs lt pv =
  let mM = Array.length pv.queue in
  let ev = lt.event in
  let vs = lt.data in
  let specs = Array.init mM (fun i ->
    let e = pv.queue.(i) in
    let pre = [P_EQ(pv.size, Psyntax.mkArgint i)] in
    let post = P_EQ(e.(0), arg_from_event ev)
      :: (list_mapi (fun i v -> P_EQ(e.(i+1), v)) vs) in
    { Core.pre = pre; post = post }) in
  HashSet.of_list (Array.to_list specs)

let max_label_length_for_vertex ( ll:transition list ) =
  List.fold_right (fun l m -> max m (List.length l.steps)) ll 0

let max_label_length ( a:automaton ) =
  VMap.fold (fun _ tl n -> max n (max_label_length_for_vertex tl)) a.transitions 0  

let max_atomic_label_size a = 3

let make_event_queue mM nN =
  Array.init mM 
    (function i -> Array.init nN 
      (function j -> Psyntax.Arg_var(Vars.concretep_str 
                     ("queue_event_"^(string_of_int i)^"_position_"^(string_of_int j)))))  

let rec get_regs_from_guard g m =
  match g with
    | EqReg(_,r) -> if (VMap.mem r m) then m else 
        (VMap.add r (Psyntax.Arg_var(Vars.concretep_str ("register_"^r))) m) 
    | Not(g') -> get_regs_from_guard g' m
    | And(gl) -> List.fold_left (fun m1 g1 -> get_regs_from_guard g1 m1) m gl
    | _ -> m

let get_regs_from_action (ac:action) (m: Psyntax.args VMap.t) = 
  RMap.fold (fun r _ m1->  
    if (VMap.mem r m1) then m1 else 
      (VMap.add r (Psyntax.Arg_var(Vars.concretep_str ("register_"^r))) m1)) ac m   

let make_registers ( a:automaton ) =
  VMap.fold (fun _ tl m -> 
    List.fold_left (fun m1 tr -> 
      List.fold_left (fun m2 st -> 
        let m3 = get_regs_from_guard st.guard m2 in
        get_regs_from_action st.action m3) m1 tr.steps ) m tl ) a.transitions VMap.empty

let make_logical_copy_of_store st i =
  VMap.mapi (fun r _ -> Psyntax.Arg_var(Vars.concretee_str ("log_register_"^r^"_"^(string_of_int i)))) st

let store_eq st l_st =
  VMap.fold (fun r v f -> P_EQ(v,(VMap.find r l_st)) :: f) st []

let init_TOPL_program_vars ( a:automaton ) =
  let st = Psyntax.Arg_var(Vars.concretep_str "current_automaton_state") in 
  let sr = make_registers a in
  let sz = Psyntax.Arg_var(Vars.concretep_str "current_queue_list_size") in 
  let e = make_event_queue (max_label_length a) (max_atomic_label_size a) in
  { state=st; store=sr; size=sz; queue=e }

let make_logical_copy_of_queue e =
  let mM = Array.length e in
  let nN = Array.length e.(0) in
  let el = Array.make_matrix mM nN (Psyntax.Arg_string("dummy")) in
  let ef = ref([]) in
  let set_el i j = el.(i).(j) 
    <- Psyntax.Arg_var(Vars.concretee_str ("log_queue_"^(string_of_int i)^"_"^(string_of_int j))) in 
  let set_ef i j x = ef := (!ef) @ [P_EQ(x,el.(i).(j))] in
  Array.iteri (fun i x -> Array.iteri (fun j eij -> set_el i j; set_ef i j eij) x) e; 
  (el, !ef)

let logical_dequeue e el n =
  let ef = ref([]) in
  for i = 0 to (Array.length e)-n-1 do 
    for j = 0 to (Array.length e.(0)) do ef := (!ef) @ [P_EQ(e.(i).(j),el.(i+n).(j))]
    done;  
  done;  
  !ef  

module IntSet = Set.Make (struct type t = int let compare = compare end)

(* Returns a list with all non-empty subsets of {0,...,n-1} *)
let index_subsets n =
  let xs = ref([IntSet.empty]) in
  for i = 0 to n-1 do 
    xs := (!xs) @ (List.map (function x -> IntSet.add i x) !xs) 
  done;
  List.tl !xs 

(* Removes all pfroms [] and [P_False] apart from those at top level *) 
let rec remove_true_and_false (f:Psyntax.pform) : Psyntax.pform =
  if List.mem P_False f then [P_False] else 
    match f with
      | [] -> []
      | h :: tl -> match h with       
          | P_Or(x,y) -> (
            let x' = remove_true_and_false x in
            match x' with
              | [] -> remove_true_and_false tl
              | [P_False] -> remove_true_and_false (y@tl)
              | _ -> let y' = remove_true_and_false y in
                     match y' with
                       | [] -> remove_true_and_false tl
                       | [P_False] -> x' @ (remove_true_and_false tl)
                       | _ -> P_Or(x',y') :: (remove_true_and_false tl) )
          | P_EQ(x,y) -> P_EQ(x,y) :: (remove_true_and_false tl)
          | P_NEQ(x,y) -> P_NEQ(x,y) :: (remove_true_and_false tl)
          | P_PPred(_,_) -> failwith "Elimination called for PPred!"    
          | P_SPred(_,_) -> failwith "Elimination called for SPred!"    
          | P_Wand(_,_) -> failwith "Elimination called for Wand!"    
          | P_Septract(_,_) -> failwith "Elimination called for Septract!"    
          | P_False -> failwith "Intenal elimination loop reached False!"   
 
let rec negate_specs_it (f:Psyntax.pform) : Psyntax.pform_at =
    match f with  
      | [] -> failwith "Internal negation loop reached empty formula!"
      | [z] -> (
        match z with 
          | P_EQ(x,y) -> P_NEQ(x,y)
          | P_NEQ(x,y) -> P_EQ(x,y) 
          | P_PPred(_,_) -> failwith "Negation called for PPred!"  
          | P_SPred(_,_) -> failwith "Negation called for SPred!"  
          | P_Wand(_,_) -> failwith "Negation called for Wand!"  
          | P_Or(x,y) -> P_Or([(negate_specs_it x); (negate_specs_it y)],[P_False])
          | P_Septract(_,_) -> failwith "Negation called for Septract!"  
          | P_False -> failwith "Internal negation loop reached False!" )
      | z :: fs ->     
        match z with  
          | P_EQ(x,y) -> P_Or([P_NEQ(x,y)], [negate_specs_it fs])
          | P_NEQ(x,y) -> P_Or([P_EQ(x,y)], [negate_specs_it fs]) 
          | P_PPred(_,_) -> failwith "Negation called for PPred!"  
          | P_SPred(_,_) -> failwith "Negation called for SPred!"  
          | P_Wand(_,_) -> failwith "Negation called for Wand!"  
          | P_Or(x,y) -> P_Or([(negate_specs_it x); (negate_specs_it y)], [negate_specs_it fs])
          | P_Septract(_,_) -> failwith "Negation called for Septract!"  
          | P_False -> failwith "Internal negation loop reached False!" 

(* Performs a rather unsophisticated negation of pforms built out of P_EQ,P_NEQ,P_False and P_Or *)
let negate_pforms (f:Psyntax.pform) : Psyntax.pform =
  let f' = remove_true_and_false f in 
  let f'' = match f' with  
      | [] -> [P_False] 
      | [P_False] -> [] 
      | _ -> [negate_specs_it f']
  in remove_true_and_false f''

(* Returns a pform given guard gd, assuming that value i of each event is stored in
   e.(i) in event queue *) 
let rec guard_conditions gd e st =
  match gd with 
    | True -> []
    | EqCt(i,v) -> [P_EQ(e.(i), v)] 
    | EqReg(i,r) -> [P_EQ(e.(i), VMap.find r st)]
    | Not(g') -> negate_pforms (guard_conditions g' e st)
    | And(gl) -> List.flatten (List.map (function g -> guard_conditions g e st) gl)


(* Conditions for e being satisfied by (st,s) and leading to st' *)
let step_conditions e st st' (s:step) = 
  let gd = s.guard in
  let ac = s.action in 
  let ev = ESet.choose s.observable_events in
  let ev_cond = [P_EQ(e.(0), arg_from_event ev)] in
  let gd_cond = guard_conditions gd e st in 
  let ac_cond = VMap.fold (fun r v f -> 
    if (RMap.mem r ac) then (P_EQ(v, e.(RMap.find r ac))::f) 
    else (P_EQ(v, VMap.find r st)::f)) st' [] in
  ev_cond @ gd_cond @ ac_cond

let pDeQu n pv el =  
  let mM = Array.length pv.queue in
  [P_EQ(pv.size, Psyntax.mkArgint (mM-n))]@(logical_dequeue pv.queue el n) 

let trans_pre_and_post pv el t i : (Psyntax.pform * Psyntax.pform) = 
  let st = t.steps in 
  let tg = t.target in
  let len = List.length st in
  let sr = pv.store in
  let l_sr =  Array.init (len+1) (function i -> make_logical_copy_of_store sr i) in
  let pre = (store_eq sr l_sr.(0))
    @ List.flatten (list_mapi (fun i s ->
      step_conditions pv.queue.(i) l_sr.(i) l_sr.(i+1) s) st) in 
  let post = [P_EQ(pv.state, Psyntax.Arg_string(tg))] 
    @ (store_eq sr l_sr.(len)) @ (pDeQu len pv el) in (pre,post)


(* Given a set of indices k, negate all formulas in l whose index appears in k, 
   and leave all other formulas intact *) 
let sign_pres k l =
  list_mapi (fun i x -> if (IntSet.mem i k) then x else negate_pforms x) l

(* Given a set of indices k, P-Or all formulas in l whose index appears in k *) 
let sign_POr_posts k l = 
  let l1 = list_mapi (fun i x -> if (IntSet.mem i k) then x else []) l in
  List.fold_left (fun rec_f f -> match f with
    | [] -> rec_f
    | _ -> [P_Or(f,rec_f)] ) [P_False] l1

let get_specs_for_regular tl v pv =
  let pAt = [P_EQ(pv.state, Psyntax.Arg_string v)] in
  (* let m = max_label_length_for_vertex tl in *)
  (* Qud below is defined differently than in the notes: in order to avoid the burden of
     trying to express e.(size-1).(0) = #, we just pad with #'s at the end of the main method. *)
  let (el,ef) = make_logical_copy_of_queue pv.queue in 
  let mM = Array.length pv.queue in                                       
  let pQud = [P_EQ(pv.size, Psyntax.mkArgint mM)]@ef in
  let (pAllSats,pAllPosts) = List.split (list_mapi (fun i t -> (trans_pre_and_post pv el t i)) tl) in
  let subs = index_subsets (List.length tl) in
  List.fold_left 
    ( fun s k -> 
      let pre = pAt @ pQud @ List.flatten (sign_pres k pAllSats) in
      let post = sign_POr_posts k pAllPosts in
      { Core.pre = pre; post = post } :: s ) [] subs

let get_specs_for_skip tl v pv = []

let get_specs_for_vertex t pv v s =
  let trans_list = if VMap.mem v t then VMap.find v t else [] in
  s @ (get_specs_for_regular trans_list v pv) @ (get_specs_for_skip trans_list v pv)

let get_specs_for_step a pv = 
  HashSet.of_list (VSet.fold (get_specs_for_vertex a.transitions pv) a.vertices [])
