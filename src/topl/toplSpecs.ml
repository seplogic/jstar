open Corestar_std

(* module PS = Psyntax *)
module TM = ToplMonitor
module TN = ToplNames

(* TODO(rgrig): Use the more high-level functions in [Psyntax] if possible. *)

type toplPVars =
  { state : Expression.t
  ; store : Expression.t TM.RMap.t
  ; size : Expression.t
  ; queue : Expression.t array array }
  (* INV: Each [Expression.t] above should be [Arg_var _]. *)

let var_of_term = failwith "TODO"
  (* function                                                *)
  (* | PS.Arg_var v -> v                                     *)
  (* | _ -> failwith "INTERNAL: toplPVars invariant broken?" *)

let rec range i j = (* [i; i+1; ...; j-1] *)
  if i >= j then [] else i :: range (i + 1) j

let wrap_call_arg a = failwith "TODO"
 (* PS.mkVar (CoreOps.parameter_var a) *)

let get_specs_for_enqueue pv = failwith "TODO"
  (* let q_sz = Array.length pv.queue in                                     *)
  (* let e_sz = Array.length pv.queue.(0) in                                 *)
  (* let specs = HashSet.create 0 in                                         *)
  (* for i = 0 to q_sz - 1 do begin                                          *)
  (*   let e = pv.queue.(i) in                                               *)
  (*   let pre = [PS.P_EQ(pv.size, PS.mkArgint i)] in                        *)
  (*   let post =                                                            *)
  (*     let cp i = PS.P_EQ (e.(i), wrap_call_arg i) in                      *)
  (*     PS.P_EQ (pv.size, PS.mkArgint (i+1))                                *)
  (*     :: List.map cp (range 0 e_sz) in                                    *)
  (*   let modifies = pv.size :: List.map (fun i -> e.(i)) (range 0 e_sz) in *)
  (*   let modifies = Some (List.map var_of_term modifies) in                *)
  (*   HashSet.add specs { Core.pre; post; modifies }                        *)
  (* end done;                                                               *)
  (* specs                                                                   *)

let max_label_length_for_vertex ll =
  List.fold_right (fun l acc ->
(*     (* debug *) Format.printf "Internal call of max_label_length_for_vertex: acc = %d, cur = %d\n" acc (List.length l.TM.steps); *)
    max acc (List.length l.TM.steps)) ll 0

let max_label_length a =
  let f v ts acc =
(*     (* debug *) Format.printf "Check max length for vertex %s with %d transitions\n" v (List.length ts); *)
    max (max_label_length_for_vertex ts) acc in
  TM.VMap.fold f a.TM.transitions 1
  (* NOTE: Artificially force the queue not to be really short, because the
  code relies on its size not being 0. *)

let max_arg a =
  let map_max f xs = xs |> List.map f |> List.fold_left max (-1) in
  let rec max_arg_guard = function
    | TM.EqCt (i, _) | TM.EqReg (i, _) -> i
    | TM.Not g -> max_arg_guard g
    | TM.And gs -> map_max max_arg_guard gs
    | TM.True -> (-1) in
  let max_arg_action a = TM.RMap.fold (fun _ -> max) a (-1) in
  let max_arg_step s =
    max (max_arg_guard s.TM.guard) (max_arg_action s.TM.action) in
  let max_arg_trans t = map_max max_arg_step t.TM.steps in
  let max_arg_vertex _ ts y = max y (map_max max_arg_trans ts) in
  TM.VMap.fold max_arg_vertex a.TM.transitions (-1)

let make_event_queue m n = failwith "TODO"
  (* let mk_name i j = TN.global (Printf.sprintf "queue_event_%d_position_%d" i j) in *)
  (* Array.init m                                                                     *)
  (*   (fun i -> Array.init n (fun j ->                                               *)
  (*     PS.Arg_var (Vars.concretep_str (mk_name i j))))                              *)

let mk_terms prefix set = failwith "TODO"
  (* let f s = StringMap.add s (PS.Arg_var (Vars.concretep_str (prefix^s))) in *)
  (* StringSet.fold f set StringMap.empty                                      *)

let rec get_regs_from_guard s = function
  | TM.EqReg (_, r) -> StringSet.add r s
  | TM.Not g -> get_regs_from_guard s g
  | TM.And gs -> List.fold_left get_regs_from_guard s gs
  | _ -> s

let get_regs_from_action =
  TM.RMap.fold (fun r _ s -> StringSet.add r s)

let make_registers a =
  mk_terms (TN.global "register_")
  (TM.VMap.fold (fun _ tl m ->
    List.fold_left (fun m1 tr ->
      List.fold_left (fun m2 st ->
        let m3 = get_regs_from_guard m2 st.TM.guard in
        get_regs_from_action st.TM.action m3) m1 tr.TM.steps ) m tl ) a.TM.transitions
        StringSet.empty)

(* Create a set of logical variables corresponding to the store. Each such set is indexed
   with the transition j examined, and the step i inside the transition. The value -1 for j
   means a logical copy common to all transitions from a given vertex. *)
let make_logical_copy_of_store st i j = failwith "TODO"
  (* let mk_name =                                                    *)
  (*   let t = if j < 0 then "" else Printf.sprintf "_trans_%d" j in  *)
  (*   fun r -> Printf.sprintf "log_register_%s_%d%s" r i t in        *)
  (* let mk_var r = r |> mk_name |> Vars.concretee_str |> PS.mkVar in *)
  (* TM.RMap.mapi (fun r _ -> mk_var r) st                            *)

let store_eq st l_st =  failwith "TODO"
  (* TM.RMap.fold (fun r v f -> PS.P_EQ (v, TM.RMap.find r l_st) :: f) st [] *)

let store_eq_modifies st _ =
  List.map (var_of_term @@ snd) (TM.RMap.bindings st)

let get_type = function
  | TM.Call_time -> "CALL"
  | TM.Return_time -> "RETN"
  | TM.Any_time -> "ANY"

let print_automaton a =
  let print_s s = Format.printf "-- %s step with %d patterns\n" (get_type s.TM.observables.TM.event_time) (List.length s.TM.observables.TM.pattern) in
  let print_t t = Format.printf "- transition to %s in %d steps\n" t.TM.target (List.length t.TM.steps); List.iter print_s t.TM.steps in
  let print_v v ts = Format.printf "Vertex: %s with %d transitions\n" v (List.length ts);
    List.iter print_t ts in
  TM.VMap.iter print_v a.TM.transitions

let init_TOPL_program_vars a = failwith "TODO"
(* (*   (* debug *) print_automaton a; *)                                             *)
(*   let st = PS.mkVar(Vars.concretep_str (TN.global ("current_automaton_state"))) in *)
(*   let sr = make_registers a in                                                     *)
(*   let sz = PS.mkVar(Vars.concretep_str (TN.global ("current_queue_list_size"))) in *)
(*   let e = make_event_queue (max_label_length a) (2 + max_arg a) in                 *)
(*   { state=st; store=sr; size=sz; queue=e }                                         *)

let make_logical_copy_of_queue e = failwith "TODO"
  (* let mM = Array.length e in                                                                    *)
  (* let nN = Array.length e.(0) in                                                                *)
  (* let el = Array.make_matrix mM nN (PS.mkString("dummy")) in                                    *)
  (* let ef = ref [] in                                                                            *)
  (* let set_el i j = el.(i).(j)                                                                   *)
  (*   <- PS.Arg_var(Vars.concretee_str ("log_queue_"^(string_of_int i)^"_"^(string_of_int j))) in *)
  (* let set_ef i j x = ef =:: PS.P_EQ(x,el.(i).(j)) in                                            *)
  (* Array.iteri (fun i x -> Array.iteri (fun j eij -> set_el i j; set_ef i j eij) x) e;           *)
  (* (el, !ef)                                                                                     *)

let logical_deque_gen e el n =
  let ef = ref [] in
  for i = 0 to (Array.length e)-n-1 do
    for j = 0 to Array.length e.(0) - 1 do
      ef =:: (e.(i).(j), el.(i+n).(j))
    done;
  done;
  !ef

let logical_dequeue e el n = failwith "TODO"
  (* let mkEQ (x, y) = PS.P_EQ (x, y) in      *)
  (* List.map mkEQ (logical_deque_gen e el n) *)

let logical_deque_modifies e el n =
  List.map (var_of_term @@ fst) (logical_deque_gen e el n)

(* Returns a list with all non-empty subsets of {0,...,n-1} *)
let index_subsets n =
  let xs = ref([IntSet.empty]) in
  for i = 0 to n-1 do
    xs := (List.map (function x -> IntSet.add i x) !xs) @ !xs
  done;
  List.tl (List.rev !xs)

(* TODO(rgrig): Move to [Psyntax]? *)
  (* (NT) Here a nasty hack is used: Wand (f,g) means:
     - if we set some local variables using f
     - then g holds
     Thus, Wand(f,g) simplifies to Wand(f,simplify(g))
  *)
let rec simplify_pform xs = failwith "TODO"
(*   let xs = xs >>= simplify_pform_at in                                             *)
(*   let retn = if List.mem PS.P_False xs then [PS.P_False] else xs in                *)
(*   retn                                                                             *)
(* and simplify_pform_at = function                                                   *)
(*   | PS.P_Or (x, y) ->                                                              *)
(*       (match (simplify_pform x, simplify_pform y) with                             *)
(*         | [], _ | _, [] -> []                                                      *)
(*         | [PS.P_False], z | z, [PS.P_False] -> z                                   *)
(*         | x, y -> [PS.P_Or (x, y)])                                                *)
(*   | PS.P_Wand (x, y) -> [PS.P_Wand (x, simplify_pform y)]                          *)
(*   | PS.P_EQ _ as x -> [x]                                                          *)
(*   | PS.P_NEQ _ as x -> [x]                                                         *)
(*   | PS.P_False as x -> [x] (* NT: Added this part as it was called with P_False *) *)
(*   | _ -> failwith "Internal: simplification with unexpected case!"                 *)

 (* (NT) Here a nasty hack is used: Wand (f,g) means:
    - if we set some local variables using f
    - then g holds
    Thus, Wand(f,g) negates to f * negate(g)
 *)
let rec negate_specs_it _ =  failwith "TODO"
  (* (f:PS.pform) : PS.pform_at =                                                                        *)
  (*   match f with                                                                                      *)
  (*     | [] -> PS.P_False                                                                              *)
  (*     | z :: fs ->                                                                                    *)
  (*       (match z with                                                                                 *)
  (*         | PS.P_EQ(x,y) -> PS.P_Or([PS.P_NEQ(x,y)], [negate_specs_it fs])                            *)
  (*         | PS.P_NEQ(x,y) -> PS.P_Or([PS.P_EQ(x,y)], [negate_specs_it fs])                            *)
  (*         | PS.P_PPred(_,_) -> failwith "Negation called for PPred!"                                  *)
  (*         | PS.P_SPred(_,_) -> failwith "Negation called for SPred!"                                  *)
  (*         | PS.P_Wand(x,y) -> PS.P_Or((negate_specs_it y)::x, [negate_specs_it fs])                   *)
  (*         | PS.P_Or(x,y) -> PS.P_Or([(negate_specs_it x); (negate_specs_it y)], [negate_specs_it fs]) *)
  (*         | PS.P_Septract(_,_) -> failwith "Negation called for Septract!"                            *)
  (*         | PS.P_False -> failwith "Internal negation loop reached False!")                           *)

(* Performs a rather unsophisticated negation of pforms built out of
   PS.P_EQ,PS.P_NEQ,PS.P_False and PS.P_Or, and a hacky PS.P_Wand *)
let negate_pforms _ = failwith "TODO"
(*   (f:PS.pform) : PS.pform =                                                       *)
(*   (* (* debug *) Format.printf "Call to negate_pforms: %a\n" PS.string_form f; *) *)
(*   let f' = simplify_pform f in                                                    *)
(*   let f'' = match f' with                                                         *)
(*       | [PS.P_False] -> []                                                        *)
(*       | _ -> [negate_specs_it f']                                                 *)
(*   in                                                                              *)
(*   let retn = simplify_pform f'' in                                                *)
(* (* (* debug *) Format.printf "-> and return: %a\n" PS.string_form retn; *)        *)
(*   retn                                                                            *)

  (* Replace hacky Wand(x,y) by x@y *)
let rec remove_dirty_wands _ =  failwith "TODO"
(*   (f:PS.pform) : PS.pform =                                                       *)
(*   let f' = remove_dirty_wands_it f in                                             *)
(*   simplify_pform f'                                                               *)
(* and remove_dirty_wands_it f = List.map (function                                  *)
(*     | PS.P_Wand (x,y) -> PS.P_Or (x @ (remove_dirty_wands_it y), [PS.P_False])    *)
(*     | PS.P_Or (x,y) -> PS.P_Or (remove_dirty_wands_it x, remove_dirty_wands_it y) *)
(*     | x -> x ) f                                                                  *)

(* Returns a pform given guard gd, assuming that value i of each event is stored in
   e.(i+1) in event queue *)
let rec guard_conditions gd e st = failwith "TODO"
  (* match gd with                                              *)
  (*   | TM.True -> []                                          *)
  (*   | TM.EqCt (i,v) -> PS.mkEQ (e.(i+1), v)                  *)
  (*   | TM.EqReg (i,r) -> PS.mkEQ (e.(i+1), TM.RMap.find r st) *)
  (*   | TM.Not g -> negate_pforms (guard_conditions g e st)    *)
  (*   | TM.And gs -> gs >>= (fun g -> guard_conditions g e st) *)

let obs_conditions e { TM.event_time; pattern } = failwith "TODO"
(*   let ev_name = match event_time with                                                             *)
(*     | TM.Call_time -> [ TN.call_event ]                                                           *)
(*     | TM.Return_time -> [ TN.return_event ]                                                       *)
(*     | TM.Any_time -> [ TN.call_event; TN.return_event ] in                                        *)
(*   let p_cond p = List.map (fun name -> PS.mkEQ (e.(0), name p)) ev_name in                        *)
(* (*   (* debug *) Format.printf "\nNow, the pattern has length: %d\n" (List.length pattern); *)    *)
(* (*   (* debug *) List.iter (fun s -> Format.printf "- here is a pattern elt: %s\n" s) pattern; *) *)
(*   PS.mkBigOr (pattern >>= p_cond)                                                                 *)

let rec string_guard = function
    | TM.True -> "True"
    | TM.EqCt(i,v) -> Format.sprintf "Eq(%d , val)" i
    | TM.EqReg(i,r) -> Format.sprintf "Eq(%d , %s)" i r
    | TM.Not(g') -> Format.sprintf "Not(%s)" (string_guard g')
    | TM.And(gl) -> "And("^(List.fold_left (fun acc g' -> acc^(string_guard g')^",") "" gl)^")"

(* Conditions for e being satisfied by (st,s) and leading to st' *)
let step_conditions e st st' s = failwith "TODO"
(* (* (* debug *) Format.printf "Calling step_conditions for a %s step of length %d\n" (get_type s.TM.observables.TM.event_time) (List.length s.TM.observables.TM.pattern) in*)                     *)
(*   let gd = s.TM.guard in                                                                                                                                                                         *)
(*   let ac = s.TM.action in                                                                                                                                                                        *)
(*   let ev_cond = obs_conditions e s.TM.observables in                                                                                                                                             *)
(*   let gd_cond = guard_conditions gd e st in                                                                                                                                                      *)
(* (*   (* debug *) Format.printf "Now, and here is the gd_cond: %a\n" PS.string_form gd_cond; *)                                                                                                   *)
(*   let ac_cond = TM.VMap.fold (fun r v f ->                                                                                                                                                       *)
(*     if (TM.RMap.mem r ac) then (PS.P_EQ(v, e.(1 + TM.RMap.find r ac))::f)                                                                                                                        *)
(*     (* Added 1+ because at position 0 is the call/ret m *)                                                                                                                                       *)
(*     else (PS.P_EQ(v, TM.VMap.find r st)::f)) st' [] in                                                                                                                                           *)
(* (* (* debug *) (Format.printf "Now, and here is the ev_cond of size %d: %a\n" (List.length ev_cond) PS.string_form ev_cond;  Format.printf "Now, and ac_cond: %a\n" PS.string_form ac_cond) in*) *)
(*   let big_cond = (ev_cond @ gd_cond) in                                                                                                                                                          *)
(* (* (* debug *) Format.printf "Now, here is the big cond of size %d: %a\n" (List.length big_cond) PS.string_form big_cond in*)                                                                    *)
(*   let retn = simplify_pform big_cond in                                                                                                                                                          *)
(* (*   (* debug *) Format.printf " and simplified, of size %d: %a\n" (List.length retn                                                                           ) PS.string_form retn; *)         *)
(*   (retn, ac_cond)                                                                                                                                                                                *)

let pDeQu n pv el = failwith "TODO"
  (* let m = Array.length pv.queue in                                       *)
  (* PS.P_EQ(pv.size, PS.mkArgint (m-n)) :: (logical_dequeue pv.queue el n) *)

let pDeQu_modifies n pv el =
  var_of_term pv.size :: logical_deque_modifies pv.queue el n

let trans_pre_and_post pv el l_sr0 j t = failwith "TODO"
(*   let st = t.TM.steps in                                                                                        *)
(*   let tg = t.TM.target in                                                                                       *)
(*   let len = List.length st in                                                                                   *)
(* (*   (* debug *) Format.printf "Inside TPAP with transition length %d and target %s\n" len tg; *)               *)
(*   let sr = pv.store in                                                                                          *)
(*   let l_sr =  Array.init (len+1) ( fun i ->                                                                     *)
(*     if i=0 then l_sr0 else make_logical_copy_of_store sr i j ) in                                               *)
(*   let unwanded = ListH.mapi (fun i s ->                                                                         *)
(*     step_conditions pv.queue.(i) l_sr.(i) l_sr.(i+1) s) st in                                                   *)
(*   let pre = List.fold_left (fun acc (x,y) -> (PS.P_Wand (y, acc)) :: x) [] (List.rev unwanded) in               *)
(*   let post = PS.P_EQ (pv.state, PS.Arg_string tg)                                                               *)
(*     :: store_eq sr l_sr.(len) @ pDeQu len pv el in                                                              *)
(* (*   (* debug *) Format.printf "\n==> Pre:\n %a\n ===> Post:\n %a\n" PS.string_form pre PS.string_form post; *) *)
(*   let modifies = var_of_term pv.state                                                                           *)
(*     :: store_eq_modifies sr l_sr.(len) @ pDeQu_modifies len pv el in                                            *)
(*   (pre, post, modifies)                                                                                         *)

(* Given a set of indices k, negate all formulas in l whose index appears in k,
   and leave all other formulas intact *)
  (* let sign_pres k l =
     ListH.mapi (fun i x -> if (IntSet.mem i k) then x else negate_pforms x) l *)

let select_subset k xs =
  ListH.foldri (fun i x xs -> if IntSet.mem i k then x :: xs else xs) xs []

let get_specs_for_vertex t pv v s = failwith "TODO"
(*   let tl = (try TM.VMap.find v t with Not_found -> [] ) in                                                                                         *)
(* (*   (* debug *) Format.printf "Here is the vertex: %s\n" v; *)                                                                                    *)
(*   (* (* debug *) TM.VMap.iter (fun s _ -> Format.printf "Here is a key: %s\n" s) t; *)                                                             *)
(* (*   (* debug *) Format.printf "Here is the length of tl: %d\n" (List.length tl); *)                                                               *)
(*   let pAt = [PS.P_EQ(pv.state, PS.Arg_string v)] in                                                                                                *)
(*   let (el,ef) = make_logical_copy_of_queue pv.queue in                                                                                             *)
(*   let mM = Array.length pv.queue in                                                                                                                *)
(* (*   (* debug *) Format.printf "Here is M: %d\n" mM; *)                                                                                            *)
(*   let pQud = PS.P_EQ(pv.size, PS.mkArgint mM) :: ef in                                                                                             *)
(*   let l_sr0 = make_logical_copy_of_store pv.store 0 (-1) in                                                                                        *)
(*   let pInit = store_eq pv.store l_sr0 in                                                                                                           *)
(* (*   (* debug *) Format.printf "Now, here is the pInit for %s: %a\n" v Psyntax.string_form pInit; *)                                               *)
(*   let pAllSats, pAllPosts, allModifies =                                                                                                           *)
(*     ListH.split3 (ListH.mapi (trans_pre_and_post pv el l_sr0) tl) in                                                                               *)
(*   let pAllSats_neg = List.map negate_pforms pAllSats in                                                                                            *)
(*   let pAllSats = List.map remove_dirty_wands pAllSats in                                                                                           *)
(* (* (* debug *) ListH.iteri (fun i x -> Format.printf "\n\nNow, here is element %d of pAllSat for %s:\n%a\n" i v PS.string_form x) pAllSats in*)    *)
(* (* (* debug *) ListH.iteri (fun i x -> Format.printf "\n\nNow, here is negated element %d of pAllSat:\n%a\n" i PS.string_form x) pAllSats_neg in*) *)
(* (* (* debug *) ListH.iteri (fun i a -> Format.printf "\nNow, here is element %d of pAllPost:\n%a\n" i PS.string_form a) pAllPosts in*)             *)
(*   let s_skip =                                                                                                                                     *)
(*     let pre = pAt @ pInit @ pQud @ List.flatten pAllSats_neg in                                                                                    *)
(*     let post = pAt @ pInit @ pDeQu 1 pv el in                                                                                                      *)
(*     let modifies = Some (pDeQu_modifies 1 pv el) in                                                                                                *)
(*     [{ Core.pre; post; modifies }] in                                                                                                              *)
(*   let subs = index_subsets (List.length tl) in                                                                                                     *)
(*   let s_regular = List.map                                                                                                                         *)
(*     ( fun k ->                                                                                                                                     *)
(*       let pSats = ListH.mapi (fun i (x,y) -> if IntSet.mem i k then x else y) (List.combine pAllSats pAllSats_neg) in                              *)
(*       let pre = pAt @ pInit @ pQud @ List.flatten pSats in                                                                                         *)
(*       let post = PS.mkBigOr (select_subset k pAllPosts) in                                                                                         *)
(*       let modifies = Some (List.concat (select_subset k allModifies)) in                                                                           *)
(*       { Core.pre; post; modifies }) subs in                                                                                                        *)
(*   s_regular @ s_skip @ s                                                                                                                           *)

let get_specs_for_step a pv =
  Core.TripleSet.of_list (TM.VSet.fold (get_specs_for_vertex a.TM.transitions pv) a.TM.vertices [])
