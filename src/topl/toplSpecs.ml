open Corestar_std

module TM = ToplMonitor
module TN = ToplNames
module U = Untyped

type toplPVars =
  { state : Z3.Expr.expr
  ; store : Z3.Expr.expr TM.RMap.t
  ; size : Z3.Expr.expr
  ; queue : Z3.Expr.expr array array }
  (* INV: Each [Z3.Expr.expr] above should be a variable. *)

let rec range i j = (* [i; i+1; ...; j-1] *)
  if i >= j then [] else i :: range (i + 1) j

let mk_pvar = U.mk_pgvar
let mk_evar = U.mk_lvar
let mk_true = Syntax.mk_emp


(* This function correctly encodes conditions x = true/false.
   Ideally, in the future it should also handle integers. *)
let mk_eq_to x = function
(*| "true" -> Syntax.mk_neq x (Syntax.mk_int_const "0")
  | "false" -> Syntax.mk_eq x (Syntax.mk_int_const "0") *)
  | y -> Syntax.mk_eq x y

let wrap_call_arg a = U.mk_plvar (U.parameter a)

let get_specs_for_enqueue pv =
  let q_sz = Array.length pv.queue in
  let e_sz = Array.length pv.queue.(0) in
  let specs = Core.TripleSet.create 0 in
  for i = 0 to q_sz - 1 do begin
    let e = pv.queue.(i) in
    let pre = Syntax.mk_eq pv.size (Syntax.mk_int_const (string_of_int i)) in
    let post = Syntax.mk_star
      (let cp i = Syntax.mk_eq e.(i) (wrap_call_arg i) in
      Syntax.mk_eq pv.size (Syntax.mk_int_const (string_of_int (i+1)))
      :: List.map cp (range 0 e_sz)) in
    let modifies = pv.size :: List.map (fun i -> e.(i)) (range 0 e_sz) in
    Core.TripleSet.add specs { Core.pre; post; modifies }
  end done;
  specs

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

let make_event_queue m n =
  let mk_name i j = Printf.sprintf "queue_event_%d_position_%d" i j in
   Array.init m
     (fun i -> Array.init n (fun j -> U.mk_pgvar (mk_name i j)))

let mk_terms mk prefix set =
  let f s = StringMap.add s (mk (prefix^s)) in
  StringSet.fold f set StringMap.empty

let rec get_regs_from_guard s = function
  | TM.EqReg (_, r) -> StringSet.add r s
  | TM.Not g -> get_regs_from_guard s g
  | TM.And gs -> List.fold_left get_regs_from_guard s gs
  | _ -> s

let get_regs_from_action =
  TM.RMap.fold (fun r _ s -> StringSet.add r s)

let make_registers a =
  mk_terms U.mk_pgvar "register_"
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
   let f r = r |> mk_name |> mk_evar in
   TM.RMap.mapi (fun r _ -> f r) st

let store_eq st l_st =
  TM.RMap.fold (fun r v f -> (Syntax.mk_eq v (TM.RMap.find r l_st)) :: f) st []

let as_var = Syntax.on_var id (fun _ -> failwith "invalid cast (idur3249)")

(* This marks what is modified from the store in a transition -- basically, we assume
   pv.store is modified, while we do not need to track modification of logical variables
   which is why the second argument is discarded *)
let store_eq_modifies st _ =
   List.map (as_var @@ snd) (TM.RMap.bindings st)

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

let init_TOPL_program_vars a =
(*   (* debug *) print_automaton a; *)
  let state = U.mk_pgvar "current_automaton_state" in
  let store = make_registers a in
  let size = U.mk_pgvar "current_queue_list_size" in
  let queue = make_event_queue (max_label_length a) (2 + max_arg a) in
  { state; store; size; queue }

let make_logical_copy_of_queue e =
  let mM = Array.length e in
  let nN = Array.length e.(0) in
  let el = Array.make_matrix mM nN Syntax.mk_emp in
  let ef = ref [] in
  let set_el i j = el.(i).(j)
    <- mk_evar ("log_queue_"^(string_of_int i)^"_"^(string_of_int j)) in
  let set_ef i j x = ef =:: Syntax.mk_eq x el.(i).(j) in
   Array.iteri (fun i x -> Array.iteri (fun j eij -> set_el i j; set_ef i j eij) x) e;
  (el, !ef) (* el contains the logical vars, ef the formulas stating that these are copies of e *)

let logical_deque_gen e el n =
  let ef = ref [] in
  for i = 0 to (Array.length e)-n-1 do
    for j = 0 to Array.length e.(0) - 1 do
      ef =:: (e.(i).(j), el.(i+n).(j))
    done;
  done;
  !ef

let logical_dequeue e el n =
  let mkEQ (x, y) = Syntax.mk_eq x y in
  List.map mkEQ (logical_deque_gen e el n)

let logical_deque_modifies e el n =
  List.map (as_var @@ fst) (logical_deque_gen e el n)

(* Returns a list with all non-empty subsets of {0,...,n-1} *)
let index_subsets n =
  let xs = ref([IntSet.empty]) in
  for i = 0 to n-1 do
    xs := (List.map (function x -> IntSet.add i x) !xs) @ !xs
  done;
  List.tl (List.rev !xs)

(* (NT) Here we define a custom operator thor (f,g) with positive meaning f * g,
   and negative meaning f * not g. It is convenient for describing:
   - the state is f and transition g is possible, but also
   - the state is f but g is not possible.
 *)

let thor =
  let bs = Syntax.bool_sort in
  Z3.FuncDecl.mk_func_decl_s Syntax.z3_ctx "thor" [bs; bs] bs
let mk_thor f g = Syntax.mk_2 thor f g

let rec negate_formula f =
  let wrong s _ =
    Format.fprintf Format.str_formatter
      "negate_formula can't handle %a; just = != * or thor (%s)"
      Syntax.pp_expr f s;
    failwith (Format.flush_str_formatter ()) in
  let mk_star_not = function
    | [f; g] -> Syntax.mk_star [f; (negate_formula g)]
    | _ -> assert false in
  let mk_not_distinct es =
    Prover.mk_big_or (Misc.map_all_pairs Syntax.mk_eq es) in
  ( Syntax.on_star (Prover.mk_big_or @@ List.map negate_formula)
  & Syntax.on_or (Prover.mk_big_star @@ List.map negate_formula)
  & Syntax.on_op thor mk_star_not
  & Syntax.on_eq (fun e f -> Syntax.mk_distinct [e; f])
  & Syntax.on_distinct mk_not_distinct
  & Syntax.on_emp (c1 Syntax.mk_false)
  & wrong "d29dnwdfw" ) f

(* Replace thor(x,y) by x*y *)
let rec remove_thors f =
  let mk_star_ton = function
    | [x; y] -> Syntax.mk_star [x; (remove_thors y)]
    | _ -> assert false in
  ( Syntax.on_op thor mk_star_ton
  & Syntax.recurse remove_thors ) f

(* Returns a formula given guard gd, assuming that value i of each event is stored in
   e.(i+1) in event queue *)
(* NT: The EqCt case has been slightly hacked to address equality with booleans *)
let rec guard_conditions gd e st =
  match gd with
     | TM.True -> mk_true
     | TM.EqCt (i,v) -> mk_eq_to e.(i+1) v
     | TM.EqReg (i,r) -> Syntax.mk_eq e.(i+1) (TM.RMap.find r st)
     | TM.Not g -> negate_formula (guard_conditions g e st)
     | TM.And gs -> Prover.mk_big_star (List.map (fun g -> guard_conditions g e st) gs)

let obs_conditions e { TM.event_time; pattern } =
(* (* debug *) Format.printf "\nNow, the pattern has length: %d\n" (List.length pattern); *)
(* (* debug *) List.iter (fun s -> Format.printf "- here is a pattern elt: %s\n" s) pattern;*)
   let ev_name = match event_time with
     | TM.Call_time -> [ TN.call_event ]
     | TM.Return_time -> [ TN.return_event ]
     | TM.Any_time -> [ TN.call_event; TN.return_event ] in
   let p_cond p = List.map (fun name -> Syntax.mk_eq e.(0) (name p)) ev_name in
   Prover.mk_big_or (pattern >>= p_cond)
(* NT: Here this is an Or because any member of the pattern can potentially
   match the transition *)

let rec string_guard = function
    | TM.True -> "True"
    | TM.EqCt(i,v) -> Format.sprintf "Eq(%d , val)" i
    | TM.EqReg(i,r) -> Format.sprintf "Eq(%d , %s)" i r
    | TM.Not(g') -> Format.sprintf "Not(%s)" (string_guard g')
    | TM.And(gl) -> "And("^(List.fold_left (fun acc g' -> acc^(string_guard g')^",") "" gl)^")"

(* Conditions for e being satisfied by (st,s) and leading to st' *)
let step_conditions e st st' s =
(* debug *) Format.printf "\nCalling step_conditions for a %s step of length %d\n" (get_type s.TM.observables.TM.event_time) (List.length s.TM.observables.TM.pattern);
   let gd = s.TM.guard in
   let ac = s.TM.action in
   let ev_cond = obs_conditions e s.TM.observables in
   let gd_cond = guard_conditions gd e st in
(* debug *) Format.printf "\nNow, and here is the gd_cond: "; Syntax.pp_expr Format.std_formatter gd_cond;
   let ac_cond = Prover.mk_big_star ( TM.VMap.fold (fun r v f ->
     if (TM.RMap.mem r ac) then ((Syntax.mk_eq v e.(1 + TM.RMap.find r ac))::f)
     (* Added 1+ because at position 0 is the call/ret m *)
     else ((Syntax.mk_eq v (TM.VMap.find r st))::f)) st' [] ) in
(* debug *) Format.printf "\nNow, and here is the ev_cond: ";
   Syntax.pp_expr Format.std_formatter ev_cond;
   Format.printf "\nNow, and ac_cond: "; Syntax.pp_expr Format.std_formatter ac_cond;
   let big_cond = Syntax.mk_star [ev_cond; gd_cond] in
(* debug *) Format.printf "\nNow, here is the big cond: ";
   Syntax.pp_expr Format.std_formatter big_cond;
   let retn = big_cond in (* NT: here there used to be  a simplification *)
   (* (* debug *) Format.printf "\n and simplified, of size %d: " (List.length retn) Syntax.pp_expr
      Format.std_formatter retn; *)
   (retn, ac_cond)

let pDeQu n pv el =
   let m = Array.length pv.queue in
   (Syntax.mk_eq pv.size (Syntax.mk_int_const (string_of_int (m-n))))
   :: (logical_dequeue pv.queue el n)

let pDeQu_modifies n pv el =
  as_var pv.size :: logical_deque_modifies pv.queue el n

(* The last argument is the previous vertex. It is used in order to decide whether the
   transition modifies pv.state *)
let trans_pre_and_post pv el l_sr0 v j t =
   let st = t.TM.steps in
   let tg = t.TM.target in
   let len = List.length st in
(* (* debug *) Format.printf "Inside TPAP with transition length %d and target %s\n" len tg; *)
   let sr = pv.store in
   let l_sr = Array.init (len+1) ( fun i ->
     if i=0 then l_sr0 else make_logical_copy_of_store sr i j ) in
   let step_conds = ListH.mapi (fun i s ->
     step_conditions pv.queue.(i) l_sr.(i) l_sr.(i+1) s) st in
   let pre =
     List.fold_left
       (fun acc (x,y) -> Syntax.mk_star [mk_thor y acc; x])
       mk_true step_conds in
   let post = Prover.mk_big_star ( (Syntax.mk_eq pv.state (Syntax.mk_string_const tg))
                                 :: store_eq sr l_sr.(len) @ pDeQu len pv el ) in
 (* debug *) Format.printf "\n==> Pre:\n"; Syntax.pp_expr Format.std_formatter pre;
   Format.printf "\n ===> Post:\n"; Syntax.pp_expr Format.std_formatter post;
   let mod_state = if tg = v then [] else [as_var pv.state] in
   let modifies = as_var pv.size :: mod_state @ store_eq_modifies sr l_sr.(len) @ pDeQu_modifies len pv el in
   (pre, post, modifies)

(* Given a set of indices k, negate all formulas in l whose index appears in k,
   and leave all other formulas intact *)
  (* let sign_pres k l =
     ListH.mapi (fun i x -> if (IntSet.mem i k) then x else negate_pforms x) l *)

let select_subset k xs =
  ListH.foldri (fun i x xs -> if IntSet.mem i k then x :: xs else xs) xs []

let get_specs_for_vertex t pv v s =
  let tl = (try TM.VMap.find v t with Not_found -> [] ) in
(* (* debug *) Format.printf "Here is the vertex: %s\n" v; *)
(* (* debug *) TM.VMap.iter (fun s _ -> Format.printf "Here is a key: %s\n" s) t; *)
(* (* debug *) Format.printf "Here is the length of tl: %d\n" (List.length tl); *)
  let pAt = Syntax.mk_eq pv.state (Syntax.mk_string_const v) in
  let (el,ef) = make_logical_copy_of_queue pv.queue in
  let mM = Array.length pv.queue in
(* (* debug *) Format.printf "Here is M: %d\n" mM; *)
  let pQud = (Syntax.mk_eq pv.size (Syntax.mk_int_const (string_of_int mM))) :: ef in
  let l_sr0 = make_logical_copy_of_store pv.store 0 (-1) in
  let pInit = store_eq pv.store l_sr0 in
(* (* debug *) Format.printf "Now, here is the pInit for %s: %a\n" v Psyntax.string_form pInit; *)
  let pAllSats, pAllPosts, allModifies =
    ListH.split3 (ListH.mapi (trans_pre_and_post pv el l_sr0 v) tl) in
  let pAllSats_neg = List.map negate_formula pAllSats in
  let pAllSats = List.map remove_thors pAllSats in
(* debug *) ListH.iteri (fun i x -> Format.printf "\n\nNow, here is element %d of pAllSat
  for %s:\n" i v; Syntax.pp_expr Format.std_formatter x) pAllSats;
(* debug *) ListH.iteri (fun i x -> Format.printf "\n\nNow, here is negated element %d of
  pAllSat:\n" i; Syntax.pp_expr Format.std_formatter x) pAllSats_neg;
(* debug *) ListH.iteri (fun i a -> Format.printf "\nNow, here is element %d of pAllPost:\n"
  i; Syntax.pp_expr Format.std_formatter a) pAllPosts;
  let s_skip =
    let pre = Prover.mk_big_star ( pAt :: pInit @ pQud @ pAllSats_neg ) |> Prover.normalize in
    let post = Prover.mk_big_star( pAt :: pInit @ pDeQu 1 pv el ) |> Prover.normalize in
    let modifies = pDeQu_modifies 1 pv el in
    [{ Core.pre; post; modifies }] in
  let subs = index_subsets (List.length tl) in
  let s_regular = List.map
    ( fun k ->
      let pSats = ListH.mapi (fun i (x,y) -> if IntSet.mem i k then x else y)
        (List.combine pAllSats pAllSats_neg) in
      let pre = Prover.mk_big_star ( pAt :: pInit @ pQud @ pSats ) in
(*      (* debug *) Format.printf "@\npre for {%a} before normalization:@,%a" (pp_list (fun f -> Format.fprintf f "%d")) (IntSet.elements k) Syntax.pp_expr pre; *)
      let pre = Prover.normalize pre in
(*      (* debug *) Format.printf "@\npre after normalization:@,%a" Syntax.pp_expr pre; *)
      let post = Prover.mk_big_or (select_subset k pAllPosts) |> Prover.normalize in
      let modifies = List.concat (select_subset k allModifies) in
      { Core.pre; post; modifies }) subs in
  s_regular @ s_skip @ s

let get_specs_for_step a pv =
  Core.TripleSet.of_list (TM.VSet.fold (get_specs_for_vertex a.TM.transitions pv) a.TM.vertices [])

