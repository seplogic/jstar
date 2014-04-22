(** Data structures for representing TOPL automata specialized
for a given class hierarchy.  (This corresponds to the data structures in the
Java implementation of the runtime monitor.) *)

open Corestar_std

type vertex = string

module VSet = StringSet
module VMap = StringMap

type event_type =
  | Call_time
  | Return_time
  | Any_time

type 'pattern event =
  { event_time : event_type
  ; pattern : 'pattern }
  (* NOTE: The pattern is first a pair (regex, arity), which is suposed to be
  used at the level of the jimple representation together with inheritance
  information.  In the second phase, the pattern is a list of [Core] procedure
  names, which are strings. *)

type value = Z3.Expr.expr

type register = string

module RMap = StringMap

type guard =
  | True
  | EqCt of int * value  (* index in event, and constant to compare to *)
  | EqReg of int * register (* index in event, and register name *)
  | Not of guard
  | And of guard list

type action = int RMap.t
  (** Register [x] is set from component [RMap.find x action] of the letter.*)

type 'pattern step =
  { guard : guard
  ; action : action
  ; observables : 'pattern event }

type 'pattern transition =
  { steps : 'pattern step list
  ; target : vertex }

type 'pattern automaton =
  { vertices : VSet.t
  ; start_vertices : VSet.t
  ; error_messages : string VMap.t
  ; transitions : 'pattern transition list VMap.t }

let empty_automaton =
  { vertices = VSet.empty
  ; start_vertices = VSet.empty
  ; error_messages = VMap.empty
  ; transitions = VMap.empty }

(* Invariant checks, to be used for debugging. *)

let check_guard = function
  | EqCt (arg, _) | EqReg (arg, _) -> assert (0 <= arg)
  | _ -> ()

let check_action =
  RMap.iter (fun _ arg -> assert (0 <= arg))

let check_step { guard; action } =
  check_guard guard;
  check_action action

let check_transition is_vertex { steps; target } =
  List.iter check_step steps;
  is_vertex target

let check_automaton { vertices; start_vertices; error_messages; transitions } =
  let is_vertex v = assert (VSet.mem v vertices) in
  VSet.iter is_vertex start_vertices;
  VMap.iter (fun v _ -> is_vertex v) error_messages;
  VMap.iter (fun v _ -> is_vertex v) transitions;
  VMap.iter (fun _ -> List.iter (check_transition is_vertex)) transitions
