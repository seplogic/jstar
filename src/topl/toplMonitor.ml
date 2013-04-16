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

type event =
  { event_time : event_type
  ; proc_name : string }

type value = Psyntax.args

type letter =
  { event : event
  ; data : value list }

module ESet = Set.Make (struct type t = event let compare = compare end)

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

type step =
  { guard : guard
  ; action : action
  ; observable_events : ESet.t }

type transition =
  { steps : step list
  ; target : vertex }

type automaton =
  { vertices : VSet.t
  ; start_vertices : VSet.t
  ; error_messages : string VMap.t
  ; transitions : transition list VMap.t }

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
