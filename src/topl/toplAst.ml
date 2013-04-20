(* modules *) (* {{{ *)
open Corestar_std
open Format

(* }}} *)
(* data types *) (* {{{ *)
type 'a with_line = { ast : 'a; line : int }

type vertex = string

(* p_str = Str.regexp p_re *)
type pattern =
  { p_re : Str.regexp
  ; p_string : string }

type ('variable, 'value) value_guard =
  | Variable of 'variable * int
  | Constant of 'value * int

type event_type =
  | Call
  | Return

type ('event_type, 'method_name, 'method_arity) tag =
  { event_type : 'event_type
  ; method_name : 'method_name
  ; method_arity : 'method_arity }
  (* Common shape for [tag_guard] and [event_tag]. *)

type 'method_name tag_guard =
  ((event_type option), 'method_name, (int * int option)) tag

type ('method_name, 'value_guard) event_guard =
  { tag_guard : 'method_name tag_guard
  ; value_guards : 'value_guard list }

let check_event_guard g =
  let amin, amax = g.tag_guard.method_arity in
  option () (fun amax -> assert (amin <= amax)) amax;
  let chk = function
    | Variable (_, m) | Constant (_, m) -> assert (m < amin) in
  List.iter chk g.value_guards

type 'variable action = ('variable * int) list

type ('method_name, 'value_guard, 'variable) label_p =
  { guard : ('method_name, 'value_guard) event_guard
  ; action : 'variable action }
  (* used by [Parser] *)

type ('method_name, 'variable, 'value) label =
  ('method_name, ('variable, 'value) value_guard, 'variable) label_p

type ('method_name, 'variable, 'value) transition =
  { source : vertex
  ; target : vertex
  ; labels : ('method_name, 'variable, 'value) label list }

type ('variable, 'value) t =
  { name : string
  ; message : string
  ; observable : pattern
  ; transitions: (pattern, 'variable, 'value) transition list }
(* }}} *)
(* utilities *) (* {{{ *)
let mk_pattern s =
  { p_re = Str.regexp s; p_string = s }

let pattern_matches p s =
  Str.string_match p.p_re s 0

let wvars l =
  List.map fst l.action

let rvars l =
  let f = function Variable (x, _) -> Some x | _ -> None in
  map_option f l.guard.value_guards

let vars_of_edge f e =
  List.concat (List.map f e.labels)

let written_vars t = vars_of_edge wvars t
let read_vars t = vars_of_edge rvars t

let mk_event_guard t v =
  let r = { tag_guard = t; value_guards = v } in
  check_event_guard r; r

let outgoing a src =
  List.filter (fun e -> e.source = src) a.transitions

let pp_event_type f = function
  | Call -> fprintf f "call"
  | Return -> fprintf f "return"

(* TODO(rgrig): remove? *)
let ok_automaton =
  { name = "AlwaysOk"
  ; message =
      "internal error: ok_automaton should be happy with all programs"
  ; observable = mk_pattern "^$"
  ; transitions = [] }

(* }}} *)
