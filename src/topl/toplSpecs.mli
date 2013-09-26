open Corestar_std

type toplPVars =
  { state : Expression.t (* Psyntax.args *)
  ; store : Expression.t (* Psyntax.args *) ToplMonitor.RMap.t
  ; size : Expression.t (* Psyntax.args *)
  ; queue : Expression.t (* Psyntax.args *) array array }

val get_specs_for_enqueue : toplPVars -> Core.spec
val init_TOPL_program_vars : 'a list ToplMonitor.automaton -> toplPVars
val get_specs_for_step
  : string list ToplMonitor.automaton -> toplPVars -> Core.spec
