open Corestar_std

type toplPVars =
  { state : Z3.Expr.expr
  ; store : Z3.Expr.expr ToplMonitor.RMap.t
  ; size : Z3.Expr.expr
  ; queue : Z3.Expr.expr array array }

val get_specs_for_enqueue : toplPVars -> Core.spec
val init_TOPL_program_vars : 'a list ToplMonitor.automaton -> toplPVars
val get_specs_for_step
  : string list ToplMonitor.automaton -> toplPVars -> Core.spec
