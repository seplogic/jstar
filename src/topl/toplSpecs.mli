type toplPVars =
    { state : Psyntax.args;
      store : Psyntax.args ToplMonitor.RMap.t;
      size : Psyntax.args;
      queue : Psyntax.args array array }

val enqueue_specs : toplPVars -> Core.ast_spec
val init_TOPL_program_vars : int -> ToplMonitor.automaton -> toplPVars
val get_specs_for_step : ToplMonitor.automaton -> toplPVars -> Core.ast_spec
