type toplPVars = 
    { state : Psyntax.args;
      store : Psyntax.args ToplMonitor.VMap.t;
      size : Psyntax.args;
      queue : Psyntax.args array array }

val enqueue_letter_specs : ToplMonitor.letter -> toplPVars -> Core.ast_spec
val init_TOPL_program_vars : ToplMonitor.automaton -> toplPVars
val get_specs_for_step : ToplMonitor.automaton -> toplPVars -> Core.ast_spec 
