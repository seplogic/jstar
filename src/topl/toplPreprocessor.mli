val read_properties : string list -> (string, string) Topl.PropAst.t list
val compile
  : Jimple_global_types.jimple_file list
    -> (ToplMonitor.register, ToplMonitor.value) Topl.PropAst.t list
    -> Core.ast_procedure list
val instrument_procedures : Core.ast_procedure list -> Core.ast_procedure list
