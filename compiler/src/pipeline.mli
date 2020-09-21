(** Pipeline representation **)
open Pipeline_program

exception UnknownConfigFormat
exception InstructionUnsupported of string

type pipeline = string

(* The order, from head to tail, defines the priority, from high to low *)
val pipelines : pipeline list

type step = Occupied of instr | Free

module PipelineMap : Map.S with type key = pipeline
type processor = (step array) PipelineMap.t

(* Current state *)
val current_cycle : int ref
val alias_analysis : operand -> operand -> bool

(* Pipeline managment *)
val latency : pipeline -> int
val pipelines_for : instr -> pipeline list
val new_pipeline : pipeline -> step array
val new_processor : unit -> processor

(* Directives *)
val ressources_available : instr -> processor -> bool
val execute_step : processor -> pipeline -> int -> unit
val execute_pipeline : processor -> pipeline -> unit
val one_cycle : processor -> unit
val can_fetch : processor -> instr -> bool
val fetch : processor -> instr -> unit

(* Sem *)
val reinit_cycles : unit -> unit
val atomic : processor -> instr -> unit
val finish : processor -> unit

(* Complete processor *)

type instrumentation = Pipeline_program.checkpoint * int * int (* min and max bound *)

type instrumentation_program =
  | ISkip
  | IBloc of instrumentation (* instrumentation put at the end of the sequence *)
  | ISeq of instrumentation_program list
  | ICond of instrumentation_program * instrumentation_program
  | ILoop of instrumentation_program

val instrument : program -> processor -> instrumentation_program
val display : instrumentation_program -> unit
val display_checkpoints : instrumentation_program -> unit

(** Display **)
val pipeline_to_string : pipeline -> string