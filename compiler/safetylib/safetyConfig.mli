open Jasmin

type call_strategy =
  | Call_Direct 
  | Call_TopByCallSite 

(* Analysis policy for abstract calls. *)
type call_policy =
  | CallDirectAll
  | CallTopHeuristic

type input_range = { ir_name : string;
                     ir_min  : string;
                     ir_max  : string; }

type init_print = IP_None  | IP_NoArray | IP_All

val sc_input_ranges            : unit -> input_range list
val sc_comp_pass               : unit -> Compiler.compiler_step
val sc_k_unroll                : unit -> int
val sc_zero_threshold          : unit -> bool
val sc_param_threshold         : unit -> bool
val sc_more_threshold          : unit -> bool
val sc_flow_dep                : unit -> bool
val sc_if_disj                 : unit -> bool
val sc_pif_movecc_as_if        : unit -> bool
val sc_while_flags_setfrom_dep : unit -> bool
val sc_dynamic_packing         : unit -> bool
val sc_call_policy             : unit -> call_policy
  
(* Printing parameters *)
val sc_print_program           : unit -> bool
val sc_print_stats             : unit -> bool
val sc_arr_no_print            : unit -> bool
val sc_glob_no_print           : unit -> bool
val sc_nrel_no_print           : unit -> bool ref
val sc_ignore_unconstrained    : unit -> bool
val sc_is_init_no_print        : unit -> init_print
val sc_bool_no_print           : unit -> bool
val sc_print_symb_subst        : unit -> bool

(* Miscelaneous *)
val sc_var_append_fun_name     : unit -> bool
val sc_widening_out            : unit -> bool

(* -------------------------------------------------------------------- *)
val mk_config_doc     : string -> unit

(* -------------------------------------------------------------------- *)
val pp_current_config      : Format.formatter -> unit
val pp_current_config_diff : unit -> unit

val load_config : string -> unit
