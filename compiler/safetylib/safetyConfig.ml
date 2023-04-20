open Jasmin
open Utils
module Json = Yojson

(***********************)
(* Analysis Parameters *)
(***********************)

(* Analysis strategy for abstract calls:
   - Call_Direct: normal abstract function call.
   - Call_TopByCallSite : function evaluated only once per call-site, with
     an initial state over-approximated by top.
     (FIXME: performance: evaluates only once on top). *)
type call_strategy =
  | Call_Direct 
  | Call_TopByCallSite 

(* Analysis policy for abstract calls. *)
type call_policy =
  | CallDirectAll
  | CallTopHeuristic

type init_print = IP_None | IP_NoArray | IP_All


let config_doc = "config/checker_config_doc.json"


(* -------------------------------------------------------------------- *)
exception BadSafetyConfig of string


(* -------------------------------------------------------------------- *)
(* Compiler steps after which the safety checker can be used. *)
let compiler_steps = [
  Compiler.ParamsExpansion ;
  Compiler.AddArrInit ;
  Compiler.Inlining ;
  Compiler.RemoveUnusedFunction ;
  Compiler.Unrolling ;
  Compiler.Renaming ;
  Compiler.DeadCode_Renaming ;
  Compiler.RemoveArrInit ;
  Compiler.RegArrayExpansion ;
  Compiler.RemoveGlobal ;
  Compiler.MakeRefArguments ;
  Compiler.LowerInstruction ;
  Compiler.StackAllocation ;
  Compiler.RemoveReturn ;
  Compiler.RegAllocation ;
  Compiler.DeadCode_RegAllocation;
]

let compiler_step_of_string s =
  List.find (fun x -> fst (Glob_options.print_strings x) = s) compiler_steps

let json_compiler_steps : Json.Basic.t =
  `List (List.map (fun x ->
      let s1, s2 = Glob_options.print_strings x in
      let data : Json.Basic.t =
        `Assoc ["pass name",`String s1; "pass description", `String s2] in
      data
    ) compiler_steps)


(* -------------------------------------------------------------------- *)
type input_range = { ir_name : string;
                     ir_min  : string;
                     ir_max  : string; }

let range_ex_json : Json.Basic.t =
  `Assoc [("var1", `Assoc ["min", `String "0"; "max", `String "100"]);
          ("var2", `Assoc ["min", `String "200"; "max", `String "300"])]

let range_of_json_assoc : string * Json.Basic.t -> input_range = function
  | s, `Assoc [(bd1, `String ibd1); (bd2, `String ibd2)] ->
    let imax, imin = match bd1, bd2 with
      | "min", "max" -> ibd2, ibd1
      | "max", "min" -> ibd1, ibd2
      | _ -> raise (BadSafetyConfig ("bad input ranges: provide a min and a \
                                      max for " ^ s ))
    in
    { ir_name = s; ir_min = imin; ir_max = imax; }
    
  | _ -> raise (BadSafetyConfig ("bad input ranges: see the example in " 
                                 ^ config_doc))
           
let input_ranges_of_json (r : Json.Basic.t) = match r with
  | `Assoc r -> List.map range_of_json_assoc r

  | _ -> raise (BadSafetyConfig ("bad input ranges: not a dictionary"))

  
(* -------------------------------------------------------------------- *)
type kind  = Parameter | Printing | Internal 

type pvalue = | Bool        of bool         
              | BoolRef     of bool ref     
              | Int         of int          
              | InitPrint   of init_print   
              | CallPolicy  of call_policy
              | CompPass    of Compiler.compiler_step
              | InputRanges of input_range list

type param = { p     : pvalue;
               name  : string;
               desc  : Json.Basic.t;
               kind  : kind; }

(* -------------------------------------------------------------------- *)
let default = 
  { p    = CompPass Compiler.ParamsExpansion;
    name = "compilation_pass";
    desc = `Assoc ([("descr",
                    `String "Compilation pass where the analysis must run. \
                             Can be any of the following passes." );
                   ("passes", json_compiler_steps)]); 
    kind = Parameter; } ::

  { p    = InputRanges [];
    name = "input_range";
    desc = `Assoc ([("descr",
                     `String "Assumed ranges for inputs." );
                   ("example", range_ex_json)]); 
    kind = Parameter; } ::

  { p    = Int 1;
    name = "k_unroll";
    desc = `String "Number of unrolling of a loop body before applying the \
                    widening. Higher values yield a more precise (and more \
                    costly) analysis."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "flow_dependency";
    desc = `String "Dependency graph includes flow dependencies."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "if_disjunction";
    desc = `String "Add disjunctions on if statements when possible."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "pif_movecc_as_if";
    desc = `String "Handle top-level conditional move and if expressions as if \
            statements. Combinatorial explosion if there are many movecc \
            and if expressions in the same block."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "while_flags_setfrom_dep";
    desc = `String "Pre-analysis looks for the variable corresponding to return \
            boolean flags appearing in while loop condition (adding them to \
            the set of variables in the relational domain)."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "dynamic_packing";
    desc = `String "Dynamic variable packing. Particularly useful if the analysis \
            runs after the register allocation."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "zero_threshold";
    desc = `String "Zero thresholds for the widening."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "param_threshold";
    desc = `String "Thresholds from the analysis parameters for the widening."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "more_threshold";
    desc = `String "More thresholds for the widening."; 
    kind = Parameter; } ::


  (***********************)
  (* Printing parameters *)
  (***********************)
  { p    = Bool false;
    name = "print_program";
    desc = `String "Print analyzed program. Useful if the analysis is not run at \
                    the source level."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "print_stats";
    desc = `String "Print analysis statistics."; 
    kind = Parameter; } ::
  
  { p    = Bool true;
    name = "arr_no_print";
    desc = `String "Turn on printing of array variables."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "glob_no_print";
    desc = `String "Turn on printing of global variables."; 
    kind = Printing; } ::

  { p    = BoolRef (ref false);
    name = "nrel_no_print";
    desc = `String "Turn on printing of non-relational variables."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "ignore_unconstrained";
    desc = `String "Turn on printing of unconstrained variables."; 
    kind = Printing; } ::

  { p    = InitPrint IP_None;
    name = "is_init_no_print";
    desc = `String " Turn on printing of not initialized variables \
            (i.e. it is not certain that the variable is initialized).\
            Can be IP_None, IP_All or IP_NoArray."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "bool_no_print";
    desc = `String "Turn on printing of boolean variables."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "print_symb_subst";
    desc = `String "Print substitutions done by the symbolic equality domain."; 
    kind = Printing; } ::

  (****************)
  (* Miscelaneous *)
  (****************)
  { p    = Bool false;
    name = "var_append_fun_name";
    desc = `String "Should the function name be appended to the variable name."; 
    kind = Internal; } ::

   { p    = Bool false;
     name = "widening_out";
     desc = `String "Widening outside or inside loops. \
             Remark: if the widening is done inside loops, then termination \
             is not guaranteed in general. Nonetheless, if the meet operator \
             is monotonous then this should always terminates."; 
     kind = Internal; } ::

    { p    = CallPolicy CallDirectAll;
    name = "call_policy";
    desc = `String "Policy used for abstract calls. Can be CallDirectAll or \
            CallTopHeuristic"; 
    kind = Internal; } ::

   []


let config = ref default


(* -------------------------------------------------------------------- *)

let find_int name () =
  let f param = match param.p with
  | Int i when param.name = name -> Some i
  | _ -> None in
  List.find_map f !config

let find_bool name () =
  let f param = match param.p with
    | Bool i when param.name = name -> Some i
    | _ -> None in
  List.find_map f !config

let find_boolref name () =
  let f param = match param.p with
    | BoolRef i when param.name = name -> Some i
    | _ -> None in
  List.find_map f !config

let find_comppass name () =
  let f param = match param.p with
    | CompPass i when param.name = name -> Some i
    | _ -> None in
  List.find_map f !config

let find_ranges name () =
  let f param = match param.p with
    | InputRanges i when param.name = name -> Some i
    | _ -> None in
  List.find_map f !config

let find_callpolicy name () =
  let f param = match param.p with
    | CallPolicy i when param.name = name -> Some i
    | _ -> None in
  List.find_map f !config

let find_initprint name () =
  let f param = match param.p with
    | InitPrint i when param.name = name -> Some i
    | _ -> None in
  List.find_map f !config

let sc_input_ranges            = find_ranges     "input_range"
let sc_comp_pass               = find_comppass   "compilation_pass"
let sc_k_unroll                = find_int        "k_unroll"
let sc_call_policy             = find_callpolicy "call_policy"
let sc_widening_out            = find_bool       "widening_out"
let sc_zero_threshold          = find_bool       "zero_threshold"
let sc_param_threshold         = find_bool       "param_threshold"
let sc_more_threshold          = find_bool       "more_threshold"
let sc_flow_dep                = find_bool       "flow_dependency"
let sc_if_disj                 = find_bool       "if_disjunction"
let sc_pif_movecc_as_if        = find_bool       "pif_movecc_as_if"
let sc_while_flags_setfrom_dep = find_bool       "while_flags_setfrom_dep"
let sc_dynamic_packing         = find_bool       "dynamic_packing"
let sc_print_program           = find_bool       "print_program"
let sc_print_stats             = find_bool       "print_stats"
let sc_arr_no_print            = find_bool       "arr_no_print"
let sc_glob_no_print           = find_bool       "glob_no_print"
let sc_nrel_no_print           = find_boolref    "nrel_no_print"
let sc_ignore_unconstrained    = find_bool       "ignore_unconstrained"
let sc_is_init_no_print        = find_initprint  "is_init_no_print"
let sc_bool_no_print           = find_bool       "bool_no_print"
let sc_print_symb_subst        = find_bool       "print_symb_subst"
let sc_var_append_fun_name     = find_bool       "var_append_fun_name"


(* -------------------------------------------------------------------- *)
let change param (t : Json.Basic.t) = match param.p, t with
  | Int _, `Int i -> { param with p = Int i }
  | Int _, _  ->
    raise (BadSafetyConfig (param.name ^ " must be of type int"))
                 
  | Bool _, `Bool b -> { param with p = Bool b }
  | Bool _, _ ->
    raise (BadSafetyConfig (param.name ^ " must be of type bool"))

  | BoolRef _, `Bool b -> { param with p = BoolRef (ref b) }
  | BoolRef _, _ ->
    raise (BadSafetyConfig (param.name ^ " must be of type bool"))

  | CallPolicy _, `String pol ->
    let topol = function
      | "CallDirectAll" -> CallDirectAll
      | "CallTopHeuristic" -> CallTopHeuristic
      | _ -> raise (BadSafetyConfig ("unknown policy"))
    in
    { param with p = CallPolicy (topol pol) }
  | CallPolicy _, _ ->
    raise (BadSafetyConfig (param.name ^ " must be of type string"))

  | InitPrint _, `String ip ->
    let toip = function        
      | "IP_None" -> IP_None
      | "IP_NoArray" -> IP_NoArray
      | "IP_All" -> IP_All
      | _ -> raise (BadSafetyConfig ("unknown init printing parameter"))
    in
    { param with p = InitPrint (toip ip) }
  | InitPrint _, _ ->
    raise (BadSafetyConfig (param.name ^ " must be of type string"))

  | CompPass _, `String s ->
    let pass =
      try  compiler_step_of_string s
      with Not_found ->
        raise (BadSafetyConfig ("unknown init printing parameter"))
    in
    { param with p = CompPass pass }
  | CompPass _, _ ->
    raise (BadSafetyConfig (param.name ^ " must be of type string"))

  | InputRanges _, (`Assoc _ as r) ->
    let ranges = input_ranges_of_json r in
    { param with p = InputRanges ranges }
  | InputRanges _, _ ->
    raise (BadSafetyConfig (param.name ^ " must be a dictionary"))


(* -------------------------------------------------------------------- *)
let rec of_json config (data : Json.Basic.t) =
  match data with
  | `Assoc data -> List.fold_left of_json_assoc config data
  | _ -> raise (BadSafetyConfig "not an dictionnary")

and of_json_assoc config (name, t) = match config with
  | [] -> raise (BadSafetyConfig ("key " ^ name ^ " not found"))
  | param :: config ->
    if param.name = name
    then (change param t) :: config
    else param :: (of_json_assoc config (name, t))


(*-------------------------------------------------------------------- *)
let irs_to_json irs : (string * Json.Basic.t) list =
  let doit ir = ( ir.ir_name,
                  `Assoc [("min", `String ir.ir_min);
                          ("max", `String ir.ir_max)] ) in
  List.map doit irs

let pol_to_string = function
      | CallDirectAll    -> "CallDirectAll" 
      | CallTopHeuristic -> "CallTopHeuristic" 

let ip_to_string = function
      | IP_None          -> "IP_None"
      | IP_NoArray       -> "IP_NoArray" 
      | IP_All           -> "IP_All"

let rec to_json_gen f config : Json.Basic.t =
  let doit param : string * Json.Basic.t =
    let t = match param.p with
      | Int i -> `Int i
      | Bool b -> `Bool b
      | BoolRef b -> `Bool !b
      | InitPrint i -> `String (ip_to_string i)
      | CallPolicy p -> `String (pol_to_string p)
      | CompPass p -> `String (fst (Glob_options.print_strings p))
      | InputRanges irs -> `Assoc (irs_to_json irs) in
    param.name, (f param t) in
  
  let data = List.map doit config in
  `Assoc data

let to_json = to_json_gen (fun _ t -> t)

let to_json_doc config : Json.Basic.t =
  let mk_param_doc param t =
    `Assoc [
      ("default", t);
      ("description", param.desc)
    ] in
  to_json_gen mk_param_doc config
        
(* -------------------------------------------------------------------- *)
let pp_config (fmt : Format.formatter) config =
  Json.Basic.pretty_print fmt (to_json config)

let pp_current_config fmt = pp_config fmt !config

let pp_current_config_diff () =
  let config = List.filter (fun x ->
      let x' = List.find (fun y -> y.name = x.name) default in
      x.p <> x'.p) !config in
  if config <> [] then
    Format.eprintf "Checker configuration parameters:@\n%a@.@." 
      pp_config config
  else
    Format.eprintf "Default checker parameters.@.@." 

(* -------------------------------------------------------------------- *)
let mk_doc dir =
  let json : Json.Basic.t = to_json_doc default in
  try
    let fpath = dir ^ "checker_config_doc.json" in
    let file = Stdlib.open_out fpath in
    let () = Json.Basic.pretty_to_channel file json in
    let () = close_out file in
    Format.printf "Created configuration documentation in %s@." fpath
  with Sys_error s ->
    Format.eprintf "@[<v>Failed to create configuration documentation:@;\
                    %s@.@]" s

let mk_default dir =
  let json : Json.Basic.t = to_json default in
  try
    let fpath = dir ^ "checker_config_default.json" in
    let file = Stdlib.open_out fpath in
    let () = Stdlib.output_string file
        "// Default configuration file. Automatically generated, any changes \
         will be overwritten.\n" in
    let () = Json.Basic.pretty_to_channel file json in
    let () = close_out file in
    Format.printf "Created default configuration file in %s@." fpath
  with Sys_error s ->
    Format.eprintf "@[<v>Failed to create default configuration file:@;\
                    %s@.@]" s

let mk_config_doc dir =
  let dir = if String.ends_with dir "/" then dir else dir ^ "/" in
  mk_doc dir;
  mk_default dir
  
  
(* -------------------------------------------------------------------- *)
let load_config (filename : string) : unit =
  try
    let () =
      config := of_json !config ((Json.Basic.from_file filename :> Json.Basic.t))
    in
    Format.eprintf "Configuration file loaded: %s@." filename
  with
  | Json.Json_error _ ->
    Format.eprintf "ERROR: safety configuration file %s is invalid@." filename;
    exit 1
  | BadSafetyConfig s ->
    Format.eprintf "ERROR: safety configuration file %s: %s@." filename s;
    exit 1
