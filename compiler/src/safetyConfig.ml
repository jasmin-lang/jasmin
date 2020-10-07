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

type init_print = IP_None  | IP_NoArray | IP_All

type kind  = Parameter | Printing | Internal 

type pvalue = | Bool       of bool         
              | BoolRef    of bool ref     
              | Int        of int          
              | InitPrint  of init_print   
              | CallPolicy of call_policy  

type param = { p     : pvalue;
               name  : string;
               desc  : string;
               kind  : kind; }

let default = 
  { p    = Int 1;
    name = "k_unroll";
    desc = "Number of unrolling of a loop body before applying the widening. \
            Higher values yield a more precise (and more costly) analysis."; 
    kind = Parameter; } ::

  { p    = CallPolicy CallDirectAll;
    name = "call_policy";
    desc = "Policy used for abstract calls."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "flow_dependency";
    desc = "Dependency graph includes flow dependencies."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "if_disjunction";
    desc = "Add disjunctions on if statements when possible."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "pif_movecc_as_if";
    desc = "Handle top-level conditional move and if expressions as if \
            statements. Combinatorial explosion if there are many movecc \
            and if expressions in the same block."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "while_flags_setfrom_dep";
    desc = "Pre-analysis looks for the variable corresponding to return \
            boolean flags appearing in while loop condition (adding them to \
            the set of variables in the relational domain)."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "dynamic_packing";
    desc = "Dynamic variable packing. Particularly useful if the analysis \
            runs after the register allocation."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "zero_threshold";
    desc = "Zero thresholds for the widening."; 
    kind = Parameter; } ::

  { p    = Bool true;
    name = "param_threshold";
    desc = "Thresholds from the analysis parameters for the widening."; 
    kind = Parameter; } ::

  { p    = Bool false;
    name = "more_threshold";
    desc = "More thresholds for the widening."; 
    kind = Parameter; } ::


  (***********************)
  (* Printing parameters *)
  (***********************)
  { p    = Bool true;
    name = "arr_no_print";
    desc = "Turn on printing of array variables."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "glob_no_print";
    desc = "Turn on printing of global variables."; 
    kind = Printing; } ::

  { p    = BoolRef (ref false);
    name = "nrel_no_print";
    desc = "Turn on printing of non-relational variables."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "ignore_unconstrained";
    desc = "Turn on printing of unconstrained variables."; 
    kind = Printing; } ::

  { p    = InitPrint IP_None;
    name = "is_init_no_print";
    desc = " Turn on printing of not initialized variables \
            (i.e. it is not certain that the variable is initialized)."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "bool_no_print";
    desc = "Turn on printing of boolean variables."; 
    kind = Printing; } ::

  { p    = Bool true;
    name = "print_symb_subst";
    desc = "Print substitutions done by the symbolic equality domain."; 
    kind = Printing; } ::

  (****************)
  (* Miscelaneous *)
  (****************)
  { p    = Bool false;
    name = "var_append_fun_name";
    desc = "Should the function name be appended to the variable name."; 
    kind = Internal; } ::

   { p    = Bool false;
     name = "widening_out";
     desc = "Widening outside or inside loops. \
             Remark: if the widening is done inside loops, then termination \
             is not guaranteed in general. Nonetheless, if the meet operator \
             is monotonous then this should always terminates."; 
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
let sc_arr_no_print            = find_bool       "arr_no_print"
let sc_glob_no_print           = find_bool       "glob_no_print"
let sc_nrel_no_print           = find_boolref    "nrel_no_print"
let sc_ignore_unconstrained    = find_bool       "ignore_unconstrained"
let sc_is_init_no_print        = find_initprint  "is_init_no_print"
let sc_bool_no_print           = find_bool       "bool_no_print"
let sc_print_symb_subst        = find_bool       "print_symb_subst"
let sc_var_append_fun_name     = find_bool       "var_append_fun_name"


(* -------------------------------------------------------------------- *)
exception BadSafetyConfig of string

let change param t = match param.p, t with
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


(* -------------------------------------------------------------------- *)
let rec of_json config (data : Json. t) =
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
let pol_to_string = function
      | CallDirectAll    -> "CallDirectAll" 
      | CallTopHeuristic -> "CallTopHeuristic" 

let ip_to_string = function
      | IP_None          -> "IP_None"
      | IP_NoArray       -> "IP_NoArray" 
      | IP_All           -> "IP_All"

let rec to_json config =
  let doit param : string * Json.t =
    let t = match param.p with
      | Int i -> `Int i
      | Bool b -> `Bool b
      | BoolRef b -> `Bool !b
      | InitPrint i -> `String (ip_to_string i)
      | CallPolicy p -> `String (pol_to_string p) in
    param.name, t in
  
  let data = List.map doit config in
  `Assoc data


(* -------------------------------------------------------------------- *)
let pp_config (fmt : Format.formatter) config =
  Json.pretty_print fmt (to_json config)

let pp_current_config fmt = pp_config fmt !config
  
let load_config (filename : string) : unit =
  try
    config := of_json !config ((Json.Basic.from_file filename :> Json.t)) 
  with
  | Json.Json_error _ ->
    Format.eprintf "ERROR: safety configuration file %s is invalid" filename
  | BadSafetyConfig s ->
    Format.eprintf "ERROR: safety configuration file %s: %s" filename s
