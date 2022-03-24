open Utils
(*--------------------------------------------------------------------- *)
let version_string = "Jasmin Compiler @VERSION@"
(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let latexfile = ref ""
let typeonly = ref false
let debug = ref false
let print_list = ref []
let ecfile = ref ""
let ec_list = ref []
let cost_analysis = ref false
let cost_after_pass = ref "cstexp"
let dot_cfg = ref false
let check_safety = ref false
let safety_param = ref None
let safety_config = ref None
let safety_makeconfigdoc = ref None
let print_transformers = ref false
let print_cost_transformers = ref false

let help_version = ref false
let help_intrinsics = ref false

let lea = ref false
let set0 = ref false
let model = ref Normal

let set_printing p () =
  print_list := p :: !print_list

let set_all_print () =
  print_list := Compiler.compiler_step_list

let set_ec f =
  ec_list := f :: !ec_list

let set_constTime () = model := ConstantTime
let set_safety () = model := Safety

let set_checksafety () = check_safety := true
let set_safetyparam s = safety_param := Some s
let set_safetyconfig s = safety_config := Some s
let set_safety_makeconfigdoc s = safety_makeconfigdoc := Some s
      
let print_strings = function
  | Compiler.Typing                      -> "typing"   , "typing"
  | Compiler.ParamsExpansion             -> "cstexp"   , "constant expansion"
  | Compiler.Inlining                    -> "inline"   , "inlining"
  | Compiler.RemoveUnusedFunction        -> "rmfunc"   , "remove unused function"
  | Compiler.Unrolling                   -> "unroll"   , "unrolling"
  | Compiler.Splitting                   -> "splitting", "liverange splitting"
  | Compiler.AllocInlineAssgn            -> "valloc"   , "inlined variables allocation"
  | Compiler.DeadCode_AllocInlineAssgn   -> "vallocd"  , "dead code after inlined variables allocation"
  | Compiler.ShareStackVariable          -> "vshare"   , "sharing of stack variables"
  | Compiler.DeadCode_ShareStackVariable -> "vshared"  , "dead code after sharing of stack variables"
  | Compiler.RemoveArrInit               -> "rmarrinit" , "remove array init"
  | Compiler.RemoveGlobal                -> "rmglobals" , "remove globals variables"
  | Compiler.RegArrayExpansion           -> "arrexp"   , "expansion of register arrays"
  | Compiler.LowerInstruction            -> "lowering" , "lowering of instructions"
  | Compiler.RegAllocation               -> "ralloc"   , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd"  , "dead code after register allocation"
  | Compiler.StackAllocation             -> "stkalloc" , "stack allocation"
  | Compiler.Linearisation               -> "linear"   , "linearisation"
  | Compiler.Assembly                    -> "asm"      , "generation of assembly"

let print_option p =
  let s, msg = print_strings p in
  ("-p"^s, Arg.Unit (set_printing p), "print program after "^msg)

let options = [
    "-version" , Arg.Set help_version  , "display version information about this compiler (and exits)";
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-typeonly", Arg.Set typeonly      , ": stop after typechecking";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-latex"     , Arg.Set_string latexfile, "[filename]: generate the corresponding LATEX file";
    "-lea"     , Arg.Set lea           , ": use lea as much as possible (default is nolea)";
    "-nolea"   , Arg.Clear lea         , ": try to use add and mul instead of lea";
    "-set0"     , Arg.Set set0          , ": use [xor x x] to set x to 0 (default is not)";
    "-noset0"   , Arg.Clear set0        , ": do not use set0 option";
    "-ec"       , Arg.String  set_ec    , "[f]: extract function [f] and its dependencies to an easycrypt file";
    "-oec"     ,  Arg.Set_string ecfile , "[filename]: use filename as output destination for easycrypt extraction";
    "-CT" , Arg.Unit set_constTime      , ": generates model for constant time verification";
    "-safety", Arg.Unit set_safety      , ": generates model for safety verification";
    "-dot", Arg.Set dot_cfg, ": print CFG of assembly in DOT format";
    "-cost", Arg.Set cost_analysis, ": execution cost (WIP)";
    "-cost-after", Arg.Set_string cost_after_pass, ": pass after which to run the cost analysis (see printing options to know the names of the passes)";
    "-checksafety", Arg.Unit set_checksafety, ": automatically check for safety";
    "-safetyparam", Arg.String set_safetyparam,
    "parameter for automatic safety verification:\n    \
     format: \"f_1>param_1|f_2>param_2|...\" \
     where each param_i is of the form:\n    \
     pt_1,...,pt_n;len_1,...,len_k\n    \
     pt_1,...,pt_n: input pointers of f_i\n    \
     len_1,...,len_k: input lengths of f_i";
     "-safetyconfig", Arg.String set_safetyconfig, "[filename]: use filename (JSON) as configuration file for the safety checker";
    "-safetymakeconfigdoc", Arg.String set_safety_makeconfigdoc, "[dir]: make the safety checker configuration docs in [dir]";
    "-lt", Arg.Set print_transformers, "Print the leak transformers to stdout";
    "-ct", Arg.Set print_cost_transformers, "Print the cost transformers to stdout";
    "-help-intrinsics", Arg.Set help_intrinsics, "List the set of intrinsic operators";
    "-pall"    , Arg.Unit set_all_print, "print program after each compilation steps";
  ] @  List.map print_option Compiler.compiler_step_list

let usage_msg = "Usage : jasminc [option] filename"



(* -------------------------------------------------------------------- *)
let eprint step pp_prog p =
  if List.mem step !print_list then
    let (_, msg) = print_strings step in
    Format.printf
"/* -------------------------------------------------------------------- */@.";
    Format.printf "/* After %s */@.@." msg;
    Format.printf "%a@.@.@." pp_prog p
