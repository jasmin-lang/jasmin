open Utils
(*--------------------------------------------------------------------- *)
let version_string = "Jasmin Compiler @VERSION@"
(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let latexfile = ref ""
let debug = ref false
let print_list = ref []
let ecfile = ref ""
let ec_list = ref []
let ec_array_path = ref Filename.current_dir_name
let cl_list = ref []
let check_safety = ref false
let safety_param = ref None
let safety_config = ref None
let stop_after = ref None
let safety_makeconfigdoc = ref None   

let help_version = ref false
let help_intrinsics = ref false
type color = | Auto | Always | Never
let color = ref Auto

let ct_list = ref None
let infer   = ref false 


let lea = ref false
let set0 = ref false
let model = ref Normal
let print_stack_alloc = ref false
let introduce_array_copy = ref true
let print_dependencies = ref false 
let lazy_regalloc = ref false

type architecture =
  | X86_64
  | ARM_M4
let target_arch = ref X86_64

let set_target_arch a =
  let a' =
    match a with
    | "x86-64" -> X86_64
    | "arm-m4" -> ARM_M4
    | _ -> assert false
  in target_arch := a'

type x86_assembly_style = [`ATT | `Intel ]
let assembly_style : x86_assembly_style ref = ref `ATT

let set_syntax style () = assembly_style := style

let set_printing p () =
  print_list := p :: !print_list

let set_stop_after p () = 
  stop_after := Some p

let set_all_print () =
  print_list := Compiler.compiler_step_list

let set_ec f =
  ec_list := f :: !ec_list

let set_cl f =
  cl_list := f :: !cl_list

let set_ec_array_path p =
  ec_array_path := p

let set_constTime () = model := ConstantTime
let set_safety () = model := Safety

let set_checksafety () = check_safety := true
let set_safetyparam s = safety_param := Some s
let set_safetyconfig s = safety_config := Some s
let set_safety_makeconfigdoc s = safety_makeconfigdoc := Some s

let set_color c =
  let assoc = function
    | "auto"   -> Auto
    | "always" -> Always
    | "never"  -> Never
    | _        -> assert false
  in
  color := assoc c

let set_ct () =  
  if !ct_list = None then ct_list := Some []

let set_ct_on s = 
  ct_list := 
    Some (match !ct_list with
          | None -> [s]
          | Some l -> s::l)

let parse_jasmin_path s =
  s |> String.split_on_char ':' |> List.map (String.split ~by:"=")

let idirs =
  ref (try "JASMINPATH" |> Sys.getenv |> parse_jasmin_path with _ -> [])

let set_idirs s = 
  match String.split_on_char ':' s with
  | [s1; s2] -> idirs := (s1,s2)::!idirs
  | _ -> hierror ~loc:Lnone ~kind:"parsing arguments" "bad format for -I : ident:path expected"

type call_conv = Linux | Windows

let call_conv = ref Linux (* Default value is chosen on start-up in `main_compiler` *)

let set_cc cc = 
  let cc = 
    match cc with
    | "windows" -> Windows
    | "linux" -> Linux
    | _ -> assert false
  in call_conv := cc

let print_strings = function
  | Compiler.Typing                      -> "typing"   , "typing"
  | Compiler.ParamsExpansion             -> "cstexp"   , "param expansion"
  | Compiler.ArrayCopy                   -> "arraycopy", "array copy"
  | Compiler.AddArrInit                  -> "addarrinit", "add array initialisation"
  | Compiler.Inlining                    -> "inline"   , "inlining"
  | Compiler.RemoveUnusedFunction        -> "rmfunc"   , "remove unused function"
  | Compiler.Unrolling                   -> "unroll"   , "unrolling"
  | Compiler.Splitting                   -> "splitting", "liverange splitting"
  | Compiler.Renaming                    -> "renaming" , "variable renaming to remove copies"
  | Compiler.RemovePhiNodes              -> "rmphi"    , "remove phi nodes introduced by splitting"
  | Compiler.DeadCode_Renaming           -> "renamingd", "dead code after variable renaming to remove copies"
  | Compiler.RemoveArrInit               -> "rmarrinit", "remove array initialisation"
  | Compiler.RegArrayExpansion           -> "arrexp"   , "expansion of register arrays"
  | Compiler.RemoveGlobal                -> "rmglobals", "remove globals variables"
  | Compiler.MakeRefArguments            -> "makeref"  , "add assignments before and after call to ensure that arguments and results are ref ptr"
  | Compiler.LowerInstruction            -> "lowering" , "lowering of instructions"
  | Compiler.PropagateInline             -> "propagate", "propagate inline variables"
  | Compiler.StackAllocation             -> "stkalloc" , "stack allocation"
  | Compiler.RemoveReturn                -> "rmreturn" , "remove unused returned values"
  | Compiler.RegAllocation               -> "ralloc"   , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd"  , "dead code after register allocation"
  | Compiler.Linearization               -> "linear"   , "linearization"
  | Compiler.Tunneling                   -> "tunnel"   , "tunneling"
  | Compiler.Assembly                    -> "asm"      , "generation of assembly"

let print_option p =
  let s, msg = print_strings p in
  ("-p"^s, Arg.Unit (set_printing p), "print program after "^msg)

let stop_after_option p = 
  let s, msg = print_strings p in
  ("-until_"^s, Arg.Unit (set_stop_after p), "stop after "^msg)

let options = [
    "-version" , Arg.Set help_version  , "display version information about this compiler (and exits)";
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-I"       , Arg.String set_idirs  , "[ident:path]: bind ident to path for from ident require ...";
    "-latex"     , Arg.Set_string latexfile, "[filename]: generate the corresponding LATEX file";
    "-lea"     , Arg.Set lea           , ": use lea as much as possible (default is nolea)";
    "-nolea"   , Arg.Clear lea         , ": try to use add and mul instead of lea";
    "-set0"     , Arg.Set set0          , ": use [xor x x] to set x to 0 (default is not)";
    "-noset0"   , Arg.Clear set0        , ": do not use set0 option";
    "-ec"       , Arg.String  set_ec    , "[f]: extract function [f] and its dependencies to an easycrypt file";
    "-oec"     ,  Arg.Set_string ecfile , "[filename]: use filename as output destination for easycrypt extraction";
    "-oecarray" , Arg.String set_ec_array_path, "[dir]: output easycrypt array theories to the given path";
    "-cl"       , Arg.String set_cl     , "[f]: extract function [f] and its dependencies to cryptoline";
    "-CT" , Arg.Unit set_constTime      , ": generates model for constant time verification";
    "-checkCT", Arg.Unit set_ct         , ": checks that the full program is constant time (using a type system)";
    "-checkCTon", Arg.String set_ct_on  , "[f]: checks that the function [f] is constant time (using a type system)";
    "-infer"    , Arg.Set infer         , "infers security level annotations of the constant time type system";          
    "-safety", Arg.Unit set_safety      , ": generates model for safety verification";
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
    "-wlea", Arg.Unit (add_warning UseLea), ": print warning when lea is used";
    "-w_"  , Arg.Unit (add_warning IntroduceNone), ": print warning when extra _ is introduced";
    "-wea", Arg.Unit (add_warning ExtraAssignment), ": print warning when extra assignment is introduced";
    "-winsertarraycopy", Arg.Unit (add_warning IntroduceArrayCopy), ": print warning when array copy is introduced";
    "-noinsertarraycopy", Arg.Clear introduce_array_copy, ": do not automatically insert array copy";
    "-nowarning", Arg.Unit (nowarning), ": do no print warning";
    "-color", Arg.Symbol (["auto"; "always"; "never"], set_color), ": print messages with color";
    "-help-intrinsics", Arg.Set help_intrinsics, "List the set of intrinsic operators";
    "-print-stack-alloc", Arg.Set print_stack_alloc, ": print the results of the stack allocation OCaml oracle";
    "-lazy-regalloc", Arg.Set lazy_regalloc, "\tAllocate variables to registers in program order";
    "-pall"    , Arg.Unit set_all_print, "print program after each compilation steps";
    "-print-dependencies", Arg.Set print_dependencies, ": print dependencies and exit";
    "-intel", Arg.Unit (set_syntax `Intel), "use intel syntax (default is AT&T)"; 
    "-ATT", Arg.Unit (set_syntax `ATT), "use AT&T syntax (default is AT&T)"; 
    "-call-conv", Arg.Symbol (["windows"; "linux"], set_cc), ": select calling convention (default depend on host architecture)";
    "-arch", Arg.Symbol (["x86-64"; "arm-m4"], set_target_arch), ": select target arch (default is x86-64)";
  ] @  List.map print_option Compiler.compiler_step_list @ List.map stop_after_option Compiler.compiler_step_list

let usage_msg = "Usage : jasminc [option] filename"



(* -------------------------------------------------------------------- *)
let eprint step pp_prog p =
  if List.mem step !print_list then begin
    let (_, msg) = print_strings step in
    Format.printf
"/* -------------------------------------------------------------------- */@.";
    Format.printf "/* After %s */@.@." msg;
    Format.printf "%a@.@.@." pp_prog p
    end;
  if !stop_after = Some step then exit 0
