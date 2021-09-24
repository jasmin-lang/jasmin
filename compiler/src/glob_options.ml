open Utils
(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let latexfile = ref ""
let debug = ref false
let print_list = ref []
let ecfile = ref ""
let ec_list = ref []
let check_safety = ref false
let safety_param = ref None
let safety_config = ref None
let stop_after = ref None
let safety_makeconfigdoc = ref None   
let help_intrinsics = ref false
type color = | Auto | Always | Never
let color = ref Auto

let ct_list = ref None
let infer   = ref false 

let lea = ref false
let set0 = ref false
let model = ref Normal
let print_stack_alloc = ref false

let set_printing p () =
  print_list := p :: !print_list

let set_stop_after p () = 
  stop_after := Some p

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

let print_strings = function
  | Compiler.Typing                      -> "typing"   , "typing"
  | Compiler.ParamsExpansion             -> "cstexp"   , "param expansion"
  | Compiler.AddArrInit                  -> "addarrinit", "add array initialisation"
  | Compiler.Inlining                    -> "inline"   , "inlining"
  | Compiler.RemoveUnusedFunction        -> "rmfunc"   , "remove unused function"
  | Compiler.Unrolling                   -> "unroll"   , "unrolling"
  | Compiler.Splitting                   -> "splitting", "liverange splitting"
  | Compiler.AllocInlineAssgn            -> "valloc"   , "inlined variables allocation"
  | Compiler.DeadCode_AllocInlineAssgn   -> "vallocd"  , "dead code after inlined variables allocation"
  | Compiler.RemoveArrInit               -> "rmarrinit", "remove array initialisation"
  | Compiler.RemoveGlobal                -> "rmglobals", "remove globals variables"
  | Compiler.RegArrayExpansion           -> "arrexp"   , "expansion of register arrays"
  | Compiler.LowerInstruction            -> "lowering" , "lowering of instructions"
  | Compiler.PropagateInline            -> "propagate", "propagate inline variables"
  | Compiler.MakeRefArguments             -> "makeref" , "add assignments before and after call to ensure that arguments and results are ref ptr"
  | Compiler.StackAllocation             -> "stkalloc" , "stack allocation"
  | Compiler.RemoveReturn                -> "rmreturn" , "remove unused returned values"
  | Compiler.RegAllocation               -> "ralloc"   , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd"  , "dead code after register allocation"
 
  | Compiler.Linearisation               -> "linear"   , "linearisation"
  | Compiler.Tunneling                   -> "tunnel"   , "tunneling"
  | Compiler.Assembly                    -> "asm"      , "generation of assembly"

let print_option p =
  let s, msg = print_strings p in
  ("-p"^s, Arg.Unit (set_printing p), "print program after "^msg)

let stop_after_option p = 
  let s, msg = print_strings p in
  ("-until_"^s, Arg.Unit (set_stop_after p), "stop after "^msg)

let options = [
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-latex"     , Arg.Set_string latexfile, "[filename]: generate the corresponding LATEX file";
    "-lea"     , Arg.Set lea           , ": use lea as much as possible (default is nolea)";
    "-nolea"   , Arg.Clear lea         , ": try to use add and mul instead of lea";
    "-set0"     , Arg.Set set0          , ": use [xor x x] to set x to 0 (default is not)";
    "-noset0"   , Arg.Clear set0        , ": do not use set0 option";
    "-ec"       , Arg.String  set_ec    , "[f]: extract function [f] and its dependencies to an easycrypt file";
    "-oec"     ,  Arg.Set_string ecfile , "[filename]: use filename as output destination for easycrypt extraction";
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
    "-wea", Arg.Unit (add_warning ExtraAssignment), ": print warning when assignment is introduced";
    "-nowarning", Arg.Unit (nowarning), ": do no print warning";
    "-color", Arg.Symbol (["auto"; "always"; "never"], set_color), ": print messages with color";
    "--help-intrinsics", Arg.Set help_intrinsics, "List the set of intrinsic operators";
    "-print-stack-alloc", Arg.Set print_stack_alloc, ": print the results of the stack allocation OCaml oracle";
    "-pall"    , Arg.Unit set_all_print, "print program after each compilation steps";
  ] @  List.map print_option Compiler.compiler_step_list @ List.map stop_after_option Compiler.compiler_step_list

let usage_msg = "Usage : jasminc [option] filename"



(* -------------------------------------------------------------------- *)
let eprint step pp_prog p =
  if List.mem step !print_list then begin
    let (_, msg) = print_strings step in
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* After %s *)@.@." msg;
    Format.eprintf "%a@.@.@." pp_prog p
    end;
  if !stop_after = Some step then exit 0

                                      
