open Utils
(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let latexfile = ref ""
let typeonly = ref false
let debug = ref false
let print_list = ref []
let ecfile = ref ""
let ec_list = ref []
let check_safety = ref false
let safety_param = ref None

let help_intrinsics = ref false

let lea = ref false
let set0 = ref false
let model = ref Normal

let poptions = [
    Compiler.Typing
  ; Compiler.ParamsExpansion
  ; Compiler.Inlining
  ; Compiler.RemoveUnusedFunction
  ; Compiler.Unrolling
  ; Compiler.Splitting
  ; Compiler.AllocInlineAssgn
  ; Compiler.DeadCode_AllocInlineAssgn
  ; Compiler.ShareStackVariable
  ; Compiler.DeadCode_ShareStackVariable
  ; Compiler.RegArrayExpansion
  ; Compiler.RemoveGlobal
  ; Compiler.LowerInstruction
  ; Compiler.RegAllocation
  ; Compiler.DeadCode_RegAllocation
  ; Compiler.StackAllocation
  ; Compiler.Linearisation
  ; Compiler.Assembly ]

let set_printing p () =
  print_list := p :: !print_list

let set_all_print () =
  print_list := poptions

let set_ec f =
  ec_list := f :: !ec_list

let set_constTime () = model := ConstantTime
let set_safety () = model := Safety

let set_checksafety () = check_safety := true

let set_safetyparam s = safety_param := Some s

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
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-typeonly", Arg.Set typeonly      , ": stop after typechecking";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-latex"     , Arg.Set_string latexfile, "[filename]: generate the corresponding LATEX file";
    "-pall"    , Arg.Unit set_all_print, "print program after each compilation steps";
    "-lea"     , Arg.Set lea           , ": use lea as much as possible (default is nolea)";
    "-nolea"   , Arg.Clear lea         , ": try to use add and mul instead of lea";
    "-set0"     , Arg.Set set0          , ": use [xor x x] to set x to 0 (default is not)";
    "-noset0"   , Arg.Clear set0        , ": do not use set0 option";
    "-ec"       , Arg.String  set_ec    , "[f]: extract function [f] and its dependencies to an easycrypt file";
    "-oec"     ,  Arg.Set_string ecfile , "[filename]: use filename as output destination for easycrypt extraction";
    "-CT" , Arg.Unit set_constTime      , ": generates model for constant time verification";
    "-safety", Arg.Unit set_safety      , ": generates model for safety verification";
    "-checksafety", Arg.Unit set_checksafety, ": automatically check for safety";
    "-safetyparam", Arg.String set_safetyparam,
    "parameter for automatic safety verification:\n\
     format: f_1>p_1:...:p_l|f_2>p_1':...:p_l'|...\
     where each p_i is of the form:\n\
     v_1,...,v_n;v_1',...,v_k'\n\
     v_1,...,v_n: list of pointer variables that have to be considered together\n\
     v_1',...,v_k': list of relational variables";
    "--help-intrinsics", Arg.Set help_intrinsics, "List the set of intrinsic operators";
  ] @  List.map print_option poptions

let usage_msg = "Usage : jasminc [option] filename"



(* -------------------------------------------------------------------- *)
let eprint step pp_prog p =
  if List.mem step !print_list then
    let (_, msg) = print_strings step in
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* After %s *)@.@." msg;
    Format.eprintf "%a@.@.@." pp_prog p
