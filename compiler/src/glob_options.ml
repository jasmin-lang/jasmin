open Utils
(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let latexfile = ref ""
let debug = ref false
let coqfile = ref ""
let coqonly = ref false
let print_list = ref []
let ecfile = ref ""
let ec_list = ref []
let check_safety = ref false
let safety_param = ref None
let safety_config = ref None
let stop_after = ref None
let lea = ref false
let set0 = ref false
let model = ref Normal

let set_coqonly s =
  coqfile := s;
  coqonly := true

let poptions = [
    Compiler.Typing
  ; Compiler.ParamsExpansion
  ; Compiler.AddArrInit
  ; Compiler.Inlining
  ; Compiler.RemoveUnusedFunction
  ; Compiler.Unrolling
  ; Compiler.Splitting
  ; Compiler.AllocInlineAssgn
  ; Compiler.DeadCode_AllocInlineAssgn
  ; Compiler.RegArrayExpansion
  ; Compiler.RemoveArrInit 
  ; Compiler.RemoveGlobal
  ; Compiler.RegArrayExpansion
  ; Compiler.MakeRefArguments
  ; Compiler.LowerInstruction
  ; Compiler.StackAllocation
  ; Compiler.RegAllocation
  ; Compiler.DeadCode_RegAllocation
  ; Compiler.Linearisation
  ; Compiler.Assembly ]

let set_printing p () =
  print_list := p :: !print_list

let set_stop_after p () = 
  stop_after := Some p

let set_all_print () =
  print_list := poptions

let set_ec f =
  ec_list := f :: !ec_list

let set_constTime () = model := ConstantTime
let set_safety () = model := Safety

let set_checksafety () = check_safety := true
let set_safetyparam s = safety_param := Some s
let set_safetyconfig s = safety_config := Some s

let print_strings = function
  | Compiler.Typing                      -> "typing"   , "typing"
  | Compiler.ParamsExpansion             -> "cstexp"   , "constant expansion"
  | Compiler.AddArrInit                  -> "addarrinit", "add array initialisation"
  | Compiler.Inlining                    -> "inline"   , "inlining"
  | Compiler.RemoveUnusedFunction        -> "rmfunc"   , "remove unused function"
  | Compiler.Unrolling                   -> "unroll"   , "unrolling"
  | Compiler.Splitting                   -> "splitting", "liverange splitting"
  | Compiler.AllocInlineAssgn            -> "valloc"   , "inlined variables allocation"
  | Compiler.DeadCode_AllocInlineAssgn   -> "vallocd"  , "dead code after inlined variables allocation"
  | Compiler.RemoveArrInit               -> "rmarrinit" , "remove array initialisation"
  | Compiler.RemoveGlobal                -> "rmglobals" , "remove globals variables"
  | Compiler.RegArrayExpansion           -> "arrexp"   , "expansion of register arrays"
  | Compiler.LowerInstruction            -> "lowering" , "lowering of instructions"
  | Compiler.MakeRefArguments             -> "makeref"   , "add assignments before and after call to ensure that arguments and results are ref ptr"
  | Compiler.StackAllocation             -> "stkalloc" , "stack allocation"
  | Compiler.RemoveReturn                -> "rmreturn" , "remove unused returned values"
  | Compiler.RegAllocation               -> "ralloc"   , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd"  , "dead code after register allocation"
 
  | Compiler.Linearisation               -> "linear"   , "linearisation"
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
    "-coq"     , Arg.Set_string coqfile, "[filename]: generate the corresponding coq file";
    "-coqonly" , Arg.String set_coqonly, "[filename]: generate the corresponding coq file, and exit";
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
    "-safetyconfig", Arg.String set_safetyconfig, "[filename]: use filename (JSON) as configuration file for the safety checker";
    "-wlea", Arg.Unit (add_warning UseLea), ": print warning when lea is used";
    "-w_"  , Arg.Unit (add_warning IntroduceNone), ": print warning when extra _ is introduced";
    "-wea", Arg.Unit (add_warning ExtraAssignment), ": print warning when assignment is introduced";
    "-nowarning", Arg.Unit (nowarning), ": do no print warning"
  ] @  List.map print_option poptions @ List.map stop_after_option poptions

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

                                      
