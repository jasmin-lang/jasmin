open X86_decl_core
open Utils
(*--------------------------------------------------------------------- *)
let version_string = "Jasmin Compiler @VERSION@"
(*--------------------------------------------------------------------- *)
let outfile = ref ""
let latexfile = ref ""
let debug = ref false
let timings = ref false
let print_list = ref []
let ecfile = ref ""
let ec_list = ref []
let ec_array_path = ref Filename.current_dir_name
let slice = ref []
let check_safety = ref false
let safety_param = ref None
let safety_config = ref None
let stop_after = ref None
let safety_makeconfigdoc = ref None   
let trust_aligned = ref false

let help_version = ref false
let help_intrinsics = ref false
type color = | Auto | Always | Never
let color = ref Auto

let ct_list = ref None
let infer   = ref false 

let sct_list = ref None

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

let set_ec_array_path p =
  ec_array_path := p

let set_slice f =
  slice := f :: !slice

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

let set_sct () =
  if !sct_list = None then sct_list := Some []

let set_sct_on s =
  sct_list :=
    Some (match !sct_list with
          | None -> [s]
          | Some l -> s::l)

let sct_comp_pass = ref Compiler.ParamsExpansion

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
  | Compiler.SLHLowering                  -> "slhlowering" , "selective load hardening lowering of instructions"
  | Compiler.PropagateInline             -> "propagate", "propagate inline variables"
  | Compiler.StackAllocation             -> "stkalloc" , "stack allocation"
  | Compiler.RemoveReturn                -> "rmreturn" , "remove unused returned values"
  | Compiler.RegAllocation               -> "ralloc"   , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd"  , "dead code after register allocation"
  | Compiler.Linearization               -> "linear"   , "linearization"
  | Compiler.Tunneling                   -> "tunnel"   , "tunneling"
  | Compiler.Assembly                    -> "asm"      , "generation of assembly"

let compiler_step_symbol =
  List.map (fun s -> fst (print_strings s)) Compiler.compiler_step_list

let symbol2pass =
  let tbl = Hashtbl.create 101 in
  List.iter (fun s -> Hashtbl.add tbl (fst (print_strings s)) s) Compiler.compiler_step_list;
  fun s -> Hashtbl.find tbl s

let set_sct_comp_pass s =
 sct_comp_pass := symbol2pass s

let print_option p =
  let s, msg = print_strings p in
  ("-p"^s, Arg.Unit (set_printing p), "print program after "^msg)

let stop_after_option p = 
  let s, msg = print_strings p in
  ("-until_"^s, Arg.Unit (set_stop_after p), "stop after "^msg)

let ip = ref 0

let rax = ref 0
let rcx = ref 0
let rdx = ref 0
let rbx = ref 0
let rsp = ref 0
let rbp = ref 0
let rsi = ref 0
let rdi = ref 0
let r8  = ref 0
let r9  = ref 0
let r10 = ref 0
let r11 = ref 0
let r12 = ref 0
let r13 = ref 0
let r14 = ref 0
let r15 = ref 0

let ref_of_reg r =
  let open X86_decl in
  match r with
  | RAX -> rax
  | RCX -> rcx
  | RDX -> rdx
  | RBX -> rbx
  | RSP -> rsp
  | RBP -> rbp
  | RSI -> rsi
  | RDI -> rdi
  | R8  -> r8
  | R9  -> r9
  | R10 -> r10
  | R11 -> r11
  | R12 -> r12
  | R13 -> r13
  | R14 -> r14
  | R15 -> r15
let regs = List.map ref_of_reg X86_decl.registers

let cf = ref Arch_decl.Undef
let pf = ref Arch_decl.Undef
let zf = ref Arch_decl.Undef
let sf = ref Arch_decl.Undef
let ofl = ref Arch_decl.Undef

let ref_of_flag f =
  let open X86_decl in
  match f with
  | CF -> cf
  | PF -> pf
  | ZF -> zf
  | SF -> sf
  | OF -> ofl
let flags = List.map ref_of_flag X86_decl.rflags

let set_flag f s =
  let open Arch_decl in
  let b =
    if s = "0" then Def false
    else if s = "1" then Def true
    else Undef
  in
  f := b

let options = [
    "-version" , Arg.Set help_version  , "display version information about this compiler (and exits)";
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-timings" , Arg.Set timings       , ": print a timestamp and elapsed time after each pass";
    "-I"       , Arg.String set_idirs  , "[ident:path]: bind ident to path for from ident require ...";
    "-latex"   , Arg.Set_string latexfile, "[filename]: generate the corresponding LATEX file (deprecated)";
    "-lea"     , Arg.Set lea           , ": use lea as much as possible (default is nolea)";
    "-nolea"   , Arg.Clear lea         , ": try to use add and mul instead of lea";
    "-set0"     , Arg.Set set0          , ": use [xor x x] to set x to 0 (default is not)";
    "-noset0"   , Arg.Clear set0        , ": do not use set0 option";
    "-ec"       , Arg.String  set_ec    , "[f]: extract function [f] and its dependencies to an easycrypt file";
    "-oec"     ,  Arg.Set_string ecfile , "[filename]: use filename as output destination for easycrypt extraction";
    "-oecarray" , Arg.String set_ec_array_path, "[dir]: output easycrypt array theories to the given path";
    "-CT" , Arg.Unit set_constTime      , ": generates model for constant time verification";
    "-checkCT", Arg.Unit set_ct         , ": checks that the full program is constant time (using a type system)";
    "-checkCTon", Arg.String set_ct_on  , "[f]: checks that the function [f] is constant time (using a type system)";
    "-infer"    , Arg.Set infer         , "infers security level annotations of the constant time type system";          
    "-checkSCT", Arg.Unit set_sct       , ": checks that the full program is speculative constant time (using a type system)";
    "-checkSCTon", Arg.String set_sct_on, "[f]: checks that the function [f] is speculative constant time (using a type system)";
    "-checkSCTafter", Arg.Symbol(compiler_step_symbol, set_sct_comp_pass), "start sct checker after given pass";
    "-slice"    , Arg.String set_slice  , "[f]: keep function [f] and all what it needs";
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
    "-nocheckalignment", Arg.Set trust_aligned, "do not report alignment issue as safety violations";
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
    "-ip", Arg.Set_int ip, "initial value of ip";
    "-regs", Arg.Tuple (List.map (fun r -> Arg.Set_int r) regs), "initial values of the regs";
    "-flags", Arg.Tuple (List.map (fun f -> Arg.String (set_flag f)) flags), "initial values of the flags";
  ] @  List.map print_option Compiler.compiler_step_list @ List.map stop_after_option Compiler.compiler_step_list

let usage_msg = "Usage : jasminc [option] filename"



(* -------------------------------------------------------------------- *)
let eprint step pp_prog p =
  if !timings then
    Format.eprintf "%t after %s@." pp_now (fst (print_strings step));
  if List.mem step !print_list then begin
    let (_, msg) = print_strings step in
    Format.printf
"/* -------------------------------------------------------------------- */@.";
    Format.printf "/* After %s */@.@." msg;
    Format.printf "%a@.@.@." pp_prog p
    end;
  if !stop_after = Some step then exit 0
