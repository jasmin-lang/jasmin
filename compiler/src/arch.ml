(* -------------------------------------------------------------------- *)
open Utils

(* -------------------------------------------------------------------- *)
type os   = [`Windows | `Linux | `Mac | `BSD | `Solaris]
type arch = [`X86 | `X86_64 | `PowerPC | `ARM | `MIPS]

(* -------------------------------------------------------------------- *)
let string_of_os (os : os) =
  match os with
  | `Windows -> "windows"
  | `Linux   -> "linux"
  | `Mac     -> "mac"
  | `BSD     -> "bsd"
  | `Solaris -> "solaris"


(* -------------------------------------------------------------------- *)
let string_of_arch (arch : arch) =
  match arch with
  | `X86     -> "x86"
  | `X86_64  -> "x86_64"
  | `PowerPC -> "powerpc"
  | `ARM     -> "arm"
  | `MIPS    -> "mips"

(* -------------------------------------------------------------------- *)
let os_patterns : (string * os) list = [
  ("windows", `Windows);
  ("linux"  , `Linux  );
  ("mac"    , `Mac    );
  ("darwin" , `Mac    );
  ("^mingw" , `Windows);
  ("^cygwin", `Windows);
  ("bsd$"   , `BSD    );
  ("SunOS"  , `Solaris);
]

let arch_patterns : (string * arch) list = [
  ("^x86$"          , `X86    );
  ("i[0-9]+86"      , `X86    );
  ("amd64"          , `X86_64 );
  ("x86_64"         , `X86_64 );
  ("Power Macintosh", `PowerPC);
  ("^arm"           , `ARM    );
  ("^mips"          , `MIPS   );
]

(* -------------------------------------------------------------------- *)
let uname (mode : char) : string option =
  let command = Printf.sprintf "uname -%c" mode in

  try
    let stream = Unix.open_process_in command in
    BatPervasives.finally
      (fun () -> close_in stream)
      (fun () -> Some (String.strip (input_line stream)))
      ()
  with
  | (End_of_file | Unix.Unix_error _ | Sys_error _) ->
      None

(* -------------------------------------------------------------------- *)
let detect_os () : os option =
  let detect name =
    let detect1 (re, os) =
      try
        ignore (Str.search_forward (Str.regexp_case_fold re) name 0 : int);
        Some os
      with Not_found -> None
    in List.Exceptionless.find_map detect1 os_patterns in

  let name =
    if   Sys.os_type == "Win32"
    then try Some (Sys.getenv "OS") with Not_found -> None
    else uname 's' in

  obind detect name

(* -------------------------------------------------------------------- *)
let detect_arch () : arch option =
  let detect name =
    let detect1 (re, arch) =
      try
        ignore (Str.search_forward (Str.regexp_case_fold re) name 0 : int);
        Some arch
      with Not_found -> None
    in List.Exceptionless.find_map detect1 arch_patterns in

  let name =
    if   Sys.os_type == "Win32"
    then try  Some (Sys.getenv "PROCESSOR_ARCHITECTURE")
         with Not_found -> None
    else uname 'm' in

  obind detect name

(* --------------------------------------------------------------------- *)
let os   = detect_os   ()
let arch = detect_arch ()
