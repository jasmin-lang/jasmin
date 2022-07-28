open Expr
open Sopn
open Arch_extra
open X86_extra
open Linear
open Format

let headers = [| "function"; "instruction" ; "branch" ; "jump" ; "ret" ; "syscall" ; "store" ; "load" ; "init_msf" ; "set_msf" ; "mov_msf" ; "protect" |]

let empty () : (string, int) Hashtbl.t = Hashtbl.create (Array.length headers)
let get s k : int =
  try Hashtbl.find s k with Not_found -> 0
let inc s k : unit =
  match Hashtbl.find s k with
  | exception Not_found -> Hashtbl.add s k 1
  | old -> Hashtbl.replace s k (old + 1)

let pp_strings fmt a =
  fprintf fmt "%s" a.(0);
  for i = 1 to Array.length a - 1 do
    fprintf fmt ",%s" a.(i)
  done

let pp_stats name fmt s =
    fprintf fmt "%s" name;
    for i = 1 to Array.length headers - 1 do
      fprintf fmt ",%d" (get s headers.(i))
    done

let compute_lval s =
  function
  | Lnone _
  | Lvar _
    -> ()
  | Lmem _ -> inc s "store"
  | Laset _ -> assert false
  | Lasub _ -> assert false

let compute_arg s =
  function
  | Pconst _ | Pbool _ -> ()
  | Parr_init _ -> assert false
  | Pvar { gs = Slocal } -> ()
  | Pvar { gs = Sglob } -> inc s "load"
  | Pget _ -> assert false
  | Psub _ -> assert false
  | Pload _ -> inc s "load"
  | Papp1 _ | Papp2 _ | PappN _ | Pif _ -> ()

let compute_xop s =
  function
  | Oset0 _
  | Oconcat128
  | Ox86MOVZX32
    -> ()
  | Oprotect _ -> inc s "protect"
  | Oset_msf -> inc s "set_msf"
  | Oinit_msf -> inc s "init_msf"
  | Omov_msf -> inc s "mov_msf"

let compute_op s =
  function
  | Oasm (ExtOp op) -> compute_xop s op
  | _ -> ()

let compute_i s { li_i ; _ } =
  inc s "instruction";
  match li_i with
  | Lopn (xs, op, args) ->
     List.iter (compute_lval s) xs;
     List.iter (compute_arg s) args;
     compute_op s op
  | Lsyscall _ -> inc s "syscall"
  | Lalign -> ()
  | Llabel _ -> ()
  | Lgoto _ -> inc s "jump"
  | LstoreLabel _ -> inc s "store"
  | Ligoto _ -> inc s "ret"
  | Lcond _ -> inc s "branch"

let compute c s = List.iter (compute_i s) c

let stats_of_fd name fd =
  let s = empty () in
  compute fd.lfd_body s;
  printf "%a@." (pp_stats name) s

let doit tbl { lp_funcs ; _ } =
  printf "%a@." pp_strings headers;
  List.iter (fun (n, fd) -> stats_of_fd (Conv.string_of_funname tbl n) fd) lp_funcs
