open Ssralg

type state = unit

(* FIXME syscall : I don't think that this implementation is a good one.
   But it allows to have something quick for the evaluator, so
   it is not crutial
*)

let _ =
  Random.self_init ()

let initial_state () = ()

let random_char _ =
  let n = Random.int 256 in
  Word0.wrepr Wsize.U8 (CoreConv.cz_of_int n)

let get_random (s : state) (z:BinNums.coq_Z) =
  let n = CoreConv.int_of_cz z in
  assert (0 <= n);
  s, List.init n random_char


(** FIXME: Reurn actual fd *)
let open_file (s : state) (filename: GRing.ComRing.sort list) =
  s, (Word0.wrepr Wsize.U64 (CoreConv.cz_of_int 1))

(** FIXME: actually close file *)
let close_file (s : state) fd =
  s, (Word0.wrepr Wsize.U64 (CoreConv.cz_of_int 1))


(** FIXME: actually write to file*)
let write_to_file (s: state) data fd =
  s, data

let read_from_file (s: state) data fd =
  s, data

let sc_sem : state Syscall.syscall_sem = {
  get_random = get_random;
  open_file =  open_file;
  close_file = close_file;
  write_to_file = write_to_file;
  read_from_file = read_from_file;
}
