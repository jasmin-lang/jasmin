open Prog

(** Remove unused results.

Based on global liveness information, this removes from non-export function the
returned values that are never used by the callers.

FIXME: this assumes that the program never calls export functions.

*)
val analyse : ('a * ('sop1, 'sop2, 'info, 'asm) func) list -> funname -> bool list option
