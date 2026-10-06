val analyse : ('info, 'asm) Prog.func list -> Prog.funname -> bool list option
(** Analyze unused results.

    Based on global liveness information, this identifies for non-export
    function the returned values that are never used by any of the callers.

    The returned function associates to each non-export function a list of
    boolean values matching its list of returned variables: a boolean true means
    that the corresponding returned variable is live at some call site; a
    boolean false means that the corresponding returned variable is dead at
    every call site. *)
