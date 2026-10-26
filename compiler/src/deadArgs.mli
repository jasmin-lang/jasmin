val analyse :
  protect:(('info, 'asm) Prog.func -> Prog.var -> bool) ->
  ('info, 'asm) Prog.func list ->
  Prog.funname ->
  bool list option * bool list option
(** The parameters and the results of the functions that are used, the oracle
    of [Dead_args].

    A result is used when it is protected, or when, at some call site, its
    destination is live after the call; a parameter is used when it is
    protected, or when it is live at the entry of the body. The liveness is
    that of [Dead_code]: an assignment or an operator whose destinations are
    dead reads nothing, nor do the destinations of the unused results and the
    arguments of the unused parameters. The used positions are the least
    solution of these constraints, computed over the whole program: a
    parameter that only computes a result that only computes the argument of
    this parameter at another call is not used.

    The returned function associates to each function the list of booleans
    that tells, for each parameter and for each result, whether it is used, or
    [None] when they all are. *)
