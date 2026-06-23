(** Dependency analysis and check that no inline variable depends, when used, of
    a non-inline one.

    This is a variation on a standard information-flow tracking system in which
    it is OK to assign Low (inline) variables in High contexts as long as the
    Low variable is not used outside of said context.

    Dependencies are not transitively closed; for instance, if X depends on Y
    and Y depends on Z, the dependency of X on Z might be overlooked. This is
    meant to reduce the amount of reported warnings and produce more focused
    diagnostic messages.

    Current limitation: flows through memory are ignored, therefore loading a
    value from memory into an inline variable will not cause any warning to be
    issued. *)

val check_prog : ('info, 'asm) Jasmin.Prog.prog -> CompileError.t list
(** Detects whenever an inline variable, whose value is expected to be known at
    compile-time, depends on some non-inline variable and is used. Such
    situation usually leads to the failure of the compilation. *)
