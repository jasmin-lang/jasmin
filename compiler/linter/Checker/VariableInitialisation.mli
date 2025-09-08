(** module VIChecker

    checker module for variable initialisation. This expects a program to be
    decorated according to the [ReachingDefinitions] module. It checks that
    every (syntactically) used variable is initialised in the domain. *)

open Jasmin
open Annotation

val check_prog : (RDDomain.t annotation, 'asm) Prog.prog -> CompileError.t list
