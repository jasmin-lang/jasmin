(** module VIChecker

    checker module for variable initialisation. This expects a program to be
    decorated according to the [ReachingDefinitions] module. It checks that
    every (syntactically) used variable is initialised in the domain. *)

open Jasmin
open Annotation

(** Check mode for initialised variable analysis
    - [Strict] : Check if a path exists where variable may not be initialised
      (can trigger false positive)
    - [NotStrict] : Check if there is no path in the program where variable is
      initialised (less restrictive but let some error pass) *)
type check_mode = Strict | NotStrict

val check_prog :
  ?mode:check_mode ->
  (RDDomain.t annotation, 'asm) Prog.prog ->
  CompileError.t list
