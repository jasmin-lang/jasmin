(**
module VIChecker

checker module for variable initialisation. Implementation relies on the [Visitor.ExpressionChecker] module.
We first compute reaching definitions for each instruction of the program using the [ReachingDefinitions] module.
Then we check if a used variable (in an expression) is initialised in the domain.
*)

(**
Check mode for initialised variable analysis
- [Strict] : Check if a path exists where variable may not be initialised (can trigger false positive)
- [NotStrict] : Check if there is no path in the program where variable is initialised (less restrictive but let some error pass)
*)
type check_mode = Strict | NotStrict

(**
Checker entrypoint
args :
- [('len,('asm) Jasmin.Prog.prog] : the program to check
- [check_mode] : checker mode

returns :
- [Error.CompileError.compile_error list] : list of variable initialisation errors
*)
val check_vi : ('info, 'asm) Jasmin.Prog.prog -> check_mode -> Error.CompileError.compile_error list
