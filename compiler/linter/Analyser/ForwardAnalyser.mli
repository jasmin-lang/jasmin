(**
Module ForwardAnalyser :

This module implements a forward dataflow analysis for Jasmin programs. Analysis is defined at function level.
The analysis find a fixpoint for given dataflow equations described by the user.

It defines three modules :
- [Logic] : Abstract interface for the logic of the forward analysis
- [S] : Signature of the ForwardAnalyser module
- [Make] : Functor that takes a module implementing the ForwardAnalyserLogic interface and returns a module implementing the [S] signature
*)

(**
module type [Logic] :
Abstract interface for the logic of the forward analysis. The user must provides :
- domain type
- functions to modify the domain (intialisation, pretty printing, inclusion test, merge, spliting)
- function to handle atomic instructions (assign, function call, syscall, opn)

Control flow is handled by the [Make] functor (user don't have to implement it).
*)
module type Logic =
  sig

    (**
      Type of the domain used for the analysis
    *)
    type domain

    (**
      Build the initial value of the domain using the function passed as argument.

      args :
      - [('info,'asm) Prog.func] (function to analyse)

      returns :
      - [domain] (intial domain)
    *)
    val initialize : ('info, 'asm) Jasmin.Prog.func -> domain Annotation.annotation

    (**
      Pretty printer for the domain.

      args :
      - [Format.formatter] (formatter to use)
      - [domain] (domain to print)
    *)
    val pp : Format.formatter -> Jasmin.Location.i_loc * domain -> unit

    (**
      Inclusion test for the domain. [included a b] test if [a] is included in [b]

      args :
      - [domain] (first domain)
      - [domain] (second domain)

      returns :
      - [bool] (true if first domain is included in the second one)

    *)
    val included : domain -> domain -> bool

    (**
    Control flow functions used to handle conditionnal branches. [assume condition d] returns a pair of domain [d1,d2] such that :
    - [d1] is the domain [d] updated with the knowledge that [condition] is true
    - [d2] is the domain [d] updated with the knowledge that [condition] is false

    args :
    - [Jasmin.Prog.expr] (condition to test)
    - [domain] (domain to split)

    returns :
    - [domain * domain]
    *)
    val assume :
      Jasmin.Prog.expr ->
      domain Annotation.annotation ->
      domain Annotation.annotation * domain Annotation.annotation

    (**
    Merge two domains. [merge a b] returns a domain that is the result of the merge of [a] and [b].

    args :
    - [domain] (first domain)
    - [domain] (second domain)

    returns :
    - [domain] (merged domain)
    *)
    val merge : domain -> domain -> domain

    (**
    Function to remove a variable from a domain. This function is needed because of the way we handle for loops.
    args :

    - [Jasmin.Prog.var_i] (variable to remove)
    - [domain] (domain to update)

    returns :
    - [domain Annotation.annotation] (updated domain wrap with annotation type)
    *)
    val forget : Jasmin.Prog.var_i -> domain -> domain Annotation.annotation

    (**
    Function to handle function call instruction
    *)
    val funcall :
      Jasmin.Location.i_loc ->
      Jasmin.Prog.lvals ->
      Jasmin.CoreIdent.funname ->
      Jasmin.Prog.length list ->
      Jasmin.Prog.exprs -> domain -> domain Annotation.annotation

    (**
    Function to handle syscall instruction
    *)
    val syscall :
      Jasmin.Location.i_loc ->
      Jasmin.Prog.lvals ->
      (Jasmin.Wsize.wsize * Jasmin.CoreIdent.length) Jasmin.Syscall_t.syscall_t ->
      Jasmin.Prog.exprs -> domain -> domain Annotation.annotation

    (**
    Function to handle assign instruction
    *)
    val assign :
      Jasmin.Location.i_loc ->
      Jasmin.Prog.lval ->
      Jasmin.Expr.assgn_tag ->
      Jasmin.Prog.ty ->
      Jasmin.Prog.expr -> domain -> domain Annotation.annotation

    (**
    Function to handle opn instruction
    *)
    val opn :
      Jasmin.Location.i_loc ->
      Jasmin.Prog.lvals ->
      Jasmin.Expr.assgn_tag ->
      'asm Jasmin.Sopn.sopn ->
      Jasmin.Prog.exprs -> domain -> domain Annotation.annotation

    (**
    Function to handle assert instruction
    *)
    val assertion :
      Jasmin.Location.i_loc ->
      string ->
      Jasmin.Prog.expr ->
      domain -> domain Annotation.annotation

  end

(**
Signature of the ForwardAnalyser module.
*)
module type S =
  sig
    type domain

    (**
    Entrypoint for analysis.
      args :
      - [('info,'asm) Prog.func] (function to analyse)
      returns :d
      - [(domain Annotation.annotation, 'asm) Prog.func] (annotated function)
    *)
    val analyse_function :
      ('info, 'asm) Jasmin.Prog.func ->
      (domain Annotation.annotation, 'asm) Jasmin.Prog.func
end

(**
Functor used to create a module implementing forward analysis.

It takes a module implementing the [Logic] interface and returns a module implementing the [S] signature.

Each instruction is annotated with its IN domain and the OUT domain is passed to the next instruction.
Domain are updated using the functions provided by the [Logic] module.
Control flow is handled as follow :
- if bloc :
  * we assume the condition of the if bloc to produce two domains [d1] and [d2]
  * we analyse the first branch (then branch) with the domain [d1]
  * we analyse the second branch (else branch) with the domain [d2]
  * we merge the two domains to produce the final domain for the if bloc
- while bloc (b1, condition, b2) :
  * we analyse the first bloc [b1] with the input domain [d]
  * we loop and analyse the body of the while bloc (b2,b1,condition) until we reach a fixpoint
  * we return the corresponding domain
- for bloc :
  * we convert the for loop to a while loop using a proxy variable for the loop variable :
  [
    inline int i;
    for i = 0 to 10 {
      ...
    }
  ]

  becomes :

  [
    inline int i;
    inline int i_proxy = 0;
    while (i_proxy < 10) {
      i = i_proxy;
      ...
      i_proxy++;
    }
  ]
  * we analyse the while loop with the while loop logic
  * we forget the proxy variable introduced by the for loop
*)
module Make :functor (Logic : Logic) -> S with type domain = Logic.domain
