(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util compiler.
Require Import allocation inline_proof dead_calls_proof
               unrolling_proof constant_prop_proof dead_code_proof
               array_expansion remove_globals_proof stack_alloc_proof
               lowering_proof
               linear_proof
               psem_of_sem_proof.
Import Utf8.
Import x86_sem x86_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PROOF.

Variable cparams : compiler_params.
Variable stk : pointer.
(*Variable p p': prog.

Hypothesis unroll_ok : dead_code_prog (const_prop_prog (unroll_prog p).1).1 =
        ok (p', Fs).*)

Hypothesis print_progP : forall s p, cparams.(print_prog) s p = p.
Hypothesis print_linearP : forall p, cparams.(print_linear) p = p.

Definition sem_call_noleak p f mem va mem' vr :=
 exists l, sem_call p f mem va l mem' vr.

Lemma unroll1P (fn: funname) (p p':prog) mem va va' mem' vr lts:
  unroll1 p = ok (p', lts) ->
  sem_call_noleak p mem fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call_noleak p' mem fn va' mem' vr' 
 /\ List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll1=> Heq Hsem Hall.
  move: Heq. t_xrbindP=> -[p1 lt] Hdp [] <- /= hlt.
  rewrite /sem_call_noleak in Hsem. case: Hsem=> lf Hsem.
  have /= := (unroll_callP). move=> Hu.
  move: (Hu p {|
         p_globs := p_globs p;
         p_funcs := [seq (t.1, t.2.1)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]] |} [seq (t.1, t.2.2)
          | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]] stk). rewrite /unroll_prog /=.
  have heq :  ({|
   p_globs := p_globs p;
   p_funcs := [seq (t.1, t.2.1)
                 | t <- [seq (t.1, unroll_fun t.2)
                           | t <- p_funcs p]] |} =
   {|
   p_globs := p_globs p;
   p_funcs := [seq (t.1, t.2.1)
                 | t <- [seq (t.1, unroll_fun t.2)
                           | t <- p_funcs p]] |}). auto.
   have heq' : ({|
      p_globs := p_globs p;
      p_funcs := [seq (t.1, t.2.1)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] |},
     [seq (t.1, t.2.2)
        | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]]) =
     ({|
      p_globs := p_globs p;
      p_funcs := [seq (t.1, t.2.1)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] |},
     [seq (t.1, t.2.2)
        | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]]). auto.
  move=> {Hu} Hup. move: (Hup heq heq' fn mem mem' va vr lf Hsem). move=> {heq} {heq'} {Hup} Hup.
  have /= := const_prop_callP. move=> Hcp.
  move: (Hcp  {|
          p_globs := p_globs p;
          p_funcs := [seq (t.1, t.2.1)
                        | t <- [seq (t.1, unroll_fun t.2)
                                  | t <- 
                                p_funcs p]] |}  {|
     p_globs := p_globs
                  {|
                  p_globs := p_globs p;
                  p_funcs := [seq (t.1, t.2.1)
                                | t <- [
                              seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]] |};
     p_funcs := [seq (t.1, t.2.1)
                   | t <- [seq (t.1, const_prop_fun t.2)
                             | t <- p_funcs
                                      {|
                                      p_globs := p_globs p;
                                      p_funcs := [seq 
                                       (t.1, t.2.1)
                                        | t <- [seq 
                                       (t.1, 
                                       unroll_fun t.2)
                                        | t <- p_funcs p]] |}]] |}  [seq (t.1, t.2.2)
          | t <- [seq (t.1, const_prop_fun t.2)
                    | t <- [seq (t.1, t.2.1)
                              | t <- [seq 
                                      (t.1, 
                                      unroll_fun t.2)
                                        | t <- 
                                      p_funcs p]]]] stk). 
  have heq :  {|
     p_globs := p_globs p;
     p_funcs := [seq (t.1, t.2.1)
                   | t <- [seq (t.1, const_prop_fun t.2)
                             | t <- [seq 
                                     (t.1, t.2.1)
                                       | t <- [
                                     seq 
                                     (t.1, 
                                     unroll_fun t.2)
                                       | t <- 
                                     p_funcs p]]]] |} =
     {|
     p_globs := p_globs p;
     p_funcs := [seq (t.1, t.2.1)
                   | t <- [seq (t.1, const_prop_fun t.2)
                             | t <- [seq 
                                     (t.1, t.2.1)
                                       | t <- [
                                     seq 
                                     (t.1, 
                                     unroll_fun t.2)
                                       | t <- 
                                     p_funcs p]]]] |}. auto.
  have heq' :  (({|
    p_globs := p_globs p;
    p_funcs := [seq (t.1, t.2.1)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]] |},
   [seq (t.1, t.2.2)
      | t <- [seq (t.1, const_prop_fun t.2)
                | t <- [seq (t.1, t.2.1)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]]]]) =
   ({|
    p_globs := p_globs p;
    p_funcs := [seq (t.1, t.2.1)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]] |},
   [seq (t.1, t.2.2)
      | t <- [seq (t.1, const_prop_fun t.2)
                | t <- [seq (t.1, t.2.1)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]]]])). auto. move=> {Hcp} Hcp. move: (Hcp heq heq').
  move=> {Hcp} Hcp {heq} {heq'}.
  move:(Hcp fn mem mem' va va' vr (lf.1,
          leak_Is
            (leak_I
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, unroll_fun t.2)
                               | t <- p_funcs p]])) stk
            (leak_Fun
               [seq (t.1, t.2.2)
                  | t <- [seq (t.1, unroll_fun t.2)
                            | t <- p_funcs p]] lf.1) lf.2) Hup Hall). move=> {Hcp} [vr'] [Hcp] Hr.
  have:= (dead_code_callP stk Hdp). rewrite /const_prop_prog /unroll_prog /=. move=> Hdp'.
  move: (Hdp' fn mem mem' va' vr' ((lf.1,
           leak_Is
             (leak_I
                (leak_Fun
                   [seq (t.1, t.2.2)
                      | t <- [seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]])) stk
             (leak_Fun
                [seq (t.1, t.2.2)
                   | t <- [seq (t.1, unroll_fun t.2)
                             | t <- p_funcs p]] lf.1) lf.2).1,
          leak_Is
            (leak_I
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, const_prop_fun t.2)
                               | t <- [seq 
                                       (t.1, t.2.1)
                                        | t <- [
                                       seq 
                                       (t.1, 
                                       unroll_fun t.2)
                                        | t <- 
                                       p_funcs p]]]])) stk
            (leak_Fun
               [seq (t.1, t.2.2)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]]
               (lf.1,
               leak_Is
                 (leak_I
                    (leak_Fun
                       [seq (t.1, t.2.2)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]])) stk
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]] lf.1) lf.2).1)
            (lf.1,
            leak_Is
              (leak_I
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]])) stk
              (leak_Fun
                 [seq (t.1, t.2.2)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] lf.1) lf.2).2) Hcp). move=> {Hdp'} H.
  exists vr'. split=> //.
  rewrite /sem_call_noleak. exists (((lf.1,
          leak_Is
            (leak_I
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, unroll_fun t.2)
                               | t <- p_funcs p]])) stk
            (leak_Fun
               [seq (t.1, t.2.2)
                  | t <- [seq (t.1, unroll_fun t.2)
                            | t <- p_funcs p]] lf.1) lf.2).1,
         leak_Is
           (leak_I
              (leak_Fun
                 [seq (t.1, t.2.2)
                    | t <- [seq (t.1, const_prop_fun t.2)
                              | t <- [seq 
                                      (t.1, t.2.1)
                                        | t <- [
                                      seq 
                                      (t.1, 
                                      unroll_fun t.2)
                                        | t <- 
                                      p_funcs p]]]])) stk
           (leak_Fun
              [seq (t.1, t.2.2)
                 | t <- [seq (t.1, const_prop_fun t.2)
                           | t <- [seq (t.1, t.2.1)
                                     | t <- [
                                   seq (t.1, unroll_fun t.2)
                                     | t <- 
                                   p_funcs p]]]]
              (lf.1,
              leak_Is
                (leak_I
                   (leak_Fun
                      [seq (t.1, t.2.2)
                         | t <- [seq (t.1, unroll_fun t.2)
                                   | t <- 
                                 p_funcs p]])) stk
                (leak_Fun
                   [seq (t.1, t.2.2)
                      | t <- [seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]] lf.1) lf.2).1)
           (lf.1,
           leak_Is
             (leak_I
                (leak_Fun
                   [seq (t.1, t.2.2)
                      | t <- [seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]])) stk
             (leak_Fun
                [seq (t.1, t.2.2)
                   | t <- [seq (t.1, unroll_fun t.2)
                             | t <- p_funcs p]] lf.1) lf.2).2).1,
        leak_Is (leak_I (leak_Fun lt)) stk
          (leak_Fun lt
             ((lf.1,
              leak_Is
                (leak_I
                   (leak_Fun
                      [seq (t.1, t.2.2)
                         | t <- [seq (t.1, unroll_fun t.2)
                                   | t <- 
                                 p_funcs p]])) stk
                (leak_Fun
                   [seq (t.1, t.2.2)
                      | t <- [seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]] lf.1) lf.2).1,
             leak_Is
               (leak_I
                  (leak_Fun
                     [seq (t.1, t.2.2)
                        | t <- [seq (t.1, const_prop_fun t.2)
                                  | t <- [
                                seq (t.1, t.2.1)
                                  | t <- [
                                seq (t.1, unroll_fun t.2)
                                  | t <- 
                                p_funcs p]]]])) stk
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, const_prop_fun t.2)
                               | t <- [seq 
                                       (t.1, t.2.1)
                                        | t <- [
                                       seq 
                                       (t.1, 
                                       unroll_fun t.2)
                                        | t <- 
                                       p_funcs p]]]]
                  (lf.1,
                  leak_Is
                    (leak_I
                       (leak_Fun
                          [seq (t.1, t.2.2)
                             | t <- [seq 
                                     (t.1, 
                                     unroll_fun t.2)
                                       | t <- 
                                     p_funcs p]])) stk
                    (leak_Fun
                       [seq (t.1, t.2.2)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]] lf.1) lf.2).1)
               (lf.1,
               leak_Is
                 (leak_I
                    (leak_Fun
                       [seq (t.1, t.2.2)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]])) stk
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]] lf.1) lf.2).2).1)
          ((lf.1,
           leak_Is
             (leak_I
                (leak_Fun
                   [seq (t.1, t.2.2)
                      | t <- [seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]])) stk
             (leak_Fun
                [seq (t.1, t.2.2)
                   | t <- [seq (t.1, unroll_fun t.2)
                             | t <- p_funcs p]] lf.1) lf.2).1,
          leak_Is
            (leak_I
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, const_prop_fun t.2)
                               | t <- [seq 
                                       (t.1, t.2.1)
                                        | t <- [
                                       seq 
                                       (t.1, 
                                       unroll_fun t.2)
                                        | t <- 
                                       p_funcs p]]]])) stk
            (leak_Fun
               [seq (t.1, t.2.2)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]]
               (lf.1,
               leak_Is
                 (leak_I
                    (leak_Fun
                       [seq (t.1, t.2.2)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]])) stk
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]] lf.1) lf.2).1)
            (lf.1,
            leak_Is
              (leak_I
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]])) stk
              (leak_Fun
                 [seq (t.1, t.2.2)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] lf.1) lf.2).2).2). auto.
Qed.

Variable Fs: seq (funname * leak_c_tr).
Lemma unroll1P' (fn: funname) (p p':prog) mem va va' mem' vr (lf: leak_fun) lts:
  unroll1 p = ok (p', lts) ->
  sem_call p mem fn va lf mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' mem fn va' (leak_compile Fs stk (get_seq_seq_leak_c_tr lts) lf) mem' vr' 
 /\ List.Forall2 value_uincl vr vr'.
Proof.
  rewrite /unroll1=> Heq Hsem Hall.
  move: Heq. t_xrbindP. move=> -[yp ltp] Hdp [] <- hlts.
  have /= := (unroll_callP). move=> Hu. move: (Hu p {|
         p_globs := p_globs p;
         p_funcs := [seq (t.1, t.2.1)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]] |} [seq (t.1, t.2.2)
          | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]] stk). rewrite /unroll_prog /=.
  have heq :  ({|
   p_globs := p_globs p;
   p_funcs := [seq (t.1, t.2.1)
                 | t <- [seq (t.1, unroll_fun t.2)
                           | t <- p_funcs p]] |} =
   {|
   p_globs := p_globs p;
   p_funcs := [seq (t.1, t.2.1)
                 | t <- [seq (t.1, unroll_fun t.2)
                           | t <- p_funcs p]] |}). auto.
   have heq' : ({|
      p_globs := p_globs p;
      p_funcs := [seq (t.1, t.2.1)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] |},
     [seq (t.1, t.2.2)
        | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]]) =
     ({|
      p_globs := p_globs p;
      p_funcs := [seq (t.1, t.2.1)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] |},
     [seq (t.1, t.2.2)
        | t <- [seq (t.1, unroll_fun t.2) | t <- p_funcs p]]). auto.
  move=> {Hu} Hup. move: (Hup heq heq' fn mem mem' va vr lf Hsem). move=> {heq} {heq'} {Hup} Hup.
  have /= := const_prop_callP. move=> Hcp.
  move: (Hcp  {|
          p_globs := p_globs p;
          p_funcs := [seq (t.1, t.2.1)
                        | t <- [seq (t.1, unroll_fun t.2)
                                  | t <- 
                                p_funcs p]] |}  {|
     p_globs := p_globs
                  {|
                  p_globs := p_globs p;
                  p_funcs := [seq (t.1, t.2.1)
                                | t <- [
                              seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]] |};
     p_funcs := [seq (t.1, t.2.1)
                   | t <- [seq (t.1, const_prop_fun t.2)
                             | t <- p_funcs
                                      {|
                                      p_globs := p_globs p;
                                      p_funcs := [seq 
                                       (t.1, t.2.1)
                                        | t <- [seq 
                                       (t.1, 
                                       unroll_fun t.2)
                                        | t <- p_funcs p]] |}]] |}  [seq (t.1, t.2.2)
          | t <- [seq (t.1, const_prop_fun t.2)
                    | t <- [seq (t.1, t.2.1)
                              | t <- [seq 
                                      (t.1, 
                                      unroll_fun t.2)
                                        | t <- 
                                      p_funcs p]]]] stk). 
  have heq :  {|
     p_globs := p_globs p;
     p_funcs := [seq (t.1, t.2.1)
                   | t <- [seq (t.1, const_prop_fun t.2)
                             | t <- [seq 
                                     (t.1, t.2.1)
                                       | t <- [
                                     seq 
                                     (t.1, 
                                     unroll_fun t.2)
                                       | t <- 
                                     p_funcs p]]]] |} =
     {|
     p_globs := p_globs p;
     p_funcs := [seq (t.1, t.2.1)
                   | t <- [seq (t.1, const_prop_fun t.2)
                             | t <- [seq 
                                     (t.1, t.2.1)
                                       | t <- [
                                     seq 
                                     (t.1, 
                                     unroll_fun t.2)
                                       | t <- 
                                     p_funcs p]]]] |}. auto.
  have heq' :  (({|
    p_globs := p_globs p;
    p_funcs := [seq (t.1, t.2.1)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]] |},
   [seq (t.1, t.2.2)
      | t <- [seq (t.1, const_prop_fun t.2)
                | t <- [seq (t.1, t.2.1)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]]]]) =
   ({|
    p_globs := p_globs p;
    p_funcs := [seq (t.1, t.2.1)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]] |},
   [seq (t.1, t.2.2)
      | t <- [seq (t.1, const_prop_fun t.2)
                | t <- [seq (t.1, t.2.1)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]]]])). auto. move=> {Hcp} Hcp. move: (Hcp heq heq').
  move=> {Hcp} Hcp {heq} {heq'}.
  move:(Hcp fn mem mem' va va' vr (lf.1,
          leak_Is
            (leak_I
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, unroll_fun t.2)
                               | t <- p_funcs p]])) stk
            (leak_Fun
               [seq (t.1, t.2.2)
                  | t <- [seq (t.1, unroll_fun t.2)
                            | t <- p_funcs p]] lf.1) lf.2) Hup Hall). move=> {Hcp} [vr'] [Hcp] Hr.
  exists vr'. rewrite /=. split=> //. 
  have:= (dead_code_callP stk Hdp). rewrite /const_prop_prog /unroll_prog /=. move=> Hdp'.
  move: (Hdp' fn mem mem' va' vr' ((lf.1,
           leak_Is
             (leak_I
                (leak_Fun
                   [seq (t.1, t.2.2)
                      | t <- [seq (t.1, unroll_fun t.2)
                                | t <- p_funcs p]])) stk
             (leak_Fun
                [seq (t.1, t.2.2)
                   | t <- [seq (t.1, unroll_fun t.2)
                             | t <- p_funcs p]] lf.1) lf.2).1,
          leak_Is
            (leak_I
               (leak_Fun
                  [seq (t.1, t.2.2)
                     | t <- [seq (t.1, const_prop_fun t.2)
                               | t <- [seq 
                                       (t.1, t.2.1)
                                        | t <- [
                                       seq 
                                       (t.1, 
                                       unroll_fun t.2)
                                        | t <- 
                                       p_funcs p]]]])) stk
            (leak_Fun
               [seq (t.1, t.2.2)
                  | t <- [seq (t.1, const_prop_fun t.2)
                            | t <- [seq 
                                    (t.1, t.2.1)
                                      | t <- [
                                    seq 
                                    (t.1, unroll_fun t.2)
                                      | t <- 
                                    p_funcs p]]]]
               (lf.1,
               leak_Is
                 (leak_I
                    (leak_Fun
                       [seq (t.1, t.2.2)
                          | t <- [seq (t.1, unroll_fun t.2)
                                    | t <- 
                                  p_funcs p]])) stk
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]] lf.1) lf.2).1)
            (lf.1,
            leak_Is
              (leak_I
                 (leak_Fun
                    [seq (t.1, t.2.2)
                       | t <- [seq (t.1, unroll_fun t.2)
                                 | t <- 
                               p_funcs p]])) stk
              (leak_Fun
                 [seq (t.1, t.2.2)
                    | t <- [seq (t.1, unroll_fun t.2)
                              | t <- p_funcs p]] lf.1) lf.2).2) Hcp). move=> {Hdp'} H.
      rewrite -hlts /=.
Admitted.

Lemma unrollP (fn: funname) (p p': prog) mem va va' mem' vr lts:
  unroll Loop.nb p = ok (p', lts) ->
  sem_call_noleak p mem  fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call_noleak p' mem fn va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  elim: Loop.nb p va va' vr => /= [p //|n Hn] p va va' vr.
  t_xrbindP=> -[pz lt] Hup.
  case: ifP=> [_ [] ->|_ /= Hu Hs Hall].
  + move=> Hlts. rewrite /sem_call_noleak. move=> [] lf. move=> /sem_call_uincl h/h{h}.
    move=> [vr'] [Hs] Hall. exists vr'. split=> //. by exists lf. 
  have [vr' [hsem1 hall1]]:= unroll1P Hup Hs Hall.
  have [vr'' [hsem2 hall2]]:= Hn _ _ _ _ Hu hsem1 (List_Forall2_refl _ value_uincl_refl).
  exists vr'';split => //.
  by apply: Forall2_trans value_uincl_trans hall1 hall2.
Qed.

(*Lemma unrollP (fn: funname) (p p': prog) mem va va' mem' vr:
  unroll Loop.nb p = ok p' ->
  sem_call p mem  fn va mem' vr ->
  List.Forall2 value_uincl va va' ->
  exists vr', sem_call p' mem fn va' mem' vr' /\ List.Forall2 value_uincl vr vr'.
Proof.
  elim: Loop.nb p va va' vr => /= [p //|n Hn] p va va' vr.
  apply: rbindP=> z Hz.
  case: ifP=> [_ [] ->|_ Hu Hs Hall].
  + by move=> /sem_call_uincl h/h{h}.
  have [vr' [hsem1 hall1]]:= unroll1P Hz Hs Hall.
  have [vr'' [hsem2 hall2]]:= Hn _ _ _ _ Hu hsem1 (List_Forall2_refl _ value_uincl_refl).
  exists vr'';split => //.
  by apply: Forall2_trans value_uincl_trans hall1 hall2.
Qed.*)

Opaque Loop.nb.

Let Ki : ∀ vr (P Q: _ → Prop),
        (∀ vr', P vr' → Q vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr')
    := λ vr P Q h x, let 'ex_intro vr' (conj u p) := x in ex_intro _ vr' (conj u (h vr' p)).

Let Kj : ∀ m vr (P Q: _ → _ → Prop),
        (∀ m' vr', P m' vr' → Q m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ P m' vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ Q m' vr')
    := λ m vr P Q h x,
      let 'ex_intro m' (ex_intro vr' (conj u (conj v p))) := x in
      ex_intro _ m' (ex_intro _ vr' (conj u (conj v (h m' vr' p)))).

Let Km : ∀ m vr (P: _ → Prop) (Q: _ → _ → Prop),
        (∀ vr, P vr → ∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ Q m' vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ m' vr', List.Forall2 value_uincl vr vr' ∧ eq_mem m m' ∧ Q m' vr')
  := λ m vr P Q h x,
      let 'ex_intro vr' (conj u p) := x in
      let 'ex_intro m' (ex_intro vr'' (conj u' q)) := h vr' p in
      ex_intro _ m' (ex_intro _ vr'' (conj (Forall2_trans value_uincl_trans u u') q)).

Let K : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro vr1 (conj u p) := x in
      let 'ex_intro vr2 (conj v q) := h _ p in
      ex_intro _ vr2 (conj (Forall2_trans value_uincl_trans u v) q).

Let K' : ∀ vr (P Q: _ → Prop),
        (∀ vr, P vr → ∃ vr', Q vr' ∧ List.Forall2 value_uincl vr vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ P vr') →
        (∃ vr', List.Forall2 value_uincl vr vr' ∧ Q vr')
  :=
      λ vr P Q h x,
      let 'ex_intro vr1 (conj u p) := x in
      let 'ex_intro vr2 (conj q v) := h _ p in
      ex_intro _ vr2 (conj (Forall2_trans value_uincl_trans u v) q).

Lemma compile_progP entries (p: prog) (gd:glob_decls) (lp: lprog) mem fn va mem' vr lts:
  compile_prog cparams entries p = cfok (gd, lp, lts) ->
  fn \in entries ->
  sem.sem_call_noleak p mem fn va mem' vr ->
  (forall f, get_fundef lp fn = Some f ->
     exists p, alloc_stack mem (lfd_stk_size f) = ok p) ->
  ∃ mem2' vr',
    List.Forall2 value_uincl vr vr' ∧
    eq_mem mem' mem2' ∧
    lsem_fd_noleak lp gd mem fn va mem2' vr'.
Proof.
  rewrite /compile_prog.
  apply: rbindP=> -[p0 l0] Hp0. rewrite !print_progP.
  apply: rbindP=> -pca Hpca. rewrite !print_progP.
  apply: rbindP=> -[p1 lp1] Hp1. rewrite !print_progP.
  apply: rbindP=> ltc -[] /= Hv.
  apply: rbindP=> -[pv lpv] Hpv. rewrite !print_progP.
  apply: rbindP=> lps -[] Hps.
  apply: rbindP=> -[ps' lps'] Hps'. rewrite !print_progP.
  apply: rbindP => lr -[] He.
  apply: rbindP => -[pg lg] Hpg. rewrite !print_progP.
  case Hlower: fvars_correct=> //.
  apply: rbindP=> lr' -[] He'.
  apply: rbindP=> -[pd ld] Hpd. rewrite !print_progP.
  apply: rbindP => -[pstk lpstk] Hpstk.
  apply: rbindP=> -[pl l] Hpl [] <- <- hlts. rewrite !print_linearP.
  move=> Hin Hcall Halloc.
  have Haok : alloc_ok pstk fn mem.
  + rewrite /alloc_ok=> fd Hfd.
    move: (get_map_cfprog_leak Hpl Hfd). move=> [f'] [lt] [Hf'1] Hf'2 Hl. 
    apply: rbindP Hf'1=> [fn' Hfn'] [] Hf'.
    have := Halloc _ Hf'2.
    by rewrite -Hf' /=.
  have va_refl := List_Forall2_refl va value_uincl_refl. rewrite /lsem_fd_noleak.
  rewrite /sem.sem_call_noleak in Hcall. case: Hcall=> -[fn' lf] Hcall.
  apply: Kj. move=> m' vr' H. eexists. have /= := (linear_fdP stk Hpl). move=> Hl.
  move: (Hl (p_globs pd) fn mem va m' vr' lf). move=> {Hl} Hl. move: H. apply Hl.
  apply: Km. move=> vr' Hvr'. have /= := (stack_alloc_proof.alloc_progP Hpstk _ Haok).
  move=> Hc. move: (Hc va lf mem' vr'). 
  (*apply: Ki; first by move => vr'; exact: (dead_code_callP Hpd).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocReg.alloc_callP He'); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (lower_callP _ _ _ Hlower).
  apply: Ki; first by move => vr';apply: (RGP.remove_globP Hpg).
  apply: K'; first by move => vr' Hvr'; apply: (CheckExpansion.alloc_callP He); exact: Hvr'.
  apply: K'; first by move => vr' Hvr'; apply: (remove_init_fdP va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callP Hps').
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocReg.alloc_callP Hps); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_code_callP Hpv).
  apply: K'; first by move => vr' Hvr'; apply: (CheckAllocReg.alloc_callP Hv); exact: Hvr'.
  apply: K'; first by move => vr' Hvr'; apply: (const_prop_callP _ va_refl); exact: Hvr'.
  apply: K'; first by move => vr' Hvr'; apply: (unrollP Hp1 _ va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: (dead_calls_err_seqP Hpca).
  apply: K'; first by move => vr' Hvr'; apply: (inline_call_errP Hp0 va_refl); exact: Hvr'.
  apply: Ki; first by move => vr'; exact: psem_call.
  exists vr; split => //.
  exact: (List_Forall2_refl _ value_uincl_refl).*)
  Admitted.


Lemma compile_prog_to_x86P entries (p: prog) (gd: glob_decls) (xp: xprog) m1 fn va m2 vr lts:
  compile_prog_to_x86 cparams entries p = cfok (gd,xp, lts) →
  fn \in entries →
  sem.sem_call_noleak p m1 fn va m2 vr →
  (∀ f, get_fundef xp fn = Some f →
     ∃ p, alloc_stack m1 (xfd_stk_size f) = ok p) →
  ∃ fd va',
    get_fundef (p_funcs p) fn = Some fd ∧
    mapM2 ErrType truncate_val (f_tyin fd) va = ok va' ∧
  ∃ fd', get_fundef xp fn = Some fd' ∧
  ∀ st1,
    List.Forall2 value_uincl va' (get_arg_values st1 fd'.(xfd_arg)) →
    st1.(xmem) = m1 →
  ∃ st2,
    x86sem_fd_noleak xp gd fn st1 st2 ∧
    List.Forall2 value_uincl vr (get_arg_values st2 fd'.(xfd_res)) ∧
    eq_mem m2 st2.(xmem).
Proof.
apply: rbindP=> -[[gd1 lp] ltp] hlp; t_xrbindP => /= _ /assertP /allP ok_sig xp' hxp ?? hlt hfn hsem hsafe;subst.
have hlsem := compile_progP hlp hfn hsem.
case: hlsem.
- move => fd hfd.
  have [xfd [hxfd]] := get_map_cfprog hxp hfd.
  by move => /hsafe; rewrite (assemble_fd_stk_size hxfd).
move/ok_sig: hfn.
rewrite /sem.sem_call_noleak in hsem. case: hsem=> lf hsem.
case: hsem => {m1 m2 hsafe fn va vr} m1 m2 fn fd va va' st1 vm2 vr vr1 lc ok_fd ok_va hm1 hm2 hm3 hm4 hsig m2'.
move=> [vr'] [ok_vr'] [hm2' hlsem].
exists fd, va.
split=> //. split=> //. rewrite /lsem_fd_noleak in hlsem. case: hlsem=> -[fn' lf'] hlsem.
case: (assemble_fdP hxp hlsem) => fd' [va1] [ok_fd'] [ok_va1] [xd] [ok_xd h].
move: ok_va1.
have -> : lfd_tyin fd' = f_tyin fd.
- by move: hsig; rewrite /check_signature ok_fd' ok_fd => /eqP [].
rewrite ok_va => - [?]; subst va1.
exists xd; split; first exact: ok_xd.
move => st hva hm1'.
have [st2 [hxsem [hvr' hm2'']]] := h st hva hm1'.
exists st2.
split=> //. rewrite /x86sem_fd_noleak. exists [seq leak_i_asm i | i <- lf']. exact: hxsem.
split=> //. 
exact: (Forall2_trans value_uincl_trans ok_vr' hvr').
by rewrite hm2''.
Qed.

End PROOF.
