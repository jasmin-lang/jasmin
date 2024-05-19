From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import ZArith.

Require Import Utf8.
Require Import expr compiler_util linear label.
Require Import seq_extra unionfind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Module Import E.

  Definition pass : string := "tunneling".

  Definition tunneling_error := pp_internal_error_s pass.

End E.


Section ASM_OP.

Context {pd : PointerData}.
Context `{asmop : asmOp}.

Section LprogSem.

  Definition labels_of_body fb :=
    pmap (λ li, if li_i li is Llabel _ lbl then Some lbl else None) fb.

  Definition goto_targets fb :=
    pmap (λ li, if li_i li is Lgoto lbl then Some lbl else None) fb.

  Definition setfb fd fb : lfundef :=
    LFundef
      fd.(lfd_info)
      fd.(lfd_align)
      fd.(lfd_tyin)
      fd.(lfd_arg)
      fb
      fd.(lfd_tyout)
      fd.(lfd_res)
      fd.(lfd_export)
      fd.(lfd_callee_saved)
      fd.(lfd_stk_max)
      fd.(lfd_frame_size)
      fd.(lfd_align_args)
  .

  Definition setfuncs p lf :=
    {| lp_rip := lp_rip p
     ; lp_rsp := lp_rsp p
     ; lp_globs := lp_globs p
     ; lp_glob_names := lp_glob_names p
     ; lp_funcs := lf |}.

End LprogSem.


Section Tunneling.

  Definition Linstr_align := (MkLI dummy_instr_info Lalign).

  Definition tunnel_chart fn uf c c' :=
    match c, c' with
    | {| li_i := Llabel InternalLabel l |}, {| li_i := Llabel InternalLabel l' |} =>
        LUF.union uf l l'
    | {| li_i := Llabel InternalLabel l |}, {| li_i := Lgoto (fn',l') |} =>
        if fn == fn' then LUF.union uf l l' else uf
    | _, _ => uf
    end.

  Definition tunnel_plan fn uf (lc : lcmd) :=
    pairfoldl (tunnel_chart fn) uf Linstr_align lc.

  Definition tunnel_bore fn uf c :=
    match c with
      | MkLI ii li =>
        match li with
          | Lgoto (fn',l') => MkLI ii (if fn == fn' then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
          | Lcond pe l' => MkLI ii (Lcond pe (LUF.find uf l'))
          | _ => MkLI ii li
        end
    end.

  Definition tunnel_head fn uf lc :=
    map (tunnel_bore fn uf) lc.

  Definition tunnel_engine fn (lc lc' : lcmd) : lcmd :=
    tunnel_head fn (tunnel_plan fn LUF.empty lc) lc'.

  Definition tunnel_lcmd fn lc :=
    tunnel_engine fn lc lc.

  Definition tunnel_lfundef fn fd :=
    setfb fd (tunnel_lcmd fn (lfd_body fd)).

  Definition tunnel_funcs :=
    map (fun f => (f.1, tunnel_lfundef f.1 f.2)).

  Definition tunnel_lprog p :=
    setfuncs p (tunnel_funcs (lp_funcs p)).

End Tunneling.


Section TunnelingWF.

  Definition well_formed_body (fn : funname) fb :=
    let lbls := labels_of_body fb in
    uniq lbls &&
    all
      (fun '(fn', l) => (fn != fn') || (l \in lbls))
      (goto_targets fb).

  Definition well_formed_funcs lf :=
    uniq (map fst lf)
    && all (fun func => well_formed_body func.1 func.2.(lfd_body)) lf.

  Definition well_formed_lprog p :=
    well_formed_funcs (lp_funcs p).

End TunnelingWF.


Section TunnelingCompiler.

  Definition tunnel_program p :=
    if well_formed_lprog p
    then ok (tunnel_lprog p)
    else Error (tunneling_error "not well-formed").

End TunnelingCompiler.

End ASM_OP.
