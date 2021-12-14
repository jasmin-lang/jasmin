From mathcomp Require Import all_ssreflect.
Require Import ZArith.

Require Import Utf8.
Require Import expr compiler_util linear.
Require Import tunneling_misc unionfind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Module Import E.

  Definition pass : string := "tunneling".

  Definition tunneling_error := pp_internal_error_s pass.

End E.


Section LprogSem.

  Definition funnames p := map fst (lp_funcs p).

  Definition labels_of_body fb :=
    filter 
      (fun li => match li with
               | Llabel _ => true
               | _ => false
               end)
      (map li_i fb).

  Definition goto_targets fb :=
    filter (fun li => if li is Lgoto _ then true else false) (map li_i fb).

  Definition setfb fd fb:=
    LFundef
      fd.(lfd_info)
      fd.(lfd_align)
      fd.(lfd_tyin)
      fd.(lfd_arg)
      fb
      fd.(lfd_tyout)
      fd.(lfd_res)
      fd.(lfd_export).

  Definition setfunc lf (fn : funname) (fd : lfundef) :=
    map (fun f => (f.1, if fn == f.1 then fd else f.2)) lf.

  Definition setfuncs p lf :=
    {| lp_rip := lp_rip p
     ; lp_rsp := lp_rsp p
     ; lp_globs := lp_globs p
     ; lp_funcs := lf |}.

End LprogSem.


Section Tunneling.

  Context (fn : funname).

  Definition Linstr_align := (MkLI xH Lalign).

  Definition tunnel_chart uf c c' :=
    match c, c' with
    | {| li_i := Llabel l |}, {| li_i := Llabel l' |} =>
        LUF.union uf l l'
    | {| li_i := Llabel l |}, {| li_i := Lgoto (fn',l') |} =>
        if fn == fn' then LUF.union uf l l' else uf
    | _, _ => uf
    end.

  Definition tunnel_plan uf (lc : lcmd) :=
    pairfoldl tunnel_chart uf Linstr_align lc.

  Definition tunnel_bore uf c :=
    match c with
      | MkLI ii li =>
        match li with
          | Lgoto (fn',l') => MkLI ii (if fn == fn' then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
          | Lcond pe l' => MkLI ii (Lcond pe (LUF.find uf l'))
          | _ => MkLI ii li
        end
    end.

  Definition tunnel_uf uf (lc : lcmd) : lcmd :=
    map (tunnel_bore uf) lc.

  Definition tunnel_partial lc lc' :=
    tunnel_uf (tunnel_plan LUF.empty lc) lc'.

  Definition lfundef_tunnel_partial fd lc lc' :=
    setfb fd (tunnel_partial lc lc').

  Definition funcs_tunnel_partial lf fd lc lc' :=
    setfunc lf fn (lfundef_tunnel_partial fd lc lc').

  Definition lprog_tunnel_partial p lf fd lc lc' :=
    setfuncs p (funcs_tunnel_partial lf fd lc lc').

  Definition lprog_tunnel p :=
    match get_fundef (lp_funcs p) fn with
    | Some fd => lprog_tunnel_partial p (lp_funcs p) fd (lfd_body fd) (lfd_body fd)
    | None => p
    end.

End Tunneling.


Section TunnelingSem.

  Definition well_formed_body (fn : funname) fb :=
    uniq (labels_of_body fb) &&
    all
      (fun li => 
         if li is Lgoto (fn',l) then 
            (fn == fn') && (Llabel l \in (labels_of_body fb))
         else false)
      (goto_targets fb).
  
  Definition well_formed_lprog p :=
    uniq (map fst (lp_funcs p))
    && all (fun func => well_formed_body func.1 func.2.(lfd_body)) p.(lp_funcs).

End TunnelingSem.


Section TunnelingCompiler.

  Definition tunnel_program p :=
    if well_formed_lprog p
    then ok (foldr lprog_tunnel p (funnames p))
    else Error (tunneling_error "not well-formed").

End TunnelingCompiler.
