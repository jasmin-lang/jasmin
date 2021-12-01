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

Section Tunneling.

Context (fn : funname).

Definition Linstr_align := (MkLI xH Lalign).

Definition tunnel_chart (uf : LUF.unionfind) (c c' : linstr) :=
  match c, c' with
  | {| li_i := Llabel l |}, {| li_i := Llabel l' |} =>
      LUF.union uf l l'
  | {| li_i := Llabel l |}, {| li_i := Lgoto (fn',l') |} =>
      if fn == fn' then LUF.union uf l l' else uf
  | _, _ => uf
  end.

Definition tunnel_plan (uf : LUF.unionfind) := pairfoldl tunnel_chart uf Linstr_align.

Definition tunnel_bore (uf : LUF.unionfind) (c : linstr) :=
  match c with
    | MkLI ii li =>
      match li with
        | Lgoto (fn',l') => MkLI ii (if fn == fn' then Lgoto (fn', LUF.find uf l') else Lgoto (fn',l'))
        | Lcond pe l' => MkLI ii (Lcond pe (LUF.find uf l'))
        | _ => MkLI ii li
      end
  end.

Definition tunnel_partial (uf : LUF.unionfind) (lc : lcmd) :=
  map (tunnel_bore uf) lc.

Definition tunnel (lc : lcmd) :=
  let uf := tunnel_plan LUF.empty lc in
  tunnel_partial uf lc.

End Tunneling.

Section TunnelingSem.

  Context (fn : funname).

  Context (p : lprog).

  Definition labels_of_body fb :=
    filter 
      (fun li => match li with
               | Llabel _ => true
               | _ => false
               end)
      (map li_i fb).

  Definition goto_targets fb :=
    filter 
      (fun li => if li is Lgoto _ then true else false)
      (map li_i fb).

  Definition well_formed_body (fn' : funname) fb :=
    uniq (labels_of_body fb) &&
    all
      (fun li => 
         if li is Lgoto (fn',l) then 
            Llabel l \in (labels_of_body fb)
         else false)
      (goto_targets fb).
  
  Definition well_formed_lprog :=
    uniq (map fst (lp_funcs p))
    && all (fun func => well_formed_body func.1 func.2.(lfd_body)) p.(lp_funcs).

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

  Definition lfundef_tunnel_partial fd lc lc' :=
    setfb fd (tunnel_partial fn (tunnel_plan fn LUF.empty lc) lc').

  Definition setfuncs lf :=
    {| lp_rip := lp_rip p
     ; lp_rsp := lp_rsp p
     ; lp_globs := lp_globs p
     ; lp_funcs := lf |}.

  Definition lprog_tunnel :=
    match get_fundef (lp_funcs p) fn with
    | Some fd => setfuncs
                  (map
                    (fun f =>
                      (f.1,
                       if fn == f.1
                       then lfundef_tunnel_partial f.2 fd.(lfd_body) fd.(lfd_body)
                       else f.2))
                    p.(lp_funcs))
    | None => p
    end.

  Definition funnames := map (fun x => x.1) (lp_funcs p).

End TunnelingSem.



Section TunnelingCompiler.

  Definition tunnel_program p :=
    if well_formed_lprog p
    then ok (foldr lprog_tunnel p (funnames p))
    else Error (tunneling_error "not well-formed").

End TunnelingCompiler.
