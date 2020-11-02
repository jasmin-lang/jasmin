 

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith.
Require Import Utf8.
Import Relations.

Require Import expr compiler_util x86_variables linear.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

(*Even when importing*)
Import Coq.PArith.BinPosDef.

Section WEIRDUNIONFIND.

  Definition WeirdUnionFind := seq (label * label).

  Definition MakeSet (l : label) (uf : WeirdUnionFind) :=
    if List.existsb (fun pl => pl.1 == l) uf
    then uf
    else (l,l) :: uf.

  Check (fun x => (x.1 = x.2)).
  
  Definition Find (l : label) (uf : WeirdUnionFind) :=
    match (List.find (fun x => x.1 == l) uf) with
      | Some pl => pl.2
      | None => l
    end.

  (*The only important thing about this UnionFind is that when using Union x y the representative of y stays the same.*)
  Definition Union (lx : label) (ly : label) (uf : WeirdUnionFind) :=
    let fx := Find lx uf in
    let fy := Find ly uf in
    map (fun pl => if pl.2 == fx then (pl.1,fy) else pl) uf.

End WEIRDUNIONFIND.

Section TUNNELING.

  Context (fn : funname).

  Definition tunnel_Lgoto (lc : lcmd) (uf : WeirdUnionFind) :=
    let uf_Lgoto uf' c :=
      match c with
        | MkLI l li =>
          match li with
            | Lgoto (fn',l') => if fn == fn' then uf' else Union l l' (MakeSet l (MakeSet l' uf'))
            | _ => uf'
          end
      end
    in
    List.fold_left uf_Lgoto lc uf.

  Definition tunnel (lc : lcmd) :=
    let uf := tunnel_Lgoto lc [::] in
    let bore c :=
      match c with
        | MkLI l li =>
          (l,
          match li with
            | Lgoto (fn',l') => if fn == fn' then Lgoto (fn', Find l' uf) else Lgoto (fn',l')
            | Lcond pe l' => Lcond pe (Find l' uf)
            (*Any shortcut like that?*)
            (*| _ => _*)
            | _ => Lgoto (fn,l)
          end)
      end
    in
    map bore lc.

End TUNNELING.
