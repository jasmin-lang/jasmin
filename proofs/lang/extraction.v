Require Import var compiler.

Require ExtrOcamlBasic.
Require ExtrOcamlString.

Extraction Inline ssrbool.is_left.
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.

Cd  "lang/ocaml".

Extraction Blacklist String List Nat Utils Var Array.

Separate Extraction utils expr sem x86_instr_decl compiler.

Cd  "../..".
