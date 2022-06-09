Require Import var compiler.
Require x86_params x86_sem.

Require ExtrOcamlBasic.
Require ExtrOcamlString.

Extraction Inline ssrbool.is_left.
Extraction Inline ssrbool.predT ssrbool.pred_of_argType.
Extraction Inline ssrbool.idP.

Extraction Inline utils.assert.
Extraction Inline utils.Result.bind.
Extraction Inline Datatypes.implb.

Extract Constant strings.ascii_beq => "Char.equal".
Extract Constant strings.ascii_cmp => "(fun x y -> let c = Char.compare x y in if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt else Datatypes.Gt)".

Cd  "lang/ocaml".

Extraction Blacklist String List Nat Utils Var Array.

Separate Extraction utils sopn expr sem x86_decl x86_sem.x86_prog x86_instr_decl x86_extra x86_params compiler.

Cd  "../..".
