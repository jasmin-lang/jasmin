(* -------------------------------------------------------------------- *)
require import AllCore List Bool IntDiv.
require export JModel_common JArray JWord_array JMemory JLeakage Jslh.


abbrev ptr_modulus = 2^32.

(* -------------------------------------------------------------------- *)
abbrev [-printing] ADD (x y : W32.t) : W32.t = x + y.
abbrev [-printing] ADDI = ADD.

abbrev [-printing] SUB (x y : W32.t) : W32.t = x - y.

op SLT (x y : W32.t) : W32.t = W32.of_int (if x \slt y then 1 else 0).
abbrev [-printing] SLTI = SLT.

op SLTU (x y : W32.t) : W32.t = W32.of_int (if x \ult y then 1 else 0).
abbrev [-printing] SLTIU = SLTU.

abbrev [-printing] AND = W32.andw.
abbrev [-printing] ANDI = AND.

abbrev [-printing] OR = W32.orw.
abbrev [-printing] ORI = OR.

abbrev [-printing] XOR (x y : W32.t) : W32.t = x +^ y.
abbrev [-printing] XORI = XOR.

abbrev [-printing] SLL = W32.(`<<`).
abbrev [-printing] SLLI = SLL.

abbrev [-printing] SRL = W32.(`>>`).
abbrev [-printing] SRLI = SRL.

abbrev [-printing] SRA = W32.(`|>>`).
abbrev [-printing] SRAI = SRA.

abbrev [-printing] MV (x : W32.t) = x.

abbrev [-printing] LA (x : W32.t) = x.

abbrev [-printing] LI (x : W32.t) = x.

abbrev [-printing] NOT = W32.invw.

abbrev [-printing] NEG (x : W32.t) = -x.

abbrev [-printing] LOAD_s8 (x : W8.t) = W32.of_int (W8.to_sint x).
abbrev [-printing] LOAD_s16 (x : W16.t) = W32.of_int (W16.to_sint x).
abbrev [-printing] LOAD_s32 (x : W32.t) = x.

abbrev [-printing] LOAD_u8 (x : W8.t) = W32.of_int (W8.to_uint x).
abbrev [-printing] LOAD_u16 (x : W16.t) = W32.of_int (W16.to_uint x).
abbrev [-printing] LOAD_u32 (x : W32.t) = x.

abbrev [-printing] STORE_8 (x : W32.t) = W8.of_int (W32.to_uint x).
abbrev [-printing] STORE_16 (x : W32.t) = W16.of_int (W32.to_uint x).
abbrev [-printing] STORE_32 (x : W32.t) = x.

abbrev [-printing] MUL (x y : W32.t) : W32.t = x * y.
abbrev [-printing] MULH = W32.wmulhs.

abbrev [-printing] MULHU = W32.mulhi.

op MULHSU (x y : W32.t) : W32.t = W32.of_int ((to_sint x * to_uint y) %/ W32.modulus).

abbrev [-printing] DIV (x y : W32.t) : W32.t = if y = W32.of_int(0) then W32.of_int(-1) else W32.(\sdiv) x y.
abbrev [-printing] DIVU (x y : W32.t) : W32.t = if y = W32.of_int(0) then W32.of_int(-1) else W32.(\udiv) x y.

abbrev [-printing] REM = W32.(\smod).
abbrev [-printing] REMU = W32.(\umod).
