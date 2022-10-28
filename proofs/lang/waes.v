(* ** AES-NI *)
(* From eclib/AES.ec *)

(* ** Imports and settings *)

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ word.
Require Import word.
Require Import Psatz ZArith utils.
Import Utf8.
Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ssrnat.

Local Open Scope Z_scope.

(* -------------------------------------------------------------- *)

Definition Sbox (v1 : u8) : u8 :=
  match toword v1 with
  | 0 => wrepr U8 99    | 1 => wrepr U8 124   | 2 => wrepr U8 119   | 3 => wrepr U8 123   | 4 => wrepr U8 242
  | 5 => wrepr U8 107   | 6 => wrepr U8 111   | 7 => wrepr U8 197   | 8 => wrepr U8 48    | 9 => wrepr U8 1
  | 10 => wrepr U8 103  | 11 => wrepr U8 43   | 12 => wrepr U8 254  | 13 => wrepr U8 215  | 14 => wrepr U8 171
  | 15 => wrepr U8 118  | 16 => wrepr U8 202  | 17 => wrepr U8 130  | 18 => wrepr U8 201  | 19 => wrepr U8 125
  | 20 => wrepr U8 250  | 21 => wrepr U8 89   | 22 => wrepr U8 71   | 23 => wrepr U8 240  | 24 => wrepr U8 173
  | 25 => wrepr U8 212  | 26 => wrepr U8 162  | 27 => wrepr U8 175  | 28 => wrepr U8 156  | 29 => wrepr U8 164
  | 30 => wrepr U8 114  | 31 => wrepr U8 192  | 32 => wrepr U8 183  | 33 => wrepr U8 253  | 34 => wrepr U8 147
  | 35 => wrepr U8 38   | 36 => wrepr U8 54   | 37 => wrepr U8 63   | 38 => wrepr U8 247  | 39 => wrepr U8 204
  | 40 => wrepr U8 52   | 41 => wrepr U8 165  | 42 => wrepr U8 229  | 43 => wrepr U8 241  | 44 => wrepr U8 113
  | 45 => wrepr U8 216  | 46 => wrepr U8 49   | 47 => wrepr U8 21   | 48 => wrepr U8 4    | 49 => wrepr U8 199
  | 50 => wrepr U8 35   | 51 => wrepr U8 195  | 52 => wrepr U8 24   | 53 => wrepr U8 150  | 54 => wrepr U8 5
  | 55 => wrepr U8 154  | 56 => wrepr U8 7    | 57 => wrepr U8 18   | 58 => wrepr U8 128  | 59 => wrepr U8 226
  | 60 => wrepr U8 235  | 61 => wrepr U8 39   | 62 => wrepr U8 178  | 63 => wrepr U8 117  | 64 => wrepr U8 9
  | 65 => wrepr U8 131  | 66 => wrepr U8 44   | 67 => wrepr U8 26   | 68 => wrepr U8 27   | 69 => wrepr U8 110
  | 70 => wrepr U8 90   | 71 => wrepr U8 160  | 72 => wrepr U8 82   | 73 => wrepr U8 59   | 74 => wrepr U8 214
  | 75 => wrepr U8 179  | 76 => wrepr U8 41   | 77 => wrepr U8 227  | 78 => wrepr U8 47   | 79 => wrepr U8 132
  | 80 => wrepr U8 83   | 81 => wrepr U8 209  | 82 => wrepr U8 0    | 83 => wrepr U8 237  | 84 => wrepr U8 32
  | 85 => wrepr U8 252  | 86 => wrepr U8 177  | 87 => wrepr U8 91   | 88 => wrepr U8 106  | 89 => wrepr U8 203
  | 90 => wrepr U8 190  | 91 => wrepr U8 57   | 92 => wrepr U8 74   | 93 => wrepr U8 76   | 94 => wrepr U8 88
  | 95 => wrepr U8 207  | 96 => wrepr U8 208  | 97 => wrepr U8 239  | 98 => wrepr U8 170  | 99 => wrepr U8 251
  | 100 => wrepr U8 67  | 101 => wrepr U8 77  | 102 => wrepr U8 51  | 103 => wrepr U8 133 | 104 => wrepr U8 69
  | 105 => wrepr U8 249 | 106 => wrepr U8 2   | 107 => wrepr U8 127 | 108 => wrepr U8 80  | 109 => wrepr U8 60
  | 110 => wrepr U8 159 | 111 => wrepr U8 168 | 112 => wrepr U8 81  | 113 => wrepr U8 163 | 114 => wrepr U8 64
  | 115 => wrepr U8 143 | 116 => wrepr U8 146 | 117 => wrepr U8 157 | 118 => wrepr U8 56  | 119 => wrepr U8 245
  | 120 => wrepr U8 188 | 121 => wrepr U8 182 | 122 => wrepr U8 218 | 123 => wrepr U8 33  | 124 => wrepr U8 16
  | 125 => wrepr U8 255 | 126 => wrepr U8 243 | 127 => wrepr U8 210 | 128 => wrepr U8 205 | 129 => wrepr U8 12
  | 130 => wrepr U8 19  | 131 => wrepr U8 236 | 132 => wrepr U8 95  | 133 => wrepr U8 151 | 134 => wrepr U8 68
  | 135 => wrepr U8 23  | 136 => wrepr U8 196 | 137 => wrepr U8 167 | 138 => wrepr U8 126 | 139 => wrepr U8 61
  | 140 => wrepr U8 100 | 141 => wrepr U8 93  | 142 => wrepr U8 25  | 143 => wrepr U8 115 | 144 => wrepr U8 96
  | 145 => wrepr U8 129 | 146 => wrepr U8 79  | 147 => wrepr U8 220 | 148 => wrepr U8 34  | 149 => wrepr U8 42
  | 150 => wrepr U8 144 | 151 => wrepr U8 136 | 152 => wrepr U8 70  | 153 => wrepr U8 238 | 154 => wrepr U8 184
  | 155 => wrepr U8 20  | 156 => wrepr U8 222 | 157 => wrepr U8 94  | 158 => wrepr U8 11  | 159 => wrepr U8 219
  | 160 => wrepr U8 224 | 161 => wrepr U8 50  | 162 => wrepr U8 58  | 163 => wrepr U8 10  | 164 => wrepr U8 73
  | 165 => wrepr U8 6   | 166 => wrepr U8 36  | 167 => wrepr U8 92  | 168 => wrepr U8 194 | 169 => wrepr U8 211
  | 170 => wrepr U8 172 | 171 => wrepr U8 98  | 172 => wrepr U8 145 | 173 => wrepr U8 149 | 174 => wrepr U8 228
  | 175 => wrepr U8 121 | 176 => wrepr U8 231 | 177 => wrepr U8 200 | 178 => wrepr U8 55  | 179 => wrepr U8 109
  | 180 => wrepr U8 141 | 181 => wrepr U8 213 | 182 => wrepr U8 78  | 183 => wrepr U8 169 | 184 => wrepr U8 108
  | 185 => wrepr U8 86  | 186 => wrepr U8 244 | 187 => wrepr U8 234 | 188 => wrepr U8 101 | 189 => wrepr U8 122
  | 190 => wrepr U8 174 | 191 => wrepr U8 8   | 192 => wrepr U8 186 | 193 => wrepr U8 120 | 194 => wrepr U8 37
  | 195 => wrepr U8 46  | 196 => wrepr U8 28  | 197 => wrepr U8 166 | 198 => wrepr U8 180 | 199 => wrepr U8 198
  | 200 => wrepr U8 232 | 201 => wrepr U8 221 | 202 => wrepr U8 116 | 203 => wrepr U8 31  | 204 => wrepr U8 75
  | 205 => wrepr U8 189 | 206 => wrepr U8 139 | 207 => wrepr U8 138 | 208 => wrepr U8 112 | 209 => wrepr U8 62
  | 210 => wrepr U8 181 | 211 => wrepr U8 102 | 212 => wrepr U8 72  | 213 => wrepr U8 3   | 214 => wrepr U8 246
  | 215 => wrepr U8 14  | 216 => wrepr U8 97  | 217 => wrepr U8 53  | 218 => wrepr U8 87  | 219 => wrepr U8 185
  | 220 => wrepr U8 134 | 221 => wrepr U8 193 | 222 => wrepr U8 29  | 223 => wrepr U8 158 | 224 => wrepr U8 225
  | 225 => wrepr U8 248 | 226 => wrepr U8 152 | 227 => wrepr U8 17  | 228 => wrepr U8 105 | 229 => wrepr U8 217
  | 230 => wrepr U8 142 | 231 => wrepr U8 148 | 232 => wrepr U8 155 | 233 => wrepr U8 30  | 234 => wrepr U8 135
  | 235 => wrepr U8 233 | 236 => wrepr U8 206 | 237 => wrepr U8 85  | 238 => wrepr U8 40  | 239 => wrepr U8 223
  | 240 => wrepr U8 140 | 241 => wrepr U8 161 | 242 => wrepr U8 137 | 243 => wrepr U8 13  | 244 => wrepr U8 191
  | 245 => wrepr U8 230 | 246 => wrepr U8 66  | 247 => wrepr U8 104 | 248 => wrepr U8 65  | 249 => wrepr U8 153
  | 250 => wrepr U8 45  | 251 => wrepr U8 15  | 252 => wrepr U8 176 | 253 => wrepr U8 84  | 254 => wrepr U8 187
  | 255 => wrepr U8 22  | _ => word0
  end.

Definition InvSbox (v1 : u8) :=
  match toword v1 with
  | 0 => wrepr U8 82    | 1 => wrepr U8 9     | 2 => wrepr U8 106   | 3 => wrepr U8 213   | 4 => wrepr U8 48
  | 5 => wrepr U8 54    | 6 => wrepr U8 165   | 7 => wrepr U8 56    | 8 => wrepr U8 191   | 9 => wrepr U8 64
  | 10 => wrepr U8 163  | 11 => wrepr U8 158  | 12 => wrepr U8 129  | 13 => wrepr U8 243  | 14 => wrepr U8 215
  | 15 => wrepr U8 251  | 16 => wrepr U8 124  | 17 => wrepr U8 227  | 18 => wrepr U8 57   | 19 => wrepr U8 130
  | 20 => wrepr U8 155  | 21 => wrepr U8 47   | 22 => wrepr U8 255  | 23 => wrepr U8 135  | 24 => wrepr U8 52
  | 25 => wrepr U8 142  | 26 => wrepr U8 67   | 27 => wrepr U8 68   | 28 => wrepr U8 196  | 29 => wrepr U8 222
  | 30 => wrepr U8 233  | 31 => wrepr U8 203  | 32 => wrepr U8 84   | 33 => wrepr U8 123  | 34 => wrepr U8 148
  | 35 => wrepr U8 50   | 36 => wrepr U8 166  | 37 => wrepr U8 194  | 38 => wrepr U8 35   | 39 => wrepr U8 61
  | 40 => wrepr U8 238  | 41 => wrepr U8 76   | 42 => wrepr U8 149  | 43 => wrepr U8 11   | 44 => wrepr U8 66
  | 45 => wrepr U8 250  | 46 => wrepr U8 195  | 47 => wrepr U8 78   | 48 => wrepr U8 8    | 49 => wrepr U8 46
  | 50 => wrepr U8 161  | 51 => wrepr U8 102  | 52 => wrepr U8 40   | 53 => wrepr U8 217  | 54 => wrepr U8 36
  | 55 => wrepr U8 178  | 56 => wrepr U8 118  | 57 => wrepr U8 91   | 58 => wrepr U8 162  | 59 => wrepr U8 73
  | 60 => wrepr U8 109  | 61 => wrepr U8 139  | 62 => wrepr U8 209  | 63 => wrepr U8 37   | 64 => wrepr U8 114
  | 65 => wrepr U8 248  | 66 => wrepr U8 246  | 67 => wrepr U8 100  | 68 => wrepr U8 134  | 69 => wrepr U8 104
  | 70 => wrepr U8 152  | 71 => wrepr U8 22   | 72 => wrepr U8 212  | 73 => wrepr U8 164  | 74 => wrepr U8 92
  | 75 => wrepr U8 204  | 76 => wrepr U8 93   | 77 => wrepr U8 101  | 78 => wrepr U8 182  | 79 => wrepr U8 146
  | 80 => wrepr U8 108  | 81 => wrepr U8 112  | 82 => wrepr U8 72   | 83 => wrepr U8 80   | 84 => wrepr U8 253
  | 85 => wrepr U8 237  | 86 => wrepr U8 185  | 87 => wrepr U8 218  | 88 => wrepr U8 94   | 89 => wrepr U8 21
  | 90 => wrepr U8 70   | 91 => wrepr U8 87   | 92 => wrepr U8 167  | 93 => wrepr U8 141  | 94 => wrepr U8 157
  | 95 => wrepr U8 132  | 96 => wrepr U8 144  | 97 => wrepr U8 216  | 98 => wrepr U8 171  | 99 => wrepr U8 0
  | 100 => wrepr U8 140 | 101 => wrepr U8 188 | 102 => wrepr U8 211 | 103 => wrepr U8 10  | 104 => wrepr U8 247
  | 105 => wrepr U8 228 | 106 => wrepr U8 88  | 107 => wrepr U8 5   | 108 => wrepr U8 184 | 109 => wrepr U8 179
  | 110 => wrepr U8 69  | 111 => wrepr U8 6   | 112 => wrepr U8 208 | 113 => wrepr U8 44  | 114 => wrepr U8 30
  | 115 => wrepr U8 143 | 116 => wrepr U8 202 | 117 => wrepr U8 63  | 118 => wrepr U8 15  | 119 => wrepr U8 2
  | 120 => wrepr U8 193 | 121 => wrepr U8 175 | 122 => wrepr U8 189 | 123 => wrepr U8 3   | 124 => wrepr U8 1
  | 125 => wrepr U8 19  | 126 => wrepr U8 138 | 127 => wrepr U8 107 | 128 => wrepr U8 58  | 129 => wrepr U8 145
  | 130 => wrepr U8 17  | 131 => wrepr U8 65  | 132 => wrepr U8 79  | 133 => wrepr U8 103 | 134 => wrepr U8 220
  | 135 => wrepr U8 234 | 136 => wrepr U8 151 | 137 => wrepr U8 242 | 138 => wrepr U8 207 | 139 => wrepr U8 206
  | 140 => wrepr U8 240 | 141 => wrepr U8 180 | 142 => wrepr U8 230 | 143 => wrepr U8 115 | 144 => wrepr U8 150
  | 145 => wrepr U8 172 | 146 => wrepr U8 116 | 147 => wrepr U8 34  | 148 => wrepr U8 231 | 149 => wrepr U8 173
  | 150 => wrepr U8 53  | 151 => wrepr U8 133 | 152 => wrepr U8 226 | 153 => wrepr U8 249 | 154 => wrepr U8 55
  | 155 => wrepr U8 232 | 156 => wrepr U8 28  | 157 => wrepr U8 117 | 158 => wrepr U8 223 | 159 => wrepr U8 110
  | 160 => wrepr U8 71  | 161 => wrepr U8 241 | 162 => wrepr U8 26  | 163 => wrepr U8 113 | 164 => wrepr U8 29
  | 165 => wrepr U8 41  | 166 => wrepr U8 197 | 167 => wrepr U8 137 | 168 => wrepr U8 111 | 169 => wrepr U8 183
  | 170 => wrepr U8 98  | 171 => wrepr U8 14  | 172 => wrepr U8 170 | 173 => wrepr U8 24  | 174 => wrepr U8 190
  | 175 => wrepr U8 27  | 176 => wrepr U8 252 | 177 => wrepr U8 86  | 178 => wrepr U8 62  | 179 => wrepr U8 75
  | 180 => wrepr U8 198 | 181 => wrepr U8 210 | 182 => wrepr U8 121 | 183 => wrepr U8 32  | 184 => wrepr U8 154
  | 185 => wrepr U8 219 | 186 => wrepr U8 192 | 187 => wrepr U8 254 | 188 => wrepr U8 120 | 189 => wrepr U8 205
  | 190 => wrepr U8 90  | 191 => wrepr U8 244 | 192 => wrepr U8 31  | 193 => wrepr U8 221 | 194 => wrepr U8 168
  | 195 => wrepr U8 51  | 196 => wrepr U8 136 | 197 => wrepr U8 7   | 198 => wrepr U8 199 | 199 => wrepr U8 49
  | 200 => wrepr U8 177 | 201 => wrepr U8 18  | 202 => wrepr U8 16  | 203 => wrepr U8 89  | 204 => wrepr U8 39
  | 205 => wrepr U8 128 | 206 => wrepr U8 236 | 207 => wrepr U8 95  | 208 => wrepr U8 96  | 209 => wrepr U8 81
  | 210 => wrepr U8 127 | 211 => wrepr U8 169 | 212 => wrepr U8 25  | 213 => wrepr U8 181 | 214 => wrepr U8 74
  | 215 => wrepr U8 13  | 216 => wrepr U8 45  | 217 => wrepr U8 229 | 218 => wrepr U8 122 | 219 => wrepr U8 159
  | 220 => wrepr U8 147 | 221 => wrepr U8 201 | 222 => wrepr U8 156 | 223 => wrepr U8 239 | 224 => wrepr U8 160
  | 225 => wrepr U8 224 | 226 => wrepr U8 59  | 227 => wrepr U8 77  | 228 => wrepr U8 174 | 229 => wrepr U8 42
  | 230 => wrepr U8 245 | 231 => wrepr U8 176 | 232 => wrepr U8 200 | 233 => wrepr U8 235 | 234 => wrepr U8 187
  | 235 => wrepr U8 60  | 236 => wrepr U8 131 | 237 => wrepr U8 83  | 238 => wrepr U8 153 | 239 => wrepr U8 97
  | 240 => wrepr U8 23  | 241 => wrepr U8 43  | 242 => wrepr U8 4   | 243 => wrepr U8 126 | 244 => wrepr U8 186
  | 245 => wrepr U8 119 | 246 => wrepr U8 214 | 247 => wrepr U8 38  | 248 => wrepr U8 225 | 249 => wrepr U8 105
  | 250 => wrepr U8 20  | 251 => wrepr U8 99  | 252 => wrepr U8 85  | 253 => wrepr U8 33  | 254 => wrepr U8 12
  | 255 => wrepr U8 125 | _ => word0
  end.

(* NOTE: SubWord clashes with subword *)
Definition SubWord (v1 : u32) :=
  make_vec U32 (map Sbox (split_vec U8 v1)).
Definition InvSubWord (v1 : u32) :=
  make_vec U32 (map InvSbox (split_vec U8 v1)).

Definition to_matrix (s : u128) :=
  let s_ := fun i j => (subword (i * U8) U8 (subword (j * U32) U32 s)) in
  (s_ 0 0, s_ 0 1, s_ 0 2, s_ 0 3,
    s_ 1 0, s_ 1 1, s_ 1 2, s_ 1 3,
    s_ 2 0, s_ 2 1, s_ 2 2, s_ 2 2,
    s_ 3 0, s_ 3 1, s_ 3 2, s_ 3 3)%nat.

Definition to_state (m : u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8 * u8) :=
  let '(s00, s01, s02, s03,
        s10, s11, s12, s13,
        s20, s21, s22, s23,
        s30, s31, s32, s33) := m in
  let c0 := make_vec U32 [:: s00; s10; s20; s30] in
  let c1 := make_vec U32 [:: s01; s11; s21; s31] in
  let c2 := make_vec U32 [:: s02; s12; s22; s32] in
  let c3 := make_vec U32 [:: s03; s13; s23; s33] in
  make_vec U128 [:: c0; c1; c2; c3].

Definition SubBytes (s : u128) :=
  make_vec U128 (map SubWord (split_vec U32 s)).
Definition InvSubBytes (s : u128) :=
  make_vec U128 (map InvSubWord (split_vec U32 s)).

Definition ShiftRows (s : u128) :=
 let '(s00, s01, s02, s03,
       s10, s11, s12, s13,
       s20, s21, s22, s23,
       s30, s31, s32, s33) := to_matrix s in
 to_state (s00, s01, s02, s03,
           s11, s12, s13, s10,
           s22, s23, s20, s21,
           s33, s30, s31, s32).

Definition InvShiftRows (s : u128) :=
 let '(s00, s01, s02, s03,
       s11, s12, s13, s10,
       s22, s23, s20, s21,
       s33, s30, s31, s32) := to_matrix s in
 to_state
    (s00, s01, s02, s03,
     s10, s11, s12, s13,
     s20, s21, s22, s23,
     s30, s31, s32, s33).

(* TODO: Implement these *)
Definition MixColumns : u128 -> u128 := fun w => w.
Definition InvMixColumns : u128 -> u128 := fun w => w.

Definition wAESDEC (state rkey : u128) :=
  let state := InvShiftRows state in
  let state := InvSubBytes state in
  let state := InvMixColumns state in
  wxor state rkey.

Definition wAESDECLAST (state rkey : u128) :=
  let state := InvShiftRows state in
  let state := InvSubBytes state in
  wxor state rkey.

Definition wAESENC (state rkey : u128) :=
  let state := ShiftRows state in
  let state := SubBytes state in
  let state := MixColumns state in
  wxor state rkey.

Definition wAESENCLAST (state rkey : u128) :=
  let state := ShiftRows state in
  let state := SubBytes state in
  wxor state rkey.

Notation wAESIMC := InvMixColumns.

Definition wAESKEYGENASSIST (v1 : u128) (v2 : u8) :=
  let rcon := zero_extend U32 v2 in
  let x1 := subword (1 * U32) U32 v1 in
  let x3 := subword (3 * U32) U32 v1 in
  let y0 := SubWord x1 in
  let y1 := wxor (wror (SubWord x1) 1) rcon in
  let y2 := SubWord x3 in
  let y3 := wxor (wror (SubWord x3) 1) rcon in
  make_vec U128 [:: y0; y1; y2; y3].

Definition wAESENC_ (state rkey: u128) :=
  let state := SubBytes state in
  let state := ShiftRows state in
  let state := MixColumns state in
  wxor state rkey.

Definition wAESENCLAST_ (state rkey: u128) :=
  let state := SubBytes state in
  let state := ShiftRows state in
  wxor state rkey.

Definition wAESDEC_ (state rkey: u128) :=
  let state := InvShiftRows state in
  let state := InvSubBytes state in
  let state := wxor state rkey in
  InvMixColumns state.
