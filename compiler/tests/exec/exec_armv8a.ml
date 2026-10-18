open Jasmin

module Armv8a : Arch_full.Arch =
  (val CoreArchFactory.get_arch_module Utils.ARMv8A Glob_options.Linux)

open Execlib.Make (Armv8a)

(* SHA-256 and SHA-512 digests of "abc", computed with the SHA-2
   instructions; the expected values are the published digests, as
   (H0..H3), (H4..H7) for SHA-256 and (H0, H1)..(H6, H7) for SHA-512, first
   word in the low bits. *)
let () =
  let prog = load_file "../success/armv8a/simd_sha2_kat.jazz" in
  exec prog [] "sha256_abc" [];
  exec prog [] "sha512_abc" []

(* The permutations and element moves on the fixed inputs of
   simd_exec.jazz. *)
let () =
  let prog = load_file "../success/armv8a/simd_exec.jazz" in
  List.iter
    (fun f -> exec prog [] f [])
    [ "perm_ext"; "perm_rev"; "perm_rev64_4s"; "perm_trn"; "perm_zip";
      "perm_uzp"; "move_dup"; "move_ins"; "move_umov_bh"; "move_umov_sd" ]
