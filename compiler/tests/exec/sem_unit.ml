open Jasmin
open Execlib

let w_of_z sz z = Values.Vword (sz, Conv.word_of_z sz z)
let w_of_string sz n = w_of_z sz (Z.of_string n)
let w8 i = w_of_string Wsize.U8 i
let w16 i = w_of_string Wsize.U16 i
let w128 i = w_of_string Wsize.U128 i
let w256 i = w_of_string Wsize.U256 i

let () =
  let prog = load_file "sem_unit.jazz" in
  exec prog [] "vpsllv_4u32" @@ List.map w128 [ "1"; "1000000" ];
  exec prog [] "vpsllv_4u32"
    [
      w128 "0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a";
      w128 "0x00000004000000030000000200000001";
    ];
  exec prog [] "vpsllv_8u32" @@ List.map w256 [ "1"; "1000000" ];
  exec prog [] "vpsllv_4u64"
    [
      w256 "0x00ffff001248a00000ffff001248a00000ffff001248a00000ffff001248a000";
      w256 "0x0000000000000002000000000000000400000000000000080000000000000010";
    ];
  exec prog [] "shrd_16" [ w16 "2"; w16 "9"; w8 "16" ];
  exec prog [] "shrd_16" [ w16 "2"; w16 "9"; w8 "17" ];
  ()
