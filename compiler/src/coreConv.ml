module B = Bigint

let rec pos_of_bi bi =
  let open B.Notations in
  if bi <=^ B.one then BinNums.Coq_xH
  else
    let p = pos_of_bi (B.rshift bi 1) in
    if (B.erem bi (B.of_int 2)) =^ B.one
    then BinNums.Coq_xI p
    else BinNums.Coq_xO p

let rec bi_of_pos pos =
  let open B.Notations in
  match pos with
  | BinNums.Coq_xH   -> B.one
  | BinNums.Coq_xO p -> B.lshift (bi_of_pos p) 1
  | BinNums.Coq_xI p -> B.lshift (bi_of_pos p) 1 +^ B.one

let z_of_bi bi =
  let open B.Notations in
  if bi =^ B.zero then BinNums.Z0
  else if bi <^ B.zero then BinNums.Zneg (pos_of_bi (B.abs bi))
  else BinNums.Zpos (pos_of_bi bi)

let bi_of_z z =
  match z with
  | BinNums.Zneg p -> B.neg (bi_of_pos p)
  | BinNums.Z0     -> B.zero
  | BinNums.Zpos p -> bi_of_pos p

let z_of_int i = z_of_bi (B.of_int i)
let int_of_z z = B.to_int (bi_of_z z)

let bi_of_nat n =
  bi_of_z (BinInt.Z.of_nat n)

let int_of_nat n = B.to_int (bi_of_nat n)
let nat_of_int i = BinInt.Z.to_nat (z_of_int i)

let pos_of_int i = pos_of_bi (B.of_int i)
let int_of_pos p = B.to_int (bi_of_pos p)
