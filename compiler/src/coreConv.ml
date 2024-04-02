let pos_of_z z =
  let open Z.Compare in
  assert (Z.one <= z);
  let rec pos_of_z z =
    if z <= Z.one then BinNums.Coq_xH
    else
      let p = pos_of_z (Z.shift_right z 1) in
      if (Z.erem z (Z.of_int 2)) = Z.one
      then BinNums.Coq_xI p
      else BinNums.Coq_xO p
  in pos_of_z z

let rec z_of_pos pos =
  let open Z in
  match pos with
  | BinNums.Coq_xH   -> Z.one
  | BinNums.Coq_xO p -> Z.shift_left (z_of_pos p) 1
  | BinNums.Coq_xI p -> Z.shift_left (z_of_pos p) 1 + Z.one

let cz_of_z z =
  let open Z.Compare in
  if z = Z.zero then BinNums.Z0
  else if z < Z.zero then BinNums.Zneg (pos_of_z (Z.abs z))
  else BinNums.Zpos (pos_of_z z)

let z_of_cz z =
  match z with
  | BinNums.Zneg p -> Z.neg (z_of_pos p)
  | BinNums.Z0     -> Z.zero
  | BinNums.Zpos p -> z_of_pos p

let cz_of_int i = cz_of_z (Z.of_int i)
let int_of_cz z = Z.to_int (z_of_cz z)
