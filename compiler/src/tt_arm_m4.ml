open Utils

module L = Location
module S = Syntax

(* -------------------------------------------------------------------- *)
(* ARM parsing. *)

let get_set_flags s =
  if String.ends_with s "s" then (true, String.drop_end 1 s) else (false, s)

let get_is_conditional s =
  if String.ends_with s "cc" then (true, String.drop_end 2 s) else (false, s)

let shift_kind_assoc =
  let s_of_sk sk = Conv.string_of_string0 (Arm_decl.string_of_shift_kind sk) in
  List.map (fun sk -> (s_of_sk sk, sk)) Arm_decl.shift_kinds

let get_has_shift args =
  let get_shift _ a =
    match a.L.pl_desc with
    | S.PEPrim (id, [ ({ L.pl_desc = S.PEInt _ } as sham) ]) -> begin
        let s = String.lowercase_ascii id.pl_desc in
        match List.assoc_opt s shift_kind_assoc with
        | Some sk -> Some (sk, sham)
        | None -> None
        end
    | _ -> None
  in
  match List.opicki get_shift args with
  | None -> (None, args)
  | Some (i, (sk, sham)) -> (Some sk, List.modify_at i (fun _ -> sham) args)

let get_arm_prim s =
  let s = String.lowercase_ascii s in
  let is_conditional, s = get_is_conditional s in
  let set_flags, s = get_set_flags s in
  (s, set_flags, is_conditional)

let tt_prim ps s args =
  let name, set_flags, is_conditional = get_arm_prim s in
  let has_shift, args = get_has_shift args in
  match List.assoc_opt name ps with
  | Some (Sopn.PrimARM pr) -> Some (pr set_flags is_conditional has_shift, args)
  | _ -> None
