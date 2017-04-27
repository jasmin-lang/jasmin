open Ascii
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Utils0
open Var0

(** val dead_code_c :
    (instr -> Sv.t -> (Sv.t * instr list) ciexec) -> instr list -> Sv.t ->
    (Sv.t * instr list) ciexec **)

let dead_code_c dead_code_i0 c s =
  foldr (fun i r ->
    Result.bind (fun r0 ->
      Result.bind (fun ri -> ciok ((fst ri), (cat (snd ri) (snd r0))))
        (dead_code_i0 i (fst r0))) r) (ciok (s, [])) c

(** val loop :
    (Sv.t -> (Sv.t * instr list) ciexec) -> instr_info -> nat -> Sv.t -> Sv.t
    -> Sv.t -> (Sv.t * instr list) ciexec **)

let rec loop dead_code_c0 ii n rx wx s =
  match n with
  | O ->
    cierror ii (Cerr_Loop (String ((Ascii (false, false, true, false, false,
      true, true, false)), (String ((Ascii (true, false, true, false, false,
      true, true, false)), (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, false, true, false, false,
      true, true, false)), (String ((Ascii (true, true, true, true, true,
      false, true, false)), (String ((Ascii (true, true, false, false, false,
      true, true, false)), (String ((Ascii (true, true, true, true, false,
      true, true, false)), (String ((Ascii (false, false, true, false, false,
      true, true, false)), (String ((Ascii (true, false, true, false, false,
      true, true, false)), EmptyString)))))))))))))))))))
  | S n0 ->
    Result.bind (fun sc ->
      let (s', c') = sc in
      let s'0 = Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s'0 s
      then ciok (s, c')
      else loop dead_code_c0 ii n0 rx wx (Sv.union s s'0)) (dead_code_c0 s)

(** val wloop :
    (Sv.t -> (Sv.t * instr list) ciexec) -> instr_info -> nat -> Sv.t ->
    (Sv.t * instr list) ciexec **)

let rec wloop dead_code_c0 ii n s =
  match n with
  | O ->
    cierror ii (Cerr_Loop (String ((Ascii (false, false, true, false, false,
      true, true, false)), (String ((Ascii (true, false, true, false, false,
      true, true, false)), (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, false, true, false, false,
      true, true, false)), (String ((Ascii (true, true, true, true, true,
      false, true, false)), (String ((Ascii (true, true, false, false, false,
      true, true, false)), (String ((Ascii (true, true, true, true, false,
      true, true, false)), (String ((Ascii (false, false, true, false, false,
      true, true, false)), (String ((Ascii (true, false, true, false, false,
      true, true, false)), EmptyString)))))))))))))))))))
  | S n0 ->
    Result.bind (fun sc ->
      let (s', c') = sc in
      if Sv.subset s' s
      then ciok (s, c')
      else wloop dead_code_c0 ii n0 (Sv.union s s')) (dead_code_c0 s)

(** val write_mem : lval -> bool **)

let write_mem = function
| Lmem (_, _) -> true
| _ -> false

(** val check_nop : lval -> pexpr -> bool **)

let check_nop rv e =
  match rv with
  | Lvar x1 ->
    (match e with
     | Pvar x2 -> eq_op var_i_eqType (Obj.magic x1) (Obj.magic x2)
     | _ -> false)
  | _ -> false

(** val dead_code_i : instr -> Sv.t -> (Sv.t * instr list) ciexec **)

let rec dead_code_i i s =
  let MkI (ii, ir) = i in
  (match ir with
   | Cassgn (x, tag, e) ->
     let w = write_i ir in
     if negb (eq_op assgn_tag_eqType (Obj.magic tag) (Obj.magic AT_keep))
     then if (&&) (disjoint s w) (negb (write_mem x))
          then ciok (s, [])
          else if check_nop x e
               then ciok (s, [])
               else ciok ((read_rv_rec (read_e_rec (Sv.diff s w) e) x),
                      (i :: []))
     else ciok ((read_rv_rec (read_e_rec (Sv.diff s w) e) x), (i :: []))
   | Copn (xs, _, es) ->
     ciok ((read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es),
       (i :: []))
   | Cif (b, c1, c2) ->
     Result.bind (fun sc1 ->
       Result.bind (fun sc2 ->
         let (s1, c3) = sc1 in
         let (s2, c4) = sc2 in
         ciok ((read_e_rec (Sv.union s1 s2) b), ((MkI (ii, (Cif (b, c3,
           c4)))) :: []))) (dead_code_c dead_code_i c2 s))
       (dead_code_c dead_code_i c1 s)
   | Cfor (x, r, c) ->
     let (p, e2) = r in
     let (dir, e1) = p in
     Result.bind (fun sc ->
       let (s0, c0) = sc in
       ciok ((read_e_rec (read_e_rec s0 e2) e1), ((MkI (ii, (Cfor (x, ((dir,
         e1), e2), c0)))) :: [])))
       (loop (dead_code_c dead_code_i c) ii Loop.nb (read_rv (Lvar x))
         (vrv (Lvar x)) s)
   | Cwhile (e, c) ->
     Result.bind (fun sc ->
       let (s0, c0) = sc in ciok (s0, ((MkI (ii, (Cwhile (e, c0)))) :: [])))
       (wloop (dead_code_c dead_code_i c) ii Loop.nb (read_e_rec s e))
   | Ccall (_, xs, _, es) ->
     ciok ((read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es),
       (i :: [])))

(** val dead_code_fd : fundef -> (instr_info * error_msg, fundef) result **)

let dead_code_fd fd =
  let { f_iinfo = ii; f_params = params; f_body = c; f_res = res } = fd in
  let s = read_es (map (fun x -> Pvar x) res) in
  Result.bind (fun c0 ->
    ciok { f_iinfo = ii; f_params = params; f_body = (snd c0); f_res = res })
    (dead_code_c dead_code_i c s)

(** val dead_code_ffd :
    (funname * fundef) -> prog cfexec -> (fun_error, (funname * fundef) list)
    result **)

let dead_code_ffd ffd p =
  Result.bind (fun p0 ->
    let (f, fd) = ffd in
    let fd' = dead_code_fd fd in
    Result.bind (fun c -> cfok ((f, c) :: p0)) (add_finfo f f fd')) p

(** val dead_code_prog : prog -> prog cfexec **)

let dead_code_prog p =
  foldr dead_code_ffd (cfok []) p
