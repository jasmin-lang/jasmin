open Ascii
open BinNums
open BinPos
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Stack_alloc
open Utils0

type label = positive

type linstr_r =
| Lassgn of lval * assgn_tag * pexpr
| Lopn of lval list * sopn * pexpr list
| Llabel of label
| Lgoto of label
| Lcond of pexpr * label
| Lreturn

type linstr = { li_ii : instr_info; li_i : linstr_r }

type lcmd = linstr list

type lfundef = { lfd_stk_size : coq_Z; lfd_nstk : Equality.sort;
                 lfd_arg : var_i list; lfd_body : lcmd; lfd_res : var_i list }

type lprog = (funname * lfundef) list

(** val linear_c :
    (instr -> label -> lcmd -> (label * lcmd) ciexec) -> instr list -> label
    -> lcmd -> (label * lcmd) ciexec **)

let rec linear_c linear_i0 c lbl lc =
  match c with
  | [] -> ciok (lbl, lc)
  | i :: c0 ->
    Result.bind (fun p -> linear_i0 i (fst p) (snd p))
      (linear_c linear_i0 c0 lbl lc)

(** val next_lbl : positive -> positive **)

let next_lbl lbl =
  Pos.add lbl Coq_xH

(** val linear_i :
    instr -> label -> lcmd -> (instr_info * error_msg, label * linstr list)
    result **)

let rec linear_i i lbl lc =
  let MkI (ii, ir) = i in
  (match ir with
   | Cassgn (x, tag, e) ->
     Ok (lbl, ({ li_ii = ii; li_i = (Lassgn (x, tag, e)) } :: lc))
   | Copn (xs, o, es) ->
     Ok (lbl, ({ li_ii = ii; li_i = (Lopn (xs, o, es)) } :: lc))
   | Cif (e, c1, c2) ->
     (match c1 with
      | [] ->
        let lbl0 = next_lbl lbl in
        Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i = (Lcond (e,
          lbl)) } :: (snd p))))
          (linear_c linear_i c2 lbl0 ({ li_ii = ii; li_i = (Llabel
            lbl) } :: lc))
      | _ :: _ ->
        (match c2 with
         | [] ->
           let lbl0 = next_lbl lbl in
           Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i = (Lcond
             ((Pnot e), lbl)) } :: (snd p))))
             (linear_c linear_i c1 lbl0 ({ li_ii = ii; li_i = (Llabel
               lbl) } :: lc))
         | _ :: _ ->
           let l2 = next_lbl lbl in
           let lbl0 = next_lbl l2 in
           Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i = (Lcond
             (e, lbl)) } :: (snd p))))
             (Result.bind (fun p -> linear_c linear_i c2 (fst p) (snd p))
               (Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i =
                 (Lgoto l2) } :: (snd p))))
                 (Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i =
                   (Llabel lbl) } :: (snd p))))
                   (linear_c linear_i c1 lbl0 ({ li_ii = ii; li_i = (Llabel
                     l2) } :: lc)))))))
   | Cfor (_, _, _) ->
     cierror ii (Cerr_linear (String ((Ascii (false, true, true, false,
       false, true, true, false)), (String ((Ascii (true, true, true, true,
       false, true, true, false)), (String ((Ascii (false, true, false,
       false, true, true, true, false)), (String ((Ascii (false, false,
       false, false, false, true, false, false)), (String ((Ascii (false,
       true, true, false, false, true, true, false)), (String ((Ascii (true,
       true, true, true, false, true, true, false)), (String ((Ascii (true,
       false, true, false, true, true, true, false)), (String ((Ascii (false,
       true, true, true, false, true, true, false)), (String ((Ascii (false,
       false, true, false, false, true, true, false)), (String ((Ascii
       (false, false, false, false, false, true, false, false)), (String
       ((Ascii (true, false, false, true, false, true, true, false)), (String
       ((Ascii (false, true, true, true, false, true, true, false)), (String
       ((Ascii (false, false, false, false, false, true, false, false)),
       (String ((Ascii (false, false, true, true, false, true, true, false)),
       (String ((Ascii (true, false, false, true, false, true, true, false)),
       (String ((Ascii (false, true, true, true, false, true, true, false)),
       (String ((Ascii (true, false, true, false, false, true, true, false)),
       (String ((Ascii (true, false, false, false, false, true, true,
       false)), (String ((Ascii (false, true, false, false, true, true, true,
       false)), EmptyString)))))))))))))))))))))))))))))))))))))))
   | Cwhile (e, c) ->
     let l2 = next_lbl lbl in
     let lbl0 = next_lbl l2 in
     Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i = (Lgoto
       lbl) } :: (snd p))))
       (Result.bind (fun p -> Ok ((fst p), ({ li_ii = ii; li_i = (Llabel
         l2) } :: (snd p))))
         (linear_c linear_i c lbl0 ({ li_ii = ii; li_i = (Llabel
           lbl) } :: ({ li_ii = ii; li_i = (Lcond (e, l2)) } :: lc))))
   | Ccall (_, _, _, _) ->
     cierror ii (Cerr_linear (String ((Ascii (true, true, false, false,
       false, true, true, false)), (String ((Ascii (true, false, false,
       false, false, true, true, false)), (String ((Ascii (false, false,
       true, true, false, true, true, false)), (String ((Ascii (false, false,
       true, true, false, true, true, false)), (String ((Ascii (false, false,
       false, false, false, true, false, false)), (String ((Ascii (false,
       true, true, false, false, true, true, false)), (String ((Ascii (true,
       true, true, true, false, true, true, false)), (String ((Ascii (true,
       false, true, false, true, true, true, false)), (String ((Ascii (false,
       true, true, true, false, true, true, false)), (String ((Ascii (false,
       false, true, false, false, true, true, false)), (String ((Ascii
       (false, false, false, false, false, true, false, false)), (String
       ((Ascii (true, false, false, true, false, true, true, false)), (String
       ((Ascii (false, true, true, true, false, true, true, false)), (String
       ((Ascii (false, false, false, false, false, true, false, false)),
       (String ((Ascii (false, false, true, true, false, true, true, false)),
       (String ((Ascii (true, false, false, true, false, true, true, false)),
       (String ((Ascii (false, true, true, true, false, true, true, false)),
       (String ((Ascii (true, false, true, false, false, true, true, false)),
       (String ((Ascii (true, false, false, false, false, true, true,
       false)), (String ((Ascii (false, true, false, false, true, true, true,
       false)), EmptyString))))))))))))))))))))))))))))))))))))))))))

(** val linear_fd : (funname * S.sfundef) -> (fun_error, lfundef) result **)

let linear_fd fd =
  Result.bind (fun fd' ->
    cfok { lfd_stk_size = (snd fd).S.sf_stk_sz; lfd_nstk =
      (snd fd).S.sf_stk_id; lfd_arg = (snd fd).S.sf_params; lfd_body =
      (snd fd'); lfd_res = (snd fd).S.sf_res })
    (add_finfo (fst fd) (fst fd)
      (linear_c linear_i (snd fd).S.sf_body Coq_xH ({ li_ii = Coq_xH; li_i =
        Lreturn } :: [])))

(** val linear_ffd :
    (funname * S.sfundef) -> lprog cfexec -> (fun_error, (funname * lfundef)
    list) result **)

let linear_ffd ffd p =
  Result.bind (fun p0 ->
    Result.bind (fun fd -> cfok (((fst ffd), fd) :: p0)) (linear_fd ffd)) p

(** val linear_prog : S.sprog -> lprog cfexec **)

let linear_prog sp =
  foldr linear_ffd (cfok []) sp
