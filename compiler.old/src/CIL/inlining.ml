open Ascii
open Datatypes
open String0
open Allocation
open Compiler_util
open Expr
open Seq
open Utils0
open Var0

(** val assgn_tuple : instr_info -> lval list -> pexpr list -> instr list **)

let assgn_tuple iinfo xs es =
  let assgn = fun xe -> MkI (iinfo, (Cassgn ((fst xe), AT_rename, (snd xe))))
  in
  map assgn (zip xs es)

(** val inline_c :
    (instr -> Sv.t -> (Sv.t * instr list) ciexec) -> instr list -> Sv.t ->
    (instr_info * error_msg, Sv.t * instr list) result **)

let inline_c inline_i0 c s =
  foldr (fun i r ->
    Result.bind (fun r0 ->
      Result.bind (fun ri -> ciok ((fst ri), (cat (snd ri) (snd r0))))
        (inline_i0 i (fst r0))) r) (ciok (s, [])) c

(** val check_rename :
    instr_info -> funname -> fundef -> fundef -> Sv.t ->
    (instr_info * error_msg, unit) result **)

let check_rename iinfo f fd1 fd2 s =
  Result.bind (fun _ ->
    let s2 = read_es (map (fun x -> Pvar x) fd2.f_res) in
    let s3 = write_c_rec s2 fd2.f_body in
    let s4 = vrvs_rec s3 (map (fun x -> Lvar x) fd2.f_params) in
    if disjoint s s4 then ciok () else cierror iinfo (Cerr_inline (s, s4)))
    (add_infun iinfo (CheckAllocReg.check_fundef (f, fd1) (f, fd2) ()))

(** val get_fun : prog -> instr_info -> funname -> fundef ciexec **)

let get_fun p iinfo f =
  match get_fundef (Obj.magic p) (Obj.magic f) with
  | Some fd -> ciok fd
  | None ->
    cierror iinfo (Cerr_unknown_fun (f, (String ((Ascii (true, false, false,
      true, false, true, true, false)), (String ((Ascii (false, true, true,
      true, false, true, true, false)), (String ((Ascii (false, false, true,
      true, false, true, true, false)), (String ((Ascii (true, false, false,
      true, false, true, true, false)), (String ((Ascii (false, true, true,
      true, false, true, true, false)), (String ((Ascii (true, false, false,
      true, false, true, true, false)), (String ((Ascii (false, true, true,
      true, false, true, true, false)), (String ((Ascii (true, true, true,
      false, false, true, true, false)), EmptyString))))))))))))))))))

(** val inline_i :
    (fundef -> fundef) -> prog -> instr -> Sv.t -> (Sv.t * instr list) ciexec **)

let rec inline_i rename_fd p i x =
  let MkI (iinfo, ir) = i in
  (match ir with
   | Cif (e, c1, c2) ->
     Result.bind (fun c3 ->
       Result.bind (fun c4 ->
         ciok ((read_e_rec (Sv.union (fst c3) (fst c4)) e), ((MkI (iinfo,
           (Cif (e, (snd c3), (snd c4))))) :: [])))
         (inline_c (inline_i rename_fd p) c2 x))
       (inline_c (inline_i rename_fd p) c1 x)
   | Cfor (x0, r, c) ->
     let x1 = Sv.union (read_i ir) x in
     Result.bind (fun c0 ->
       ciok (x1, ((MkI (iinfo, (Cfor (x0, r, (snd c0))))) :: [])))
       (inline_c (inline_i rename_fd p) c x1)
   | Cwhile (e, c) ->
     let x0 = Sv.union (read_i ir) x in
     Result.bind (fun c0 ->
       ciok (x0, ((MkI (iinfo, (Cwhile (e, (snd c0))))) :: [])))
       (inline_c (inline_i rename_fd p) c x0)
   | Ccall (inline, xs, f, es) ->
     let x0 = Sv.union (read_i ir) x in
     (match inline with
      | InlineFun ->
        Result.bind (fun fd ->
          let fd' = rename_fd fd in
          Result.bind (fun _ ->
            ciok (x0,
              (cat
                (assgn_tuple iinfo (map (fun x1 -> Lvar x1) fd'.f_params) es)
                (cat fd'.f_body
                  (assgn_tuple iinfo xs (map (fun x1 -> Pvar x1) fd'.f_res))))))
            (check_rename iinfo f fd fd' (Sv.union (vrvs xs) x0)))
          (get_fun p iinfo f)
      | DoNotInline -> ciok (x0, (i :: [])))
   | _ -> ciok ((Sv.union (read_i ir) x), (i :: [])))

(** val inline_fd :
    (fundef -> fundef) -> prog -> fundef -> (instr_info * error_msg, fundef)
    result **)

let inline_fd rename_fd p fd =
  let { f_iinfo = ii; f_params = params; f_body = c; f_res = res } = fd in
  let s = read_es (map (fun x -> Pvar x) res) in
  Result.bind (fun c0 -> Ok { f_iinfo = ii; f_params = params; f_body =
    (snd c0); f_res = res }) (inline_c (inline_i rename_fd p) c s)

(** val inline_fd_cons :
    (fundef -> fundef) -> (funname * fundef) -> prog cfexec -> (fun_error,
    (funname * fundef) list) result **)

let inline_fd_cons rename_fd ffd p =
  Result.bind (fun p0 ->
    let f = fst ffd in
    Result.bind (fun fd -> cfok ((f, fd) :: p0))
      (add_finfo f f (inline_fd rename_fd p0 (snd ffd)))) p

(** val inline_prog : (fundef -> fundef) -> prog -> prog cfexec **)

let inline_prog rename_fd p =
  foldr (inline_fd_cons rename_fd) (cfok []) p
