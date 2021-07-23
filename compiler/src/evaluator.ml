open BinNums
open Utils0 
open Type
open Sem_type
open Warray_
open Var0
open Low_memory
open Expr
open Sem
         
exception Eval_error of instr_info * Utils0.error 

let pp_error fmt (tbl, ii, err) = 
  let i_loc, _ = Conv.get_iinfo tbl ii in
  let msg = 
    match err with
    | ErrOob -> "out_of_bound"
    | ErrAddrUndef -> "undefined address"
    | ErrAddrInvalid -> "invalid address"
    | ErrStack -> "stack error"
    | ErrType  -> "type error" in
  Format.fprintf fmt "Evaluation error at position %a: %s" 
    Printer.pp_iloc i_loc msg

let exn_exec (ii:instr_info) (r: 't exec) = 
  match r with
  | Ok r -> r
  | Error e -> raise (Eval_error(ii, e))

let of_val_z ii v : coq_Z = 
  Obj.magic (exn_exec ii (of_val Coq_sint v))

let of_val_b ii v : bool = 
  Obj.magic (exn_exec ii (of_val Coq_sbool v))

(* ----------------------------------------------------------------- *)
type stack = 
  | Sempty of instr_info * fundef
  | Scall of 
      instr_info * fundef * lval list * sem_t exec Fv.t * instr list * stack
  | Sfor of instr_info * var_i * coq_Z list * instr list * instr list * stack

type state = 
  { s_prog : prog;
    s_cmd  : instr list;
    s_estate : estate;
    s_stk  : stack;
  }

exception Final of Memory.mem * values

let return s = 
  assert (s.s_cmd = []);
  match s.s_stk with
  | Sempty(ii, f) ->
    let s2 = s.s_estate in
    let m2 = s2.emem and vm2 = s2.evm in
    let vres = 
      exn_exec ii (mapM (fun (x:var_i) -> get_var vm2 x.v_var) f.f_res) in
    let vres' = exn_exec ii (mapM2 ErrType truncate_val f.f_tyout vres) in
    raise (Final(m2, vres'))
    
  | Scall(ii,f,xs,vm1,c,stk) ->
    let gd = s.s_prog.p_globs in
    let s2 = s.s_estate in
    let m2 = s2.emem and vm2 = s2.evm in
    let vres = 
      exn_exec ii (mapM (fun (x:var_i) -> get_var vm2 x.v_var) f.f_res) in
    let vres' = exn_exec ii (mapM2 ErrType truncate_val f.f_tyout vres) in
    let s1 = exn_exec ii (write_lvals gd {emem = m2; evm = vm1 } xs vres') in
    { s with 
      s_cmd = c;
      s_estate = s1;
      s_stk = stk }

  | Sfor(ii,i,ws,body,c,stk) ->
    match ws with
    | [] -> { s with s_cmd = c; s_stk = stk }
    | w::ws ->
      let s1 = exn_exec ii (write_var i (Vint w) s.s_estate) in
      { s with s_cmd = body;
               s_estate = s1;
               s_stk = Sfor(ii, i, ws, body, c, stk) }

let small_step1 s = 
  match s.s_cmd with
  | [] -> return s
  | i :: c ->
    let MkI(ii,ir) = i in
    let gd = s.s_prog.p_globs in
    let s1 = s.s_estate in
    match ir with

    | Cassgn(x,_,ty,e) ->
      let v  = exn_exec ii (sem_pexpr gd s1 e) in
      let v' = exn_exec ii (truncate_val ty v) in
      let s2 = exn_exec ii (write_lval gd x v' s1) in
      { s with s_cmd = c; s_estate = s2 }

    | Copn(xs,_,op,es) ->
      let s2 = exn_exec ii (sem_sopn gd op s1 xs es) in
      { s with s_cmd = c; s_estate = s2 }

    | Cif(e,c1,c2) ->
      let b = of_val_b ii (exn_exec ii (sem_pexpr gd s1 e)) in
      let c = (if b then c1 else c2) @ c in
      { s with s_cmd = c }

    | Cfor (i,((d,lo),hi), body) ->
      let vlo = of_val_z ii (exn_exec ii (sem_pexpr gd s1 lo)) in
      let vhi = of_val_z ii (exn_exec ii (sem_pexpr gd s1 hi)) in
      let rng = wrange d vlo vhi in
      let s =
        {s with s_cmd = []; s_stk = Sfor(ii, i, rng, body, c, s.s_stk) } in
      return s
 
    | Cwhile (_, c1, e, c2) ->
      { s with s_cmd = c1 @ MkI(ii, Cif(e, c2@[i],[])) :: c }

    | Ccall(_,xs,fn,es) ->
      let vargs' = exn_exec ii (sem_pexprs gd s1 es) in
      let f = 
        match get_fundef s.s_prog.p_funcs fn with
        | Some f -> f
        | None -> assert false in
      let vargs = exn_exec ii (mapM2 ErrType truncate_val f.f_tyin vargs') in
      let m1 = s1.emem and vm1 = s1.evm in
      let stk = Scall(ii,f, xs, vm1, c, s.s_stk) in
      let sf = 
        exn_exec ii (write_vars f.f_params vargs {emem = m1; evm = vmap0}) in
      {s with s_cmd = f.f_body;
              s_estate = sf;
              s_stk = stk }


let rec small_step s =
  small_step (small_step1 s)

let init_state p fn m = 
  let f = 
    match get_fundef p.p_funcs fn with
    | Some f -> f
    | None -> assert false in
  assert (f.f_tyin = []);
  { s_prog = p;
    s_cmd = f.f_body;
    s_estate = {emem = m; evm = vmap0 };
    s_stk = Sempty(Coq_xO Coq_xH, f) }


let exec p fn m = 
  let s = init_state p fn m in
  try small_step s
  with Final(m,vs) -> m, vs 

(* ----------------------------------------------------------- *)
let pp_undef fmt ty = 
  Format.fprintf fmt "undef<%a>" Printer.pp_ty (Conv.ty_of_cty ty)
 
let pp_word fmt ws w = 
  let z = Word0.wunsigned ws w in
  let z = Conv.bi_of_z z in
  Bigint.pp_print_X fmt z
  
let pp_val fmt v = 
  match v with
  | Vbool b -> Format.fprintf fmt "%b" b
  | Vint z  -> Format.fprintf fmt "%a" Bigint.pp_print (Conv.bi_of_z z)
  | Varr(p,t) ->
    let ip = Conv.int_of_pos p in
    let pp_res fmt = function 
      | Ok w               -> pp_word fmt U8 w
      | Error ErrAddrUndef -> pp_undef fmt (Coq_sword U8)
      | Error _            -> assert false in
    Format.fprintf fmt "@[[";
    for i = 0 to ip-2 do
      let i = Conv.z_of_int i in
      Format.fprintf fmt "%a;@ " pp_res (WArray.get p U8 t i);
    done;
    if 0 < ip then 
      pp_res fmt (WArray.get p U8 t (Conv.z_of_int (ip-1)));
    Format.fprintf fmt "]@]";
  | Vword(ws, w) -> pp_word fmt ws w
  | Vundef ty -> pp_undef fmt ty


 

      



