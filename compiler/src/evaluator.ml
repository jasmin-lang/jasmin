open BinNums
open Utils0 
open Type
open Warray_
open Low_memory
open Expr
open Sem
open Values
open Varmap

exception Eval_error of instr_info * Utils0.error 

let pp_error fmt err =
  let msg = 
    match err with
    | ErrOob -> "out_of_bound"
    | ErrAddrUndef -> "undefined address"
    | ErrAddrInvalid -> "invalid address"
    | ErrStack -> "stack error"
    | ErrType  -> "type error" in
  Format.fprintf fmt "%s" msg

let exn_exec (ii:instr_info) (r: 't exec) = 
  match r with
  | Ok r -> r
  | Error e -> raise (Eval_error(ii, e))

let of_val_z ii v : coq_Z = 
  Obj.magic (exn_exec ii (of_val Coq_sint v))

let of_val_b ii v : bool = 
  Obj.magic (exn_exec ii (of_val Coq_sbool v))

(* ----------------------------------------------------------------- *)
type 'asm stack = 
  | Sempty of instr_info * 'asm fundef
  | Scall of 
      instr_info * 'asm fundef * lval list * Vmap.t * 'asm instr list * 'asm stack
  | Sfor of instr_info * var_i * coq_Z list * 'asm instr list * 'asm instr list * 'asm stack

type ('syscall_state, 'asm) state =
  { s_prog : 'asm prog;
    s_cmd  : 'asm instr list;
    s_estate : 'syscall_state estate;
    s_stk  : 'asm stack;
  }

exception Final of Memory.mem * values

let return pd (sc_sem: 'syscall_state Syscall.syscall_sem) s =
  assert (s.s_cmd = []);
  match s.s_stk with
  | Sempty(ii, f) ->
    let s2 = s.s_estate in
    let m2 = s2.emem and vm2 = s2.evm in
    let vres = 
      List.map (fun (x:var_i) -> Vmap.get_var vmr_eq vm2 x.v_var) f.f_res in
    let vres' = exn_exec ii (mapM2 ErrType truncate_defined_val f.f_tyout vres) in
    raise (Final(m2, vres'))
    
  | Scall(ii,f,xs,vm1,c,stk) ->
    let gd = s.s_prog.p_globs in
    let {escs = scs2; emem = m2; evm = vm2} = s.s_estate in
    let vres = 
      List.map (fun (x:var_i) -> Vmap.get_var vmr_eq vm2 x.v_var) f.f_res in
    let vres' = exn_exec ii (mapM2 ErrType truncate_defined_val f.f_tyout vres) in
    let s1 = exn_exec ii (write_lvals pd sc_sem gd {escs = scs2; emem = m2; evm = vm1 } xs vres') in
    { s with 
      s_cmd = c;
      s_estate = s1;
      s_stk = stk }

  | Sfor(ii,i,ws,body,c,stk) ->
    match ws with
    | [] -> { s with s_cmd = c; s_stk = stk }
    | w::ws ->
      let s1 = exn_exec ii (write_var pd sc_sem i (Vint w) s.s_estate) in
      { s with s_cmd = body;
               s_estate = s1;
               s_stk = Sfor(ii, i, ws, body, c, stk) }

let small_step1 pd (sc_sem: 'syscall_state Syscall.syscall_sem) asmOp s =
  match s.s_cmd with
  | [] -> return pd sc_sem s
  | i :: c ->
    let MkI(ii,ir) = i in
    let gd = s.s_prog.p_globs in
    let s1 = s.s_estate in
    match ir with

    | Cassgn(x,_,ty,e) ->
      let v  = exn_exec ii (sem_pexpr pd sc_sem gd s1 e) in
      let v' = exn_exec ii (truncate_defined_val ty v) in
      let s2 = exn_exec ii (write_lval pd sc_sem gd x v' s1) in
      { s with s_cmd = c; s_estate = s2 }

    | Copn(xs,_,op,es) ->
      let s2 = exn_exec ii (sem_sopn pd sc_sem asmOp gd op s1 xs es) in
      { s with s_cmd = c; s_estate = s2 }

    | Csyscall(xs,o, es) ->
        let ves = exn_exec ii (sem_pexprs pd sc_sem gd s1 es) in
        let ((scs, m), vs) = exn_exec ii (exec_syscall pd sc_sem s1.escs s1.emem o ves) in
        let s2 = exn_exec ii (write_lvals pd sc_sem gd {escs = scs; emem = m; evm = s1.evm} xs vs) in
      { s with s_cmd = c; s_estate = s2 }

    | Cif(e,c1,c2) ->
      let b = of_val_b ii (exn_exec ii (sem_pexpr pd sc_sem gd s1 e)) in
      let c = (if b then c1 else c2) @ c in
      { s with s_cmd = c }

    | Cfor (i,((d,lo),hi), body) ->
      let vlo = of_val_z ii (exn_exec ii (sem_pexpr pd sc_sem gd s1 lo)) in
      let vhi = of_val_z ii (exn_exec ii (sem_pexpr pd sc_sem gd s1 hi)) in
      let rng = wrange d vlo vhi in
      let s =
        {s with s_cmd = []; s_stk = Sfor(ii, i, rng, body, c, s.s_stk) } in
      return pd sc_sem s
 
    | Cwhile (_, c1, e, c2) ->
      { s with s_cmd = c1 @ MkI(ii, Cif(e, c2@[i],[])) :: c }

    | Ccall(_,xs,fn,es) ->
      let vargs' = exn_exec ii (sem_pexprs pd sc_sem gd s1 es) in
      let f = 
        match get_fundef s.s_prog.p_funcs fn with
        | Some f -> f
        | None -> assert false in
      let vargs = exn_exec ii (mapM2 ErrType truncate_defined_val f.f_tyin vargs') in
      let {escs; emem = m1; evm = vm1}  = s1 in
      let stk = Scall(ii,f, xs, vm1, c, s.s_stk) in
      let sf = 
        exn_exec ii (write_vars pd sc_sem f.f_params vargs {escs; emem = m1; evm = Vmap.empty vmr_eq }) in
      {s with s_cmd = f.f_body;
              s_estate = sf;
              s_stk = stk }


let rec small_step pd sc_sem asmOp s =
  small_step pd sc_sem asmOp (small_step1 pd sc_sem asmOp s)

let init_state scs0 p fn m =
  let f = 
    match get_fundef p.p_funcs fn with
    | Some f -> f
    | None -> assert false in
  assert (f.f_tyin = []);
  { s_prog = p;
    s_cmd = f.f_body;
    s_estate = {escs = scs0; emem = m; evm = Vmap.empty vmr_eq };
    s_stk = Sempty(dummy_instr_info, f) }


let exec pd sc_sem asmOp scs0 p fn m =
  let s = init_state scs0 p fn m in
  try small_step pd sc_sem asmOp s
  with Final(m,vs) -> m, vs 

(* ----------------------------------------------------------- *)
let pp_undef fmt ty = 
  Format.fprintf fmt "undef<%a>" Printer.pp_ty (Conv.ty_of_cty ty)
 
let pp_word fmt ws w = 
  let z = Word0.wunsigned ws w in
  let z = Conv.z_of_cz z in
  Printer.pp_print_X fmt z
  
let pp_val fmt v = 
  match v with
  | Vbool b -> Format.fprintf fmt "%b" b
  | Vint z  -> Format.fprintf fmt "%a" Z.pp_print (Conv.z_of_cz z)
  | Varr(p,t) ->
    let ip = Conv.int_of_pos p in
    let pp_res fmt = function 
      | Ok w               -> pp_word fmt U8 w
      | Error ErrAddrUndef -> pp_undef fmt (Coq_sword U8)
      | Error _            -> assert false in
    Format.fprintf fmt "@[[";
    for i = 0 to ip-2 do
      let i = Conv.cz_of_int i in
      Format.fprintf fmt "%a;@ " pp_res (WArray.get p AAscale U8 t i);
    done;
    if 0 < ip then 
      pp_res fmt (WArray.get p AAscale U8 t (Conv.cz_of_int (ip-1)));
    Format.fprintf fmt "]@]";
  | Vword(ws, w) -> pp_word fmt ws w
  | Vundef ty -> pp_undef fmt ty


 

      



