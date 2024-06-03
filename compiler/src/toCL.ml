open Allocation
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Compiler_util
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Inline
open Lowering
open MakeReferenceArguments
open Propagate_inline
open Remove_globals
open Utils0
open Compiler
open Utils
open Prog
open Glob_options
open Utils

let unsharp = String.map (fun c -> if c = '#' then '_' else c)

module CL = struct

  type const = Z.t

  let pp_const fmt c = Format.fprintf fmt "%s" (Z.to_string c)

  type var = Prog.var

  let pp_var fmt x =
    Format.fprintf fmt "%s_%s" (unsharp x.v_name) (string_of_uid x.v_id)

  type ty =
    | Uint of int
    | Sint of int (* Should be bigger than 1 *)
    | Bit
    | Vector of int * ty

  let rec pp_ty fmt ty =
    match ty with
    | Uint i -> Format.fprintf fmt "uint%i" i
    | Sint i -> Format.fprintf fmt "sint%i" i
    | Bit -> Format.fprintf fmt "bit"
    | Vector (i,t) -> Format.fprintf fmt "%a[%i]" pp_ty t i

  let pp_cast fmt ty = Format.fprintf fmt "%@%a" pp_ty ty

  type tyvar = var * ty

  let pp_vector fmt typ =
    match typ with
    | Vector _ -> Format.fprintf fmt "%%"
    | _ -> ()

  let pp_vvar fmt (x, ty) =
      Format.fprintf fmt "%a%a" pp_vector ty pp_var x

  let pp_tyvar fmt ((x, ty) as v) =
      Format.fprintf fmt "%a%a" pp_vvar v pp_cast ty

  let pp_tyvars fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_tyvar) xs

  let pp_tyvar2 fmt (x, ty) =
    Format.fprintf fmt "%a%a" pp_vector ty pp_var x

  let pp_tyvars2 fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_tyvar2) xs

  (* Expression over z *)

  module I = struct

    type eexp =
      | Iconst of const
      | Ivar   of tyvar
      | Iunop  of string * eexp
      | Ibinop of eexp * string * eexp
      | Ilimbs of const * eexp list

    let (!-) e1 = Iunop ("-", e1)
    let (-) e1 e2 = Ibinop (e1, "-", e2)
    let (+) e1 e2 = Ibinop (e1, "+", e2)
    let mull e1 e2 = Ibinop (e1, "*", e2)
    let power e1 e2 = Ibinop (e1, "**", e2)

    let rec pp_eexp fmt e =
      match e with
      | Iconst c    -> pp_const fmt c
      | Ivar   x    -> pp_tyvar2 fmt x
      | Iunop(s, e) -> Format.fprintf fmt "(%s %a)" s pp_eexp e
      | Ibinop (e1, s, e2) -> Format.fprintf fmt "(%a %s %a)" pp_eexp e1 s pp_eexp e2
      | Ilimbs (c, es) ->
        Format.fprintf fmt  "(limbs %a [%a])"
          pp_const c
          (pp_list ",@ " pp_eexp) es

    type epred =
      | Eeq of eexp * eexp
      | Eeqmod of eexp * eexp * eexp list

    let pp_epred fmt ep =
      match ep with
      | Eeq(e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_eexp e1 pp_eexp e2
      | Eeqmod(e1,e2, es) ->
        Format.fprintf fmt "(%a = %a (mod [%a]))"
          pp_eexp e1
          pp_eexp e2
          (pp_list ",@ " pp_eexp) es

    let pp_epreds fmt eps =
      if eps = [] then Format.fprintf fmt "true"
      else Format.fprintf fmt "/\\[@[%a@]]" (pp_list ",@ " pp_epred) eps

  end

  (* Range expression *)
  module R = struct

    type rexp =
      | Rvar   of tyvar
      | Rconst of int * const
      | Ruext of rexp * int
      | Rsext of rexp * int
      | Runop  of string * rexp
      | Rbinop of rexp * string * rexp
      | Rpreop of string * rexp * rexp
      | Rlimbs of const * rexp list
      | RVget  of rexp * int * int * const

    let const z1 z2 = Rconst(z1, z2)
    let (!-) e1 = Runop ("-", e1)
    let minu e1 e2 = Rbinop (e1, "-", e2)
    let add e1 e2 = Rbinop (e1, "+", e2)
    let mull e1 e2 = Rbinop (e1, "*", e2)
    let neg e1 = Runop ("neg", e1)
    let not e1 = Runop ("not", e1)
    let rand e1 e2 = Rbinop (e1, "&", e2)
    let ror e1 e2 = Rbinop (e1, "|", e2)
    let xor e1 e2 = Rbinop (e1, "^", e2)
    let umod e1 e2 = Rpreop ("umod", e1, e2)
    let smod e1 e2 = Rpreop ("smod", e1, e2)
    let srem e1 e2 = Rpreop ("srem", e1, e2)
    let shl e1 e2 = Rpreop ("shl", e1, e2)
    let shr e1 e2 = Rpreop ("shr", e1, e2)
    let udiv e1 e2 = Rpreop ("udiv", e1, e2)

    let rec pp_rexp fmt r =
      match r with
      | Rvar x -> pp_tyvar fmt x
      | Rconst (c1, c2) -> Format.fprintf fmt "(const %i %a)" c1 pp_const c2
      | Ruext (e, c) -> Format.fprintf fmt "(uext %a %i)" pp_rexp e c
      | Rsext (e, c) -> Format.fprintf fmt "(sext %a %i)" pp_rexp e c
      | Runop(s, e) -> Format.fprintf fmt "(%s %a)" s pp_rexp e
      | Rbinop(e1, s, e2) ->  Format.fprintf fmt "(%a %s %a)" pp_rexp e1 s pp_rexp e2
      | Rpreop(s, e1, e2) -> Format.fprintf fmt "(%s %a %a)" s pp_rexp e1 pp_rexp e2
      | Rlimbs(c, es) ->
        Format.fprintf fmt  "(limbs %a [%a])"
          pp_const c
          (pp_list ",@ " pp_rexp) es
      | RVget(e,i1,i2,c) ->
        Format.fprintf fmt  "(%a[%a])"
          pp_rexp e
          pp_const c

    type rpred =
      | RPcmp   of rexp * string * rexp
      | RPeqmod of rexp * rexp * string * rexp
      | RPnot   of rpred
      | RPand   of rpred list
      | RPor    of rpred list

    let eq e1 e2 = RPcmp (e1, "=", e2)
    let equmod e1 e2 e3 = RPeqmod (e1, e2, "umod", e3)
    let eqsmod e1 e2 e3 = RPeqmod (e1, e2, "smod", e3)
    let ult e1 e2 = RPcmp (e1, "<", e2)
    let ule e1 e2 = RPcmp (e1, "<=", e2)
    let ugt e1 e2 = RPcmp (e1, ">", e2)
    let uge e1 e2 = RPcmp (e1, ">=", e2)
    let slt e1 e2 = RPcmp (e1, "<s", e2)
    let sle e1 e2 = RPcmp (e1, "<=s", e2)
    let sgt e1 e2 = RPcmp (e1, ">s", e2)
    let sge e1 e2 = RPcmp (e1, ">=s", e2)

    let rec pp_rpred fmt rp =
      match rp with
      | RPcmp(e1, s, e2) -> Format.fprintf fmt "(%a %s %a)" pp_rexp e1 s pp_rexp e2
      | RPeqmod(e1, e2, s, e3) ->
        Format.fprintf fmt "(%a = %a (%s %a))" pp_rexp e1 pp_rexp e2 s pp_rexp e3
      | RPnot e -> Format.fprintf fmt "(~ %a)" pp_rpred e
      | RPand rps ->
        begin
          match rps with
          | [] -> Format.fprintf fmt "true"
          | [h] -> pp_rpred fmt h
          | h :: q -> Format.fprintf fmt "/\\[%a]" (pp_list ",@ " pp_rpred) rps
        end
      | RPor  rps -> Format.fprintf fmt "\\/[%a]" (pp_list ",@ " pp_rpred) rps

    let pp_rpreds fmt rps = pp_rpred fmt (RPand rps)

  end

  type clause = I.epred list * R.rpred list

  let pp_clause fmt (ep,rp) =
    Format.fprintf fmt "@[<hov 2>@[%a@] &&@ @[%a@]@]"
      I.pp_epreds ep
      R.pp_rpreds rp

  type gvar = var

  let pp_gvar fmt x =
    Format.fprintf fmt "%a@@bit :" pp_var x

  let pp_gvars fmt xs =
    Format.fprintf fmt "%a" (pp_list ",@ " pp_gvar) xs

  module Instr = struct

    type atom =
      | Aconst of const * ty
      | Avar of tyvar
      | Avecta of tyvar * int
      | Avatome of atom list

    let rec pp_atom fmt a =
      match a with
      | Aconst (c, ty) -> Format.fprintf fmt "%a%a" pp_const c pp_cast ty
      | Avar tv -> pp_tyvar fmt tv
      | Avecta (v, i) -> Format.fprintf fmt "%a[%i]" pp_vvar v i
      | Avatome al -> Format.fprintf fmt "[%a]" (pp_list ", " pp_atom) al

    type lval = tyvar

    type arg =
      | Atom of atom
      | Lval of lval
      | Const of const
      | Ty    of ty
      | Pred of clause
      | Gval of gvar

    type args = arg list

    let pp_arg fmt a =
      match a with
      | Atom a  -> pp_atom fmt a
      | Lval lv -> pp_tyvar fmt lv
      | Const c -> pp_const fmt c
      | Ty ty   -> pp_ty fmt ty
      | Pred cl -> pp_clause fmt cl
      | Gval x  -> pp_gvar fmt x

    type instr =
      { iname : string;
        iargs : args; }

    let pp_instr fmt (i : instr) =
      Format.fprintf fmt "%s %a;"
        i.iname (pp_list " " pp_arg) i.iargs

    let pp_instrs fmt (is : instr list) =
      Format.fprintf fmt "%a" (pp_list "@ " pp_instr) is

    module Op1 = struct

      let op1 iname (d : lval) (s : atom) =
        { iname; iargs = [Lval d; Atom s] }

      let mov  = op1 "mov"
      let not  = op1 "not"

    end

    module Op2 = struct

      let op2 iname (d : lval) (s1 : atom) (s2 : atom) =
        { iname; iargs = [Lval d; Atom s1; Atom s2] }

      let add  = op2  "add"
      let sub  = op2  "sub"
      let mul  = op2  "mul"
      let seteq = op2 "seteq"
      let and_  = op2 "and"
      let xor  = op2  "xor"
      let mulj = op2  "mulj"
      let setne = op2 "setne"
      let or_   = op2 "or"
      let join = op2 "join"

    end

    module Op2c = struct

      let op2c iname (d : lval) (s1 : atom) (s2 : atom) (c : tyvar) =
        { iname; iargs = [Lval d; Atom s1; Atom s2; Atom (Avar c)] }

      let adc  = op2c  "adc"
      let sbc  = op2c  "sbc"
      let sbb  = op2c  "sbb"

    end

    module Op2_2 = struct

      let op2_2 iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2] }

      let subc = op2_2 "subc"
      let mull = op2_2 "mull"
      let cmov = op2_2  "cmov"
      let adds = op2_2  "adds"
      let subb = op2_2  "subb"
      let muls = op2_2  "muls"

    end

    module Op2_2c = struct

      let op2_2c iname (d1 : lval) (d2: lval) (s1 : atom) (s2 : atom) (c : tyvar) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2; Atom (Avar c)] }

      let adcs = op2_2c "adcs"
      let sbcs = op2_2c "sbcs"
      let sbbs = op2_2c "sbbs"

    end

    module Shift = struct

      let shift iname (d : lval) (s : atom) (c : const) =
        { iname; iargs = [Lval d; Atom s; Const c] }

      let shl  = shift "shl"
      let shr  = shift "shr"
      let sar  = shift "sar"

    end

    let rec int_of_ty = function
      | Uint n -> n
      | Sint n -> n
      | Bit -> 1
      | Vector (i,t) -> i * int_of_ty t

    module ShiftV =  struct
      let shift iname (d : lval) (s : atom) (c : const) (w : int) =
        { iname; iargs = [Lval d; Atom s; Atom (Avatome
             (List.init w (fun _ -> (Aconst (c,Uint (int_of_ty (snd d) / w))))))] }
      let shl = shift "shl"
      let shr = shift "shr"
      let sar = shift "sar"
    end

    module Cshift = struct

      let cshift iname (d1 : lval) (d2 : lval) (s1 : atom) (s2 : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Atom s1; Atom s2; Const c] }

      let cshl = cshift "cshl"
      let cshr = cshift "cshr"

    end

    module Shifts =  struct

      let shifts iname (d1 : lval) (d2 : lval) (s : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Atom s; Const c] }

      let shls = shifts "shls"
      let shrs = shifts "shrs"
      let sars = shifts "sars"
      let spl = shifts "spl"
      let split = shifts "split"
      let ssplit = shifts "ssplit"

    end

    module Shift2s = struct

      let shift2s iname (d1 : lval) (d2 : lval) (d3 : lval) (s1 : atom) (s2 : atom) (c : const) =
        { iname; iargs = [Lval d1; Lval d2; Lval d3; Atom s1; Atom s2; Const c] }

      let cshls = shift2s "cshls"
      let cshrs = shift2s "cshrs"

    end

    let cast _ty (d : lval) (s : atom) =
      { iname = "cast"; iargs = [Lval d; Atom s] }

    let assert_ cl =
      { iname = "assert"; iargs = [Pred cl] }

    let cut ep rp =
      { iname = "cut"; iargs = [Pred(ep, rp)] }

    let vpc ty (d : lval) (s : atom) =
      { iname = "vpc"; iargs = [Ty ty; Lval d; Atom s] }

    let assume cl =
      { iname = "assume"; iargs  = [Pred cl] }

    let ghost (v: gvar) cl =
      { iname = "ghost";  iargs = [Gval v; Pred cl] }

    (* nondet set rcut clear ecut *)

  end

  module Proc = struct

    type proc =
      { id : string;
        formals : tyvar list;
        pre : clause;
        prog : Instr.instr list;
        post : clause;
      }

    let pp_proc fmt (proc : proc) =
      Format.fprintf fmt
        "@[<v>proc %s(@[<hov>%a@]) = @ {@[<v>@ %a@]@ }@ %a@ {@[<v>@ %a@]@ }@ @] "
        proc.id
        pp_tyvars proc.formals
        pp_clause proc.pre
        Instr.pp_instrs proc.prog
        pp_clause proc.post
  end
end

module Counter = struct
  let cpt = ref 0
  let next () = incr cpt ; !cpt
  let get () = !cpt
end

module Cfg = struct

  type node =
    { mutable nkind : CL.Instr.instr;
      mutable succs : node list;
      mutable preds: node list;
      id: int
    }

  and program = node list

  let mk_node nkind =
    let preds = [] in
    let succs = [] in
    let id = Counter.next() in
    { nkind ; succs; preds; id }

  (** Compute CFG:
      Requires to first compute all nodes, by maintaining the order of the stmt
      in the list.
  *)

  let rec update_succ node succ =
    let addSucc n  =
      node.succs <- n :: node.succs;
      n.preds <- node :: n.preds
    in
    let addOptionSucc (n: node option) =
      match n with
      | None -> ()
      | Some n' -> addSucc n'
    in
    addOptionSucc succ

  let rec cfg_node nodes next =
    match nodes with
    | [] -> assert false
    | [h] -> update_succ h next
    | h :: q ->
      update_succ h (Some (List.hd q));
      cfg_node q next

  let compute_cfg program = cfg_node program None

  let cfg_of_prog prog =
    let cfg = List.map mk_node prog in
    compute_cfg cfg;
    List.hd cfg

  let prog_of_cfg cfg =
    let rec aux node acc =
      match node.succs with
      | [] -> node.nkind::acc
      | [h] -> aux h (node.nkind::acc)
      | _ -> assert false
    in
    aux cfg []

end

(* module SimplVector = struct *)
(*   open Cfg *)
(*   open CL.Instr *)

(*   let rec find_vect_lval v i ty n  = *)
(*     match n.nkind with *)
(*     | {iname = "mov"; iargs = [Lval v ; Atom (Avar (v,Vector (i,ty)))]} -> *)
(*       assert false *)
(*     | _ -> *)
(*       begin *)
(*         match n.succs with *)
(*         | [] -> () *)
(*         | h :: [] -> find_vect_lval v i ty h *)
(*         | _ -> assert false *)
(*       end *)

(*   let rec simplvect n = *)
(*     match n.nkind with *)
(*     | {iname = "adds"; iargs = [_ ; _; Atom (Avar (v,Vector (i,ty))) ; Atom _]} -> *)
(*       assert false *)
(*     | _ -> *)
(*       begin *)
(*         match n.succs with *)
(*         | [] -> () *)
(*         | h :: [] -> simplvect h *)
(*         | _ -> assert false *)
(*       end *)
(* end *)

module I = struct

  let int_of_typ = function
    | Bty (U ws) -> Some (int_of_ws ws)
    | Bty (Bool) -> Some 1
    | Bty (Abstract ('/'::'*':: q)) -> Some (String.to_int (String.of_list q))
    | Bty (Int)  -> None
    | _ -> assert false

  let to_var x =
    let var = L.unloc x.gv in
    var, CL.Uint (Option.get (int_of_typ var.v_ty))

  let rec gexp_to_rexp e : CL.R.rexp =
    let open CL.R in
    let (!>) e = gexp_to_rexp e in
    match e with
    | Papp1 (Oword_of_int ws, Pconst z) -> Rconst(int_of_ws ws, z)
    | Papp1 (Oword_of_int ws, Pvar x) -> Rvar (L.unloc x.gv, Uint (int_of_ws ws))
    | Pvar x -> Rvar (to_var x)
    | Papp1(Oneg _, e) -> neg !> e
    | Papp1(Olnot _, e) -> not !> e
    | Papp2(Oadd _, e1, e2) -> add !> e1 !> e2
    | Papp2(Osub _, e1, e2) -> minu !> e1 !> e2
    | Papp2(Omul _, e1, e2) -> mull !> e1 !> e2
    | Papp2(Odiv (Cmp_w (Unsigned,_)), e1, e2) -> udiv !> e1 !> e2
    | Papp2(Olxor _, e1, e2) -> xor !> e1 !> e2
    | Papp2(Oland _, e1, e2) -> rand !> e1 !> e2
    | Papp2(Olor _, e1, e2) -> ror !> e1 !> e2
    | Papp2(Omod (Cmp_w (Unsigned,_)), e1, e2) -> umod !> e1 !> e2
    | Papp2(Omod (Cmp_w (Signed,_)), e1, e2) -> smod !> e1 !> e2
    | Papp2(Olsl _, e1, e2) ->  shl !> e1 !> e2
    | Papp2(Olsr _, e1, e2) ->  shr !> e1 !> e2
    | Papp1(Ozeroext (osz,isz), e1) -> Ruext (!> e1, (int_of_ws osz) - (int_of_ws isz))
    | Pabstract ({name="se_16_64"}, [v]) -> Rsext (!> v, 48)
    | Pabstract ({name="se_32_64"}, [v]) -> Rsext (!> v, 32)
    | Pabstract ({name="ze_16_64"}, [v]) -> Ruext (!> v, 48)
    | Presult (_, x) -> Rvar (to_var x)
    | _ -> assert false

  let rec gexp_to_rpred e : CL.R.rpred =
    let open CL.R in
    let (!>) e = gexp_to_rexp e in
    let (!>>) e = gexp_to_rpred e in
    match e with
    | Pbool (true) -> RPand []
    | Pbool (false) -> assert false
    | Papp1(Onot, e) -> RPnot (!>> e)
    | Papp2(Oeq _, e1, e2) -> eq !> e1 !> e2
    | Papp2(Obeq, e1, e2)  -> eq !> e1 !> e2
    | Papp2(Oand, e1, e2)  -> RPand [!>> e1; !>> e2]
    | Papp2(Oor, e1, e2)  -> RPor [!>> e1; !>> e2]
    | Papp2(Ole (Cmp_w (Signed,_)), e1, e2)  -> sle !> e1 !>e2
    | Papp2(Ole (Cmp_w (Unsigned,_)), e1, e2)  -> ule !> e1 !> e2
    | Papp2(Olt (Cmp_w (Signed,_)), e1, e2)  -> slt !> e1 !> e2
    | Papp2(Olt (Cmp_w (Unsigned,_)), e1, e2)  -> ult !> e1 !> e2
    | Papp2(Oge (Cmp_w (Signed,_)), e1, e2)  -> sge !> e1 !> e2
    | Papp2(Oge (Cmp_w (Unsigned,_)), e1, e2)  -> uge !> e1 !> e2
    | Papp2(Ogt (Cmp_w (Signed,_)), e1, e2)  -> sgt !> e1 !> e2
    | Papp2(Ogt (Cmp_w (Unsigned,_)), e1, e2)  -> ugt !> e1 !> e2
    | Pif(_, e1, e2, e3) -> RPand [RPor [RPnot !>> e1; !>> e2];RPor[ !>> e1; !>> e3]]
    | Pabstract ({name="eqsmod64"}, [e1;e2;e3]) -> eqsmod !> e1 !> e2 !> e3
    | Pabstract ({name="equmod64"}, [e1;e2;e3]) -> equmod !> e1 !> e2 !> e3
    | Pabstract ({name="eq"}, [e1;e2]) -> eq !> e1 !> e2
    | Pabstract ({name="u256_as_16u16"}, [e0;e1;e2;e3;e4;e5;e6;e7;e8;e9;e10;e11;e12;e13;e14;e15;e16]) -> 
           RPand [] (* FIX ME: INTRODUCE AN INITIAL ASSIGNMENT! *)
    | _ ->  assert false

  let rec extract_list e aux =
    match e with
    | Pabstract ({name="single"}, [h]) -> [h]
    | Pabstract ({name="pair"}, [h1;h2]) -> [h1;h2]
    | Pabstract ({name="triple"}, [h1;h2;h3]) -> [h1;h2;h3]
    | Pabstract ({name="word_nil"}, []) -> List.rev aux
    | Pabstract ({name="word_cons"}, [h;q]) -> extract_list q (h :: aux)
    | _ -> assert false

  let rec get_const x =
    match x with
    | Pconst z -> Z.to_int z
    | Papp1 (Oword_of_int _ws, x) -> get_const x
    | _ -> assert false

  let var_to_tyvar ?(sign=false) ?vector v : CL.tyvar =
    match vector with
    | None ->
      begin
        match int_of_typ v.v_ty with
        | None -> v, CL.Bit
        | Some w ->
          if sign then v, CL.Sint w
          else v, CL.Uint w
      end
    | Some (n,w) ->
      begin
        match int_of_typ v.v_ty with
        | None -> assert false
        | Some w' ->
          assert (n * w = w' && not sign);
          v, CL.Vector (n, CL.Uint w)
      end

  let mk_tmp_lval ?(name = "TMP____") ?(l = L._dummy)
      ?(kind = (Wsize.Stack Direct)) ?(sign=false)
      ?vector ty : CL.Instr.lval =
    let v = CoreIdent.GV.mk name kind ty l [] in
    var_to_tyvar ~sign ?vector v

  let mk_spe_tmp_lval ?(name = "TMP____") ?(l = L._dummy)
      ?(kind = (Wsize.Stack Direct)) ?(sign=false)
      size =
    let size = String.to_list (String.of_int size) in
    mk_tmp_lval ~name ~l ~kind ~sign (Bty(Abstract ('/'::'*':: size)))

  let rec gexp_to_eexp env e : CL.I.eexp =
    let open CL.I in
    let (!>) e = gexp_to_eexp env e in
    match e with
    | Pconst z -> Iconst z
    | Pvar x -> Ivar (to_var x)
    | Papp1 (Oword_of_int _ws, x) -> !> x
    | Papp1 (Oint_of_word _ws, x) -> !> x
    | Papp1(Oneg _, e) -> !- !> e
    | Papp2(Oadd _, e1, e2) -> !> e1 + !> e2
    | Papp2(Osub _, e1, e2) -> !> e1 - !> e2
    | Papp2(Omul _, e1, e2) -> mull !> e1 !> e2
    | Pabstract ({name="limbs"}, [h;q]) ->
      begin
        match !> h with
        | Iconst c -> Ilimbs (c, (List.map (!>) (extract_list q [])))
        | _ -> assert false
      end
    | Pabstract ({name="pow"}, [b;e]) -> power !> b !> e
    | Pabstract ({name="mon"}, [c;a;b]) ->
      let c = get_const c in
      let v =
        match Hash.find env c with
        | exception Not_found ->
          let name = "X" ^ "_" ^ string_of_int c in
          let x =
            mk_tmp_lval ~name (Bty Int)
          in
          Hash.add env c x;
          x
        | x -> x
      in
      mull !> b (power (Ivar v) !> a)
    | _ -> assert false

  let rec gexp_to_epred env e :CL.I.epred list =
    let open CL.I in
    let (!>) e = gexp_to_eexp env e in
    let (!>>) e = gexp_to_epred env e in
    match e with
    | Papp2(Oeq _, e1, e2)  -> [Eeq (!> e1, !> e2)]
    | Papp2(Oand, e1, e2)  -> !>> e1 @ !>> e2
    | Pabstract ({name="eqmod"} as _opa, [h1;h2;h3]) ->
      [Eeqmod (!> h1, !> h2, List.map (!>) (extract_list h3 []))]
    | _ -> assert false

  let glval_to_lval x : CL.Instr.lval =
    match x with
    | Lvar v -> var_to_tyvar (L.unloc v)
    | Lnone (l,ty)  ->
      let name = "NONE____" in
      mk_tmp_lval ~name ~l ty
    | Lmem _ | Laset _ | Lasub _ -> assert false

  let gexp_to_var x : CL.tyvar =
    match x with
    | Pvar x -> var_to_tyvar (L.unloc x.gv)
    | _ -> assert false

  let gexp_to_const x : CL.const * CL.ty =
    match x with
    | Papp1 (Oword_of_int ws, Pconst c) -> (c, CL.Uint (int_of_ws ws))
    | _ -> assert false

  let mk_const c : CL.const = Z.of_int c

  let mk_const_atome ws c = CL.Instr.Aconst (c, CL.Uint ws)

  let gexp_to_atome x : CL.Instr.atom =
    match x with
    | Pvar _ -> Avar (gexp_to_var x)
    | Papp1 (Oword_of_int _, Pconst _) ->
      let c,ty = gexp_to_const x in
      Aconst (c,ty)
    | _ -> assert false

  let mk_lval_atome (lval: CL.Instr.lval) = CL.Instr.Avar (lval)
end

let rec power acc n = match n with | 0 -> acc | n -> power (acc * 2) (n - 1)

module type BaseOp = sig
  type op
  type extra_op

  type trans =
    | Cas1
    | Cas2
    | Cas3
    | Smt

  val op_to_instr :
    trans ->
    int Prog.glval list ->
    op -> int Prog.gexpr list -> CL.Instr.instr list

  val assgn_to_instr :
    trans ->
    int Prog.glval -> int Prog.gexpr -> CL.Instr.instr list

end

module X86BaseOp : BaseOp
  with type op = X86_instr_decl.x86_op
  with type extra_op = X86_extra.x86_extra_op
= struct

  type op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op

  type trans =
    | Cas1
    | Cas2
    | Cas3
    | Smt

  let cast_atome ws x =
    match x with
    | Pvar va ->
      let ws_x = ws_of_ty (L.unloc va.gv).v_ty in
      if ws = ws_x then I.gexp_to_atome x,[]
      else
        let e = I.gexp_to_atome x in
        let v = L.unloc va.gv in
        let kind = v.v_kind in
        let (_,ty) as x = I.mk_tmp_lval ~kind (CoreIdent.tu ws) in
        CL.Instr.Avar x, [CL.Instr.cast ty x e]
    | Papp1 (Oword_of_int ws_x, Pconst z) ->
      if ws = ws_x then I.gexp_to_atome x,[]
      else
        let e = I.gexp_to_atome x in
        let (_,ty) as x = I.mk_tmp_lval (CoreIdent.tu ws) in
        CL.Instr.Avar x, [CL.Instr.cast ty x e]
    | _ -> assert false

  let (!) e = I.mk_lval_atome e

  let cast_vector_atome ws v x =
    let a,i = cast_atome ws x in
    let a1 = CL.Instr.Avatome [a] in
    let v = int_of_velem v in
    let s = int_of_ws ws in
    let l_tmp = I.mk_tmp_lval ~vector:(1,s) (CoreIdent.tu ws) in
    let l_tmp2 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
    let ty = CL.(Vector (v, Uint (s/v))) in
    CL.Instr.Avar l_tmp2,
    i @ [CL.Instr.Op1.mov l_tmp a1;
         CL.Instr.cast ty l_tmp2 !l_tmp;
        ]

  let cast_atome_vector ws v x l =
    let s = int_of_ws ws in
    let l_tmp = I.mk_tmp_lval ~vector:(1,s) (CoreIdent.tu ws) in
    let ty = CL.(Vector (v, Uint s)) in
    let a = CL.Instr.Avecta (l_tmp, 0) in
    [CL.Instr.cast ty l_tmp x;
     CL.Instr.Op1.mov l a
    ]

  let assgn_to_instr trans x e =
    let a = I.gexp_to_atome e in
    let l = I.glval_to_lval x in
    [CL.Instr.Op1.mov l a]

  let op_to_instr trans xs o es =
    match o with
    | X86_instr_decl.MOV ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      i @ [CL.Instr.Op1.mov l a]

    | ADD ws ->
      begin
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | Smt ->
          i1 @ i2 @ [CL.Instr.Op2.add l a1 a2]
        | Cas1 ->
          let l_tmp = I.mk_spe_tmp_lval 1 in
          i1 @ i2 @ [CL.Instr.Op2_2.adds l_tmp l a1 a2]
        | _ -> assert false
      end

    | SUB ws ->
      begin
        let a1, i1 = cast_atome ws (List.nth es 0) in
        let a2, i2 = cast_atome ws (List.nth es 1) in
        let l = I.glval_to_lval (List.nth xs 5) in
        match trans with
        | Smt ->
          i1 @ i2 @ [CL.Instr.Op2.sub l a1 a2]
        | Cas1 ->
          let l_tmp = I.mk_spe_tmp_lval 1 in
          i1 @ i2 @ [CL.Instr.Op2_2.subb l_tmp l a1 a2]
        | _ -> assert false
      end

    | IMULr ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l a1 a2]

    | IMULri ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l a1 a2]

    | ADC ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 1) in
      let l2 = I.glval_to_lval (List.nth xs 5) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.adcs l1 l2 a1 a2 v]

    | SBB ws ->
      let a1, i1 = cast_atome ws (List.nth es 0) in
      let a2, i2 = cast_atome ws (List.nth es 1) in
      let l1 = I.glval_to_lval (List.nth xs 1) in
      let l2 = I.glval_to_lval (List.nth xs 5) in
      let v = I.gexp_to_var (List.nth es 2) in
      i1 @ i2 @ [CL.Instr.Op2_2c.sbbs l1 l2 a1 a2 v]

    | NEG ws ->
      let a1 = I.mk_const_atome (int_of_ws ws) Z.zero in
      let a2,i2 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i2 @ [CL.Instr.Op2.sub l a1 a2]

    | INC ws ->
      let a1 = I.mk_const_atome (int_of_ws ws) Z.one in
      let a2,i2 = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 4) in
      let l_tmp = I.mk_spe_tmp_lval 1 in
      i2 @ [CL.Instr.Op2_2.adds l_tmp l a1 a2] (* should we account for overflow in increment? *)

    | DEC ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2 = I.mk_const_atome (int_of_ws ws) Z.one in
      let l = I.glval_to_lval (List.nth xs 4) in
      let l_tmp = I.mk_spe_tmp_lval 1 in
      i1 @ [CL.Instr.Op2_2.subb l_tmp l a1 a2] (* should we account for underflow in decrement? *)

    | AND ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.and_ l a1 a2]

    | ANDN ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l_tmp = I.mk_tmp_lval (CoreIdent.tu ws) in
      let at = I.mk_lval_atome l_tmp in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op1.not l_tmp a1; CL.Instr.Op2.and_ l a2 at]

    | OR ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.or_ l a1 a2]

    | XOR ws ->
      let a1,i1 = cast_atome ws (List.nth es 0) in
      let a2,i2 = cast_atome ws (List.nth es 1) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i1 @ i2 @ [CL.Instr.Op2.xor l a1 a2]

    | NOT ws ->
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 5) in
      i @ [CL.Instr.Op1.not l a]

    | SHL ws ->
      begin
        match trans with
        | Smt ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.Shift.shl l a c]
        | Cas1 ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const (List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval (Z.to_int c) in
          i @ [CL.Instr.Shifts.shls l_tmp l a c]
        | _ -> assert false
      end

    | SHR ws ->
      begin
        match trans with
        | Smt ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.Shift.shr l a c]
        | Cas1 ->
          let a, i = cast_atome ws (List.nth es 0) in
          let (c,_) = I.gexp_to_const (List.nth es 1) in
          let l = I.glval_to_lval (List.nth xs 5) in
          let l_tmp = I.mk_spe_tmp_lval (Z.to_int c) in
          i @ [CL.Instr.Shifts.shrs l l_tmp a c]
        | _ -> assert false
      end

    | SAR ws ->
      begin
        match trans with
        | Smt ->
          let a,i = cast_atome ws (List.nth es 0) in
          let sign = true in
          let l_tmp1 = I.mk_tmp_lval ~sign (CoreIdent.tu ws) in
          let ty1 = CL.Sint (int_of_ws ws) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let l_tmp2 = I.mk_tmp_lval ~sign (CoreIdent.tu ws) in
          let l_tmp3 = I.mk_tmp_lval (CoreIdent.tu ws) in
          let ty2 = CL.Uint (int_of_ws ws) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.Shifts.ssplit l_tmp2 l_tmp3 !l_tmp1 c;
               CL.Instr.cast ty2 l !l_tmp2]
        | Cas1 ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome c Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval (c + 1) in
          let a3 = I.mk_const_atome (c + 1) (Z.of_int (power 1 (c + 1) - 1)) in
          let l_tmp4 = I.mk_spe_tmp_lval (c + 1) in
          let l_tmp5 = I.mk_spe_tmp_lval (c + int_of_ws ws) in
          let c2 = Z.of_int c in
          let l_tmp6 = I.mk_spe_tmp_lval c in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Op2.join l_tmp5 !l_tmp4 !l_tmp2;
                CL.Instr.Shifts.spl l l_tmp6 !l_tmp5 c2
               ]
        | Cas2 ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome (c -1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval c in
          let a3 = I.mk_const_atome c (Z.of_int (power 1 c - 1)) in
          let l_tmp4 = I.mk_spe_tmp_lval c in
          let l_tmp5 = I.mk_spe_tmp_lval c in
          let c2 = Z.of_int c in
          let l_tmp6 = I.mk_spe_tmp_lval (int_of_ws ws - c) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Shifts.spl l_tmp6 l_tmp5 a1 c2;
                CL.Instr.Op2.join l !l_tmp4 !l_tmp6;
               ]
        | Cas3 ->
          let a1,i1 = cast_atome ws (List.nth es 0) in
          let c1 = I.mk_const (int_of_ws ws - 1) in
          let l_tmp = I.mk_spe_tmp_lval (int_of_ws ws) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws - 1) in
          let c = I.get_const (List.nth es 1) in
          let a2 = I.mk_const_atome (c -1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval c in
          let a3 = I.mk_const_atome c (Z.of_int (power 1 c - 1)) in
          let l_tmp4 = I.mk_spe_tmp_lval c in
          let l_tmp5 = I.mk_spe_tmp_lval c in
          let c2 = Z.of_int c in
          let c3 = Z.of_int (power 1 c) in
          let l_tmp6 = I.mk_spe_tmp_lval (int_of_ws ws - c) in
          let l = I.glval_to_lval (List.nth xs 5) in
          i1 @ [CL.Instr.Op1.mov l_tmp a1;
                CL.Instr.assert_ ([Eeqmod(Ivar l_tmp, Iconst Z.zero,[Iconst c3])] ,[]);
                CL.Instr.Shifts.spl l_tmp1 l_tmp2 a1 c1;
                CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
                CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
                CL.Instr.Shifts.spl l_tmp6 l_tmp5 a1 c2;
                CL.Instr.assume ([Eeq(Ivar l_tmp5, Iconst Z.zero)] ,[]);
                CL.Instr.Op2.join l !l_tmp4 !l_tmp6;
               ]
      end

    | MOVSX (ws1, ws2) ->
      begin
        match trans with
        | Smt ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let sign = true in
          let l_tmp1 = I.mk_tmp_lval ~sign (CoreIdent.tu ws2) in
          let ty1 = CL.Sint (int_of_ws ws2) in
          let l_tmp2 = I.mk_tmp_lval ~sign (CoreIdent.tu ws1) in
          let ty2 = CL.Sint (int_of_ws ws1) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let ty3 = CL.Uint (int_of_ws ws1) in
          i @ [CL.Instr.cast ty1 l_tmp1 a;
               CL.Instr.cast ty2 l_tmp2 !l_tmp1;
               CL.Instr.cast ty3 l !l_tmp2]
        | Cas1 ->
          let a,i = cast_atome ws2 (List.nth es 0) in
          let c = Z.of_int (int_of_ws ws2 - 1) in
          let l_tmp1 = I.mk_spe_tmp_lval 1 in
          let l_tmp2 = I.mk_spe_tmp_lval (int_of_ws ws2 - 1) in
          let diff = int_of_ws ws1 - (int_of_ws ws2) in
          let a2 = I.mk_const_atome (diff - 1) Z.zero in
          let l_tmp3 = I.mk_spe_tmp_lval diff in
          let a3 =
            I.mk_const_atome diff (Z.of_int ((power 1 diff) - 1))
          in
          let l_tmp4 = I.mk_spe_tmp_lval diff in
          let l = I.glval_to_lval (List.nth xs 0) in
          i @ [CL.Instr.Shifts.spl l_tmp1 l_tmp2 a c;
               CL.Instr.Op2.join l_tmp3 a2 !l_tmp1;
               CL.Instr.Op2.mul l_tmp4 !l_tmp3 a3;
               CL.Instr.Op2.join l !l_tmp4 a;
              ]
        | _ -> assert false
      end
    | MOVZX (ws1, ws2) ->
      let a,i = cast_atome ws2 (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let ty = CL.Uint (int_of_ws ws1) in
      i @ [CL.Instr.cast ty l a]

    | VPADD (v,ws) ->
      begin
      let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws v (List.nth es 1) in
      let v = int_of_velem v in
      let s = int_of_ws ws in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      match trans with
        | Smt ->
          i1 @ i2 @ [CL.Instr.Op2.add l_tmp a1 a2] @ i3
        | Cas1 ->
          let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          i1 @ i2 @ [CL.Instr.Op2_2.adds l_tmp1 l_tmp a1 a2] @ i3
        | _ -> assert false
      end
    |SETcc -> assert false
    |CLC -> assert false
    |STC -> assert false
    |VBROADCASTI128 -> assert false
    |VEXTRACTI128 -> assert false
    |VINSERTI128 -> assert false
    |VPERM2I128 -> assert false
    |VPERMD -> assert false
    |VPERMQ -> assert false
    |VMOVLPD -> assert false
    |VMOVHPD -> assert false
    |CLFLUSH -> assert false
    |LFENCE -> assert false
    |MFENCE -> assert false
    |SFENCE -> assert false
    |AESDEC -> assert false
    |VAESDEC -> assert false
    |AESDECLAST -> assert false
    |VAESDECLAST -> assert false
    |AESENC -> assert false
    |VAESENC -> assert false
    |AESENCLAST -> assert false
    |VAESENCLAST -> assert false
    |AESIMC -> assert false
    |VAESIMC -> assert false
    |AESKEYGENASSIST -> assert false
    |VAESKEYGENASSIST -> assert false
    |PCLMULQDQ -> assert false
    |CMOVcc _ -> assert false
    |MUL _ -> assert false
    |IMUL _ -> assert false
    |DIV _ -> assert false
    |IDIV _ -> assert false
    |CQO _ -> assert false
    |LZCNT _ -> assert false
    |BT _ -> assert false
    |LEA _ -> assert false
    |TEST _ -> assert false
    |CMP _ -> assert false
    |ROR _ -> assert false
    |ROL _ -> assert false
    |RCR _ -> assert false
    |RCL _ -> assert false
    |SAL _ -> assert false
    |SHLD _ -> assert false
    |SHRD _ -> assert false
    |MULX_lo_hi _ -> assert false
    |ADCX _ -> assert false
    |ADOX _ -> assert false
    |BSWAP _ -> assert false
    |POPCNT _ -> assert false
    |PEXT _ -> assert false
    |PDEP _ -> assert false
    |MOVX _ -> assert false
    |MOVD _ -> assert false
    |VMOV _ -> assert false
    |VMOVDQA _ -> assert false
    |VMOVDQU ws ->       
      let a,i = cast_atome ws (List.nth es 0) in
      let l = I.glval_to_lval (List.nth xs 0) in
      i @ [CL.Instr.Op1.mov l a]
    |VPMOVSX _ -> assert false
    |VPMOVZX _ -> assert false
    |VPAND ws ->
      let a1,i1 = cast_vector_atome ws VE16 (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws VE16 (List.nth es 1) in
      let s = int_of_ws ws in
      let v = s / 16 in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
          i1 @ i2 @ [CL.Instr.Op2.and_ l_tmp a1 a2] @ i3
    |VPANDN _ -> assert false
    |VPOR _ -> assert false
    |VPXOR _ -> assert false
    |VPSUB (v,ws) ->
      begin
      let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws v (List.nth es 1) in
      let v = int_of_velem v in
      let s = int_of_ws ws in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      match trans with
        | Smt ->
          i1 @ i2 @ [CL.Instr.Op2.sub l_tmp a1 a2] @ i3
        | Cas1 ->
          let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          i1 @ i2 @ [CL.Instr.Op2_2.subb l_tmp1 l_tmp a1 a2] @ i3
        | _ -> assert false
      end
    |VPAVG _ -> assert false
    |VPMULL (v,ws) ->
      let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws v (List.nth es 1) in
      let v = int_of_velem v in
      let s = int_of_ws ws in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp1 l_tmp a1 a2] @ i3
    |VPMULH ws ->
      let a1,i1 = cast_vector_atome ws VE16 (List.nth es 0) in
      let a2,i2 = cast_vector_atome ws VE16 (List.nth es 1) in
      let s = int_of_ws ws in
      let v = s / 16 in
      let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      let l = I.glval_to_lval (List.nth xs 0) in
      let i3 = cast_atome_vector ws v !l_tmp l in
      let l_tmp1 = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
      i1 @ i2 @ [CL.Instr.Op2_2.mull l_tmp l_tmp1 a1 a2] @ i3
    |VPMULHU _ -> assert false
    |VPMULHRS _ -> assert false
    |VPMUL _ -> assert false
    |VPMULU _ -> assert false
    |VPEXTR _ -> assert false
    |VPINSR _ -> assert false
    |VPSLL (v,ws) -> 
      begin
      match trans with
        | Smt ->
          let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let v = int_of_velem v in
          let s = int_of_ws ws in
          let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let i3 = cast_atome_vector ws v !l_tmp l in
          i1 @ [CL.Instr.ShiftV.shl l_tmp a1 c v] @ i3
        | _ -> assert false
      end
    |VPSRL (v,ws) ->
      begin
      match trans with
        | Smt ->
          let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let v = int_of_velem v in
          let s = int_of_ws ws in
          let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let i3 = cast_atome_vector ws v !l_tmp l in
          i1 @ [CL.Instr.ShiftV.shr l_tmp a1 c v] @ i3
        | _ -> assert false
      end
    |VPSRA (v,ws) ->
      begin
      match trans with
        | Smt ->
          let a1,i1 = cast_vector_atome ws v (List.nth es 0) in
          let (c,_) = I.gexp_to_const(List.nth es 1) in
          let v = int_of_velem v in
          let s = int_of_ws ws in
          let l_tmp = I.mk_tmp_lval ~vector:(v,s/v) (CoreIdent.tu ws) in
          let l = I.glval_to_lval (List.nth xs 0) in
          let i3 = cast_atome_vector ws v !l_tmp l in
          i1 @ [CL.Instr.ShiftV.sar l_tmp a1 c v] @ i3
        | _ -> assert false
      end
    |VPSLLV _ -> assert false
    |VPSRLV _ -> assert false
    |VPSLLDQ _ -> assert false
    |VPSRLDQ _ -> assert false
    |VPSHUFB _ -> assert false
    |VPSHUFD _ -> assert false
    |VPSHUFHW _ -> assert false
    |VPSHUFLW _ -> assert false
    |VPBLEND _ -> assert false
    |VPBLENDVB _ -> assert false
    |VPACKUS _ -> assert false
    |VPACKSS _ -> assert false
    |VSHUFPS _ -> assert false
    |VPBROADCAST _ -> assert false
    |VMOVSHDUP _ -> assert false
    |VMOVSLDUP _ -> assert false
    |VPALIGNR _ -> assert false
    |VPUNPCKH _ -> assert false
    |VPUNPCKL _ -> assert false
    |VPMOVMSKB _ -> assert false
    |VPCMPEQ _ -> assert false
    |VPCMPGT _ -> assert false
    |VPMADDUBSW _ -> assert false
    |VPMADDWD _ -> assert false
    |VPMINU _ -> assert false
    |VPMINS _ -> assert false
    |VPMAXU _ -> assert false
    |VPMAXS _ -> assert false
    |VPTEST _ -> assert false
    |RDTSC _ -> assert false
    |RDTSCP _ -> assert false
    |VPCLMULQDQ _ -> assert false
    | _ -> assert false
end

module ARMBaseOp : BaseOp
  with type op = Arm_instr_decl.arm_op
   and  type extra_op = Arm_extra.__
= struct

  open Arm_instr_decl

  type op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.__

  type trans =
    | Cas1
    | Cas2
    | Cas3
    | Smt

  let ws = Wsize.U32

  let assgn_to_instr trans x e = assert false

  let op_to_instr trans xs o es =
    let mn, opt = match o with Arm_instr_decl.ARM_op (mn, opt) -> mn, opt in
    match mn with
    | ADD -> assert false
(*
      let v1 = pp_cast fmt (List.nth es 0, ws) in
      let v2 = pp_cast fmt (List.nth es 1, ws) in
      let v2' = pp_shifted fmt opt v2 es in
      Format.fprintf fmt "add %a %a %a"
        pp_lval (List.nth xs 5, int_of_ws ws)
        pp_atome (v1, int_of_ws ws)
        pp_atome (v2', int_of_ws ws)
*)

    | ADC
    | MUL
    | MLA
    | MLS
    | SDIV
    | SUB
    | RSB
    | UDIV
    | UMULL
    | UMAAL
    | UMLAL
    | SMULL
    | SMLAL
    | SMMUL
    | SMMULR
    | SMUL_hw _
    | SMLA_hw _
    | SMULW_hw _
    | AND
    | BFC
    | BFI
    | BIC
    | EOR
    | MVN
    | ORR
    | ASR
    | LSL
    | LSR
    | ROR
    | REV
    | REV16
    | REVSH
    | ADR
    | MOV
    | MOVT
    | UBFX
    | UXTB
    | UXTH
    | SBFX
    | CLZ
    | CMP
    | TST
    | CMN
    | LDR
    | LDRB
    | LDRH
    | LDRSB
    | LDRSH
    | STR
    | STRB
    | STRH -> assert false

end

let sub_fun_return r =
  let aux f = List.map (fun (prover,clause) -> prover, f clause) in
  let aux1 i v =
    match snd (List.findi (fun ii _ -> ii = i) r) with
    | Lvar v -> {gv = v; gs = Expr.Slocal}
    | _ -> assert false
  in
  aux (Subst.subst_result aux1)

let sub_fun_param args params =
  let aux f =
    List.map (fun (prover,clause) -> prover, f clause)
  in
  let check v vi=
    (L.unloc v.gv).v_name = vi.v_name && (L.unloc v.gv).v_id = vi.v_id
  in
  let aux1 v =
    match fst (List.findi (fun _ vi -> check v vi) args) with
    | i -> snd (List.findi (fun ii _ -> ii = i) params)
    | exception _ -> Pvar v
  in
  aux (Subst.gsubst_e (fun x -> x) aux1)

module Mk(O:BaseOp) = struct

  let pp_ext_op xs o es trans =
    match o with
    | Arch_extra.BaseOp (_, o) -> O.op_to_instr trans xs o es
    | Arch_extra.ExtOp o -> assert false

  let pp_sopn xs o es tcas =
    match o with
    | Sopn.Opseudo_op _ -> assert false
    | Sopn.Oslh _ -> assert false
    | Sopn.Oasm o -> pp_ext_op xs o es tcas

  let rec filter_clause cs (cas,smt) =
    match cs with
    | [] -> cas,smt
    | (Expr.Cas,c)::q -> filter_clause q (c::cas,smt)
    | (Expr.Smt,c)::q -> filter_clause q (cas,c::smt)

  let to_smt smt =
    List.fold_left (fun acc a -> I.gexp_to_rpred a ::  acc) [] smt

  let to_cas env cas =
    List.fold_left (fun acc a -> I.gexp_to_epred env a  @ acc) [] cas

  let to_clause env clause : CL.clause =
    let cas,smt = filter_clause clause ([],[]) in
    let smt = to_smt smt in
    let cas = to_cas env cas in
    (cas,smt)

  let pp_i env fds i =
    let l = ["smt", O.Smt ; "cas", Cas1; "cas2", Cas2; "cas3", Cas3 ] in
    let mk_trans = Annot.filter_string_list None l in
    let atran annot =
      match Annot.ensure_uniq1 "tran" mk_trans annot with
      | None -> O.Cas1
      | Some aty -> aty
    in
    let trans = atran i.i_annot in
    match i.i_desc with
    | Cassert (t, p, e) ->
      let cl = to_clause env [(p,e)] in
      begin
        match t with
        | Expr.Assert -> [], [CL.Instr.assert_ cl]
        | Expr.Assume -> [], [CL.Instr.assume cl]
        | Expr.Cut -> assert false
      end
    | Csyscall _ | Cif _ | Cfor _ | Cwhile _ -> assert false
    | Ccall (r,f,params) ->
      let fd = List.find (fun fd -> fd.f_name.fn_id = f.fn_id) fds in
      let pre = sub_fun_param fd.f_args params fd.f_contra.f_pre in
      let post = sub_fun_param fd.f_args params fd.f_contra.f_post in
      let post =  sub_fun_return r post in
      let pre_cl = to_clause env pre in
      let post_cl = to_clause env post in
      r , [CL.Instr.assert_ pre_cl] @  [CL.Instr.assume post_cl]

    | Cassgn (a, _, _, e) ->
      begin
        match a with
        | Lvar x -> [], O.assgn_to_instr trans a e
        | Lnone _ | Lmem _ | Laset _ |Lasub _ -> assert false
      end
    | Copn(xs, _, o, es) -> [], pp_sopn xs o es trans

  let pp_c env fds c =
    List.fold_left (fun (acc1,acc2) a ->
        let l1,l2 = pp_i env fds a in
        acc1 @ l1, acc2 @ l2
      ) ([],[]) c

  let filter_add cond l1 l2 =
    List.fold_left (
        fun l a ->
          if List.exists (cond a) l
          then l else a :: l
      ) l1 l2

  let fun_to_proc fds fd =
    let env = Hash.create 10 in
    let ret = List.map L.unloc fd.f_ret in
    let cond a x = (x.v_name = a.v_name) && (x.v_id = a.v_id) in
    let args = filter_add cond fd.f_args ret in
    let formals = List.map I.var_to_tyvar args in
    let pre = to_clause env fd.f_contra.f_pre in
    let post = to_clause env fd.f_contra.f_post in
    let lval,prog = pp_c env fds fd.f_body in
    let formals_lval = List.map I.glval_to_lval lval in
    let cond (a,_) (x,_) = (x.v_name = a.v_name) && (x.v_id = a.v_id) in
    let formals = filter_add cond formals formals_lval in
    let ghost = ref [] in
    Hash.iter (fun _ x -> ghost := x :: ! ghost) env;
    let formals = filter_add cond formals !ghost in

    (* let cfg = Cfg.cfg_of_prog prog in *)
    (* let prog = Cfg.prog_of_cfg cfg in *)

    CL.Proc.{id = fd.f_name.fn_name;
             formals;
             pre;
             prog;
             post}
end
