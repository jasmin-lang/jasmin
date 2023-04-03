open Jasmin
open Prog
open Apron
open Wsize

module Config = SafetyConfig  


(*-------------------------------------------------------------------------*)
(* TODO: fix [ToEC.ty_expr] and use it here instead*)
let rec ty_expr = function
  | Psub (_,ws,len,_,_) -> Arr (ws,len)
  | a -> ToEC.ty_expr a

(* TODO: fix [ToEC.ty_lval] and use it here instead*)
let rec ty_lval = function
  | Lasub (_,ws,len,_,_) -> Arr (ws,len)
  | a -> ToEC.ty_lval a
           
(*---------------------------------------------------------------*)
exception Aint_error of string
               
(*------------------------------------------------------------*)
let last_time = ref 0.
    
let print_time a =
  let t = Sys.time () in
  let diff = t -. !last_time in
  last_time := t;
  Format.eprintf "Time: %1.3f s. (+ %1.3f s.)@." t diff;
  a ()

let debug_print_time = true

let debug a = 
  if !Glob_options.debug then
    if debug_print_time then print_time a else a ()
  else ()

let timestamp () =
  if !Glob_options.timings then
    let depth = ref 0 in
    let pp_depth fmt = Format.fprintf fmt "%s" (String.make !depth '.') in
    fun f_decl ->
    if f_decl.f_cc = Internal then ignore else
      function
      | `Ret ->
         decr depth
      | `Call loc ->
         incr depth;
         Format.eprintf "%t %t%s (%a)@."
           Utils.pp_now
           pp_depth
           f_decl.f_name.fn_name
           L.pp_iloc loc
  else fun _ _ -> ()

let () = debug (fun () ->
    Format.eprintf "Debug: record backtrace@.";
    Printexc.record_backtrace true)

(*---------------------------------------------------------------*)
(* Turn on printing of only the relational part *)
let only_rel_print = ref false


(*------------------------------------------------------------*)
let ident = fun x -> x

let oget = function
  | Some x -> x
  | None -> raise (Failure "Oget")

let obind2 f x y = match x, y with
  | Some u, Some v -> f u v
  | _ -> None

let rec assoc_up s f = function
  | [] -> raise Not_found
  | (a,b) :: t ->
    if a = s then (a, f b) :: t
    else (a,b) :: assoc_up s f t

let rec combine3 l1 l2 l3 = match l1,l2,l3 with
  | h1 :: t1, h2 :: t2, h3 :: t3 -> (h1,h2,h3) :: combine3 t1 t2 t3
  | [], [], [] -> []
  | _ -> raise (Invalid_argument "combine3")

let rec fold_left3 f accu l1 l2 l3 =
  match l1,l2,l3 with
  | [], [], [] -> accu
  | a1::l1, a2::l2, a3::l3 -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | _ -> raise (Invalid_argument "fold_left3")
    
(*------------------------------------------------------------*)
(* Analyzer parameters *)

type analyzer_param = { relationals : string list option;
                        pointers : string list option }

(*------------------------------------------------------------*)
let get_fun_def prog f = List.find_opt (fun x -> x.f_name = f) (snd prog)


(*------------------------------------------------------------*)
let wsize_of_int = function
  | 8   -> U8
  | 16  -> U16
  | 32  -> U32
  | 64  -> U64
  | 128 -> U128
  | 256 -> U256
  | _   -> assert false


(*------------------------------------------------------------*)
let env_of_list l =
  let vars = Array.of_list l 
  and empty_var_array = Array.make 0 (Var.of_string "") in
  Environment.make vars empty_var_array 

(*------------------------------------------------------------*)
(* Mpq Utils *)

(* Return 2^n *)
let mpq_pow n =
  let c_div = Mpq.of_int 1 in
  let mpq2 = Mpq.of_int 1 in
  Mpq.mul_2exp c_div mpq2 n;
  Mpqf.of_mpq c_div 

(* Return 2^n - y *)
let mpq_pow_minus n y =
  Mpqf.sub (mpq_pow n |> Mpqf.of_mpq) (Mpqf.of_int y)

let mpq_of_z z  = Mpq.init_set_str (Z.to_string z) ~base:10
let mpqf_of_z z = Mpqf.of_mpq (mpq_of_z z)

(*------------------------------------------------------------*)
(* Coeff and Interval Utils *)

let scalar_to_zint scal =
  let tent_i = match scal with
    | Scalar.Float f -> Mpqf.of_float f
    | Scalar.Mpqf q -> q
    | Scalar.Mpfrf f -> Mpfrf.to_mpqf f in
  if Scalar.cmp scal (Scalar.of_mpqf tent_i) = 0
  then Some (Z.of_string (Mpqf.to_string tent_i))
  else None

let interval_to_zint int =
  let open Interval in
  if Scalar.equal int.inf int.sup then scalar_to_zint int.inf
  else None

let to_int c = match c with
  | Coeff.Scalar s -> Coeff.i_of_scalar s s
  | Coeff.Interval _ -> c

let s_to_mpqf = function
  | Scalar.Float f -> Mpqf.of_float f
  | Scalar.Mpqf x -> x
  | Scalar.Mpfrf f -> Mpfr.to_mpq f

let scalar_add s s' = Scalar.Mpqf (Mpqf.add (s_to_mpqf s) (s_to_mpqf s'))

let coeff_add c c' = match Coeff.reduce c, Coeff.reduce c' with
  | Coeff.Scalar s, Coeff.Scalar s' -> Coeff.Scalar (scalar_add s s')
  | _,_ ->
    match to_int c, to_int c' with
    | Coeff.Interval i, Coeff.Interval i' ->
      Coeff.Interval (Interval.of_scalar
                        (scalar_add i.inf i'.inf)
                        (scalar_add i.sup i'.sup))
    | _ -> assert false

let interval_join i1 i2 =
  let inf1, inf2 = i1.Interval.inf, i2.Interval.inf in
  let inf = if Scalar.cmp inf1 inf2 < 0 then inf1 else inf2 in
  
  let sup1, sup2 = i1.Interval.sup, i2.Interval.sup in
  let sup = if Scalar.cmp sup1 sup2 < 0 then sup2 else sup1 in
  Interval.of_infsup inf sup

let interval_meet i1 i2 =
  let inf1, inf2 = i1.Interval.inf, i2.Interval.inf in
  let inf = if Scalar.cmp inf1 inf2 < 0 then inf2 else inf1 in
  
  let sup1, sup2 = i1.Interval.sup, i2.Interval.sup in
  let sup = if Scalar.cmp sup1 sup2 < 0 then sup1 else sup2 in
  Interval.of_infsup inf sup


(*---------------------------------------------------------------*)
(* Fix-point computation *)
let rec fpt f eq x =
  let x' = f x in
  if (eq x x') then
    x
  else
    fpt f eq x'

(*---------------------------------------------------------------*)
(* Pretty Printers *)

let rec pp_list ?sep:(msep = Format.pp_print_space) pp_el fmt l = match l with
  | [] -> Format.fprintf fmt ""
  | h :: t -> Format.fprintf fmt "%a%a%a" pp_el h msep ()
                (pp_list ~sep:msep pp_el) t

let pp_opt pp_el fmt = function
  | None -> Format.fprintf fmt "None"
  | Some el -> Format.fprintf fmt "Some @[%a@]" pp_el el

let pp_call_strategy fmt = function
  | Config.Call_Direct             -> Format.fprintf fmt "direct"
  | Config.Call_TopByCallSite      -> Format.fprintf fmt "top"



