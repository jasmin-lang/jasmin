open Prog
open Apron

module Config = SafetyConfig
  
let round_typ = Texpr1.Zero
  
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

let () = debug (fun () ->
    Format.eprintf "Debug: record backtrace@.";
    Printexc.record_backtrace true)

let ident = fun x -> x

(* Turn on printing of only the relational part *)
let only_rel_print = ref false


(***********************)
(* Analyzer parameters *)
(***********************)

type analyzer_param = { relationals : string list option;
                        pointers : string list option }


(*------------------------------------------------------------*)
let get_fun_def prog f = List.find_opt (fun x -> x.f_name = f) (snd prog)

let oget = function
  | Some x -> x
  | None -> raise (Failure "Oget")

let env_of_list l =
  let vars = Array.of_list l 
  and empty_var_array = Array.make 0 (Var.of_string "") in
  Environment.make vars empty_var_array 


(*------------------------------------------------------------*)
let rec assoc_up s f = function
  | [] -> raise Not_found
  | (a,b) :: t ->
    if a = s then (a, f b) :: t
    else (a,b) :: assoc_up s f t


(*************)
(* Mpq Utils *)
(*************)

(* Return 2^n *)
let mpq_pow n =
  let c_div = Mpq.of_int 1 in
  let mpq2 = Mpq.of_int 1 in
  Mpq.mul_2exp c_div mpq2 n;
  Mpqf.of_mpq c_div 

(* Return 2^n - y *)
let mpq_pow_minus n y =
  Mpqf.sub (mpq_pow n |> Mpqf.of_mpq) (Mpqf.of_int y)


(****************************)
(* Coeff and Interval Utils *)
(****************************)

let scalar_to_int scal =
  let tent_i = match scal with
    | Scalar.Float f -> int_of_float f
    | Scalar.Mpqf q -> Mpqf.to_float q |> int_of_float
    | Scalar.Mpfrf f -> Mpfrf.to_float f |> int_of_float in
  if Scalar.cmp_int scal tent_i = 0 then Some tent_i
  else None

let interval_to_int int =
  let open Interval in
  if Scalar.equal int.inf int.sup then scalar_to_int int.inf
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
let swap_op2 op e1 e2 =
  match op with
  | E.Ogt   _ -> e2, e1
  | E.Oge   _ -> e2, e1
  | _         -> e1, e2

let mpq_of_bigint z  = Mpq.init_set_str (B.to_string z) ~base:10
let mpqf_of_bigint z = Mpqf.of_mpq (mpq_of_bigint z)

(*---------------------------------------------------------------*)
(* Fix-point computation *)
let rec fpt f eq x =
  let x' = f x in
  if (eq x x') then
    x
  else
    fpt f eq x'

module Scmp = struct
  type t = string
  let compare = compare
end

module Ms = Map.Make(Scmp)


(*******************)
(* Pretty Printers *)
(*******************)

let pp_apr_env ppf e = Environment.print ppf e

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
  (* | Call_WideningByCallSite -> Format.fprintf fmt "widening" *)

