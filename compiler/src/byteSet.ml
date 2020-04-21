open Interval

(* An interval { min ; max } represents the interval [min, max) *)

type t = interval list (* sorted in increasing order, no overlap *)

let empty = []
let is_empty t = t == []
               
let full n = [n]

let memi_inter i inter = inter.min <= i && i < inter.max

let rec memi i t = 
  match t with
  | [] -> false
  | n::t -> memi_inter i n || (n.max <= i && memi i t)
          
let is_empty_inter n = n.max <= n.min
                     
let subset_inter n1 n2 = n2.min <= n1.min && n1.max <= n2.max
                       
let rec mem n t = 
  match t with
  | [] -> false
  | n'::t -> subset_inter n n' || (n'.max <= n.min) && mem n t
           
let rec add n t = 
  match t with
  | [] -> [n]
  | n'::t' ->
    if n.max < n'.min then n :: t
    else if n'.max < n.min then n' :: add n t'
    else 
      let n = { min = min n.min n'.min; 
                max = max n.max n'.max } in
      add n t'
      
let push n t = if is_empty_inter n then t else n :: t

let rec remove excl t = 
  match t with
  | [] -> t
  | n' :: t' ->
    let n1 = { min = n'.min; max = min n'.max excl.min } in
    let n2 = { min = max n'.min excl.max; max = n'.max } in
    let excl = {min = max n'.max excl.min; max = excl.max } in
    let t' = if is_empty_inter excl then t' else remove excl t' in
    push n1 (push n2 t')
    
let rec subset t1 t2 = 
  match t1, t2 with
  | [], _ -> true
  | _::_, [] -> false
  | n1::t1', n2::t2' ->
    if subset_inter n1 n2 then subset t1' t2
    else 
      if n2.max <= n1.min then subset t1 t2'
      else false

let rec inter t1 t2 = 
  match t1, t2 with
  | _, [] | [], _ -> []
  | n1::t1', n2 :: t2' ->
    if n1.max <= n2.min then inter t1' t2
    else if n2.max <= n1.min then inter t1 t2'
    else 
      let n = { min = max n1.min n2.min;
                max = min n1.max n2.max; } in
      let n1' = { min = max n2.max n1.min; max = n1.max } in
      let n2' = { min = max n1.max n2.min; max = n2.max } in
      n :: inter (push n1' t1') (push n2' t2') 

let rec union t1 t2 = 
  match t1, t2 with
  | _, [] -> t1 
  | [], t2 -> t2
  | n1 :: t1', n2:: t2' ->
    if n1.max < n2.min then n1 :: (union t1' t2)
    else if n2.max < n1.min then n2 :: (union t1 t2')
    else union t1' (add n1 t2)
    
        
let pp fmt t = 
  let pp_interval fmt n = 
    Format.fprintf fmt "[%i..%i) " n.min n.max in
  Format.fprintf fmt "@[%a@]"
    (Printer.pp_list "@ " pp_interval) t



