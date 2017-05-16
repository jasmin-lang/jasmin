open Prog
open Utils

let split_live_ranges (f: 'info func) : 'info func =
  let lf = Liveness.live_fd f in
  f

let remove_phi_nodes (f: 'info func) : 'info func =
  let rec instr_r =
    function
    | Cblock s -> (match stmt s with [] -> [] | s -> [Cblock s])
    | Cassgn (x, tg, e) as i ->
      (match tg with
       | AT_rename_arg ->
         (match x, e with
          | Lvar v, Pvar v' -> if v = v' then [] else
              let pv = Printer.pp_var ~debug:true in
              hierror "SSA: cannot remove assignment %a = %a"
                pv (L.unloc v) pv (L.unloc v')
          | _, _ -> [i])
       | _ -> [i])
    | Cif (b, s1, s2) -> [Cif (b, stmt s1, stmt s2)]
    | Cwhile (s1, b, s2) -> [Cwhile (stmt s1, b, stmt s2)]
    | (Copn _ | Cfor _ | Ccall _) as i -> [i]
  and instr i = List.map (fun i_desc -> { i with i_desc }) (instr_r i.i_desc)
  and stmt s = List.(flatten (map instr s)) in
  let f_body = stmt f.f_body in
  { f with f_body }
