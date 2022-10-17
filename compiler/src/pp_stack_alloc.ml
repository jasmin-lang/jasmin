open Stack_alloc

let pp_pos fmt p =
  Z.pp_print fmt (Conv.z_of_pos p)

let pp_var tbl fmt x =
  Printer.pp_var ~debug:true fmt (Conv.var_of_cvar tbl x)

let pp_region tbl fmt r =
  Format.fprintf fmt "{ slot = %a; wsize = %s; align = %b }"
    (pp_var tbl) r.r_slot
    (Prog.string_of_ws r.r_align)
    r.r_writable

let pp_zone fmt z =
  Format.fprintf fmt "[%a:%a]" Z.pp_print (Conv.z_of_cz z.z_ofs) Z.pp_print (Conv.z_of_cz z.z_len)

let pp_sub_region tbl fmt sr =
  Format.fprintf fmt "{ region = %a; zone = %a }" (pp_region tbl) sr.sr_region pp_zone sr.sr_zone

let pp_var_region tbl fmt vr =
  Format.fprintf fmt "@[<v>";
  Var0.Mvar.fold (fun x sr () ->
    Format.fprintf fmt "@[<h>%a -> %a@]@," (pp_var tbl) (Obj.magic x) (pp_sub_region tbl) sr) vr ();
  Format.fprintf fmt "@]"

let pp_interval fmt i =
  Format.fprintf fmt "[%a,%a]" Z.pp_print (Conv.z_of_cz i.Byteset.imin) Z.pp_print (Conv.z_of_cz i.Byteset.imax)

let pp_byteset fmt b =
  Format.pp_print_list pp_interval fmt b

let pp_region_var tbl fmt rv =
  Format.fprintf fmt "@[<v>";
  Mr.fold (fun r sm () ->
    Var0.Mvar.fold (fun x s () ->
      Format.fprintf fmt "%a -> %a -> %a@,"
        (pp_var tbl) (Obj.magic r).r_slot (pp_var tbl) (Obj.magic x)
        pp_byteset (Byteset.ByteSet.to_list s)) sm ()) rv ();
  Format.fprintf fmt "@]"

let pp_rmap tbl fmt rmap =
  let open Region in
  Format.fprintf fmt "@[<v>{ var_region:@;<2 4>%a@;<2 2>region_var:@;<2 4>%a@,}@]@." (pp_var_region tbl) rmap.var_region (pp_region_var tbl) rmap.region_var
