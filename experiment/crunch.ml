open Data (* generate with `sh crunch.sh > data` *)

let log2 f = log f /. log 2.

let overhead { ref = my, sy ; ct = mx, sx } =
  log2 (mx /. my),
  sqrt ((sx *. sx) /. (mx *. mx) +. (sy *. sy) /. (my *. my))

let pp_m fmt (m, d) =
    Format.fprintf fmt "%f±%f" m d

let pp fmt (n, m, o) =
    Format.fprintf fmt "%s\t%a\t%a\t%a@."
      n pp_m m.ref pp_m m.ct pp_m o

let () =
  Format.printf "Compilation times:@.Name\tRef\tCT\tOverhead@.";
  data
  |> List.map (fun (n, m) -> n, m, overhead m)
  |> List.sort (fun (_, x, _) (_, y, _) -> Float.compare (fst x.ref) (fst y.ref))
  |> List.iter (Format.printf "%a" pp)
