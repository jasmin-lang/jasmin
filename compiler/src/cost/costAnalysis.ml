open Prog

let check_safety counters p : unit =
  List.iter (fun f_decl ->
      if f_decl.f_cc = Export then
        let () = Format.eprintf "@[<v>Analyzing function %s@]@."
                   f_decl.f_name.fn_name in

        let module AbsInt = SafetyInterpreter.AbsAnalyzer(struct
                                let main_source = f_decl
                                let main = f_decl
                                let prog = p
                                let cost_variables = counters
                              end) in

        AbsInt.analyze ())
    (List.rev (snd p))

let summarize_counters counters =
  let h = Hashtbl.create 17 in
  let add n =
    match Hashtbl.find h n with
    | c -> Hashtbl.replace h n (c + 1)
    | exception Not_found -> Hashtbl.add h n 1
  in
  List.iter (fun (n, _) -> add n) counters;
  Hashtbl.fold (fun n c acc -> (n, c) :: acc) h []


let analyze prog : unit =
  Format.printf ">>> Cost analysis <<<@.";
  Format.printf "Analyzed program:\n%a@." (Printer.pp_prog ~debug:true) prog;
  let counters, instrumented = CostInstrumentation.instrument prog in
  Format.printf "After instrumentation:\n%a@." (Printer.pp_prog ~debug:true) instrumented;
  Format.printf "The instrumentation has added the following amount of counters: %a@."
    (Printer.pp_list " ;@ " (fun fmt (n, c) -> Format.fprintf fmt "%s ↦ %d" n c)) (summarize_counters counters);
  Format.printf "Checking safety@.";
  check_safety counters instrumented;
  Format.printf "@.Bye bye…@.";
  exit 0
