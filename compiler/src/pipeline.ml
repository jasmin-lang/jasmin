open Pipeline_program

type pipeline = string

module PipelineMap = Map.Make (struct type t = pipeline let compare = compare end)

module InstrIdMap = Map.Make (struct type t = string let compare = compare end)

let pipeline_to_latency = ref PipelineMap.empty 
let instruction_to_pipelines = ref InstrIdMap.empty

let get_first_token_after s i =
    if i > String.length s
    then ("", -1)
    else begin
        match String.index_from_opt s i ' ' with
        | None -> (String.trim (String.sub s i ((String.length s) - i)), (String.length s) + 1)
        | Some index_space -> (String.trim (String.sub s i (index_space - i + 1)), index_space + 1)
        end

let pipeline_from_config =
    let current_config = ref [] in
    let new_pipeline_list new_pipeline instr_id =
        let previous = (InstrIdMap.find_opt instr_id !instruction_to_pipelines)
        in match previous with
        | None -> new_pipeline :: []
        | Some l -> l @ [new_pipeline]
    in
    let file = open_in "src/pipelines.cfg" in
    let read_next_pipeline () =
        (* Get one line, with id latency and instructions handled *)
        let line = input_line file in
        if line <> "" then begin
            let (id, next) = get_first_token_after line 0 in
            let (size_str, next') = get_first_token_after line next in
            let size = if size_str <> "" then int_of_string size_str else 1 in
            (* Update config with new id and latency *)
            pipeline_to_latency := PipelineMap.add id size !pipeline_to_latency;
            current_config := !current_config @ [id];
            (* Get instructions *)
            let (first_instr, i) = (get_first_token_after line next') in
            let last_pos = ref i in
            let last_instr = ref first_instr in
            while !last_pos <> -1 do
                instruction_to_pipelines :=
                    InstrIdMap.add !last_instr (new_pipeline_list id !last_instr) !instruction_to_pipelines;
                let (next_instr, next_pos) = (get_first_token_after line !last_pos) in
                last_pos := next_pos;
                last_instr := next_instr
            done
            end
        else ()
    in
    try (
        while true do read_next_pipeline () done ; []
    )
    with End_of_file -> !current_config


let pipelines = pipeline_from_config

type step = Occupied of instr | Free

type processor = (step array) PipelineMap.t

let print_pipelines_stages = ref true

let current_cycle = ref 0

let reinit_cycles () = current_cycle := 0

let store_visual = false (* For debug *)

let data_file = ref (if store_visual then (open_out "visualisation/data0.js") else stdout)

(** Display **)
let pipeline_to_string p = p

let latency p = PipelineMap.find p !pipeline_to_latency

let store_proc_state_symbolic proc =
    if store_visual then begin
        (* Cycle *)
        output_string !data_file ("    cycle: " ^ (string_of_int !current_cycle) ^ ",\n");
        (* Pipelines *)
        output_string !data_file "    occupancy:[";
        let print_step next s = begin match s with
            | Free -> output_string !data_file "null"
            | Occupied i -> (
                let vars = i.instr_inputs @ i.instr_outputs in
                output_string !data_file "\"";
                List.iter (fun v ->
                    output_string !data_file ((Pipeline_program.operand_to_string v) ^ " "))vars;
                if List.length vars = 0 then output_string !data_file "∅";
                output_string !data_file "\"")
            end;
            if next then output_string !data_file ", "
        in
        let print_pipeline next p =
            Array.iteri
                (fun i -> fun step -> print_step (next || i < latency p) step)
                (PipelineMap.find p proc)
        in
        List.iteri (fun i -> fun pip -> print_pipeline (i < List.length pipelines) pip) pipelines;
        output_string !data_file "],\n"
    end

let store_fetch_symbolic proc instr =
    if store_visual then begin
        output_string !data_file "  {\n";
        store_proc_state_symbolic proc;
        output_string !data_file ("    fetch: \"" ^ (instr_to_string instr) ^ "\"\n  },\n")
    end

let store_execute_step_symbolic proc p i =
    if store_visual then begin
        output_string !data_file "  {\n";
        store_proc_state_symbolic proc;
        output_string !data_file ("    execute: \"" ^ p ^ (string_of_int i) ^ "\"\n  },\n")
    end

let pipelines_for i = InstrIdMap.find (i.instr_id) !instruction_to_pipelines

let new_pipeline p = Array.make (latency p) Free

let new_processor () =
    let rec add_pipeline pips proc = match pips with
        | h :: t -> add_pipeline t (PipelineMap.add h (new_pipeline h) proc)
        | [] -> proc
    in
    add_pipeline pipelines PipelineMap.empty

let alias_analysis o1 o2 = match (o1, o2) with
    | (Value, _) -> false
    | (_, Value) -> false
    | (Register _, MemoryAt _) -> false
    | (MemoryAt _, Register _) -> false
    | (Register a, Register b) -> (a == b)
    | (MemoryAt _, MemoryAt _) -> true (* -> Means maybe *)

let ressources_available instr proc =
    let step_no_write step value = 
        if value then
            match step with
            | Free -> true
            | Occupied i ->
                    (* No inputs of instr should be an output of i *)
                    let outputs = i.instr_outputs in
                    let inputs_ready = List.fold_right (fun w -> fun acc -> acc && not (List.mem w instr.instr_inputs)) outputs true in
                    (* No outputs of instr should be an input or output of i *)
                    let needed = i.instr_outputs @ i.instr_inputs in
                    let outputs_ready = List.fold_right (fun w -> fun acc -> acc && not (List.mem w instr.instr_outputs)) needed true in
                    inputs_ready && outputs_ready
                    (* TODO: Use alias-analysis *)
        else false
    in
    let variable_available _ steps all_available =
        (* For this pipeline, check every step *)
        if all_available then (Array.fold_right step_no_write steps true) else false
    in
    PipelineMap.fold variable_available proc true

let execute_step proc p i =
    let lat = latency p in
    if i >= lat
    then failwith ("Execute step called on "
            ^ (pipeline_to_string p) ^ (string_of_int (i + 1))
            ^ ". Maximum step index is " ^ (string_of_int lat))
    else
        let step = (PipelineMap.find p proc).(i) in
        match step with
        | Free -> ()
        | Occupied instr -> begin
            if i = lat - 1
            then (PipelineMap.find p proc).(i) <- Free
            else (
                (PipelineMap.find p proc).(i) <- Free;
                (PipelineMap.find p proc).(i + 1) <- Occupied instr);
            store_execute_step_symbolic proc p i
            end

let execute_pipeline proc p =
    for i = (latency p) - 1 downto 0 do
        execute_step proc p i
    done

let one_cycle proc =
    let rec one_pipeline pips = match pips with
    | [] -> ()
    | h :: t -> (execute_pipeline proc h ; one_pipeline t)
    in
    incr current_cycle;
    one_pipeline pipelines

let can_fetch proc instr =
    let rec try_candidate candidates = match candidates with
    | [] -> false
    | h :: t -> if (PipelineMap.find h proc).(0) = Free
                then true
                else try_candidate t
    in
    if ressources_available instr proc
    then try_candidate (pipelines_for instr)
    else false

let fetch proc instr = 
    let rec try_candidate candidates = match candidates with
    | [] -> failwith ("No pipeline to fetch " ^ (instr_to_string instr))
    | h :: t -> if (PipelineMap.find h proc).(0) = Free
                then (PipelineMap.find h proc).(0) <- Occupied instr
                else try_candidate t
    in
    try_candidate (pipelines_for instr);
    store_fetch_symbolic proc instr

let atomic proc instr =
    while not (can_fetch proc instr) do
        one_cycle proc
    done;
    fetch proc instr

let finish proc =
    let is_step_empty value s =
        match s with
        | Free -> value
        | Occupied _ -> false
    in
    let is_pipeline_empty _ steps all_empty =
        if all_empty
        then Array.fold_left is_step_empty true steps
        else false
    in
    let is_proc_empty () = PipelineMap.fold is_pipeline_empty proc true in
    while not (is_proc_empty ()) do
        one_cycle proc
    done

type instrumentation = Pipeline_program.checkpoint * int * int (* min and max bound *)

type instrumentation_program =
  | ISkip
  | IBloc of instrumentation (* instrumentation put at the end of the sequence *)
  | ISeq of instrumentation_program list
  | ICond of instrumentation_program * instrumentation_program
  | ILoop of instrumentation_program

let open_new_data prgm_js =
    if store_visual then begin
        close_out !data_file;
        data_file := open_out "visualisation/data0.js";
        output_string !data_file "var analysis = {\n  prog:";
        output_string !data_file prgm_js;
        output_string !data_file ",\n  steps:[";
        let rec add_pipeline pips = match pips with
            | [] -> ()
            | h :: t -> begin
                for i = 0 to (latency h) - 1 do
                    output_string !data_file ("\"" ^ h ^ (string_of_int i) ^ "\"");
                    if (t <> [] || i < (latency h)) then output_string !data_file ", ";
                done;
                add_pipeline t
                end
        in
        add_pipeline pipelines;
        output_string !data_file "],\n  has_next:{";
        let rec add_pipeline_next pips = match pips with
            | [] -> ()
            | h :: t -> begin
                for i = 0 to (latency h) - 1 do
                    output_string !data_file ("\"" ^ h ^ (string_of_int i) ^ "\":");
                    if i < (latency h) - 1
                    then output_string !data_file " true"
                    else output_string !data_file " false";
                    if (t <> [] || i < (latency h) - 1) then output_string !data_file ", ";
                done;
                add_pipeline_next t
                end
        in
        add_pipeline_next pipelines;
        output_string !data_file "},\n  actions : [\n"
    end

let close_data () =
    if store_visual then begin
        output_string !data_file "  ]\n}\n";
        close_out !data_file
    end

let instrument prog proc =
    let rec aux prog' proc' = match prog' with
        | Skip -> ISkip
        | Bloc (c, l) -> begin
            if store_visual then output_string !data_file "    [\n";
            let cost = ref 0 in
            let fetch_next i = 
                (* Execute cycle on proc' until i can be fetched *)
                while not (can_fetch proc' i) do
                    incr cost;
                    one_cycle proc'
                done;
                (* Updates proc' with the fetch *)
                fetch proc' i in
            List.iter fetch_next l;
            if store_visual then output_string !data_file "    ],\n";
            IBloc (c, !cost, !cost + 5)
            end
        | Seq [] -> ISeq []
        | Seq (h :: l) ->
            (* First element can use proc but then we need an empty proc *)
            ISeq ((aux h proc') :: (List.map aux_empty l))
        | Cond (_, cif, celse) ->
            ICond (aux_empty cif, aux_empty celse)
        | Loop (_, cbody) -> 
            ILoop (aux_empty cbody)
    and aux_empty prog' = aux prog' (new_processor ()) in
    aux prog proc

let rec display = function
  | ISkip -> 
    Format.printf "ISkip@ "
  | IBloc (c, min, max) ->
    Format.printf "IBloc no %d : cost += [%d, %d]@ " c min max
  | ISeq l -> begin
        Format.printf "ISeq (@ @[<v 2>  ";
        List.iter display l;
        Format.printf ")@]@ "
    end
  | ICond (cif, celse) -> begin
        Format.printf "cost += [0, 5]@ ICond (@ @[<v 2>  ";
        display cif;
        Format.printf ",@ ";
        display celse;
        Format.printf ")@]@ "
    end
  | ILoop c -> begin
        Format.printf "cost += [1, 6]@ ILoop (@ @[<v 2>  cost += [1, 5]@ ";
        display c;
        Format.printf ")@]@ "
    end

let rec display_checkpoints = function
  | ISkip -> ()
  | IBloc (c, min, max) ->
    Format.printf "%d %d %d@ " c min max
  | ISeq l -> List.iter display_checkpoints l
  | ICond (cif, celse) -> begin
        display_checkpoints cif;
        display_checkpoints celse
    end
  | ILoop c -> display_checkpoints c