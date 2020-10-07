open Pipeline_program

(* Errors *)

exception UnknownConfigFormat

let unknown_config_format_error () =
  raise UnknownConfigFormat

exception InstructionUnsupported of string

let unsupported_instr_error msg =
  raise (InstructionUnsupported ("Cannot instrument the program : the following instructions are not supported by any pipeline.\n" ^ msg))

(* -------------------------------------------------------------------- *)

let config_file = "src/pipelines.cfg"
let config_mode_per_pipeline = true

(* -------------------------------------------------------------------- *)

type pipeline = string

module PipelineMap = Map.Make (struct type t = pipeline let compare = compare end)

module InstrIdMap = Map.Make (struct type t = string let compare = compare end)

let instruction_to_pipelines = ref InstrIdMap.empty

let get_first_token_after s i =
    if i > String.length s
    then ("", -1)
    else begin
        match String.index_from_opt s i ' ' with
        | None -> (String.trim (String.sub s i ((String.length s) - i)), (String.length s) + 1)
        | Some index_space -> (String.trim (String.sub s i (index_space - i + 1)), index_space + 1)
        end

(* -------------------------------------------------------------------- *)

let pipeline_to_latency = ref PipelineMap.empty 

let add_pipeline_to_instr instr pipeline =
    (* Returns the list of pipelines that handles the instruction, including
       the new one placed at the end. *)
    let new_pipeline_list =
        let previous = (InstrIdMap.find_opt instr !instruction_to_pipelines)
        in match previous with
        | None -> [pipeline]
        | Some l -> l @ [pipeline]
    in
    instruction_to_pipelines :=
        InstrIdMap.add instr new_pipeline_list !instruction_to_pipelines

(* -------------------------------------------------------------------- *)
(* Per_pipeline config mode *)

let add_new_pipeline pipeline_id latency =
    pipeline_to_latency := PipelineMap.add pipeline_id latency !pipeline_to_latency

(* -------------------------------------------------------------------- *)
(* Per_instruction config mode *)

let instruction_to_latency = ref InstrIdMap.empty

let add_new_instr instr_id latency =
    instruction_to_latency := InstrIdMap.add instr_id latency !instruction_to_latency

(* Take the maximum between the currently stored latency for this pipeline and 
   the one given *)
let add_pipeline_latency pipeline_id latency =
    let previous = (PipelineMap.find_opt pipeline_id !pipeline_to_latency) in
    let old_value = match previous with
        | None -> 0
        | Some v -> v
    in
    pipeline_to_latency :=
        PipelineMap.add pipeline_id (max old_value latency) !pipeline_to_latency

(* -------------------------------------------------------------------- *)

let pipeline_from_config =
    let current_config = ref [] in
    let file = open_in config_file in
    if config_mode_per_pipeline then
        let read_next_pipeline () =
            (* Get one line, with id, latency and instructions handled *)
            let line = input_line file in
            if line <> "" then begin
                let (pipeline_id, next) = get_first_token_after line 0 in
                let (latency_str, next') = get_first_token_after line next in
                let latency = if latency_str <> "" then int_of_string latency_str else 1 in
                (* Update config with new id and latency *)
                add_new_pipeline pipeline_id latency;
                current_config := !current_config @ [pipeline_id];
                (* Get instructions *)
                let (first_instr, i) = (get_first_token_after line next') in
                let last_pos = ref i in
                let last_instr = ref first_instr in
                while !last_pos <> -1 do
                    add_pipeline_to_instr !last_instr pipeline_id;
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
    else
        let read_next_instruction () =
            (* Get one line, with id, latency and pipelines *)
            let line = input_line file in
            if line <> "" then begin
                let (instr_id, next) = get_first_token_after line 0 in
                let (latency_str, next') = get_first_token_after line next in
                let latency = if latency_str <> "" then int_of_string latency_str else 1 in
                (* Update config with new id and latency *)
                add_new_instr instr_id latency;
                (* Get instructions *)
                let (first_pipeline, i) = (get_first_token_after line next') in
                let last_pos = ref i in
                let last_pipeline = ref first_pipeline in
                while !last_pos <> -1 do
                    add_pipeline_to_instr instr_id !last_pipeline;
                    add_pipeline_latency !last_pipeline latency;
                    let (next_pipeline, next_pos) = (get_first_token_after line !last_pos) in
                    last_pos := next_pos;
                    last_pipeline := next_pipeline
                done
                end
            else ()
        in
        try (
            (* Get one line, with all pipelines s *)
            let line = input_line file in
            if line <> "" then begin
                let (first_pipeline, i) = (get_first_token_after line 0) in
                let last_pos = ref i in
                let last_pipeline = ref first_pipeline in
                while !last_pos <> -1 do
                    current_config := !current_config @ [!last_pipeline];
                    let (next_pipeline, next_pos) = (get_first_token_after line !last_pos) in
                    last_pos := next_pos;
                    last_pipeline := next_pipeline
                done
                end;
            while true do read_next_instruction () done ; []
        )
        with End_of_file -> !current_config


let pipelines = pipeline_from_config

(* -------------------------------------------------------------------- *)

let max_latency =
    if config_mode_per_pipeline then
        PipelineMap.fold (fun pip -> fun lat -> fun current_max -> max current_max lat) !pipeline_to_latency 0
    else
        InstrIdMap.fold (fun instr -> fun lat -> fun current_max -> max current_max lat) !instruction_to_latency 0


(* -------------------------------------------------------------------- *)

type step = Occupied of instr | Free

type processor = (step array) PipelineMap.t

let print_pipelines_stages = ref true

let current_cycle = ref 0

let reinit_cycles () = current_cycle := 0

(** Display **)
let pipeline_to_string p = p

let latency p = PipelineMap.find p !pipeline_to_latency

let has_pipeline_for i = InstrIdMap.mem i !instruction_to_pipelines

let pipelines_for i = InstrIdMap.find i.instr_id !instruction_to_pipelines

let new_pipeline p = Array.make (latency p) Free

let new_processor () =
    let rec add_pipeline pips proc = match pips with
        | h :: t -> add_pipeline t (PipelineMap.add h (new_pipeline h) proc)
        | [] -> proc
    in
    add_pipeline pipelines PipelineMap.empty

let copy_processor proc =
    let rec add_pipeline pips proc' = match pips with
        | h :: t ->
            let pipeline = PipelineMap.find h proc in
             add_pipeline t (PipelineMap.add h (Array.copy pipeline) proc')
        | [] -> proc'
    in
    add_pipeline pipelines PipelineMap.empty

let alias_names_to_operands = List.map (fun n -> MemoryAt n)

let ressources_available compute_lower_bound instr proc =
    let step_no_write step value = 
        if value then
            match step with
            | Free -> true
            | Occupied ip ->
                    (* All inputs of instr should be ready: none should be an output of ip *)
                    let outputs = ip.instr_outputs in
                    let inputs_ready = List.fold_right (fun w -> fun acc -> acc && not (List.mem w instr.instr_inputs)) outputs true in
                    (* All outputs of instr should be ready: none should be an output or an input of ip *)
                    let needed = ip.instr_outputs @ ip.instr_inputs in
                    let outputs_ready = List.fold_right (fun w -> fun acc -> acc && not (List.mem w instr.instr_outputs)) needed true in
                    (* If we compute the upper bound, we need to take into account may aliases too *)
                    let inputs_aliases_ready = List.fold_right (fun w -> fun acc -> acc && not (List.mem w instr.instr_may_inputs)) outputs true in
                    let iar = compute_lower_bound || inputs_aliases_ready in
                    let outputs_aliases_ready = List.fold_right (fun w -> fun acc -> acc && not (List.mem w instr.instr_may_outputs)) needed true in
                    let oar = compute_lower_bound || outputs_aliases_ready in

                    inputs_ready && outputs_ready && iar && oar
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
            if (i = lat - 1) || (not config_mode_per_pipeline && (InstrIdMap.find instr.instr_id !instruction_to_latency) = i)
            then (PipelineMap.find p proc).(i) <- Free
            else (
                (PipelineMap.find p proc).(i) <- Free;
                (PipelineMap.find p proc).(i + 1) <- Occupied instr)
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

let can_fetch compute_lower_bound proc instr =
    let rec try_candidate candidates = match candidates with
    | [] -> false
    | h :: t -> if (PipelineMap.find h proc).(0) = Free
                then true
                else try_candidate t
    in
    if ressources_available compute_lower_bound instr proc
    then try_candidate (pipelines_for instr)
    else false

let fetch proc instr = 
    let rec try_candidate candidates = match candidates with
    | [] -> failwith ("No pipeline to fetch " ^ (instr_to_string instr))
    | h :: t -> if (PipelineMap.find h proc).(0) = Free
                then (PipelineMap.find h proc).(0) <- Occupied instr
                else try_candidate t
    in
    try_candidate (pipelines_for instr)

let atomic compute_lower_bound proc instr =
    while not (can_fetch compute_lower_bound proc instr) do
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

let instrument prog proc =
    let rec aux prog' proc_min' proc_max' = match prog' with
        | Skip -> ISkip
        | Bloc (c, l) -> begin
            let cost_min = ref 0 in
            let cost_max = ref 0 in
            let fetch_next_min i = 
                (* Execute cycle on proc' until i can be fetched *)
                while not (can_fetch true proc_min' i) do
                    incr cost_min;
                    one_cycle proc_min'
                done;
                (* Updates proc' with the fetch *)
                Format.eprintf " %d: %s@." !cost_min (instr_to_string i);
                fetch proc_min' i in
            Format.eprintf "Cost Min of bloc %d@." c;
            List.iter fetch_next_min l;
            let fetch_next_max i = 
                (* Execute cycle on proc' until i can be fetched *)
                while not (can_fetch false proc_max' i) do
                    incr cost_max;
                    one_cycle proc_max'
                done;
                (* Updates proc' with the fetch *)
                Format.eprintf " %d: %s@." !cost_max (instr_to_string i);
                fetch proc_max' i in
            Format.eprintf "Cost Max of bloc %d@." c;
            List.iter fetch_next_max l;
            Format.eprintf "@.";
            IBloc (c, !cost_min, !cost_max + max_latency)
            end
        | Seq [] -> ISeq []
        | Seq (h :: l) ->
            (* First element can use proc but then we need an empty proc *)
            ISeq ((aux h proc_min' proc_max') :: (List.map aux_empty l))
        | Cond (_, cif, celse) ->
            ICond (aux_empty cif, aux_empty celse)
        | Loop (_, cbody) -> 
            ILoop (aux_empty cbody)
    and aux_empty prog' = aux prog' (new_processor ()) (new_processor ()) in
    let unsupported_instrs =
        List.filter (fun i -> not (has_pipeline_for i)) (get_all_instr_in prog)
    in
    if unsupported_instrs <> []
    then begin
        let s = List.fold_left
            (fun acc -> fun i -> Format.sprintf "%s %s" acc i)
            ""
            unsupported_instrs in
        unsupported_instr_error s
    end
    else begin
        Format.eprintf "@.@[<v 0>\
                        *----------------------------*@;\
                        |  Pipeline instrumentation  |@;\
                        *----------------------------*@;@;@]@.@[<v 0>";
        print_prog_struct prog;
        Format.eprintf "@]@.@.";
        aux prog (copy_processor proc) (copy_processor proc)
    end

let naive_instrument prog =
    let rec aux prog' = match prog' with
        | Skip -> ISkip
        | Bloc (c, l) -> begin
            let cost = ref 0 in
            let cost_of_instr i = 
                if config_mode_per_pipeline
                then cost := !cost + PipelineMap.find (List.hd (pipelines_for i)) !pipeline_to_latency
                else cost := !cost + InstrIdMap.find i.instr_id !instruction_to_latency;
                (* Updates proc' with the fetch *)
                Format.eprintf " %d: %s@." !cost (instr_to_string i)
            in
            Format.eprintf "Naive Cost of bloc %d@." c;
            List.iter cost_of_instr l;
            Format.eprintf "@.";
            IBloc (c, 0, !cost)
            end
        | Seq [] -> ISeq []
        | Seq (h :: l) ->
            (* First element can use proc but then we need an empty proc *)
            ISeq ((aux h) :: (List.map aux l))
        | Cond (_, cif, celse) ->
            ICond (aux cif, aux celse)
        | Loop (_, cbody) -> 
            ILoop (aux cbody)
    in
    let unsupported_instrs =
        List.filter (fun i -> not (has_pipeline_for i)) (get_all_instr_in prog)
    in
    if unsupported_instrs <> []
    then begin
        let s = List.fold_left
            (fun acc -> fun i -> Format.sprintf "%s %s" acc i)
            ""
            unsupported_instrs in
        unsupported_instr_error s
    end
    else begin
        Format.eprintf "@.@[<v 0>\
                        *----------------------------------*@;\
                        |  Naive Pipeline instrumentation  |@;\
                        *----------------------------------*@;@;@]@.@[<v 0>";
        print_prog_struct prog;
        Format.eprintf "@]@.@.";
        aux prog
    end