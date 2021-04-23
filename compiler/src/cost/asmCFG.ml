open Utils
open X86_decl
open X86_sem

let labels (p: asm array) : label -> int =
  let labels = Hashtbl.create 43 in
  Array.iteri (fun pc ->
      function
      | (ALIGN | JMP _ | Jcc _ | AsmOp _) -> ()
      | LABEL n -> Hashtbl.add labels n (pc + 1)
    )
    p;
  Hashtbl.find labels

let predecessors labels (p: asm array) : int list array =
  let predecessors = Array.make (Array.length p + 1) [] in
  let edge b e = predecessors.(e) <- b :: predecessors.(e) in
  let edge_to_label b tgt = edge b (labels tgt) in
  Array.iteri (fun pc ->
      function
      | (ALIGN | LABEL _ | AsmOp _) -> edge pc (pc + 1)
      | JMP tgt -> edge_to_label pc tgt
      | Jcc (tgt, _) -> edge pc (pc + 1); edge_to_label pc tgt
    ) p;
  predecessors

let successors labels predecessors (p: asm array) (pc: int) : int list =
  let is_join pc = 1 < List.length predecessors.(pc) in
  let rec successors pc =
    if pc = Array.length p then [ pc ] else
    match p.(pc) with
    | (ALIGN | LABEL _ | AsmOp _) ->
       let next = pc + 1 in
       if is_join next then [ next ] else successors next
    | JMP tgt ->
       let next = labels tgt in
       if is_join next then [ next ] else successors next
    | Jcc (tgt, _) -> [ pc + 1 ; labels tgt ]
  in successors pc

let basic_blocks (p: asm list) : (int, int list) Hashtbl.t =
  let p = Array.of_list p in
  let labels = labels p in
  let predecessors = predecessors labels p in
  let successors = Array.init (Array.length p) (successors labels predecessors p) in
  let is_successor = Hashtbl.create 97 in
  Array.iter (List.iter (fun pc -> if not (Hashtbl.mem is_successor pc) then Hashtbl.add is_successor pc ())) successors;
  let graph = Hashtbl.create 17 in
  let add pc =
    match successors.(pc) with
    | exception _ -> ()
    | s -> Hashtbl.add graph pc s
  in
  add 0;
  Hashtbl.iter (fun pc () -> add pc) is_successor;
  graph

let pp_cfg fmt (name: string) (p: asm list) : unit =
  let graph = basic_blocks p in
  let open Format in
  let node fmt pc = fprintf fmt "_%d" pc in
  fprintf fmt "digraph %s {@." name;
  fprintf fmt "%a [ shape = box ];@." node 0;
  Hashtbl.iter (fun b ->
      List.iter (fun e ->
          fprintf fmt "%a -> %a;@." node b node e
        )
    ) graph;
  fprintf fmt "}@."
