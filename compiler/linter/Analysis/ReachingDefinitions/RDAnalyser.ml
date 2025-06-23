open Jasmin.Prog
open Annotation

(* TODO : remove when added to Prog.mli*)
let written_lvs = List.fold_left written_lv Sv.empty

(* TODO : remove when added to Prog.mli*)
let params fc = List.fold_left (fun s v -> Sv.add v s) Sv.empty fc.f_args

module ReachingDefinitionLogic : ForwardAnalyser.Logic with type domain = RDDomain.t = struct
  type domain = RDDomain.t

  (**
    Initial domain : each local variable is associated with the Default Iloc corresponding to (?) notation
  *)
  let initialize f =
      let locvars = locals f in
      let s = Sv.fold (fun x acc -> Mv.add x (Iloc.SIloc.singleton Default) acc) locvars Mv.empty in
      Annotation
        (Sv.fold
           (fun x acc ->
             Mv.add x (Iloc.SIloc.singleton (Iloc.Instruction (Jasmin.Location.i_loc0 f.f_loc))) acc )
           (params f) s )

  let pp fmt = RDDomain.pp fmt

  (** Check if a is included in b*)
  let included a b = RDDomain.included a b

  (**
    In the case of reaching definitions, we do not analyse the condition so this function is the identity
  *)
  let assume _ state = (state, state)

  let merge s1 s2 = RDDomain.join s1 s2

  let forget var domain = Annotation (RDDomain.forget (L.unloc var) domain)


  (**
  logic for any assignment : we kill all left variables, meaning removing all previously defined locations and set the location of the current instruction
  *)
  let funcall loc lvs _ _ domain =
      Annotation (RDDomain.add (written_lvs lvs) (Instruction loc) domain)

  let syscall loc lvs _ _ domain =
      Annotation (RDDomain.add (written_lvs lvs) (Instruction loc) domain)

  let assign loc lv _ _ _ domain =
      Annotation (RDDomain.add (written_lv Sv.empty lv) (Instruction loc) domain)

  let opn loc lvs _ _ _ domain = Annotation (RDDomain.add (written_lvs lvs) (Instruction loc) domain)
end

include (ForwardAnalyser.Make (ReachingDefinitionLogic))
