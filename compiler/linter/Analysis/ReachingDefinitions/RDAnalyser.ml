open Jasmin.Prog
open Jasmin.Utils
open Annotation

module ReachingDefinitionLogic :
  ForwardAnalyser.Logic with type domain = RDDomain.t = struct
  type domain = RDDomain.t

  (** Initial domain : each argument is treated as initialized at the function
      location *)
  let initialize f =
    Annotation
      (List.fold_left
         (fun dom x ->
           Mv.add x (Siloc.singleton (Jasmin.Location.i_loc0 f.f_loc)) dom)
         Mv.empty f.f_args)

  let pp fmt = RDDomain.pp fmt

  (** Check if a is included in b*)
  let included a b = RDDomain.included a b

  (** In the case of reaching definitions, we do not analyse the condition so
      this function is the identity *)
  let assume _ state = (state, state)

  let merge s1 s2 = RDDomain.join s1 s2
  let forget var domain = Annotation (RDDomain.forget (L.unloc var) domain)

  (** logic for any assignment : we kill all left variables, meaning removing
      all previously defined locations and set the location of the current
      instruction *)
  let logic loc lvs domain =
    Annotation
      (RDDomain.add (List.fold_left written_lv Sv.empty lvs) loc domain)

  let funcall loc lvs _ _ domain = logic loc lvs domain
  let syscall loc lvs _ _ domain = logic loc lvs domain
  let assign loc lv _ _ _ domain = logic loc [ lv ] domain
  let opn loc lvs _ _ _ domain = logic loc lvs domain
  let assertion loc _ _ domain = logic loc [] domain
end

include ForwardAnalyser.Make (ReachingDefinitionLogic)
