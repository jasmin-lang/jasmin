open SafetyInterfaces
    
module type AprManager = sig
  type t

  val man : t Apron.Manager.t
end

module BoxManager : AprManager with type t = Box.t

module PplManager : AprManager

(*------------------------------------------------------------*)
module AbsNumI (Manager : AprManager) (PW : ProgWrap) : AbsNumType
