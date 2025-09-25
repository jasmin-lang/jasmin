type ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info = {
  pd : Wsize.wsize;
  asmOp : ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp;
  known_implicits : (CoreIdent.Name.t * string) list;
  flagnames: CoreIdent.Name.t list;
}