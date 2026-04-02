open Prog

type modulename = Name.t

type 'len modulearg =
  | MaParam of 'len gexpr
  | MaGlob  of 'len gvar_i
  | MaFun   of funname

type 'len moduleargs = 'len modulearg list

type 'len module_app =
  { ma_name : modulename;
    ma_func : modulename;
    ma_args : 'len moduleargs; }

type 'len funsig =
  { fs_tyin : 'len gty list;
    fs_tyout : 'len gty list;
  }

type 'len mparamdecl =
  | Param of 'len gvar
  | Glob  of 'len gvar
  | Fun   of 'len funsig

type 'len mparamdecls = 'len mparamdecl list

type ('len,'info,'asm) functor_def =
  { functorname : modulename;
    functorparams : 'len mparamdecls;
    functorbody: ('len,'info,'asm) gmodule_item list
  }

and  ('len,'info,'asm) gmodule_item =
  | MdItem of ('len,'info,'asm) gmod_item
  | MdFunctor of ('len,'info,'asm) functor_def
  | MdModApp  of 'len module_app

type ('len,'info,'asm) gmprog = ('len,'info,'asm) gmodule_item list
   (* first declaration occur at the end (i.e reverse order) *)

type ('info, 'asm) mpprog = (pexpr_,'info,'asm) gmprog


type ('len,'info, 'asm) module_summary = {
  name : string;
  params : 'len mparamdecl list;
  funcs : ('len, 'info, 'asm) gfunc list;
  globs : ('len gvar * 'len ggexpr) list;
  renames : 'len module_app list;
  imodules : ('len,'info,'asm) module_summary list;
}