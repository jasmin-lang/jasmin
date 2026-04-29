open Prog

type modulename = Name.t

type ('len,'info, 'asm) modulearg =
  | MaParam of 'len gexpr
  | MaGlob  of 'len gexpr
  | MaFun   of ('len,'info, 'asm) gfunc

type ('len,'info, 'asm) moduleargs = ('len,'info, 'asm) modulearg list

type ('len,'info, 'asm) module_app =
  { ma_name : modulename;
    ma_func : modulename;
    ma_args : ('len,'info, 'asm) moduleargs; }

type 'len funsig =
  {
    name : funname;
    fs_tyin : 'len gty list;
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
  | MdModApp  of ('len,'info, 'asm) module_app

type ('len,'info,'asm) gmprog = ('len,'info,'asm) gmodule_item list
   (* first declaration occur at the end (i.e reverse order) *)

type ('info, 'asm) mpprog = (pexpr_,'info,'asm) gmprog


type ('len,'info,'asm) ms_funs =
  | MsFun of ('len,'info, 'asm) gfunc
  | MsModApp of ('len,'info, 'asm) module_app

type ('len,'info,'asm) ms_modules =
  | MsMod of ('len,'info, 'asm) module_summary
  | MsClone of ('len,'info, 'asm) module_app

and ('len,'info, 'asm) module_summary = {
  name : string;
  params : 'len mparamdecl list;
  globs : ('len gvar * 'len ggexpr) list;
  modules: ('len,'info,'asm) ms_modules list;
  funs : ('len, 'info, 'asm) ms_funs list;
}