open Prog

type modulename = Name.t

type ('info, 'asm) modulearg =
  | MaParam of pexpr_ gexpr
  | MaGlob  of pexpr_ gvar_i
  | MaFun   of (pexpr_,'info, 'asm) gfunc

type ('info, 'asm) moduleargs = ('info, 'asm) modulearg list

type ('info, 'asm) module_app =
  { ma_name : modulename;
    ma_func : modulename;
    ma_args : ('info, 'asm) moduleargs; }

type  funsig =
  {
    name : funname;
    fs_tyin : pexpr_ gty list;
    fs_tyout : pexpr_ gty list;
  }

type mparamdecl =
  | Param of pexpr_ gvar
  | Glob  of pexpr_ gvar
  | Fun   of  funsig

type  mparamdecls =  mparamdecl list

type ('info,'asm) functor_def =
  { functorname : modulename;
    functorparams : mparamdecls;
    functorimports: string list;
    functorbody: ('info,'asm) gmodule_item list
  }

and  ('info,'asm) gmodule_item =
  | MdItem of (pexpr_,'info,'asm) gmod_item
  | MdFunctor of ('info,'asm) functor_def
  | MdModApp  of ('info, 'asm) module_app

type ('info,'asm) gmprog = ('info,'asm) gmodule_item list
   (* first declaration occur at the end (i.e reverse order) *)

type ('info, 'asm) mpprog = ('info,'asm) gmprog

type ( 'info,'asm) ms_item =
  | MsModApp of ('info, 'asm) module_app
  | MsFun of (pexpr_,'info, 'asm) gfunc
  | MsGlob of (pexpr_ gvar * pexpr_ ggexpr)
  | MsMod of ('info, 'asm) module_summary

and ('info, 'asm) module_summary = {
  name : string;
  requires: string list;
  params : mparamdecl list;
  items: ('info,'asm) ms_item list;
}