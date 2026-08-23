(* ** Imports and settings *)
From elpi.apps Require Import derive.std.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq div eqtype.
From mathcomp Require Import ssralg word_ssrZ.
Require Import strings wsize utils.
Import Utf8 ZArith Lia.
Require Import ssrring.
Require Import word.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Local Open Scope Z_scope.

Section POINTER.
  
Context (pointer: eqType).

Class pointer_op (pointer: eqType) : Type := PointerOp {

  add : pointer -> Z -> pointer;
  sub : pointer -> pointer -> Z;
  p_to_z : pointer -> Z;

  add_sub : forall p k, add p (sub k p) = k;
  sub_add : forall p k, 0 <= k < wsize_size U256 -> sub (add p k) p = k;
  add_0   : forall p, add p 0 = p;

}.

Context {Pointer: pointer_op pointer}.

Fixpoint pos_is_aligned_to (p: positive) (n: nat) {struct n} : bool :=
  if n is n.+1 then
    (if p is p~0 then
      pos_is_aligned_to p n
    else false)%positive
  else true.

Lemma pos_is_aligned_toE p n :
  pos_is_aligned_to p n = (mod_pow2 p n == 0)%N.
Proof.
  elim: n p => // n ih [] // p /=.
  - by case: (_ p n).
  rewrite ih.
  by case: (_ p n).
Qed.

Definition is_aligned_to (z: Z) (n: nat) : bool :=
  match z with
  | Z0 => true
  | Zpos p => pos_is_aligned_to p n
  | Zneg _ => z mod 2 ^ Z.of_nat n == 0
  end.

Definition is_align (p: pointer) (sz: wsize) : bool :=
  is_aligned_to (p_to_z p) (wsize_log2 sz).

Lemma is_alignE p sz :
  is_align p sz = (p_to_z p mod wsize_size sz == 0)%Z.
Proof.
  rewrite /is_align; case: (p_to_z p) => // {} p; 
  rewrite /is_aligned_to wsize_size_is_pow2;
    last done.
  rewrite pos_is_aligned_toE.
  suff : (p mod 2 ^ Z.of_nat (wsize_log2 sz)) = Z.of_N (mod_pow2 p (wsize_log2 sz)).
  - case: eqP; case: eqP; lia.
  by rewrite mod_pow2E N2Z.inj_mod /= shift_nat_correct Zpower_nat_Z Z.mul_1_r.
Qed.

Global Opaque is_align.

Lemma is_align8 p : is_align p U8.
Proof. by rewrite is_alignE Zmod_1_r. Qed.


(********************************************************************)

(* Programs can make external calls that may make changes to the
caller stack at locations that are passed as call arguments. An export
function, which may be called externally, in its syntactic definition
depends on a context interface (a list of abstract chunks with input
permissions). The context of the callee is instantiated, at call time,
with chunks from the caller stack and context, over which the caller
has permissions that are not lower than those specified in the callee
context as input ones. The call takes as argument also the expected
output permissions for the context chunks. The actual execution of the
callee needs to return the caller stack and context with permissions
that are not lower than the expected ones for those chunks.

Notice that the context is really important only for external
calls. In internal calls, the arguments can be stored in the callee
frame, so there is no need to access directly the rest of the stack.
Nonetheless, also in internal calls we pass the return result location
(which btw we may even pass before zeroization, and expect to be
returned as readable).

Semantically, the callee context works as a mask on the caller stack
and the context. For this reason, it is convenient in the memory model
to distinguish the current stack, as the stack of the executing
fuction, from the current context, as a list of stacks (a stack of
stacks) associated with the branch in the call tree that is currently
executing, the idea being that each external call is associated with a
new stack. In fact, concatenating context and stack should give a
single stack that corresponds to the current frames in the
whole-program execution of the linked modules. However, the modular
execution can also be understood as interleaving execution of module
functions as non-yielding threads, each with its own stack.

A stack can be seen as a block made of a list of chunks.

The map of permissions on the memory can be inferred from the stack,
the context (each function can only access its context and its frame),
and the information about zeroization (this corresponds to validW
before zeroization and validR after; validG is kept as a global
predicate to represent allocated memory). *)

Context (funname ModName: eqType).

(*
Variant Permission : Type := Read | Write | Free. 

Definition PMap : Type := pointer -> Permission -> bool.

Definition empty_pmap : PMap := fun _ _ => false.
*)

Variant Permission : Type :=
  Bot | FWO | Top. 

Definition le_POrd (p1 p2: Permission) : bool :=
  match (p1, p2) with
  | (_, Top) => true
  | (FWO, FWO) => true
  | (Bot, _) => true
  | _ => false end.                

Definition PermSel (p1 p2: Permission) : Permission :=
  if le_POrd p1 p2 then p2 else p1.

Definition PMap : Type := pointer -> Permission.

Definition empty_pmap : PMap := fun _ => Bot.

Definition max_pmap (m1 m2: PMap) : PMap :=
  fun p => PermSel (m1 p) (m2 p).

Definition le_pmap (m1 m2: PMap) : Prop :=
  forall p, le_POrd (m1 p) (m2 p).
  
Definition is_FWO (p: Permission) : bool :=
  match p with
  | FWO => true
  | _ => false end.                            

Definition is_Top (p: Permission) : bool :=
  match p with
  | Top => true
  | _ => false end.                            

(* patch-up class - to disappear *)
Class PArith (pointer: Type) := {
     p2Z : pointer -> Z                
   ; u8_zero : u8
   ; u8_size : Z
  }.                

Context (I_PArith : PArith pointer).

(**************************************************************************)

Definition pointer_off_eq (p1 p2: pointer) (sz: Z) :=
  p2Z p2 == p2Z p1 + sz.

(* forward-directed chunks (with positive Z) *)
Definition in_chunk (c: (pointer * Z)) (p: pointer) : Prop :=
  let z := p2Z (fst c) in
  let d := snd c in
  let z0 := p2Z p in (z0 > z) /\ (z0 <= z + d).

(* equivalence between chunks and intervals (forward or backward) *)
Definition chunk_intv_eq (c: (pointer * Z)) (i: (pointer * pointer)) :
  Prop := (fst c = fst i) /\ (snd c = p2Z (fst i) - p2Z (snd i)).

Definition bIn_chunk (c: (pointer * Z)) (p: pointer) : bool :=
  let z := p2Z (fst c) in
  let d := snd c in
  let z0 := p2Z p in (Z.ltb z z0) && (Z.leb z0 (z + d)).

Definition bIn_chunks (cs: seq (pointer * Z)) (p: pointer) : bool :=
  foldr (fun c r => bIn_chunk c p || r) false cs.

Definition chunk_incl (c1 c2: (pointer * Z)) : Prop :=
  forall p, in_chunk c1 p -> in_chunk c2 p.

Definition chunk_disjoint (c1 c2: (pointer * Z)) : Prop :=
  forall p, in_chunk c1 p -> ~ (in_chunk c2 p).

Definition chunk_bIncl (c1 c2: (pointer * Z)) : bool :=
  let x1 := p2Z (fst c1) in
  let x2 := p2Z (fst c2) in
  let l1 := snd c1 in
  let l2 := snd c2 in 
  (Z.leb x2 x1) && (Z.leb (x1 + l1) (x2 + l2)).  

Definition chunk_list_bIncl (cl: seq (pointer * Z))
    (c0: (pointer * Z)) : bool :=
  foldr (fun c b => chunk_bIncl c c0 && b) true cl.                       

Definition chunk_intv_incl (c: (pointer * Z)) (i: (pointer * pointer)) :=
  forall c0, chunk_intv_eq c0 i -> chunk_incl c c0.      

Definition intv_chunk_incl (i: (pointer * pointer)) (c: (pointer * Z)) :=
  forall c0, chunk_intv_eq c0 i -> chunk_incl c0 c.      

Definition chunk_bpred_incl (c: (pointer * Z)) (bp: pointer -> bool) :=
  forall p, in_chunk c p -> bp p.

Definition chunk_pred_incl (c: (pointer * Z)) (bp: pointer -> Prop) :=
  forall p, in_chunk c p -> bp p.

Definition pw_set_pmap (cf1: PMap) (p: pointer) (x: Permission) : PMap :=
  fun p0 => match p0 == p with
    | true => x              
    | false => cf1 p0 end.               

Definition chunk_pmap_eq (cf1 cf2: PMap) (c: (pointer * Z)) : Prop :=
  chunk_pred_incl c (fun p => cf1 p = cf2 p).

Definition chunk_set_pmap_eq (cf1 cf2: PMap)
  (c: (pointer * Z)) x : Prop :=
  forall p0, if (bIn_chunk c p0) 
             then cf2 p0 = x 
             else cf2 p0 = cf1 p0.   


(**************************************************************************)

Notation Sz := Z (only parsing).


(*****************************************************************)

Record stackChunk (mem: Type) (in_ctx: seq (pointer * Sz * Permission)) : Type :=
  StackChunk {
      stackC_root : pointer
    ; stackC_limit :  pointer
    ; out_ctx : seq (pointer * Sz * Permission)                          

(*    ; stackC : mem -> seq (pointer * Sz)
    ; permissionsC : mem -> PMap                   *)    
                    
    ; stackC_max_size := p2Z stackC_root - p2Z stackC_limit
    ; stackC_max_sizeP : 0 <= stackC_max_size  
    ; stackC_memory : (pointer * Sz) := (stackC_root, stackC_max_size) 
}.      

(* program modules, with local oracles *)
Class modProg (prog: Type): Type := ModProg {
    gprog_local (pr: prog) : funname -> bool

  ; gprog_export (pr: prog) : funname -> bool

  ; gprog_oracle (pr: prog) : forall fn, funname -> gprog_export pr fn -> Sz
}.
                                         
(* program modules, with local oracles *)
Class modCProg (prog mem: Type) (M: modProg prog) : Type := ModCProg {                           
   mod_map (pr: prog) :
    forall (fn: funname), gprog_export pr fn ->
                          forall (ctx: seq (pointer * Sz * Permission)),
                            stackChunk mem ctx                                
}.

Class finGMem (prog mem: Type) : Type := FinGFMem {         

      gstack_root : prog -> pointer
    ; gstack_limit : prog -> pointer          
    ; global_memory : mem -> seq (pointer * Sz)

    ; gstack : mem -> seq (pointer * Sz)
    ; gpermissions: mem -> PMap                       
    ; gcontext_input : mem -> seq (Sz * Permission)
    ; gcontext_output : mem -> seq (Sz * Permission)
 
   (* concrete stack chunk; size; expected return permissions for the
   context passed to the call. NOTE: return permissions should be same
   as set by stackChunk (given the function name), and similarly the
   size should be same as set by the oracle *)                     
   ; concrete_gcontext : mem ->
       seq (seq (pointer * Sz) * Sz * seq (pointer * Sz * Permission))
}.

(********************************************************************)           


(* the fixed part of a module memory structure *)
Class baseMem (mem: Type) : Type := BaseMem {
      stack_root : mem -> pointer
    ; stack_limit :  mem -> pointer          
    ; gblocks : mem -> seq (pointer * Sz)

    ; stack_max_size m := p2Z (stack_root m) - p2Z (stack_limit m)
    ; stack_max_sizeP (m: mem) : 0 <= stack_max_size m 
    ; stack_memory m : (pointer * Sz) := (stack_root m, stack_max_size m) 
                           
    ; baseMem_eq (m1 m2: mem) : Prop
    ; baseMem_eqP m1 m2 : baseMem_eq m1 m2 ->
        stack_root m1 = stack_root m2 /\
        stack_limit m1 = stack_limit m2 /\
        gblocks m1 = gblocks m2  
}.                                        

(* Context (baseMem_eq : forall {mem: Type} {X: baseMem mem} (m1 m2: mem), Prop). *)

(* dynamic part of a module memory structure, with basic properties *)
(* gblocks > context root >= stack root >= stack top > stack limit >= 0 *)
Class finMem (mem: Type) (BM: baseMem mem) : Type := FinMem {         
     stack : mem -> seq (pointer * Sz)

   (* concrete stack chunk; size; expected return
   permissions for the context passed to the call *)                     
   ; concrete_context : mem ->
       seq (seq (pointer * Sz) * Sz * seq (pointer * Sz * Permission))

   (* can be defined *)
   ; concrete_context_head (m: mem) :
     (seq (pointer * Sz) * Sz * seq (pointer * Sz * Permission))                
   ; concrete_context_head_root (m: mem) : pointer 
                    
(*   ; concrete_context_head_pmap (m: mem) : PMap :=
       snd (fst (concrete_context_head m)) *)
            
   ; stack_head m : (pointer * Sz) :=
       head (stack_root m, 0) (stack m)
            
   ; stack_top m : pointer := fst (stack_head m)
                                   
   ; stack_topP (m: mem) : in_chunk (stack_memory m) (stack_top m)
                                    
   ; stack_current_size (m: mem) := p2Z (stack_root m) - p2Z (stack_top m)      
}.                                       

(* memory data operations (controlled by a function): get, set;
   validity *)
Class coreMem (mem: Type) (BM: baseMem mem) (FM: finMem BM) := CoreMem {
      get : mem -> pointer -> exec u8
    ; set : mem -> pointer -> u8 -> exec mem

    ; pt_validG : mem -> pointer -> bool
    (* validR, validW and validF can actually be defined, once we know 
       the stack, the context and the permission map *)                         
    ; pt_validR : mem -> pointer -> bool
    ; pt_validW : mem -> pointer -> bool
    ; pt_validF : mem -> pointer -> bool  
(*    ; pt_validF m p := pt_validR m p || pt_validW m p  *)
    ; pt_validZ m p := pt_validW m p || ~~ pt_validR m p  
    ; pt_validRW m p := pt_validR m p && pt_validW m p  
    ; pt_validRO m p := pt_validR m p || ~~ pt_validW m p  
    ; pt_validB m p := pt_validG m p && ~~ pt_validR m p && ~~ pt_validW m p  
    ; pt_invalid m p := ~~ (pt_validG m p)
                                 
    ; validG m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validG m)
    ; validR m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validR m)
    ; validW m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validW m)
    ; validF m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validF m)
    ; validZ m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validZ m)
    ; validRW m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validRW m)
    ; validRO m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validRO m)
    ; validB m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validB m)
    ; invalid m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_invalid m)

    ; coreMem_impl (m1 m2: mem) : Prop

    ; coreMem_implP m1 m2 := forall p w,
        get m1 p = ok w -> get m2 p = ok w                                    
                                 
    ; coreMem_eq (m1 m2: mem) : Prop 

    ; coreMem_eqP m1 m2 := baseMem_eq m1 m2 /\
       forall p, get m1 p = get m2 p                           
     
    ; get_reflectP (m: mem) : forall p,
       reflect (exists w, get m p = ok w) (pt_validR m p)

    ; set_reflectP (m: mem) : forall p w,
       reflect (exists m', set m p w = ok m') (pt_validW m p)

    ; setP (m: mem) :
       forall p w w0 w' p' m',
         set m p w = ok m' ->
         get m p' = ok w0 ->
         get m' p' = ok w' ->
         if p == p' then w' == w else w' == w0 

    ; set_preserveP (m: mem) : forall p w,
       forall m', set m p w = ok m' ->
            (pt_validR m p -> pt_validR m' p)  
            /\ pt_validW m' p  

    ; validGP m : forall p sz,
        (validR m p sz \/ validW m p sz) -> validG m p sz         
  }.

(* memory management operations (controlled by the system): fresh,
   alloc, free, zeroize; they don't change data, but can change
   permissions; zeroize is actually a hybrid, because it is
   implemented as a setting operation and it also changes data *)
Class absMem (mem: Type) : Type := AbsMem {
      empty_mem : mem
    ; fresh_loc (m: mem) (in_stk: bool) : Sz -> pointer
    ; alloc_frame : mem -> pointer -> Sz -> exec mem
    ; free_frame : mem -> pointer -> Sz -> exec mem
    ; zeroize_pt : mem -> pointer -> exec mem                                     }.

(* basic properties of memory management *)
Class memP (mem: Type) (BM: baseMem mem) (FM: finMem BM) (RM: coreMem FM)
  (AM: absMem mem) : Type := MemP { 

    fresh_loc_stackP (m: mem) (sz: Sz) :
       let p := fresh_loc m true sz in                                
       chunk_bpred_incl (p, sz) (pt_invalid m) 

 ; alloc_frameP (m: mem) (p: pointer) (sz: Sz) :
     forall m',  
          let p := fresh_loc m true sz in        
          (alloc_frame m p sz = ok m') ->
          (chunk_incl (p, sz) (stack_memory m)) /\ 
          (coreMem_eq m m') /\
          (chunk_bpred_incl (p, sz) (pt_validZ m')) 

 ; free_frameP (m: mem) (p: pointer) (sz: Sz) :    
     forall m',
          (p, sz) = stack_head m ->
          (free_frame m p sz = ok m') ->
          (chunk_bpred_incl (p, sz) (pt_validF m)) /\
          (coreMem_eq m m') /\
          chunk_bpred_incl (p, sz) (pt_invalid m) 
                           
 ; zeroize_ptP (m: mem) (p: pointer) :
      forall m',  
        (zeroize_pt m p = ok m') ->
        (set m p u8_zero = ok m') /\
        (pt_validZ m p) /\ (pt_validRW m' p) 
}.

(* program modules, with local oracles *)
Class progMod (mem: Type): Type := ProgMod {
    mod_local (md: ModName) : funname -> bool

  ; mod_export (md: ModName) : funname -> bool
                                           
  ; mod_import (md: ModName) : funname -> bool

  ; mod_context (md: ModName) :
       funname -> seq (Sz * Permission * Permission)
     (*  funname -> seq (pointer * Sz * Permission * Permission) *)

  (* 2 define *)                    
  ; mod_context_input (md: ModName) :
       funname -> seq (Sz * Permission)
  ; mod_context_output (md: ModName) :
       funname -> seq (Sz * Permission)
            
  ; mod_defined (md: ModName) (fn: funname) : bool := 
      mod_local md fn || mod_export md fn

(*  ; mod_contextP md fn : ~~ mod_export md fn /\ ~~ mod_import md fn ->
       mod_context md fn = nil                   *)
}.                               

(* multi-module programs *)
Class progMem (prog mem: Type) (BM: baseMem mem)
  (PMM: progMod mem) : Type := ProgMem {
     def_module (pr: prog) : ModName -> bool

   ; prog_oracle (pr: prog) : funname -> Sz

   (* the oracle agrees with the stack size in each module *)                   
   ; prog_oracleP (pr: prog) (m: mem) : forall md, def_module pr md ->
       forall fn m, prog_oracle pr fn <= stack_max_size m

   (* linking consistency: no function name conflict allowed *)     
   ; def_modulesP (pr: prog) :
     forall md1 md2, def_module pr md1 /\ def_module pr md2 ->
        (exists fn, mod_defined md1 fn /\ mod_defined md2 fn) ->
        md1 = md2             
}.                                                        

(* adding permissions, with properties *)
Class permMem (mem: Type) (BM: baseMem mem) (FM: finMem BM)
  (CM: coreMem FM) : Type := PermMem {
     permissions (m: mem) : PMap 

  ; validZ_permP (m: mem) (p: pointer) (sz: Sz) :
       validZ m p sz = 
           chunk_bpred_incl (p, sz)  
             (fun p0 => is_FWO (permissions m p0))
             
  ; validRW_permP (m: mem) (p: pointer) (sz: Sz) :
       validRW m p sz = 
           chunk_bpred_incl (p, sz)  
             (fun p0 => is_Top (permissions m p0))
}.

(* adding permissions, with properties *)
Class stackMem (prog mem: Type) (BM: baseMem mem) (FM: finMem BM)
  (CM: coreMem FM) (AM: absMem mem) (PRM: @permMem mem BM FM CM)
  (PMM: progMod mem) (PM: @progMem prog mem BM PMM) : Type :=
  StackMem {
    frame_size : Sz               
                   
  ; check_input_permissions : (seq (pointer * Sz)) -> PMap ->
                                (seq (Sz * Permission)) -> Prop

  ; check_output_permissions : PMap ->
                                (seq (Sz * Permission)) -> Prop                                                           
  ; mk_ctx_mask : (seq (pointer * Sz)) -> (seq (Sz * Permission)) ->
                  seq (pointer * Sz * Permission)

  (* before allocation *)                    
    (* get the context of fn; find the permissions for the context in
       m0; those should be higher than the context input permissions.
       make a mask from the input context permissions (we are before
       allocation). *)                                                            ; init_external_call pr md fn (m0 m1: mem) (args: seq (pointer * Sz)) :
      Prop :=
      let ctx_imask := mod_context_input md fn in
      let ctx_omask := mod_context_output md fn in
      let ctx_fmask := mk_ctx_mask args ctx_omask in 
(*      let concr_ctx := concrete_context m0 in *)
(*      let pm0 := concrete_context_head_pmap m0 *)
      let pm0 := permissions m0 in      
      (* the args need to match something in concr_ctx, and the
          current permissions need to be not lower than the input
          permission of ctx_mask. in the case of internal calls, the
          args are stored in the frame and the context is only the
          return value location *)
          check_input_permissions args pm0 ctx_imask /\         
          stack_root m1 = fresh_loc m0 true (prog_oracle pr fn)
                    (* stack_top m0 + 1 *) /\
          stack_max_size m1 = prog_oracle pr fn   
                    (* stack_limit m1 = stack_limit m0 *) /\
      (* still need to check the consistency of m1 *)  
          concrete_context m1 =
              (stack m0, prog_oracle pr fn, ctx_fmask) ::
                (concrete_context m0) /\
          stack m1 = nil   

  (* after deallocation *)
    (* get the context of fn; find the permissions for the context in
       m0; those should be higher than the context output permissions.
       make a mask from the output context permissions (we are after
       deallocation). *)
   ; final_external_call md fn (m0 m1: mem) (args: seq (pointer * Sz)) :
      Prop :=
      let ctx_imask := mod_context_input md fn in
      let ctx_omask := mod_context_output md fn in
      let ctx_fmask := mk_ctx_mask args ctx_omask in 
(*      let concr_ctx := concrete_context m0 in *)
(*      let pm0 := concrete_context_head_pmap m0 *)
      let pm0 := permissions m0 in      
      (* the args need to match something in concr_ctx, and the
          current permissions need to be not lower than the input
          permission of ctx_mask. in the case of internal calls, the
          args are stored in the frame and the context is only the
          return value location *)
          stack m0 = nil /\
          check_output_permissions pm0 ctx_omask /\
          stack m1 = fst (fst (concrete_context_head m0)) /\
                       
          stack_root m1 = concrete_context_head_root m0 /\
          stack_max_size m1 = snd (fst (concrete_context_head m0)) 
                    (* stack_limit m1 = stack_limit m0 *) /\
      (* still need to check the consistency of m1 *)  
          concrete_context m1 = List.tail (concrete_context m0)

                       
}.        

(* NOTE: no need to add permission maps to the stack. just make the
checks against the context interface, and perform the changes as in
shared memory *)    

(* NOTE: make the context mask part of the stack? but then, this would
mean again having stack entries for external functions. make the
context mask part of the concrete context?  yes. each context chunk
should record: the permission map at the time of the final external
call; the expected output permission map for the initial one. so the
new stack will start from the context input map (which needs to be
checked against the final permissions of the top context chunk), then
carry out frame allocation, and at the end, after deallocation, the
permissions should be checked against the context output ones. this
output permissions will be used to update the permission map of the
con PM2text top chunk, when this is set back to be the stack in continuing
the execution. *)

(* all together *)
Class fullMem (prog mem: Type) (BM: baseMem mem) (FM: finMem BM)
  (CM: coreMem FM) (AM: absMem mem) 
  (PM: @memP mem BM FM CM AM) (PRM: @permMem mem BM FM CM) (PMM: progMod mem)
  (PM2: @progMem prog mem BM PMM)
  (STM: @stackMem prog mem BM FM CM AM PRM PMM PM2)          
  : Type := FullMem {}.

End POINTER.

(* NOTE: make abs_stack part of frames, to avoid problems with passes
that change the stack structure (e.g. linearization) *)

(* NOTE: understand how to reinstate the caller context/stack
   distinction when the callee returns *)


(*              
  (* from m0 to m1, merges the stack into the context *)            
  ; stack2context (m0 m1: mem) : Prop :=
      coreMem_eq m0 m1 /\
      stack_root m1 = stack_top m0 /\
      context m1 = frames m0 ++ context m0 /\
      frames m1 = nil /\
      abs_stack m1 = nil /\  
      context_pmap m1 = astack_hd m0  

  (* import context and frames of m0 as context into m1  *)                     
  ; linking_callee (m0 m1: mem) : Prop :=
      stack_top m0 = context_root m0 /\
      stack_current_size m0 = context_size m1 /\
      p2Z (stack_limit m1) <= p2Z (stack_limit m0) /\
      context m1 = context m0 /\
      le_pmap (context_pmap m1) (astack_hd m0)   
}.
*)

(* NOTE: context and frames are both class attributes, but
    instance-wise frames is going to be a record field, context is
    going to be a parameter *)




(*** NOT USED ******************************************************)

(*
Context (efunname lfunname : eqType)

Variant FunName := EFN (fn: efunname) | LFN (efn: efunname) (lfn: lfunname).

Definition FunName_eq (x y : FunName) : bool :=
  match x, y with
  | EFN f, EFN g => f == g
  | LFN e l, LFN e' l' => (e == e') && (l == l')
  | _, _ => false
  end.

Lemma FunName_eqP : Equality.axiom FunName_eq.
Proof.
  case=> [f|e l] [g|e' l']; simpl.
  - apply: (iffP eqP).
    + by move=> ->.
    + intro H. inversion H; subst; auto.
  - constructor. discriminate.
  - constructor. discriminate.
  - apply: (iffP andP).
    + intros [H H0].
      f_equal; apply/eqP; auto.
    + move=> [-> ->].
      by rewrite eqxx eqxx.
Qed.

Definition FunName_eqMixin := FunName_eqP. 

HB.instance Definition _ := hasDecEq.Build FunName FunName_eqMixin.
*)

(*******************************************************************)

(*
Definition PermMap : Type := FunName -> Permission. 

Definition pw_set_pmap' (cf1: pointer -> PermMap) (p: pointer) (fn: FunName)
  (x: Permission) : pointer -> PermMap :=
  fun p0 => match p == p0 with
    | true => fun fn0 => match fn == fn0 with
                         | true => x
                         | false => cf1 p0 fn0 end              
    | false => cf1 p0 end.               

Definition chunk_pmap_eq' (cf1 cf2: pointer -> PermMap)
  (c: (pointer * Sz)) : Prop :=
  chunk_pred_incl c (fun p => forall fn, cf1 p fn = cf2 p fn).

Definition chunk_set_pmap_eq' (cf1 cf2: pointer -> PermMap)
  (c: (pointer * Sz)) fn x : Prop :=
  forall p0 fn0, if (bIn_chunk c p0) && (fn0 == fn) 
                 then cf2 p0 fn0 = x 
                 else cf2 p0 fn0 = cf1 p0 fn0.   


(* adding permissions, with properties *)
Class capMem (mem: Type) (BM: baseMem mem) (FM: finMem BM)
  (CM: coreMem FM) (AM: absMem mem): Type := CapMem {
    exec_fun : mem -> FunName                       

  ; capability : mem -> pointer -> PermMap
                                                        
  ; validWP' (m: mem) (p: pointer) (sz: Sz) (fn: FunName) :
       let fn := exec_fun m in 
       validW m p sz <-> 
           chunk_bpred_incl (p, sz)  
             (fun p0 => is_FWO (capability m p0 fn))
             
  ; validRP' (m: mem) (p: pointer) (sz: Sz) (fn: FunName) :
       let fn := exec_fun m in 
       validR m p sz <-> 
           chunk_bpred_incl (p, sz)  
             (fun p0 => is_Top (capability m p0 fn))

 ; alloc_frameP2' (m: mem) (p: pointer) (sz: Sz) :
     let fn := exec_fun m in    
     forall m',
          let p := fresh_loc m true sz in        
          (alloc_frame m p sz = ok m') ->
          (chunk_set_pmap_eq' (capability m) (capability m')
                (p, sz) fn FWO)

 ; free_frameP2' (m: mem) (p: pointer) (sz: Sz) :
     forall m',
          p = stack_top m ->
          (free_frame m p sz = ok m') ->
          forall fn, (chunk_set_pmap_eq' (capability m) (capability m')
                            (p, sz) fn Bot)
}.



Variant Permission1 : Type :=
  Bot1 | FO1 | WO1 | RO1 | FWO1 | FRO1 | WRO1 | Top1. 

Definition can_write (p: Permission1) : bool :=
  match p with
  | WO1 | FWO1 | WRO1 | Top1 => true
  | _ => false end.                            

Definition can_read (p: Permission1) : bool :=
  match p with
  | RO1 | FRO1 | WRO1 | Top1 => true
  | _ => false end.                            

Definition can_free (p: Permission1) : bool :=
  match p with
  | FO1 | FWO1 | FRO1 | Top1 => true
  | _ => false end.                            

Definition can_allocate (p: Permission1) : bool :=
  match p with
  | Bot1 => true
  | _ => false end.                            

(* chunks going backward *)
Definition in_bkchunk (c: (pointer * Sz)) (p: pointer) : Prop :=
  let z := p2Z (fst c) in
  let d := sz2Z (snd c) in
  let z0 := p2Z p in (z0 <= z) /\ (z0 > z - d).

Definition bIn_bkchunk (c: (pointer * Sz)) (p: pointer) : bool :=
  let z := p2Z (fst c) in
  let d := sz2Z (snd c) in
  let z0 := p2Z p in (Z.leb z0 z) && (Z.ltb (z - d) z0).

Definition bkchunk_incl (c1 c2: (pointer * Sz)) :=
  forall p, in_bkchunk c1 p -> in_bkchunk c2 p.

Definition bkchunk_intv_incl (c: (pointer * Sz)) (i: (pointer * pointer)) :=
  forall c0, chunk_intv_eq c0 i -> bkchunk_incl c c0.      

Definition intv_bkchunk_incl (i: (pointer * pointer)) (c: (pointer * Sz)) :=
  forall c0, chunk_intv_eq c0 i -> bkchunk_incl c0 c.      

Definition bkchunk_bpred_incl (c: (pointer * Sz)) (bp: pointer -> bool) :=
  forall p, in_bkchunk c p -> bp p.

Definition bkchunk_pred_incl (c: (pointer * Sz)) (bp: pointer -> Prop) :=
  forall p, in_bkchunk c p -> bp p.

Definition bkchunk_pmap_eq (cf1 cf2: pointer -> PermMap)
  (c: (pointer * Sz)) : Prop :=
  bkchunk_pred_incl c (fun p => forall fn, cf1 p fn = cf2 p fn).

Definition bkchunk_set_pmap_eq (cf1 cf2: pointer -> PermMap)
  (c: (pointer * Sz)) fn x : Prop :=
  forall p0 fn0, if (bIn_bkchunk c p0) && (fn0 == fn) 
                 then cf2 p0 fn0 = x 
                 else cf2 p0 fn0 = cf1 p0 fn0.   

(* DONE 1. remove local oracles, add weak oracle consistency with stack
   size, add linking properties *)

(* DONE 2. switch from permission (pointer and fuction) maps to
   capabilities (pointer maps) *)

(* DONE 3. fix validity wrt alignment *)

(* DONE: need to introduce notion of base frame for the context *)
*)



(*******************************************************************)
(*******************************************************************)

(*
Class progMem (prog mem: Type) (BM: baseMem mem) (FM: finMem BM)
  (CM: capMem BM) (AM: absMem mem) (RM: coreMem mem)
  (PM: @memP mem BM FM CM AM RM)            
  : Type := ProgMem {
     mod_main (pr: prog) : efunname -> bool
                                                       
   ; oracle (pr: prog) : efunname -> option Sz

   ; mod_mem (pr: prog) : efunname -> option mem

   ; oracleP (pr: prog) : forall fn,
       (exists sz, oracle pr fn = sz) <-> mod_main pr fn

   ; mod_memP (pr: prog) : forall fn,
       (exists m, mod_mem pr fn = m) <-> mod_main pr fn
                                                   
   (* the oracle agrees with the stack size in each module *)                   
   ; det_oracle (pr: prog) : forall fn m sz, mod_mem pr fn = Some m ->
                                  oracle pr fn = Some sz ->
                                  sz2Z sz = stack_max_size m

   (* the oracle agrees with the local oracle in each module *)   
   ; det_local_oracle (pr: prog) :
     forall fn m sz, mod_mem pr fn = Some m ->
                     local_oracle m fn = Some sz ->
                                       oracle pr fn = Some sz      
  }.


*)

(***********************************************************
  **********************************************************)

(*

Context (program: Type).

(* should be modules rather than function names *)
Class memory (mem: Type) (FM: finMem mem)
  (AM: absMem mem) (CM: coreMem mem) (pr: program)
  : Type := Mem {         
       mod_main : funname -> bool
     ; mod_mem (fn: funname) (mf: mod_main fn) : mem
     ; mod_memP (fn: funname) (mf: mod_main fn) :
       @memP mem FM AM CM fn (@mod_mem fn mf)        
    (* ; mod_local (fn: funname) (mf: mod_main fn) : funname -> option bool *)
  }.


(* NOTE: 1) fix conditions for alloc, free, zeroize. 2) is AO really
   useful?  3) think more about oracles and local functions *)


(************************************************************************)

Class memory (mem: Type) (AM: absMem mem) (CM: coreMem mem) (pr: program)
  : Type := Mem {
       program_fun : funname -> bool          
     ; is_module_main : forall (fn: funname), program_fun fn -> bool
 (* WRONG: should it return mem? *)
     ; mod_mem : forall (fn: funname) (pf: program_fun fn),
         is_module_main pf -> finMem mem }.
         
Print reflect.


(* NOTE: 1) init not needed; just need to make sure blocks are above
stack_root. 2) consider zeroization. 3) consider permissions, from the
point of view of local functions. *)


Class memory (mem: Type) (fn: funname) (* (CM: coreMem pointer mem) *) :
  Type :=
  Memory {
      (* root >= top >= limit >= 0 *)
      (* top of the stack: stack_top = head _ (frames m) *)
      (* current size of the stack: stack_size = stack_root - stack_top *)
      (* maximum stack size: stack_max_size = stack_root - stack_limit *)
      (* therefore: stack_size <= stack_max_size *)
      (* stack_region_is_free - p still free and available for allocation: 
         stack_limit <= p < stack_top *)
      (* so the allocatable region is: stack_top - stack_limit *)
      (* top_stack_below_root: stack_top <= stack_root *)
      stack_root : mem -> pointer
    ; stack_limit : mem -> pointer
    ; frames : mem -> seq pointer
    ; fresh_loc : mem -> Size -> pointer
    (* replaces mem_incr, uses fresh_loc *)                      
    ; alloc_region : mem -> Size -> exec mem
    (* alignment, size, extra initial size, extra-size *)
    (*    ; alloc_stack : mem -> wsize -> Z -> Z -> Z -> exec mem 
           (* alignment, size, extra initial size, extra-size *) *)
    (* we only need to free the head of the stack *)
    ; free_frame : mem -> mem
    (* initialize the empty memory with a sequence of blocks, all
    above the stack root (hence uses stack_root an alloc_region) *)             
    ; init : seq (pointer * Size) -> exec mem 
    ; permission : mem -> pointer -> Permission 
                                                 
    ; stack_top : mem -> pointed := head (stack_root m) (frames m)                                             
    ; stack_region_is_free : ∀ (m: mem) (p: pointer), wunsigned (stack_limit m) <= wunsigned p < wunsigned (head (stack_root m) (frames m)) → ~~ validw m Aligned p U8
    ; top_stack_below_root : ∀ (m: mem), wunsigned (head (stack_root m) (frames m)) <= wunsigned (stack_root m)
    }.




  Record frame := { frame_off : Z; frame_size : Z ; frame_padding : Z }.

  Definition footprint_of_frame (f: frame) : Z :=
    frame_size f + frame_padding f.

  (** Total size of the stack, padding included *)
  Definition footprint_of_stack (frames: seq frame) :=
    foldr (λ f, Z.add (footprint_of_frame f)) 0 frames.

  (** Frames are valid when:
    - sizes are positive
    - stack does not overflow
  *)
  Definition valid_frame (f: frame) : bool :=
    [&& 0 <=? frame_off f, frame_off f <=? frame_size f & 0 <=? frame_padding f].
  
  Definition valid_frames (stk_limit stk_root: pointer) (frames: seq frame) :=
    all valid_frame frames && (footprint_of_stack frames <=? wunsigned stk_root - wunsigned stk_limit).

  
(* from memory_example.mem_ *)
Class ConcreteMemory (Frame: Type) (fn: funname) := {
(*    data      : Mz.t u8;
    alloc     : Mz.t unit; *)
    stk_root  : pointer; (* root of the stack *)
    stk_limit : pointer; (* limit of the stack *)
    frames    : seq frame; (* shape of the frames on the stack *)
    framesP   : valid_frames stk_limit stk_root frames;
    stk_allocP x : pointer_into_stack x stk_root frames → is_zalloc alloc x;
    stk_freeP x : 0 <= x < wunsigned stk_root - footprint_of_stack frames → is_zalloc alloc x = false;
  }.

Class support (Sup: Type) := Support {
  sup_empty : Sup ;
  fresh_frame : Sup -> pointer ;
  sup_incr : Sup -> Sup ;
  sup_in : pointer -> Sup -> Prop ;
                                 
  sup_dec : forall p s, (sup_in p s) + not (sup_in p s) ;
  empty_in : forall p, not (sup_in p sup_empty) ;
  freshness : forall s, not (sup_in (fresh_frame s) s) ;
  sup_incr_in : forall p s, sup_in p (sup_incr s) <->
                              (sup_in p s \/ p = fresh_frame s) ;
}.                                 

Class coreMem (core_mem: Type) (f: funname) := CoreMem {
  get : core_mem -> pointer -> exec u8;
  set : core_mem -> pointer -> u8 -> exec core_mem;
  valid8 : core_mem -> pointer -> bool;
  permission : core_mem -> pointer -> Permission ;

  setP :
    forall m p w p' m',
      set m p w = ok m' ->
      get m' p' = if p == p' then ok w else get m p';
  valid8P : forall m p w,
      reflect (exists m', set m p w = ok m') (valid8 m p); 
  get_valid8 : forall m p w, get m p = ok w -> valid8 m p;
  valid8_set : forall m p w m' p',
      set m p w = ok m' -> valid8 m' p' = valid8 m p';

  setP_ok m p : forall w m', set m p w = ok m' -> can_write (permission m p);
  getP_ok m p : forall w, get m p = ok w -> can_read (permission m p);
  validP_ok m p : valid8 m p -> can_free (permission m p); 
}.

Class support (Sup: Type) := Support {
  sup_empty : Sup ;
  fresh_frame : Sup -> pointer ;
  sup_incr : Sup -> Sup ;
  sup_in : pointer -> Sup -> Prop ;
                                 
  sup_dec : forall p s, (sup_in p s) + not (sup_in p s) ;
  empty_in : forall p, not (sup_in p sup_empty) ;
  freshness : forall s, not (sup_in (fresh_frame s) s) ;
  sup_incr_in : forall p s, sup_in p (sup_incr s) <->
                              (sup_in p s \/ p = fresh_frame s) ;
}.                                 

(* idea: instantiate valid8_set with a support type *)

End POINTER.


(* -------------------------------------------------------------------- *)

(** This type describes whether a memory access must check for alignment.
  With Unaligned, there are no particular constraints.
  With Aligned, the pointer must be a multiple of the size of the access. *)
#[only(eqbOK)] derive
Variant aligned := Unaligned | Aligned.

HB.instance Definition _ := hasDecEq.Build aligned aligned_eqb_OK.

Definition aligned_le (x y: aligned) : bool :=
  (x == Unaligned) || (y == Aligned).



(* LittleEndian *)
Module LE.

  Definition encode sz (w: word sz) : seq u8 := split_vec U8 w.
  Definition decode sz (n: seq u8)  : word sz := make_vec sz n.

  Lemma size_encode sz (w: word sz) :
    size (encode w) = Z.to_nat (wsize_size sz).
  Proof.
    by rewrite /encode /split_vec size_map size_iota => {w}; case: sz.
  Qed.

  Lemma decodeK sz (w: word sz) :
    decode sz (encode w) = w.
  Proof. by rewrite /decode /encode make_vec_split_vec. Qed.

  Lemma decode_inj sz (bs bs': seq u8) :
    size bs = size bs' →
    size bs = Z.to_nat (wsize_size sz) →
    decode sz bs = decode sz bs' →
    bs = bs'.
  Proof.
    by move => eqsz hsz /make_vec_inj; apply.
  Qed.

  Definition wread8 ws (v:word ws) (k:Z) :=
    nth 0%w (encode v) (Z.to_nat k).

  Lemma encode8E (w: u8): encode w = [:: w].
  Proof.
  Local Opaque word.subword.
    have {2}<-:= decodeK w.
    rewrite /encode /decode /make_vec /split_vec divnn modnn /= mul0n.
    by rewrite Z.lor_0_r /wrepr word.ureprK.
  Local Transparent word.subword.
  Qed.

  Lemma encodeE s (w:word s) : encode w = [seq wread8 w k | k <- ziota 0 (wsize_size s)].
  Proof.
    symmetry; apply (eq_from_nth (x0 := 0%R)).
    + by rewrite size_map size_ziota size_encode.
    move=> i; rewrite size_map size_ziota => hi.
    by rewrite (nth_map 0%Z) ?size_ziota // nth_ziota // Z.add_0_l /wread8 Nat2Z.id.
  Qed.

  Lemma read0 ws x :
    wread8 (ws := ws) 0 x = 0%R.
  Proof.
    rewrite /LE.wread8 /LE.encode /split_vec.
    case: (Nat.le_gt_cases (ws %/ U8 + ws %% U8) (Z.to_nat x)) => h0.
    - rewrite nth_default; first done.
      rewrite size_map size_iota.
      by apply/leP.
    rewrite (nth_map O); first last.
    - rewrite size_iota.
      by apply/ltP.
    rewrite /word.subword -word.urepr_word word.urepr_lsr Z.shiftr_0_l.
    exact/eqP.
  Qed.

End LE.


(* -------------------------------------------------------------------- *)
Module Export CoreMem.
Section CoreMem.

  Context {funname: Type} {pointer: eqType} {Pointer: pointer_op pointer}.
  Context {core_mem: Type} {CM: coreMem funname pointer core_mem}.

  Definition is_aligned_if (al: aligned) (ptr: pointer) (sz: wsize) : bool :=
    if al is Aligned then is_align ptr sz else true.

  Lemma is_aligned_if_is_align al ptr sz :
    is_align ptr sz → is_aligned_if al ptr sz.
  Proof. by rewrite /is_aligned_if => ->; case: al. Qed.

  Lemma aligned_leP al al' p sz :
    aligned_le al al' →
    is_aligned_if al' p sz →
    is_aligned_if al p sz.
  Proof. by case: al => // /eqP ->. Qed.
  
  Definition read (f: option funname) (m: core_mem) (al: aligned) (ptr: pointer) (sz: wsize) : exec (word.word sz) :=
    Let _ := assert (is_aligned_if al ptr sz) ErrAddrInvalid in
    Let l := mapM (fun k => get f m (add ptr k)) (ziota 0 (wsize_size sz)) in
    ok (LE.decode sz l).

  Definition write (f: option funname) (m:core_mem) (al: aligned) (ptr:pointer) (sz:wsize) (w: word sz) : exec core_mem :=
    Let _ := assert (is_aligned_if al ptr sz) ErrAddrInvalid in
    let bytes := LE.encode w in
    foldM (fun k m => set f m (add ptr k) (nth 0%w bytes (Z.to_nat k))) m (ziota 0 (wsize_size sz)).

  Definition validw (f: option funname) (m:core_mem) (al: aligned) (ptr:pointer) (sz:wsize) :=
    is_aligned_if al ptr sz && all (fun k => valid8 f m (add ptr k)) (ziota 0 (wsize_size sz)).

  Lemma valid8_validw f m al p : valid8 f m p = validw f m al p U8.
  Proof. by rewrite /validw is_aligned_if_is_align ?is_align8 // /= add_0 andbT. Qed.

  Lemma validwP f m al p ws :
    reflect (is_aligned_if al p ws ∧ ∀ k, 0 <= k < wsize_size ws -> validw f m al (add p k) U8) (validw f m al p ws).
  Proof.
    apply (iffP andP).
    + by move=> [? /allP h]; split => // k hk; rewrite -valid8_validw; apply h; rewrite in_ziota !zify.
    by move=> [? h]; split => //;apply/allP => k; rewrite in_ziota !zify (valid8_validw _ _ al); apply h.
  Qed.

  Lemma validw8_alignment f al' m al p :
    validw f m al p U8 = validw f m al' p U8.
  Proof. by rewrite /validw !is_aligned_if_is_align // is_align8. Qed.

  Lemma read8_alignment f al' m al p :
    read f m al p U8 = read f m al' p U8.
  Proof. by rewrite /read !is_aligned_if_is_align // is_align8. Qed.

  Lemma get_read8 f m al p: get f m p = read f m al p U8.
  Proof.
    rewrite /read is_aligned_if_is_align /= ?is_align8 // /= add_0.
    by case: get => //= w; rewrite -LE.encode8E LE.decodeK.
  Qed.

  Lemma set_write8 f m al p w: set f m p w = write f m al p w.
  Proof.
    rewrite /write is_aligned_if_is_align; last by rewrite is_align8.
    have := LE.encode8E w; rewrite LE.encodeE /= => -[->].
    rewrite add_0.
    by case: set.
  Qed.

  Lemma readE f m al p sz :
    read f m al p sz =
      Let _ := assert (is_aligned_if al p sz) ErrAddrInvalid in
      Let l := mapM (fun k => read f m al (add p k) U8) (ziota 0 (wsize_size sz)) in
      ok (LE.decode sz l).
  Proof.
    by rewrite {1}/read !ziotaE; case: is_aligned_if => //=; f_equal; apply eq_mapM => k _; apply get_read8.
  Qed.

  Lemma write_valid8_eq f m m' al p s (v :word s) :
    write f m al p v = ok m' ->
    forall p',
    valid8 f m' p' = valid8 f m p'.
  Proof.
    rewrite /write; t_xrbindP => ? hfold p'; move: m hfold.
    apply ziota_ind => /= [ m [->]//| i l _ hrec m]; t_xrbindP => ? h /hrec ->.
    by apply (valid8_set _ h).
  Qed.

  Lemma write_validw_eq f m m' al p s (v :word s) :
    write f m al p v = ok m' ->
    forall al' p' s',
    validw f m' al' p' s' = validw f m al' p' s'.
  Proof.
    by move=> hw al' p' s'; rewrite /validw; f_equal; apply all_ziota => ? _; apply (write_valid8_eq hw).
  Qed.

  Lemma write_read8 f m m' al p ws (v: word ws) :
    write f m al p v = ok m' ->
    forall al' k, read f m' al' k U8 =
      let i := sub k p in
       if (0 <=? i) && (i <? wsize_size ws) then ok (LE.wread8 v i)
       else read f m al' k U8.
  Proof.
    rewrite /write; t_xrbindP => _ h al' k; move: h.
    rewrite -(@in_ziota 0 (wsize_size ws)).
    move: m; apply ziota_ind => /=; first by move=> ? [<-].
    move=> i l hi hrec m; t_xrbindP => mi hset /hrec ->.
    rewrite in_cons -!get_read8 (setP _ hset) orbC.
    case: ifP => //= _.
    case: eqP => [<- | hne].
    + rewrite sub_add ?eq_refl //.
      have : wsize_size ws <= wsize_size U256 by case: (ws).
      lia.
    by case: eqP => // heq; case: hne; rewrite -heq add_sub.
  Qed.

  Lemma eq_read f m1 m2 al p ws :
    (forall al' i, 0 <= i < wsize_size ws -> read f m1 al' (add p i) U8 = read f m2 al' (add p i) U8) ->
    read f m1 al p ws = read f m2 al p ws.
  Proof.
    Opaque Z.to_nat.
    move=> h8; rewrite !readE ziotaE; case: is_aligned_if => //=; f_equal.
    apply eq_mapM => k /mapP[] n; rewrite mem_iota add0n => /andP[] /leP ? /ltP ? ?; subst.
    apply: h8.
    Lia.lia.
  Qed.

  Lemma writeV f s (v:word s) m al p:
    reflect (exists m', write f m al p v = ok m') (validw f m al p s).
  Proof.
    rewrite /write /validw; case: is_aligned_if => //; last by constructor => -[].
    rewrite ziotaE /=.
    elim: iota m => /=; first by move=> ?; constructor; eauto.
    move=> k l hrec m.
    apply (iffP andP).
    + move=> [] /valid8P -/(_ (LE.wread8 v (Z.of_nat k))) [m'] hset hall.
      by rewrite hset;apply/hrec; apply: sub_all hall => i; rewrite (valid8_set _ hset).
    move=> [m'];t_xrbindP => m'' hset hf; split.
    + by apply/valid8P; eexists; eauto.
    apply/sub_all; last by apply/hrec; eexists; eauto.
    by move=> i;rewrite (valid8_set _ hset).
  Qed.

  Lemma readV f m al ptr sz w :
    read f m al ptr sz = ok w ->
    validw f m al ptr sz.
  Proof.
    move=> h; apply /validwP; move: h; rewrite /read; t_xrbindP => -> l h _; split => //.
    move=> k hk; have {hk}: k \in ziota 0 (wsize_size sz).
    + by rewrite in_ziota !zify.
    rewrite -valid8_validw.
    move: l h;apply ziota_ind => //= i li hi hr ?.
    t_xrbindP => wi hwi; have ?:= get_valid8 hwi.
    by move=> l /hr{}hr _; rewrite inE => /orP [/eqP ->| /hr].
  Qed.

  Lemma read8_read f m al p s v:
    (forall al' i, 0 <= i < wsize_size s -> read f m al' (add p i) U8 = ok (LE.wread8 v i)) ->
    read f m al p s = if is_aligned_if al p s then ok v else Error ErrAddrInvalid.
  Proof.
    rewrite readE => h8; case: is_aligned_if => //.
    have -> : mapM (λ k, read f m al (add p k) U8) (ziota 0 (wsize_size s)) =
                   ok (map (λ k, LE.wread8 v k) (ziota 0 (wsize_size s))).
    + by apply ziota_ind => //= k l hk ->; rewrite h8.
    by rewrite -{2}(LE.decodeK v) LE.encodeE ziotaE.
  Qed.

  Lemma read_read8 f m al p s v:
    read f m al p s = ok v ->
    is_aligned_if al p s /\ (forall i, 0 <= i < wsize_size s -> read f m al (add p i) U8 = ok (LE.wread8 v i)).
  Proof.
    rewrite readE; t_xrbindP => ha l hl.
    rewrite -{1}(LE.decodeK v) => /LE.decode_inj.
    rewrite -(size_mapM hl) size_ziota LE.size_encode => /(_ refl_equal refl_equal) ?; subst l.
    rewrite LE.encodeE in hl.
    split => // i hi.
    have : i \in ziota 0 (wsize_size s) by rewrite in_ziota !zify.
    move: hl; apply ziota_ind => //= k l hk hrec.
    t_xrbindP => w hw ws hws ??; subst w ws.
    by rewrite inE => /orP [/eqP -> | /(hrec hws)].
  Qed.

  Lemma writeP_eq f m m' al p s (v :word s):
    write f m al p v = ok m' ->
    read f m' al p s = ok v.
  Proof.
    move=> hw.
    rewrite (read8_read (m:=m') al (v:= v) (p:=p)).
    + by have /validwP [->] : validw f m al p s by apply /writeV; eexists; eauto.
    move=> al' k hk.
    rewrite (write_read8 hw) sub_add /=.
    + by case: andP => //; rewrite !zify; lia.
    have : wsize_size s <= wsize_size U256 by case: (s).
    lia.
  Qed.

  Lemma aligned_le_read f m p sz v al al' :
    aligned_le al al' →
    read f m al' p sz = ok v →
    read f m al p sz = ok v.
  Proof. by rewrite /read; t_xrbindP => h /(aligned_leP h) -> ? -> /= ->. Qed.

  Lemma aligned_le_write f al al' m p sz (w: word sz) m' :
    aligned_le al al' →
    write f m al' p w = ok m' →
    write f m al p w = ok m'.
  Proof. by rewrite /write; t_xrbindP => /aligned_leP h /h -> ->. Qed.

  Definition disjoint_range p s p' s' :=
    forall i i', 0 <= i < wsize_size s -> 0 <= i' < wsize_size s' ->
       add p i <> add p' i'.

  Lemma disjoint_range_U8 p sz p' :
    (∀ i, 0 <= i < wsize_size sz → p' ≠ add p i) →
    disjoint_range p sz p' U8.
  Proof.
    move => h i i' i_range.
    change (wsize_size U8) with 1%Z => i'_range.
    have -> : i' = 0 by Lia.lia.
    rewrite {i' i'_range} add_0 => ?.
    exact: (h _ i_range).
  Qed.

  Lemma writeP_neq f m m' al p s (v :word s) al' p' s':
    write f m al p v = ok m' ->
    disjoint_range p s p' s' ->
    read f m' al' p' s' = read f m al' p' s'.
  Proof.
    move=> hw hd; apply eq_read => a k hk.
    rewrite (write_read8 hw) /=.
    case: andP => //; rewrite !zify => hin.
    elim: (hd (sub (add p' k) p) k) => //; by rewrite add_sub.
  Qed.

  Lemma disjoint_range_valid_not_valid_U8 f m al1 p1 ws1 p2 :
    validw f m al1 p1 ws1 ->
    ~ validw f m Aligned p2 U8 ->
    disjoint_range p1 ws1 p2 U8.
  Proof.
    move=> /validwP [hal1 hval1] hnval.
    red; rewrite wsize8 => i i' i_range ?.
    have ? : i' = 0 by Lia.lia.
    subst; rewrite add_0.
    move => ?; subst; apply: hnval; apply/validwP; split.
    + by apply is_align8.
    move=> k; rewrite wsize8 => hk; have ->: k = 0%Z by Lia.lia.
    rewrite add_0 (validw8_alignment f al1).
    exact: hval1.
  Qed.

  Lemma read_write_any_mem f m1 m1' ar aw pr pw szw (vw:word szw) m2 m2':
    read f m1 ar pr U8 = read f m1' ar pr U8 ->
    write f m1 aw pw vw = ok m2 ->
    write f m1' aw pw vw = ok m2' ->
    read f m2 ar pr U8 = read f m2' ar pr U8.
  Proof.
    move=> hr hw hw'.
    by rewrite (write_read8 hw) (write_read8 hw') /=; case: andP.
 Qed.

 Definition disjoint_zrange_ovf p s p' s' : Prop :=
   ∀ i i' : Z, 0 <= i < s → 0 <= i' < s' → add p i ≠ add p' i'.
 
End CoreMem.
End CoreMem.


Require Import word.

(* ** Memory
 * -------------------------------------------------------------------- *)

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

Definition no_overflow (p: pointer) (sz: Z) : bool :=
  (wunsigned p + sz <=? wbase Uptr)%Z.

Definition disjoint_zrange (p: pointer) (s: Z) (p': pointer) (s': Z) :=
  [/\ no_overflow p s,
      no_overflow p' s' &
      wunsigned p + s <= wunsigned p' \/
        wunsigned p' + s' <= wunsigned p]%Z.

Definition disjoint_range p s p' s' :=
  disjoint_zrange p (wsize_size s) p' (wsize_size s').

Definition zbetween (pstk : pointer) (sz : Z) (p : pointer) (sz' : Z) : bool :=
  ((wunsigned pstk <=? wunsigned p) && (wunsigned p + sz' <=? wunsigned pstk + sz))%Z.

Definition between (pstk : pointer)  (sz : Z) (p : pointer) (s : wsize) : bool :=
  zbetween pstk sz p (wsize_size s).

Lemma no_overflow_incl p1 sz1 p2 sz2 :
  zbetween p1 sz1 p2 sz2 ->
  no_overflow p1 sz1 ->
  no_overflow p2 sz2.
Proof. by rewrite /zbetween /no_overflow !zify; lia. Qed.

Lemma zbetween_refl p sz : zbetween p sz p sz.
Proof. by rewrite /zbetween !zify; lia. Qed.

Lemma zbetween_trans p1 sz1 p2 sz2 p3 sz3 :
  zbetween p1 sz1 p2 sz2 ->
  zbetween p2 sz2 p3 sz3 ->
  zbetween p1 sz1 p3 sz3.
Proof.
  rewrite /between => /andP [] /ZleP a /ZleP b /andP [] /ZleP c /ZleP d.
  apply/andP; split; apply/ZleP; lia.
Qed.

Lemma zbetween_le p sz1 sz2 :
  sz2 <= sz1 ->
  zbetween p sz1 p sz2.
Proof. by rewrite /zbetween !zify; lia. Qed.

Lemma between_byte pstk sz b i sz' :
  no_overflow b sz' →
  zbetween pstk sz b sz' →
  0 <= i ∧ i < sz' →
  between pstk sz (b + wrepr Uptr i) U8.
Proof.
  rewrite /zbetween !zify; change (wsize_size U8) with 1 => novf [] lo hi i_range.
  rewrite wunsigned_add; first lia.
  move: (wunsigned_range b); lia.
Qed.

Lemma not_zbetween_neg p1 p2 sz1 sz2 :
  (sz1 <= 0)%Z ->
  (0 < sz2)%Z ->
  ~~ zbetween p1 sz1 p2 sz2.
Proof. by move=> ??; apply /idP; rewrite /zbetween !zify; lia. Qed.

Lemma zbetween_not_disjoint_zrange p1 s1 p2 s2 :
  zbetween p1 s1 p2 s2 ->
  0 < s2 ->
  ~ disjoint_zrange p1 s1 p2 s2.
Proof. by rewrite /zbetween !zify => hb hlt [_ _ ?]; lia. Qed.

Lemma not_between_U8_disjoint_zrange p1 sz1 p2 :
  no_overflow p1 sz1 ->
  ~ between p1 sz1 p2 U8 ->
  disjoint_zrange p1 sz1 p2 (wsize_size U8).
Proof.
  move=> hnover.
  rewrite /between /zbetween wsize8 !zify => hnb.
  split=> //; last by lia.
  rewrite /no_overflow zify.
  have := wunsigned_range p2.
  by lia.
Qed.

Lemma disjoint_zrange_sym p1 sz1 p2 sz2 :
  disjoint_zrange p1 sz1 p2 sz2 ->
  disjoint_zrange p2 sz2 p1 sz1.
Proof.
  rewrite /disjoint_zrange; move=> [*]; split=> //; lia.
Qed.

Lemma disjoint_zrange_incl p1 s1 p2 s2 p1' s1' p2' s2' :
  zbetween p1 s1 p1' s1' ->
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2' s2'.
Proof.
  rewrite /zbetween /disjoint_zrange /no_overflow !zify.
  by move=> ?? [/ZleP ? /ZleP ? ?]; split; rewrite ?zify; lia.
Qed.

Lemma disjoint_zrange_incl_l p1 s1 p2 s2 p1' s1' :
  zbetween p1 s1 p1' s1' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1' s1' p2 s2.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

Lemma disjoint_zrange_incl_r p1 s1 p2 s2 p2' s2' :
  zbetween p2 s2 p2' s2' ->
  disjoint_zrange p1 s1 p2 s2 ->
  disjoint_zrange p1 s1 p2' s2'.
Proof. by move=> ?; apply disjoint_zrange_incl=> //; apply zbetween_refl. Qed.

Lemma disjoint_zrange_byte p1 sz1 p2 sz2 i :
  disjoint_zrange p1 sz1 p2 sz2 ->
  0 <= i /\ i < sz2 ->
  disjoint_zrange p1 sz1 (p2 + wrepr _ i) (wsize_size U8).
Proof.
  move=> hd hrange.
  case: (hd) => _ hover _.
  apply: disjoint_zrange_incl_r hd.
  apply: (between_byte hover) => //.
  by apply zbetween_refl.
Qed.

Lemma disjoint_zrange_add p sz p' sz1 sz2 :
  0 < sz ->
  0 <= sz1 ->
  0 < sz2 ->
  no_overflow p' (sz1 + sz2) ->
  disjoint_zrange p sz p' sz1 ->
  disjoint_zrange p sz (p' + wrepr _ sz1) sz2 ->
  disjoint_zrange p sz p' (sz1 + sz2).
Proof.
  move=> hsz hsz1 hsz2 hover' [hover _ hdisj] [_ _ hdisj'].
  split=> //.
  move: hdisj'; rewrite wunsigned_add; first by lia.
  by move: hover'; rewrite /no_overflow zify; have := wunsigned_range p'; lia.
Qed.

Lemma disjoint_zrange_U8 p sz p' sz' :
  0 < sz ->
  0 < sz' ->
  no_overflow p' sz' ->
  (forall k, 0 <= k /\ k < sz' -> disjoint_zrange p sz (p' + wrepr _ k) (wsize_size U8)) ->
  disjoint_zrange p sz p' sz'.
Proof.
  move=> hsz /[dup] /Z.lt_le_incl.
  move: sz'; apply: natlike_ind; first by lia.
  move=> sz' hsz' ih _ hover hdisj.
  have /Z_le_lt_eq_dec [?|?] := hsz'.
  + apply disjoint_zrange_add => //; last by apply hdisj; lia.
    apply ih => //.
    + by move: hover; rewrite /no_overflow !zify; lia.
    by move=> k hk; apply hdisj; lia.
  subst sz'.
  rewrite -(GRing.addr0 p') -wrepr0.
  by apply hdisj; lia.
Qed.

Definition pointer_range (lo hi: pointer) : pred pointer :=
  λ p, (wunsigned lo <=? wunsigned p) && (wunsigned p <? wunsigned hi).

Lemma pointer_rangeP lo hi pr :
  reflect (wunsigned lo <= wunsigned pr < wunsigned hi) (pointer_range lo hi pr).
Proof. by apply: (iffP idP); rewrite /pointer_range !zify. Qed.

Lemma pointer_range_incl_l lo lo' hi pr :
  (wunsigned lo' <= wunsigned lo)%Z ->
  pointer_range lo hi pr ->
  pointer_range lo' hi pr.
Proof. by rewrite /pointer_range !zify; lia. Qed.

Lemma pointer_range_incl_r lo hi hi' pr :
  (wunsigned hi <= wunsigned hi')%Z ->
  pointer_range lo hi pr ->
  pointer_range lo hi' pr.
Proof. by rewrite /pointer_range !zify; lia. Qed.

Lemma pointer_range_between lo hi pr :
  pointer_range lo hi pr = between lo (wunsigned hi - wunsigned lo) pr U8.
Proof.
  rewrite /pointer_range /between /zbetween wsize8.
  by apply /idP/idP; rewrite !zify; lia.
Qed.

(* -------------------------------------------------- *)
(** Pointer arithmetic *)

#[ global ]
Instance PointerW : pointer_op pointer.
Proof.
refine
  {| add p k   := (p + wrepr Uptr k)%w
   ; sub p1 p2 := wunsigned (p1 - p2)%w
   ; p_to_z p  := wunsigned p
  |}.
- abstract (move=> p k; rewrite wrepr_unsigned add_wordE sub_wordE; ssring).
- abstract (move=> p k => hk;
  rewrite -{2}(@wunsigned_repr_small Uptr k);
    [ f_equal; rewrite add_wordE sub_wordE; ssring
    | have := wsize_size_wbase U256;
      have := wbase_m (wsize_le_U8 (@Uptr pd));
      Lia.lia ]).
- abstract (move => p; rewrite wrepr0 add_wordE; ssring).
Defined.

Lemma addE p k : add p k = (p + wrepr Uptr k)%R.
Proof. by []. Qed.

Lemma subE p1 p2 : sub p1 p2 = wunsigned (p1 - p2).
Proof.
Local Opaque sub_word.
  by rewrite [LHS]/= sub_wordE.
Local Transparent sub_word.
Qed.

Lemma addC p i j : add (add p i) j = add p (i + j).
Proof. by rewrite /= wrepr_add !add_wordE; ssring. Qed.

Lemma p_to_zE p : p_to_z p = wunsigned p.
Proof. done. Qed.

Global Opaque PointerW.

Lemma disjoint_zrange_alt a m b n :
  disjoint_zrange a m b n →
  disjoint_zrange_ovf a m b n.
Proof.
  case => /ZleP ha /ZleP hb D i j hi hj.
  rewrite !addE => K.
  suff : wunsigned a + i = wunsigned b + j by Lia.lia.
  have a_range := wunsigned_range a.
  have b_range := wunsigned_range b.
  do 2 rewrite <-wunsigned_add by Lia.lia.
  by rewrite K.
Qed.

Lemma zbetween_disjoint_zrange_ovf a b p m n s :
  zbetween a n b m → disjoint_zrange_ovf p s a n → disjoint_zrange_ovf p s b m.
Proof.
  rewrite /zbetween /disjoint_zrange_ovf !zify => - [] hlo hhi D i i' hi hi' K.
  set ofs := wunsigned b - wunsigned a.
  have hofs : 0 <= ofs + i' < n by Lia.lia.
  apply: (D _ _ hi hofs).
  rewrite K /ofs !addE wrepr_add wrepr_sub !wrepr_unsigned GRing.addrA.
  f_equal.
  by rewrite GRing.addrC GRing.subrK.
Qed.

Lemma disjoint_range_alt p1 ws1 p2 ws2 :
  disjoint_range p1 ws1 p2 ws2 ->
  CoreMem.disjoint_range p1 ws1 p2 ws2.
Proof.
  case; rewrite /no_overflow !zify => hover1 hover2 hdisj i1 i2 hi1 hi2.
  rewrite !addE => /(f_equal wunsigned).
  have h1 := wunsigned_range p1.
  have h2 := wunsigned_range p2.
  by rewrite !wunsigned_add; lia.
Qed.

Lemma is_align_modE ptr sz : (wunsigned ptr mod wsize_size sz == 0)%Z = is_align ptr sz.
Proof. by rewrite is_alignE p_to_zE (rwP eqP). Qed.

Lemma is_align_mod ptr sz : reflect (wunsigned ptr mod wsize_size sz = 0)%Z (is_align ptr sz).
Proof. rewrite -is_align_modE; apply eqP. Qed.

Lemma is_align_addE (ptr1:pointer) sz :
  is_align ptr1 sz ->
  forall ptr2, is_align (ptr1 + ptr2)%R sz = is_align ptr2 sz.
Proof.
  have hn := wsize_size_pos sz.
  move => /is_align_mod h ptr2; rewrite -!is_align_modE.
  by rewrite /wunsigned mathcomp.word.word.addwE -/(wbase Uptr) mod_wbase_wsize_size -Zplus_mod_idemp_l h.
Qed.

Lemma is_align_add (ptr1 ptr2:pointer) sz :
  is_align ptr1 sz -> is_align ptr2 sz -> is_align (ptr1 + ptr2)%R sz.
Proof. by move=> /is_align_addE ->. Qed.

Lemma is_align_m sz sz' (ptr: pointer) :
  (sz' ≤ sz)%CMP →
  is_align ptr sz →
  is_align ptr sz'.
Proof.
  rewrite !is_alignE.
  have wsnz s : wsize_size s ≠ 0.
  - by have := wsize_size_pos s.
  move => /wsize_size_le le /eqP /Z.mod_divide - /(_ (wsnz _)) /(Z.divide_trans _ _ _ le) {}le.
  by apply/eqP/Z.mod_divide.
Qed.

Lemma is_align_mul sz j : is_align (wrepr Uptr (wsize_size sz * j)) sz.
Proof.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by lia.
  by rewrite is_alignE p_to_zE wunsigned_repr mod_wbase_wsize_size Z.mul_comm Z_mod_mult.
Qed.

Lemma is_align_no_overflow ptr sz :
  is_align ptr sz → no_overflow ptr (wsize_size sz).
Proof.
  rewrite /no_overflow is_alignE p_to_zE => /eqP ha; apply/ZleP.
  have hn := wsize_size_pos sz.
  have hnz : wsize_size sz ≠ 0%Z by lia.
  move: (wunsigned ptr) (wunsigned_range ptr) ha => {}ptr.
  have [a ->] := wsize_size_div_wbase sz Uptr.
  move: (wsize_size sz) hn hnz => n hn hnz hr /Zmod_divides [] // q ?; subst ptr.
  cut (q + 1 <= a)%Z; nia.
Qed.

Notation do_align := align_word (only parsing).

Lemma do_align_is_align sz p : is_align (do_align sz p) sz.
Proof. rewrite is_alignE; apply align_word_aligned. Qed.

Lemma is_align_array ptr sz j :
  is_align ptr sz → is_align (wrepr _ (wsize_size sz * j) + ptr)%R sz.
Proof. by move=> hptr; apply is_align_add => //; apply is_align_mul. Qed.

(** Rounds the given size to the next larger-or-equal multiple of [ws] *)
Definition round_ws (ws:wsize) (sz: Z) : Z :=
  (let d := wsize_size ws in
   let: (q, r) := Z.div_eucl sz d in
   if r == 0 then sz else (q + 1) * d)%Z.

Lemma round_ws_aligned ws sz :
  (round_ws ws sz) mod wsize_size ws == 0.
Proof.
  have ws_pos : wsize_size ws ≠ 0 by case: ws.
  apply/eqP; rewrite Z.mod_divide // /round_ws.
  elim_div => z z' /(_ ws_pos) [] ->{sz} D.
  case: eqP => ?.
  - exists z; lia.
  exists (z + 1); lia.
Qed.

Lemma round_ws_range ws sz :
  sz <= round_ws ws sz < sz + wsize_size ws.
Proof.
  have ws_pos := wsize_size_pos ws.
  rewrite /round_ws; elim_div => ? ? [] // -> []; last by lia.
  case: eqP; lia.
Qed.

Lemma round_wsE ws sz : round_ws ws sz =
  if (sz mod wsize_size ws == 0)%Z then sz else sz + wsize_size ws - sz mod wsize_size ws.
Proof.
  have ws_pos: wsize_size ws ≠ 0 by case: ws.
  rewrite /round_ws.
  elim_div => ? ? /(_ ws_pos) [] ->{sz} D.
  case: eqP => ? //.
  by lia.
Qed.

(*********************************************************************)

Class memory (mem: Type) (CM: coreMem pointer mem) : Type :=
  Memory {  
      stack_root : mem -> pointer
    ; stack_limit : mem -> pointer
    ; frames : mem -> seq pointer
    ; alloc_stack : mem -> wsize -> Z -> Z -> Z -> exec mem (* alignment, size, extra initial size, extra-size *)
    ; free_stack : mem -> mem
    ; init : seq (pointer * Z) → pointer → exec mem

    ; stack_region_is_free : ∀ (m: mem) (p: pointer), wunsigned (stack_limit m) <= wunsigned p < wunsigned (head (stack_root m) (frames m)) → ~~ validw m Aligned p U8
    ; top_stack_below_root: ∀ (m: mem), wunsigned (head (stack_root m) (frames m)) <= wunsigned (stack_root m)
    }.

#[ global ] Arguments Memory {mem CM} _ _ _ _ _ _ _.
#[ global ] Arguments top_stack_below_root {mem CM} _.

Definition top_stack {mem: Type} {CM: coreMem pointer mem} {M: memory CM} (m: mem) : pointer :=
  head (stack_root m) (frames m).

Section SPEC.
  Context mem (CM: coreMem pointer mem) (M: memory CM)
    (m: mem) (ws:wsize) (sz: Z) (ioff:Z) (sz': Z) (m': mem) .
  Let pstk := top_stack m'.

  Definition top_stack_after_alloc (top: pointer) (ws: wsize) (sz: Z) : pointer :=
    do_align ws (top + wrepr Uptr (- sz)).

  Record alloc_stack_spec : Prop := mkASS {
    ass_read_old8 : forall p, validw m Aligned p U8 -> read m Aligned p U8 = read m' Aligned p U8;
    ass_read_new  : forall p, ~validw m Aligned p U8 -> validw m' Aligned p U8 -> read m' Aligned p U8 = Error ErrAddrInvalid;
    ass_valid     : forall p, validw m' Aligned p U8 = validw m Aligned p U8 || between (pstk + wrepr _ ioff) (sz - ioff) p U8;
    ass_align_stk : is_align pstk ws;
    ass_above_limit: wunsigned (stack_limit m) <= wunsigned pstk ∧ wunsigned pstk +  sz + Z.max 0 sz' <= wunsigned (top_stack m);
    ass_ioff      : 0 <= ioff <= sz;
    ass_fresh     : forall al p s, validw m al p s ->
                        (wunsigned p + wsize_size s <= wunsigned pstk \/
                         wunsigned pstk + sz <= wunsigned p)%Z;
    ass_root      : stack_root m' = stack_root m;
    ass_limit     : stack_limit m' = stack_limit m;
    ass_frames    : frames m' = top_stack_after_alloc (top_stack m) ws (sz + sz') :: frames m;
  }.

  Record stack_stable : Prop := mkSS {
    ss_root: stack_root m = stack_root m';
    ss_limit: stack_limit m = stack_limit m';
    ss_frames: frames m = frames m';
  }.

  Record free_stack_spec : Prop := mkFSS {
    fss_read_old8 : forall p, validw m' Aligned p U8 -> read m Aligned p U8 = read m' Aligned p U8;
    fss_valid    : ∀ p, validw m' Aligned p U8 = validw m Aligned p U8 && ~~ pointer_range (top_stack m) (top_stack m') p;
    fss_root : stack_root m' = stack_root m;
    fss_limit : stack_limit m' = stack_limit m;
    fss_frames : frames m' = behead (frames m);
   }.

  Lemma ass_align (ass:alloc_stack_spec) ofs s :
    (s <= ws)%CMP ->
    is_align (pstk + wrepr _ ofs)%R s = is_align (wrepr _ ofs) s.
  Proof.
    by move=> hs; apply/is_align_addE;apply: is_align_m (ass_align_stk ass).
  Qed.

  Lemma ass_add_ioff (ass: alloc_stack_spec) :
    wunsigned (pstk + wrepr _ ioff) = wunsigned pstk + ioff.
  Proof.
    have ? := ass_above_limit ass; have ? := ass_ioff ass.
    rewrite wunsigned_add //.
    assert (h := wunsigned_range (top_stack m)).  assert (h' := wunsigned_range pstk).
    lia.
  Qed.

  Lemma ass_read_old (ass:alloc_stack_spec) al p s : validw m al p s -> read m al p s = read m' al p s.
  Proof.
    move /validwP => [] ha hv; apply eq_read => al' k hk.
    rewrite 2!(read8_alignment Aligned).
    apply: (ass_read_old8 ass).
    rewrite (validw8_alignment al).
    exact: hv.
  Qed.

  Lemma fss_read_old (fss:free_stack_spec) al p s :
    validw m' al p s -> read m al p s = read m' al p s.
  Proof.
    move /validwP => [] ha hv; apply eq_read => al' k hk.
    rewrite 2!(read8_alignment Aligned).
    apply: (fss_read_old8 fss).
    rewrite (validw8_alignment al).
    exact: hv.
  Qed.

  (* ass_fresh using pointer_range *)
  Lemma ass_fresh_alt (ass:alloc_stack_spec) p :
    validw m Aligned p U8 ->
    ~ pointer_range pstk (top_stack m) p.
  Proof.
    move=> hvalid.
    rewrite /pointer_range !zify => hpointer.
    have habove := ass.(ass_above_limit).
    move: hvalid; apply /negP.
    apply stack_region_is_free.
    by rewrite -/(top_stack _); lia.
  Qed.

  (* TODO: we could also prove [no_overflow pstk (sz + Z.max 0 sz')] *)
  Lemma ass_no_overflow (ass:alloc_stack_spec) :
    no_overflow pstk sz.
  Proof.
    rewrite /no_overflow zify.
    assert (hover := wunsigned_range (top_stack m)).
    have := ass.(ass_above_limit).
    by lia.
  Qed.

  (* ass_fresh using disjoint_zrange *)
  Lemma ass_fresh_disjoint_zrange (ass:alloc_stack_spec) p s :
    validw m Aligned p s ->
    disjoint_zrange p (wsize_size s) pstk sz.
  Proof.
    move=> /[dup] /ass.(ass_fresh) hfresh hvalid.
    split=> //.
    + apply is_align_no_overflow.
      by move: hvalid => /validwP [? _].
    by apply (ass_no_overflow ass).
  Qed.

  (* part of ass_above_limit using disjoint_zrange *)
  (* the new frame is disjoint from the rest of the stack *)
  Lemma ass_above_limit_disjoint_zrange (ass:alloc_stack_spec) :
    disjoint_zrange
      pstk (sz + Z.max 0 sz')
      (top_stack m) (wunsigned (stack_root m) - wunsigned (top_stack m)).
  Proof.
    split.
    - rewrite /no_overflow zify.
      have := ass.(ass_above_limit).
      have := [elaborate wunsigned_range (top_stack m)].
      by lia.
    - rewrite /no_overflow zify.
      have := [elaborate wunsigned_range (stack_root m)].
      by lia.
    by left; have := ass.(ass_above_limit); lia.
  Qed.

End SPEC.

#[ global ] Arguments alloc_stack_spec {_ _ _} _ _ _ _ _.
#[ global ] Arguments stack_stable {_ _ _} _ _.
#[ global ] Arguments free_stack_spec {_ _ _} _ _.

Definition is_stack_stable mem {CM : coreMem pointer mem} {M : memory CM} m m' :=
  [&& stack_root m == stack_root m'
    , stack_limit m == stack_limit m'
    & frames m == frames m'].

Lemma stack_stableP mem {CM : coreMem pointer mem} {M : memory CM} m m' :
  reflect (stack_stable m m') (is_stack_stable m m').
Proof.
  apply: (equivP and3P); split.
  + by move=> [/eqP ? /eqP ? /eqP ?]; constructor.
  by move=> [-> -> ->]; rewrite !eqxx.
Qed.

Lemma stack_stable_trans mem {CM : coreMem pointer mem} {M : memory CM} m2 m1 m3 :
   stack_stable m1 m2 -> stack_stable m2 m3 -> stack_stable m1 m3.
Proof. by move=> [???] [???]; split; congruence. Qed.

Lemma stack_stable_sym mem {CM : coreMem pointer mem} {M : memory CM} m1 m2 : stack_stable m1 m2 -> stack_stable m2 m1.
Proof. by case; constructor. Qed.

Lemma top_stack_after_aligned_alloc p ws sz :
  is_align p ws ->
  top_stack_after_alloc p ws sz = (p + wrepr Uptr (- round_ws ws sz))%R.
Proof.
  rewrite is_alignE p_to_zE => /eqP hal.
  rewrite round_wsE.
  rewrite /top_stack_after_alloc.
  apply wunsigned_inj.
  rewrite align_wordE.
  rewrite !wrepr_opp.

  have h: (wunsigned (p - wrepr Uptr sz) mod wsize_size ws = - (sz mod wsize_size ws) mod wsize_size ws)%Z.
  + by rewrite wunsigned_sub_mod Zminus_mod hal Z.sub_0_l wunsigned_repr mod_wbase_wsize_size.

  case: eqP => hsz.
  + by rewrite h Z.mod_opp_l_z // ?Zmod_mod // Z.sub_0_r.
  rewrite Z.mod_opp_l_nz // Zmod_mod // in h.
  rewrite -Z.add_sub_assoc -h.
  rewrite wrepr_add -{1}[p in RHS](GRing.subrK (wrepr Uptr sz)) GRing.addrKA.
  rewrite [RHS]wunsigned_sub //.
  have [hle hlt] := wunsigned_range (p - wrepr Uptr sz).
  have := Z.mod_le _ _ hle (wsize_size_pos ws).
  have := Z_mod_lt (wunsigned (p - wrepr Uptr sz)) (wsize_size ws) ltac:(done).
  move: (wunsigned (p - wrepr Uptr sz)) hlt.
  lia.
Qed.

Lemma top_stack_after_alloc_bounded p ws sz :
  0 <= sz ∧ sz <= wunsigned p ->
  wunsigned p - wunsigned (top_stack_after_alloc p ws sz) <= sz + wsize_size ws - 1.
Proof.
  move=> hsz.
  rewrite /top_stack_after_alloc.
  have := align_word_range ws (p + wrepr _ (- sz)).
  rewrite wunsigned_add; first by lia.
  by have := wunsigned_range p; lia.
Qed.

End WITH_POINTER_DATA.

Module Type MemoryT.

Parameter mem : PointerData -> Type.
#[ global ] Arguments mem {_}.

Section WITH_POINTER_DATA.
Context {pd: PointerData}.

#[ global ] Declare Instance CM : coreMem pointer mem.
#[ global ] Declare Instance M : memory CM.

(*Parameter readV : forall m p s v,
  read m p s = ok v -> validw m p s. *)

(* -------------------------------------------------------------------- *)
Parameter alloc_stackP : forall m m' ws sz ioff sz',
  alloc_stack m ws sz ioff sz' = ok m' -> alloc_stack_spec m ws sz ioff sz' m'.

Parameter alloc_stack_complete : forall m ws sz ioff sz',
  let: old_size := wunsigned (stack_root m) - wunsigned (top_stack m) in
  let: max_size := wunsigned (stack_root m) - wunsigned (stack_limit m) in
  let: available := max_size - old_size in
  [&& 0 <=? ioff, ioff <=? sz, 0 <=? sz' &
  if is_align (top_stack m) ws
  then round_ws ws (sz + sz') <=? available (* tight bound *)
  else sz + sz' + wsize_size ws - 1 <=? available (* loose bound, exact behavior is under-specified *)
  ] →
  ∃ m', alloc_stack m ws sz ioff sz' = ok m'.

Parameter write_mem_stable : forall m m' al p s (v:word s),
  write m al p v = ok m' -> stack_stable m m'.

Parameter free_stackP : forall m,
  free_stack_spec m (free_stack m).

End WITH_POINTER_DATA.
End MemoryT.

*)
