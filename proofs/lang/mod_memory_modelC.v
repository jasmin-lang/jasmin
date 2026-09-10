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

(** The Jasmin memory model is concrete, particularly insofar as it
keeps memory consumption upfront into account. We follow the existing
model on this and on using Z for size - although: why not using
positive numbers instead? On the other hand, we make the type of
pointers abstract, and we rely on an abstract freshness operator to
find fresh memory chunks (that is, available ones for allocation,
where each chunk is defined by a pointer and a size; e.g. a stack is
defined as a list of chunks, each corresponding to a frame; a list of
arguments is also defined as a list of chunks).

We want to support contexts and modules. To make it simpler for now we
consider 'modular' program signatures that distinguish between local
(or internal) functions and export functions and that have a
main. Each export function depends on a context (a list of chunks) in
its definition as well as in its memory model. We express this by
abstracting over contexts in the corresponding notions. At this stage,
we simply identify program modules with export functions. Crucially,
each export function can be defined (and given a semantics) in
isolation, given the local ones and just the signature of the other
export functions it uses. Local functions may call export functions,
but they need to be always defined from the empty context.

Linking a modular program where all modules are Jasmin functions,
should produce a whole program where all functions are local (save for
the main one; so the resulting program is 'whole' but might still be
'open'). Each export function (except for the main one) is redefined
as a local one, eliminating its context by turning it into arguments
and results.

Concretely, external calls can be either Jasmin, Linear or Assembly
functions, and they may need to allocate a stack at runtime. In order
to keep the memory model as concrete as possible, on top of a global
stack size, we include a stack maximum size in the signature of each
export function.

Notice that in general, an executing function can only access its own
stack frame (which is allocated and deallocated by the function
itself) and its context instance (on which the function as no
deallocation power).

Basically, any function can make an external call to an export one,
and this call may write to the caller stack at locations that are
passed as writable arguments in its context. At call time, the context
abstraction of the callee is instantiated (by function application)
with chunks from the current continuation: more precisely, from the
caller stack frame and its context.

The continuation is updated every time the program either makes an
external call or returns from it, and it is (essentially) a list of
pairs of stack chunks and context instances. This 'stack of stacks'
should give the semantics an interleaving flavour, as if each call
involved spawning a thread that blocks the calling one and does not
yield until it terminates (thus, a kind of trivial concurrency). A
possible alternative to this approach would be that of maintaing a
stack of export call frames; but this seems both more labourious and
more constraining.

In fact, by choosing a sequentional implementation of freshness, it
should be possible to append the current stack to the flattening of
the continuation stack chunks, obtaining a single stack that
corresponds to the stack in the whole-program execution of the linked
program. On the other hand, one can opt for a 'parallel'
implementation of freshness with multiple stacks. The notion of
support (used for freshness) remains the same.

Notice that the context only matters for external calls. In internal
calls, the Jasmin semantics ensures that the arguments are stored in
the callee frame, so there is no need to access directly the rest of
the stack. Nonetheless, also in internal calls we pass the location to
store the return result. The notion of context is a generalization of
this idea, designed to avoid the need to (artificially) require that
an external call packs all the contextual runtime changes as a return
result, and to support the introduction of pre- and post-condition in
the export function signature. Anyway: this is basically the way we
can eliminate contexts when we do the linking (for Jasmin functions,
at least).

At call time, we consider preconditions and postconditions on the
caller context as well as on the callee one.
*)

Local Open Scope Z_scope.

Section MODEL.

(** Abstract pointers *)
  
Context (pointer: eqType) (funname: eqType).

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

(* temporary: patch-up class *)
Class PArith (pointer: Type) := {
     p2Z : pointer -> Z                
   ; u8_zero : u8
   ; u8_size : Z
  }.                
Context (I_PArith : PArith pointer).


(**************************************************************************)

(** Chunks *)

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


(**************************************************************************)

(** Memory model *)

Notation Sz := Z (only parsing).

Notation CSeq := (seq (pointer * Sz)) (only parsing).

Notation Ctx := (seq (pointer * Sz)) (only parsing).

Notation CPred := (CSeq -> Prop) (only parsing).  

(* Notation CBounds := (PMap -> CSeq -> CPerms -> Prop) (only parsing). *)

Context (frame_size : Sz).
  (* perm_bounded : CBounds) (restrict_pmap : PMap -> Ctx -> PMap *)               

(* context paired with memory *)
Record eMem (mem: Type) : Type :=
   EMem { base_ctx: Ctx ; base_mem : mem }.

(* either context or memory (might be useful, but not used so far) *)
Variant xMem (mem: Type) : Type := XMem (m: mem) | XCtx (ctx: Ctx).

(* export functions fixed parameters: stack max size, pre- and
   post-conditions for context permissions. *)
Record expParams : Type := ExpParams {
    stack_size : Sz
  ; ctx_pre : CPred 
  ; ctx_post : CPred                                
}.
                      
(* modular program signature (NOTE: only the part that is relevant to
   the memory model), with local functions, export functions, a main,
   and an oracle for the export functions parameters *)
Class modProg (prog: Type) : Type := ModProg {
    prog_local (pr: prog) : funname -> bool
  ; prog_export (pr: prog) : funname -> bool
  ; prog_main (pr: prog) : funname
  ; prog_mainP (pr: prog) : prog_export pr (prog_main pr) 
  ; prog_oracle (pr: prog) (fn: funname) : prog_export pr fn -> expParams
  ; prog_main_params pr : expParams := prog_oracle (prog_mainP pr)      
}.

(* freshness operator *)
Class freshSpec : Type := FreshSpec {
      fresh_loc (in_stk: bool) : Ctx -> CSeq -> Sz -> pointer
}.

(* immutable global memory spec with global blocks and the main
   parameters; the stack root is defined using freshness from a memory
   which is empty (except for the global blocks) *)
Class fixedMem (mem: Type) : Type :=
  FixedMem {
      main_pars : mem -> expParams                      
    ; fixed_blocks : mem -> seq (pointer * Sz)

    ; stack_root m : pointer
(*    := fresh_loc true (fixed_blocks m) (stack_size (main_pars m)) *)
                                          
    ; fstack_chunk m : (pointer * Sz) :=
        (stack_root m, stack_size (main_pars m))      
}.      

(* parameters of concrete stack chunks: context post-permissions,
   chunk size and chunk root *)
Record cstackParams : Type := CStackParams {
      cstack_post : CPred 
    ; cstack_size : Sz
    ; cstack_root : pointer                   
}.                    

(* concrete stack chunks for the continuation, packed with context
   instance (depending on a global context instance),
   post-permissions, size and root; post-permissions and size are
   'remembered' from the signature; the root is determined by cstack
   unless it is empty *)
Record cStack : Type :=
  CStack {
      cstack : CSeq
    ; cstack_ctx : Ctx -> Ctx
    ; cstack_params : cstackParams                   
}.                    
(* default value *)
Definition empty_cstack (pd: CPred) (p: pointer) : cStack :=
  CStack nil id (CStackParams pd 0 p).
(* Definition empty_cstack (p: pointer) : cStack :=
  CStack nil id (CStackParams nil 0 p). *)

(* mutable global memory with the current stack chunk (cstack),
   continuation and global permission map *)
Class globMem (mem: Type) (FM: fixedMem mem) : Type :=
  GlobMem {         
     gcstack : mem -> cStack

   ; gcontinuation : mem -> seq cStack

   ; gstack m : CSeq := cstack (gcstack m)

   ; gstack_ctx m : Ctx -> Ctx := cstack_ctx (gcstack m)
                               
   ; gparams m : cstackParams := cstack_params (gcstack m)

   ; gsupport m : CSeq :=
       gstack m ++ (List.concat (map cstack (gcontinuation m)))

   ; gstack_root m := cstack_root (gparams m) 
                               
   ; gstack_head m : (pointer * Sz) :=
       head (gstack_root m, 0) (gstack m)
   
   ; gstack_top m : pointer := fst (gstack_head m)
                                   
   ; gstack_topP (m: mem) : in_chunk (fstack_chunk m) (gstack_top m)
                                    
   ; gstack_current_size m : Z :=
       p2Z (gstack_root m) - p2Z (gstack_top m)
}.

(* memory data operations (controlled by the program): get, set;
   validity. validR, validW and validF can be defined, once we know
   the stack, the context and the permission map *)                         
Class coreMem (mem: Type) := CoreMem {                    
      get : @eMem mem -> pointer -> exec u8
    ; set : @eMem mem -> pointer -> u8 -> exec (@eMem mem)

    ; pt_validG : mem -> pointer -> bool
    ; pt_validR : mem -> pointer -> bool
    ; pt_validW : mem -> pointer -> bool
    ; pt_validF : mem -> pointer -> bool  
    ; pt_validGC : @eMem mem -> pointer -> bool
    ; pt_validRC : @eMem mem -> pointer -> bool
    ; pt_validWC : @eMem mem -> pointer -> bool
                                                     
    ; pt_validZ m p := pt_validW m p && ~~ pt_validR m p  
    ; pt_validZC m p := pt_validWC m p && ~~ pt_validRC m p  
    ; pt_validRW m p := pt_validR m p && pt_validW m p  
    ; pt_validRWC m p := pt_validRC m p && pt_validWC m p  
    ; pt_validRO m p := pt_validR m p || ~~ pt_validW m p  
    ; pt_validROC m p := pt_validRC m p || ~~ pt_validWC m p  
    ; pt_weak_invalid m p := ~~ pt_validRC m p && ~~ pt_validWC m p  
    ; pt_invalid m p := ~~ (pt_validG m p)
    ; pt_invalidC m p := ~~ (pt_validGC m p)
}.

(* memory management operations (controlled by the system): alloc,
   free, zeroize; they don't change data, but can change permissions;
   zeroize is actually a hybrid (it is implemented as setting data to
   0) *)
Class absMem (mem: Type) : Type := AbsMem {
      alloc_frame : mem -> pointer -> Sz -> exec mem
    ; free_frame : mem -> pointer -> Sz -> exec mem
    ; initialize_pt : @eMem mem -> pointer -> exec (@eMem mem)
}.

(* properties of validity *)
Class coreMemP (mem: Type) (CM: coreMem mem) := CoreMemP { 
      validG m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validG m)
    ; validR m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validR m)
    ; validW m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validW m)

    ; validGC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validGC m)
    ; validRC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validRC m)
    ; validWC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validWC m)

    ; validF m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validF m)
    ; validZ m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validZ m)
    ; validZC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validZC m)
    ; validRW m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validRW m)
    ; validRO m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validRO m)
    ; validRWC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validRWC m)
    ; validROC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_validROC m)
    ; weak_invalid m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_weak_invalid m)
    ; invalid m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_invalid m)
    ; invalidC m p (sz: Sz) : Prop := 
        chunk_bpred_incl (p, sz) (pt_invalidC m)

    ; coreMem_impl (m1 m2: mem) : Prop

    ; coreMem_implP m1 m2 := forall p w,
        get m1 p = ok w -> get m2 p = ok w                                    
                                 
    ; coreMem_eq (m1 m2: mem) : Prop 

    ; coreMem_eqP m1 m2 := (* baseMem_eq m1 m2 /\ *)
       forall p, get m1 p = get m2 p                           
 
    ; get_reflectP m : forall p,
       reflect (exists w, get m p = ok w) (pt_validRC m p)

    ; set_reflectP m : forall p w,
       reflect (exists m', set m p w = ok m') (pt_validWC m p)

    ; setP m :
       forall p w w0 w' p' m',
         set m p w = ok m' ->
         get m p' = ok w0 ->
         get m' p' = ok w' ->
         if p == p' then w' == w else w' == w0 

    ; set_preserveP m : forall p w,
       forall m', set m p w = ok m' ->
            (pt_validRC m p -> pt_validRC m' p)  
            /\ (pt_validF (base_mem m) p -> pt_validF (base_mem m') p)  
            /\ pt_validWC m' p  

    ; validGP m : forall p sz,
        (validR m p sz \/ validW m p sz) -> validG m p sz         

    ; validGCP m : forall p sz,
        (validRC m p sz \/ validWC m p sz) -> validGC m p sz         
}.

(* properties of memory management *)
Class absMemP (FS: freshSpec) (mem: Type) (FM: fixedMem mem)
  (GM: globMem FM) (CM: @coreMem mem) (CP: @coreMemP mem CM)
  (AM: @absMem mem) : Type := AbsMemP {  

   (* fresh always succeeds, but then alloc may fail of the chunk is
      out of bounds *)                               
    fresh_loc_stackP ctx m (sz: Sz) :
       let p := fresh_loc true ctx (gsupport m) sz in  
       chunk_bpred_incl (p, sz) (pt_invalidC (EMem ctx m))  

 ; alloc_frameP (m: mem) (p: pointer) (sz: Sz) :
     forall ctx m',  
          let p := fresh_loc true ctx (gsupport m) sz in        
          (alloc_frame m p sz = ok m') ->
          (chunk_incl (p, sz) (fstack_chunk m)) /\  
          (coreMem_eq m m') /\
          (chunk_bpred_incl (p, sz) (pt_validW m')) 

 ; free_frameP (m: mem) (p: pointer) (sz: Sz) :    
     forall m',
          (p, sz) = gstack_head m -> 
          (free_frame m p sz = ok m') ->
          (chunk_bpred_incl (p, sz) (pt_validF m)) /\
          (coreMem_eq m m') /\
          chunk_bpred_incl (p, sz) (pt_invalid m) 
                           
 ; initialize_ptP m (p: pointer) :
      forall m',  
        (initialize_pt m p = ok m') ->
        (set m p u8_zero = ok m') /\
        (pt_validWC m p) /\ (pt_validRWC m' p) 
}.

(* specification of external calls (pre and post conditions) *)
Class xCallSpec (FS: freshSpec) (mem: Type) (FM: fixedMem mem)
  (GM: globMem FM) (CM: @coreMem mem) (CP: @coreMemP mem CM)
  (AM: @absMem mem) (AP: @absMemP FS mem FM GM CM CP AM)
  : Type := XCallSpec {
   (* if the continuation is empty, finalizing the external calls
   means the program returns *)           
     continuation_head m : cStack :=
      head (empty_cstack (ctx_post (main_pars m)) (stack_root m))
           (gcontinuation m) 

   (* specify the global stack root *)        
   ; stack_rootP (ctx: Ctx) m :
     stack_root m =
       fresh_loc true ctx (fixed_blocks m) (stack_size (main_pars m)) 
           
  (* before allocation: clr = caller, cle = callee, cleP is determined
     by the program signature (given the function name). ctx is the whole
     program context, and args are the call arguments which may depend
     on such context and go to define the callee context. *)
   ; initialize_external_call 
       (clr cle: mem) (cleP: expParams) 
        (ctx args: Ctx) : Prop :=
      let cle_size := stack_size cleP in
      let cle_pre := ctx_pre cleP in
      let cle_post := ctx_post cleP in
      let cle_params :=
        CStackParams cle_post cle_size
          (fresh_loc true ctx (gsupport clr) cle_size) in
      let cle_ctx := gstack_ctx cle in

      (* callee precondition *)  
      cle_pre (cle_ctx ctx) /\
      args = cle_ctx ctx /\

      gcstack cle = CStack nil cle_ctx cle_params /\
      gcontinuation cle = gcstack clr :: gcontinuation clr /\
      (* trivial, as we are before allocation and the callee stack is
      empty *)  
      in_chunk (fstack_chunk cle) (gstack_top cle)
 
  (* after deallocation *)
   ; finalize_external_call (cle clr: mem) (ctx: Ctx) : Prop :=
      let cle_ctx := gstack_ctx cle in
      let cle_post := cstack_post (cstack_params (gcstack cle)) in

      (* callee postcondition *)          
      cle_post (cle_ctx ctx) /\   
      gstack cle = nil /\
        
      gcstack clr = continuation_head cle /\  
      gcontinuation clr = List.tail (gcontinuation cle) /\    
      (* should be trivial, as the caller stack chunk should be the
      same as before call *)  
      in_chunk (fstack_chunk clr) (gstack_top clr)
}.

(* global memory packed with context instance *)
Record cMem (FS: freshSpec) (mem: Type) (FM: fixedMem mem)
  (GM: globMem FM) : Type := CMem {         
    cmem_ctx : seq (pointer * Sz)
  ; cmem_emem (m: mem) : eMem mem := EMem cmem_ctx m 
}.

(* all together *)
Class fullMem (FS: freshSpec) (prog mem: Type) (FM: fixedMem mem)
  (GM: globMem FM) (CM: @coreMem mem) (CP: @coreMemP mem CM)
  (AM: @absMem mem) (AP: @absMemP FS mem FM GM CM CP AM)
  (XS: @xCallSpec FS mem FM GM CM CP AM AP) (MP: modProg prog) : Type :=
  FullMem {}.

(********************************************************************)

(* stronger specification of external calls, with caller pre- and
   post-conditions *)
Class xCallSpecS (FS: freshSpec) (mem: Type) (FM: fixedMem mem)
  (GM: globMem FM) (CM: @coreMem mem) (CP: @coreMemP mem CM)
  (AM: @absMem mem) (P1: @absMemP FS mem FM GM CM CP AM)
  (X: @xCallSpec FS mem FM GM CM CP AM P1)
  : Type := XCallSpecS {

  (* before allocation: clr = caller, cle = callee, cleP is determined
     by the program signature (given the function name), Pre is a
     precondition on the caller frame and context. ctx is the whole
     program context, and args are the call arguments which may depend
     on such context and go to define the callee context. *)
     initialize_external_callS 
       (clr cle: mem) (cleP: expParams) (Pre: CSeq -> CPred)
        (ctx args: Ctx) : Prop :=
      let cle_size := stack_size cleP in
      let cle_pre := ctx_pre cleP in
      let cle_post := ctx_post cleP in
      let cle_params :=
        CStackParams cle_post cle_size
          (fresh_loc true ctx (gsupport clr) cle_size) in
      let clr_ctx := gstack_ctx clr in
      let cle_ctx := gstack_ctx cle in

      (* caller precondition *)  
      Pre (gstack clr) (clr_ctx ctx) /\
      (* callee precondition *)  
      cle_pre (cle_ctx ctx) /\
      args = cle_ctx ctx /\

      gcstack cle = CStack nil cle_ctx cle_params /\
      gcontinuation cle = gcstack clr :: gcontinuation clr /\
      in_chunk (fstack_chunk cle) (gstack_top cle)

  (* after deallocation: Post is the caller postcondition on the
     caller frame and context. *)
   ; finalize_external_callS (cle clr: mem) (Post: CSeq -> CPred)
       (ctx: Ctx) : Prop :=
      let clr_ctx := gstack_ctx clr in
      let cle_ctx := gstack_ctx cle in
      let cle_post := cstack_post (cstack_params (gcstack cle)) in

      (* callee postcondition *)          
      cle_post (cle_ctx ctx) /\   
      gstack cle = nil /\
      (* caller postcondition *)          
      Post (gstack clr) (clr_ctx ctx) /\  
        
      gcstack clr = continuation_head cle /\  
      gcontinuation clr = List.tail (gcontinuation cle) /\    
      in_chunk (fstack_chunk clr) (gstack_top clr)
}.

End MODEL.

