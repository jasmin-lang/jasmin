open Datatypes
open FMapAVL
open FMapFacts
open Nat0
open Eqtype
open Seq
open Ssrbool
open Ssreflect
open Ssrfun

type __ = Obj.t

module type CmpType =
 sig
  val t : Equality.coq_type

  val cmp : Equality.sort -> Equality.sort -> comparison
 end

module MkOrdT :
 functor (T:CmpType) ->
 sig
  type t = Equality.sort

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare

  val eq_dec : Equality.sort -> Equality.sort -> bool
 end

module type CompuEqDec =
 sig
  val t : Equality.coq_type

  val eq_dec : Equality.sort -> Equality.sort -> bool
 end

module type MAP =
 sig
  module K :
   CmpType

  type 'x t

  val empty : 'a1 t

  val get : 'a1 t -> Equality.sort -> 'a1 option

  val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 t

  val remove : 'a1 t -> Equality.sort -> 'a1 t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (Equality.sort -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t

  val elements : 'a1 t -> (Equality.sort * 'a1) list

  val fold : (Equality.sort -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val in_codom : Equality.coq_type -> Equality.sort -> Equality.sort t -> bool

  val elementsP :
    Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
    -> reflect
 end

module Mmake :
 functor (K__1:CmpType) ->
 sig
  module K :
   sig
    val t : Equality.coq_type

    val cmp : Equality.sort -> Equality.sort -> comparison
   end

  module Ordered :
   sig
    type t = Equality.sort

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare

    val eq_dec : Equality.sort -> Equality.sort -> bool
   end

  module Map :
   sig
    module E :
     sig
      type t = Equality.sort

      val compare :
        Equality.sort -> Equality.sort -> Equality.sort
        OrderedType.coq_Compare

      val eq_dec : Equality.sort -> Equality.sort -> bool
     end

    module Raw :
     sig
      type key = Equality.sort

      type 'elt tree =
      | Leaf
      | Node of 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t

      val tree_rect :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val tree_rec :
        'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
        Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

      val height : 'a1 tree -> Int.Z_as_Int.t

      val cardinal : 'a1 tree -> nat

      val empty : 'a1 tree

      val is_empty : 'a1 tree -> bool

      val mem : Equality.sort -> 'a1 tree -> bool

      val find : Equality.sort -> 'a1 tree -> 'a1 option

      val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

      val remove_min :
        'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

      val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

      val remove : Equality.sort -> 'a1 tree -> 'a1 tree

      val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

      type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                           t_right : 'elt tree }

      val t_left : 'a1 triple -> 'a1 tree

      val t_opt : 'a1 triple -> 'a1 option

      val t_right : 'a1 triple -> 'a1 tree

      val split : Equality.sort -> 'a1 tree -> 'a1 triple

      val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

      val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

      val elements : 'a1 tree -> (key * 'a1) list

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      type 'elt enumeration =
      | End
      | More of key * 'elt * 'elt tree * 'elt enumeration

      val enumeration_rect :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val enumeration_rec :
        'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
        'a1 enumeration -> 'a2

      val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

      val equal_more :
        ('a1 -> 'a1 -> bool) -> Equality.sort -> 'a1 -> ('a1 enumeration ->
        bool) -> 'a1 enumeration -> bool

      val equal_cont :
        ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
        enumeration -> bool

      val equal_end : 'a1 enumeration -> bool

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

      val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

      val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

      val map2_opt :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
        'a3 tree

      module Proofs :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = Equality.sort
           end

          module IsTO :
           sig
            
           end

          module OrderTac :
           sig
            
           end

          val eq_dec : Equality.sort -> Equality.sort -> bool

          val lt_dec : Equality.sort -> Equality.sort -> bool

          val eqb : Equality.sort -> Equality.sort -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
              
             end

            module OrderTac :
             sig
              
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end
         end

        module L :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
              
             end

            module OrderTac :
             sig
              
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Equality.sort
               end

              module IsTO :
               sig
                
               end

              module OrderTac :
               sig
                
               end

              val eq_dec : Equality.sort -> Equality.sort -> bool

              val lt_dec : Equality.sort -> Equality.sort -> bool

              val eqb : Equality.sort -> Equality.sort -> bool
             end
           end

          type key = Equality.sort

          type 'elt t = (Equality.sort * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_mem_2 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_mem_3 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
            coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_find_2 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_find_3 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
            coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_add_2 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_add_3 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * 'elt t * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort ->
            'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) ->
            ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list ->
            __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort ->
            'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) ->
            ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list ->
            __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort ->
            'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) ->
            ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list ->
            __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort ->
            'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) ->
            ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list ->
            __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_remove_2 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
          | R_remove_3 of 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * 'elt t * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
            -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ ->
            __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
            (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
            'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
          | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
             * Equality.sort * 'elt * (Equality.sort * 'elt) list * 'a
             * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
            -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> ('a1, __)
            coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t
            -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2

          val coq_R_fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
            -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> ('a1, __)
            coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t
            -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2

          val fold_rect :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
            -> 'a1 -> (Equality.sort * 'a1) list -> __ -> 'a2 -> 'a2) -> (key
            -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2

          val fold_rec :
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
            (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
            -> 'a1 -> (Equality.sort * 'a1) list -> __ -> 'a2 -> 'a2) -> (key
            -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          type 'elt coq_R_equal =
          | R_equal_0 of 'elt t * 'elt t
          | R_equal_1 of 'elt t * 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * bool * 'elt coq_R_equal
          | R_equal_2 of 'elt t * 'elt t * Equality.sort * 'elt
             * (Equality.sort * 'elt) list * Equality.sort * 'elt
             * (Equality.sort * 'elt) list
             * Equality.sort OrderedType.coq_Compare
          | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

          val coq_R_equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1)
            list -> __ -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
            -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) ->
            ('a1 t -> 'a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1)
            list -> __ -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
            -> __ -> Equality.sort OrderedType.coq_Compare -> __ -> __ ->
            'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
            'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

          val coq_R_equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1)
            list -> __ -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
            -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) ->
            ('a1 t -> 'a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1)
            list -> __ -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
            -> __ -> Equality.sort OrderedType.coq_Compare -> __ -> __ ->
            'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ ->
            'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

          val equal_rect :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1)
            list -> __ -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
            -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ ->
            Equality.sort OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1
            t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
            -> 'a1 t -> 'a2

          val equal_rec :
            ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
            ('a1 t -> 'a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1)
            list -> __ -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
            -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ ->
            Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __ ->
            Equality.sort OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1
            t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t
            -> 'a1 t -> 'a2

          val coq_R_equal_correct :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2_l :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

          val map2_r :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3
            t

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

          val map2_alt :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
            option -> 'a3 option
         end

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt tree
        | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * bool * 'elt coq_R_mem
        | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

        type 'elt coq_R_find =
        | R_find_0 of 'elt tree
        | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
        | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

        type 'elt coq_R_bal =
        | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
           'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
        | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
           key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
           'elt * 'elt tree * Int.Z_as_Int.t
        | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

        val coq_R_bal_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2)
          -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
          __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
          -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
          -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
          -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree
          -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

        val coq_R_bal_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key
          -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> __ ->
          'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2)
          -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
          __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
          -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
          -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
          __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
          -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
          'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree
          -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

        type 'elt coq_R_add =
        | R_add_0 of 'elt tree
        | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add
        | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
          tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
          key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2)
          -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

        type 'elt coq_R_remove_min =
        | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
        | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
           * key * 'elt * 'elt tree * Int.Z_as_Int.t
           * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
           * (key * 'elt)

        val coq_R_remove_min_rect :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        val coq_R_remove_min_rec :
          ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
          key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
          coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) ->
          'a1 coq_R_remove_min -> 'a2

        type 'elt coq_R_merge =
        | R_merge_0 of 'elt tree * 'elt tree
        | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t
        | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

        val coq_R_merge_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
          -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2

        val coq_R_merge_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
          -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
          coq_R_merge -> 'a2

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt tree
        | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove
        | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove

        val coq_R_remove_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __
          -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
          'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

        type 'elt coq_R_concat =
        | R_concat_0 of 'elt tree * 'elt tree
        | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t
        | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt tree * (key * 'elt)

        val coq_R_concat_rect :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        val coq_R_concat_rec :
          ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
          -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
          'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

        type 'elt coq_R_split =
        | R_split_0 of 'elt tree
        | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree
        | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t
        | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
           * 'elt option * 'elt tree

        val coq_R_split_rect :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
          'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
          -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2

        val coq_R_split_rec :
          Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
          'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
          'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
          'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
          -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
          option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
          coq_R_split -> 'a2

        type ('elt, 'x) coq_R_map_option =
        | R_map_option_0 of 'elt tree
        | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
           * 'x tree * ('elt, 'x) coq_R_map_option
        | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
           * Int.Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 
           'x tree * ('elt, 'x) coq_R_map_option

        val coq_R_map_option_rect :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
          'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
          tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3

        val coq_R_map_option_rec :
          (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree
          -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
          'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
          tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree ->
          'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
          'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1,
          'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
          ('a1, 'a2) coq_R_map_option -> 'a3

        type ('elt, 'x0, 'x) coq_R_map2_opt =
        | R_map2_opt_0 of 'elt tree * 'x0 tree
        | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t
        | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 
           'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt
        | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
           * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
           * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
           * ('elt, 'x0, 'x) coq_R_map2_opt

        val coq_R_map2_opt_rect :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree
          -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2
          option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4

        val coq_R_map2_opt_rec :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) ->
          ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
          Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
          tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree
          -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree
          -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
          key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2
          option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
          coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
          -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2,
          'a3) coq_R_map2_opt -> 'a4

        val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        val flatten_e : 'a1 enumeration -> (key * 'a1) list
       end
     end

    type 'elt bst =
      'elt Raw.tree
      (* singleton inductive, whose constructor was Bst *)

    val this : 'a1 bst -> 'a1 Raw.tree

    type 'elt t = 'elt bst

    type key = Equality.sort

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val elements : 'a1 t -> (key * 'a1) list

    val cardinal : 'a1 t -> nat

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
   end

  module Facts :
   sig
    val eqb : Equality.sort -> Equality.sort -> bool

    val coq_In_dec : 'a1 Map.t -> Map.key -> bool
   end

  type 't t = 't Map.t

  val empty : 'a1 t

  val get : 'a1 t -> Equality.sort -> 'a1 option

  val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 Map.t

  val remove : 'a1 t -> Equality.sort -> 'a1 Map.t

  val map : ('a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t

  val mapi : (Map.key -> 'a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t

  val raw_map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1
    Map.Raw.tree -> 'a2 Map.Raw.tree -> 'a3 Map.Raw.tree

  val elements : 'a1 Map.t -> (Map.key * 'a1) list

  val fold : (Map.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 Map.t -> 'a2 -> 'a2

  val in_codom : Equality.coq_type -> Equality.sort -> Equality.sort t -> bool

  val map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t

  val elementsP :
    Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
    -> reflect
 end

module DMmake :
 functor (K:CmpType) ->
 functor (E:CompuEqDec) ->
 sig
  type 'p boxed = { box_t : Equality.sort; box_v : 'p }

  val box_t : 'a1 boxed -> Equality.sort

  val box_v : 'a1 boxed -> 'a1

  val from_boxed : Equality.sort -> 'a1 boxed option -> 'a1 option

  module Map :
   sig
    module K :
     sig
      val t : Equality.coq_type

      val cmp : Equality.sort -> Equality.sort -> comparison
     end

    module Ordered :
     sig
      type t = Equality.sort

      val compare :
        Equality.sort -> Equality.sort -> Equality.sort
        OrderedType.coq_Compare

      val eq_dec : Equality.sort -> Equality.sort -> bool
     end

    module Map :
     sig
      module E :
       sig
        type t = Equality.sort

        val compare :
          Equality.sort -> Equality.sort -> Equality.sort
          OrderedType.coq_Compare

        val eq_dec : Equality.sort -> Equality.sort -> bool
       end

      module Raw :
       sig
        type key = Equality.sort

        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Int.Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : Equality.sort -> 'a1 tree -> bool

        val find : Equality.sort -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : Equality.sort -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : Equality.sort -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> Equality.sort -> 'a1 -> ('a1 enumeration ->
          bool) -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = Equality.sort
             end

            module IsTO :
             sig
              
             end

            module OrderTac :
             sig
              
             end

            val eq_dec : Equality.sort -> Equality.sort -> bool

            val lt_dec : Equality.sort -> Equality.sort -> bool

            val eqb : Equality.sort -> Equality.sort -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Equality.sort
               end

              module IsTO :
               sig
                
               end

              module OrderTac :
               sig
                
               end

              val eq_dec : Equality.sort -> Equality.sort -> bool

              val lt_dec : Equality.sort -> Equality.sort -> bool

              val eqb : Equality.sort -> Equality.sort -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = Equality.sort
               end

              module IsTO :
               sig
                
               end

              module OrderTac :
               sig
                
               end

              val eq_dec : Equality.sort -> Equality.sort -> bool

              val lt_dec : Equality.sort -> Equality.sort -> bool

              val eqb : Equality.sort -> Equality.sort -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = Equality.sort
                 end

                module IsTO :
                 sig
                  
                 end

                module OrderTac :
                 sig
                  
                 end

                val eq_dec : Equality.sort -> Equality.sort -> bool

                val lt_dec : Equality.sort -> Equality.sort -> bool

                val eqb : Equality.sort -> Equality.sort -> bool
               end
             end

            type key = Equality.sort

            type 'elt t = (Equality.sort * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_mem_2 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_mem_3 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
              'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
              'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_find_2 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_find_3 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
              'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
              'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_add_2 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_add_3 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * 'elt t * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
              -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
              'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
              -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
              'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
              -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2)
              -> ('a1 t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list
              -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_remove_2 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
            | R_remove_3 of 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * 'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1
              -> (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
              t -> Equality.sort -> 'a1 -> (Equality.sort * 'a1) list -> __
              -> __ -> __ -> 'a2) -> ('a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
            | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
               * Equality.sort * 'elt * (Equality.sort * 'elt) list * 
               'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> ('a1, __)
              coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1
              t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2

            val coq_R_fold_rec :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> __ -> ('a1, __)
              coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1
              t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2

            val fold_rect :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> 'a2 -> 'a2) ->
              (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2

            val fold_rec :
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2) ->
              (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> 'a2 -> 'a2) ->
              (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * bool * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * Equality.sort * 'elt
               * (Equality.sort * 'elt) list * Equality.sort * 'elt
               * (Equality.sort * 'elt) list
               * Equality.sort OrderedType.coq_Compare
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> Equality.sort ->
              'a1 -> (Equality.sort * 'a1) list -> __ -> Equality.sort
              OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
              -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
              -> bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
              coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> Equality.sort
              -> 'a1 -> (Equality.sort * 'a1) list -> __ -> Equality.sort ->
              'a1 -> (Equality.sort * 'a1) list -> __ -> Equality.sort
              OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
              -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
              -> bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              ('a1 t -> 'a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort
              OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
              -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
              -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
              ('a1 t -> 'a1 t -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort -> 'a1 ->
              (Equality.sort * 'a1) list -> __ -> Equality.sort
              OrderedType.coq_Compare -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
              -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
              -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
            -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
            -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
            -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
            -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Int.Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Int.Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Int.Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Int.Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Int.Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
             key * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 
             'elt * 'elt tree * Int.Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
            __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
            -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
            tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
            __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
            -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
            __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
            -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
            tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
            __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
            -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Int.Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Int.Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt
             * 'elt tree * Int.Z_as_Int.t * 'elt tree * (key * 'elt) * 
             key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
            -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ ->
            key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
            'a1 coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
            -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ ->
            key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
            'a1 coq_R_merge -> 'a2

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
            -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
            __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
            -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Int.Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt
             * 'elt tree * Int.Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
            -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ ->
            'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
            'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
            -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ ->
            'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
            'a2

          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
            'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple ->
            'a1 coq_R_split -> 'a2

          val coq_R_split_rec :
            Equality.sort -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
            'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
            __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
            'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple ->
            'a1 coq_R_split -> 'a2

          type ('elt, 'x) coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Int.Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
            -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
            -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Int.Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0
             * 'x0 tree * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
             * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 
             'elt * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0
             * 'x0 tree * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
             * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __
            -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
            tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
            ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __
            -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
            ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
            'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
            tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __
            -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
            tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
            ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
            __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __
            -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
            ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
            'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
            tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = Equality.sort

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module Facts :
     sig
      val eqb : Equality.sort -> Equality.sort -> bool

      val coq_In_dec : 'a1 Map.t -> Map.key -> bool
     end

    type 't t = 't Map.t

    val empty : 'a1 t

    val get : 'a1 t -> Equality.sort -> 'a1 option

    val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 Map.t

    val remove : 'a1 t -> Equality.sort -> 'a1 Map.t

    val map : ('a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t

    val mapi : (Map.key -> 'a1 -> 'a2) -> 'a1 Map.t -> 'a2 Map.t

    val raw_map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1
      Map.Raw.tree -> 'a2 Map.Raw.tree -> 'a3 Map.Raw.tree

    val elements : 'a1 Map.t -> (Map.key * 'a1) list

    val fold : (Map.key -> 'a1 -> 'a2 -> 'a2) -> 'a1 Map.t -> 'a2 -> 'a2

    val in_codom :
      Equality.coq_type -> Equality.sort -> Equality.sort t -> bool

    val map2 :
      (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t ->
      'a2 t -> 'a3 t

    val elementsP :
      Equality.coq_type -> (Equality.sort * Equality.sort) -> Equality.sort t
      -> reflect
   end

  type 'p t = 'p boxed Map.t

  val empty : 'a1 t

  val get : 'a1 t -> Equality.sort -> 'a1 option

  val set : 'a1 t -> Equality.sort -> 'a1 -> 'a1 boxed Map.Map.t

  val map : (Equality.sort -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    (Equality.sort -> 'a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t
 end

module MkMOrdT :
 functor (T:CmpType) ->
 sig
  type t = Equality.sort

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module Smake :
 functor (T:CmpType) ->
 sig
  module Ordered :
   sig
    type t = Equality.sort

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  module Raw :
   sig
    type elt = Equality.sort

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * Equality.sort * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : Equality.sort -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : Equality.sort list -> tree -> Equality.sort list

    val elements : tree -> Equality.sort list

    val rev_elements_aux : Equality.sort list -> tree -> Equality.sort list

    val rev_elements : tree -> Equality.sort list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      Equality.sort -> (enumeration -> comparison) -> enumeration ->
      comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> Equality.sort -> tree -> bool

    val subsetr : (tree -> bool) -> Equality.sort -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : Equality.sort -> tree

    val create : t -> Equality.sort -> t -> tree

    val assert_false : t -> Equality.sort -> t -> tree

    val bal : t -> Equality.sort -> t -> tree

    val add : Equality.sort -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : Equality.sort -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : Equality.sort -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : Equality.sort -> tree -> bool

    val gtb_tree : Equality.sort -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = Equality.sort

          val compare : Equality.sort -> Equality.sort -> comparison

          val eq_dec : Equality.sort -> Equality.sort -> bool
         end

        module TO :
         sig
          type t = Equality.sort

          val compare : Equality.sort -> Equality.sort -> comparison

          val eq_dec : Equality.sort -> Equality.sort -> bool
         end
       end

      val eq_dec : Equality.sort -> Equality.sort -> bool

      val lt_dec : Equality.sort -> Equality.sort -> bool

      val eqb : Equality.sort -> Equality.sort -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_min_elt_2 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
       * Int.Z_as_Int.t * tree * Equality.sort * tree * elt option
       * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_max_elt_2 of tree * Int.Z_as_Int.t * tree * Equality.sort * tree
       * Int.Z_as_Int.t * tree * Equality.sort * tree * elt option
       * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Equality.sort

            val compare : Equality.sort -> Equality.sort -> comparison

            val eq_dec : Equality.sort -> Equality.sort -> bool
           end

          module TO :
           sig
            type t = Equality.sort

            val compare : Equality.sort -> Equality.sort -> comparison

            val eq_dec : Equality.sort -> Equality.sort -> bool
           end
         end

        val eq_dec : Equality.sort -> Equality.sort -> bool

        val lt_dec : Equality.sort -> Equality.sort -> bool

        val eqb : Equality.sort -> Equality.sort -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * Equality.sort * t
    | R_bal_1 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_2 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_3 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree
    | R_bal_4 of t * Equality.sort * t
    | R_bal_5 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_6 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree
    | R_bal_7 of t * Equality.sort * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree
    | R_bal_8 of t * Equality.sort * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * Equality.sort * tree * (t * elt) * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
       * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort
       * tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * Equality.sort * 
       tree * Int.Z_as_Int.t * tree * Equality.sort * tree * t * bool * 
       t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = Equality.sort

    val compare : Equality.sort -> Equality.sort -> comparison

    val eq_dec : Equality.sort -> Equality.sort -> bool
   end

  type elt = Equality.sort

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end
