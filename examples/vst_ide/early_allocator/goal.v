Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import lib.
Local Open Scope sac.
Require Import example_strategy_goal.
Require Import example_strategy_proof.

(*----- Function hyp_early_alloc_nr_pages -----*)

Definition hyp_early_alloc_nr_pages_safety_wit_1 := 
forall (base: Z) (cur: Z) ,
  [| (base <= cur) |]
  &&  ((( &( "base" ) )) # UInt64  |-> base)
  **  ((( &( "cur" ) )) # UInt64  |-> cur)
|--
  [| (12 <= 63) |] 
  &&  [| (0 <= 12) |]
.

Definition hyp_early_alloc_nr_pages_return_wit_1 := 
forall (base_2: Z) (cur_2: Z) ,
  [| (base_2 <= cur_2) |]
  &&  ((( &( "base" ) )) # UInt64  |-> base_2)
  **  ((( &( "cur" ) )) # UInt64  |-> cur_2)
|--
  EX base cur,
  [| ((Z.shiftr (unsigned_last_nbits ((cur_2 - base_2 )) (64)) 12) = (Z.shiftr (cur - base ) PAGE_SHIFT)) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "base" ) )) # UInt64  |-> base)
.

(*----- Function clear_page -----*)

Definition clear_page_safety_wit_1 := 
forall (to_pre: Z) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  (store_undef_array undef_store_char to_pre PAGE_SIZE )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clear_page_safety_wit_2 := 
forall (to_pre: Z) (i: Z) ,
  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
  **  (store_undef_array_rec undef_store_char to_pre i PAGE_SIZE (Z_to_nat ((PAGE_SIZE - i ))) )
|--
  [| (4096 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 4096) |]
.

Definition clear_page_safety_wit_3 := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((to_pre + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition clear_page_safety_wit_4 := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  (store_array store_char to_pre (i + 1 ) (repeat (0) ((Z_to_nat ((i + 1 ))))) )
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
|--
  [| ((i + 1 ) <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= (i + 1 )) |]
.

Definition clear_page_entail_wit_1 := 
forall (to_pre: Z) ,
  (store_undef_array undef_store_char to_pre PAGE_SIZE )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= 4096) |]
  &&  (store_array store_char to_pre 0 (repeat (0) ((Z_to_nat (0)))) )
  **  (store_undef_array_rec undef_store_char to_pre 0 PAGE_SIZE (Z_to_nat ((PAGE_SIZE - 0 ))) )
.

Definition clear_page_entail_wit_2 := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  (store_array store_char to_pre (i + 1 ) (repeat (0) ((Z_to_nat ((i + 1 ))))) )
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
|--
  [| (0 <= (i + 1 )) |] 
  &&  [| ((i + 1 ) <= 4096) |]
  &&  (store_array store_char to_pre (i + 1 ) (repeat (0) ((Z_to_nat ((i + 1 ))))) )
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
.

Definition clear_page_return_wit_1 := 
forall (to_pre: Z) (i: Z) ,
  [| (i >= 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
  **  (store_undef_array_rec undef_store_char to_pre i PAGE_SIZE (Z_to_nat ((PAGE_SIZE - i ))) )
|--
  (store_array store_char to_pre PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
.

Definition clear_page_partial_solve_wit_1_pure := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
  **  (store_undef_array_rec undef_store_char to_pre i PAGE_SIZE (Z_to_nat ((PAGE_SIZE - i ))) )
|--
  [| (0 <= i) |] 
  &&  [| (i < 4096) |]
.

Definition clear_page_partial_solve_wit_1_aux := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
  **  (store_undef_array_rec undef_store_char to_pre i PAGE_SIZE (Z_to_nat ((PAGE_SIZE - i ))) )
|--
  [| (0 <= i) |] 
  &&  [| (i < 4096) |] 
  &&  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  (store_undef_array_rec undef_store_char to_pre i PAGE_SIZE (Z_to_nat ((PAGE_SIZE - i ))) )
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
.

Definition clear_page_partial_solve_wit_1 := clear_page_partial_solve_wit_1_pure -> clear_page_partial_solve_wit_1_aux.

Definition clear_page_partial_solve_wit_2_pure := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  ((( &( "to" ) )) # Ptr  |-> to_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (((to_pre + (i * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
|--
  [| (0 <= i) |]
.

Definition clear_page_partial_solve_wit_2_aux := 
forall (to_pre: Z) (i: Z) ,
  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  (((to_pre + (i * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
|--
  [| (0 <= i) |] 
  &&  [| (i < 4096) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= 4096) |]
  &&  (((to_pre + (i * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (store_array store_char to_pre i (repeat (0) ((Z_to_nat (i)))) )
  **  (store_undef_array_rec undef_store_char to_pre (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
.

Definition clear_page_partial_solve_wit_2 := clear_page_partial_solve_wit_2_pure -> clear_page_partial_solve_wit_2_aux.

Definition clear_page_which_implies_wit_1 := 
forall (i: Z) (to: Z) ,
  [| (0 <= i) |] 
  &&  [| (i < 4096) |]
  &&  (store_undef_array_rec undef_store_char to i PAGE_SIZE (Z_to_nat ((PAGE_SIZE - i ))) )
|--
  (((to + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (store_undef_array_rec undef_store_char to (i + 1 ) PAGE_SIZE (Z_to_nat ((PAGE_SIZE - (i + 1 ) ))) )
.

Definition clear_page_which_implies_wit_2 := 
forall (i: Z) (to: Z) ,
  [| (0 <= i) |]
  &&  (((to + (i * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (store_array store_char to i (repeat (0) ((Z_to_nat (i)))) )
|--
  (store_array store_char to (i + 1 ) (repeat (0) ((Z_to_nat ((i + 1 ))))) )
.

(*----- Function hyp_early_alloc_page -----*)

Definition hyp_early_alloc_page_safety_wit_1 := 
forall (arg_pre: Z) (cur: Z) (end_: Z) ,
  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) > end_) |] 
  &&  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hyp_early_alloc_page_entail_wit_1 := 
forall (cur: Z) (end_: Z) ,
  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_page_return_wit_1 := 
forall (cur_2: Z) (end__2: Z) ,
  [| ((unsigned_last_nbits ((cur_2 + 4096 )) (64)) > end__2) |] 
  &&  [| (cur_2 >= 0) |] 
  &&  [| ((cur_2 + PAGE_SIZE ) <= end__2) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur_2)
  **  ((( &( "end_" ) )) # UInt64  |-> end__2)
  **  (store_undef_array undef_store_char cur_2 (end__2 - cur_2 ) )
|--
  EX end_ cur,
  [| (cur = (cur_2 + PAGE_SIZE )) |] 
  &&  [| (0 = cur_2) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  (store_array store_char 0 PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_page_return_wit_2 := 
forall (cur_2: Z) (end__2: Z) ,
  [| ((unsigned_last_nbits ((cur_2 + 4096 )) (64)) <= end__2) |] 
  &&  [| (cur_2 >= 0) |] 
  &&  [| ((cur_2 + PAGE_SIZE ) <= end__2) |]
  &&  (store_array store_char cur_2 PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end__2)
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur_2 + 4096 )) (64)))
  **  (store_undef_array undef_store_char (unsigned_last_nbits ((cur_2 + 4096 )) (64)) (end__2 - (unsigned_last_nbits ((cur_2 + 4096 )) (64)) ) )
|--
  EX end_ cur,
  [| (cur = (cur_2 + PAGE_SIZE )) |] 
  &&  [| (cur_2 = cur_2) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  (store_array store_char cur_2 PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_page_partial_solve_wit_1_pure := 
forall (arg_pre: Z) (cur: Z) (end_: Z) ,
  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |] 
  &&  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + 4096 )) (64)))
  **  ((( &( "arg" ) )) # Ptr  |-> arg_pre)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| ((cur + PAGE_SIZE ) = (unsigned_last_nbits ((cur + 4096 )) (64))) |] 
  &&  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |]
.

Definition hyp_early_alloc_page_partial_solve_wit_1_aux := 
forall (cur: Z) (end_: Z) ,
  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |] 
  &&  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + 4096 )) (64)))
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| ((cur + PAGE_SIZE ) = (unsigned_last_nbits ((cur + 4096 )) (64))) |] 
  &&  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |] 
  &&  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |] 
  &&  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + 4096 )) (64)))
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_page_partial_solve_wit_1 := hyp_early_alloc_page_partial_solve_wit_1_pure -> hyp_early_alloc_page_partial_solve_wit_1_aux.

Definition hyp_early_alloc_page_partial_solve_wit_2 := 
forall (cur: Z) (end_: Z) ,
  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |] 
  &&  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  (store_undef_array undef_store_char cur PAGE_SIZE )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + 4096 )) (64)))
  **  (store_undef_array undef_store_char (unsigned_last_nbits ((cur + 4096 )) (64)) (end_ - (unsigned_last_nbits ((cur + 4096 )) (64)) ) )
|--
  [| ((unsigned_last_nbits ((cur + 4096 )) (64)) <= end_) |] 
  &&  [| (cur >= 0) |] 
  &&  [| ((cur + PAGE_SIZE ) <= end_) |]
  &&  (store_undef_array undef_store_char cur PAGE_SIZE )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + 4096 )) (64)))
  **  (store_undef_array undef_store_char (unsigned_last_nbits ((cur + 4096 )) (64)) (end_ - (unsigned_last_nbits ((cur + 4096 )) (64)) ) )
.

Definition hyp_early_alloc_page_which_implies_wit_1 := 
forall (ret: Z) (cur: Z) (end_: Z) ,
  [| ((ret + PAGE_SIZE ) = cur) |] 
  &&  [| (cur <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char ret (end_ - ret ) )
|--
  (store_undef_array undef_store_char ret PAGE_SIZE )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

(*----- Function hyp_early_alloc_contig -----*)

Definition hyp_early_alloc_contig_safety_wit_1 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) ,
  [| (nr_pages_pre = 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "p" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # UInt64  |->_)
  **  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "nr_pages" ) )) # UInt  |-> nr_pages_pre)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| False |]
.

Definition hyp_early_alloc_contig_safety_wit_2 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) ,
  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "p" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # UInt64  |->_)
  **  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "nr_pages" ) )) # UInt  |-> nr_pages_pre)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| (12 <= 31) |] 
  &&  [| (0 <= 12) |]
.

Definition hyp_early_alloc_contig_safety_wit_3 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) ,
  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) > end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "p" ) )) # UInt64  |->_)
  **  ((( &( "i" ) )) # UInt64  |->_)
  **  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "nr_pages" ) )) # UInt  |-> nr_pages_pre)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| (0 <= INT_MAX) |] 
  &&  [| ((INT_MIN) <= 0) |]
.

Definition hyp_early_alloc_contig_safety_wit_4 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  (store_undef_array undef_store_char (cur + (i * PAGE_SIZE ) ) (end_ - (cur + (i * PAGE_SIZE ) ) ) )
  **  ((( &( "p" ) )) # UInt64  |->_)
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
  **  ((( &( "nr_pages" ) )) # UInt  |-> nr_pages_pre)
|--
  [| (12 <= 63) |] 
  &&  [| (0 <= 12) |]
.

Definition hyp_early_alloc_contig_entail_wit_1 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) ,
  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_contig_entail_wit_2 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) ,
  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
|--
  [| (0 <= 0) |] 
  &&  [| (0 <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_array store_char cur (0 * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((0 * PAGE_SIZE ))))) )
  **  (store_undef_array undef_store_char (cur + (0 * PAGE_SIZE ) ) (end_ - (cur + (0 * PAGE_SIZE ) ) ) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
.

Definition hyp_early_alloc_contig_entail_wit_3 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "p" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)))
  **  (store_array store_char cur ((i + 1 ) * PAGE_SIZE ) (repeat (0) ((Z_to_nat (((i + 1 ) * PAGE_SIZE ))))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char (cur + ((i + 1 ) * PAGE_SIZE ) ) (end_ - (cur + ((i + 1 ) * PAGE_SIZE ) ) ) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
|--
  [| (0 <= (unsigned_last_nbits ((i + 1 )) (64))) |] 
  &&  [| ((unsigned_last_nbits ((i + 1 )) (64)) <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_array store_char cur ((unsigned_last_nbits ((i + 1 )) (64)) * PAGE_SIZE ) (repeat (0) ((Z_to_nat (((unsigned_last_nbits ((i + 1 )) (64)) * PAGE_SIZE ))))) )
  **  (store_undef_array undef_store_char (cur + ((unsigned_last_nbits ((i + 1 )) (64)) * PAGE_SIZE ) ) (end_ - (cur + ((unsigned_last_nbits ((i + 1 )) (64)) * PAGE_SIZE ) ) ) )
  **  ((( &( "p" ) )) # UInt64  |->_)
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
.

Definition hyp_early_alloc_contig_return_wit_2 := 
forall (nr_pages_pre: Z) (cur_2: Z) (end__2: Z) ,
  [| ((unsigned_last_nbits ((cur_2 + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) > end__2) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur_2 >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur_2 + (nr_pages_pre * PAGE_SIZE ) ) <= end__2) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur_2)
  **  ((( &( "end_" ) )) # UInt64  |-> end__2)
  **  (store_undef_array undef_store_char cur_2 (end__2 - cur_2 ) )
|--
  EX end_ cur,
  [| (cur = (cur_2 + (nr_pages_pre * PAGE_SIZE ) )) |] 
  &&  [| (0 = cur_2) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  (store_array store_char 0 (nr_pages_pre * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((nr_pages_pre * PAGE_SIZE ))))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_contig_return_wit_3 := 
forall (nr_pages_pre: Z) (cur_2: Z) (end__2: Z) (i: Z) ,
  [| (i >= nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur_2 + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end__2) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur_2 >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur_2 + (nr_pages_pre * PAGE_SIZE ) ) <= end__2) |]
  &&  ((( &( "end_" ) )) # UInt64  |-> end__2)
  **  (store_array store_char cur_2 (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  (store_undef_array undef_store_char (cur_2 + (i * PAGE_SIZE ) ) (end__2 - (cur_2 + (i * PAGE_SIZE ) ) ) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur_2 + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
|--
  EX end_ cur,
  [| (cur = (cur_2 + (nr_pages_pre * PAGE_SIZE ) )) |] 
  &&  [| (cur_2 = cur_2) |]
  &&  ((( &( "cur" ) )) # UInt64  |-> cur)
  **  (store_array store_char cur_2 (nr_pages_pre * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((nr_pages_pre * PAGE_SIZE ))))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char cur (end_ - cur ) )
.

Definition hyp_early_alloc_contig_partial_solve_wit_1_pure := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  (store_undef_array undef_store_char (cur + (i * PAGE_SIZE ) ) (end_ - (cur + (i * PAGE_SIZE ) ) ) )
  **  ((( &( "p" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)))
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
  **  ((( &( "nr_pages" ) )) # UInt  |-> nr_pages_pre)
|--
  [| (i < nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) = (cur + (i * PAGE_SIZE ) )) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
.

Definition hyp_early_alloc_contig_partial_solve_wit_1_aux := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  (store_undef_array undef_store_char (cur + (i * PAGE_SIZE ) ) (end_ - (cur + (i * PAGE_SIZE ) ) ) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
|--
  [| (i < nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) = (cur + (i * PAGE_SIZE ) )) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |] 
  &&  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char (cur + (i * PAGE_SIZE ) ) (end_ - (cur + (i * PAGE_SIZE ) ) ) )
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
.

Definition hyp_early_alloc_contig_partial_solve_wit_1 := hyp_early_alloc_contig_partial_solve_wit_1_pure -> hyp_early_alloc_contig_partial_solve_wit_1_aux.

Definition hyp_early_alloc_contig_partial_solve_wit_2 := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  (store_undef_array undef_store_char (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) PAGE_SIZE )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) (end_ - ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) ) )
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
|--
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  (store_undef_array undef_store_char (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) PAGE_SIZE )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) (end_ - ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) ) )
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
.

Definition hyp_early_alloc_contig_partial_solve_wit_3_pure := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  (store_array store_char (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "i" ) )) # UInt64  |-> i)
  **  ((( &( "nr_pages" ) )) # UInt  |-> nr_pages_pre)
  **  ((( &( "ret" ) )) # UInt64  |-> cur)
  **  ((( &( "p" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)))
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) (end_ - ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) ) )
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
|--
  [| (i >= 0) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) = (cur + (i * PAGE_SIZE ) )) |]
.

Definition hyp_early_alloc_contig_partial_solve_wit_3_aux := 
forall (nr_pages_pre: Z) (cur: Z) (end_: Z) (i: Z) ,
  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  (store_array store_char (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) (end_ - ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) ) )
  **  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
|--
  [| (i >= 0) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) = (cur + (i * PAGE_SIZE ) )) |] 
  &&  [| (i < nr_pages_pre) |] 
  &&  [| (0 <= i) |] 
  &&  [| (i <= nr_pages_pre) |] 
  &&  [| ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)) <= end_) |] 
  &&  [| (nr_pages_pre <> 0) |] 
  &&  [| (cur >= 0) |] 
  &&  [| (0 < nr_pages_pre) |] 
  &&  [| ((nr_pages_pre * PAGE_SIZE ) <= UINT_MAX) |] 
  &&  [| ((cur + (nr_pages_pre * PAGE_SIZE ) ) <= end_) |]
  &&  (store_array store_char cur (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  (store_array store_char (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) (end_ - ((unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl i 12)) (64)) )) (64)) + PAGE_SIZE ) ) )
  **  ((( &( "cur" ) )) # UInt64  |-> (unsigned_last_nbits ((cur + (unsigned_last_nbits ((Z.shiftl nr_pages_pre 12)) (32)) )) (64)))
.

Definition hyp_early_alloc_contig_partial_solve_wit_3 := hyp_early_alloc_contig_partial_solve_wit_3_pure -> hyp_early_alloc_contig_partial_solve_wit_3_aux.

Definition hyp_early_alloc_contig_which_implies_wit_1 := 
forall (i: Z) (nr_pages: Z) (p: Z) (ret: Z) (end_: Z) ,
  [| (i < nr_pages) |] 
  &&  [| (p = (ret + (i * PAGE_SIZE ) )) |] 
  &&  [| ((ret + (nr_pages * PAGE_SIZE ) ) <= end_) |]
  &&  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char (ret + (i * PAGE_SIZE ) ) (end_ - (ret + (i * PAGE_SIZE ) ) ) )
|--
  (store_undef_array undef_store_char p PAGE_SIZE )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char (p + PAGE_SIZE ) (end_ - (p + PAGE_SIZE ) ) )
.

Definition hyp_early_alloc_contig_which_implies_wit_2 := 
forall (i: Z) (p: Z) (ret: Z) (end_: Z) ,
  [| (i >= 0) |] 
  &&  [| (p = (ret + (i * PAGE_SIZE ) )) |]
  &&  (store_array store_char ret (i * PAGE_SIZE ) (repeat (0) ((Z_to_nat ((i * PAGE_SIZE ))))) )
  **  (store_array store_char p PAGE_SIZE (repeat (0) ((Z_to_nat (PAGE_SIZE)))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char (p + PAGE_SIZE ) (end_ - (p + PAGE_SIZE ) ) )
|--
  (store_array store_char ret ((i + 1 ) * PAGE_SIZE ) (repeat (0) ((Z_to_nat (((i + 1 ) * PAGE_SIZE ))))) )
  **  ((( &( "end_" ) )) # UInt64  |-> end_)
  **  (store_undef_array undef_store_char (ret + ((i + 1 ) * PAGE_SIZE ) ) (end_ - (ret + ((i + 1 ) * PAGE_SIZE ) ) ) )
.

Module Type VC_Correct.

Include example_Strategy_Correct.

Axiom proof_of_hyp_early_alloc_nr_pages_safety_wit_1 : hyp_early_alloc_nr_pages_safety_wit_1.
Axiom proof_of_hyp_early_alloc_nr_pages_return_wit_1 : hyp_early_alloc_nr_pages_return_wit_1.
Axiom proof_of_clear_page_safety_wit_1 : clear_page_safety_wit_1.
Axiom proof_of_clear_page_safety_wit_2 : clear_page_safety_wit_2.
Axiom proof_of_clear_page_safety_wit_3 : clear_page_safety_wit_3.
Axiom proof_of_clear_page_safety_wit_4 : clear_page_safety_wit_4.
Axiom proof_of_clear_page_entail_wit_1 : clear_page_entail_wit_1.
Axiom proof_of_clear_page_entail_wit_2 : clear_page_entail_wit_2.
Axiom proof_of_clear_page_return_wit_1 : clear_page_return_wit_1.
Axiom proof_of_clear_page_partial_solve_wit_1_pure : clear_page_partial_solve_wit_1_pure.
Axiom proof_of_clear_page_partial_solve_wit_1 : clear_page_partial_solve_wit_1.
Axiom proof_of_clear_page_partial_solve_wit_2_pure : clear_page_partial_solve_wit_2_pure.
Axiom proof_of_clear_page_partial_solve_wit_2 : clear_page_partial_solve_wit_2.
Axiom proof_of_clear_page_which_implies_wit_1 : clear_page_which_implies_wit_1.
Axiom proof_of_clear_page_which_implies_wit_2 : clear_page_which_implies_wit_2.
Axiom proof_of_hyp_early_alloc_page_safety_wit_1 : hyp_early_alloc_page_safety_wit_1.
Axiom proof_of_hyp_early_alloc_page_entail_wit_1 : hyp_early_alloc_page_entail_wit_1.
Axiom proof_of_hyp_early_alloc_page_return_wit_1 : hyp_early_alloc_page_return_wit_1.
Axiom proof_of_hyp_early_alloc_page_return_wit_2 : hyp_early_alloc_page_return_wit_2.
Axiom proof_of_hyp_early_alloc_page_partial_solve_wit_1_pure : hyp_early_alloc_page_partial_solve_wit_1_pure.
Axiom proof_of_hyp_early_alloc_page_partial_solve_wit_1 : hyp_early_alloc_page_partial_solve_wit_1.
Axiom proof_of_hyp_early_alloc_page_partial_solve_wit_2 : hyp_early_alloc_page_partial_solve_wit_2.
Axiom proof_of_hyp_early_alloc_page_which_implies_wit_1 : hyp_early_alloc_page_which_implies_wit_1.
Axiom proof_of_hyp_early_alloc_contig_safety_wit_1 : hyp_early_alloc_contig_safety_wit_1.
Axiom proof_of_hyp_early_alloc_contig_safety_wit_2 : hyp_early_alloc_contig_safety_wit_2.
Axiom proof_of_hyp_early_alloc_contig_safety_wit_3 : hyp_early_alloc_contig_safety_wit_3.
Axiom proof_of_hyp_early_alloc_contig_safety_wit_4 : hyp_early_alloc_contig_safety_wit_4.
Axiom proof_of_hyp_early_alloc_contig_entail_wit_1 : hyp_early_alloc_contig_entail_wit_1.
Axiom proof_of_hyp_early_alloc_contig_entail_wit_2 : hyp_early_alloc_contig_entail_wit_2.
Axiom proof_of_hyp_early_alloc_contig_entail_wit_3 : hyp_early_alloc_contig_entail_wit_3.
Axiom proof_of_hyp_early_alloc_contig_return_wit_2 : hyp_early_alloc_contig_return_wit_2.
Axiom proof_of_hyp_early_alloc_contig_return_wit_3 : hyp_early_alloc_contig_return_wit_3.
Axiom proof_of_hyp_early_alloc_contig_partial_solve_wit_1_pure : hyp_early_alloc_contig_partial_solve_wit_1_pure.
Axiom proof_of_hyp_early_alloc_contig_partial_solve_wit_1 : hyp_early_alloc_contig_partial_solve_wit_1.
Axiom proof_of_hyp_early_alloc_contig_partial_solve_wit_2 : hyp_early_alloc_contig_partial_solve_wit_2.
Axiom proof_of_hyp_early_alloc_contig_partial_solve_wit_3_pure : hyp_early_alloc_contig_partial_solve_wit_3_pure.
Axiom proof_of_hyp_early_alloc_contig_partial_solve_wit_3 : hyp_early_alloc_contig_partial_solve_wit_3.
Axiom proof_of_hyp_early_alloc_contig_which_implies_wit_1 : hyp_early_alloc_contig_which_implies_wit_1.
Axiom proof_of_hyp_early_alloc_contig_which_implies_wit_2 : hyp_early_alloc_contig_which_implies_wit_2.

End VC_Correct.
