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
Require Import goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import lib.
Local Open Scope sac.

Lemma proof_of_hyp_early_alloc_nr_pages_return_wit_1 : hyp_early_alloc_nr_pages_return_wit_1.
Proof.
  pre_process.
  repeat prop_apply store_uint64_range. Intros.
  Exists base_2 cur_2. entailer!.
  f_equal.
  rewrite -> UInt64_unsigned_eq by lia.
  reflexivity.
Qed.

Lemma proof_of_clear_page_entail_wit_1 : clear_page_entail_wit_1.
Proof.
  pre_process.
  rewrite -> Z.sub_0_r.
  unfold store_array. simpl store_array_rec.
  unfold store_undef_array.
  entailer!.
Qed.

Lemma proof_of_clear_page_return_wit_1 : clear_page_return_wit_1.
Proof.
  pre_process.
  assert (i = 4096) by lia. subst.
  simpl store_undef_array_rec.
  entailer!.
Qed.

Lemma proof_of_clear_page_which_implies_wit_1 : clear_page_which_implies_wit_1.
Proof.
  pre_process.
  replace (4096 - i) with (Z.succ (4096 - (i + 1))) by ring.
  rewrite -> Z2Nat.inj_succ by lia.
  unfold store_undef_array_rec. fold store_undef_array_rec.
  unfold undef_store_char.
  entailer!.
Qed.

Lemma proof_of_clear_page_which_implies_wit_2 : clear_page_which_implies_wit_2.
Proof.
  pre_process.
  unfold store_array.
  replace ((to + i * sizeof(CHAR)) # Char |-> 0)
     with (store_char to i 0) by reflexivity.
  sep_apply (@store_array_rec_snoc Z).
  rewrite -> Z2Nat.inj_add by lia.
  rewrite -> repeat_app. simpl repeat.
  entailer!.
Qed.

Lemma proof_of_hyp_early_alloc_page_entail_wit_1 : hyp_early_alloc_page_entail_wit_1.
Proof.
  pre_process.
  prop_apply store_uint64_range. Intros.
  entailer!.
Qed.

Lemma proof_of_hyp_early_alloc_page_return_wit_1 : hyp_early_alloc_page_return_wit_1.
Proof.
  pre_process.
  prop_apply (store_uint64_range (&("end_"))). Intros.
  enough False by contradiction.
  rewrite <- UInt64_unsigned_eq in H by lia.
  lia.
Qed.

Lemma proof_of_hyp_early_alloc_page_return_wit_2 : hyp_early_alloc_page_return_wit_2.
Proof.
  pre_process.
  prop_apply store_uint64_range. Intros.
  Exists end__2 (unsigned_last_nbits (cur_2 + 4096) 64). entailer!.
  rewrite <- UInt64_unsigned_eq by lia.
  reflexivity.
Qed.

Lemma proof_of_hyp_early_alloc_page_partial_solve_wit_1_pure : hyp_early_alloc_page_partial_solve_wit_1_pure.
Proof.
  pre_process.
  prop_apply (store_uint64_range (&("end_"))). Intros.
  entailer!.
  rewrite <- UInt64_unsigned_eq by lia.
  reflexivity.
Qed.

Lemma proof_of_hyp_early_alloc_page_which_implies_wit_1 : hyp_early_alloc_page_which_implies_wit_1.
Proof.
  pre_process.
  sep_apply (store_undef_char_array_split 4096).
  - rewrite <- Z.sub_add_distr.
    rewrite -> H.
    entailer!.
  - lia.
Qed.

Lemma proof_of_hyp_early_alloc_contig_entail_wit_1 : hyp_early_alloc_contig_entail_wit_1.
Proof.
  pre_process.
  prop_apply store_uint64_range. Intros.
  entailer!.
Qed.

Lemma proof_of_hyp_early_alloc_contig_entail_wit_2 : hyp_early_alloc_contig_entail_wit_2.
Proof.
  pre_process.
  rewrite -> Z.mul_0_l.
  rewrite -> Z.add_0_r.
  unfold store_array. simpl store_array_rec.
  entailer!.
Qed.

Lemma proof_of_hyp_early_alloc_contig_entail_wit_3 : hyp_early_alloc_contig_entail_wit_3.
Proof.
  pre_process.
  rewrite <- (UInt64_unsigned_eq (i + 1))
          by (rewrite -> max_unsigned_val; lia).
  sep_apply (store_uint64_undef_store_uint64 (&("p"))).
  entailer!.
Qed.

Lemma proof_of_hyp_early_alloc_contig_return_wit_2 : hyp_early_alloc_contig_return_wit_2.
Proof.
  pre_process.
  repeat prop_apply store_uint64_range. Intros.
  rewrite -> Z.shiftl_mul_pow2 in H by lia.
  replace (2 ^ 12) with 4096 in H by reflexivity.
  rewrite -> (unsigned_last_nbits_eq _ 32) in H by lia.
  rewrite <- UInt64_unsigned_eq in H by lia.
  lia.
Qed.

Lemma proof_of_hyp_early_alloc_contig_return_wit_3 : hyp_early_alloc_contig_return_wit_3.
Proof.
  pre_process.
  assert (i = nr_pages_pre) by lia. subst.
  prop_apply store_uint64_range. Intros.
  rewrite -> Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 12) with 4096 by reflexivity.
  rewrite -> (unsigned_last_nbits_eq _ 32) by lia.
  rewrite <- UInt64_unsigned_eq by lia.
  Exists end__2 (cur_2 + nr_pages_pre * 4096). entailer!.
Qed.

Lemma proof_of_hyp_early_alloc_contig_partial_solve_wit_1_pure : hyp_early_alloc_contig_partial_solve_wit_1_pure.
Proof.
  pre_process.
  prop_apply (store_uint64_range (&("end_"))). Intros.
  entailer!.
  rewrite -> Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 12) with 4096 by reflexivity.
  rewrite <- (UInt64_unsigned_eq (i * 4096))
          by (rewrite -> max_unsigned_val; lia).
  rewrite <- UInt64_unsigned_eq by lia.
  reflexivity.
Qed.

Lemma proof_of_hyp_early_alloc_contig_partial_solve_wit_3_pure : hyp_early_alloc_contig_partial_solve_wit_3_pure.
Proof.
  pre_process.
  prop_apply (store_uint64_range (&("end_"))). Intros.
  entailer!.
  rewrite -> Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 12) with 4096 by reflexivity.
  rewrite <- (UInt64_unsigned_eq (i * 4096))
          by (rewrite -> max_unsigned_val; lia).
  rewrite <- UInt64_unsigned_eq by lia.
  reflexivity.
Qed.

Lemma proof_of_hyp_early_alloc_contig_which_implies_wit_1 : hyp_early_alloc_contig_which_implies_wit_1.
Proof.
  pre_process.
  rewrite <- H0.
  entailer!.
  sep_apply (store_undef_char_array_split 4096).
  - rewrite -> Z.sub_add_distr.
    entailer!.
  - lia.
Qed.

Lemma proof_of_hyp_early_alloc_contig_which_implies_wit_2 : hyp_early_alloc_contig_which_implies_wit_2.
Proof.
  pre_process.
  replace (ret + (i + 1) * 4096) with (p + 4096) by (subst; ring).
  entailer!.
  subst.
  assert (forall {A} (x : A) n, n >= 0 ->
          Zlength (repeat x (Z_to_nat n)) = n). {
    intros.
    rewrite -> Zlength_correct.
    rewrite -> repeat_length.
    rewrite -> Z2Nat.id by lia.
    reflexivity.
  }
  pose proof (H0 _ 0 4096) ltac:(lia).
  pose proof (H0 _ 0 (i * 4096)) ltac:(lia).
  rewrite <- H1 at 4.
  rewrite <- H2 at 1 3.
  sep_apply store_char_array_merge.
  rewrite -> H1.
  rewrite -> H2.
  rewrite <- repeat_app.
  rewrite <- Z2Nat.inj_add by lia.
  rewrite <- Z.mul_succ_l.
  entailer!.
Qed.
