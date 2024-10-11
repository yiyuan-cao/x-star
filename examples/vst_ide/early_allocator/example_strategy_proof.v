Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import SeparationLogic.
Require Import example_strategy_goal.
Import naive_C_Rules.
Require Import lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma example_strategy0_correctness : example_strategy0.
Proof.
  pre_process.
Qed.

Lemma example_strategy1_correctness : example_strategy1.
Proof.
  pre_process.
  cancel.
  apply shallow_allp_right. intros.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
Qed.

Lemma example_strategy10_correctness : example_strategy10.
Proof.
  pre_process.
Qed.

Lemma example_strategy20_correctness : example_strategy20.
Proof.
  pre_process.
Qed.

Lemma example_strategy22_correctness : example_strategy22.
Proof.
  pre_process.
  subst.
  entailer!.
Qed.

Lemma example_strategy30_correctness : example_strategy30.
Proof.
  pre_process.
Qed.

Lemma example_strategy21_correctness : example_strategy21.
Proof.
  pre_process.
  subst.
  rewrite -> Z.add_0_r.
  entailer!.
Qed.

Lemma example_strategy31_correctness : example_strategy31.
Proof.
  pre_process.
  Intros. subst.
  unfold store_array. simpl store_array_rec.
  entailer!.
Qed.

Lemma example_strategy11_correctness : example_strategy11.
Proof.
  pre_process.
  subst.
  unfold store_undef_array.
  entailer!.
Qed.
