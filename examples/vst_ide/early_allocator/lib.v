Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z_scope.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Local Open Scope sac.

Notation Z_to_nat := Z.to_nat.

Notation UINT_MAX := (2^32 - 1).

Definition undef_store_char p i := ((p + i * sizeof(CHAR)) # Char |->_).
Definition store_char p i v := ((p + i * sizeof(CHAR)) # Char |-> v).

Notation PAGE_SHIFT := 12.
Notation PAGE_SIZE := 4096.

Lemma store_array_rec_snoc : forall {A} (a : A) l storeA p lo hi,
  storeA p hi a ** store_array_rec storeA p lo hi l |--
  store_array_rec storeA p lo (hi + 1) (l ++ (a::nil)).
Proof.
  induction l; intros; simpl.
  - Intros. subst.
    entailer!.
  - sep_apply IHl.
    entailer!.
Qed.

Lemma store_undef_char_array_split : forall m n p, 0 <= m <= n ->
  store_undef_array undef_store_char p n |--
  store_undef_array undef_store_char p m **
  store_undef_array undef_store_char (p + m) (n - m).
Proof.
  intros.
  pose proof store_undef_array_divide.
  specialize H0 with (size := 1) (storeA := fun p => p # Char |->_).
  rewrite -> H0 with (m := m).
  - rewrite -> Z.mul_1_r.
    entailer!.
  - assumption.
  - unfold undef_store_char.
    rewrite -> sizeof_char.
    reflexivity.
Qed.

Lemma store_char_array_merge : forall p l1 l2,
  store_array store_char p (Zlength l1) l1 **
  store_array store_char (p + Zlength l1) (Zlength l2) l2 |--
  store_array store_char p (Zlength l1 + Zlength l2) (l1 ++ l2).
Proof.
  intros.
  pose proof (Zlength_nonneg l1).
  pose proof (Zlength_nonneg l2).
  pose proof (@store_array_divide Z).
  specialize H1 with (size := 1) (storeA := fun p v => p # Char |-> v).
  rewrite -> H1 with (l := l1 ++ l2) (m := Zlength l1) (f := store_char).
  - rewrite -> Z.mul_1_r.
    rewrite -> Z.add_simpl_l.
    rewrite -> sublist_app_exact1.
    rewrite -> sublist_split_app_r with (len := Zlength l1) by lia.
    rewrite -> Z.sub_diag.
    rewrite -> Z.add_simpl_l.
    rewrite -> sublist_self by reflexivity.
    entailer!.
  - lia.
  - rewrite -> Zlength_app.
    subst. reflexivity.
  - unfold store_char.
    rewrite -> sizeof_char.
    reflexivity.
  - reflexivity.
Qed.
