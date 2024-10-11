Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition example_strategy0 :=
  forall ty (v : Z) (p : Z),
    TT &&
    emp **
    ((poly_store ty p v))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((poly_store ty p v))
    ).

Definition example_strategy1 :=
  forall ty (v : Z) (p : Z),
    TT &&
    emp **
    ((poly_store ty p v))
    |--
    (
    TT &&
    emp **
    ((poly_store ty p v))
    ) ** (
    ALL (x : Z),
      TT &&
      emp **
      ((poly_store ty p x)) -*
      TT &&
      emp **
      ((poly_store ty p x))
      ).

Definition example_strategy10 :=
  forall (storeA : (Z -> (Z -> Assertion))) (lo : Z) (n : nat) (hi : Z) (p : Z),
    TT &&
    emp **
    ((store_undef_array_rec storeA p lo hi n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_undef_array_rec storeA p lo hi n))
    ).

Definition example_strategy20 :=
  forall (storeA : (Z -> (Z -> Assertion))) (n : Z) (p : Z),
    TT &&
    emp **
    ((store_undef_array storeA p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_undef_array storeA p n))
    ).

Definition example_strategy22 :=
  forall (n : Z) (m : Z) (storeA : (Z -> (Z -> Assertion))) (p : Z),
    TT &&
    ([| (n = m) |]) &&
    emp **
    ((store_undef_array storeA p n))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_undef_array storeA p m))
    ).

Definition example_strategy30 :=
  forall (A : Type) (storeA : (Z -> (Z -> (A -> Assertion)))) (n : Z) (l : (list A)) (p : Z),
    TT &&
    emp **
    ((store_array storeA p n l))
    |--
    (
    TT &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    ((store_array storeA p n l))
    ).

Definition example_strategy21 :=
  forall (e : Z),
    TT &&
    ([| (e = 0) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (storeA : (Z -> (Z -> Assertion))) (n : Z) (p : Z),
      TT &&
      emp **
      ((store_undef_array storeA p n)) -*
      TT &&
      emp **
      ((store_undef_array storeA (Z.add p e) n))
      ).

Definition example_strategy31 :=
  forall (n : Z),
    TT &&
    ([| (n = 0) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (A : Type) (l : (list A)) (storeA : (Z -> (Z -> (A -> Assertion)))) (p : Z),
      TT &&
      ([| (l = (@nil A)) |]) &&
      emp -*
      TT &&
      emp **
      ((store_array storeA p n l))
      ).

Definition example_strategy11 :=
  forall (n : Z) (m : Z),
    TT &&
    ([| (n = m) |]) &&
    emp
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (storeA : (Z -> (Z -> Assertion))) (p : Z),
      TT &&
      emp **
      ((store_undef_array storeA p n)) -*
      TT &&
      emp **
      ((store_undef_array_rec storeA p 0 n (@Z_to_nat m)))
      ).

Module Type example_Strategy_Correct.

  Axiom example_strategy0_correctness : example_strategy0.
  Axiom example_strategy1_correctness : example_strategy1.
  Axiom example_strategy10_correctness : example_strategy10.
  Axiom example_strategy20_correctness : example_strategy20.
  Axiom example_strategy22_correctness : example_strategy22.
  Axiom example_strategy30_correctness : example_strategy30.
  Axiom example_strategy21_correctness : example_strategy21.
  Axiom example_strategy31_correctness : example_strategy31.
  Axiom example_strategy11_correctness : example_strategy11.

End example_Strategy_Correct.
