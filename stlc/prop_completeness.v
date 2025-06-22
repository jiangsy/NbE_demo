Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Hammer Require Import Tactics.
From TLC Require Import LibTactics.

Require Import nbe.stlc.prop_nbe.

Definition sem_typ := d -> d -> Prop.

Definition sem_typ_top (d d' : d_nf) : Prop :=
  forall n, exists w, Rⁿᶠ ⦇ n ⦈ d ↘ w /\ Rⁿᶠ ⦇ n ⦈ d' ↘ w.

Definition sem_typ_bot (e e' : d_ne) : Prop :=
  forall n, exists u, Rⁿᵉ ⦇ n ⦈ e ↘ u /\ Rⁿᵉ ⦇ n ⦈ e' ↘ u.

Notation "e ≈ e' ∈ ⊥" := (sem_typ_bot e e')
  (at level 55, e' at next level, no associativity).

Notation "d ≈ d' ∈ ⊤" := (sem_typ_top d d')
  (at level 55, d' at next level, no associativity).

Lemma sem_bot_symm : forall e e',
  e ≈ e' ∈ ⊥ -> 
  e' ≈ e ∈ ⊥.
Proof.
  intros. hauto unfold:sem_typ_bot.
Qed.

Lemma sem_bot_trans : forall e1 e2 e3,
  e1 ≈ e2 ∈ ⊥ -> 
  e2 ≈ e3 ∈ ⊥ -> 
  e1 ≈ e3 ∈ ⊥.
Proof.
  intros. unfold sem_typ_bot in *. intros.
  specialize (H n). specialize (H0 n).
  destruct H as [u1 [Hrnee1 Hrnee2]].
  destruct H0 as [u2 [Hrnee2' Hrnee3]].
  sauto use:rne_det limit:100.
Qed.

Lemma sem_typ_bot_var : forall i,
  (dne_l i) ≈ (dne_l i) ∈ ⊥.
Proof.
  intros. unfold sem_typ_bot.
  sauto limit:50.
Qed.

Lemma sem_typ_bot_app : forall e e' d d',
  e ≈ e' ∈ ⊥ ->
  d ≈ d' ∈ ⊤ ->
  (dne_app e d) ≈ (dne_app e' d') ∈ ⊥.
Proof.
  intros. unfold sem_typ_bot in *. unfold sem_typ_top in *. 
  hauto ctrs:rne_rel.
Qed.

Lemma sem_typ_top_ne : forall e e',
  e ≈ e' ∈ ⊥ ->
  dnf_reif typ_bool (d_refl typ_bool e) ≈ dnf_reif typ_bool (d_refl typ_bool e') ∈ ⊤.
Proof.
  intros. 
  unfold sem_typ_top. unfold sem_typ_bot in *.
  sauto limit:100.
Qed.

Lemma sem_bot_if : forall T e e' dt df dt' df',
  e ≈ e' ∈ ⊥ ->
  dt ≈ dt' ∈ ⊤ ->
  df ≈ df' ∈ ⊤ ->
  dne_if T e dt df ≈ dne_if T e' dt' df' ∈ ⊥.
Proof.
  intros. unfold sem_typ_bot in *. unfold sem_typ_top in *.
  intros. specialize (H n). specialize (H0 n). specialize (H1 n).
  hauto ctrs:rne_rel limit:100.
Qed.

Lemma sem_top_true : 
  (dnf_reif typ_bool d_true) ≈ (dnf_reif typ_bool d_true) ∈ ⊤.
Proof.
  sauto.
Qed.

Lemma sem_top_false : 
  (dnf_reif typ_bool d_false) ≈ (dnf_reif typ_bool d_false) ∈ ⊤.
Proof.
  sauto.
Qed.

Lemma sem_typ_top_abs : forall f f' S T,
  (forall e e', e ≈ e' ∈ ⊥ -> 
    exists b b', f ∙ (d_refl S e) ↘ b /\ f' ∙ (d_refl S e') ↘ b' /\ 
      (dnf_reif T b) ≈ (dnf_reif T b') ∈ ⊤) ->
  (dnf_reif (S → T) f) ≈ (dnf_reif (S → T) f') ∈ ⊤.
Proof.
  intros. unfold sem_typ_top. intros.
  assert (dne_l n ≈ dne_l n ∈ ⊥) by (sauto use:sem_typ_bot_var).
  apply H in H0.
  destruct H0 as [b [b']]. intuition.
  unfold sem_typ_top in H3. specialize (H3 (1 + n)).
  hauto ctrs:rnf_rel limit:100.
Qed.
