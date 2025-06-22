Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Hammer Require Import Tactics.
From TLC Require Import LibTactics.

Require Import nbe.stlc.def_syntax.
Require Import nbe.stlc.def_nbe.
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