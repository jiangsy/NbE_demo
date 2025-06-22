Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Hammer Require Import Tactics.
From TLC Require Import LibTactics.

Require Import nbe.stlc.def_syntax.
Require Import nbe.stlc.def_nbe.

Lemma app_eval_det : 
  ( forall t ρ a1, ⟦ t ⟧ ρ ↘ a1 -> forall a2, ⟦ t ⟧ ρ ↘ a2 -> a1 = a2 ) /\
  ( forall f a b1, f ∙ a ↘ b1 -> forall b2, f ∙ a ↘ b2 -> b1 = b2 ).
Proof.
  apply eval_app_mutind; try sauto limit:50.
Qed.

Lemma rne_rnf_det : 
  ( forall n e u1, Rⁿᵉ ⦇ n ⦈ e ↘ u1 -> forall u2, Rⁿᵉ ⦇ n ⦈ e ↘ u2 -> u1 = u2 ) /\ 
  ( forall n d v1, Rⁿᶠ ⦇ n ⦈ d ↘ v1 -> forall v2, Rⁿᶠ ⦇ n ⦈ d ↘ v2 -> v1 = v2 ).
Proof.
  apply rne_rnf_mutind; intros; try sauto limit:50 use:app_eval_det.
  - inversion H0. subst.
    eapply app_eval_det in a; sauto. 
Qed.

Corollary rne_det : forall n e u1 u2, 
  Rⁿᵉ ⦇ n ⦈ e ↘ u1 -> 
  Rⁿᵉ ⦇ n ⦈ e ↘ u2 -> 
  u1 = u2.  
Proof.
  sauto use:rne_rnf_det.
Qed.

Corollary rnf_det : forall n d v1 v2, 
  Rⁿᶠ ⦇ n ⦈ d ↘ v1 -> 
  Rⁿᶠ ⦇ n ⦈ d ↘ v2 -> 
  v1 = v2.
Proof.
  sauto use:rne_rnf_det.
Qed.