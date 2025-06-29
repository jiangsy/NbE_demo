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

Definition realize (T : typ) (A : sem_typ) : Prop :=
  (forall a a', A a a' -> dnf_reif T a ≈ dnf_reif T a' ∈ ⊤) /\
  (forall e e', e ≈ e' ∈ ⊥ -> A (d_refl T e) (d_refl T e')).

Notation "T ⊩ A" := (realize T A)
  (at level 55, no associativity).

Inductive sem_typ_bool : d -> d -> Prop :=
  | sbool_true: sem_typ_bool d_true d_true
  | sbool_false: sem_typ_bool d_false d_false
  | sbool_ne : forall e e',
      e ≈ e' ∈ ⊥ ->
      sem_typ_bool (d_refl typ_bool e) (d_refl typ_bool e').

Notation "a ≈ a' ∈ 'Bool'" := (sem_typ_bool a a')
  (at level 55, a' at next level, no associativity).

Lemma bool_realize_sem_bool : typ_bool ⊩ sem_typ_bool.
Proof.
  unfold realize. split; intros; try sauto limit:50.
  - destruct H; unfold sem_typ_top; intros; 
    try sauto limit:50.
    + unfold sem_typ_bot in H. specialize (H n).
      hauto limit:100 ctrs:rnf_rel. 
Qed.

Lemma sem_bool_symm : forall a a',
  a ≈ a' ∈ Bool -> 
  a' ≈ a ∈ Bool.
Proof.
  sauto use:sem_bot_symm limit:50.
Qed.

Lemma sem_bool_trans : forall a1 a2 a3,
  a1 ≈ a2 ∈ Bool -> 
  a2 ≈ a3 ∈ Bool -> 
  a1 ≈ a3 ∈ Bool.
Proof.
  sauto use:sem_bot_trans limit:50.
Qed.

Definition sem_arr (S T : sem_typ) : sem_typ :=
  fun f f' => forall a a', S a a' -> exists b b', f ∙ a ↘ b /\ f' ∙ a' ↘ b' /\ T b b'.

Notation "S ⇒ T" := (sem_arr S T)  (at level 55, right associativity).

Lemma arr_realize_sem_arr : forall S T A B,
  S ⊩ A -> T ⊩ B -> 
  (S → T) ⊩ (A ⇒ B).
Proof.
  intros. unfold realize in *. split.
  - intros. apply sem_typ_top_abs. intros. unfold sem_arr in H1.  
    sauto limit:50.
  - intros. unfold sem_arr. intros.
    sauto use:sem_typ_bot_app limit:100.
Qed.

Fixpoint interp_typ (T : typ) : sem_typ :=
  match T with 
  | typ_bool => sem_typ_bool 
  | S' → T' => (interp_typ S') ⇒ (interp_typ T')
  end.

Notation "⟦ T ⟧T" := (interp_typ T) (at level 55, no associativity).

Notation "a ≈ a' ∈ ⟦ T ⟧T" := ((interp_typ T) a a') 
  (at level 55, a' at next level, no associativity).

Lemma sem_typ_symm: forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  a' ≈ a ∈ ⟦ T ⟧T.
Proof.
  intros. gen a a'. induction T; intros.
  - sauto use:sem_bool_symm limit:50.
  - simpl in *. unfold sem_arr in *. intros.
    apply IHT1 in H0. sauto limit:50.
Qed.

Lemma sem_typ_trans : forall a1 a2 a3 T,
  a1 ≈ a2 ∈ ⟦ T ⟧T ->
  a2 ≈ a3 ∈ ⟦ T ⟧T ->
  a1 ≈ a3 ∈ ⟦ T ⟧T.
Proof.
  intros. gen a1 a2 a3. induction T; intros.
  - sauto use:sem_bool_trans limit:50.
  - simpl in *. unfold sem_arr in *. intros.
    apply sem_typ_symm in H1 as H1'.
    eapply IHT1 in H1 as H1''; eauto.
    apply H in H1 as IH1.
    apply H0 in H1'' as IH2.
    destruct IH1 as [b1 [b2]].
    destruct IH2 as [b2' [b3]].
    intuition.
    eapply app_det in H2; eauto. subst.
    sauto.
Qed.

Lemma sem_typ_refl : forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  a ≈ a ∈ ⟦ T ⟧T.
Proof.
  intros.
  eapply sem_typ_trans with (a2:=a'); eauto using sem_typ_symm.
Qed.

Lemma typ_realize_interp_typ : forall T,
  T ⊩ ⟦ T ⟧T.
Proof.
  intros. induction T.
  - apply bool_realize_sem_bool.
  - apply arr_realize_sem_arr; eauto.
Qed.

Lemma bot_subset_T : forall e e' T,
  e ≈ e' ∈ ⊥ ->
  d_refl T e ≈ d_refl T e' ∈ ⟦ T ⟧T.
Proof.
  intros. pose proof (typ_realize_interp_typ T).
  sauto unfold:realize.
Qed.

Lemma T_subset_top : forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  (dnf_reif T a) ≈ (dnf_reif T a') ∈ ⊤.
Proof.
  intros. pose proof (typ_realize_interp_typ T).
  sauto unfold:realize.
Qed.

Definition sem_env (ρ ρ' : env) (Γ : ctx) :=
  forall i T, nth_error Γ i = Some T -> (ρ i) ≈ (ρ' i) ∈ ⟦ T ⟧T.

Notation "ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ" := (sem_env ρ ρ' Γ)
  (at level 55, ρ' at next level, no associativity).

Lemma sem_env_symm : forall Γ ρ ρ',
  ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ ->
  ρ' ≈ ρ ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. unfold sem_env in *.
  sauto use:sem_typ_symm limit:50.
Qed.

Lemma sem_env_refl : forall Γ ρ ρ',
  ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ ->
  ρ ≈ ρ ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. unfold sem_env in *.
  sauto use:sem_typ_refl limit:50.
Qed.

Lemma sem_env_trans : forall Γ ρ1 ρ2 ρ3,
  ρ1 ≈ ρ2 ∈ ⟦ Γ ⟧Γ ->
  ρ2 ≈ ρ3 ∈ ⟦ Γ ⟧Γ ->
  ρ1 ≈ ρ3 ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. unfold sem_env in *. intros.
  sauto use:sem_typ_trans limit:50.
Qed.

Import UnscopedNotations.

(* 
The naive version of `eval_subst_prop` cannot be proved,
which is required by `sem_eq_beta_abs`.
*)
Module SemExp0.
  Definition sem_exp (Γ : ctx) (t t' : exp) (T : typ) : Prop := 
    forall ρ ρ', 
      ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ -> 
      exists a a', ⟦ t ⟧ ρ ↘ a /\ ⟦ t' ⟧ ρ' ↘ a' /\ a ≈ a' ∈ ⟦ T ⟧T.

  Notation "Γ ⊨ t ≈ t' : T" := (sem_exp Γ t t' T) 
    (at level 55, t at next level, t' at next level, no associativity).

  Notation "Γ ⊨ t : T" := (sem_exp Γ t t T) 
    (at level 55, t at next level, no associativity).

  (* feel like `sem_closure_inversion` in a useful prop, 
     as it always allow as to reapply the eta rule to get
     rid of the closure by applying an additional argument 
  *)
  Lemma sem_closure_inversion : forall t ρ a T,
    (ƛ t) ρ ≈ a ∈ ⟦ T ⟧T ->
    exists S' T', T = S' → T'.
  Proof.
    intros. destruct T; eauto.
    - simpl in H. dependent destruction H.
  Qed.

  Lemma eval_subst_prop : forall ρ t σ a ρ',
    ⟦ t[σ] ⟧ ρ ↘ a ->
    ⟦ σ ⟧s ρ ↘ ρ' ->
    ⟦ t ⟧ ρ' ↘ a.
  Proof.
    intros. gen a σ ρ. induction t; asimpl; try sauto limit:50; intros. 
    - dependent destruction H; asimpl in x;
      unfold eval_subst_rel in H0; admit.
    - dependent destruction H. 
      (* problematic *)
      admit. 
  Abort.

  Lemma eval_subst_prop : forall T ρ t σ a ρ',
    (* how to deal with this T *)
    a ≈ a ∈ ⟦ T ⟧T ->
    (* this is not true, we need type-preserving substitution *)
    ⟦ t[σ] ⟧ ρ ↘ a ->
    ⟦ σ ⟧s ρ ↘ ρ' ->
    exists a', ⟦ t ⟧ ρ' ↘ a' /\ a ≈ a' ∈ ⟦ T ⟧T.
  Proof.
    intros. gen T a σ ρ. induction t; asimpl; try sauto limit:50; intros.
    - apply H1 in H0. eexists; sauto.
    - admit.
    - dependent destruction H0.
      admit.
  Abort.

  Lemma sem_eq_exp_symm : forall Γ t t' T,
    Γ ⊨ t ≈ t' : T ->
    Γ ⊨ t' ≈ t : T.
  Proof.
    intros. unfold sem_exp in *. intros.
    apply sem_env_symm in H0.
    eapply H in H0.
    firstorder. sauto use:sem_typ_symm.
  Qed.

  (* for the old sem_exp def, congruence is trivial *)
  Lemma sem_eq_cong_abs : forall Γ t t' S T,
    (S :: Γ) ⊨ t ≈ t' : T ->
    Γ ⊨ (λ t) ≈ (λ t') : S → T.
  Proof.
    intros. unfold sem_exp in *; intros.
    do 2 eexists. split; [econstructor | split]; [econstructor |].
    simpl. unfold sem_arr. intros.
    assert (ρ ↦ a ≈ ρ' ↦ a' ∈ ⟦ S :: Γ ⟧Γ). {
      intros i n ?.
      destruct i; simpl; sauto.
    }
    sauto.
  Qed.

  Lemma sem_eq_beta_abs : forall Γ t s S T,
    Γ ⊨ t : S → T ->
    Γ ⊨ s : S ->
    Γ ⊨ (λ t) ▫ s ≈ t[s..] : T.
  Proof.
    intros. unfold sem_exp in *; intros.
    apply H in H1 as Ht.
    apply H0 in H1 as Hs. firstorder. simpl in *.
    unfold sem_arr in *.
    asimpl.
    (* problematic *)
    admit.
  Admitted.

  Lemma sem_eq_eta_abs : forall Γ t S T,
    Γ ⊨ t : S → T ->
    Γ ⊢ t ≈ (λ (t⟨↑⟩ ▫ (exp_var 0))) : S → T.
  Proof.
  Admitted.

End SemExp0.

(* 
In SemExp1, `sem_eq_cong_abs` depends on `eval_weaken_prop`, 
which is a more specialized form of `eval_subst_prop` in SemExp0.
but the naive version of `eval_weaken_prop` can neither be proved.

in the worst case, we may need to embed all subst_prop rules in explicit 
substitution in `sem_exp` defs here. if that's true, 
we have many more proof obligations to deal with.
*)
Module SemExp1.
  (* I think this cannot be true
     we must use type-preserving substitution,
     suppose Γ, Bool ⊢ var 0 : Bool
     σ = (↑,zero)
     then ⟦ var 0[σ] ⟧ ρ ↘ zero, and zero ≈ zero ∈ ⟦ Nat ⟧
     this PER model would give us
     Γ, Bool ⊢ var 0 ≈ var 0 : Nat
  *)
  Definition sem_exp (Γ : ctx) (t1 t2 : exp) (T : typ) : Prop :=
    forall (ρ1 ρ2 : env),
      ρ1 ≈ ρ2 ∈ ⟦ Γ ⟧Γ ->
      (forall (σ : nat -> exp) ρ1',
          ⟦ σ ⟧s ρ1 ↘ ρ1' ->
          exists a1 a2,
            ⟦ t1 ⟧ ρ1' ↘ a1 /\ ⟦ t2[σ] ⟧ ρ2 ↘ a2 /\ a1 ≈ a2 ∈ ⟦ T ⟧T) /\
      (forall (σ : nat -> exp) ρ2',
          ⟦ σ ⟧s ρ2 ↘ ρ2' ->
          exists a1 a2,
            ⟦ t1[σ] ⟧ ρ1 ↘ a1 /\ ⟦ t2 ⟧ ρ2' ↘ a2 /\ a1 ≈ a2 ∈ ⟦ T ⟧T).

  Notation "Γ ⊨ t ≈ t' : T" := (sem_exp Γ t t' T) 
    (at level 55, t at next level, t' at next level, no associativity).

  Notation "Γ ⊨ t : T" := (sem_exp Γ t t T) 
    (at level 55, t at next level, no associativity).

  Lemma sem_eq_exp_symm : forall Γ t t' T,
    Γ ⊨ t ≈ t' : T ->
    Γ ⊨ t' ≈ t : T.
  Proof.
    intros. unfold sem_exp in *. intros.
    apply sem_env_symm in H0.
    eapply H in H0.
    firstorder.
    - specialize (H1 _ _ H2). firstorder.
      repeat eexists; sauto use:sem_typ_symm limit:50.
    - specialize (H0 _ _ H2). firstorder.
      repeat eexists; sauto use:sem_typ_symm limit:50.
  Qed.

  Lemma eval_weaken_prop : forall t ρ a b,
    ⟦ t ⟨↑⟩ ⟧ (ρ ↦ b) ↘ a ->
    ⟦ t ⟧ ρ ↘ a.
  Proof.
    intros. gen ρ a b. induction t; intros; asimpl; try sauto limit:50.
    (* does not hold *)
    - admit.
  Admitted.

  Lemma sem_eq_cong_abs : forall Γ t t' S T,
    (S :: Γ) ⊨ t ≈ t' : T ->
    Γ ⊨ (λ t) ≈ (λ t') : S → T.
  Proof.
    intros. unfold sem_exp in *; intros.
    split.
    - intros. asimpl.
      do 2 eexists. split; [econstructor | split]; [econstructor |].
      intros a a' ?.
      assert (ρ1 ↦ a ≈ ρ2 ↦ a' ∈ ⟦ S :: Γ ⟧Γ). {
        intros i n ?.
        destruct i; simpl; sauto.
      }
      specialize (H _ _ H3) as [].
      assert (⟦  0 __exp .: (σ ∘ ⟨↑⟩) ⟧s ρ1 ↦ a ↘ ρ1' ↦ a). {
        intros i b ?. destruct i; simpl in *.
        - dependent destruction H5. auto.
        - eapply H1. unfold funcomp in H5.
          eapply eval_weaken_prop; eauto.
      }
      specialize (H _ _ H5) as [a1 [a2 [? []]]].
      sauto.
    - admit.
  Admitted.

  Lemma sem_eq_beta_abs : forall Γ t s S T,
    Γ ⊨ t : S → T ->
    Γ ⊨ s : S ->
    Γ ⊨ (λ t) ▫ s ≈ t[s..] : T.
  Proof.
  Admitted.

  Lemma sem_eq_eta_abs : forall Γ t S T,
    Γ ⊨ t : S → T ->
    Γ ⊢ t ≈ (λ (t⟨↑⟩ ▫ (exp_var 0))) : S → T.
  Proof.
  Admitted.

End SemExp1.
