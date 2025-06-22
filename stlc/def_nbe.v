Require Import nbe.stlc.def_as2.
Require Import nbe.stlc.def_syntax.

Inductive d : Set :=
  | d_true
  | d_false
  | d_abs (t : exp) (ρ : nat -> d)
  | d_refl (T: typ) (e : d_ne)
with d_ne : Set :=
  | dne_l (n : nat) 
  | dne_if (T : typ) (e : d_ne) (dt df : d_nf)
  | dne_app (e : d_ne) (d : d_nf)
with d_nf : Set :=
  | dnf_reif (T : typ) (a : d).

Notation " ( 'ƛ' t ) ρ " := (d_abs t ρ)
  (at level 55).

Definition env := nat -> d.

Definition add (ρ : env) (d : d) : env :=
  fun n => match n with 
    | 0 => d
    | S n => ρ n
    end.

Definition drop : env -> env :=
  fun ρ n => ρ (S n).

Notation "ρ ↦ d" := (add ρ d)
  (at level 48, left associativity).

Reserved Notation "if( T , db , dt , df ) ↘ d"
  (at level 55, db at next level, dt at next level, df at next level, no associativity).
Inductive if_rel : typ -> d -> d -> d -> d -> Prop :=
  | if_true : forall dt df T,
    if( T , d_true , dt , df ) ↘ dt
  | if_false : forall dt df T,
    if( T , d_false , dt , df ) ↘ df
  | if_ne : forall dt df e T,
    if( T , d_refl typ_bool e , dt , df) ↘ d_refl T (dne_if T e (dnf_reif T dt) (dnf_reif T df))
where "if( T , db , dt , df ) ↘ d" := (if_rel T db dt df d).

Reserved Notation "f ∙ a ↘ b"
  (at level 55, a at next level, no associativity).
Reserved Notation "⟦ t ⟧ ρ ↘ a"
  (at level 55, ρ at next level, no associativity).
Inductive eval_rel : exp -> env -> d -> Prop :=
  | eval_true : forall ρ,
    ⟦ exp_true ⟧ ρ ↘ d_true
  | eval_false : forall ρ,
    ⟦ exp_false ⟧ ρ ↘ d_false
  | eval_var : forall ρ n,
    ⟦ exp_var n ⟧ ρ ↘ (ρ n)
  | eval_abs : forall ρ t,
    ⟦ exp_abs t ⟧ ρ ↘ (d_abs t ρ)
  | eval_app : forall ρ r s f a b,
    ⟦ r ⟧ ρ ↘ f ->
    ⟦ s ⟧ ρ ↘ a ->
    f ∙ a ↘ b ->
    ⟦ exp_app r s ⟧ ρ ↘ b
with app_rel : d -> d -> d -> Prop :=
  | app_abs : forall t ρ a b,
    ⟦ t ⟧ (ρ ↦ a) ↘ b ->
    (d_abs t ρ) ∙ a ↘ b
  | app_app : forall e d S T,
    (d_refl (S → T) e) ∙ d ↘ (d_refl T (dne_app e ( dnf_reif S d )))
where "f ∙ a ↘ b" := (app_rel f a b) and 
      "⟦ t ⟧ ρ ↘ a" := (eval_rel t ρ a).

Scheme eval_ind := Induction for eval_rel Sort Prop
  with app_ind := Induction for app_rel Sort Prop.

Combined Scheme eval_app_mutind from eval_ind, app_ind.

Reserved Notation " 'Rⁿᶠ' ⦇ n ⦈ d ↘ v"
  (at level 55, d at next level, no associativity).
Reserved Notation " 'Rⁿᵉ' ⦇ n ⦈ e ↘ u"
  (at level 55, e at next level, no associativity).
Inductive rnf_rel : nat -> d_nf -> nf -> Prop := 
  | rnf_abs : forall f b n t S T,
    f ∙ (d_refl S (dne_l n)) ↘ b ->
    Rⁿᶠ ⦇ 1 + n ⦈ (dnf_reif T b) ↘ t ->
    Rⁿᶠ ⦇ n ⦈ (dnf_reif (S → T) f) ↘ (nf_abs t)
  | rnf_true : forall n,
    Rⁿᶠ ⦇ n ⦈ (dnf_reif typ_bool d_true) ↘ nf_true
  | rnf_false : forall n,
    Rⁿᶠ ⦇ n ⦈ (dnf_reif typ_bool d_false) ↘ nf_false
  | rnf_ne : forall n e t,
    Rⁿᵉ ⦇ n ⦈ e ↘ t ->
    Rⁿᶠ ⦇ n ⦈ (dnf_reif typ_bool (d_refl typ_bool e)) ↘ (nf_ne t)
with rne_rel : nat -> d_ne -> ne -> Prop :=
  | rne_v : forall n k,
    Rⁿᵉ ⦇ n ⦈ (dne_l k) ↘ (ne_v (n - k - 1))
  | rne_app : forall n e d u v,
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᶠ ⦇ n ⦈ d ↘ v ->
    Rⁿᵉ ⦇ n ⦈ (dne_app e d) ↘ (ne_app u v)
  | rne_if : forall n e dt df u vt vf T,
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᶠ ⦇ n ⦈ dt ↘ vt ->
    Rⁿᶠ ⦇ n ⦈ df ↘ vf ->
    Rⁿᵉ ⦇ n ⦈ (dne_if T e dt df) ↘ (ne_if T u vt vf)
where " 'Rⁿᶠ' ⦇ n ⦈ d ↘ v" := (rnf_rel n d v) and 
      " 'Rⁿᵉ' ⦇ n ⦈ e ↘ u" := (rne_rel n e u).

Scheme rne_ind := Induction for rne_rel Sort Prop
  with rnf_ind := Induction for rnf_rel Sort Prop.

Combined Scheme rne_rnf_mutind from rne_ind, rnf_ind.

Definition Nbe (n : nat) (ρ : env) (t : exp) (T: typ) (w : nf) :=
  exists a, ⟦ t ⟧ ρ ↘ a /\ Rⁿᶠ ⦇ n ⦈ (dnf_reif T a) ↘ w.

Definition Completenss' (n : nat) (ρ ρ' : env) (s t : exp) (T : typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ' t T w.

Definition Completenss (n : nat) (ρ : env) (s t : exp) (T : typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ t T w.

Definition Soundness (Γ : ctx) (t : exp) (T : typ) (ρ : env) : Prop :=
  exists w, Nbe (length Γ) ρ t T w /\ Γ ⊢ t ≈ w : T.
