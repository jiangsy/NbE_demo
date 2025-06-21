Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Lia.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import nbe.stlc.def_as2.

Declare Scope full_scope.
Delimit Scope full_scope with F.

Import SubstNotations.
Import UnscopedNotations.

Definition ctx := list typ.

Notation "S → T" := (typ_arr S T)
  (at level 54, right associativity).

Notation "'λ' t" := (exp_abs t)
  (at level 55). 

Notation "r ▫ s" := (exp_app r s)
  (at level 53, left associativity).

Reserved Notation "Γ ⊢ t : T" 
  (at level 55, t at next level, no associativity).
Inductive wf_exp : ctx -> exp -> typ -> Prop := 
  | wf_exp_v : forall Γ n T,
    nth_error Γ n = Some T ->
    Γ ⊢ (exp_var n) : T
  | wf_exp_abs : forall Γ S T t ,
    (S :: Γ) ⊢ t : T ->
    Γ ⊢ (exp_abs t) : S → T
  | wf_exp_app : forall Γ r s S T,
    Γ ⊢ r : S → T ->
    Γ ⊢ s : S ->
    Γ ⊢ (exp_app r s) : T
where "Γ ⊢ t : T" := (wf_exp Γ t T).

Inductive ne : Set :=
  | ne_v (vi : nat)
  | ne_app (u : ne) (v : nf)
  | ne_if (u : nf) (v1 v2 : nf)
with nf : Set :=
  | nf_ne (u : ne)
  | nf_abs (v : nf)
  | nf_true
  | nf_false.

Reserved Notation "Γ ⊢ t ≈ t' : T"
  (at level 55, t at next level, t' at next level, no associativity).
Inductive eq_exp : ctx -> exp -> exp -> typ -> Prop := 
| exp_eq_beta_abs : forall Γ s t S T,
    (S :: Γ) ⊢ t : T ->
    Γ ⊢ s : S ->
    Γ ⊢ exp_app (exp_abs t) s ≈ t [s..] : T
| exp_eq_beta_if_true : forall Γ t1 t2 T,
    Γ ⊢ exp_if exp_true t1 t2 ≈ t1 : T
| exp_eq_beta_if_false : forall Γ t1 t2 T,
    Γ ⊢ exp_if exp_false t1 t2 ≈ t2 : T
| exp_eq_comp_true : forall Γ,
    Γ ⊢ exp_true ≈ exp_true : typ_bool
| exp_eq_comp_false : forall Γ,
    Γ ⊢ exp_false ≈ exp_false : typ_bool
| exp_eq_comp_if : forall Γ r r' s s' t t' T,
    Γ ⊢ r ≈ r' : typ_bool ->
    Γ ⊢ s ≈ s' : T ->
    Γ ⊢ t ≈ t' : T ->
    Γ ⊢ exp_if r s t ≈ exp_if r' s' t' : T
| exp_eq_comp_var : forall Γ n T,
    nth_error Γ n = Some T ->
    Γ ⊢ exp_var n ≈ exp_var n : T
| exp_eq_comp_app : forall Γ r r' s s' S T,
    Γ ⊢ r ≈ r' : S → T ->
    Γ ⊢ s ≈ s' : S ->
    Γ ⊢ r ▫ s ≈ r' ▫ s' : T
| exp_eq_symm : forall Γ t t' T,
    Γ ⊢ t ≈ t' : T ->
    Γ ⊢ t' ≈ t : T
| exp_eq_trans : forall Γ t1 t2 t3 T,
    Γ ⊢ t1 ≈ t2 : T ->
    Γ ⊢ t2 ≈ t3 : T ->
    Γ ⊢ t1 ≈ t3 : T
| exp_eq_ext_xi : forall Γ t t' S T,
    (S :: Γ) ⊢ t ≈ t' : T ->
    Γ ⊢ (λ t) ≈ (λ t') : S → T
| exp_eq_ext_eta : forall Γ t S T,
    Γ ⊢ t : S → T ->
    Γ ⊢ t ≈ (λ (t⟨↑⟩ ▫ (exp_var 0))) : S → T
where "Γ ⊢ t ≈ t' : T" := (eq_exp Γ t t' T).

Fixpoint nf_to_exp (w : nf) : exp :=
  match w with 
  | nf_abs w' => exp_abs (nf_to_exp w')
  | nf_ne u => ne_to_exp u
  | nf_true => exp_true
  | nf_false => exp_false
  end
with ne_to_exp (u : ne) : exp :=
  match u with
  | ne_app u' w => exp_app (ne_to_exp u') (nf_to_exp w)
  | ne_v n => exp_var n
  | ne_if u' v1 v2 => exp_if (nf_to_exp u') (nf_to_exp v1) (nf_to_exp v2)
  end.

Coercion nf_to_exp : nf >-> exp.
Coercion ne_to_exp : ne >-> exp.
