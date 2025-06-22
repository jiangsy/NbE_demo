Require Import Coq.Program.Equality.

Require Import nbe.stlc.def_as2.
Require Import nbe.stlc.def_syntactic.

Inductive D : Set :=
  | d_true
  | d_false
  | d_abs (t : exp) (ρ : nat -> D)
  | d_refl (T: typ) (e : Dne)
with Dne : Set :=
  | dne_l (n : nat) 
  | dne_if (T : typ) (dt df : Dnf) (db : Dne)
  | dne_app (e : Dne) (d : Dnf)
with Dnf : Set :=
  | dnf_reif (T : typ) (a : D).

Notation " ( 'ƛ' t ) ρ " := (d_abs t ρ)
  (at level 55).

Definition env := nat -> D.

Definition add (ρ : env) (d : D) : env :=
  fun n => match n with 
    | 0 => d
    | S n => ρ n
    end.

Definition drop : env -> env :=
  fun ρ n => ρ (S n).

Notation "ρ ↦ d" := (add ρ d)
  (at level 48, left associativity).

Reserved Notation "f ∙ a ↘ b"
  (at level 55, a at next level, no associativity).
Reserved Notation "⟦ t ⟧ ρ ↘ a"
  (at level 55, ρ at next level, no associativity).
Reserved Notation "if( T , db , dt , df ) ↘ d"
  (at level 55, db at next level, dt at next level, df at next level, no associativity).
Inductive eval_rel : exp -> env -> D -> Prop :=
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
with app_rel : D -> D -> D -> Prop :=
  | app_abs : forall t ρ a b,
    ⟦ t ⟧ (ρ ↦ a) ↘ b ->
    (d_abs t ρ) ∙ a ↘ b
  | app_app : forall e d S T,
    (d_refl (S → T) e) ∙ d ↘ (d_refl T (dne_app e ( dnf_reif S d )))
with if_rel : typ -> D -> D -> D -> D -> Prop :=
  | if_true : forall dt df T,
    if( T , d_true , dt , df ) ↘ dt
  | if_false : forall dt df T,
    if( T , d_false , dt , df ) ↘ df
  | rec_rec : forall dt df e T,
    if( T , d_refl typ_bool e , dt , df) ↘ d_refl T (dne_if T (dnf_reif T dt) (dnf_reif T df) e)
where "f ∙ a ↘ b" := (app_rel f a b) and 
      "⟦ t ⟧ ρ ↘ a" := (eval_rel t ρ a) and 
      "if( T , db , dt , df ) ↘ d" := (if_rel T db dt df d).