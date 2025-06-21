Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Lia.

Require Import nbe.stlc.def_as2.

Declare Scope full_scope.
Delimit Scope full_scope with F.

Reserved Notation "⊢ Γ" 
  (at level 55, Γ at next level, no associativity).
Reserved Notation "Γ ⊢ t : T"
  (at level 55, t at next level, no associativity).
Reserved Notation  "Γ ⊢ t ≈ t' : T" 
  (at level 55, t at next level, t' at next level, no associativity).
Inductive WfCtx : Ctx -> Prop :=
| wf_ctx_nil : ⊢ nil
| wf_ctx_cons : forall Γ T i,
  ⊢ Γ ->
  Γ ⊢ T : (𝕊 i) ->
  ⊢ (T :: Γ)
with WfExp : Ctx -> Exp -> Exp -> Prop :=
| typing_nat : forall Γ i,
  ⊢ Γ ->
  Γ ⊢ exp_nat : (𝕊 i)
| typing_set : forall Γ i,
  ⊢ Γ ->
  Γ ⊢ (𝕊 i) : (exp_set (1 + i))
| typing_pi : forall Γ S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ exp_pi S T : 𝕊 i
| typing_var : forall Γ n T,
  ⊢ Γ ->
  n : T ∈ Γ ->
  Γ ⊢ (exp_var n) : T
| typing_zero : forall Γ,
  ⊢ Γ ->
  Γ ⊢ exp_zero : exp_nat
| typing_suc : forall Γ t,
  Γ ⊢ t : exp_nat ->
  Γ ⊢ (exp_suc t) : exp_nat
| typing_rec : forall Γ tz ts tn T i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts : ( T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ) ->
  Γ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts tn : T [| tn ]
| typing_abs : forall Γ t S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ t : T ->
  Γ ⊢ (exp_abs t) : (exp_pi S T) 
| typing_app : forall Γ r s S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ r : exp_pi S T ->
  Γ ⊢ s : S ->
  Γ ⊢ r ▫ s : T [| s ]
| typing_subst : forall Γ Δ σ t T,
  Γ ⊢s σ : Δ ->
  Δ ⊢ t : T ->
  Γ ⊢ t [ σ ] : T [ σ ]
| typing_cumu : forall Γ T i,
  Γ ⊢ T : 𝕊 i ->
  Γ ⊢ T : exp_set (1 + i)
| typing_conv : forall Γ t S T i,
  Γ ⊢ t : T ->
  Γ ⊢ T ≈ S : 𝕊 i ->
  Γ ⊢ t : S
with EqExp : Ctx -> Exp -> Exp -> Exp -> Prop :=
| eq_exp_prop_nat : forall Γ Δ σ i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ ℕ [ σ ] ≈ ℕ : 𝕊 i
| eq_exp_prop_set : forall Γ Δ σ i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ 𝕊 i [ σ ] ≈ 𝕊 i : exp_set (1 + i)
| eq_exp_prop_pi : forall Γ Δ σ S T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : 𝕊 i ->
  (S :: Δ) ⊢ T : 𝕊 i ->
  Γ ⊢ exp_pi S T [ σ ] ≈ exp_pi (S [ σ ]) (T [subst_ext (σ ∘ ↑) (exp_var 0)]) : 𝕊 i
| eq_exp_prop_zero : forall Γ Δ σ,
  Γ ⊢s σ : Δ ->
  Γ ⊢ exp_zero ≈ exp_zero [ σ ] : ℕ
| eq_exp_prop_suc : forall Γ Δ t σ,
  Γ ⊢s σ : Δ ->
  Δ ⊢ t : ℕ ->
  Γ ⊢ exp_suc t [ σ ] ≈ exp_suc (t [ σ ]) : ℕ
| eq_exp_prop_app : forall Γ Δ r s σ S T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ r : exp_pi S T ->
  Δ ⊢ S : exp_set i ->
  (S :: Δ) ⊢ T : exp_set i ->
  Δ ⊢ s : S ->
  Γ ⊢ (r ▫ s) [ σ ] ≈ (r [ σ ]) ▫ (s [ σ ]) : T [ subst_ext σ (s [ σ ]) ]
| eq_exp_prop_rec : forall Γ Δ σ tz ts tn T i,
  Γ ⊢s σ : Δ ->
  (ℕ :: Δ) ⊢ T : 𝕊 i ->
  Δ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Δ) ⊢ ts : T [ subst_ext ( ↑ ∘ ↑ ) (exp_suc (exp_var 1)) ] ->
  Δ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts tn [ σ ] ≈ exp_rec (T [q σ]) (tz [σ]) (ts [q (q σ)]) (tn [ σ ]) : T [ subst_ext σ (tn [ σ ]) ]
| eq_exp_prop_abs : forall Γ Δ σ t S T,
  Γ ⊢s σ : Δ ->
  (S :: Δ) ⊢ t : T ->
  Γ ⊢ (λ t) [ σ ] ≈ (λ (t [q σ])) : (exp_pi S T) [ σ ]
| eq_exp_comp_pi : forall Γ S S' T T' i, 
  Γ ⊢ S : 𝕊 i ->
  Γ ⊢ S ≈ S' : 𝕊 i ->
  (S :: Γ) ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ exp_pi S T ≈ exp_pi S' T' : 𝕊 i
| eq_exp_comp_var : forall Γ n T,
  ⊢ Γ ->
  n : T ∈ Γ ->
  Γ ⊢ exp_var n ≈ exp_var n : T
| eq_exp_comp_zero : forall Γ,
  ⊢ Γ ->
  Γ ⊢ exp_zero ≈ exp_zero : ℕ
| eq_exp_comp_suc : forall Γ t t',
  Γ ⊢ t ≈ t' : ℕ ->
  Γ ⊢ exp_suc t ≈ exp_suc t' : ℕ
| eq_exp_comp_app : forall Γ r r' s s' S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ r ≈ r' : exp_pi S T ->
  Γ ⊢ s ≈ s' : S ->
  Γ ⊢ r ▫ s ≈ r' ▫ s' : T [| s ]
| eq_exp_comp_rec : forall Γ tz tz' ts ts' tn tn' T T' i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz ≈ tz' : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts ≈ ts' : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ tn ≈ tn' : ℕ ->
  (ℕ :: Γ) ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ exp_rec T tz ts tn ≈ exp_rec T' tz' ts' tn' : T [| tn ]
| eq_exp_comp_abs : forall Γ t t' S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ t ≈ t' : T ->
  Γ ⊢ (λ t) ≈ (λ t') : exp_pi S T
| eq_exp_comp_subst : forall Γ Δ t t' σ σ' T,
  Γ ⊢s σ ≈ σ' : Δ ->
  Δ ⊢ t ≈ t' : T ->
  Γ ⊢ t [ σ ] ≈ t' [ σ' ] : T [ σ ]
| eq_exp_beta_abs : forall Γ t s S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  (S :: Γ) ⊢ t : T ->
  Γ ⊢ s : S ->
  Γ ⊢ (λ t) ▫ s ≈ t [| s ] : T [| s ] 
| eq_exp_beta_rec_zero : forall Γ tz ts T i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ exp_rec T tz ts exp_zero ≈ tz : T [| exp_zero ]
| eq_exp_beta_rec_suc : forall Γ tz ts tn T i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts (exp_suc tn) ≈ ts [ subst_ext (subst_ext subst_id tn) (exp_rec T tz ts tn) ] : T [| exp_suc tn ]
| eq_exp_eta_abs : forall Γ t S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ t : exp_pi S T ->
  Γ ⊢ t ≈ exp_abs (t [ ↑ ] ▫ (exp_var 0)) : exp_pi S T
| eq_exp_subst_id : forall Γ t T,
  Γ ⊢ t : T ->
  Γ ⊢ t [ subst_id ] ≈ t : T
| eq_exp_substs_shift : forall Γ S T n,
  n : T ∈ Γ ->
  ⊢ (S :: Γ) ->
  (S :: Γ) ⊢ exp_var n [ ↑ ] ≈ exp_var (1 + n) : T [ ↑ ]
| eq_exp_subst_comp : forall Γ1 Γ2 Γ3 σ1 σ2 t T,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ3 ⊢ t : T ->
  Γ1 ⊢ t [ σ2 ∘ σ1 ] ≈ t [ σ2 ] [ σ1 ] : T [ σ2 ∘ σ1 ]
| eq_exp_subst_ext_var_0 : forall Γ Δ σ s S i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : 𝕊 i ->
  Γ ⊢ s : S [ σ ] ->
  Γ ⊢ exp_var 0 [ subst_ext σ s ] ≈ s : S [ σ ] 
| eq_exp_subst_ext_var_sn : forall Γ Δ σ s S T n i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : 𝕊 i ->
  Γ ⊢ s : S [ σ ] ->
  n : T ∈ Δ ->
  Γ ⊢ exp_var (1 + n) [ subst_ext σ s ] ≈ exp_var n [ σ ] : T [ σ ]
| eq_exp_conv : forall Γ t t' T T' i,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ t ≈ t' : T'
| eq_exp_cumu : forall Γ T T' i,
  Γ ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ T ≈ T' : exp_set (1 + i)
| eq_exp_sym : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊢ t' ≈ t : T
| eq_exp_trans : forall Γ t1 t2 t3 T,
  Γ ⊢ t1 ≈ t2 : T ->
  Γ ⊢ t2 ≈ t3 : T ->
  Γ ⊢ t1 ≈ t3 : T
where "⊢ Γ" := (WfCtx Γ) : full_scope and
      "Γ ⊢ t : T" := (WfExp Γ t T) : full_scope and 
      "Γ ⊢ t ≈ t' : T" := (EqExp Γ t t' T) : full_scope. 

Scheme wf_exp_ind := Induction for WfExp Sort Prop
  with eq_exp_ind := Induction for EqExp Sort Prop.

Combined Scheme wf_exp_eq_exp_mutind from wf_exp_ind, eq_exp_ind.

#[local] Hint Constructors WfCtx WfExp EqExp : core.