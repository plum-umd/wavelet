import Wavelet.Semantics.Defs

import Wavelet.Thm.Data.Function

/-! Definitions of simulations. -/

namespace Wavelet.Semantics

abbrev StrongSimilaritySt
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.SimilaritySt R sem₁.lts sem₂.lts sem₁.init sem₂.init

abbrev StrongSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts sem₂.lts sem₁.init sem₂.init

notation sem₁ " ≲ₛ" "[" R "] " sem₂ => StrongSimilaritySt sem₁ sem₂ R
infix:50 " ≲ₛ " => StrongSimilarity

abbrev WeakSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init

infix:50 " ≲ " => WeakSimilarity

private theorem WeakSimilarity.alt_helper
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {s₁ s₁' : sem₁.S} {s₂ : sem₂.S}
  (hsim : Lts.Similarity sem₁.lts (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init)
  (hR : hsim.Sim s₁ s₂)
  (hstep_tau : sem₁.lts.TauStar .τ s₁ s₁') :
  ∃ s₂', sem₂.lts.TauStar .τ s₂ s₂' ∧ hsim.Sim s₁' s₂' := by
  induction hstep_tau with
  | refl =>
    exists s₂
    constructor
    · exact .refl
    · exact hR
  | tail pref tail ih =>
    rename_i s₁'' s₁'
    have ⟨s₂'', hstep_s₂, hR₂''⟩ := ih
    have ⟨s₂', hstep_s₂', hR'⟩ := hsim.sim_step _ _ _ _ hR₂'' tail
    exists s₂'
    constructor
    · exact .trans hstep_s₂ hstep_s₂'.to_tau_star
    · exact hR'

theorem WeakSimilarity.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (hsim : Lts.Similarity sem₁.lts (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init) :
  Lts.Similarity (sem₁.lts.WeakStep .τ) (sem₂.lts.WeakStep .τ) sem₁.init sem₂.init
  := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    cases hstep with
    | refl =>
      exists s₂
      exact ⟨.refl, hR⟩
    | step htau₁' hstep' htau₁'' =>
      have ⟨s₂₁, hstep_s₂₁, hsim₁⟩ := alt_helper hsim hR htau₁'
      have ⟨s₂', hstep_s₂₂, hsim'⟩ := hsim.sim_step _ _ _ _ hsim₁ hstep'
      have ⟨s₂'', hstep_s₂₃, hsim''⟩ := alt_helper hsim hsim' htau₁''
      exists s₂''
      constructor
      · cases hstep_s₂₂ with
        | refl =>
          exact .from_tau_star (.trans hstep_s₂₁ hstep_s₂₃)
        | step htau₂₁ hstep₂ htau₂₂ =>
          exact .step (.trans hstep_s₂₁ htau₂₁) hstep₂ (.trans htau₂₂ hstep_s₂₃)
      · exact hsim''

theorem WeakSimilarity.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ sem := Lts.Similarity.refl_single .single

theorem WeakSimilarity.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ sem₂) (h₂ : sem₂ ≲ sem₃) :
  sem₁ ≲ sem₃ :=
  Lts.Similarity.trans h₁ (WeakSimilarity.alt h₂)

/-- Stronger than `WeakStep` and does not allow τ steps
before input, after output, or before/after yields. -/
inductive Lts.IORestrictedStep
  {S} [Arity Op]
  (lts : Lts S (Label Op V m n)) : Lts S (Label Op V m n) where
  | step_yield :
    lts.Step s (.yield o inputs outputs) s' →
    lts.IORestrictedStep s (.yield o inputs outputs) s'
  | step_input :
    lts.Step s (.input vals) s' →
    lts.TauStar .τ s' s'' →
    lts.IORestrictedStep s (.input vals) s''
  | step_output :
    lts.TauStar .τ s s' →
    lts.Step s' (.output vals) s'' →
    lts.IORestrictedStep s (.output vals) s''
  | step_tau :
    lts.TauStar .τ s s' →
    lts.IORestrictedStep s .τ s'

theorem Lts.IORestrictedStep.single
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' : S} {l : Label Op V m n}
  (hstep : lts.Step s l s')
  : lts.IORestrictedStep s l s' := by
  cases l with
  | yield => exact .step_yield hstep
  | input => exact .step_input hstep .refl
  | output => exact .step_output .refl hstep
  | τ => exact .step_tau (.single hstep)

/-- Append a τ transition at the end if allowed. -/
theorem Lts.IORestrictedStep.tail_tau
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' s'' : S} {l : Label Op V m n}
  (hl : l.isInput ∨ l.isSilent)
  (hstep : lts.IORestrictedStep s l s')
  (hstep_tau : lts.Step s' .τ s'') :
  lts.IORestrictedStep s l s'' := by
  cases hstep with
  | step_yield hstep' => simp at hl
  | step_input hstep₁ hstep₂ => exact .step_input hstep₁ (.tail hstep₂ hstep_tau)
  | step_output hstep₁ hstep₂ => simp at hl
  | step_tau hstep' => exact .step_tau (.tail hstep' hstep_tau)

/-- Append a non-τ transition at the end if allowed. -/
theorem Lts.IORestrictedStep.tail_non_tau
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s s' s'' : S} {l : Label Op V m n}
  (hl : l.isOutput ∨ l.isSilent)
  (hstep_tau : lts.IORestrictedStep s .τ s')
  (hstep : lts.Step s' l s'') :
  lts.IORestrictedStep s l s'' := by
  cases hstep_tau with | step_tau hstep_tau =>
  cases l with
  | yield => simp at hl
  | input => simp at hl
  | output => exact .step_output hstep_tau hstep
  | τ => exact .step_tau (.tail hstep_tau hstep)

theorem Lts.IORestrictedStep.eq_rhs
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s₁ s₂ s₂' : S} {l : Label Op V m n}
  (hstep : lts.IORestrictedStep s₁ l s₂)
  (heq : s₂ = s₂') :
  lts.IORestrictedStep s₁ l s₂' := by
  subst heq
  exact hstep

theorem Lts.IORestrictedStep.eq_lhs
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s₁ s₁' s₂ : S} {l : Label Op V m n}
  (hstep : lts.IORestrictedStep s₁ l s₂)
  (heq : s₁ = s₁') :
  lts.IORestrictedStep s₁' l s₂ := by
  subst heq
  exact hstep

theorem Lts.IORestrictedStep.to_tau_star
  {S} [Arity Op]
  {lts : Lts S (Label Op V m n)}
  {s₁ s₂ : S}
  (hstep : lts.IORestrictedStep s₁ .τ s₂) :
  lts.TauStar .τ s₁ s₂ := by
  cases hstep
  assumption

abbrev IORestrictedSimulation
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.Simulation sem₁.lts sem₂.lts.IORestrictedStep R sem₁.init sem₂.init

abbrev IORestrictedSimilaritySt
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n)
  (R : sem₁.S → sem₂.S → Prop) : Prop
  := Lts.SimilaritySt R sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init

abbrev IORestrictedSimilarity
  [Arity Op]
  (sem₁ sem₂ : Semantics Op V m n) : Prop
  := Lts.Similarity sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init

-- notation sem₁ " ≲ᵣ" "[" R "] " sem₂ => IORestrictedSimulation sem₁ sem₂ R
notation sem₁ " ≲ᵣ" "[" R "] " sem₂ => IORestrictedSimilaritySt sem₁ sem₂ R
infix:50 " ≲ᵣ " => IORestrictedSimilarity

@[refl]
theorem IORestrictedSimilarity.refl
  [Arity Op]
  (sem : Semantics Op V m n) :
  sem ≲ᵣ sem :=
  Lts.Similarity.refl_single .single

private theorem IORestrictedSimilaritySt.alt_helper
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {s₁ s₁' : sem₁.S} {s₂ : sem₂.S}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : Lts.SimilaritySt R sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init)
  (hR : hsim.Sim s₁ s₂)
  (hstep_tau : sem₁.lts.TauStar .τ s₁ s₁') :
  ∃ s₂', sem₂.lts.TauStar .τ s₂ s₂' ∧ hsim.Sim s₁' s₂' := by
  induction hstep_tau with
  | refl =>
    exists s₂
    constructor
    · exact .refl
    · exact hR
  | tail pref tail ih =>
    rename_i s₁'' s₁'
    have ⟨s₂'', hstep_s₂, hR₂''⟩ := ih
    have ⟨s₂', hstep_s₂', hR'⟩ := hsim.sim_step _ _ _ _ hR₂'' tail
    exists s₂'
    constructor
    · exact .trans hstep_s₂ hstep_s₂'.to_tau_star
    · exact hR'

theorem IORestrictedSimilaritySt.alt
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : Lts.SimilaritySt R sem₁.lts sem₂.lts.IORestrictedStep sem₁.init sem₂.init) :
  Lts.SimilaritySt R sem₁.lts.IORestrictedStep sem₂.lts.IORestrictedStep sem₁.init sem₂.init
  := by
  apply Lts.SimilaritySt.intro hsim.Sim
  · constructor
    · exact hsim.sim_init
    · intros s₁ s₂ l s₁' hR hstep
      cases hstep with
      | step_yield hstep' =>
        have ⟨s₂', hsim'⟩ := hsim.sim_step _ _ _ _ hR hstep'
        exists s₂'
      | step_input hstep₁ hstep₂ =>
        have ⟨s₂₁, hstep_s₂₁, hsim₁⟩ := hsim.sim_step _ _ _ _ hR hstep₁
        have ⟨s₂', hstep_s₂₂, hsim'⟩ := alt_helper hsim hsim₁ hstep₂
        exists s₂'
        constructor
        · cases hstep_s₂₁ with | step_input h₁ h₂ =>
          exact .step_input h₁ (.trans h₂ hstep_s₂₂)
        · exact hsim'
      | step_output hstep₁ hstep₂ =>
        have ⟨s₂₁, hstep_s₂₁, hsim₁⟩ := alt_helper hsim hR hstep₁
        have ⟨s₂', hstep_s₂₂, hsim'⟩ := hsim.sim_step _ _ _ _ hsim₁ hstep₂
        exists s₂'
        constructor
        · cases hstep_s₂₂ with | step_output h₁ h₂ =>
          exact .step_output (.trans hstep_s₂₁ h₁) h₂
        · exact hsim'
      | step_tau hstep' =>
        have ⟨s₂', hstep_s₂, hsim'⟩ := alt_helper hsim hR hstep'
        exists s₂'
        constructor
        · exact .step_tau hstep_s₂
        · exact hsim'
  · apply hsim.sim_prop

theorem IORestrictedSimilarity.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ᵣ sem₂) (h₂ : sem₂ ≲ᵣ sem₃) :
  sem₁ ≲ᵣ sem₃ := Lts.Similarity.trans h₁ (IORestrictedSimilaritySt.alt h₂)

theorem IORestrictedSimilaritySt.trans
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  {R₁ : sem₁.S → sem₂.S → Prop}
  {R₂ : sem₂.S → sem₃.S → Prop}
  (h₁ : sem₁ ≲ᵣ[R₁] sem₂) (h₂ : sem₂ ≲ᵣ[R₂] sem₃) :
  sem₁ ≲ᵣ[RelComp R₁ R₂] sem₃ :=
    Lts.SimilaritySt.trans h₁ (IORestrictedSimilaritySt.alt h₂)

theorem IORestrictedSimilarity.to_weak_sim
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (hsim : sem₁ ≲ᵣ sem₂) : sem₁ ≲ sem₂ := by
  apply Lts.Similarity.intro hsim.Sim
  constructor
  · exact hsim.sim_init
  · intros s₁ s₂ l s₁' hR hstep
    have ⟨s₂', hstep', hR'⟩ := hsim.sim_step _ _ _ _ hR hstep
    exists s₂'
    constructor
    · cases hstep' with
      | step_yield hstep' => exact .single hstep'
      | step_input hstep' htau => exact .step .refl hstep' htau
      | step_output htau hstep' => exact .step htau hstep' .refl
      | step_tau htau => exact .from_tau_star htau
    · exact hR'

theorem StrongSimilaritySt.to_restricted_sim
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : sem₁ ≲ₛ[R] sem₂) : sem₁ ≲ᵣ[R] sem₂ := by
  apply Lts.SimilaritySt.intro hsim.Sim
  · constructor
    · exact hsim.sim_init
    · intros s₁ s₂ l s₁' hR hstep
      have ⟨s₂', hstep', hR'⟩ := hsim.sim_step _ _ _ _ hR hstep
      exists s₂'
      constructor
      · exact Lts.IORestrictedStep.single hstep'
      · exact hR'
  · apply hsim.sim_prop

theorem IORestrictedSimilaritySt.map_tau_star
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  {R : sem₁.S → sem₂.S → Prop}
  (hsim : sem₁ ≲ᵣ[R] sem₂)
  {s₁ s₁' : sem₁.S}
  {s₂ : sem₂.S}
  (h : hsim.Sim s₁ s₂)
  (htau : sem₁.lts.TauStar .τ s₁ s₁') :
    ∃ s₂', sem₂.lts.TauStar .τ s₂ s₂' ∧ hsim.Sim s₁' s₂'
  := by
  induction htau with
  | refl => exact ⟨_, .refl, h⟩
  | tail pref tail ih =>
    have ⟨_, pref', h'⟩ := ih
    have ⟨_, tail', h''⟩ := hsim.sim_step _ _ _ _ h' tail
    cases tail' with | step_tau tail'' =>
    exact ⟨_, pref'.trans tail'', h''⟩

instance [Arity Op] : IsRefl (Semantics Op V m n) IORestrictedSimilarity where
  refl := .refl

instance [Arity Op] : IsTrans (Semantics Op V m n) IORestrictedSimilarity where
  trans _ _ _ := .trans

/-- Used for restricting some simulation relations. -/
def PreservesInit
  [Arity Op]
  {sem₁ sem₂ : Semantics Op V m n}
  (s₁ : sem₁.S) (s₂ : sem₂.S) : Prop :=
  s₁ = sem₁.init → s₂ = sem₂.init

theorem IORestrictedSimilaritySt.trans_preserves_init
  {Op : Type u} {V : Type v}
  [Arity Op]
  {sem₁ sem₂ sem₃ : Semantics Op V m n}
  (h₁ : sem₁ ≲ᵣ[PreservesInit] sem₂) (h₂ : sem₂ ≲ᵣ[PreservesInit] sem₃) :
  sem₁ ≲ᵣ[PreservesInit] sem₃ := by
  have := Lts.SimilaritySt.trans h₁ (IORestrictedSimilaritySt.alt h₂)
  apply Lts.SimilaritySt.weaken _ this
  simp [RelComp, PreservesInit]
  grind only

end Wavelet.Semantics
