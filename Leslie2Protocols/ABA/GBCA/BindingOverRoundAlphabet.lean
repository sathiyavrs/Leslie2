/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.SpecificationOverRoundAlphabet
import Leslie2Protocols.ABA.GBCA.SpecificationSafety

/-!
# Binding of the specification over the round's alphabet

The alphabet of a graded-agreement round is the family alphabet
`Composition.ExtendedLabel n M`, over the type `M` of the messages the round exchanges. The round's
returns and announcements are the shared labels `Sum.inl (Label.retG r id out)` and
`Sum.inl (Label.boundG r b)`, and `BindingTraceExtended` reads the three conjuncts of
`GBCA.BindingTrace` on them: two announcements of round `r` name the same bit, a return of a value
and an announcement name the same bit, and two returns of values return the same bit (D29).

`specificationOverRoundAlphabet_binding` proves binding of `specificationOverRoundAlphabet`, the
specification read over that alphabet. An execution of that system has the states of a `specInst`
execution: a transition on a label `specificationLabelMap` names is a `GBCA.Step` transition at
that label, and a transition on a label it leaves unnamed is a self-loop. The exclusion set
therefore only grows along such an execution and holds at most one bit. An announcement of `β`
fires under `(!β) ∈ excluded` (`step_boundG_cases`) and a return of `v` under `(!v) ∈ excluded`
(`retG_value_guards`), which is the binding argument of `ABA/GBCA/SpecificationSafety.lean` (D19,
D29).

Binding is a property of the labels, so every inclusion into `specificationOverRoundAlphabet`
carries it. The three compositions of the two-gather round take it along theirs in
`ABA/GBCA/AFW/Binding.lean`.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

open Implementation Composition

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {P : Parameters} {M : Type} [DecidableEq M] {r : ℕ}

/-! ### Binding over the family alphabet -/

/-- **Binding (trace form) over the family alphabet.** `GBCA.BindingTrace` read on the shared
labels of the round's alphabet: two round-`r` announcements name the same bit, a round-`r` return
of a value and a round-`r` announcement name the same bit, and two round-`r` returns of values
return the same bit (D29). -/
def BindingTraceExtended (P : Parameters) (r : ℕ)
    (t : Seq (Composition.ExtendedLabel P.n M)) : Prop :=
  (∀ β₁ β₂ : Bool, (Sum.inl (Label.boundG r β₁) : Composition.ExtendedLabel P.n M) ∈ t →
    (Sum.inl (Label.boundG r β₂) : Composition.ExtendedLabel P.n M) ∈ t → β₁ = β₂) ∧
  (∀ (id : Fin P.n) (o : GBCAOutput) (v β : Bool),
    (Sum.inl (Label.retG r id o) : Composition.ExtendedLabel P.n M) ∈ t → outValue o = some v →
      (Sum.inl (Label.boundG r β) : Composition.ExtendedLabel P.n M) ∈ t → v = β) ∧
  (∀ (id₁ id₂ : Fin P.n) (o₁ o₂ : GBCAOutput) (v₁ v₂ : Bool),
    (Sum.inl (Label.retG r id₁ o₁) : Composition.ExtendedLabel P.n M) ∈ t →
      (Sum.inl (Label.retG r id₂ o₂) : Composition.ExtendedLabel P.n M) ∈ t →
      outValue o₁ = some v₁ → outValue o₂ = some v₂ → v₁ = v₂)

/-! ### Transitions of the lifted specification -/

/-- A transition of the lifted specification on a label `specificationLabelMap` names is a
transition of the specification at that label. -/
theorem specificationOverRoundAlphabet_step_some {s : SpecState P.n}
    {l : Composition.ExtendedLabel P.n M} {l₀ : Label P.n} {μ : PMF (SpecState P.n)}
    (hpull : specificationLabelMap P.n l = some l₀)
    (h : (specificationOverRoundAlphabet P M r).step s l μ) : Step P r s l₀ μ :=
  (System.mapIdle_step_some (sys := specInst P r) hpull μ).mp h

/-- A transition of the lifted specification is a transition of the
specification at the label `specificationLabelMap` names, or a self-loop. -/
theorem specificationOverRoundAlphabet_step_cases {s s' : SpecState P.n}
    {l : Composition.ExtendedLabel P.n M} {μ : PMF (SpecState P.n)}
    (h : (specificationOverRoundAlphabet P M r).step s l μ) (hs' : s' ∈ μ.support) :
    (∃ l₀, specificationLabelMap P.n l = some l₀ ∧ Step P r s l₀ μ) ∨ s' = s := by
  rcases (System.mapIdle_step (specificationLabelMap P.n) (specInst P r) s l μ).mp h with
    ⟨l₀, hpull, hstep⟩ | ⟨-, rfl⟩
  · exact Or.inl ⟨l₀, hpull, hstep⟩
  · exact Or.inr ((PMF.mem_support_pure_iff _ _).mp hs')

/-! ### The exclusion set along an execution of the lifted specification -/

/-- **The exclusion set never shrinks**, along a transition of the lifted
specification: a named label takes a specification transition, and an unnamed one
leaves the state alone. -/
theorem specificationOverRoundAlphabet_excluded_mono {s s' : SpecState P.n}
    {l : Composition.ExtendedLabel P.n M} {μ : PMF (SpecState P.n)}
    (h : (specificationOverRoundAlphabet P M r).step s l μ) (hs' : s' ∈ μ.support) :
    s.excluded ⊆ s'.excluded := by
  rcases specificationOverRoundAlphabet_step_cases h hs' with ⟨_, -, hstep⟩ | rfl
  · exact Step.excluded_mono hstep hs'
  · exact Finset.Subset.refl _

/-- **An excluded bit stays excluded along a run** of the lifted
specification. -/
theorem specificationOverRoundAlphabet_excluded_mem_stable
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n M)}
    (he : is_exec e (specificationOverRoundAlphabet P M r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b : Bool} (hst₁ : e.stateAt k₁ = some s₁)
    (hst₂ : e.stateAt k₂ = some s₂) (hb : b ∈ s₁.excluded) : b ∈ s₂.excluded :=
  is_exec_stable (sys := specificationOverRoundAlphabet P M r) (fun s => b ∈ s.excluded)
    (fun _ _ _ _ hmem hstep hs' => specificationOverRoundAlphabet_excluded_mono hstep hs' hmem)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hb

/-- **One exclude per instance**, at every state of an execution of the lifted
specification. -/
theorem specificationOverRoundAlphabet_excluded_card_le_one
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n M)}
    (he : is_exec e (specificationOverRoundAlphabet P M r)) {k : ℕ} {s : SpecState P.n}
    (hst : e.stateAt k = some s) : s.excluded.card ≤ 1 :=
  is_exec_stable (sys := specificationOverRoundAlphabet P M r) (fun s => s.excluded.card ≤ 1)
    (fun _ _ _ _ hcard hstep hs' => by
      rcases specificationOverRoundAlphabet_step_cases hstep hs' with ⟨_, -, htransition⟩ | rfl
      · exact Step.excluded_card_le_one htransition hs' hcard
      · exact hcard)
    he 0 k e.init s (Nat.zero_le k) rfl hst
    (by rw [← he.2]; simp [SpecState.initial])

/-- Two bits excluded at two states of one execution of the lifted specification are equal: the
earlier exclusion stands at the later state, which excludes at most one bit. -/
private theorem specificationOverRoundAlphabet_excluded_eq_of_mem_run
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n M)}
    (he : is_exec e (specificationOverRoundAlphabet P M r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {b₁ b₂ : Bool} (hst₁ : e.stateAt k₁ = some s₁)
    (hst₂ : e.stateAt k₂ = some s₂) (h₁ : b₁ ∈ s₁.excluded) (h₂ : b₂ ∈ s₂.excluded) :
    b₁ = b₂ := by
  rcases le_total k₁ k₂ with hk | hk
  · exact Finset.card_le_one.mp (specificationOverRoundAlphabet_excluded_card_le_one he hst₂) _
      (specificationOverRoundAlphabet_excluded_mem_stable he hk hst₁ hst₂ h₁) _ h₂
  · exact Finset.card_le_one.mp (specificationOverRoundAlphabet_excluded_card_le_one he hst₁) _
      h₁ _ (specificationOverRoundAlphabet_excluded_mem_stable he hk hst₂ hst₁ h₂)

/-! ### The announcements and the returns of a run -/

/-- **One bound bit per round**, along an execution of the lifted specification. Each
announcement of `β` fires under `(!β) ∈ excluded`, the exclusion set only grows, and no state of
an execution excludes two bits. -/
theorem specificationOverRoundAlphabet_boundG_agree
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n M)}
    (he : is_exec e (specificationOverRoundAlphabet P M r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {β₁ β₂ : Bool} {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.boundG r β₁) μ₁) (hstep₂ : Step P r s₂ (.boundG r β₂) μ₂) :
    β₁ = β₂ := by
  have h := specificationOverRoundAlphabet_excluded_eq_of_mem_run he hst₁ hst₂
    (step_boundG_cases hstep₁).1 (step_boundG_cases hstep₂).1
  revert h
  cases β₁ <;> cases β₂ <;> simp

/-- **A return of a value and an announcement name the same bit**, along an execution of the
lifted specification. The return of `v` fires under `(!v) ∈ excluded`, the announcement of `β`
under `(!β) ∈ excluded`, and the states of one execution exclude at most one bit among them. -/
theorem specificationOverRoundAlphabet_retG_value_eq_bound
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n M)}
    (he : is_exec e (specificationOverRoundAlphabet P M r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {id : Fin P.n} {o : GBCAOutput} {v β : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hstep₁ : Step P r s₁ (.retG r id o) μ₁)
    (ho : outValue o = some v)
    (hst₂ : e.stateAt k₂ = some s₂) (hstep₂ : Step P r s₂ (.boundG r β) μ₂) : v = β := by
  have h := specificationOverRoundAlphabet_excluded_eq_of_mem_run he hst₁ hst₂
    (retG_value_guards hstep₁ ho).2 (step_boundG_cases hstep₂).1
  revert h
  cases v <;> cases β <;> simp

/-- **Two returns of values return the same bit**, along an execution of the lifted
specification. Each return of `v` fires under `(!v) ∈ excluded`, and the states of one execution
exclude at most one bit among them. -/
theorem specificationOverRoundAlphabet_retG_value_agree
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n M)}
    (he : is_exec e (specificationOverRoundAlphabet P M r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput} {v₁ v₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁) μ₁) (hstep₂ : Step P r s₂ (.retG r id₂ o₂) μ₂)
    (ho₁ : outValue o₁ = some v₁) (ho₂ : outValue o₂ = some v₂) : v₁ = v₂ := by
  have h := specificationOverRoundAlphabet_excluded_eq_of_mem_run he hst₁ hst₂
    (retG_value_guards hstep₁ ho₁).2 (retG_value_guards hstep₂ ho₂).2
  revert h
  cases v₁ <;> cases v₂ <;> simp

/-! ### Binding of the lifted specification -/

/-- **Binding of the specification read over the family alphabet**: every trace
in the support of every achievable trace distribution of `specificationOverRoundAlphabet
P M r` satisfies `BindingTraceExtended`. Every round-`r` announcement and return of the trace is a
transition of the specification at a state of one execution, and the three statements above
apply. -/
theorem specificationOverRoundAlphabet_binding (P : Parameters) (M : Type) [DecidableEq M]
    (r : ℕ) :
    ∀ D ∈ achievableTraceDists (specificationOverRoundAlphabet P M r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ := exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  have hevent : ∀ l : Label P.n, (Sum.inl l : Composition.ExtendedLabel P.n M) ∈ t →
      ∃ (k : ℕ) (s : SpecState P.n) (μ : PMF (SpecState P.n)),
        e.stateAt k = some s ∧ Step P r s l μ := by
    intro l hl
    obtain ⟨-, k, s', hg⟩ := (h_char _).mp hl
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    exact ⟨k, s, μ, hst,
      specificationOverRoundAlphabet_step_some (specificationLabelMap_inl l) hstep⟩
  refine ⟨?_, ?_, ?_⟩
  · intro β₁ β₂ h₁ h₂
    obtain ⟨k₁, s₁, μ₁, hst₁, hstep₁⟩ := hevent _ h₁
    obtain ⟨k₂, s₂, μ₂, hst₂, hstep₂⟩ := hevent _ h₂
    exact specificationOverRoundAlphabet_boundG_agree h_exec hst₁ hst₂ hstep₁ hstep₂
  · intro id o v β h₁ ho h₂
    obtain ⟨k₁, s₁, μ₁, hst₁, hstep₁⟩ := hevent _ h₁
    obtain ⟨k₂, s₂, μ₂, hst₂, hstep₂⟩ := hevent _ h₂
    exact specificationOverRoundAlphabet_retG_value_eq_bound h_exec hst₁ hstep₁ ho hst₂ hstep₂
  · intro id₁ id₂ o₁ o₂ v₁ v₂ h₁ h₂ ho₁ ho₂
    obtain ⟨k₁, s₁, μ₁, hst₁, hstep₁⟩ := hevent _ h₁
    obtain ⟨k₂, s₂, μ₂, hst₂, hstep₂⟩ := hevent _ h₂
    exact specificationOverRoundAlphabet_retG_value_agree h_exec hst₁ hst₂ hstep₁ hstep₂ ho₁ ho₂

end GBCA
end ABA
end PLTS
