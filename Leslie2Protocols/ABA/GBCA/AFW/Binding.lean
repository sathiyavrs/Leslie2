/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitutions
import Leslie2Protocols.ABA.GBCA.SpecificationSafety
import Leslie2.Results

/-!
# Binding of the round over the family alphabet

The round speaks the family alphabet `Composition.ExtendedLabel n`, in which a round-`r` return
appears twice: as `Sum.inl (Label.retG r id out bnd)` and as the Byzantine row
`Sum.inr (.byzantineRetG r id out bnd)`. `GBCA.ByABDY.gbcaLabelMap` sends both to the same
specification return, and `GBCA.BindingTraceExtended` states binding at every
label of a trace that `GBCA.ByABDY.gbcaLabelMap` sends to a round-`r` return, so both forms
count.

`GBCA.specificationOverRoundAlphabet_binding` proves binding of the specification read over
that alphabet, `GBCA.ByABDY.specificationOverRoundAlphabet`. An execution of the lifted system has
the states of a `GBCA.specInst` execution: a transition on a label `GBCA.ByABDY.gbcaLabelMap`
names is a `GBCA.Step` transition at that label, and a transition on a label it
leaves unnamed is a self-loop. The exclusion set therefore only grows along
such an execution and holds at most one bit, which is what the binding
argument of `ABA/GBCA/SpecificationSafety.lean` runs on.

The three tiers of the round reach the lifted specification through
`GBCA.ByAFW.refinesSpecification` and the two substitutions of `GBCA/AFW/GatherSubstitutions.lean`.
Each inherits binding along its inclusion: `GBCA.roundOverGatherSpecifications_binding`,
`GBCA.roundOverBroadcastSpecification_binding` and `GBCA.roundOverBracha_binding`.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

open Implementation Composition GBCA.ByAFW

variable {P : Parameters} {r : ℕ}

/-! ### Binding over the family alphabet -/

/-- **Binding (trace form) over the family alphabet.** The round is bound to
one bit on the trace: all labels the trace carries that name a round-`r` return
announce the same bit, and every one of them that hands out a value hands out
that bit. A return is named by `Sum.inl (Label.retG r id out bnd)` and by the
Byzantine row `Sum.inr (.byzantineRetG r id out bnd)` alike, `GBCA.ByABDY.gbcaLabelMap` sending
both to the specification's return. -/
def BindingTraceExtended (P : Parameters) (r : ℕ) (t : Seq (Composition.ExtendedLabel P.n)) : Prop
  :=
  (∀ (l₁ l₂ : Composition.ExtendedLabel P.n) (id₁ id₂ : Fin P.n) (o₁ o₂ : GBCAOutput)
    (β₁ β₂ : Bool),
      l₁ ∈ t → l₂ ∈ t → GBCA.ByABDY.gbcaLabelMap P.n l₁ = some (Label.retG r id₁ o₁ β₁) →
      GBCA.ByABDY.gbcaLabelMap P.n l₂ = some (Label.retG r id₂ o₂ β₂) → β₁ = β₂) ∧
    ∀ (l : Composition.ExtendedLabel P.n) (id : Fin P.n) (o : GBCAOutput) (β v : Bool),
      l ∈ t → GBCA.ByABDY.gbcaLabelMap P.n l = some (Label.retG r id o β) →
      outValue o = some v → v = β

/-! ### Transitions of the lifted specification -/

/-- A transition of the lifted specification on a label `GBCA.ByABDY.gbcaLabelMap` names is a
transition of the specification at that label. -/
theorem specificationOverRoundAlphabet_step_some {s : SpecState P.n}
    {l : Composition.ExtendedLabel P.n} {l₀ : Label P.n} {μ : PMF (SpecState P.n)}
    (hpull : GBCA.ByABDY.gbcaLabelMap P.n l = some l₀)
    (h : (GBCA.ByABDY.specificationOverRoundAlphabet P r).step s l μ) : Step P r s l₀ μ :=
  (System.mapIdle_step_some (sys := specInst P r) hpull μ).mp h

/-- A transition of the lifted specification is a transition of the
specification at the label `GBCA.ByABDY.gbcaLabelMap` names, or a self-loop. -/
theorem specificationOverRoundAlphabet_step_cases {s s' : SpecState P.n}
    {l : Composition.ExtendedLabel P.n} {μ : PMF (SpecState P.n)}
    (h : (GBCA.ByABDY.specificationOverRoundAlphabet P r).step s l μ) (hs' : s' ∈ μ.support) :
    (∃ l₀, GBCA.ByABDY.gbcaLabelMap P.n l = some l₀ ∧ Step P r s l₀ μ) ∨ s' = s := by
  rcases (System.mapIdle_step (GBCA.ByABDY.gbcaLabelMap P.n) (specInst P r) s l μ).mp h with
    ⟨l₀, hpull, hstep⟩ | ⟨-, rfl⟩
  · exact Or.inl ⟨l₀, hpull, hstep⟩
  · exact Or.inr ((PMF.mem_support_pure_iff _ _).mp hs')

/-! ### The exclusion set along an execution of the lifted specification -/

/-- **The exclusion set never shrinks**, along a transition of the lifted
specification: a named label takes a specification row, and an unnamed one
leaves the state alone. -/
theorem specificationOverRoundAlphabet_excluded_mono {s s' : SpecState P.n}
    {l : Composition.ExtendedLabel P.n} {μ : PMF (SpecState P.n)}
    (h : (GBCA.ByABDY.specificationOverRoundAlphabet P r).step s l μ) (hs' : s' ∈ μ.support) :
    s.excluded ⊆ s'.excluded := by
  rcases specificationOverRoundAlphabet_step_cases h hs' with ⟨_, -, hstep⟩ | rfl
  · exact Step.excluded_mono hstep hs'
  · exact Finset.Subset.refl _

/-- **An excluded bit stays excluded along a run** of the lifted
specification. -/
theorem specificationOverRoundAlphabet_excluded_mem_stable
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n)}
    (he : is_exec e (GBCA.ByABDY.specificationOverRoundAlphabet P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b : Bool} (hst₁ : e.stateAt k₁ = some s₁)
    (hst₂ : e.stateAt k₂ = some s₂) (hb : b ∈ s₁.excluded) : b ∈ s₂.excluded :=
  is_exec_stable (sys := GBCA.ByABDY.specificationOverRoundAlphabet P r) (fun s => b ∈ s.excluded)
    (fun _ _ _ _ hmem hstep hs' => specificationOverRoundAlphabet_excluded_mono hstep hs' hmem)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hb

/-- **One exclude per instance**, at every state of an execution of the lifted
specification. -/
theorem specificationOverRoundAlphabet_excluded_card_le_one
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n)}
    (he : is_exec e (GBCA.ByABDY.specificationOverRoundAlphabet P r)) {k : ℕ} {s : SpecState P.n}
    (hst : e.stateAt k = some s) : s.excluded.card ≤ 1 :=
  is_exec_stable (sys := GBCA.ByABDY.specificationOverRoundAlphabet P r) (fun s => s.excluded.card ≤
    1)
    (fun _ _ _ _ hcard hstep hs' => by
      rcases specificationOverRoundAlphabet_step_cases hstep hs' with ⟨_, -, hrow⟩ | rfl
      · exact Step.excluded_card_le_one hrow hs' hcard
      · exact hcard)
    he 0 k e.init s (Nat.zero_le k) rfl hst
    (by rw [← he.2]; simp [SpecState.initial])

/-! ### The two returns of a run -/

/-- Two bits excluded at one state of an execution of the lifted specification
are equal: the exclusion set holds at most one bit. -/
private theorem specificationOverRoundAlphabet_excluded_eq_of_mem
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n)}
    (he : is_exec e (GBCA.ByABDY.specificationOverRoundAlphabet P r)) {k : ℕ} {s : SpecState P.n}
    {b₁ b₂ : Bool} (hst : e.stateAt k = some s) (h₁ : b₁ ∈ s.excluded) (h₂ : b₂ ∈ s.excluded) :
    b₁ = b₂ :=
  Finset.card_le_one.mp (specificationOverRoundAlphabet_excluded_card_le_one he hst) _ h₁ _ h₂

/-- Two returns of one run of the lifted specification announce the same bit
(`k₁ ≤ k₂` case). -/
private theorem specificationOverRoundAlphabet_retG_bound_agree_le
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n)}
    (he : is_exec e (GBCA.ByABDY.specificationOverRoundAlphabet P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput} {β₁ β₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)} (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁) (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂) :
    β₁ = β₂ := by
  have hcarry : (!β₁) ∈ s₂.excluded :=
    specificationOverRoundAlphabet_excluded_mem_stable he hk hst₁ hst₂ (retG_bound_guard hstep₁)
  have h := specificationOverRoundAlphabet_excluded_eq_of_mem he hst₂ hcarry (retG_bound_guard
    hstep₂)
  revert h
  cases β₁ <;> cases β₂ <;> simp

/-- **One bound bit per round**, along an execution of the lifted
specification. Each return fires under `(!β) ∈ excluded`, the exclusion set
only grows, and no state of an execution excludes two bits. -/
theorem specificationOverRoundAlphabet_retG_bound_agree
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n)}
    (he : is_exec e (GBCA.ByABDY.specificationOverRoundAlphabet P r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput} {β₁ β₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)} (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁) (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂) :
    β₁ = β₂ := by
  rcases le_total k₁ k₂ with h | h
  · exact specificationOverRoundAlphabet_retG_bound_agree_le he h hst₁ hst₂ hstep₁ hstep₂
  · exact (specificationOverRoundAlphabet_retG_bound_agree_le he h hst₂ hst₁ hstep₂ hstep₁).symm

/-- **A value-bearing return announces the bit it hands out**, along an
execution of the lifted specification. The value guard excludes `!v`, the bound
guard excludes `!β`, and a state of an execution excludes at most one bit. -/
theorem specificationOverRoundAlphabet_retG_value_eq_bound
    {e : AlterSeq (SpecState P.n) (Composition.ExtendedLabel P.n)}
    (he : is_exec e (GBCA.ByABDY.specificationOverRoundAlphabet P r)) {k : ℕ} {s : SpecState P.n}
    {id : Fin P.n} {o : GBCAOutput} {v β : Bool} {μ : PMF (SpecState P.n)}
    (hst : e.stateAt k = some s) (hstep : Step P r s (.retG r id o β) μ) (ho : outValue o = some v)
    : v = β := by
  have h := specificationOverRoundAlphabet_excluded_eq_of_mem he hst (retG_value_guards hstep ho).2
    (retG_bound_guard hstep)
  revert h
  cases v <;> cases β <;> simp

/-! ### Binding of the lifted specification -/

/-- **Binding of the specification read over the family alphabet**: every trace
in the support of every achievable trace distribution of `GBCA.ByABDY.specificationOverRoundAlphabet
P r` satisfies `BindingTraceExtended`. -/
theorem specificationOverRoundAlphabet_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (GBCA.ByABDY.specificationOverRoundAlphabet P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ := exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  have hret : ∀ (l : Composition.ExtendedLabel P.n) (id : Fin P.n) (o : GBCAOutput) (β : Bool),
      l ∈ t → GBCA.ByABDY.gbcaLabelMap P.n l = some (Label.retG r id o β) →
      ∃ (k : ℕ) (s : SpecState P.n) (μ : PMF (SpecState P.n)),
        e.stateAt k = some s ∧ Step P r s (Label.retG r id o β) μ := by
    intro l id o β hl hpull
    obtain ⟨-, k, s', hg⟩ := (h_char l).mp hl
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    exact ⟨k, s, μ, hst, specificationOverRoundAlphabet_step_some hpull hstep⟩
  constructor
  · intro l₁ l₂ id₁ id₂ o₁ o₂ β₁ β₂ h₁ h₂ hp₁ hp₂
    obtain ⟨k₁, s₁, μ₁, hst₁, hstep₁⟩ := hret l₁ id₁ o₁ β₁ h₁ hp₁
    obtain ⟨k₂, s₂, μ₂, hst₂, hstep₂⟩ := hret l₂ id₂ o₂ β₂ h₂ hp₂
    exact specificationOverRoundAlphabet_retG_bound_agree h_exec hst₁ hst₂ hstep₁ hstep₂
  · intro l id o β v h_mem hpull ho
    obtain ⟨k, s, μ, hst, hstep⟩ := hret l id o β h_mem hpull
    exact specificationOverRoundAlphabet_retG_value_eq_bound h_exec hst hstep ho

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather specifications in
the specification read over the round's interface, the soundness of
`refinesSpecification`. -/
theorem roundOverGatherSpecifications_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverGatherSpecifications P r) ⊆ achievableTraceDists
      (GBCA.ByABDY.specificationOverRoundAlphabet P r) :=
  (ForwardSimulation.toProbabilistic (roundOverGatherSpecifications_isLTS P r)
    (GBCA.ByABDY.specificationOverRoundAlphabet_isLTS P r)
    (specificationRelation_init P r) (refinesSpecification P r)).achievableTraceDists_subset

/-- **The round over the gather instances over Bracha's broadcast refines the
specification**: the two substitutions and the counting simulation, each taken
probabilistically, joined by Result 2
(`ProbabilisticForwardSimulation.trans`). -/
theorem roundOverBracha_refinesSpecification (P : Parameters) (r : ℕ) :
    ProbabilisticForwardSimulation (roundOverBracha P r) (GBCA.ByABDY.specificationOverRoundAlphabet
      P r)
      (compRel (diracRel (BroadcastSubstitutionRelation P))
        (compRel (diracRel (GatherSubstitutionRelation P)) (diracRel (SpecificationRelation P)))) :=
  (ForwardSimulation.toProbabilistic (roundOverBracha_isLTS P r)
    (roundOverBroadcastSpecification_isLTS P r)
      (broadcastSubstitutionRelation_init P r) (broadcastSubstitution P r)).trans
    ((ForwardSimulation.toProbabilistic (roundOverBroadcastSpecification_isLTS P r)
      (roundOverGatherSpecifications_isLTS P r)
        (gatherSubstitutionRelation_init P r) (gatherSubstitution P r)).trans
      (ForwardSimulation.toProbabilistic (roundOverGatherSpecifications_isLTS P r)
        (GBCA.ByABDY.specificationOverRoundAlphabet_isLTS P r)
        (specificationRelation_init P r) (refinesSpecification P r)))

/-- The soundness inclusion of the round: every trace distribution
achievable by the round over the gather instances over Bracha's broadcast is
achievable by the lifted specification. -/
theorem roundOverBracha_specificationTraces (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBracha P r) ⊆ achievableTraceDists
      (GBCA.ByABDY.specificationOverRoundAlphabet P r) :=
  (roundOverBracha_refinesSpecification P r).achievableTraceDists_subset

/-- The soundness inclusion of the gather substitution above the counting
simulation: every trace distribution achievable by the round over the gather
instances over the broadcast specification is achievable by the lifted
specification. -/
theorem roundOverBroadcastSpecification_specificationTraces (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBroadcastSpecification P r) ⊆ achievableTraceDists
      (GBCA.ByABDY.specificationOverRoundAlphabet P r) :=
  Set.Subset.trans (roundOverBroadcastSpecification_refines P r)
    (roundOverGatherSpecifications_refines P r)

/-! ### Binding of the three tiers -/

/-- **Binding of the round over the gather specifications, on a trace.** Every
positive-probability trace of the round is bound to one bit: all its round-`r`
returns announce that bit, and every one of them that hands out a value hands
out it. Binding is a property of the labels (`BindingTraceExtended`), so
`roundOverGatherSpecifications_refines` carries it from
`specificationOverRoundAlphabet_binding`. -/
theorem roundOverGatherSpecifications_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (roundOverGatherSpecifications P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t :=
  safety_transfer (roundOverGatherSpecifications_refines P r)
    (specificationOverRoundAlphabet_binding P r)

/-- **Binding of the round over the gather instances over the broadcast
specification, on a trace**, along the inclusion
`roundOverBroadcastSpecification_specificationTraces`. -/
theorem roundOverBroadcastSpecification_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (roundOverBroadcastSpecification P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t :=
  safety_transfer (roundOverBroadcastSpecification_specificationTraces P r)
    (specificationOverRoundAlphabet_binding P r)

/-- **Binding of the round over the gather instances over Bracha's broadcast,
on a trace**, along the three-tier inclusion `roundOverBracha_specificationTraces`. -/
theorem roundOverBracha_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (roundOverBracha P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t :=
  safety_transfer (roundOverBracha_specificationTraces P r) (specificationOverRoundAlphabet_binding
    P r)

/-! ### Mechanical axiom check

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.GBCA.specificationOverRoundAlphabet_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationOverRoundAlphabet_binding

/-- info: 'PLTS.ABA.GBCA.roundOverBracha_refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_refinesSpecification

/-- info: 'PLTS.ABA.GBCA.roundOverBracha_specificationTraces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_specificationTraces

/-- info: 'PLTS.ABA.GBCA.roundOverGatherSpecifications_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverGatherSpecifications_binding

/-- info: 'PLTS.ABA.GBCA.roundOverBroadcastSpecification_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBroadcastSpecification_binding

/-- info: 'PLTS.ABA.GBCA.roundOverBracha_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_binding

end GBCA
end ABA
end PLTS
