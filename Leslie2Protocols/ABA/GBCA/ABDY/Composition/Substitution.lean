/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Composition.ProjectsOntoImplementation

/-!
# The round instance is replaced by the graded agreement specification

`instanceSubstitution` licenses replacing the round instance by the graded agreement specification.
It runs through the implementation instance of `GBCA/ABDY/Implementation.lean` in two steps. The
first is `composition_projects`, which is strong and functional. The second is the per-instance
refinement `GBCA.ByABDY.refinesSpecification` (`GBCA/ABDY/RefinesSpecification.lean`), used as it
stands: its answer is a weak run of the specification over the shared alphabet `Label n`, lifted to
the round instance's interface along a section of `gbcaLabelMap`, which is where a Byzantine
handshake row is answered by the specification's own call or return row (D11).
`substitutionRelation` is the relation the simulation runs on, the implementation's
`GBCA.ByABDY.specificationRelation`, which the shared state lets it be verbatim.

`specificationCorruptionAct` is the broadcast corruption act the lifted specification carries at the
extended alphabet. `instanceSubstitution_init` and `instanceSubstitution_failAct` are the two
premises `ForwardSimulation.family` asks of the round-indexed family: the relation holds at the
initial states, and it survives the broadcast corruption.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation Composition

/-! ### The round instance is refined by the graded agreement specification

The round instance's answer to a step is the implementation's answer, read through the per-instance
refinement (`GBCA.ByABDY.refinesSpecification`, `GBCA/ABDY/RefinesSpecification.lean`): the first
step is strong and functional, so nothing of that refinement is reproved here. The specification's
weak answer is finally lifted to the round instance's interface along a section of `gbcaLabelMap` —
which is where a Byzantine handshake row is answered by the specification's own call or return row
(D11). -/

/-- **The simulation relation of the round instance**: the relation
`GBCA.ByABDY.specificationRelation` of the implementation, which the shared state lets it be
verbatim. -/
def substitutionRelation (P : Parameters) (r : ℕ) (σ : GBCA.ByABDY.ImplementationState P.n)
    (s : GBCA.SpecState P.n) : Prop :=
  GBCA.ByABDY.specificationRelation P r σ s

/-- **The per-round instance simulation**: the round-`r` instance is forward
simulated by the round-`r` graded agreement specification, read over the
instance's interface. -/
theorem instanceSubstitution (P : Parameters) (r : ℕ) :
    ForwardSimulation (composition P r) (specificationOverRoundAlphabet P r)
    (substitutionRelation P r) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, himpl⟩ := composition_projects P r q₁ l μ hstep
  obtain ⟨s', hdis,
    hrel⟩ := (GBCA.ByABDY.refinesSpecification P r).step q₁ q₂ hR l₀ μ himpl q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨gbcaLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_specificationOverRoundAlphabet P r hweak⟩
  · refine Or.inr ⟨?_, weakLStep_specificationOverRoundAlphabet P r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : gbcaLabelMap P.n (Silent.τ : ExtendedLabel P.n) = some l₀ := by
      rw [← hl]; exact hpull
    rw [gbcaLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### What the family lift will need

The two premises of `ForwardSimulation.family` for the round-indexed family: the relation holds at
the initial states, and it survives the broadcast corruption. Both are the implementation instance's
own facts, which the shared state lets stand verbatim. -/

/-- The broadcast corruption act on a specification state, over the extended
alphabet: `GBCA.failAct` taken on the extended `fail` label. -/
def specificationCorruptionAct (P : Parameters) : ExtendedLabel P.n → GBCA.SpecState P.n →
  GBCA.SpecState P.n
  | Sum.inl (.fail k), s => s.corrupt P k
  | _, s => s

/-- The initial states of the instance and of its specification are
related. -/
theorem instanceSubstitution_init (P : Parameters) (r : ℕ) :
    substitutionRelation P r (composition P r).init (GBCA.specInst P r).init :=
  GBCA.ByABDY.specificationRelation_init P r

/-- **Broadcast compatibility**: corruption preserves the instance relation.
The network state's corrupted set is the implementation's, so the two guards
`k ∉ F ∧ |F| < f` agree and the implementation-level statement
(`GBCA.ByABDY.specificationRelation_corrupt`) applies verbatim (D1). -/
theorem instanceSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n, isFailLabel l → ∀ (r : ℕ) (σ : GBCA.ByABDY.ImplementationState P.n)
      (s : GBCA.SpecState P.n), substitutionRelation P r σ s →
      substitutionRelation P r (corruptionAct P l σ) (specificationCorruptionAct P l s) := by
  rintro l hl r ⟨u, w⟩ s hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k =>
      have hs : corruptionAct P (Sum.inl (Label.fail k)) (u, w)
          = GBCA.ByABDY.ImplementationState.corrupt P k (u, w) := composition_corrupt k
      have hc := GBCA.ByABDY.specificationRelation_corrupt P r k hR
      rw [← hs] at hc
      exact hc
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.instanceSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceSubstitution

end GBCA.ByABDY
end ABA
end PLTS
