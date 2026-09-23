/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.BroadcastSubstitution

/-!
# The common core at the two gather implementations

The common core read off a trace (`Gather.CoreTrace`, `ABA/Gather/SpecificationSafety.lean`) holds
at the gather instance over the broadcast specifications and at the gather instance over Bracha's
broadcast: `Gather.instanceOverBroadcastSpecification_core` and `Gather.instanceOverBracha_core`.
Every return of a positive-probability trace names one payload set, of at least `n − f` entries and
below the returned map, and every return of that trace names the same set.

`toSpecificationLabel` sends an interface label to the specification label it stands for: the call
loop stands for the call it loops on. An execution of `specificationOverInstanceAlphabet` has the
states of a `specInst` execution and labels that `toSpecificationLabel` sends to its labels, so
`specificationOverInstanceAlphabet_core` reads `CoreTrace` off the relabelled trace, where
`Gather.specInst_core` reads it at the specification itself. The two implementations then inherit
it along their refinements (`PLTS.safety_transfer`): the counting refinement
(`instanceOverBroadcastSpecification_refines`, `ABA/Gather/RefinesSpecification.lean`) and, beneath
it, the broadcast substitution (`instanceOverBracha_refines`,
`ABA/Gather/BroadcastSubstitution.lean`).

What makes that transfer say anything is that the core is on the label (D29): an implementation
holds it in a field no process reads, and its refinements match the labels that carry it.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The common core along the refinements -/

/-- The specification label an interface label stands for: the call loop stands
for the call it loops on. -/
def toSpecificationLabel {n : ℕ} : InstanceLabel n X → Label n X
  | Sum.inl l => l
  | Sum.inr (.callLoop id x) => .call id x

omit [DecidableEq X] in
/-- The specification's alphabet read off an interface label is `toSpecificationLabel`. -/
theorem specificationLabelMap_eq_toSpecificationLabel {n : ℕ} (l : InstanceLabel n X) :
    specificationLabelMap n X l = some (toSpecificationLabel l) := by
  cases l with
  | inl l₀ => rfl
  | inr e => cases e; rfl

/-- A transition of the lifted specification is a transition of the
specification at the label `toSpecificationLabel` names. -/
theorem specificationOverInstanceAlphabet_step_toSpecification (P : Parameters)
    {s : SpecState P.n X} {l : InstanceLabel P.n X} {μ : PMF (SpecState P.n X)}
    (h : (specificationOverInstanceAlphabet P X).step s l μ) :
    (specInst P X).step s (toSpecificationLabel l) μ :=
  (System.mapIdle_step_some (specificationLabelMap_eq_toSpecificationLabel l) μ).mp h

/-- **The lifted specification binds one core.** An execution of `specificationOverInstanceAlphabet`
has the states of a `specInst` execution and labels that `toSpecificationLabel` sends to its
labels, so the guards of a return are read off the specification's own transitions. -/
theorem specificationOverInstanceAlphabet_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (specificationOverInstanceAlphabet P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map toSpecificationLabel) := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ := exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  have h_exec' : is_exec (e.mapLabels toSpecificationLabel) (specInst P X) :=
    ⟨is_partial_exec_mapLabels toSpecificationLabel (fun _ _ _ h =>
      specificationOverInstanceAlphabet_step_toSpecification P h)
      h_exec.1,
      h_exec.2⟩
  have hret : ∀ (id : Fin P.n) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X),
      Label.ret id g C ∈ t.map toSpecificationLabel →
      ∃ (k : ℕ) (s : SpecState P.n X), (e.mapLabels toSpecificationLabel).stateAt k = some s ∧
        s.core = some C ∧ AcceptedPairs.subMap C g := by
    intro id g C h₁
    obtain ⟨l, hl, hdown⟩ := Stream'.Seq.exists_of_mem_map h₁
    obtain ⟨-, k, s', hg⟩ := (h_char l).mp hl
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    have hstep' : Step P s (Label.ret id g C) μ := by
      have h2 := specificationOverInstanceAlphabet_step_toSpecification P hstep
      rwa [hdown] at h2
    obtain ⟨hC, hmem⟩ := ret_guards hstep'
    exact ⟨k, s, by rw [AlterSeq.stateAt_mapLabels]; exact hst, hC, hmem⟩
  refine ⟨?_, ?_⟩
  · intro id g C h₁
    obtain ⟨k, s, hst, hC, hmem⟩ := hret id g C h₁
    exact ⟨core_card h_exec' k s hst C hC, hmem⟩
  · intro id₁ id₂ g₁ g₂ C₁ C₂ h₁ h₂
    obtain ⟨k₁, s₁, hst₁, hC₁, -⟩ := hret id₁ g₁ C₁ h₁
    obtain ⟨k₂, s₂, hst₂, hC₂, -⟩ := hret id₂ g₂ C₂ h₂
    rcases le_total k₁ k₂ with hk | hk
    · have hcarry := is_exec_stable (sys := specInst P X)
        (fun s => s.core = some C₁) (fun s l μ s' => core_stable s l μ s')
        h_exec' k₁ k₂ s₁ s₂ hk hst₁ hst₂ hC₁
      rw [hcarry] at hC₂
      exact Option.some.inj hC₂
    · have hcarry := is_exec_stable (sys := specInst P X)
        (fun s => s.core = some C₂) (fun s l μ s' => core_stable s l μ s')
        h_exec' k₂ k₁ s₂ s₁ hk hst₂ hst₁ hC₂
      rw [hcarry] at hC₁
      exact (Option.some.inj hC₁).symm

/-- **The composed gather instance binds one core.** -/
theorem instanceOverBroadcastSpecification_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (instanceOverBroadcastSpecification P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map toSpecificationLabel) :=
  safety_transfer (instanceOverBroadcastSpecification_refines P X)
    (specificationOverInstanceAlphabet_core P X)

/-- **The common core at the gather instance over Bracha's broadcasts**: every
return of a positive-probability trace names a set of at least `n − f` entries
below the returned map, and every return names the same set. The two
substitutions carry it down from the specification. -/
theorem instanceOverBracha_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (instanceOverBracha P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map toSpecificationLabel) :=
  safety_transfer (Set.Subset.trans (instanceOverBracha_refines P X)
    (instanceOverBroadcastSpecification_refines P X))
    (specificationOverInstanceAlphabet_core P X)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.specificationOverInstanceAlphabet_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationOverInstanceAlphabet_core

/-- info: 'PLTS.ABA.Gather.instanceOverBroadcastSpecification_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBroadcastSpecification_core

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_core

end Gather
end ABA
end PLTS
