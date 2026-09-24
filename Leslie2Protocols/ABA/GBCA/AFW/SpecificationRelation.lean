/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Invariant

/-!
# The simulation relation of the round over the gather specifications

`GBCA.ByAFW.SpecificationRelation P s t` relates a state of the round over the gather
specifications (`GBCA.ByAFW.roundOverGatherSpecifications`, `ABA/GBCA/AFW/Composition.lean`) to a
state of the round-`r` graded agreement specification (`GBCA.specInst`, the exclusion-set
specification). `specificationRelation_init` holds it at the two initial states, and
`specificationRelation_corrupt` is broadcast compatibility: the relation is preserved by corrupting
both systems at once, in the shape the family congruence consumes.

The relation carries the invariant of `ABA/GBCA/AFW/Invariant.lean`, and reads the call records,
the return flags and the corrupted sets off the round's state directly (`call_eq`, `ret_eq`,
`F_eq`). The specification's `excluded` and `grade` are bookkeeping the round records nothing; the
relation carries evidence for them instead. An excluded bit is covered by an exclusion certificate
`ExclusionEvidence` (`exclusion_certificate`), the grade-2 guard by a value on at least `|S| − f`
entries of the second gather's core (`grade2_evidence`), and the grade-0 guard by that core
carrying each bit on at most `f` entries (`grade0_evidence`).

## The bound bit on the label

The return label carries the round's bound bit, which the round's network holds (D29). The clause
`excluded_bound` says the specification's `excluded` holds nothing but that bit's complement, so a
return finds either `(!bnd) ∈ excluded` already — and fires `ret` alone — or `excluded = ∅` — and
fires `bindUnset (!bnd) ; ret`. A value-bearing outcome's value is the bound bit, by
`boundOfCore_of_aboveThreshold` on the first gather's core, so the specification's guard pair
`v ∉ excluded`, `(!v) ∈ excluded` is the same pair.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Parameters}

/-! ### The relation -/

/-- The refinement relation of the round over the gather specifications. -/
structure SpecificationRelation (P : Parameters) (s : RoundStateOverGatherSpecifications P.n)
    (t : GBCA.SpecState P.n) : Prop where
  /-- The invariant. -/
  invariant : Invariant P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = (firstGather s).call k
  /-- The return flags agree: the specification returns at the graded return,
  which the program marks. -/
  ret_eq : ∀ id, t.ret id = (programs s id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = (firstGather s).F
  /-- An excluded bit is certified excluded. -/
  exclusion_certificate : ∀ b ∈ t.excluded, ExclusionEvidence P s b
  /-- An excluded bit is the complement of the round's bound bit: the
  exclusion is written inside the first return's run, which announces that
  bit. -/
  excluded_bound : ∀ b ∈ t.excluded, ∃ β, bound s = some β ∧ b = !β
  /-- The grade-2 guard is certified by a value on at least `|S| − f` entries
  of the second gather's core. -/
  grade2_evidence : t.grade = some true → ∃ S v, (secondGather s).core = some S ∧
    S.card - P.f ≤ AcceptedPairs.count S (some v)
  /-- The grade-0 guard is certified by the second gather's core carrying each
  bit on at most `f` entries. -/
  grade0_evidence : t.grade = some false → ∃ S, (secondGather s).core = some S ∧
    ∀ v, AcceptedPairs.count S (some v) ≤ P.f

/-- The relation holds initially. -/
theorem specificationRelation_init (P : Parameters) (r : ℕ) :
    SpecificationRelation P ((roundOverGatherSpecifications P r).init)
      ((GBCA.specificationOverRoundAlphabet P Empty r).init) := by
  refine ⟨Invariant.initial P r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, programs, bound, firstGather, secondGather,
      Gather.SpecState.initial, GBCA.SpecState.initial, ProcessRecord.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both systems at once. -/
theorem specificationRelation_corrupt {r : ℕ} {s : RoundStateOverGatherSpecifications P.n}
    {t : GBCA.SpecState P.n} (hR : SpecificationRelation P s t) (id : Fin P.n) :
    SpecificationRelation P
    (corruptAll P id (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s)
    (t.corrupt P id) := by
  refine ⟨hR.invariant.step (r := r) (AlgorithmOverGatherSpecifications.fail s id) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp only [firstGather_corruptAll]
    rw [GBCA.corrupt_call, Gather.corrupt_call]
    exact hR.call_eq k
  · intro k
    rw [GBCA.corrupt_ret]
    exact hR.ret_eq k
  · dsimp only [firstGather_corruptAll]
    rw [GBCA.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hR.F_eq]
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    obtain ⟨S, hS, hl⟩ := hR.exclusion_certificate b hb
    exact ⟨S, by rw [firstGather_corruptAll, Gather.corrupt_core]; exact hS, hl⟩
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    exact hR.excluded_bound b hb
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, v, hS, hh⟩ := hR.grade2_evidence hg
    exact ⟨S, v, by rw [secondGather_corruptAll, Gather.corrupt_core]; exact hS, hh⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, hS, hl⟩ := hR.grade0_evidence hg
    exact ⟨S, by rw [secondGather_corruptAll, Gather.corrupt_core]; exact hS, hl⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.specificationRelation_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationRelation_corrupt

end GBCA.ByAFW
end ABA
end PLTS
