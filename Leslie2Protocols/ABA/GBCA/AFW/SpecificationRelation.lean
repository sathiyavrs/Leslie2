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

The relation carries the invariant of `ABA/GBCA/AFW/Invariant.lean`, and reads the calls,
the return flags and the corrupted sets directly from the round's state (`call_eq`, `ret_eq`,
`F_eq`). The specification's `excluded` and `grade` record data that has no field in the round's
state, so the relation carries a witness for each. An excluded bit is covered by an exclusion
witness `ExclusionWitness` (`exclusion_witness`), the grade-2 guard by a value on at least
`|S| − f` entries of the second gather's core (`grade2_witness`), and the grade-0 guard by that
core carrying each bit on at most `f` entries (`grade0_witness`).

## The bound bit

The round's bound bit `β` is `GBCA.boundOfCore P S` of the first gather's core `S`, and the
round's network announces it once it has recorded `S` and the round has returned (D29). The clause
`excluded_bound` says the specification's `excluded` holds nothing but that bit's complement, so
at a return either `(!β) ∈ excluded` holds already and the specification fires its return alone,
or `excluded = ∅` and it fires `bindUnset (!β)` and then its return. The value of a grade-1 or
grade-2 outcome is the bound bit, by `boundOfCore_of_aboveThreshold` on the first gather's core,
so the specification's guard pair `v ∉ excluded`, `(!v) ∈ excluded` is the same pair. The clause
`returned_excluded` ties the network's record of the round's return to the specification: from
the round's first return on, the specification excludes the complement of the bound bit, which is
the guard of its own announcement.
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
  /-- The calls agree. -/
  call_eq : ∀ k, t.call k = (firstGather s).call k
  /-- The return flags agree: the specification returns at the graded return,
  which the program marks. -/
  ret_eq : ∀ id, t.ret id = (programs s id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = (firstGather s).F
  /-- An excluded bit is witnessed excluded. -/
  exclusion_witness : ∀ b ∈ t.excluded, ExclusionWitness P s b
  /-- An excluded bit is the complement of the bound bit of the first gather's core: the
  exclusion is written inside the run that matches the round's first return. -/
  excluded_bound : ∀ b ∈ t.excluded, ∃ S, (firstGather s).core = some S ∧ b = !boundOfCore P S
  /-- Once the round's network has recorded a return, the specification excludes the complement
  of the bound bit of the first gather's core. -/
  returned_excluded : (network s).returned = true →
    ∃ S, (firstGather s).core = some S ∧ (!boundOfCore P S) ∈ t.excluded
  /-- The grade-2 guard is witnessed by a value on at least `|S| − f` entries
  of the second gather's core. -/
  grade2_witness : t.grade = some true → ∃ S v, (secondGather s).core = some S ∧
    S.card - P.f ≤ AcceptedPairs.count S (some v)
  /-- The grade-0 guard is witnessed by the second gather's core carrying each
  bit on at most `f` entries. -/
  grade0_witness : t.grade = some false → ∃ S, (secondGather s).core = some S ∧
    ∀ v, AcceptedPairs.count S (some v) ≤ P.f

/-- The relation holds initially. -/
theorem specificationRelation_init (P : Parameters) (r : ℕ) :
    SpecificationRelation P ((roundOverGatherSpecifications P r).init)
      ((GBCA.specificationOverRoundAlphabet P Empty r).init) := by
  refine ⟨Invariant.initial P r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, programs, network, firstGather, secondGather,
      Gather.SpecState.initial, GBCA.SpecState.initial, ProcessVariables.initial,
      NetworkState.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both systems at once. -/
theorem specificationRelation_corrupt {r : ℕ} {s : RoundStateOverGatherSpecifications P.n}
    {t : GBCA.SpecState P.n} (hR : SpecificationRelation P s t) (id : Fin P.n) :
    SpecificationRelation P
    (corruptAll P id (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s)
    (t.corrupt P id) := by
  refine ⟨hR.invariant.step (r := r) (AlgorithmOverGatherSpecifications.fail s id) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    obtain ⟨S, hS, hl⟩ := hR.exclusion_witness b hb
    exact ⟨S, by rw [firstGather_corruptAll, Gather.corrupt_core]; exact hS, hl⟩
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    obtain ⟨S, hS, hbS⟩ := hR.excluded_bound b hb
    exact ⟨S, by rw [firstGather_corruptAll, Gather.corrupt_core]; exact hS, hbS⟩
  · intro hret
    obtain ⟨S, hS, hex⟩ := hR.returned_excluded hret
    exact ⟨S, by rw [firstGather_corruptAll, Gather.corrupt_core]; exact hS,
      by rw [GBCA.corrupt_excluded]; exact hex⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, v, hS, hh⟩ := hR.grade2_witness hg
    exact ⟨S, v, by rw [secondGather_corruptAll, Gather.corrupt_core]; exact hS, hh⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, hS, hl⟩ := hR.grade0_witness hg
    exact ⟨S, by rw [secondGather_corruptAll, Gather.corrupt_core]; exact hS, hl⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.specificationRelation_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationRelation_corrupt

end GBCA.ByAFW
end ABA
end PLTS
