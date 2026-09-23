/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.SpecificationRelation

/-!
# The reliable-broadcast refinement: Bracha's protocol implements Transition System 6

`BRB.brachaRefinesSpecification`: the reliable-broadcast instance `BRB.brachaInstance`
(`ABA/ReliableBroadcast/Bracha/Composition.lean`) is forward simulated by the broadcast
specification instance with the same leader, read over the instance's interface
(`BRB.specificationOverInstanceAlphabet`), along `BRB.SpecificationRelation`.

The refinement runs in two steps. The first is strong and functional: a transition of the instance
is one transition of `BRB.BrachaAlgorithm` at the same state, at the specification label the
interface label projects to (`BRB.brachaInstance_step_row`). The second is the matching
`BRB.specificationRelation_row`, whose answer is a weak run of the specification over `BRB.Label`;
it is lifted to the interface along a section of `BRB.specificationLabelMap`, which is where the
call loop is answered by the specification's own loop.

The step-level transports beside the refinement export the relation across one transition, for the
systems that replay Bracha's transitions inside a larger algorithm: `specificationRelation_tau` for
an internal transition under a stuttering specification, `brachaAlgorithm_tau_F` for the corrupted
set across one, `specificationRelation_call` for the fused effects of a call, and `commitReach` for
the on-demand commit that a derived delivery licenses.

## Model and deviations

* **D27 (safety only).** The specification the instance refines carries Validity and Agreement;
  Totality is out of scope.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-- **The reliable-broadcast refinement**: the reliable-broadcast instance is forward simulated
by the specification instance with the same leader, read over the instance's interface. A
transition of the instance is one transition of `BrachaAlgorithm`
(`BRB.brachaInstance_step_row`), that transition is answered by a weak run of the specification
(`specificationRelation_row`), and the run is lifted to the interface along a section of
`specificationLabelMap`, which is where the call loop is answered by the specification's own
loop. -/
theorem brachaRefinesSpecification (P : Parameters) (ldr : Fin P.n) :
    ForwardSimulation (brachaInstance P ldr M) (specificationOverInstanceAlphabet P ldr M)
    (SpecificationRelation P ldr) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := brachaInstance_step_row P ldr q₁ l μ hstep
  obtain ⟨s', hdis, hrel⟩ := specificationRelation_row P ldr q₁ q₂ hR l₀ μ hrow q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨specificationLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_specificationOverInstanceAlphabet P ldr hweak⟩
  · refine Or.inr ⟨?_, weakLStep_specificationOverInstanceAlphabet P ldr hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : specificationLabelMap P.n M (Silent.τ : InstanceLabel P.n M) = some l₀ := by
      rw [← hl]; exact hpull
    rw [specificationLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### Step-level relation transports

The relation across one transition, exported for the systems that replay Bracha's transitions
inside a larger algorithm: an internal transition under a stuttering specification, the call
across the fused effects, and the on-demand commit that a derived delivery licenses. -/

/-- The relation across any internal transition, the specification stuttering. -/
theorem specificationRelation_tau {P : Parameters} {ldr : Fin P.n} {s s' : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t)
    (hstep : BrachaAlgorithm P ldr s Label.tau (PMF.pure s')) :
    SpecificationRelation P ldr s' t := by
  have hInv' := hR.invariant.step hstep (by rw [PMF.mem_support_pure_iff])
  generalize hμ : (PMF.pure s' : PMF (BrachaState P.n M)) = μ at hstep
  cases hstep with
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.receiveMessage_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.receiveMessage_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_certificate m' hm').receiveMessage i j m
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteAmplification j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | byzantine j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.multicast_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.multicast_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast]
      exact hR.val_certificate m' hm'

/-- An internal transition leaves the corrupted set alone. -/
theorem brachaAlgorithm_tau_F {P : Parameters} {ldr : Fin P.n} {s s' : BrachaState P.n M}
    (hstep : BrachaAlgorithm P ldr s Label.tau (PMF.pure s')) : s'.F = s.F := by
  generalize hμ : (PMF.pure s' : PMF (BrachaState P.n M)) = μ at hstep
  cases hstep with
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    rfl
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | voteAmplification j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | byzantine j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp

/-- The relation across the leader's call, the specification calling too. -/
theorem specificationRelation_call {P : Parameters} {ldr : Fin P.n} {s : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t) {m : M}
    (h : (s.process ldr).input = none) :
    SpecificationRelation P ldr
      ((s.setProcess ldr { s.process ldr with input := some m }).multicast ldr (.init m))
      { t with input := some m } := by
  refine ⟨hR.invariant.step (BrachaAlgorithm.call s m h) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
  · intro k
    by_cases hkl : k = ldr
    · subst hkl
      rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
      exact hR.ret_eq k
    · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
      exact hR.ret_eq k
  · simpa using hR.F_eq
  · intro m' hm'
    rw [echoCertificate_multicast, echoCertificate_setProcess]
    exact hR.val_certificate m' hm'

/-- **The on-demand commit.** A `VOTE` receipt quorum licenses the
specification's committed value: either it is already this value, or the
`commit` guard holds towards it, the relation restored either way. -/
theorem commitReach {P : Parameters} {ldr : Fin P.n} {s : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t) {id : Fin P.n} {m : M}
    (hcnt : 2 * P.f + 1 ≤ s.receivedCount id (.vote m)) :
    (t.val = some m ∧ SpecificationRelation P ldr s t) ∨
    (t.val = none ∧ (ldr ∈ t.F ∨ t.input = some m) ∧
      SpecificationRelation P ldr s { t with val := some m }) := by
  have hcert : EchoCertificate P s m := echoCertificate_of_vote_quorum hR.invariant hcnt
  rcases hval : t.val with _ | m'
  · right
    have hcommit : ldr ∈ t.F ∨ t.input = some m := by
      by_cases hldr : ldr ∈ s.F
      · exact Or.inl (by rw [hR.F_eq]; exact hldr)
      · exact Or.inr (by
          rw [hR.input_eq]
          exact input_of_echoCertificate hR.invariant hldr hcert)
    refine ⟨rfl, hcommit, hR.invariant, ?_, hR.ret_eq, hR.F_eq, ?_⟩
    · dsimp only
      exact hR.input_eq
    · intro m'' hm''
      dsimp only at hm''
      obtain rfl : m = m'' := by
        injection hm''
      exact hcert
  · left
    obtain rfl : m' = m :=
      echoCertificate_unique hR.invariant (hR.val_certificate m' hval) hcert
    exact ⟨rfl, hR⟩

/-- info: 'PLTS.ABA.BRB.brachaRefinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaRefinesSpecification

end BRB
end ABA
end PLTS
