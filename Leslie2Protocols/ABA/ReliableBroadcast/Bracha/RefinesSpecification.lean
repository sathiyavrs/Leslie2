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
interface label projects to (`BRB.brachaInstance_step_algorithm`). The second is the matching
`BRB.specificationRelation_transition`, whose matching run is a weak run of the specification over
`BRB.Label`; it is lifted to the interface along a section of `BRB.specificationLabelMap`, which is
where the call loop is answered by the specification's own loop.

The matching is stated here, one transition of `BRB.BrachaAlgorithm` at a time, along
`BRB.SpecificationRelation` (`ABA/ReliableBroadcast/Bracha/SpecificationRelation.lean`). The
internal transitions stutter. The call and corruption are matched by the specification's own
transitions. A return is matched by `ret` alone when `val` is already committed, the witnesses
identifying the two values, and by the two-step run `commit ; ret` when it is not, with `commit`'s
guard discharged by `input_of_echoWitness` under a correct leader and by membership in the
corrupted set otherwise.

Four lemmas beside the refinement hold the relation across one transition:
`specificationRelation_tau` for an internal transition under a stuttering specification,
`brachaAlgorithm_tau_F` for the corrupted set across one, `specificationRelation_call` for the
Four lemmas beside the refinement hold the relation across one transition:
`specificationRelation_tau` for an internal transition under a stuttering specification,
`brachaAlgorithm_tau_F` for the corrupted set across one, `specificationRelation_call` for the two
effects of a call, the write of the leader's input and the `INIT` multicast, and `commitReach` for
the on-demand commit that a derived delivery licenses.

## Model and deviations

* **D27 (safety only).** The specification the instance refines carries Validity and Agreement;
  Totality is out of scope.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-! ### The relation across one transition -/

/-- **The relation across one transition**: every transition of `BrachaAlgorithm` at a related
pair is matched by a weak run of the specification instance, ending at a related state. The
internal transitions stutter; `call` and `fail` are matched by the specification's own
transitions; `ret id m` is matched by `ret` alone when `val` is already committed, and by the
two-step run `commit ; ret` when it is not. -/
theorem specificationRelation_transition (P : Parameters) (ldr : Fin P.n) (q₁ : BrachaState P.n M)
    (q₂ : SpecState P.n M) (hR : SpecificationRelation P ldr q₁ q₂) (l : Label P.n M)
    (μ : PMF (BrachaState P.n M)) (hstep : BrachaAlgorithm P ldr q₁ l μ)
    (q₁' : BrachaState P.n M) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l = Silent.τ ∧ (specInst P ldr M).weakLSilent q₂ q₂') ∨
      (¬ l = Silent.τ ∧ (specInst P ldr M).weakLStep q₂ l q₂')) ∧
      SpecificationRelation P ldr q₁' q₂' := by
  have hInv' := hR.invariant.step hstep hq₁'
  cases hstep with
  | call m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨{ q₂ with input := some m },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ m (by rw [hR.input_eq]; exact h))⟩, hInv', ?_, ?_, ?_, ?_⟩
    · simp
    · intro k
      by_cases hkl : k = ldr
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | callLoop m =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ m)⟩, hR⟩
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.receiveMessage_processVariables]
      exact hR.input_eq
    · intro k
      rw [InstanceState.receiveMessage_processVariables]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_witness m' hm').receiveMessage i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_processVariables, hkl,
          InstanceState.setProcessVariables_processVariables_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_processVariables, hkl,
          InstanceState.setProcessVariables_processVariables_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | voteAmplification j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_processVariables, hkl,
          InstanceState.setProcessVariables_processVariables_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | byzantine j m hj =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.multicast_processVariables]
      exact hR.input_eq
    · intro k
      rw [InstanceState.multicast_processVariables]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast]
      exact hR.val_witness m' hm'
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hcert : EchoWitness P q₁ m := echoWitness_of_vote_quorum hR.invariant hcnt
    have hretQ : q₂.ret id = false := by
      rw [hR.ret_eq id]; exact hr
    have hRel : ∀ t' : SpecState P.n M, t'.val = some m →
        t'.input = q₂.input → t'.F = q₂.F →
        t'.ret = q₂.ret →
        SpecificationRelation P ldr (q₁.setProcessVariables id { q₁.processVariables id with
          returned := true })
          { t' with ret := Function.update t'.ret id true } := by
      intro t' hval hinput hF hret
      refine ⟨hInv', ?_, ?_, ?_, ?_⟩
      · rw [hinput]
        by_cases hkl : ldr = id
        · rw [hkl, InstanceState.setProcessVariables_processVariables_self]
          rw [hR.input_eq, hkl]
        · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hR.input_eq
      · intro k
        by_cases hkl : k = id
        · subst hkl
          rw [InstanceState.setProcessVariables_processVariables_self]
          change Function.update t'.ret k true k = true
          rw [Function.update_self]
        · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          change Function.update t'.ret id true k = _
          rw [Function.update_of_ne hkl, hret]
          exact hR.ret_eq k
      · rw [InstanceState.setProcessVariables_F]
        rw [hF]
        exact hR.F_eq
      · intro m' hm'
        rw [echoWitness_setProcessVariables]
        obtain rfl : m = m' := by
          have := hval
          rw [show ({ t' with ret := Function.update t'.ret id true } :
            SpecState P.n M).val = t'.val from rfl] at hm'
          rw [hval] at hm'
          injection hm'
        exact hcert
    cases hval : q₂.val with
    | some m' =>
      obtain rfl : m = m' :=
        echoWitness_unique hR.invariant hcert (hR.val_witness m' hval)
      refine ⟨{ q₂ with ret := Function.update q₂.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.ret q₂ id m hval hretQ)⟩, ?_⟩
      exact hRel q₂ hval rfl rfl rfl
    | none =>
      have hcommit : (specInst P ldr M).LStep q₂ Silent.τ
          { q₂ with val := some m } := by
        refine Step.commit q₂ m hval ?_
        by_cases hldr : ldr ∈ q₁.F
        · exact Or.inl (by rw [hR.F_eq]; exact hldr)
        · exact Or.inr (by
            rw [hR.input_eq]
            exact input_of_echoWitness hR.invariant hldr hcert)
      have hret : (specInst P ldr M).LStep { q₂ with val := some m }
          (.ret id m)
          { q₂ with val := some m, ret := Function.update q₂.ret id true } :=
        Step.ret _ id m rfl hretQ
      refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hcommit hret (by simp)⟩, ?_⟩
      exact hRel { q₂ with val := some m } rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.fail q₂ id)⟩, specificationRelation_corrupt hR id⟩

/-! ### The refinement -/

/-- **The reliable-broadcast refinement**: the reliable-broadcast instance is forward simulated
by the specification instance with the same leader, read over the instance's interface. A
transition of the instance is one transition of `BrachaAlgorithm`
(`BRB.brachaInstance_step_algorithm`), that transition is matched by a weak run of the
specification (`specificationRelation_transition`), and the run is lifted to the interface along a
section of `specificationLabelMap`, which is where the call loop is answered by the specification's
own loop. -/
theorem brachaRefinesSpecification (P : Parameters) (ldr : Fin P.n) :
    ForwardSimulation (brachaInstance P ldr M) (specificationOverInstanceAlphabet P ldr M)
    (SpecificationRelation P ldr) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, htransition⟩ := brachaInstance_step_algorithm P ldr q₁ l μ hstep
  obtain ⟨s', hdis, hrel⟩ := specificationRelation_transition P ldr q₁ q₂ hR l₀ μ htransition q₁'
    hq₁'
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

/-! ### The relation across the internal and the call transitions

An internal transition under a stuttering specification, the corrupted set across an internal
An internal transition under a stuttering specification, the corrupted set across an internal
transition, the two effects of a call, the write of the leader's input and the `INIT` multicast, and
the on-demand commit that a derived delivery licenses. -/

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
    · rw [InstanceState.receiveMessage_processVariables]
      exact hR.input_eq
    · intro k
      rw [InstanceState.receiveMessage_processVariables]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_witness m' hm').receiveMessage i j m
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_processVariables, hkl,
          InstanceState.setProcessVariables_processVariables_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_processVariables, hkl,
          InstanceState.setProcessVariables_processVariables_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | voteAmplification j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_processVariables, hkl,
          InstanceState.setProcessVariables_processVariables_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      exact hR.val_witness m' hm'
  | byzantine j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.multicast_processVariables]
      exact hR.input_eq
    · intro k
      rw [InstanceState.multicast_processVariables]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoWitness_multicast]
      exact hR.val_witness m' hm'

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
    (h : (s.processVariables ldr).input = none) :
    SpecificationRelation P ldr
      ((s.setProcessVariables ldr { s.processVariables ldr with input := some m }).multicast ldr
        (.init m))
      { t with input := some m } := by
  refine ⟨hR.invariant.step (BrachaAlgorithm.call s m h) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [InstanceState.multicast_processVariables,
      InstanceState.setProcessVariables_processVariables_self]
  · intro k
    by_cases hkl : k = ldr
    · subst hkl
      rw [InstanceState.multicast_processVariables,
        InstanceState.setProcessVariables_processVariables_self]
      exact hR.ret_eq k
    · rw [InstanceState.multicast_processVariables,
        InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
      exact hR.ret_eq k
  · simpa using hR.F_eq
  · intro m' hm'
    rw [echoWitness_multicast, echoWitness_setProcessVariables]
    exact hR.val_witness m' hm'

/-- **The on-demand commit.** A quorum of received `VOTE` messages licenses the
specification's committed value: either it is already this value, or the
`commit` guard holds towards it, the relation restored either way. -/
theorem commitReach {P : Parameters} {ldr : Fin P.n} {s : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t) {id : Fin P.n} {m : M}
    (hcnt : 2 * P.f + 1 ≤ s.receivedCount id (.vote m)) :
    (t.val = some m ∧ SpecificationRelation P ldr s t) ∨
    (t.val = none ∧ (ldr ∈ t.F ∨ t.input = some m) ∧
      SpecificationRelation P ldr s { t with val := some m }) := by
  have hcert : EchoWitness P s m := echoWitness_of_vote_quorum hR.invariant hcnt
  rcases hval : t.val with _ | m'
  · right
    have hcommit : ldr ∈ t.F ∨ t.input = some m := by
      by_cases hldr : ldr ∈ s.F
      · exact Or.inl (by rw [hR.F_eq]; exact hldr)
      · exact Or.inr (by
          rw [hR.input_eq]
          exact input_of_echoWitness hR.invariant hldr hcert)
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
      echoWitness_unique hR.invariant (hR.val_witness m' hval) hcert
    exact ⟨rfl, hR⟩

/-- info: 'PLTS.ABA.BRB.brachaRefinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaRefinesSpecification

end BRB
end ABA
end PLTS
