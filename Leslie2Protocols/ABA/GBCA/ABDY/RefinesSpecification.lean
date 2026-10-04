/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.SpecificationRelation

/-!
# The refinement of the round's graded-agreement composition

`GBCA.ByABDY.refinesSpecification`: the round-`r` composition (`GBCA.ByABDY.composition`,
`ABA/GBCA/ABDY/Composition.lean`) forward-simulates the graded agreement specification read over
the round's interface (`GBCA.specificationOverRoundAlphabet`), along `specificationRelation`
(`ABA/GBCA/ABDY/SpecificationRelation.lean`).

A transition of the composition is one transition of `Algorithm`
(`GBCA.ByABDY.composition_projects`), that transition is matched by a weak run of the
specification (`specificationRelation_transition`), and the run is lifted to the round's interface
along a section of `specificationLabelMap`. A Byzantine call or return transition is matched at
that lifting by the specification's own call or return (D11).
`composition_specificationTraces` is the trace-distribution inclusion the simulation yields.

Every return of the algorithm does the same decidable case split on the specification's `excluded`.
Where the exclusion is missing, the return is matched by the two-step weak run of
`GBCA/ABDY/SpecificationRelation.lean`, whose excluded bit comes from the return's own exclusion
witness. Where the exclusion is on record, the return is matched by a single graded
specification return. A `fail` is matched by the specification's corruption, and
`specificationRelation_corrupt_F_eq` keeps the two `corrupt` functions equal on aligned
corrupted sets.

`specificationCorruptionAct` is the broadcast corruption act the lifted specification carries at
the extended alphabet. `specificationRelation_init` and `refinesSpecification_failAct` are the two
premises `ForwardSimulation.family` (`Framework/FamilySimulation.lean`) asks of the round-indexed
family: the relation holds at the initial states, and it survives the broadcast corruption. The
family lifting that consumes them is `ABA/ABDY/Substitution.lean`.

Binding is stated on the labels of a trace (`GBCA.BindingTraceExtended`), so the inclusion carries
it; `ABA/GBCA/ABDY/Binding.lean` takes that step.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

variable {P : Parameters}

/-! ### The relation across one transition -/

/-- **The relation across one transition**: every transition of `Algorithm` at a related
pair is matched by a weak run of the graded agreement specification, ending at a related
state. The internal transitions stutter, the multicast of the process's own `INPUT` among them;
the call, the call loop and `fail` are matched by the
specification's own transitions; a return is matched by a graded specification return, preceded by
`bindUnset` where the bit that return needs excluded is not excluded yet. -/
theorem specificationRelation_transition (P : Parameters) (r : ℕ) (q1 : RoundState P.n)
    (q2 : SpecState P.n) (hR : specificationRelation P r q1 q2) (l : Label P.n)
    (μ1 : PMF (RoundState P.n)) (hstep : Algorithm P r q1 l μ1)
    (q1' : RoundState P.n) (hq1' : q1' ∈ μ1.support) :
    ∃ q2', ((l = Silent.τ ∧ (specInst P r).weakLSilent q2 q2') ∨
      (¬ l = Silent.τ ∧ (specInst P r).weakLStep q2 l q2')) ∧
      specificationRelation P r q1' q2' := by
  have hRR : SpecificationRelation P q1 q2 := hR
  have hI' : Invariant P q1' := hRR.invariant.step hstep hq1'
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨{ q2 with call := Function.update q2.call id (some b) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q2 id b (by rw [hRR.call_eq]; exact h))⟩,
      hI', ?_, ?_, hRR.F_eq, ?_,
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      change Function.update q2.call id (some b) k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.ret_eq k
      · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hRR.ret_eq k
    · intro b' hb'
      refine ExclusionWitness.mono (s := q1) (fun _ _ _ hm => by simpa using hm)
        (fun k w hk => ?_) (Finset.Subset.refl _) (hRR.exclusion_witness b' hb')
      by_cases hkj : k = id
      · subst hkj
        rw [RoundState.setProcessVariables_processVariables_self]
        exact hk
      · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hkj]
        exact hk
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inr ⟨by simp,
      System.weakLStep_of_step (by simp) (Step.callLoop q2 id b)⟩, hRR⟩
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', by simpa using hRR.call_eq, by simpa using hRR.ret_eq, hRR.F_eq, ?_, ?_, ?_,
      hRR.bound_excluded⟩
    · intro b hb
      exact ExclusionWitness.mono (s := q1)
        (fun i' j' m' hm' => RoundState.mem_receiveMessage_received.mpr (Or.inr hm'))
        (fun k w hk => by simpa using hk) (Finset.Subset.refl _) (hRR.exclusion_witness b hb)
    · intro hg
      obtain ⟨v0, i0, hi0⟩ := hRR.grade2_witness hg
      exact ⟨v0, i0,
        le_trans hi0 (RoundState.receivedCount_le_receiveMessage q1 i j m i0 _)⟩
    · intro hg
      obtain ⟨i0, hi0⟩ := hRR.grade0_witness hg
      exact ⟨i0, le_trans hi0 (RoundState.receivedCount_le_receiveMessage q1 i j m i0 _)⟩
  | input j b hin hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | voteBot j hin _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | bindBit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | bindBot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionWitness_send (by intro w hw; exact hw)
        (hRR.exclusion_witness b' hb'),
      by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [processVariables_send_ne hk]
        exact hRR.ret_eq k
  | byzantine j m hjF =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, hRR.exclusion_witness, hRR.grade2_witness,
      hRR.grade0_witness, hRR.bound_excluded⟩
  | retGrade2 id v bnd _hin _hlv hcnt hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k₁, hk₁F, hbq⟩ := received_binds_of_echo5_quorum hRR.invariant hcnt
    obtain ⟨k, hkF, hvq⟩ :=
      voteQuorum_of_received_binds hRR.invariant (i := k₁) (v := v) (by omega)
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_grade2 q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_exclusionWitness_of_voteQuorum hRR.invariant hvq (hRR.exclusion_witness v hv)
    have hgr : q2.grade = none ∨ q2.grade = some true := by
      have hne := grade_ne_false_of_echo5_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact absurd hg hne
        · exact Or.inr rfl
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with
      grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade2 q2 id v v hlive hexcluded hexcluded hgr hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => exclusionWitness_setBound (exclusionWitness_ret
          (hRR.exclusion_witness b hb)),
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [RoundState.setBound_processVariables,
          RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, RoundState.setBound_processVariables,
            RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (receivedEchoQuorum_of_received_votes hRR.invariant (i := k) (v := v) (by omega))
      refine ⟨{ q2 with
        excluded := insert (!v) q2.excluded, grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade2_run hq hw hlive hd0 hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [RoundState.setBound_processVariables,
          RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, RoundState.setBound_processVariables,
            RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact exclusionWitness_setBound
            (exclusionWitness_ret (exclusionWitness_of_voteQuorum hRR.invariant hvq))
        · exact exclusionWitness_setBound (exclusionWitness_ret (hRR.exclusion_witness b
            hb))
  | retGrade1 id v bnd _hin _hlv _hnotGrade2 hcnt honce hbind hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k, hkF, hvq⟩ := voteQuorum_of_received_binds hRR.invariant hbind
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_grade1 q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_exclusionWitness_of_voteQuorum hRR.invariant hvq (hRR.exclusion_witness v hv)
    have hd : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some (!v) ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval (!v))
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade1 q2 id v v hlive hexcluded hexcluded hd hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => exclusionWitness_setBound (exclusionWitness_ret
          (hRR.exclusion_witness b hb)),
        by simpa using hRR.grade2_witness, by simpa using hRR.grade0_witness,
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [RoundState.setBound_processVariables,
          RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, RoundState.setBound_processVariables,
            RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (receivedEchoQuorum_of_received_votes hRR.invariant (i := k) (v := v) (by omega))
      refine ⟨{ q2 with
        excluded := insert (!v) q2.excluded,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade1_run hq hw hlive hd0 hd hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, by simpa using hRR.grade2_witness,
        by simpa using hRR.grade0_witness, by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [RoundState.setBound_processVariables,
          RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, RoundState.setBound_processVariables,
            RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact exclusionWitness_setBound
            (exclusionWitness_ret (exclusionWitness_of_voteQuorum hRR.invariant hvq))
        · exact exclusionWitness_setBound (exclusionWitness_ret (hRR.exclusion_witness b
            hb))
  | retGrade0 id bnd _hin _hlv _hnotGrade2 _hnotGrade1 hcnt hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some true ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval true)
    have hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some false ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval false)
    have hgr : q2.grade = none ∨ q2.grade = some false := by
      have hne := grade_ne_true_of_echo5Bot_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact Or.inr rfl
        · exact absurd hg hne
    have hex := hRR.bound_excluded
    cases hb : q1.bound with
    | none =>
      -- the round has not returned yet: exclude the announced bit's complement
      rw [hb, excludedOf_none] at hex
      have hbv : bnd = boundOf q1.sent q1.F .grade0 := by
        rw [hbnd, hb]; rfl
      have hcert : ExclusionWitness P q1 (!bnd) := by
        rw [hbv]; exact exclusionWitness_boundOf_grade0 hRR.invariant hcnt
      have hq : q2.quorum P := quorum_of_messageQuorum hRR
        (fun j hj hm' => hRR.invariant.input_called j true hj hm')
        (RoundState.bothValid_le hval true)
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun k' => q2.call k' = some bnd ∨ k' ∈ q2.F)).card :=
        hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval bnd)
      refine ⟨{ q2 with
        excluded := insert (!bnd) q2.excluded, grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade0_run hq hw hex hwT hwF hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simp [hex]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [RoundState.setBound_processVariables,
          RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, RoundState.setBound_processVariables,
            RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b' hb'
        rw [Finset.mem_insert] at hb'
        rcases hb' with rfl | hb'
        · exact exclusionWitness_setBound (exclusionWitness_ret hcert)
        · exact exclusionWitness_setBound (exclusionWitness_ret (hRR.exclusion_witness
            b' hb'))
    | some β =>
      -- the round has returned before: it announces the bit on record
      rw [hb, excludedOf_some] at hex
      have hbv : bnd = β := by
        rw [hbnd, hb]; rfl
      subst hbv
      have hmem : (!bnd) ∈ q2.excluded := by
        rw [hex]; exact Finset.mem_singleton_self _
      refine ⟨{ q2 with
        grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade0 q2 id bnd hmem hwT hwF hgr hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb' => exclusionWitness_setBound (exclusionWitness_ret
          (hRR.exclusion_witness b hb')),
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simpa using hex⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [RoundState.setBound_processVariables,
          RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, RoundState.setBound_processVariables,
            RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hRR.ret_eq k'
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2.corrupt P id,
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp) (Step.fail q2 id)⟩,
      hI', ?_, ?_, specificationRelation_corrupt_F_eq hRR.F_eq id, ?_, ?_, ?_, ?_⟩
    · intro k
      rw [corrupt_call, RoundState.corrupt_processVariables]
      exact hRR.call_eq k
    · intro k
      rw [corrupt_ret, RoundState.corrupt_processVariables]
      exact hRR.ret_eq k
    · intro b hb
      rw [corrupt_excluded] at hb
      refine ExclusionWitness.mono (s := q1) (fun i' j' m' hm' => ?_) (fun k w hk => ?_)
        (RoundState.corrupt_F_subset q1 id) (hRR.exclusion_witness b hb)
      · rw [RoundState.corrupt_received]
        exact hm'
      · rw [RoundState.corrupt_processVariables]
        exact hk
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨v0, i0, hi0⟩ := hRR.grade2_witness hg
      exact ⟨v0, i0, by rw [RoundState.corrupt_receivedCount]; exact hi0⟩
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨i0, hi0⟩ := hRR.grade0_witness hg
      exact ⟨i0, by rw [RoundState.corrupt_receivedCount]; exact hi0⟩
    · rw [corrupt_excluded, RoundState.corrupt_bound]
      exact hRR.bound_excluded

/-! ### The refinement

The matching run for a transition of the composition is the algorithm's own, read through
`specificationRelation_transition`: the projection `composition_projects` is strong and functional,
so one step of the composition costs one step of the algorithm and nothing of the matching is
reproved here. The specification's matching weak run is finally lifted to the round's interface
along a section of `specificationLabelMap`. A Byzantine call or return transition is matched at
that lifting by the specification's own call or return (D11). -/

/-- **The refinement of the round's graded-agreement composition**: the round-`r` composition is
forward simulated by the graded agreement specification, read over the round's interface. -/
theorem refinesSpecification (P : Parameters) (r : ℕ) :
    ForwardSimulation (composition P r) (specificationOverRoundAlphabet P Message r)
    (specificationRelation P r) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, halg⟩ := composition_projects P r q₁ l μ hstep
  obtain ⟨s', hdis, hrel⟩ := specificationRelation_transition P r q₁ q₂ hR l₀ μ halg q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨specificationLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_specificationOverRoundAlphabet P Message r hweak⟩
  · refine Or.inr ⟨?_, weakLStep_specificationOverRoundAlphabet P Message r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : specificationLabelMap P.n (Silent.τ : ExtendedLabel P.n Message) = some l₀ := by
      rw [← hl]; exact hpull
    rw [specificationLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-- The soundness inclusion of the refinement: every trace distribution achievable by the round-`r`
composition is achievable by the specification read over the round's interface. -/
theorem composition_specificationTraces (P : Parameters) (r : ℕ) :
    achievableTraceDists (composition P r) ⊆ achievableTraceDists
      (specificationOverRoundAlphabet P Message r) :=
  (ForwardSimulation.toProbabilistic (composition_isLTS P r)
    (specificationOverRoundAlphabet_isLTS P Message r)
    (specificationRelation_init P r) (refinesSpecification P r)).achievableTraceDists_subset

/-! ### What the family lift will need

The two premises of `ForwardSimulation.family` for the round-indexed family: the relation holds at
the initial states (`specificationRelation_init`, `GBCA/ABDY/SpecificationRelation.lean`), and it
survives the broadcast corruption. -/

/-- The broadcast corruption act on a specification state, over the extended
alphabet: `GBCA.failAct` taken on the extended `fail` label. -/
def specificationCorruptionAct (P : Parameters) {M : Type} :
    ExtendedLabel P.n M → GBCA.SpecState P.n → GBCA.SpecState P.n
  | Sum.inl (.fail k), s => s.corrupt P k
  | _, s => s

/-- **Broadcast compatibility**: corruption preserves the relation. The network state's corrupted
set is the one the algorithm reads, so the two guards `k ∉ F ∧ |F| < f` agree and
`GBCA.ByABDY.specificationRelation_corrupt` applies verbatim (D1). -/
theorem refinesSpecification_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n Message, isFailLabel l → ∀ (r : ℕ) (σ : GBCA.ByABDY.RoundState P.n)
      (s : GBCA.SpecState P.n), specificationRelation P r σ s →
      specificationRelation P r (corruptionAct P l σ) (specificationCorruptionAct P l s) := by
  rintro l hl r ⟨u, w⟩ s hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k =>
      have hs : corruptionAct P (Sum.inl (Label.fail k)) (u, w)
          = GBCA.ByABDY.RoundState.corrupt P k (u, w) := composition_corrupt k
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

/-- info: 'PLTS.ABA.GBCA.ByABDY.refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesSpecification

/-- info: 'PLTS.ABA.GBCA.ByABDY.composition_specificationTraces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composition_specificationTraces

end GBCA.ByABDY
end ABA
end PLTS
