/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.SpecificationRelation

/-!
# The per-instance GBCA refinement

The round-`r` implementation instance (`GBCA.ByABDY.implementation`, ABDY22 Algorithm 6 —
all five message levels, D18) forward-simulates the round-`r` specification
instance (`GBCA.specInst`, the exclusion-set specification, D19):
`GBCA.ByABDY.refinesSpecification`, along `specificationRelation`.

Every return row does the same decidable case split on the specification's `excluded`. Where the
exclusion is missing, the row is answered by the two-step weak run of
`GBCA/ABDY/SpecificationRelation.lean`, whose excluded bit comes from the return's own exclude
certificate; where the exclusion is on record, the row is answered by a single graded specification
return. A `fail` is answered by the specification's corruption, and
`implementationSpecification_corrupt_F_eq` keeps the two `corrupt` functions equal on aligned
corrupted sets.

Binding is stated on the labels of a trace (`GBCA.BindingTrace`), so the
soundness inclusion of that simulation carries it: `GBCA.ByABDY.implementation_refines` is
the inclusion and `GBCA.ByABDY.implementation_binding` is the specification's
`GBCA.specInst_binding` at the implementation instance.

The family congruence `ForwardSimulation.family` (`Framework/FamilySimulation.lean`) reaches
`ABA/Composition/GBCAInstanceByABDY/Substitution.lean` and
`ABA/Implementation/ABDY/CompositionChain.lean` along this file, which also supplies the broadcast
ingredient that congruence consumes (`specificationRelation_corrupt`).
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

variable {P : Parameters}

/-! ### The refinement -/

/-- The two `corrupt` functions stay equal on aligned corrupted sets (a strong per-coordinate `fail`
match, as required by the family lift). -/
private theorem implementationSpecification_corrupt_F_eq {t : SpecState P.n} {s : ImplementationState P.n}
    (hF : t.F = s.F) (id : Fin P.n) :
    (t.corrupt P id).F = (s.corrupt P id).F := by
  rw [ImplementationState.corrupt_F]
  unfold SpecState.corrupt
  by_cases hc : id ∉ s.F ∧ s.F.card < P.f
  · rw [if_pos (by rw [hF]; exact hc), if_pos hc]
    simp [hF]
  · rw [if_neg (by rw [hF]; exact hc), if_neg hc]
    exact hF

/-- **The per-instance GBCA refinement**: the round-`r` implementation
instance refines the round-`r` specification instance — a forward simulation
of the implementation by the specification along `specificationRelation`. -/
theorem refinesSpecification (P : Parameters) (r : ℕ) :
    ForwardSimulation (implementation P r) (specInst P r) (specificationRelation P r) := by
  constructor
  intro q1 q2 hR l μ1 hstep q1' hq1'
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
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      change Function.update q2.call id (some b) k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
    · intro b' hb'
      exact exclusionCertificate_send (by intro w hw; exact hw) (hRR.exclusion_certificate b' hb')
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
      exact ExclusionCertificate.mono (s := q1)
        (fun i' j' m' hm' => ImplementationState.mem_receiveMessage_received.mpr (Or.inr hm'))
        (fun k w hk => by simpa using hk) (Finset.Subset.refl _) (hRR.exclusion_certificate b hb)
    · intro hg
      obtain ⟨v0, i0, hi0⟩ := hRR.grade2_evidence hg
      exact ⟨v0, i0,
        le_trans hi0 (ImplementationState.receivedCount_le_receiveMessage q1 i j m i0 _)⟩
    · intro hg
      obtain ⟨i0, hi0⟩ := hRR.grade0_evidence hg
      exact ⟨i0, le_trans hi0 (ImplementationState.receivedCount_le_receiveMessage q1 i j m i0 _)⟩
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | voteBot j hin _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | bindBit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | bindBot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | byzantine j m hjF =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, hRR.exclusion_certificate, hRR.grade2_evidence,
      hRR.grade0_evidence, hRR.bound_excluded⟩
  | retGrade2 id v bnd _hin _hlv hcnt hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k₁, hk₁F, hbq⟩ := bind_receipts_of_echo5_quorum hRR.invariant hcnt
    obtain ⟨k, hkF, hvq⟩ :=
      voteQuorum_of_bind_receipts hRR.invariant (i := k₁) (v := v) (by omega)
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_grade2 q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_exclusionCertificate_of_voteQuorum hRR.invariant hvq (hRR.exclusion_certificate v hv)
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
        fun b hb => exclusionCertificate_setBound (exclusionCertificate_ret
          (hRR.exclusion_certificate b hb)),
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoReceiptQuorum_of_vote_receipts hRR.invariant (i := k) (v := v) (by omega))
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
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact exclusionCertificate_setBound
            (exclusionCertificate_ret (exclusionCertificate_of_voteQuorum hRR.invariant hvq))
        · exact exclusionCertificate_setBound (exclusionCertificate_ret (hRR.exclusion_certificate b
            hb))
  | retGrade1 id v bnd _hin _hlv _hnotGrade2 hcnt honce hbind hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k, hkF, hvq⟩ := voteQuorum_of_bind_receipts hRR.invariant hbind
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_grade1 q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_exclusionCertificate_of_voteQuorum hRR.invariant hvq (hRR.exclusion_certificate v hv)
    have hd : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some (!v) ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval (!v))
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade1 q2 id v v hlive hexcluded hexcluded hd hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => exclusionCertificate_setBound (exclusionCertificate_ret
          (hRR.exclusion_certificate b hb)),
        by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoReceiptQuorum_of_vote_receipts hRR.invariant (i := k) (v := v) (by omega))
      refine ⟨{ q2 with
        excluded := insert (!v) q2.excluded,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade1_run hq hw hlive hd0 hd hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, by simpa using hRR.grade2_evidence,
        by simpa using hRR.grade0_evidence, by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact exclusionCertificate_setBound
            (exclusionCertificate_ret (exclusionCertificate_of_voteQuorum hRR.invariant hvq))
        · exact exclusionCertificate_setBound (exclusionCertificate_ret (hRR.exclusion_certificate b
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
      have hcert : ExclusionCertificate P q1 (!bnd) := by
        rw [hbv]; exact exclusionCertificate_boundOf_grade0 hRR.invariant hcnt
      have hq : q2.quorum P := quorum_of_messageQuorum hRR
        (fun j hj hm' => hRR.invariant.input_called j true hj hm')
        (ImplementationState.bothValid_le hval true)
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
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b' hb'
        rw [Finset.mem_insert] at hb'
        rcases hb' with rfl | hb'
        · exact exclusionCertificate_setBound (exclusionCertificate_ret hcert)
        · exact exclusionCertificate_setBound (exclusionCertificate_ret (hRR.exclusion_certificate
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
        fun b hb' => exclusionCertificate_setBound (exclusionCertificate_ret
          (hRR.exclusion_certificate b hb')),
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simpa using hex⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2.corrupt P id,
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp) (Step.fail q2 id)⟩,
      hI', ?_, ?_, implementationSpecification_corrupt_F_eq hRR.F_eq id, ?_, ?_, ?_, ?_⟩
    · intro k
      rw [corrupt_call, ImplementationState.corrupt_process]
      exact hRR.call_eq k
    · intro k
      rw [corrupt_ret, ImplementationState.corrupt_process]
      exact hRR.ret_eq k
    · intro b hb
      rw [corrupt_excluded] at hb
      refine ExclusionCertificate.mono (s := q1) (fun i' j' m' hm' => ?_) (fun k w hk => ?_)
        (ImplementationState.corrupt_F_subset q1 id) (hRR.exclusion_certificate b hb)
      · rw [ImplementationState.corrupt_received]
        exact hm'
      · rw [ImplementationState.corrupt_process]
        exact hk
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨v0, i0, hi0⟩ := hRR.grade2_evidence hg
      exact ⟨v0, i0, by rw [ImplementationState.corrupt_receivedCount]; exact hi0⟩
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨i0, hi0⟩ := hRR.grade0_evidence hg
      exact ⟨i0, by rw [ImplementationState.corrupt_receivedCount]; exact hi0⟩
    · rw [corrupt_excluded, ImplementationState.corrupt_bound]
      exact hRR.bound_excluded

/-! ### Broadcast compatibility of the simulation relation

The round-indexed family lift of the refinement takes `fail` as a broadcast act, applied to every
round at once. It needs the per-round relation to be preserved by that act. The specification
corruption projections (`corrupt_call`/`corrupt_ret`/`corrupt_excluded`/`corrupt_grade`) come from
`ABA/GBCA/Specification.lean`; the two `corrupt` functions stay equal by
`implementationSpecification_corrupt_F_eq`. The statement is proved directly rather than through
`refinesSpecification`, whose `fail` case only yields an existential match. Its consumer is the
round instance's family lifting
(`ABA/Composition/GBCAInstanceByABDY/Substitution.lean`). -/

/-- **Broadcast compatibility**: `specificationRelation` is preserved by the synchronized corruption
of both systems. The two `corrupt`s share the guard `id ∉ F ∧ |F| < f` and `specificationRelation`
aligns the `F`s, so the `if`-conditions agree; every other field is untouched by corruption. -/
theorem specificationRelation_corrupt (P : Parameters) (r : ℕ) (id : Fin P.n)
    {x : ImplementationState P.n} {y : SpecState P.n} (h : specificationRelation P r x y) :
    specificationRelation P r (x.corrupt P id) (y.corrupt P id) := by
  have hR : SpecificationRelation P x y := h
  exact
    { invariant := hR.invariant.step (ImplementationStep.fail (r := r) x id)
        (by rw [PMF.mem_support_pure_iff])
      call_eq := fun k => by
        rw [corrupt_call, ImplementationState.corrupt_process]
        exact hR.call_eq k
      ret_eq := fun k => by
        rw [corrupt_ret, ImplementationState.corrupt_process]
        exact hR.ret_eq k
      F_eq := implementationSpecification_corrupt_F_eq hR.F_eq id
      exclusion_certificate := fun b hb => by
        rw [corrupt_excluded] at hb
        exact ExclusionCertificate.mono
          (fun i j m hm => by rw [ImplementationState.corrupt_received]; exact hm)
          (fun j w hw => by rw [ImplementationState.corrupt_process]; exact hw)
          (ImplementationState.corrupt_F_subset x id)
          (hR.exclusion_certificate b hb)
      grade2_evidence := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨v, i, hi⟩ := hR.grade2_evidence hg
        exact ⟨v, i, by rw [ImplementationState.corrupt_receivedCount]; exact hi⟩
      grade0_evidence := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨i, hi⟩ := hR.grade0_evidence hg
        exact ⟨i, by rw [ImplementationState.corrupt_receivedCount]; exact hi⟩
      bound_excluded := by
        rw [corrupt_excluded, ImplementationState.corrupt_bound]
        exact hR.bound_excluded }

/-! ### Binding at the implementation instance

Binding is stated on the labels of a trace (`BindingTrace`, `ABA/GBCA/SpecificationSafety.lean`),
so a trace-distribution inclusion carries it. The inclusion is the soundness of
`refinesSpecification`, and `safety_transfer` moves the property across it. -/

/-- The soundness inclusion of the per-instance refinement: every trace
distribution achievable by the round-`r` implementation instance is achievable
by the round-`r` specification instance. -/
theorem implementation_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (implementation P r) ⊆ achievableTraceDists (specInst P r) :=
  (ForwardSimulation.toProbabilistic (implementation_isLTS P r) (specInst_isLTS P r)
    (specificationRelation_init P r) (refinesSpecification P r)).achievableTraceDists_subset

/-- **Binding of the implementation instance, on a trace.** Every
positive-probability trace of the round-`r` implementation instance is bound to
one bit: all its round-`r` returns announce that bit, and every one of them that
hands out a value hands out it. The specification has the property
(`specInst_binding`) and `implementation_refines` includes the trace distributions. -/
theorem implementation_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (implementation P r), ∀ t, D t ≠ 0 →
      BindingTrace P r t :=
  safety_transfer (implementation_refines P r) (specInst_binding P r)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.implementation_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implementation_refines

/-- info: 'PLTS.ABA.GBCA.ByABDY.implementation_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implementation_binding

end GBCA.ByABDY
end ABA
end PLTS
