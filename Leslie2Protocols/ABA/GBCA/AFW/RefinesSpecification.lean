/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.SpecificationRelation
import Leslie2Protocols.Framework.FamilySimulation

/-!
# The refinement of the round over the gather specifications

`GBCA.ByAFW.refinesSpecification`: the round over the gather specifications
(`GBCA.ByAFW.roundOverGatherSpecifications`, `ABA/GBCA/AFW/Composition.lean`) forward-simulates the
graded agreement specification read over the round's interface
(`GBCA.specificationOverRoundAlphabet`), along `GBCA.ByAFW.SpecificationRelation`
(`ABA/GBCA/AFW/SpecificationRelation.lean`).

A transition of the round is one case of `GBCA.ByAFW.AlgorithmOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_row`), `specificationRelation_row` answers that
case by a weak run of the graded agreement specification with the relation restored, and
`refinesSpecification` lifts the run to the interface along a section of
`GBCA.specificationLabelMap`.

The runs are at most two steps — `bindUnset ; ret` through `weakLStep_tauThen`. The long commit
chains live one tier down, inside the gather instances' own internal transitions.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Parameters}

/-! ### The row-wise step -/

/-- **The row-wise step**: every row of the round is answered by a weak run of the graded agreement
specification, the relation restored. -/
theorem specificationRelation_row (P : Parameters) (r : ℕ)
    (q₁ : RoundStateOverGatherSpecifications P.n) (q₂ : GBCA.SpecState P.n)
    (hR : SpecificationRelation P q₁ q₂) (l₀ : Label P.n)
    (μ : PMF (RoundStateOverGatherSpecifications P.n))
    (hrow : AlgorithmOverGatherSpecifications P r q₁ l₀ μ)
    (q₁' : RoundStateOverGatherSpecifications P.n)
    (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLSilent q₂ q₂') ∨
      (¬ l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLStep q₂ l₀ q₂')) ∧
      SpecificationRelation P q₁' q₂' := by
  have hInv' := hR.invariant.step hrow hq₁'
  cases hrow with
  | callG id b t1 h0 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall))⟩,
        hInv', ?_, ?_, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      · intro k
        dsimp only [firstGather_setFirstGather]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hk, Function.update_of_ne hk]
          exact hR.call_eq k
      · intro k
        dsimp only [programs_setFirstGather, programs_setPrograms]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          exact hR.ret_eq k
        · rw [Function.update_of_ne hk]
          exact hR.ret_eq k
    | callLoop id' b' =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (GBCA.Step.callLoop q₂ id b)⟩, hInv', hR.call_eq, ?_, hR.F_eq,
        hR.exclusion_certificate, hR.excluded_bound, hR.grade2_evidence, hR.grade0_evidence⟩
      intro k
      dsimp only [programs_setFirstGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | callLoop id b t1 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall))⟩,
        hInv', ?_, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      intro k
      dsimp only [firstGather_setFirstGather]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.call_eq k
    | callLoop id' b' =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (GBCA.Step.callLoop q₂ id b)⟩, hR⟩
  | firstGatherTau t1 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
    | bindCore S h0 hval hcard =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      intro b hb
      obtain ⟨S', hS', -⟩ := hR.exclusion_certificate b hb
      rw [h0] at hS'
      exact absurd hS' (by simp)
  | secondGatherTau t2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
    | bindCore S h0 hval hcard =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        ?_, ?_⟩
      · intro hg
        obtain ⟨S', v, hS', -⟩ := hR.grade2_evidence hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro hg
        obtain ⟨S', hS', -⟩ := hR.grade0_evidence hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
  | firstGatherReturn id g C t1 hin hc h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.exclusion_certificate, ?_, hR.grade2_evidence,
        hR.grade0_evidence⟩
      · intro k
        dsimp only [programs_setBound, programs_setFirstGather, programs_setPrograms]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          exact hR.ret_eq k
        · rw [Function.update_of_ne hk]
          exact hR.ret_eq k
      · intro b hb
        obtain ⟨β, hβ, hbβ⟩ := hR.excluded_bound b hb
        exact ⟨β, by dsimp only [bound_setBound]; rw [hβ]; rfl, hbβ⟩
  | secondGatherCall id x t2 hc h2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨hval2, hcore2, hF2⟩ := call_unchanged h
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
      hR.call_eq, ?_, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound, ?_, ?_⟩
    · intro k
      dsimp only [programs_setSecondGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
    · intro hg
      obtain ⟨S, v, hS, hh⟩ := hR.grade2_evidence hg
      exact ⟨S, v, by dsimp only [secondGather_setSecondGather,
        secondGather_setPrograms]; rw [hcore2]; exact hS, hh⟩
    · intro hg
      obtain ⟨S, hS, hl⟩ := hR.grade0_evidence hg
      exact ⟨S, by dsimp only [secondGather_setSecondGather,
        secondGather_setPrograms]; rw [hcore2]; exact hS, hl⟩
  | secondGatherReturn id g C t2 h2 ho h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      intro k
      dsimp only [programs_setSecondGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | retG id out ho hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hf := P.hResilience
    obtain ⟨hbnd, hcert⟩ := hR.invariant.out_certificate id out ho
    have hretflag : q₂.ret id = false := by
      rw [hR.ret_eq id]
      exact hr
    obtain ⟨β, hβ⟩ : ∃ β, bound q₁ = some β := Option.ne_none_iff_exists'.mp hbnd
    obtain ⟨S, hS, hβS⟩ := hR.invariant.bound_core β hβ
    have hScard : P.n - P.f ≤ S.card := hR.invariant.firstGatherCore_card S hS
    have hSval := hR.invariant.firstGatherCore_val S hS
    have hBelowThreshold : ExclusionEvidence P q₁ (!β) :=
      ⟨S, hS, by rw [hβS]; exact count_boundOfCore_belowThreshold hScard⟩
    have hexcl : ∀ b ∈ q₂.excluded, b = !β := by
      intro b hb
      obtain ⟨β', hβ', rfl⟩ := hR.excluded_bound b hb
      rw [hβ] at hβ'
      obtain rfl : β = β' := Option.some.inj hβ'
      rfl
    have hret_eq : ∀ k, Function.update q₂.ret id true k =
        (programs (setPrograms q₁ (Function.update (programs q₁) id
          { programs q₁ id with output := none, returned := true })) k).returned := by
      intro k
      dsimp only [programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.ret_eq k
    have hbndeq : (bound q₁).getD (boundOfCore P (∅ : AcceptedPairs P.n Bool)) = β := by
      rw [hβ]
      rfl
    rw [hbndeq]
    cases out with
    | grade2 v =>
      obtain ⟨⟨C₂, hC₂, hA_ev⟩, S', hS', hAboveThreshold⟩ := hcert
      obtain rfl : S = S' := by
        rw [hS] at hS'; exact Option.some.inj hS'
      have hC₂card : P.n - P.f ≤ C₂.card := hR.invariant.secondGatherCore_card C₂ hC₂
      have hβv : β = v := by
        rw [hβS]
        exact boundOfCore_of_aboveThreshold hScard hAboveThreshold
      have hlive : v ∉ q₂.excluded := by
        intro hv
        have hb := hexcl v hv
        rw [hβv] at hb
        simp at hb
      have hgA : q₂.grade = none ∨ q₂.grade = some true := by
        rcases hgr : q₂.grade with _ | b
        · exact Or.inl rfl
        · cases b
          · exfalso
            obtain ⟨S₂, hS₂, hCoreBelowThreshold⟩ := hR.grade0_evidence hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hCoreBelowThreshold v
            omega
          · exact Or.inr rfl
      by_cases hbv : (!v) ∈ q₂.excluded
      · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade2 q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
            hgA hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_certificate,
          hR.excluded_bound, ?_, ?_⟩
        · intro _
          exact ⟨C₂, v, hC₂, hA_ev⟩
        · intro hgr
          exact absurd hgr (by simp)
      · have hd0 : q₂.excluded = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro b' hb'
          have hb := hexcl b' hb'
          rw [hβv] at hb
          subst hb
          exact hbv hb'
        have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
            { q₂ with excluded := insert (!v) q₂.excluded } :=
          GBCA.Step.bindUnset q₂ (!v)
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance hSval hScard)
            (by
              rw [Bool.not_not]
              exact callSupport_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
                hSval (by omega))
            hd0
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.grade2 v) β)
            { q₂ with
              excluded := insert (!v) q₂.excluded
              grade := some true
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade2 _ id v β (by rw [hd0]; simp)
            (Finset.mem_insert_self _ _)
            (by rw [hβv]; exact Finset.mem_insert_self _ _) hgA hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, ?_⟩
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · rw [← hβv]
            exact hBelowThreshold
          · simp at hb
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact ⟨β, hβ, by rw [hβv]⟩
          · simp at hb
        · intro _
          exact ⟨C₂, v, hC₂, hA_ev⟩
        · intro hgr
          exact absurd hgr (by simp)
    | grade1 v =>
      obtain ⟨⟨S', hS', hAboveThreshold⟩, hw1⟩ := hcert
      obtain rfl : S = S' := by
        rw [hS] at hS'; exact Option.some.inj hS'
      have hβv : β = v := by
        rw [hβS]
        exact boundOfCore_of_aboveThreshold hScard hAboveThreshold
      have hlive : v ∉ q₂.excluded := by
        intro hv
        have hb := hexcl v hv
        rw [hβv] at hb
        simp at hb
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some (!v) ∨ id' ∈ q₂.F)).card :=
        callSupport_of_firstGatherSupport hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
          hw1
      by_cases hbv : (!v) ∈ q₂.excluded
      · exact ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade1 q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
            hw hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_certificate,
          hR.excluded_bound, hR.grade2_evidence, hR.grade0_evidence⟩
      · have hd0 : q₂.excluded = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro b' hb'
          have hb := hexcl b' hb'
          rw [hβv] at hb
          subst hb
          exact hbv hb'
        have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
            { q₂ with excluded := insert (!v) q₂.excluded } :=
          GBCA.Step.bindUnset q₂ (!v)
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance hSval hScard)
            (by
              rw [Bool.not_not]
              exact callSupport_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
                hSval (by omega))
            hd0
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.grade1 v) β)
            { q₂ with
              excluded := insert (!v) q₂.excluded
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade1 _ id v β (by rw [hd0]; simp)
            (Finset.mem_insert_self _ _)
            (by rw [hβv]; exact Finset.mem_insert_self _ _) hw hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, hR.grade2_evidence,
          hR.grade0_evidence⟩
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · rw [← hβv]
            exact hBelowThreshold
          · simp at hb
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact ⟨β, hβ, by rw [hβv]⟩
          · simp at hb
    | grade0 =>
      obtain ⟨⟨C₂, hC₂, hCoreBelowThreshold⟩, hsupp1⟩ := hcert
      have hC₂card : P.n - P.f ≤ C₂.card := hR.invariant.secondGatherCore_card C₂ hC₂
      have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some b ∨ id' ∈ q₂.F)).card := fun b =>
        callSupport_of_firstGatherSupport hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
          (hsupp1 b)
      have hgC : q₂.grade = none ∨ q₂.grade = some false := by
        rcases hgr : q₂.grade with _ | b
        · exact Or.inl rfl
        · cases b
          · exact Or.inr rfl
          · exfalso
            obtain ⟨S₂, v', hS₂, hh⟩ := hR.grade2_evidence hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hCoreBelowThreshold v'
            omega
      by_cases hdne : q₂.excluded = ∅
      · have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
            { q₂ with excluded := insert (!β) q₂.excluded } :=
          GBCA.Step.bindUnset q₂ (!β)
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance hSval hScard)
            (by rw [Bool.not_not]; exact hsupp β)
            hdne
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!β) q₂.excluded } (.retG r id .grade0 β)
            { q₂ with
              excluded := insert (!β) q₂.excluded
              grade := some false
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade0 _ id β (Finset.mem_insert_self _ _)
            (hsupp true) (hsupp false) hgC hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, ?_⟩
        · intro b hb
          dsimp only at hb
          rw [hdne, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact hBelowThreshold
          · simp at hb
        · intro b hb
          dsimp only at hb
          rw [hdne, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact ⟨β, hβ, rfl⟩
          · simp at hb
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hCoreBelowThreshold⟩
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hdne
        have hbeq := hexcl b hb
        subst hbeq
        refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade0 q₂ id β hb (hsupp true) (hsupp false) hgC hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_certificate,
          hR.excluded_bound, ?_, ?_⟩
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hCoreBelowThreshold⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (GBCA.Step.fail q₂ id)⟩, specificationRelation_corrupt (r := r) hR id⟩

/-! ### The refinement -/

/-- **The refinement of the round over the gather specifications**: the round
forward-simulates the graded agreement specification read over the round's
interface. A transition of the round is one case of `GBCA.ByAFW.AlgorithmOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_row`), the row is answered by a weak run of the
specification (`specificationRelation_row`), and that run is lifted to the interface along a
section of `GBCA.specificationLabelMap`. -/
theorem refinesSpecification (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverGatherSpecifications P r)
      (GBCA.specificationOverRoundAlphabet P r) (SpecificationRelation P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := roundOverGatherSpecifications_step_row P r q₁ l μ hstep
  obtain ⟨t', hdis, hrel⟩ := specificationRelation_row P r q₁ q₂ hR l₀ μ hrow q₁' hq₁'
  refine ⟨t', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨GBCA.specificationLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      GBCA.weakLSilent_specificationOverRoundAlphabet P r hweak⟩
  · refine Or.inr ⟨?_, GBCA.weakLStep_specificationOverRoundAlphabet P r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : GBCA.specificationLabelMap P.n (Silent.τ : Composition.ExtendedLabel P.n) = some l₀ :=
      by
      rw [← hl]; exact hpull
    rw [GBCA.specificationLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesSpecification

end GBCA.ByAFW
end ABA
end PLTS
