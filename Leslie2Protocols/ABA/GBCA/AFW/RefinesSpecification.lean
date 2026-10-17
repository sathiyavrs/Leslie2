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
(`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm`), `specificationRelation_transition`
matches that case by a weak run of the graded agreement specification with the relation restored,
and `refinesSpecification` lifts the run to the interface along a section of
`GBCA.specificationLabelMap`.

A call is matched by the specification's call or its loop, the round's announcement of the bound
bit by the specification's announcement, and corruption by the specification's corruption, each
in one step (`specificationRelation_singleStep`). The round's return is matched by its return,
preceded by `bindUnset` at the round's first return. Every internal transition of the round is
matched by no transition; the commit chains are internal transitions of the gather instances.

`refinesSpecification_untouchedFirstStep` is the first-step hypothesis of the family congruence
(`ForwardSimulation.family`): at a round whose programs hold no grade, the state a family reads at
an untouched round, a transition on a label the round owns is matched by one transition of the
specification on the same label.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Parameters}

/-! ### The transitions matched by one step -/

/-- **A visible transition other than a return, matched by one step.** A call, an announcement
of the bound bit or a corruption of the round is matched by one transition of the specification
at the label `GBCA.specificationLabelMap` sends it to, the relation restored. -/
theorem specificationRelation_singleStep (P : Parameters) (r : ℕ)
    {q₁ : RoundStateOverGatherSpecifications P.n} {q₂ : GBCA.SpecState P.n}
    (hR : SpecificationRelation P q₁ q₂) {l : Composition.ExtendedLabel P.n Empty}
    {μ : PMF (RoundStateOverGatherSpecifications P.n)}
    (htransition : AlgorithmOverGatherSpecifications P r q₁ l μ)
    (hl : l ≠ Sum.inl Label.tau) (hret : ∀ id out, l ≠ Sum.inl (.retG r id out))
    {q₁' : RoundStateOverGatherSpecifications P.n} (hq₁' : q₁' ∈ μ.support) :
    ∃ l₀, GBCA.specificationLabelMap P.n l = some l₀ ∧
      ∃ q₂', (GBCA.specInst P r).step q₂ l₀ (PMF.pure q₂') ∧ SpecificationRelation P q₁' q₂' := by
  have hInv' := hR.invariant.step htransition hq₁'
  cases htransition with
  | callG l' id b hl' t1 h0 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, hl', ?_⟩
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall),
        hInv', ?_, ?_, hR.F_eq, hR.exclusion_witness, hR.excluded_bound, hR.returned_excluded,
        hR.grade2_witness, hR.grade0_witness⟩
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
      refine ⟨q₂, GBCA.Step.callLoop q₂ id b, hInv', hR.call_eq, ?_, hR.F_eq,
        hR.exclusion_witness, hR.excluded_bound, hR.returned_excluded, hR.grade2_witness,
        hR.grade0_witness⟩
      intro k
      dsimp only [programs_setFirstGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | callLoop l' id b hl' t1 hin h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, hl', ?_⟩
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall),
        hInv', ?_, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
        hR.returned_excluded, hR.grade2_witness, hR.grade0_witness⟩
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
      exact ⟨q₂, GBCA.Step.callLoop q₂ id b, hR⟩
  | firstGatherTau t1 h => exact absurd rfl hl
  | secondGatherTau t2 h => exact absurd rfl hl
  | firstGatherReturn id g t1 hin hc h => exact absurd rfl hl
  | firstGatherReturnLoop id g t1 hloop h => exact absurd rfl hl
  | firstGatherCore C hC => exact absurd rfl hl
  | secondGatherCall id x t2 hc h2 h => exact absurd rfl hl
  | secondGatherReturn id g t2 h2 ho h => exact absurd rfl hl
  | secondGatherReturnLoop id g t2 hloop h => exact absurd rfl hl
  | retG id out ho hr => exact absurd rfl (hret id out)
  | announceBound C hC hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨S, hS, hex⟩ := hR.returned_excluded hr
    have hCS : S = C := by
      have hC' := hR.invariant.recordedCore_eq C hC
      rw [hS] at hC'
      exact Option.some.inj hC'
    subst hCS
    exact ⟨_, rfl, q₂, GBCA.Step.announceBound q₂ (boundOfCore P S) hex, hR⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨_, rfl, q₂.corrupt P id, GBCA.Step.fail q₂ id,
      specificationRelation_corrupt (r := r) hR id⟩

/-- A visible transition matched by one step is matched by a weak run of one transition. -/
theorem weakRun_of_singleStep {r : ℕ} {q₁' : RoundStateOverGatherSpecifications P.n}
    {q₂ : GBCA.SpecState P.n} {l : Composition.ExtendedLabel P.n Empty}
    (hl : l ≠ Sum.inl Label.tau)
    (h : ∃ l₀, GBCA.specificationLabelMap P.n l = some l₀ ∧
      ∃ q₂', (GBCA.specInst P r).step q₂ l₀ (PMF.pure q₂') ∧ SpecificationRelation P q₁' q₂') :
    ∃ l₀, GBCA.specificationLabelMap P.n l = some l₀ ∧
      ∃ q₂', ((l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLSilent q₂ q₂') ∨
        (¬ l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLStep q₂ l₀ q₂')) ∧
        SpecificationRelation P q₁' q₂' := by
  obtain ⟨l₀, hl₀, q₂', hstep, hR'⟩ := h
  have hne : ¬ l₀ = Silent.τ := fun h0 =>
    hl (GBCA.specificationLabelMap_eq_tau (by rw [hl₀, h0]; rfl))
  exact ⟨l₀, hl₀, q₂', Or.inr ⟨hne, System.weakLStep_of_step hne hstep⟩, hR'⟩

/-! ### The step, transition by transition -/

/-- **The step, transition by transition**: every transition of the round is matched by a weak run
of the graded-agreement specification at the label `GBCA.specificationLabelMap` sends it to, the
relation restored. -/
theorem specificationRelation_transition (P : Parameters) (r : ℕ)
    (q₁ : RoundStateOverGatherSpecifications P.n) (q₂ : GBCA.SpecState P.n)
    (hR : SpecificationRelation P q₁ q₂) (l : Composition.ExtendedLabel P.n Empty)
    (μ : PMF (RoundStateOverGatherSpecifications P.n))
    (htransition : AlgorithmOverGatherSpecifications P r q₁ l μ)
    (q₁' : RoundStateOverGatherSpecifications P.n) (hq₁' : q₁' ∈ μ.support) :
    ∃ l₀, GBCA.specificationLabelMap P.n l = some l₀ ∧
      ∃ q₂', ((l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLSilent q₂ q₂') ∨
        (¬ l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLStep q₂ l₀ q₂')) ∧
        SpecificationRelation P q₁' q₂' := by
  have hInv' := hR.invariant.step htransition hq₁'
  cases htransition with
  | callG _ id b hl' t1 h0 h =>
    obtain ⟨-, -, -, hlτ⟩ := callLabel_maps hl'
    refine weakRun_of_singleStep hlτ (specificationRelation_singleStep P r hR
      (.callG _ l id b hl' t1 h0 h) hlτ ?_ hq₁')
    rintro id' out rfl
    simp at hl'
  | callLoop _ id b hl' t1 hin h =>
    obtain ⟨-, -, -, hlτ⟩ := callLabel_maps hl'
    refine weakRun_of_singleStep hlτ (specificationRelation_singleStep P r hR
      (.callLoop _ l id b hl' t1 hin h) hlτ ?_ hq₁')
    rintro id' out rfl
    simp at hl'
  | announceBound C hC hr =>
    exact weakRun_of_singleStep (by simp) (specificationRelation_singleStep P r hR
      (.announceBound _ C hC hr) (by simp) (by simp) hq₁')
  | fail id =>
    exact weakRun_of_singleStep (by simp) (specificationRelation_singleStep P r hR
      (.fail _ id) (by simp) (by simp) hq₁')
  | firstGatherTau t1 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
        hR.returned_excluded, hR.grade2_witness, hR.grade0_witness⟩
    | bindCore S h0 hval hcard =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, ?_, ?_, ?_, hR.grade2_witness, hR.grade0_witness⟩
      · intro b hb
        obtain ⟨S', hS', -⟩ := hR.exclusion_witness b hb
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro b hb
        obtain ⟨S', hS', -⟩ := hR.excluded_bound b hb
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro hret
        obtain ⟨S', hS', -⟩ := hR.returned_excluded hret
        rw [h0] at hS'
        exact absurd hS' (by simp)
  | secondGatherTau t2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
        hR.returned_excluded, hR.grade2_witness, hR.grade0_witness⟩
    | bindCore S h0 hval hcard =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
        hR.returned_excluded, ?_, ?_⟩
      · intro hg
        obtain ⟨S', v, hS', -⟩ := hR.grade2_witness hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro hg
        obtain ⟨S', hS', -⟩ := hR.grade0_witness hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
  | firstGatherReturn id g t1 hin hc h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret _ _ C hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.exclusion_witness, hR.excluded_bound, hR.returned_excluded,
        hR.grade2_witness, hR.grade0_witness⟩
      intro k
      dsimp only [programs_setFirstGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | firstGatherReturnLoop id g t1 hloop h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret _ _ C hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
        hR.returned_excluded, hR.grade2_witness, hR.grade0_witness⟩
  | firstGatherCore C hC =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨_, rfl, q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
      hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
      hR.returned_excluded, hR.grade2_witness, hR.grade0_witness⟩
  | secondGatherCall id x t2 hc h2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    obtain ⟨hval2, hcore2, hF2⟩ := call_unchanged h
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
      hR.call_eq, ?_, hR.F_eq, hR.exclusion_witness, hR.excluded_bound, hR.returned_excluded,
      ?_, ?_⟩
    · intro k
      dsimp only [programs_setSecondGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
    · intro hg
      obtain ⟨S, v, hS, hh⟩ := hR.grade2_witness hg
      exact ⟨S, v, by dsimp only [secondGather_setSecondGather,
        secondGather_setPrograms]; rw [hcore2]; exact hS, hh⟩
    · intro hg
      obtain ⟨S, hS, hl⟩ := hR.grade0_witness hg
      exact ⟨S, by dsimp only [secondGather_setSecondGather,
        secondGather_setPrograms]; rw [hcore2]; exact hS, hl⟩
  | secondGatherReturn id g t2 h2 ho h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret _ _ C hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.exclusion_witness, hR.excluded_bound, hR.returned_excluded,
        hR.grade2_witness, hR.grade0_witness⟩
      intro k
      dsimp only [programs_setSecondGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | secondGatherReturnLoop id g t2 hloop h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret _ _ C hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_witness, hR.excluded_bound,
        hR.returned_excluded, hR.grade2_witness, hR.grade0_witness⟩
  | retG id out ho hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨_, rfl, ?_⟩
    have hf := P.hResilience
    obtain ⟨hcoreS, hcert⟩ := hR.invariant.out_witness id out ho
    have hretflag : q₂.ret id = false := by
      rw [hR.ret_eq id]
      exact hr
    obtain ⟨S, hS⟩ : ∃ S, (firstGather q₁).core = some S := Option.ne_none_iff_exists'.mp hcoreS
    have hScard : P.n - P.f ≤ S.card := hR.invariant.firstGatherCore_card S hS
    have hSval := hR.invariant.firstGatherCore_val S hS
    have hBelowThreshold : ExclusionWitness P q₁ (!boundOfCore P S) :=
      ⟨S, hS, count_boundOfCore_belowThreshold hScard⟩
    have hexcl : ∀ b ∈ q₂.excluded, b = !boundOfCore P S := by
      intro b hb
      obtain ⟨S', hS', rfl⟩ := hR.excluded_bound b hb
      rw [hS] at hS'
      obtain rfl : S = S' := Option.some.inj hS'
      rfl
    have hret_eq : ∀ k, Function.update q₂.ret id true k =
        (programs (setNetwork (setPrograms q₁ (Function.update (programs q₁) id
          { programs q₁ id with output := none, returned := true }))
          { network q₁ with returned := true }) k).returned := by
      intro k
      dsimp only [programs_setNetwork, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.ret_eq k
    cases out with
    | grade2 v =>
      obtain ⟨⟨C₂, hC₂, hA_ev⟩, S', hS', hAboveThreshold⟩ := hcert
      obtain rfl : S = S' := by
        rw [hS] at hS'; exact Option.some.inj hS'
      have hC₂card : P.n - P.f ≤ C₂.card := hR.invariant.secondGatherCore_card C₂ hC₂
      have hβv : boundOfCore P S = v := boundOfCore_of_aboveThreshold hScard hAboveThreshold
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
            obtain ⟨S₂, hS₂, hCoreBelowThreshold⟩ := hR.grade0_witness hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hCoreBelowThreshold v
            omega
          · exact Or.inr rfl
      by_cases hbv : (!v) ∈ q₂.excluded
      · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade2 q₂ id v hlive hbv hgA hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_witness,
          hR.excluded_bound, ?_, ?_, ?_⟩
        · intro _
          exact ⟨S, hS, by rw [hβv]; exact hbv⟩
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
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call hSval hScard)
            (by
              rw [Bool.not_not]
              exact callSupport_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call
                hSval (by omega))
            hd0
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.grade2 v))
            { q₂ with
              excluded := insert (!v) q₂.excluded
              grade := some true
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade2 _ id v (by rw [hd0]; simp) (Finset.mem_insert_self _ _) hgA hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, ?_, ?_⟩
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
          · exact ⟨S, hS, by rw [hβv]⟩
          · simp at hb
        · intro _
          exact ⟨S, hS, by rw [hβv]; exact Finset.mem_insert_self _ _⟩
        · intro _
          exact ⟨C₂, v, hC₂, hA_ev⟩
        · intro hgr
          exact absurd hgr (by simp)
    | grade1 v =>
      obtain ⟨⟨S', hS', hAboveThreshold⟩, hw1⟩ := hcert
      obtain rfl : S = S' := by
        rw [hS] at hS'; exact Option.some.inj hS'
      have hβv : boundOfCore P S = v := boundOfCore_of_aboveThreshold hScard hAboveThreshold
      have hlive : v ∉ q₂.excluded := by
        intro hv
        have hb := hexcl v hv
        rw [hβv] at hb
        simp at hb
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some (!v) ∨ id' ∈ q₂.F)).card :=
        callSupport_of_firstGatherSupport hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call
          hw1
      by_cases hbv : (!v) ∈ q₂.excluded
      · exact ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade1 q₂ id v hlive hbv hw hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_witness,
          hR.excluded_bound, fun _ => ⟨S, hS, by rw [hβv]; exact hbv⟩, hR.grade2_witness,
          hR.grade0_witness⟩
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
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call hSval hScard)
            (by
              rw [Bool.not_not]
              exact callSupport_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call
                hSval (by omega))
            hd0
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.grade1 v))
            { q₂ with
              excluded := insert (!v) q₂.excluded
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade1 _ id v (by rw [hd0]; simp) (Finset.mem_insert_self _ _) hw hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, hR.grade2_witness,
          hR.grade0_witness⟩
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
          · exact ⟨S, hS, by rw [hβv]⟩
          · simp at hb
        · intro _
          exact ⟨S, hS, by rw [hβv]; exact Finset.mem_insert_self _ _⟩
    | grade0 =>
      obtain ⟨⟨C₂, hC₂, hCoreBelowThreshold⟩, hsupp1⟩ := hcert
      have hC₂card : P.n - P.f ≤ C₂.card := hR.invariant.secondGatherCore_card C₂ hC₂
      have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some b ∨ id' ∈ q₂.F)).card := fun b =>
        callSupport_of_firstGatherSupport hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call
          (hsupp1 b)
      have hgC : q₂.grade = none ∨ q₂.grade = some false := by
        rcases hgr : q₂.grade with _ | b
        · exact Or.inl rfl
        · cases b
          · exact Or.inr rfl
          · exfalso
            obtain ⟨S₂, v', hS₂, hh⟩ := hR.grade2_witness hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hCoreBelowThreshold v'
            omega
      by_cases hdne : q₂.excluded = ∅
      · have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
            { q₂ with excluded := insert (!boundOfCore P S) q₂.excluded } :=
          GBCA.Step.bindUnset q₂ (!boundOfCore P S)
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_of_call hSval hScard)
            (by rw [Bool.not_not]; exact hsupp _)
            hdne
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!boundOfCore P S) q₂.excluded } (.retG r id .grade0)
            { q₂ with
              excluded := insert (!boundOfCore P S) q₂.excluded
              grade := some false
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade0 _ id (Finset.insert_ne_empty _ _) (hsupp true) (hsupp false) hgC
            hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, ?_, ?_⟩
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
          · exact ⟨S, hS, rfl⟩
          · simp at hb
        · intro _
          exact ⟨S, hS, Finset.mem_insert_self _ _⟩
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hCoreBelowThreshold⟩
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hdne
        have hbeq := hexcl b hb
        subst hbeq
        refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade0 q₂ id hdne (hsupp true) (hsupp false) hgC hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_witness,
          hR.excluded_bound, fun _ => ⟨S, hS, hb⟩, ?_, ?_⟩
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hCoreBelowThreshold⟩

/-! ### The refinement -/

/-- **The refinement of the round over the gather specifications**: the round
forward-simulates the graded agreement specification read over the round's
interface. A transition of the round is one case of `GBCA.ByAFW.AlgorithmOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm`), that transition is matched by a
weak run of the specification (`specificationRelation_transition`), and that run is lifted to the
interface along a section of `GBCA.specificationLabelMap`. -/
theorem refinesSpecification (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverGatherSpecifications P r)
      (GBCA.specificationOverRoundAlphabet P Empty r) (SpecificationRelation P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, t', hdis, hrel⟩ := specificationRelation_transition P r q₁ q₂ hR l μ
    ((roundOverGatherSpecifications_step_iff_algorithm P r q₁ l μ).mp hstep) q₁' hq₁'
  refine ⟨t', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨GBCA.specificationLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      GBCA.weakLSilent_specificationOverRoundAlphabet P Empty r hweak⟩
  · refine Or.inr ⟨?_, GBCA.weakLStep_specificationOverRoundAlphabet P Empty r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : GBCA.specificationLabelMap P.n
        (Silent.τ : Composition.ExtendedLabel P.n Empty) = some l₀ := by
      rw [← hl]; exact hpull
    rw [GBCA.specificationLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### The first step at an untouched round

The family of rounds (`System.family`) holds a round it has not touched as the initial round
under the broadcast actions applied so far. The family congruence asks that a transition on a
label the round owns, from such a state, be matched by a transition of the specification on that
label followed by a silent run (`ForwardSimulation.family`, `hUntouchedFirstStep`). The broadcast
actions leave the programs where they stand, so no program holds a grade there, the round has no
return to take, and every other visible transition is matched by one step. -/

/-- The broadcast actions leave the programs where they stand. -/
theorem programs_foldr {actC : Composition.ExtendedLabel P.n Empty →
      RoundStateOverGatherSpecifications P.n → RoundStateOverGatherSpecifications P.n}
    (hActPrograms : ∀ l x, programs (actC l x) = programs x)
    (initialC : RoundStateOverGatherSpecifications P.n) :
    ∀ broadcasts : List (Composition.ExtendedLabel P.n Empty),
      programs (broadcasts.foldr actC initialC) = programs initialC
  | [] => rfl
  | l :: broadcasts => by
    rw [List.foldr_cons, hActPrograms, programs_foldr hActPrograms initialC broadcasts]

/-- **The first step at an untouched round.** Let the broadcast actions `actC` leave the programs
where they stand, and let no program of `initialC` hold a grade. From related states reached by a
list of broadcasts, a transition of the round on a label the round owns is matched by one
transition of the specification on the same label. -/
theorem refinesSpecification_untouchedFirstStep (P : Parameters)
    (owns : Composition.ExtendedLabel P.n Empty → Option ℕ) (hOwnsSilent : owns Silent.τ = none)
    (actC : Composition.ExtendedLabel P.n Empty → RoundStateOverGatherSpecifications P.n →
      RoundStateOverGatherSpecifications P.n)
    (actA : Composition.ExtendedLabel P.n Empty → GBCA.SpecState P.n → GBCA.SpecState P.n)
    (initialC : RoundStateOverGatherSpecifications P.n) (initialA : GBCA.SpecState P.n)
    (hActPrograms : ∀ l x, programs (actC l x) = programs x)
    (hInitialOutput : ∀ k, (programs initialC k).output = none) :
    ∀ (r : ℕ) (broadcasts : List (Composition.ExtendedLabel P.n Empty))
      (l : Composition.ExtendedLabel P.n Empty), owns l = some r →
      SpecificationRelation P (broadcasts.foldr actC initialC) (broadcasts.foldr actA initialA) →
      ∀ μ, (roundOverGatherSpecifications P r).step (broadcasts.foldr actC initialC) l μ →
      ∀ x ∈ μ.support, ∃ y, SpecificationRelation P x y ∧
        ∃ ν, (GBCA.specificationOverRoundAlphabet P Empty r).step
          (broadcasts.foldr actA initialA) l ν ∧
          ∃ z ∈ ν.support, (GBCA.specificationOverRoundAlphabet P Empty r).weakLSilent z y := by
  intro r broadcasts l howns hR μ hstep x hx
  have hprog : programs (broadcasts.foldr actC initialC) = programs initialC :=
    programs_foldr hActPrograms initialC broadcasts
  generalize broadcasts.foldr actC initialC = x₀ at hR hstep hprog
  have hl : l ≠ Sum.inl Label.tau := by
    rintro rfl
    exact absurd (howns.symm.trans hOwnsSilent) (by simp)
  have htransition := (roundOverGatherSpecifications_step_iff_algorithm P r _ l μ).mp hstep
  have hret : ∀ id out, l ≠ Sum.inl (.retG r id out) := by
    rintro id out rfl
    cases htransition with
    | callG l' id' b hl' t1 h0 h => simp at hl'
    | callLoop l' id' b hl' t1 hin h => simp at hl'
    | retG id out ho hr =>
      rw [hprog, hInitialOutput id] at ho
      exact absurd ho (by simp)
  obtain ⟨l₀, hl₀, y, hstepA, hRxy⟩ :=
    specificationRelation_singleStep P r hR htransition hl hret hx
  exact ⟨y, hRxy, PMF.pure y, (System.mapIdle_step_some hl₀ _).mpr hstepA, y,
    (PMF.mem_support_pure_iff _ _).mpr rfl, System.weakLSilent_refl _ y⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesSpecification

/-- info: 'PLTS.ABA.GBCA.ByAFW.refinesSpecification_untouchedFirstStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesSpecification_untouchedFirstStep

end GBCA.ByAFW
end ABA
end PLTS
