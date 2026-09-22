/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# `Invariant` across the graded-agreement `τ` rows of `hybrid`

`Invariant.step_gbcaTau`, preservation of `Invariant` at `bindUnset`, the GBCA family's only
genuine `τ`-step, which excludes one bit of round `r`'s exclusion set. The value-transport corners
lean on the exclusion's own D15 guard: the spared bit `!b` keeps `f + 1` F-blind call support at
round `r`, whose derived correct caller determines `!b` at every standing commitment.
`down_settled`'s round-`r` corner needs "a call at round `r` implies current round `≥ r`", a fact
`Invariant` does not carry explicitly, and is handed off.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- `bindUnset` (the GBCA family's only genuine `τ`-step): excludes one bit of round `r`'s
exclusion set. `down_settled`'s round-`r` corner needs "a call at round `r` implies current
round `≥ r`", a fact `Invariant` doesn't carry explicitly — handed off. The value-transport
corners lean on the exclusion's own D15 guard: the spared bit `!b` keeps `f + 1` F-blind call
support at round `r`, whose derived correct caller determines `!b` at every standing
commitment. -/
theorem Invariant.step_gbcaTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    Invariant P (Function.update g r gr') c w ∧
      AbstractStateUnchanged P g (Function.update g r gr') c c := by
  cases hstep
  case bindUnset b _hq _hw hd0 =>
    rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
    have hb : b ∉ (g r).excluded := by
      rw [hd0]; simp
    set g' := Function.update g r { g r with excluded := insert b (g r).excluded } with hg'def
    have hFeq : ∀ r', (g' r').F = (g r').F := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hCalleq : ∀ r', (g' r').call = (g r').call := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hGradeeq : ∀ r', (g' r').grade = (g r').grade := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hExcludedSelf : (g' r).excluded = insert b (g r).excluded := by
      rw [hg'def, Function.update_self]
    have hExcludedNe : ∀ r', r' ≠ r → (g' r').excluded = (g r').excluded := by
      intro r' h; rw [hg'def, Function.update_of_ne h]
    have hExcludedMono : ∀ r' x, x ∈ (g r').excluded → x ∈ (g' r').excluded := by
      intro r' x hx
      by_cases h : r' = r
      · subst h; rw [hExcludedSelf]; exact Finset.mem_insert_of_mem hx
      · rw [hExcludedNe r' h]; exact hx
    obtain ⟨id0, hid0F, hcall0⟩ :=
      GBCA.exists_correct_caller _hw (by rw [hI.F_gbca r]; exact hI.F_card)
    have hFid0 : id0 ∉ c.F := by
      rw [← hI.F_gbca r]; exact hid0F
    have hClosedNe : ∀ r', r' ≠ r → (RoundSettled g' r' ↔ RoundSettled g r') :=
      fun r' h => RoundSettled.congr (hExcludedNe r' h) (hGradeeq r')
    have hClosedSelf : RoundSettled g' r := Or.inl (by rw [hExcludedSelf]; simp)
    have hDissTrans : ∀ r₀, DissentWitness P g c r₀ → DissentWitness P g' c r₀ := by
      intro r₀ hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hExcludedMono r₀ _ hbv, ?_⟩
      by_cases h0 : r₀ = 0
      · rw [if_pos h0] at hif ⊢; exact hif
      · rw [if_neg h0] at hif ⊢
        rcases hif with hh | hh
        · exact Or.inl (hExcludedMono (r₀ - 1) _ hh)
        · exact Or.inr ((hGradeeq (r₀ - 1)).trans hh)
    have hCarrTrans : ∀ r₀ id₀ v, OutcomeHolder P g' c r₀ id₀ v → OutcomeHolder P g c r₀ id₀ v := by
      intro r₀ id₀ v hc
      unfold OutcomeHolder at hc ⊢
      rwa [hCalleq (r₀ + 1)] at hc
    have hCommitTrans : ∀ r'' b'', (!b'') ∈ (g r'').excluded → Grade2Commitment P g c r'' b'' →
        Grade2Commitment P g' c r'' b'' := by
      rintro r'' b'' hres ⟨h1, h2, h3, h4⟩
      refine ⟨fun r₀ b₀ hrr hb' => ?_,
        fun r₀ id₀ b₀ hrr hmem hcall =>
          h2 r₀ id₀ b₀ hrr hmem (by rw [← hCalleq r₀]; exact hcall), h3,
        fun id₀ v hmem hcar => h4 id₀ v hmem (hCarrTrans r'' id₀ v hcar)⟩
      by_cases h3' : r₀ = r
      · subst h3'
        rw [hExcludedSelf] at hb'
        have hb₀nd : b₀ ∉ (g r₀).excluded := fun hh => hb'.2 (Finset.mem_insert_of_mem hh)
        rcases Finset.mem_insert.mp hb'.1 with hnew | hold
        · rcases eq_or_lt_of_le hrr with heq | hlt
          · have hne : b₀ ≠ !b'' := fun hh => hb₀nd (hh ▸ (heq ▸ hres))
            revert hne; cases b₀ <;> cases b'' <;> simp
          · have hb₀ : b₀ = !b := by revert hnew; cases b₀ <;> cases b <;> simp
            rw [hb₀]; exact h2 r₀ id0 (!b) hlt hFid0 hcall0
        · exact h1 r₀ b₀ hrr ⟨hold, hb₀nd⟩
      · rw [hExcludedNe r₀ h3'] at hb'; exact h1 r₀ b₀ hrr hb'
    have hCertTrans : ∀ r'' b'',
        Grade2Certificate P g c r'' b'' → Grade2Certificate P g' c r'' b'' := by
      rintro r'' b'' ⟨hg1, hd1, hcm⟩
      exact ⟨(hGradeeq r'').trans hg1, hExcludedMono r'' _ hd1, hCommitTrans r'' b'' hd1 hcm⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin => hpin⟩
    refine ⟨hI.corrupted_F, fun r' => (hFeq r').trans (hI.F_gbca r'), hI.F_wcc, hI.F_card,
      ?_, ?_, hI.phase_input,
      ?_, ?_, ?_,
      hI.received_sound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.round_flip, hI.estimate0, ?_, ?_,
      ?_, ?_, ?_, ?_, hI.estimate_previous_ne, hI.wcc_order, ?_, hI.wcc_callRound, ?_,
      hI.idle_no_wccCall, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r₀ i j v v' hm hm' h h' => (hI.outcomeHolder_agree r₀ i j v v' hm hm'
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h')).imp (fun x => x)
        (fun hh => (hGradeeq r₀).trans hh),
      hI.grade2Lock_agree⟩
    · intro id b' hmem hcall; rw [hCalleq] at hcall; exact hI.input_gbcaRound0 id b' hmem hcall
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.input_called r' id hmem hcall
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · by_cases h1 : r' + 1 = r
        · -- the fresh exclusion at `r' + 1` had a correct caller of the spared bit, whose
          -- round progress closes `r'`
          obtain ⟨id0, hid0F, hcall0⟩ :=
            GBCA.exists_correct_caller _hw (by rw [hI.F_gbca r]; exact hI.F_card)
          have hFid0 : id0 ∉ c.F := by
            rw [← hI.F_gbca r]; exact hid0F
          have hcr : r ≤ (c.processes id0).round :=
            hI.call_round r id0 hFid0 (by rw [hcall0]; simp)
          rw [hClosedNe r' h2]
          exact hI.round_bound id0 hFid0 r' (by omega)
        · rw [hClosedNe r' h2]
          exact hI.down_settled r' ((hClosedNe (r' + 1) h1).mp h)
    · obtain ⟨R, hR⟩ := hI.quiescent
      exact ⟨max R (r + 1), fun r' hr' h =>
        hR r' (by omega) ((hClosedNe r' (by omega)).mp h)⟩
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.wcc_bound r' h
    · intro id b' hmem h
      exact (hI.decided_source id b' hmem h).imp (fun r'' => hCertTrans r'' b')
    · intro r' b' hgr hbr
      rw [hGradeeq] at hgr
      have hpair : (!b') ∈ (g r').excluded ∧ b' ∉ (g r').excluded := by
        by_cases h2 : r' = r
        · subst h2
          rw [hExcludedSelf] at hbr
          refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
          rcases Finset.mem_insert.mp hbr.1 with hnew | hold
          · -- the fresh exclusion is `!b'`: the grade-2-locked round already had an excluded bit,
            -- which can be neither `b` (`hb`) nor `b'` (still alive), so it is `!b'`
            obtain ⟨wd, hwd⟩ :=
              Finset.nonempty_iff_ne_empty.mpr (hI.grade2_needs_bind r' hgr)
            have hwb : wd ≠ b := fun hh => hb (hh ▸ hwd)
            have hwb' : wd ≠ b' := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
            have hwd' : wd = !b' := by
              revert hwb hwb' hnew; cases wd <;> cases b' <;> cases b <;> simp
            exact hwd' ▸ hwd
          · exact hold
        · rw [hExcludedNe r' h2] at hbr; exact hbr
      exact hCommitTrans r' b' hpair.1 (hI.grade2Lock_commit r' b' hgr hpair)
    · intro id hmem r' hround
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.round_bound id hmem r' hround
    · intro r' v hlast hbr hcoin id hmem hround
      by_cases h1 : r' + 1 = r
      · exfalso
        have hemp : (g' (r' + 1)).excluded = ∅ := hlast.2
        rw [h1, hExcludedSelf] at hemp; exact absurd hemp (by simp)
      · by_cases h2 : r' = r
        · have hExcludedSelf' : (g' r').excluded = insert b (g r').excluded := by
            rw [h2]; exact hExcludedSelf
          have hbAt : b ∉ (g r').excluded := by
            rw [h2]; exact hb
          have hemp1 : (g (r' + 1)).excluded = ∅ := by
            rw [← hExcludedNe (r' + 1) h1]; exact hlast.2
          by_cases hexcluded0 : (g r').excluded = ∅
          · -- round `r'` was fresh before this exclusion, hence already grade-0-blocked upward;
            -- `estimate_previous` fixes `id`'s estimate at the agreeing coin's bit.
            have hnoC : (g (r' + 1)).grade ≠ some false :=
              fun hh => hI.no_grade0Lock_succ r' v hcoin (by rw [hexcluded0]; simp) hh
            have hround1 : (c.processes id).round = r' + 1 := by
              by_contra hne
              rcases hI.round_bound id hmem (r' + 1) (by omega) with hh | hh
              · exact hh hemp1
              · exact hnoC hh
            by_cases hgroup : (c.processes id).phase = .toCallW ∨ (c.processes id).phase = .awaitW
            · exfalso
              obtain ⟨hnone, hsome⟩ := hI.estimate_ret (r' + 1) id hmem hround1 hgroup
              rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with he | ⟨u, he⟩
              · exact hnoC (hnone he).1
              · have hu := hsome u he
                rw [hemp1] at hu; exact absurd hu (by simp)
            · have hphase3 : (c.processes id).phase = .idle ∨ (c.processes id).phase = .toCallG ∨
                  (c.processes id).phase = .awaitG := by
                rcases hph2 : (c.processes id).phase with _ | _ | _ | _ | _
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr rfl)
                · exact absurd (Or.inl hph2) hgroup
                · exact absurd (Or.inr hph2) hgroup
              obtain ⟨u, he⟩ :=
                Option.ne_none_iff_exists'.mp (hI.estimate_previous_ne id hmem (by omega) hphase3)
              rw [he]
              rcases hI.estimate_previous r' id hmem hround1 hphase3 u he with hbu | ⟨-, hw0⟩
              · rw [hexcluded0] at hbu; simp at hbu
              · rcases hw0 with hh | hh
                · rw [hcoin] at hh; simp only [CoinValue.bit.injEq] at hh; rw [hh]
                · rw [hcoin] at hh; simp at hh
          · -- round `r'` already had an excluded bit, which the live pair fixes at `!v`:
            -- the pre-exclude pair holds and the old `agree_locked` applies
            have hpairold : (!v) ∈ (g r').excluded ∧ v ∉ (g r').excluded := by
              rw [hExcludedSelf'] at hbr
              refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
              rcases Finset.mem_insert.mp hbr.1 with hnew | hold
              · obtain ⟨wd, hwd⟩ := Finset.nonempty_iff_ne_empty.mpr hexcluded0
                have hwb : wd ≠ b := fun hh => hbAt (hh ▸ hwd)
                have hwv : wd ≠ v := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
                have hwd' : wd = !v := by
                  revert hwb hwv hnew; cases wd <;> cases v <;> cases b <;> simp
                exact hwd' ▸ hwd
              · exact hold
            have hlast' : IsLastBound g r' :=
              ⟨Finset.nonempty_iff_ne_empty.mp ⟨_, hpairold.1⟩, hemp1⟩
            exact hI.agree_locked r' v hlast' hpairold hcoin id hmem hround
        · have hlast' : IsLastBound g r' := ⟨by rw [← hExcludedNe r' h2]; exact hlast.1,
            by rw [← hExcludedNe (r' + 1) h1]; exact hlast.2⟩
          rw [hExcludedNe r' h2] at hbr
          exact hI.agree_locked r' v hlast' hbr hcoin id hmem hround
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; rw [hExcludedSelf]; simp
      · rw [hGradeeq] at h
        rw [hExcludedNe r' h2]; exact hI.grade2_needs_bind r' h
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.call_round r' id hmem hcall
    · intro r' id hmem hcalled
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.wcc_called r' id hmem hcalled
    · intro id b hlg
      exact (hI.grade2_source id b hlg).imp (fun r'' => hCertTrans r'' b)
    · intro r' id hmem hround hphase
      obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id hmem hround hphase
      refine ⟨fun he => ?_, fun b' hb' => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨(hGradeeq r').trans hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · exact hExcludedMono r' _ (hsome b' hb')
    · intro r' v h
      by_cases h1 : r' + 1 = r
      · rw [h1, hExcludedSelf] at h
        rcases Finset.mem_insert.mp h with hnew | hold
        · -- the fresh exclusion: the spared bit `!b = v` was carried by the derived
          -- correct caller, whose `call_provenance` provenance is the conclusion verbatim
          have hveq : v = !b := by
            revert hnew; cases v <;> cases b <;> simp
          have hcp := hI.call_provenance r' id0 (!b) hFid0 (by rw [h1]; exact hcall0)
          rw [← hveq] at hcp
          rcases hcp with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hExcludedMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
        · rcases hI.bind_succ r' v (by rw [h1]; exact hold) with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hExcludedMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
      · rw [hExcludedNe (r' + 1) h1] at h
        rcases hI.bind_succ r' v h with hd | ⟨hg0, hw0⟩
        · exact Or.inl (hExcludedMono r' _ hd)
        · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id v hmem hcall
      rw [hCalleq] at hcall
      rcases hI.call_provenance r' id v hmem hcall with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hExcludedMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id hmem hround hphase v hest
      rcases hI.estimate_previous r' id hmem hround hphase v hest with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hExcludedMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' h
      rw [hGradeeq] at h ⊢
      exact hI.grade0Lock_chain r' h
    · intro id b' h; rw [hCalleq] at h; exact hI.input_gbcaRound0_permanent id b' h
    · -- `flip_grade2Lock`: `grade` and every residue component are monotone-transported
      intro r' h
      rcases hI.flip_grade2Lock r' h with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hp
      rcases hI.retG_witness r' id hmem hp with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hcalled
      rcases hI.wccCalled_witness r' id hmem hcalled with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' h
      by_cases h2 : r' = r
      · rw [h2]
        exact GBCA.SpecState.quorum_of_eq (hFeq r) (hCalleq r) _hq
      · rw [hExcludedNe r' h2] at h
        exact GBCA.SpecState.quorum_of_eq (hFeq r') (hCalleq r') (hI.bound_quorum r' h)
    · -- I26 establishment: the fresh exclusion's D15 count is the spared bit's sent source
      intro r' v hb'
      by_cases h2 : r' = r
      · rw [h2, hExcludedSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · have hveq : v = !b := by revert hnew; cases v <;> cases b <;> simp
          rw [hveq]
          exact hI.support_of_call_count r (!b) _hw
        · exact hI.bind_support r v hold
      · rw [hExcludedNe r' h2] at hb'; exact hI.bind_support r' v hb'
    · intro r' b' hgf
      rw [hGradeeq] at hgf
      exact GBCA.callSupport_mono (fun id' h => by rw [hCalleq r']; exact h) (hFeq r').ge
        (hI.grade0Lock_support r' b' hgf)
    · -- I28 establishment: the fresh exclusion records its own guard; old exclusions keep theirs
      intro r' b' hb'
      have hcnt : ∀ r₀ b₀, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g r₀).call id' = some (!b₀) ∨ id' ∈ (g r₀).F)).card →
          P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g' r₀).call id' = some (!b₀) ∨ id' ∈ (g' r₀).F)).card :=
        fun r₀ b₀ hh => GBCA.callSupport_mono (fun id' h => by rw [hCalleq r₀]; exact h)
          (hFeq r₀).ge hh
      by_cases h2 : r' = r
      · rw [h2] at hb' ⊢
        rw [hExcludedSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · rw [hnew]; exact hcnt r b _hw
        · exact hcnt r b' (hI.excluded_support r b' hold)
      · rw [hExcludedNe r' h2] at hb'
        exact hcnt r' b' (hI.excluded_support r' b' hb')

end ABA
end PLTS
