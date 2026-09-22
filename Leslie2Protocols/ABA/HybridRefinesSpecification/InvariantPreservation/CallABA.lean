/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# `Invariant` across the `callABA` rows of `hybrid`

`Invariant.step_callABA`, preservation of `Invariant` at a call of the ABA interface. The row is
either a never-corrupted process's genuine external input, guarded by `input = none`, so that
`input_called` rules out the corner where the graded-agreement call has already been made, or the
idle self-loop.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- `callABA`: either a never-corrupted process's genuine external input (guarded by
`input = none`, so `input_called` rules out the "already called GBCA" corner) or the idle
self-loop. -/
theorem Invariant.step_callABA {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (ABAState P)}
    (hstep :
      (id ∉ c.F ∧ (c.processes id).input = none ∧
          μc = PMF.pure (c.setProcess id { c.processes id with
            input := some b, estimate := some b, round := 0, phase := .toCallG })) ∨
        ((c.corrupted id = true ∨ (c.processes id).input ≠ none) ∧ μc = PMF.pure c))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' w ∧ AbstractStateUnchanged P g g c c' := by
  rcases hstep with ⟨-, hin, rfl⟩ | ⟨-, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    set c' := c.setProcess id { c.processes id with
      input := some b, estimate := some b, round := 0, phase := .toCallG } with hc'def
    have hF : c'.F = c.F := ABAState.setProcess_F _ _ _
    have hCorr : c'.corrupted = c.corrupted := ABAState.setProcess_corrupted _ _ _
    have hDS : c'.decidedSent = c.decidedSent := ABAState.setProcess_decidedSent _ _ _
    have hDR : c'.decidedReceived = c.decidedReceived := ABAState.setProcess_decidedReceived _ _ _
    have hSelf : c'.processes id = { c.processes id with
        input := some b, estimate := some b, round := 0, phase := .toCallG } := by
      rw [hc'def]; exact ABAState.setProcess_processes_self _ _ _
    have hNe : ∀ id', id' ≠ id → c'.processes id' = c.processes id' := by
      intro id' h; rw [hc'def]; exact ABAState.setProcess_processes_ne _ _ _ h
    have hDissTrans : ∀ r, DissentWitness P g c r → DissentWitness P g c' r := by
      intro r hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hbv, ?_⟩
      by_cases h0 : r = 0
      · rw [if_pos h0] at hif ⊢
        obtain ⟨id', hid'⟩ := hif
        by_cases hidmatch : id' = id
        · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
        · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
      · rw [if_neg h0] at hif ⊢; exact hif
    have hInMono : ∀ id' b',
      (c.processes id').input = some b' → (c'.processes id').input = some b' := by
      intro id' b' h
      by_cases hid : id' = id
      · exact absurd (hid ▸ h) (by rw [hin]; simp)
      · rw [hNe id' hid]; exact h
    have hCarrTrans : ∀ r' id₀ v, OutcomeHolder P g c' r' id₀ v → OutcomeHolder P g c r' id₀ v := by
      intro r' id₀ v hc
      rcases hc with h | ⟨he, hk⟩
      · exact Or.inl h
      · by_cases hid : id₀ = id
        · subst hid; exfalso; simp [hSelf] at hk
        · rw [hNe id₀ hid] at he hk
          exact Or.inr ⟨he, hk⟩
    have hCertTrans : ∀ r' b', Grade2Certificate P g c r' b' → Grade2Certificate P g c' r' b' := by
      rintro r' b' ⟨hg1, hd1, h1, h2, h3, h4⟩
      refine ⟨hg1, hd1, h1,
        fun r'' id'' b'' hrr hmem hcall => h2 r'' id'' b'' hrr (hF ▸ hmem) hcall,
        fun id'' hmem hr => ?_,
        fun id'' v hmem hcar => h4 id'' v (hF ▸ hmem) (hCarrTrans r' id'' v hcar)⟩
      by_cases h : id'' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id'' h] at hr ⊢; exact h3 id'' (hF ▸ hmem) hr
    have hLG : ∀ id₀, (c'.processes id₀).lastGrade = (c.processes id₀).lastGrade := by
      intro id₀; by_cases h : id₀ = id
      · subst h; simp [hSelf]
      · rw [hNe id₀ h]
    have hHold : ∀ id₀ b₀, Grade2Holder P c' id₀ b₀ → Grade2Holder P c id₀ b₀ := by
      intro id₀ b₀ h
      unfold Grade2Holder at h ⊢
      rwa [hLG, hDS] at h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
    refine ⟨fun id' => by rw [hCorr, hF]; exact hI.corrupted_F id',
      fun r => (hI.F_gbca r).trans hF.symm, fun r => hF ▸ hI.F_wcc r, hF ▸ hI.F_card,
      ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono hInMono (fun x hx => by rw [hF]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i j v v' hm hm' h h' => hI.outcomeHolder_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h'),
      fun i j b₀ b₀' hm hm' h h' => hI.grade2Lock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
        (hHold _ _ h) (hHold _ _ h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem
        have hne : (g 0).call id ≠ none := by
          rw [hcall]; simp
        exact absurd hin (hI.input_called 0 id (hF ▸ hmem) hne)
      · rw [hNe id' h]; exact hI.input_gbcaRound0 id' b' (hF ▸ hmem) hcall
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h]; exact hI.input_called r id' (hF ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h] at hne ⊢; exact hI.phase_input id' (hF ▸ hmem) hne
    · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.received_sound i j b' h
    · intro id' b' hmem h; rw [hDS] at h
      exact (hI.decided_source id' b' (hF ▸ hmem) h).imp (fun r => hCertTrans r b')
    · intro r b' hg hb
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hg hb
      refine ⟨h1, h2, fun id' hmem hr => ?_,
        fun id0 v hmem hcar => h4 id0 v (hF ▸ hmem) (hCarrTrans r id0 v hcar)⟩
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact h3 id' (hF ▸ hmem) hr
    · intro id' hmem r hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_bound id' (hF ▸ hmem) r hr
    · intro r v hlast hb hcoin id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) hr
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem; exact absurd hin (hI.input_called r id (hF ▸ hmem) hcall)
      · rw [hNe id' h]; exact hI.call_round r id' (hF ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hF ▸ hmem) hcalled
    · intro r id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf]
      · rw [hNe id' h] at hround hphase ⊢; exact hI.estimate0 id' (hF ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · rw [h] at hlg; rw [hSelf] at hlg
        exact (hI.grade2_source id b' hlg).imp (fun r => hCertTrans r b')
      · rw [hNe id' h] at hlg
        exact (hI.grade2_source id' b' hlg).imp (fun r => hCertTrans r b')
    · intro r id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hphase
      · rw [hNe id' h] at hround hphase ⊢; exact hI.estimate_ret r id' (hF ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hF ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase hest
        exact hI.estimate_previous r id' (hF ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase ⊢
        exact hI.estimate_previous_ne id' (hF ▸ hmem) hround hphase
    · intro id' b' h
      rcases hI.input_gbcaRound0_permanent id' b' h with hpre | hf
      · by_cases hid : id' = id
        · rw [hid, hin] at hpre; exact absurd hpre (by simp)
        · left; rw [hNe id' hid]; exact hpre
      · right; rw [hF]; exact hf
    · -- `wcc_callRound`'s `id' = id` corner: `id` was just idle (`hin`), so `idle_no_wccCall`
      -- rules out `id` having ever called any `WCC` instance.
      intro r id' hmem hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem hcalled
        have := hI.idle_no_wccCall id (hF ▸ hmem) hin r
        rw [this] at hcalled
        exact absurd hcalled (by simp)
      · rw [hNe id' hid]; exact hI.wcc_callRound r id' (hF ▸ hmem) hcalled
    · -- `flip_grade2Lock`: `g` is untouched entirely; the only wrinkle is the `r = 0` dissent
      -- witness possibly naming `id` itself, ruled out by `hin : input = none` (the fresh
      -- the input of a correct process cannot have been the opposing dissenter).
      intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right
        obtain ⟨v, hbv, hif⟩ := hd
        refine ⟨v, hbv, ?_⟩
        by_cases h0 : r = 0
        · rw [if_pos h0] at hif ⊢
          obtain ⟨id', hid'⟩ := hif
          by_cases hidmatch : id' = id
          · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
          · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
        · rw [if_neg h0] at hif ⊢; exact hif
    · intro id' hmem hin' r'
      by_cases h : id' = id
      · subst h; simp [hSelf] at hin'
      · rw [hNe id' h] at hin'; exact hI.idle_no_wccCall id' (hF ▸ hmem) hin' r'
    · intro r id' hmem hp
      by_cases h : id' = id
      · subst h; simp [hSelf] at hp
      · rw [hNe id' h] at hp
        rcases hI.retG_witness r id' (hF ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDissTrans r hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDissTrans r hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    exact ⟨hI, AbstractStateUnchanged.refl P g _⟩

end ABA
end PLTS
