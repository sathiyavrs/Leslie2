/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.SpecificationStateCorruption

/-!
# `Invariant` across the `fail` rows of `hybrid`

`Invariant.step_fail`, preservation of `Invariant` at a synchronised corruption of all three
components, under the row's own guards: the named process is not corrupted yet and the budget has
room. `F` only grows and every other projection is untouched, so the correctness hypotheses
transfer by `F`-monotonicity. The two guards are what puts the replacement flag and the corrupted
set together (I0, D23), the flag going up at `id` and `F` gaining exactly `id`.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- `fail`: `Invariant` is preserved and the abstract state is unchanged at a synchronised
corruption of all three components. -/
theorem Invariant.step_fail {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n)
    (hnew : id ∉ c.F) (hbud : c.F.card < P.f) :
    Invariant P (fun r => (g r).corrupt P id) (c.corrupt P id) (fun r => (w r).corrupt P id) ∧
      AbstractStateUnchanged P g (fun r => (g r).corrupt P id) c (c.corrupt P id) := by
  set g' := fun r => (g r).corrupt P id with hg'def
  set c' := c.corrupt P id with hc'def
  set w' := fun r => (w r).corrupt P id with hw'def
  have hcall : ∀ r, (g' r).call = (g r).call := fun r => GBCA.corrupt_call P (g r) id
  have hbind : ∀ r, (g' r).excluded = (g r).excluded := fun r => GBCA.corrupt_excluded P (g r) id
  have hgrade : ∀ r, (g' r).grade = (g r).grade := fun r => GBCA.corrupt_grade P (g r) id
  have hval : ∀ r, (w' r).val = (w r).val := fun r => WCC.corrupt_val id (w r)
  have hcalled : ∀ r, (w' r).called = (w r).called := fun r => WCC.corrupt_called id (w r)
  have hprocs : c'.processes = c.processes := ABAState.corrupt_processes c id
  have hDS : c'.decidedSent = c.decidedSent := ABAState.corrupt_decidedSent c id
  have hDR : c'.decidedReceived = c.decidedReceived := ABAState.corrupt_decidedReceived c id
  have hFg : ∀ r, (g' r).F = c'.F := fun r => GBCA.corrupt_F_eq id (g r) c (hI.F_gbca r)
  have hFw : ∀ r, (w' r).F = c'.F := fun r => WCC.corrupt_F_eq id (w r) c (hI.F_wcc r)
  have hFsub : c.F ⊆ c'.F := by
    rw [hc'def, ABAState.corrupt_F]; split_ifs with hcond
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  have hFcard : c'.F.card ≤ P.f := by
    rw [hc'def, ABAState.corrupt_F]; split_ifs with hcond
    · obtain ⟨-, hlt⟩ := hcond
      show (insert id c.F).card ≤ P.f
      have hcard := Finset.card_insert_le id c.F
      omega
    · exact hI.F_card
  have hLastBound : ∀ r, IsLastBound g' r ↔ IsLastBound g r := by
    intro r; unfold IsLastBound; rw [hbind r, hbind (r + 1)]
  have hCarrTrans : ∀ r' id₀ v, OutcomeHolder P g' c' r' id₀ v → OutcomeHolder P g c r' id₀ v := by
    intro r' id₀ v hc
    unfold OutcomeHolder at hc ⊢
    rwa [hprocs, hcall (r' + 1)] at hc
  have hCertTrans : ∀ r' b',
    Grade2Certificate P g c r' b' → Grade2Certificate P g' c' r' b' := fun r' b' =>
      Grade2Certificate.of_unchanged (hgrade r') hbind (fun r'' id' => congrFun (hcall r'') id')
        hFsub
      (fun id' => by rw [hprocs]) (fun id' => by rw [hprocs])
      (fun id0 v => hCarrTrans r' id0 v)
  have hHold : ∀ id₀ b₀, Grade2Holder P c' id₀ b₀ → Grade2Holder P c id₀ b₀ := by
    intro id₀ b₀ h
    unfold Grade2Holder at h ⊢
    rwa [hprocs, hDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (fun h0 => hj (hFsub h0)) (hHold j b' hh)⟩
  have hFins : c'.F = insert id c.F := by
    rw [hc'def, ABAState.corrupt_F, if_pos ⟨hnew, hbud⟩]
  have hCorr : ∀ id', c'.corrupted id' = true ↔ id' ∈ c'.F := by
    intro id'
    rw [hFins, Finset.mem_insert]
    by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.corrupt_corrupted_self]; simp
    · rw [hc'def, ABAState.corrupt_corrupted_ne c id h, hI.corrupted_F id']; simp [h]
  refine ⟨hCorr, fun r => hFg r, fun r => hFw r, hFcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r v hb => (hI.bind_support r v (by rw [← hbind r]; exact hb)).mono
      (fun id' b' h => by rw [hprocs]; exact h) hFsub,
    fun r b hgf => GBCA.callSupport_mono (fun id' h => by rw [hcall r]; exact h)
      (by rw [hFg r, hI.F_gbca r]; exact hFsub)
      (hI.grade0Lock_support r b (by rw [← hgrade r]; exact hgf)),
    fun r b h => GBCA.callSupport_mono (fun id' h' => by rw [hcall r]; exact h')
      (by rw [hFg r, hI.F_gbca r]; exact hFsub)
      (hI.excluded_support r b (by rw [← hbind r]; exact h)),
    fun r' i j v v' hm hm' h h' => hI.outcomeHolder_agree r' i j v v'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h') |>.imp (fun hh => hh) (fun hh => by
        rw [hgrade r']; exact hh),
    fun i j b₀ b₀' hm hm' h h' => hI.grade2Lock_agree i j b₀ b₀'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall0
    rw [hprocs]; rw [hcall 0] at hcall0
    exact hI.input_gbcaRound0 id' b' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.input_called r id' (fun h => hmem (hFsub h)) hcall0
  · intro id' hmem hne
    rw [hprocs] at hne ⊢; exact hI.phase_input id' (fun h => hmem (hFsub h)) hne
  · intro r h
    rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.down_settled r ((RoundSettled.congr (hbind (r + 1)) (hgrade (r + 1))).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r hr h => hR r hr ((RoundSettled.congr (hbind r) (hgrade r)).mp h)⟩
  · intro r h
    rw [hval r] at h; rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.wcc_bound r h
  · intro i j b' h
    rw [hDR] at h; rw [hDS]
    exact hI.received_sound i j b' h
  · intro id' b' hmem h
    rw [hDS] at h
    exact (hI.decided_source id' b' (fun h' => hmem (hFsub h')) h).imp (fun r => hCertTrans r b')
  · intro r b' hgr hbr
    rw [hgrade r] at hgr; rw [hbind r] at hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
    refine ⟨fun r' b'' hrr' hb' => ?_, fun r' id' b'' hrr' hmem hcall0 => ?_,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (fun h => hmem (hFsub h)) (hCarrTrans r id0 v hcar)⟩
    · rw [hbind r'] at hb'; exact h1 r' b'' hrr' hb'
    · rw [hcall r'] at hcall0; exact h2 r' id' b'' hrr' (fun h => hmem (hFsub h)) hcall0
    · rw [hprocs] at hround ⊢; exact h3 id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem r hround
    rw [hprocs] at hround; rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.round_bound id' (fun h => hmem (hFsub h)) r hround
  · intro r v hlast hbr hcoin id' hmem hround
    rw [hLastBound r] at hlast; rw [hbind r] at hbr; rw [hval r] at hcoin
    rw [hprocs] at hround ⊢
    exact hI.agree_locked r v hlast hbr hcoin id' (fun h => hmem (hFsub h)) hround
  · intro r h; rw [hgrade r] at h; rw [hbind r]; exact hI.grade2_needs_bind r h
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.call_round r id' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.wcc_called r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r id' hmem hround
    rw [hprocs] at hround; rw [hval r]
    exact hI.round_flip r id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.estimate0 id' (fun h => hmem (hFsub h)) hround hphase
  · intro id' b' hlg
    rw [hprocs] at hlg
    exact (hI.grade2_source id' b' hlg).imp (fun r => hCertTrans r b')
  · intro r id' hmem hround hphase
    rw [hprocs] at hround hphase
    obtain ⟨hnone, hsome⟩ := hI.estimate_ret r id' (fun h => hmem (hFsub h)) hround hphase
    rw [hprocs]
    refine ⟨fun he => ?_, fun b' hb' => ?_⟩
    · obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨by rw [hgrade]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
      rw [hgrade] at hgr0
      exact hno r₀ hr0 hgr0
    · rw [hbind]; exact hsome b' hb'
  · intro r v h
    rw [hbind (r + 1)] at h; rw [hbind r, hgrade r, hval r]
    exact hI.bind_succ r v h
  · intro r id' v hmem hcall0
    rw [hcall (r + 1)] at hcall0; rw [hbind r, hgrade r, hval r]
    exact hI.call_provenance r id' v (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hround hphase v hest
    rw [hprocs] at hround hphase hest; rw [hbind r, hgrade r, hval r]
    exact hI.estimate_previous r id' (fun h => hmem (hFsub h)) hround hphase v hest
  · intro r h; rw [hgrade (r + 1)] at h; rw [hgrade r]; exact hI.grade0Lock_chain r h
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.estimate_previous_ne id' (fun h => hmem (hFsub h)) hround hphase
  · intro r h; rw [hval] at h ⊢; exact hI.wcc_order r h
  · intro id' b' h
    rw [hcall 0] at h; rw [hprocs]
    rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
    · left; exact hin
    · right; exact hFsub hf
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [hprocs]
    exact hI.wcc_callRound r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r h
    rw [hval] at h
    rcases hI.flip_grade2Lock r h with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentWitness.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro id' hmem hin r
    rw [hprocs] at hin; rw [hcalled r]
    exact hI.idle_no_wccCall id' (fun h => hmem (hFsub h)) hin r
  · intro r id' hmem hp
    rw [hprocs] at hp
    rcases hI.retG_witness r id' (fun h => hmem (hFsub h)) hp with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentWitness.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0
    rcases hI.wccCalled_witness r id' (fun h => hmem (hFsub h)) hcalled0 with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentWitness.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r h
    rw [hbind r] at h
    exact GBCA.SpecState.quorum_mono (by rw [hFg r, hI.F_gbca r]; exact hFsub)
      (fun id' hne => by rw [hcall r]; exact hne) (hI.bound_quorum r h)

end ABA
end PLTS
