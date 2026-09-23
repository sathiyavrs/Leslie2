/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# `Invariant` across the round loops' `τ` rows of `hybrid`

`Invariant.step_roundLoopTau`, preservation of `Invariant` at a core `τ`: DECIDED delivery, echo,
or byzantine injection. All three leave `processes` and `F` untouched, so only `received_sound` and
`decided_source` need real work. The `echo` case's correct sender comes from an `f + 1`-vs-`≤ f`
pigeonhole on the delivered senders.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- The round loops' `τ` rows: `Invariant` is preserved and the abstract state is unchanged at a
DECIDED delivery, an echo or a byzantine injection. -/
theorem Invariant.step_roundLoopTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w)
    {μc : PMF (ABAState P)}
    (hstep :
      (∃ i j b, b ∈ c.decidedSent j ∧ b ∉ c.decidedReceived i j ∧
          μc = PMF.pure (c.deliverDecided i j b)) ∨
        (∃ id b, P.f + 1 ≤ c.decidedCount id b ∧ b ∉ c.decidedSent id ∧
          μc = PMF.pure (c.sendDecided id b)) ∨
        (∃ id b, id ∈ c.F ∧ μc = PMF.pure (c.sendDecided id b)))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' w ∧ AbstractStateUnchanged P g g c c' := by
  rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩
  · -- deliver
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.deliverDecided i j b).processes = c.processes :=
      ABAState.deliverDecided_processes _ _ _ _
    have hFeq : (c.deliverDecided i j b).F = c.F := ABAState.deliverDecided_F _ _ _ _
    have hDS : (c.deliverDecided i j b).decidedSent = c.decidedSent :=
      ABAState.deliverDecided_decidedSent _ _ _ _
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g (c.deliverDecided i j b) r' b' := fun r'
        b' => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj)
        (by unfold Grade2Holder at hh ⊢; rwa [hProcs, hDS] at hh)⟩
    refine ⟨fun id' => by
        rw [ABAState.deliverDecided_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r => by rw [hFeq]; exact hI.F_gbca r, fun r => by rw [hFeq]; exact hI.F_wcc r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold OutcomeHolder at h ⊢; rwa [hProcs] at h)
        (by unfold OutcomeHolder at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Grade2Holder at h ⊢; rwa [hProcs, hDS] at h)
        (by unfold Grade2Holder at h' ⊢; rwa [hProcs, hDS] at h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDS]
      by_cases hij : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [ABAState.deliverDecided_decidedReceived_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact hs
        · exact hI.received_sound i' j' b' h
      · rw [ABAState.deliverDecided_decidedReceived_of_ne _ _ _ _ (by tauto)] at h
        exact hI.received_sound i' j' b' h
    · intro id' b' hmem h
      rw [hDS] at h
      exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.estimate_previous r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_gbcaRound0_permanent id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.wcc_callRound r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retG_witness r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- echo: a correct sender among the `f + 1` counted deliveries
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).processes = c.processes := ABAState.sendDecided_processes _ _
      _
    have hFeq : (c.sendDecided id b).F = c.F := ABAState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedReceived = c.decidedReceived :=
      ABAState.sendDecided_decidedReceived _ _ _
    have hcnt' : P.f + 1 ≤ (Finset.univ.filter (fun j => b ∈ c.decidedReceived id j)).card :=
      hcnt
    have hcard : c.F.card < (Finset.univ.filter (fun j => b ∈ c.decidedReceived id j)).card := by
      have := hI.F_card
      omega
    obtain ⟨j, hjmem, hjF⟩ :=
      (Finset.not_subset (s := Finset.univ.filter (fun j => b ∈ c.decidedReceived id j))
        (t := c.F)).mp (fun hsub => absurd (Finset.card_le_card hsub) (by omega))
    rw [Finset.mem_filter] at hjmem
    have hjsent : b ∈ c.decidedSent j := hI.received_sound id j b hjmem.2
    obtain ⟨r0, hcert0⟩ := hI.decided_source j b hjF hjsent
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g (c.sendDecided id b) r' b' := fun r' b'
        => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → Grade2Holder P (c.sendDecided id b) i0 b0 →
        ∃ j0, j0 ∉ c.F ∧ Grade2Holder P c j0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact ⟨i0, hm, Or.inl h⟩
      · rcases (ABAState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨-, rfl⟩ | h
        · exact ⟨j, hjF, Or.inr hjsent⟩
        · exact ⟨i0, hm, Or.inr h⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => by
        obtain ⟨j0, hj0, hh0⟩ := hHold j b' (hFeq ▸ hj) hh
        exact hpin j0 b' hj0 hh0⟩
    refine ⟨fun id' => by
        rw [ABAState.sendDecided_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r => by rw [hFeq]; exact hI.F_gbca r, fun r => by rw [hFeq]; exact hI.F_wcc r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold OutcomeHolder at h ⊢; rwa [hProcs] at h)
        (by unfold OutcomeHolder at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => by
        obtain ⟨ja, hjaF, hja⟩ := hHold i0 b0 (hFeq ▸ hm) h
        obtain ⟨jb, hjbF, hjb⟩ := hHold j0 b0' (hFeq ▸ hm') h'
        exact hI.grade2Lock_agree ja jb b0 b0' hjaF hjbF hja hjb⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact ABAState.sendDecided_decidedSent_mono _ _ _ (hI.received_sound i' j' b' h)
    · intro id' b' hmem h
      rw [ABAState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid
        rw [Function.update_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact ⟨r0, hCert r0 b' hcert0⟩
        · exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg; exact hI.grade2_source id' b' hlg
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.estimate_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.estimate_previous r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_gbcaRound0_permanent id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.wcc_callRound r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retG_witness r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- byzantine DECIDED injection: `id ∈ F`, so correct `decided_source` at `id` is vacuous
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).processes = c.processes := ABAState.sendDecided_processes _ _
      _
    have hFeq : (c.sendDecided id b).F = c.F := ABAState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedReceived = c.decidedReceived :=
      ABAState.sendDecided_decidedReceived _ _ _
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g (c.sendDecided id b) r' b' := fun r' b'
        => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → Grade2Holder P (c.sendDecided id b) i0 b0 →
        Grade2Holder P c i0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact Or.inl h
      · rcases (ABAState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨rfl, rfl⟩ | h
        · exact absurd hF hm
        · exact Or.inr h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hHold j b' (hFeq ▸ hj) hh)⟩
    refine ⟨fun id' => by
        rw [ABAState.sendDecided_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r => by rw [hFeq]; exact hI.F_gbca r, fun r => by rw [hFeq]; exact hI.F_wcc r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold OutcomeHolder at h ⊢; rwa [hProcs] at h)
        (by unfold OutcomeHolder at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hHold i0 b0 (hFeq ▸ hm) h) (hHold j0 b0' (hFeq ▸ hm') h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact ABAState.sendDecided_decidedSent_mono _ _ _ (hI.received_sound i' j' b' h)
    · intro id' b' hmem h
      rw [ABAState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid; exact absurd (hFeq ▸ hmem) (not_not.mpr hF)
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.estimate_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.estimate_previous r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_gbcaRound0_permanent id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.wcc_callRound r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retG_witness r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd

end ABA
end PLTS
