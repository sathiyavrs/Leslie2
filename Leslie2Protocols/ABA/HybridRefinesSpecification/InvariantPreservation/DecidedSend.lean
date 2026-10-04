/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# `Invariant` across the DECIDED send of `hybrid`

`Invariant.step_decidedSend`, preservation of `Invariant` at the DECIDED send of a grade-2 round.
The process `id` stands at `toSendDecided` with the grade `grade2 b` of the round it has just
closed. The send inserts `b` into `id`'s DECIDED set, clears the grade and moves `id` to `toCallG`
at the same round. `g` and the coin are untouched. The phases `toSendDecided` and `toCallG` belong
to the same groups of every clause, so the holders of every round's outcome are unchanged.
`decided_source` for the inserted bit is `grade2_source` read at the sender, `received_sound`
holds since the sent set grows, and `grade2Bound_agree` holds since the grade-2 holder at `id`
moves from the grade to the sent set.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- The DECIDED send: `Invariant` is preserved and the abstract state is unchanged at the DECIDED
send of a grade-2 round. -/
theorem Invariant.step_decidedSend {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n)
    (b : Bool) (hph : (c.processes id).phase = .toSendDecided)
    (hlg : (c.processes id).lastGrade = some (.grade2 b)) :
    Invariant P g (c.sendDecidedOnGrade2 id b) w ∧
      AbstractStateUnchanged P g g c (c.sendDecidedOnGrade2 id b) := by
  set c' := c.sendDecidedOnGrade2 id b with hc'
  have hFeq : c'.F = c.F := ABAState.sendDecidedOnGrade2_F _ _ _
  have hDR : c'.decidedReceived = c.decidedReceived :=
    ABAState.sendDecidedOnGrade2_decidedReceived _ _ _
  have hSelf : c'.processes id =
      { c.processes id with lastGrade := none, phase := .toCallG } :=
    ABAState.sendDecidedOnGrade2_processes_self _ _ _
  have hNe : ∀ k, k ≠ id → c'.processes k = c.processes k := fun k hk =>
    ABAState.sendDecidedOnGrade2_processes_ne _ _ _ hk
  have hIn : ∀ k, (c'.processes k).input = (c.processes k).input := by
    intro k; by_cases hk : k = id
    · rw [hk, hSelf]
    · rw [hNe k hk]
  have hRd : ∀ k, (c'.processes k).round = (c.processes k).round := by
    intro k; by_cases hk : k = id
    · rw [hk, hSelf]
    · rw [hNe k hk]
  have hEs : ∀ k, (c'.processes k).estimate = (c.processes k).estimate := by
    intro k; by_cases hk : k = id
    · rw [hk, hSelf]
    · rw [hNe k hk]
  have hIdle : ∀ k, (c'.processes k).phase ≠ .idle → (c.processes k).phase ≠ .idle := by
    intro k h; by_cases hk : k = id
    · rw [hk, hph]; decide
    · rwa [hNe k hk] at h
  have hW : ∀ k, ((c'.processes k).phase = .toCallW ∨ (c'.processes k).phase = .awaitW) →
      ((c.processes k).phase = .toCallW ∨ (c.processes k).phase = .awaitW) := by
    intro k h; by_cases hk : k = id
    · rw [hk, hSelf] at h; simp at h
    · rwa [hNe k hk] at h
  have hG : ∀ k, ((c'.processes k).phase = .idle ∨ (c'.processes k).phase = .toCallG ∨
        (c'.processes k).phase = .awaitG ∨ (c'.processes k).phase = .toSendDecided) →
      ((c.processes k).phase = .idle ∨ (c.processes k).phase = .toCallG ∨
        (c.processes k).phase = .awaitG ∨ (c.processes k).phase = .toSendDecided) := by
    intro k h; by_cases hk : k = id
    · rw [hk]; exact Or.inr (Or.inr (Or.inr hph))
    · rwa [hNe k hk] at h
  have hOH : ∀ r k v, OutcomeHolder P g c' r k v → OutcomeHolder P g c r k v := by
    rintro r k v (hcall | ⟨he, ⟨hr, hp⟩ | ⟨hr, hp⟩⟩)
    · exact Or.inl hcall
    · exact Or.inr ⟨(hEs k).symm.trans he, Or.inl ⟨(hRd k).symm.trans hr, hW k hp⟩⟩
    · exact Or.inr ⟨(hEs k).symm.trans he, Or.inr ⟨(hRd k).symm.trans hr, hG k hp⟩⟩
  have hLG : ∀ k b1, (c'.processes k).lastGrade = some (.grade2 b1) →
      (c.processes k).lastGrade = some (.grade2 b1) := by
    intro k b1 h; by_cases hk : k = id
    · rw [hk, hSelf] at h; simp at h
    · rwa [hNe k hk] at h
  have hCert : ∀ r b0, Grade2Witness P g c r b0 → Grade2Witness P g c' r b0 := fun r _ =>
    Grade2Witness.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl) (by rw [hFeq] : c.F ⊆ _)
      hRd hEs (hOH r)
  have hHold : ∀ k b1, Grade2Holder P c' k b1 → Grade2Holder P c k b1 := by
    rintro k b1 (h | h)
    · exact Or.inl (hLG k b1 h)
    · rcases (ABAState.mem_sendDecidedOnGrade2_decidedSent_iff _ _ _ _ _).mp h with
        ⟨rfl, rfl⟩ | h
      · exact Or.inl hlg
      · exact Or.inr h
  have hDissent : ∀ r, DissentWitness P g c r → DissentWitness P g c' r := fun r hd =>
    DissentWitness.preserved rfl rfl (fun h => h) hIn hd
  refine ⟨?_, fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hHold j b' hh)⟩
  exact
    { corrupted_F := fun k => by
        rw [ABAState.sendDecidedOnGrade2_corrupted, hFeq]; exact hI.corrupted_F k
      F_gbca := fun r => by rw [hFeq]; exact hI.F_gbca r
      F_wcc := fun r => by rw [hFeq]; exact hI.F_wcc r
      F_card := hFeq ▸ hI.F_card
      input_gbcaRound0 := fun k b' hk hcall => by
        rw [hIn]; exact hI.input_gbcaRound0 k b' (hFeq ▸ hk) hcall
      input_called := fun r k hk hcall => by
        rw [hIn]; exact hI.input_called r k (hFeq ▸ hk) hcall
      phase_input := fun k hk hne => by
        rw [hIn]; exact hI.phase_input k (hFeq ▸ hk) (hIdle k hne)
      down_settled := hI.down_settled
      quiescent := hI.quiescent
      wcc_bound := hI.wcc_bound
      received_sound := fun i j b' h => by
        rw [hDR] at h
        exact (ABAState.mem_sendDecidedOnGrade2_decidedSent_iff _ _ _ _ _).mpr
          (Or.inr (hI.received_sound i j b' h))
      decided_source := fun k b' hk h => by
        rcases (ABAState.mem_sendDecidedOnGrade2_decidedSent_iff _ _ _ _ _).mp h with
          ⟨rfl, rfl⟩ | h
        · exact (hI.grade2_source k b' hlg).imp (fun r => hCert r b')
        · exact (hI.decided_source k b' (hFeq ▸ hk) h).imp (fun r => hCert r b')
      grade2Bound_commit := fun r b' hgr hbr =>
        Grade2Commitment.of_unchanged (fun _ => rfl) (fun _ _ => rfl) (by rw [hFeq] : c.F ⊆ _)
          hRd hEs (hOH r) (hI.grade2Bound_commit r b' hgr hbr)
      round_bound := fun k hk r hr => hI.round_bound k (hFeq ▸ hk) r (by rwa [hRd] at hr)
      agree_bound := fun r v hlast hbr hcoin k hk hr => by
        rw [hEs]; exact hI.agree_bound r v hlast hbr hcoin k (hFeq ▸ hk) (by rwa [hRd] at hr)
      grade2_needs_bind := hI.grade2_needs_bind
      call_round := fun r k hk hcall => by
        rw [hRd]; exact hI.call_round r k (hFeq ▸ hk) hcall
      wcc_called := fun r k hk hcalled => hI.wcc_called r k (hFeq ▸ hk) hcalled
      round_flip := fun r k hk hr => hI.round_flip r k (hFeq ▸ hk) (by rwa [hRd] at hr)
      estimate0 := fun k hk hr hp => by
        rw [hEs, hIn]; exact hI.estimate0 k (hFeq ▸ hk) (by rwa [hRd] at hr) (hG k hp)
      grade2_source := fun k b' h => (hI.grade2_source k b' (hLG k b' h)).imp (fun r => hCert r b')
      estimate_ret := fun r k hk hr hp => by
        rw [hEs]; exact hI.estimate_ret r k (hFeq ▸ hk) (by rwa [hRd] at hr) (hW k hp)
      bind_succ := hI.bind_succ
      call_of_previousRound := fun r k v hk hcall =>
        hI.call_of_previousRound r k v (hFeq ▸ hk) hcall
      estimate_previous := fun r k hk hr hp v he =>
        hI.estimate_previous r k (hFeq ▸ hk) (by rwa [hRd] at hr) (hG k hp) v (by rwa [hEs] at he)
      grade0_chain := hI.grade0_chain
      estimate_previous_ne := fun k hk hr hp => by
        rw [hEs]; exact hI.estimate_previous_ne k (hFeq ▸ hk) (by rwa [hRd] at hr) (hG k hp)
      wcc_order := hI.wcc_order
      input_gbcaRound0_permanent := fun k b' h => by
        rw [hIn, hFeq]; exact hI.input_gbcaRound0_permanent k b' h
      wcc_callRound := fun r k hk hcalled => by
        rw [hRd]; exact hI.wcc_callRound r k (hFeq ▸ hk) hcalled
      flip_witness := fun r h => (hI.flip_witness r h).imp _root_.id (hDissent r)
      idle_no_wccCall := fun k hk hin r =>
        hI.idle_no_wccCall k (hFeq ▸ hk) (by rwa [hIn] at hin) r
      retG_witness := fun r k hk hp => by
        refine (hI.retG_witness r k (hFeq ▸ hk) ?_).imp _root_.id (hDissent r)
        rw [hRd] at hp
        exact hp.imp (fun h => ⟨h.1, hW k h.2⟩) _root_.id
      wccCalled_witness := fun r k hk hcalled =>
        (hI.wccCalled_witness r k (hFeq ▸ hk) hcalled).imp _root_.id (hDissent r)
      bound_quorum := hI.bound_quorum
      bind_support := fun r v hb => (hI.bind_support r v hb).mono
        (fun k b' h => by rw [hIn]; exact h) (fun x hx => by rw [hFeq]; exact hx)
      grade0_support := hI.grade0_support
      excluded_support := hI.excluded_support
      outcomeHolder_agree := fun r i j v v' hi hj h h' =>
        hI.outcomeHolder_agree r i j v v' (hFeq ▸ hi) (hFeq ▸ hj) (hOH r i v h) (hOH r j v' h')
      grade2Bound_agree := fun i j b0 b0' hi hj h h' =>
        hI.grade2Bound_agree i j b0 b0' (hFeq ▸ hi) (hFeq ▸ hj) (hHold i b0 h) (hHold j b0' h') }

end ABA
end PLTS
