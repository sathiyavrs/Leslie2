/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.SimulationRows
import Leslie2Protocols.Framework.DiracRelationCoupling

/-!
# The gather-based protocol into its composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed
P` reads the same protocol as a composition of components, down to the
broadcast instances. This file carries the first into the second, which is
where the gather-based chain passes from implementation to specification, as
`ABA/ImplementationByABDY/Simulation.lean` does for ABDY22's. `ABA/Results.lean` takes the
inclusion from here to the ABA specification.

## The relation is a function

`AFW.ProtocolRelation` (`ABA/ImplementationByAFW/RoundProjection.lean`) determines the composed
state from the implementation: the round loops and the coin oracle are shared, the ABA network is
the DECIDED sets beside the corrupted set, and every round is the view `AFW.roundProjection`.
`PLTS.coupling_pure` and `PLTS.coupling_map` (`Framework/DiracRelationCoupling.lean`) are the two
couplings that answer a Dirac outcome and an outcome whose only free coordinate is the oracle's.

## The matching, label class by label class

`AFW.match_tau`, `AFW.match_label` and `AFW.match_event` answer the silent label, a visible shared
label and a rendezvous of the implementation, each from the runs of
`ABA/ImplementationByAFW/SimulationRows.lean`. An implementation row that fuses two events of the
composed round is answered by a run of two transitions, so `AFW.match_hidden` concludes in a weak
run of the composed group, and `AFW.match_step` carries that run through the sub-protocol hiding
with `weakTau_abstract`, `weakTau_of_weakStep_mem` and `weakStep_abstract`.
`AFW.protocolSimulation` is the forward simulation these matchings assemble, and
`AFW.protocol_composed` the trace inclusion it yields. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

/-! ### Assembling a matched run

Three shapes of answer: a visible shared label the four components answer with one transition each,
a hidden rendezvous they answer the same way, and a silent run of the graded-agreement family
alone. -/

/-- A visible shared label: the four components move together, the oracle's
successor free. -/
private theorem match_visible (P : Parameters) {x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w' : NetworkState P.n} {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A' : ABANetworkState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {l : Label P.n} (hl : l ≠ Label.tau)
    (hrel : ∀ o' ∈ ν.support, ProtocolRelation P (x, w', o') (G', C', A', o'))
    (hG : (roundFamilyOverBracha P).weakLStep G (Sum.inl l) G')
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inl l) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inl l) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o (Sum.inl l) ν) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      weakStep (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
        (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_map ν (fun o' => ((x, w', o') : ProtocolState P))
    (fun o' => ((G', C', A', o') : ComposedState P)) hrel
  rw [← prodPMF_two_pure_factors] at hr
  rw [← prodPMF_three_pure_factors] at hb
  exact ⟨Ω, hr, hb ▸ composedHidden_weakStep P hl hG hC hA hW⟩

/-- A hidden rendezvous: the four components move together and the composed
group reads the move as silent. -/
private theorem match_hiddenRendezvous (P : Parameters) {x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w' : NetworkState P.n} {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A' : ABANetworkState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} (e : NetworkEvent P.n)
    (hrel : ∀ o' ∈ ν.support, ProtocolRelation P (x, w', o') (G', C', A', o'))
    (hG : (roundFamilyOverBracha P).step G (Sum.inr e) (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inr e) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inr e) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o (Sum.inr e) ν) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_map ν (fun o' => ((x, w', o') : ProtocolState P))
    (fun o' => ((G', C', A', o') : ComposedState P)) hrel
  rw [← prodPMF_two_pure_factors] at hr
  rw [← prodPMF_three_pure_factors] at hb
  refine ⟨Ω, hr, ?_⟩
  rw [hb]
  exact weakTau_of_step rfl
    (composedHidden_of_event P e (composedExtended_visible_step P (by simp) hG hC hA hW))

/-- A row internal to the graded-agreement family: the family takes a silent run and nothing else
moves. -/
private theorem match_run (P : Parameters) {x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w' : NetworkState P.n} {G' G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hrel : ProtocolRelation P (x, w', o) (G', C, A, o))
    (hG : (roundFamilyOverBracha P).weakLSilent G G') :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure ((x, w', o) : ProtocolState P)) Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_pure hrel
  exact ⟨Ω, hr, hb ▸ composedHidden_weakTau P C A o hG⟩

/-- A composed state that is unchanged. -/
private theorem match_unchanged (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRelation P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure s) Ω ∧
      weakTau (composedHidden P) (PMF.pure t) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_pure h
  exact ⟨Ω, hr, hb ▸ weakTau_refl (composedHidden P) (PMF.pure t)⟩

/-! ### The matching on the silent label

The implementation's own `terminate` row writes no coordinate the relation reads,
so the composed answer to it is to remain unchanged; the adversary's two injections
are answered by a transition. -/

theorem match_tau (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl Label.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB, hI⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  rcases systemExtended_tau_inversion h with ⟨i, y, hstep, rfl⟩ | ⟨w', hn, rfl⟩
  · obtain ⟨b, hh, hret, hcnt, hterm, hy⟩ := programStep_tau_terminate hstep
    obtain rfl : y = ((u i).1, { (u i).2 with terminated := true }) := pure_inj hy
    have hst : ∀ (j : Fin P.n) (r : ℕ),
        ((Function.update u i ((u i).1,
            { (u i).2 with terminated := true }) j).2.roundRecord r) = ((u j).2.roundRecord r) := by
      intro j r
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne hj]
    have hview : ∀ r, roundProjection P (Function.update u i ((u i).1,
        { (u i).2 with terminated := true })) w r = roundProjection P u w r :=
      fun r => roundProjection_congr (fun j => hst j r)
    refine match_unchanged P ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun j => ?_, rfl, hA, ?_,
        boundInvariant_of hB (fun j r => by rw [hst j r]) (fun _ hb => hb),
        broadcastReturnsInvariant_congr hI hview⟩)
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact hC j
      · rw [Function.update_of_ne hj]; exact hC j
    · rw [hGv]
      funext r
      exact (hview r).symm
  · rcases networkStep_tau hn with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.recordGBCASend r k m := pure_inj hw
      obtain ⟨hstep, hinv⟩ := byzantine_answer P u w hI r m hF
      have hfam := roundProjectionFamily_byzantine u w r k m
      refine match_run P ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
          ⟨hC, rfl, by simpa using hA, hfam.symm,
            boundInvariant_of hB (fun _ _ => rfl) (fun _ hb => hb),
            broadcastReturnsInvariant_update hI hfam hinv⟩) ?_
      rw [hGv]
      exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P)
        (roundOverBracha_run_one hstep)
    · obtain rfl : w' = w.recordDecided k b := pure_inj hw
      have hrel : ProtocolRelation P (u, w.recordDecided k b, o)
          (G, C, ⟨(w.recordDecided k b).decidedSent, (w.recordDecided k b).F⟩, o) :=
        (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, rfl,
          by rw [hGv]; funext r; rfl,
          boundInvariant_of hB (fun _ _ => rfl) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun _ => rfl)⟩
      obtain ⟨Ω, hr, hb⟩ := coupling_pure hrel
      refine ⟨Ω, hr, ?_⟩
      rw [hb]
      refine weakTau_of_step rfl (composedHidden_of_tau P (composedExtended_tau_ABANetwork P ?_))
      rw [hA]
      exact ABANetworkStep.byzantineDecided ⟨w.decidedSent, w.F⟩ k b hF


/-! ### The matching on a visible shared label -/

theorem match_label (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {l : Label P.n} (hl : l ≠ Label.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakStep (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
        (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB, hI⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := systemExtended_label_inversion hl h
  have hWl : (coinOverRoundAlphabet P).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (coinLabelMap_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : ExtendedLabel P.n) ≠ Silent.τ := by
    simpa using hl
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pure_inj (networkStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callABA_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_callABA_own (hall i) with ⟨-, -, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun r => roundProjection_congr (fun i => by rw [hsame
            i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) (ABANetworkStep.callABAIdle A id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_callABA_own (hall i) with ⟨hh, hin, hx⟩ | ⟨hloop, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.input _ b hh hin
      · rw [pure_inj hx]
        by_cases hc : (u i).1.corrupted = true
        · exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
        · exact RoundLoopStep.inputLoop _ b (by simpa using hc) (hloop.resolve_left hc)
    · rw [hfor i hi]; exact RoundLoopStep.callABAIdle _ id b (Ne.symm hi)
  | retABA id b =>
    obtain ⟨hdp, hw⟩ := networkStep_retABA hn
    obtain rfl : w' = w := pure_inj hw
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retABA_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_retABA_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;>
          rw [pure_inj hx]
      · rw [hfor i hi]
    have hAn : ABANetworkStep P A (Sum.inl (Label.retABA id b)) (PMF.pure A) := by
      rw [hA]
      rcases hdp with hd | hf
      · exact ABANetworkStep.retABA ⟨w'.decidedSent, w'.F⟩ id b hd
      · exact ABANetworkStep.retByzantine ⟨w'.decidedSent, w'.F⟩ id b hf
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun r => roundProjection_congr (fun i => by rw [hsame
            i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) hAn hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_retABA_own (hall i) with ⟨hh, hin, hcnt, hret, hx⟩ | ⟨hc, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.ret _ b hh hcnt hret
      · rw [pure_inj hx]
        exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w' = w := pure_inj (networkStep_callW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callW_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_callW_own (hall i) with ⟨-, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun r => roundProjection_congr (fun i => by rw [hsame
            i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) (ABANetworkStep.callWIdle A r id) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_callW_own (hall i) with ⟨hh, hph, hr, hx⟩ | ⟨hc, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.callW _ r hh hph hr
      · rw [pure_inj hx]
        exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w' = w := pure_inj (networkStep_retW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retW_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_retW_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun r => roundProjection_congr (fun i => by rw [hsame
            i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) (ABANetworkStep.retWIdle A r id co) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_retW_own (hall i) with ⟨hh, hph, hr, hgr, hx⟩ | ⟨hc, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.retW _ r co hh hph hr hgr
      · rw [pure_inj hx]
        exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain ⟨hnew, hbud, hw⟩ := networkStep_fail hn
    obtain rfl : w' = Implementation.NetworkState.corrupt P k w := pure_inj hw
    have hfor : ∀ i, i ≠ k → x i = u i := fun i hi =>
      pure_inj (programStep_fail_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = k
      · subst hi
        rcases programStep_fail_own (hall i) with ⟨-, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    have hview : ∀ r, roundProjection P x (Implementation.NetworkState.corrupt P k w) r
        = corruptionOverBracha P (Sum.inl (Label.fail k)) (roundProjection P u w r) := fun r =>
      (roundProjection_congr (fun i => by rw [hsame i])).trans (roundProjection_fail u w r k)
    have hSI : BroadcastReturnsInvariant P x (Implementation.NetworkState.corrupt P k w) := by
      intro r
      rw [hview r]
      exact roundInvariant_both (roundInvariant_of_broadcastReturnsInvariant hI r)
        (Gather.StepOverBracha.fail _ k)
        (Gather.StepOverBracha.fail _ k)
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, ?_, ?_,
          boundInvariant_of hB (fun i r => by rw [hsame i]) (fun _ hb => by simpa using hb),
          hSI⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_fail P G k)) (fun i => ?_)
      (ABANetworkStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    · rw [hA]
      unfold ABANetworkState.corrupt Implementation.NetworkState.corrupt
      split_ifs <;> rfl
    · funext r
      rw [hGv]
      exact (hview r).symm
    · by_cases hi : i = k
      · subst hi
        rcases programStep_fail_own (hall i) with ⟨hh, hx⟩ | ⟨hh, hx⟩
        · rw [hCeq i, pure_inj hx]; exact RoundLoopStep.failSelf _ hh
        · rw [hCeq i, pure_inj hx]
          exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = (w.recordGBCASend r id (gbcaCallPayload P id b)).writeGhost (ghostStep P)
        (Sum.inl (Label.callG r id b)) := pure_inj (networkStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callG_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hest, hx1, hoff, hga2, hlow, hinv⟩ :=
      roundRecord_answer_callG P w (u := u) (j := id) rfl hI (roundRow_of_own rfl (hall id))
    obtain rfl : x id = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundRecord r'
        = ((Function.update u id (x id)) i).2.roundRecord r' := by
      intro i r'
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ), (((x i).2.roundRecord r'').secondGather.process).input
        = (((u i).2.roundRecord r'').secondGather.process).input := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hga2 r''
      · rw [hfor i hi]
    have hfam : (fun r' => roundProjection P x
          ((w.recordGBCASend r id (gbcaCallPayload P id b)).writeGhost (ghostStep P)
            (Sum.inl (Label.callG r id b))) r')
        = Function.update (fun r' => roundProjection P u w r') r
          (roundProjection P (Function.update u id (x id))
            ((w.recordGBCASend r id (gbcaCallPayload P id b)).writeGhost (ghostStep P)
              (Sum.inl (Label.callG r id b))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact roundProjection_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr']
        exact (roundProjection_congr (fun i => by
          by_cases hi : i = id
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])).trans (roundProjection_otherSent u w hr' id _ rfl)
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, hfam.symm,
          boundInvariant_of hB hxg (fun _ hb => writeGhost_bound _ (by simpa using hb)),
          broadcastReturnsInvariant_update hI hfam hinv⟩)
      (by rw [hGv]; exact roundFamilyOverBracha_weakStep P (by simp) hlow)
      (fun i => ?_) (ABANetworkStep.callGIdle A r id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rw [hx1]
      exact RoundLoopStep.callG _ r b hh hph hrr hest
    · rw [hfor i hi]; exact RoundLoopStep.callGIdle _ r id b (Ne.symm hi)
  | retG r id out bnd =>
    obtain ⟨hbnd, hw⟩ := networkStep_retG hn
    obtain rfl : w' = w.writeGhost (ghostStep P)
        (Sum.inl (Label.retG r id out bnd)) := pure_inj hw
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retG_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hx1, hoff, hga2, hlow, hinv⟩ :=
      roundRecord_answer_retG P w (u := u) (j := id) rfl hI hbnd (hB r)
        (roundRow_of_own rfl (hall id))
    obtain rfl : x id = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundRecord r'
        = ((Function.update u id (x id)) i).2.roundRecord r' := by
      intro i r'
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ), (((x i).2.roundRecord r'').secondGather.process).input
        = (((u i).2.roundRecord r'').secondGather.process).input := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hga2 r''
      · rw [hfor i hi]
    have hfam : (fun r' => roundProjection P x
          (w.writeGhost (ghostStep P) (Sum.inl (Label.retG r id out bnd))) r')
        = Function.update (fun r' => roundProjection P u w r') r
          (roundProjection P (Function.update u id (x id))
            (w.writeGhost (ghostStep P) (Sum.inl (Label.retG r id out bnd))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact roundProjection_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr',
          roundProjection_writeGhost_ne (L := Sum.inl (Label.retG r id out bnd)) _ _ rfl hr']
        exact roundProjection_congr (fun i => by
          by_cases hi : i = id
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])
    refine match_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, hfam.symm,
          boundInvariant_of hB hxg (fun _ hb => writeGhost_bound _ hb),
          broadcastReturnsInvariant_update hI hfam hinv⟩)
      (by rw [hGv]; exact roundFamilyOverBracha_weakStep P (by simp) hlow)
      (fun i => ?_) (ABANetworkStep.retGIdle A r id out bnd) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rw [hx1]
      exact RoundLoopStep.retG _ r out bnd hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.retGIdle _ r id out bnd (Ne.symm hi)


/-! ### The matching on a rendezvous of the implementation

A send and a delivery are internal to the round, so the composed system answers them with a silent
run of the graded-agreement family; the DECIDED rows, the fused coin return and the handshake rows
are answered by the same rendezvous. -/

theorem match_event (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    (e : NetworkEvent P.n (Message P.n)) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB, hI⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := systemExtended_event_inversion h
  have hrun : ∀ {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}, ν = PMF.pure o →
      ProtocolRelation P (x, w', o) (G', C, A, o) →
      (roundFamilyOverBracha P).weakLSilent G G' →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRelation P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P))
          (Ω.bind id) := by
    intro G' hν hrel hGs
    subst hν
    obtain ⟨Ω, hr, hs⟩ := match_run P hrel hGs
    refine ⟨Ω, ?_, hs⟩
    rwa [prodPMF_pure_pure, prodPMF_pure_pure]
  cases e with
  | gbcaSend r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaSend r j m) ν).mp hWs
    obtain rfl : w' = (w.recordGBCASend r j m).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.gbcaSend r j m)) := pure_inj (networkStep_gbcaSend hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pure_inj (programStep_gbcaSend_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hcore, hoff, hlow, hinv⟩ :=
      roundRecord_answer_gbcaSend P w (u := u) (j := j) rfl hI (roundRow_of_own rfl (hall j))
    obtain rfl : x j = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundRecord r'
        = ((Function.update u j (x j)) i).2.roundRecord r' := by
      intro i r'
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hfam : (fun r' => roundProjection P x
          ((w.recordGBCASend r j m).writeGhost (ghostStep P)
            (Sum.inr (NetworkEvent.gbcaSend r j m))) r')
        = Function.update (fun r' => roundProjection P u w r') r
          (roundProjection P (Function.update u j (x j))
            ((w.recordGBCASend r j m).writeGhost (ghostStep P)
              (Sum.inr (NetworkEvent.gbcaSend r j m))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact roundProjection_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr']
        exact (roundProjection_congr (fun i => by
          by_cases hi : i = j
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])).trans (roundProjection_otherSent u w hr' j m rfl)
    have hbI : BoundInvariant P x
        ((w.recordGBCASend r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) := by
      rcases roundRecord_gbcaSend_secondGather P (roundRow_of_own rfl (hall j)) with
        hkeep | ⟨q, y, rfl⟩
      · refine boundInvariant_of hB (fun i r'' => ?_)
          (fun _ hb => writeGhost_bound _ (by simpa using hb))
        by_cases hi : i = j
        · subst hi; exact hkeep _ rfl r''
        · rw [hfor i hi]
      · intro r'' i hne
        by_cases hr'' : r'' = r
        · subst hr''
          rw [writeGhost_ghostRecord_self _ rfl]
          simp [ghostStep]
        · rw [writeGhost_ghostRecord_ne _ rfl hr'']
          refine hB r'' i ?_
          by_cases hi : i = j
          · subst hi; rwa [hoff r'' hr''] at hne
          · rwa [hfor i hi] at hne
    refine hrun rfl ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i => by
        rw [hCeq i]
        by_cases hi : i = j
        · subst hi; rw [hcore]
        · rw [hfor i hi], rfl, by rw [hA]; simp, hfam.symm, hbI,
        broadcastReturnsInvariant_update hI hfam hinv⟩) ?_
    rw [hGv]
    exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hlow
  | gbcaDeliver r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaDeliver r i k m) ν).mp hWs
    obtain ⟨hsent, hw⟩ := networkStep_gbcaDeliver hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m)) :=
      pure_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pure_inj (programStep_gbcaDeliver_foreign (Ne.symm hi) (hall i'))
    obtain ⟨y, hy, hcore, hoff, hga2, hlow, hinv⟩ :=
      roundRecord_answer_gbcaDeliver P w (u := u) (j := i) rfl hI hsent
        (roundRow_of_own rfl (hall i))
    obtain rfl : x i = y := pure_inj hy
    have hxc : ∀ (i' : Fin P.n) (r' : ℕ), (x i').2.roundRecord r'
        = ((Function.update u i (x i)) i').2.roundRecord r' := by
      intro i' r'
      by_cases hi : i' = i
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i' hi]
    have hxg : ∀ (i' : Fin P.n) (r'' : ℕ), (((x i').2.roundRecord r'').secondGather.process).input
        = (((u i').2.roundRecord r'').secondGather.process).input := by
      intro i' r''
      by_cases hi : i' = i
      · subst hi; exact hga2 r''
      · rw [hfor i' hi]
    have hfam : (fun r' => roundProjection P x
          (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m))) r')
        = Function.update (fun r' => roundProjection P u w r') r
          (roundProjection P (Function.update u i (x i))
            (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact roundProjection_congr (fun i' => hxc i' r')
      · rw [Function.update_of_ne hr',
          roundProjection_writeGhost_ne
            (L := Sum.inr (NetworkEvent.gbcaDeliver r i k m)) _ _ rfl hr']
        exact roundProjection_congr (fun i' => by
          by_cases hi : i' = i
          · subst hi; exact hoff r' hr'
          · rw [hfor i' hi])
    refine hrun rfl ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i' => by
        rw [hCeq i']
        by_cases hi : i' = i
        · subst hi; rw [hcore]
        · rw [hfor i' hi], rfl, by rw [hA]; simp, hfam.symm,
        boundInvariant_of hB hxg (fun _ hb => writeGhost_bound _ hb),
        broadcastReturnsInvariant_update hI hfam hinv⟩) ?_
    rw [hGv]
    exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hlow
  | decidedSend j b =>
    obtain ⟨hd, hw⟩ := networkStep_decidedSend hn
    obtain rfl : w' = w.recordDecided j b := pure_inj hw
    have hx : ∀ i, x i = u i := by
      intro i
      by_cases hi : i = j
      · subst hi
        rcases programStep_decidedSend_self (hall i) with ⟨-, -, -, hxi⟩ | ⟨-, hxi⟩ <;>
          exact pure_inj hxi
      · exact pure_inj (programStep_decidedSend_foreign (Ne.symm hi) (hall i))
    refine match_hiddenRendezvous P (.decidedSend j b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, by rw [hA]; rfl, by
          rw [hGv]; funext r; exact (roundProjection_congr (fun i => by rw [hx i])).symm,
          boundInvariant_of hB (fun i r => by rw [hx i]) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun r => roundProjection_congr (fun i => by rw [hx
            i]))⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.decidedSend ⟨w.decidedSent, w.F⟩ j b hd) hWs
    rw [hCeq i]
    by_cases hi : i = j
    · subst hi
      rcases programStep_decidedSend_self (hall i) with ⟨hh, hin, hcnt, -⟩ | ⟨hc, -⟩
      · exact RoundLoopStep.decidedSendRelay _ b hh hcnt
      · exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · exact RoundLoopStep.decidedSendIdle _ j b (Ne.symm hi)
  | decidedDeliver i k b =>
    obtain ⟨hd, hw⟩ := networkStep_decidedDeliver hn
    obtain rfl : w' = w := pure_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pure_inj (programStep_decidedDeliver_foreign (Ne.symm hi) (hall i'))
    obtain ⟨hh, hr, hxi⟩ := programStep_decidedDeliver_self (hall i)
    have hsame : ∀ i', (x i').2 = (u i').2 := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [pure_inj hxi]
      · rw [hfor i' hi]
    refine match_hiddenRendezvous P (.decidedDeliver i k b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i' r => by rw [hsame i']) (fun _ hb => hb),
          broadcastReturnsInvariant_congr hI (fun r => roundProjection_congr (fun i' => by rw [hsame
            i']))⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i' => ?_)
      (hA ▸ ABANetworkStep.decidedDeliver ⟨w'.decidedSent, w'.F⟩ i k b hd) hWs
    rw [hCeq i']
    by_cases hi : i' = i
    · subst hi; rw [pure_inj hxi]; exact RoundLoopStep.decidedDeliverReceive _ k b hh hr
    · rw [hfor i' hi]; exact RoundLoopStep.decidedDeliverIdle _ i k b (Ne.symm hi)
  | retWPublish r id cc b =>
    obtain rfl : w' = (w.recordDecided id b).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.retWPublish r id cc b)) := pure_inj (networkStep_retWPublish hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retWPublish_foreign (Ne.symm hi) (hall i))
    obtain ⟨hh, hph, hr, hgr, hxi⟩ := programStep_retWPublish_self (hall id)
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; rw [pure_inj hxi]
      · rw [hfor i hi]
    have hview : ∀ r', roundProjection P x ((w.recordDecided id b).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.retWPublish r id cc b))) r' = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hsame i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.retWPublish r id cc b))
          (fun _ _ => rfl) u _ r')
    refine match_hiddenRendezvous P (.retWPublish r id cc b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; rfl, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInvariant_of hB (fun i r' => by rw [hsame i])
            (fun _ hb => writeGhost_bound _ hb),
          broadcastReturnsInvariant_congr hI hview⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.retWPublish ⟨w.decidedSent, w.F⟩ r id cc b) hWs
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [pure_inj hxi]
      exact RoundLoopStep.retWPublish _ r cc b hh hph hr hgr
    · rw [hfor i hi]; exact RoundLoopStep.retWPublishIdle _ r id cc b (Ne.symm hi)
  | gbcaCallLoop r id b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaCallLoop r id b) ν).mp hWs
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaCallLoop r id b)) :=
      pure_inj (networkStep_gbcaCallLoop hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_gbcaCallLoop_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hy2, hh, hph, hrr, hest, hx1, hlow⟩ :=
      roundRecord_answer_gbcaCallLoop P w (u := u) (j := id) rfl
        (roundRow_of_own rfl (hall id))
    obtain rfl : x id = y := pure_inj hy
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; exact hy2
      · rw [hfor i hi]
    have hview : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaCallLoop r id b))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hsame i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.gbcaCallLoop r id b))
          (fun _ _ => rfl) u w r')
    refine match_hiddenRendezvous P (.gbcaCallLoop r id b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInvariant_of hB (fun i r' => by rw [hsame i])
            (fun _ hb => writeGhost_bound _ hb),
          broadcastReturnsInvariant_congr hI hview⟩)
      (roundFamilyOverBracha_owned_id P G r (by simp) (by rw [hGv]; exact hlow))
      (fun i => ?_) (ABANetworkStep.gbcaCallLoop A r id b) hWs
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [hx1]; exact RoundLoopStep.gbcaCallLoop _ r b hh hph hrr hest
    · rw [hfor i hi]; exact RoundLoopStep.gbcaCallLoopIdle _ r id b (Ne.symm hi)
  | byzantineCallGLoop r k b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_byzantineCallGLoop r k b) ν).mp hWs
    obtain ⟨hF, hw⟩ := networkStep_byzantineCallGLoop hn
    obtain rfl : w' = w.writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.byzantineCallGLoop r k b)) := pure_inj hw
    have hx : ∀ i, x i = u i := fun i => pure_inj (programStep_byzantineCallGLoop (hall i))
    have hview : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallGLoop r k b))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hx i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.byzantineCallGLoop r k b))
          (fun _ _ => rfl) u w r')
    refine match_hiddenRendezvous P (.byzantineCallGLoop r k b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInvariant_of hB (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb),
          broadcastReturnsInvariant_congr hI hview⟩)
      (roundFamilyOverBracha_owned_id P G r (by simp)
        (by rw [hGv]; exact roundOverBracha_byzantineCallLoop (roundProjection P u w r) k b))
      (fun i => ?_) (hA ▸ ABANetworkStep.byzantineCallGLoop ⟨w.decidedSent, w.F⟩ r k b hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineCallGLoopIdle _ r k b
  | byzantineCallW r k =>
    obtain ⟨hF, hw⟩ := networkStep_byzantineCallW hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallW r k)) :=
      pure_inj hw
    have hx : ∀ i, x i = u i := fun i => pure_inj (programStep_byzantineCallW (hall i))
    have hview : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallW r k))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hx i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.byzantineCallW r k))
          (fun _ _ => rfl) u w r')
    refine match_hiddenRendezvous P (.byzantineCallW r k) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInvariant_of hB (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb),
          broadcastReturnsInvariant_congr hI hview⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.byzantineCallW ⟨w.decidedSent, w.F⟩ r k hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineCallWIdle _ r k
  | byzantineRetW r k b =>
    obtain ⟨hF, hw⟩ := networkStep_byzantineRetW hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineRetW r k b)) :=
      pure_inj hw
    have hx : ∀ i, x i = u i := fun i => pure_inj (programStep_byzantineRetW (hall i))
    have hview : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineRetW r k b))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hx i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.byzantineRetW r k b))
          (fun _ _ => rfl) u w r')
    refine match_hiddenRendezvous P (.byzantineRetW r k b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInvariant_of hB (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb),
          broadcastReturnsInvariant_congr hI hview⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.byzantineRetW ⟨w.decidedSent, w.F⟩ r k b hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineRetWIdle _ r k b
  | byzantineCallG r k b => exact (programStep_byzantineCallG_noStep (hall k)).elim
  | byzantineRetG r k out bnd => exact (programStep_byzantineRetG_noStep (hall k)).elim


/-! ### The matching at the group and at the system -/

/-- **The matching at the group level**: the rendezvous alphabet is hidden in both systems, so a
hidden rendezvous of the implementation is answered by a silent run of the composed group. -/
theorem match_hidden (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P s t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolHidden P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((l = Label.tau ∧ weakTau (composedHidden P) (PMF.pure t) (Ω.bind id)) ∨
          (l ≠ Label.tau ∧ weakStep (composedHidden P) (PMF.pure t) l (Ω.bind id))) := by
  obtain ⟨u, w, o⟩ := s
  obtain ⟨G, C, A, o'⟩ := t
  obtain ⟨hC, ho, hA, hGv, hB, hI⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  have hR' : ProtocolRelation P (u, w, o) (G, C, A, o) :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hGv, hB, hI⟩
  rcases (systemHidden_step_iff _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := match_event P hR' e hstep
    exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
  · by_cases hl : l = Label.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := match_tau P hR' hstep
      exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
    · obtain ⟨Ω, hrel, hs⟩ := match_label P hR' hl hstep
      exact ⟨Ω, hrel, Or.inr ⟨hl, hs⟩⟩

/-- **The matching at the system level**: a hidden sub-protocol label is silent in both systems, and
every other label is answered on the nose or by a run. -/
theorem match_step (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P s t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (system_step_iff s l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_hidden P hR hg
    rcases hlay with ⟨rfl, -⟩ | ⟨-, hlay⟩
    · exact absurd hmem Label.tau_not_mem_hiddenAPI
    · exact ⟨Ω, hrel, Or.inl ⟨rfl,
        weakTau_of_weakStep_mem (composedHidden P) (Label.hiddenAPI P.n) hmem hlay⟩⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_hidden P hR hg
    rcases hlay with ⟨rfl, hlay⟩ | ⟨hne, hlay⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl,
        weakTau_abstract (composedHidden P) (Label.hiddenAPI P.n) hlay⟩⟩
    · exact ⟨Ω, hrel, Or.inr ⟨hne,
        weakStep_abstract (composedHidden P) (Label.hiddenAPI P.n) hnm hlay⟩⟩

/-- **The gather-based protocol forward-simulates into its composed system**,
along the Dirac lift of the view. -/
theorem protocolSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (protocol P) (composed P)
      (diracRel (ProtocolRelation P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRelation_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact match_step P hR hstep

/-- **The composition inclusion**: every trace distribution the gather-based
protocol achieves is achieved by its composed system. -/
theorem protocol_composed (P : Parameters) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (composed P) :=
  (protocolSimulation P).achievableTraceDists_subset

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.AFW.protocolSimulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolSimulation

/-- info: 'PLTS.ABA.AFW.protocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_composed


end AFW

end ABA
end PLTS
