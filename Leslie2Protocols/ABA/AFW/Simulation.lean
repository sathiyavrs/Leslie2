/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.SimulationOfEachTransition
import Leslie2Protocols.Framework.DiracRelationCoupling

/-!
# The gather-based protocol into its composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed
P` reads the same protocol as a composition of components, down to the
broadcast instances. This file carries the first into the second, which is
where the gather-based chain passes from implementation to specification, as
`ABA/ABDY/Simulation.lean` does for ABDY22's. `ABA/Results.lean` takes the
inclusion from here to the ABA specification.

## The relation is a function

`AFW.ProtocolRelation` (`ABA/AFW/RoundProjection.lean`) determines the composed
state from the implementation: the round loops and the common coin are shared, the ABA network is
the DECIDED sets beside the corrupted set, and every round is the projection `AFW.roundProjection`.
`PLTS.coupling_pure` and `PLTS.coupling_map` (`Framework/DiracRelationCoupling.lean`) are the two
couplings for a Dirac outcome and for an outcome whose only free coordinate is the coin's.

## The matching, label class by label class

`AFW.coupling_tau`, `AFW.coupling_label` and `AFW.coupling_event` match the silent label, a
visible shared label and a synchronisation of the implementation, each from the runs of
`ABA/AFW/SimulationOfEachTransition.lean`. `AFW.coupling_hidden` concludes in a weak run of the
composed group, and `AFW.coupling_step` carries that run through the sub-protocol hiding with
`weakTau_abstract`, `weakTau_of_weakStep_mem` and `weakStep_abstract`.
`AFW.protocolSimulation` is the forward simulation these matchings assemble, and
`AFW.protocol_composed` the trace inclusion it yields. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

/-! ### Assembling a matched run

Three shapes of matching run: a visible shared label the four components take with one transition
each, a hidden synchronisation they take the same way, and a silent run of the graded-agreement
family alone. -/

/-- A visible shared label: the four components move together, the coin's
successor free. -/
private theorem coupling_visible (P : Parameters) {x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w' : NetworkState P.n} {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {l : Label P.n} (hl : l ≠ Label.tau)
    (hrel : ∀ o' ∈ ν.support, ProtocolRelation P (x, w', o') (G', C', A', o'))
    (hG : (roundFamilyOverBracha P).weakLStep G (Sum.inl l) G')
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inl l : ExtendedLabel P.n Empty) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inl l : ExtendedLabel P.n Empty) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P Empty).step o (Sum.inl l) ν) :
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

/-- A hidden synchronisation: the four components move together and the composed
group reads the move as silent. -/
private theorem coupling_hiddenSynchronisation (P : Parameters)
    {x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w' : NetworkState P.n} {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} (e : NetworkEvent P.n Empty)
    (hrel : ∀ o' ∈ ν.support, ProtocolRelation P (x, w', o') (G', C', A', o'))
    (hG : (roundFamilyOverBracha P).step G (Sum.inr e) (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inr e) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inr e) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P Empty).step o (Sum.inr e) ν) :
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

/-- A transition internal to the graded-agreement family: the family takes a silent run and nothing
else moves. -/
private theorem coupling_run (P : Parameters) {x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w' : NetworkState P.n} {G' G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hrel : ProtocolRelation P (x, w', o) (G', C, A, o))
    (hG : (roundFamilyOverBracha P).weakLSilent G G') :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure ((x, w', o) : ProtocolState P)) Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_pure hrel
  exact ⟨Ω, hr, hb ▸ composedHidden_weakTau P C A o hG⟩

/-- A composed state that is unchanged. -/
private theorem coupling_unchanged (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRelation P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure s) Ω ∧
      weakTau (composedHidden P) (PMF.pure t) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_pure h
  exact ⟨Ω, hr, hb ▸ weakTau_refl (composedHidden P) (PMF.pure t)⟩

/-! ### The matching on the silent label

The implementation's own `terminate` transition writes no coordinate the relation reads,
so the composed system matches it by remaining unchanged; the adversary's two injections
are matched by a transition. -/

theorem coupling_tau (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl Label.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  rcases systemExtended_tau_cases h with ⟨i, y, hstep, rfl⟩ | ⟨w', hn, rfl⟩
  · obtain ⟨b, hh, hret, hcnt, hterm, hy⟩ := programStep_tau_terminate hstep
    obtain rfl : y = ((u i).1, { (u i).2 with terminated := true }) := pure_inj hy
    have hst : ∀ (j : Fin P.n) (r : ℕ),
        ((Function.update u i ((u i).1,
            { (u i).2 with terminated := true }) j).2.roundVariables r) = ((u j).2.roundVariables r)
              := by
      intro j r
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne hj]
    have hprojection : ∀ r, roundProjection P (Function.update u i ((u i).1,
        { (u i).2 with terminated := true })) w r = roundProjection P u w r :=
      fun r => roundProjection_congr (fun j => hst j r)
    refine coupling_unchanged P ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun j => ?_, rfl, hA, ?_,
        boundInvariant_of hB (fun j r => by rw [hst j r])
            (fun j r => by rw [hst j r]) (fun j r => by rw [hst j r]) (fun _ hb => hb)⟩)
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact hC j
      · rw [Function.update_of_ne hj]; exact hC j
    · rw [hGv]
      funext r
      exact (hprojection r).symm
  · rcases networkStep_tau hn with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.recordGBCASend r k m := pure_inj hw
      have hstep := byzantine_match P u w r m hF
      have hfam := roundProjectionFamily_byzantine u w r k m
      refine coupling_run P ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
          ⟨hC, rfl, by simpa using hA, hfam.symm,
            boundInvariant_of hB (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ hb => hb)⟩) ?_
      rw [hGv]
      exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P)
        (roundOverBracha_run_one hstep)
    · obtain rfl : w' = w.recordDecided k b := pure_inj hw
      have hrel : ProtocolRelation P (u, w.recordDecided k b, o)
          (G, C, ⟨(w.recordDecided k b).decidedSent, (w.recordDecided k b).F⟩, o) :=
        (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, rfl,
          by rw [hGv]; funext r; rfl,
          boundInvariant_of hB (fun _ _ => rfl)
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ hb => hb)⟩
      obtain ⟨Ω, hr, hb⟩ := coupling_pure hrel
      refine ⟨Ω, hr, ?_⟩
      rw [hb]
      refine weakTau_of_step rfl (composedHidden_of_tau P (composedExtended_tau_ABANetwork P ?_))
      rw [hA]
      exact ABANetworkStep.byzantineDecided ⟨w.decidedSent, w.F⟩ k b hF


/-! ### The matching on a visible shared label -/

theorem coupling_label (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {l : Label P.n} (hl : l ≠ Label.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakStep (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
        (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := systemExtended_label_cases hl h
  have hWl : (coinOverRoundAlphabet P Empty).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (coinLabelMap_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : ExtendedLabel P.n Empty) ≠ Silent.τ := by
    simpa using hl
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pure_inj (networkStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callABA_notOwn (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_callABA_own (hall i) with ⟨-, -, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i])
            (fun i r => by rw [hsame i]) (fun i r => by rw [hsame i]) (fun _ hb => hb)⟩)
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
      pure_inj (programStep_retABA_notOwn (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_retABA_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;>
          rw [pure_inj hx]
      · rw [hfor i hi]
    have hAn : ABANetworkStep P A (Sum.inl (Label.retABA id b) : ExtendedLabel P.n Empty)
        (PMF.pure A) := by
      rw [hA]
      rcases hdp with hd | hf
      · exact ABANetworkStep.retABA ⟨w'.decidedSent, w'.F⟩ id b hd
      · exact ABANetworkStep.retByzantine ⟨w'.decidedSent, w'.F⟩ id b hf
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i])
            (fun i r => by rw [hsame i]) (fun i r => by rw [hsame i]) (fun _ hb => hb)⟩)
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
      pure_inj (programStep_callW_notOwn (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_callW_own (hall i) with ⟨-, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i])
            (fun i r => by rw [hsame i]) (fun i r => by rw [hsame i]) (fun _ hb => hb)⟩)
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
      pure_inj (programStep_retW_notOwn (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases programStep_retW_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i r => by rw [hsame i])
            (fun i r => by rw [hsame i]) (fun i r => by rw [hsame i]) (fun _ hb => hb)⟩)
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
      pure_inj (programStep_fail_notOwn (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = k
      · subst hi
        rcases programStep_fail_own (hall i) with ⟨-, hx⟩ | ⟨-, hx⟩ <;> rw [pure_inj hx]
      · rw [hfor i hi]
    have hprojection : ∀ r, roundProjection P x (Implementation.NetworkState.corrupt P k w) r
        = corruptionOverBracha P (Sum.inl (Label.fail k)) (roundProjection P u w r) := fun r =>
      (roundProjection_congr (fun i => by rw [hsame i])).trans (roundProjection_fail u w r k)
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, ?_, ?_,
          boundInvariant_of hB (fun i r => by rw [hsame i])
            (fun i r => by rw [hsame i]) (fun i r => by rw [hsame i])
            (fun _ hb => by simpa using hb)⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_fail P G k)) (fun i => ?_)
      (ABANetworkStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    · rw [hA]
      unfold ABANetworkState.corrupt Implementation.NetworkState.corrupt
      split_ifs <;> rfl
    · funext r
      rw [hGv]
      exact (hprojection r).symm
    · by_cases hi : i = k
      · subst hi
        rcases programStep_fail_own (hall i) with ⟨hh, hx⟩ | ⟨hh, hx⟩
        · rw [hCeq i, pure_inj hx]; exact RoundLoopStep.failSelf _ hh
        · rw [hCeq i, pure_inj hx]
          exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = w.writeGhost (ghostStep P)
        (Sum.inl (Label.callG r id b)) := pure_inj (networkStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callG_notOwn (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hest, hx1, hoff, hga2, hgc, hgo, hlow⟩ :=
      roundVariables_match_callG P w (u := u) (j := id) rfl (roundTransition_of_own rfl (hall id))
    obtain rfl : x id = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundVariables r'
        = ((Function.update u id (x id)) i).2.roundVariables r' := by
      intro i r'
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ), (((x i).2.roundVariables
      r'').secondGather.processVariables).input
        = (((u i).2.roundVariables r'').secondGather.processVariables).input := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hga2 r''
      · rw [hfor i hi]
    have hxcand : ∀ (i : Fin P.n) (r'' : ℕ), ((x i).2.roundVariables r'').candidate
        = ((u i).2.roundVariables r'').candidate := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hgc r''
      · rw [hfor i hi]
    have hxout : ∀ (i : Fin P.n) (r'' : ℕ), ((x i).2.roundVariables r'').output
        = ((u i).2.roundVariables r'').output := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hgo r''
      · rw [hfor i hi]
    have hfam : (fun r' => roundProjection P x
          (w.writeGhost (ghostStep P)
            (Sum.inl (Label.callG r id b))) r')
        = Function.update (fun r' => roundProjection P u w r') r
          (roundProjection P (Function.update u id (x id))
            (w.writeGhost (ghostStep P)
              (Sum.inl (Label.callG r id b))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact roundProjection_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr',
          roundProjection_writeGhost_ne (L := Sum.inl (Label.callG r id b)) _ _ rfl hr']
        exact roundProjection_congr (fun i => by
          by_cases hi : i = id
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, hfam.symm,
          boundInvariant_of hB hxcand hxg hxout
            (fun _ hb => writeGhost_bound _ (by simpa using hb))⟩)
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
      pure_inj (programStep_retG_notOwn (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hx1, hoff, hga2, hgc, hgo, hlow⟩ :=
      roundVariables_match_retG P w (u := u) (j := id) rfl hbnd (hB.1 r)
        (fun i h => (hB.2 r i).2 ((hB.2 r i).1 h)) (roundTransition_of_own rfl (hall id))
    obtain rfl : x id = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundVariables r'
        = ((Function.update u id (x id)) i).2.roundVariables r' := by
      intro i r'
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ), (((x i).2.roundVariables
      r'').secondGather.processVariables).input
        = (((u i).2.roundVariables r'').secondGather.processVariables).input := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hga2 r''
      · rw [hfor i hi]
    have hxcand : ∀ (i : Fin P.n) (r'' : ℕ), ((x i).2.roundVariables r'').candidate
        = ((u i).2.roundVariables r'').candidate := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hgc r''
      · rw [hfor i hi]
    have hxout : ∀ (i : Fin P.n) (r'' : ℕ), ((x i).2.roundVariables r'').output ≠ none →
        ((u i).2.roundVariables r'').output ≠ none := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hgo r''
      · rw [hfor i hi]; exact fun h => h
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
    refine coupling_visible P hl (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, hfam.symm,
          boundInvariant_ofOutputCleared hB hxcand hxg hxout
            (fun _ hb => writeGhost_bound _ hb)⟩)
      (by rw [hGv]; exact roundFamilyOverBracha_weakStep P (by simp) hlow)
      (fun i => ?_) (ABANetworkStep.retGIdle A r id out bnd) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rw [hx1]
      exact RoundLoopStep.retG _ r out bnd hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.retGIdle _ r id out bnd (Ne.symm hi)


/-! ### The matching on a synchronisation of the implementation

A send and a delivery are internal to the round, so the composed system matches them with a silent
run of the graded-agreement family. The DECIDED transitions, the fused coin return and the
call and return transitions are matched by the same synchronisation. -/

theorem coupling_event (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    (e : Implementation.NetworkEvent P.n (Message P.n) (RoundEvent P.n)) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := systemExtended_event_cases h
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
    obtain ⟨Ω, hr, hs⟩ := coupling_run P hrel hGs
    refine ⟨Ω, ?_, hs⟩
    rwa [prodPMF_pure_pure, prodPMF_pure_pure]
  cases e with
  | gbcaRoundEvent r j ev =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaRoundEvent r j ev) ν).mp hWs
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaRoundEvent r j ev)) :=
      pure_inj (networkStep_gbcaRoundEvent hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pure_inj (programStep_gbcaRoundEvent_notOwn (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hcore, hoff, hga2, hlow⟩ :=
      roundVariables_match_gbcaRoundEvent P w (u := u) (j := j) rfl
        (roundTransition_of_own rfl (hall j))
    obtain rfl : x j = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundVariables r'
        = ((Function.update u j (x j)) i).2.roundVariables r' := by
      intro i r'
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ),
        (((x i).2.roundVariables r'').secondGather.processVariables).input
            = (((u i).2.roundVariables r'').secondGather.processVariables).input ∨
          ((((x i).2.roundVariables r'').secondGather.processVariables).input ≠ none ∧
            ((u i).2.roundVariables r'').candidate ≠ none) := by
      intro i r''
      by_cases hi : i = j
      · subst hi; exact hga2 r''
      · exact Or.inl (by rw [hfor i hi])
    have hfam : (fun r' => roundProjection P x
          (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaRoundEvent r j ev))) r')
        = Function.update (fun r' => roundProjection P u w r') r
          (roundProjection P (Function.update u j (x j))
            (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaRoundEvent r j ev))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact roundProjection_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr',
          roundProjection_writeGhost_ne
            (L := Sum.inr (NetworkEvent.gbcaRoundEvent r j ev)) _ _ rfl hr']
        exact roundProjection_congr (fun i => by
          by_cases hi : i = j
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])
    have hcandAt : ∀ (i : Fin P.n) (r'' : ℕ), ((u i).2.roundVariables r'').candidate ≠ none →
        ((x i).2.roundVariables r'').candidate ≠ none := by
      intro i r'' hne
      by_cases hi : i = j
      · subst hi
        by_cases hr'' : r'' = r
        · subst hr''
          rcases roundVariables_candidate_gbcaRoundEvent P
            (roundTransition_of_own rfl (hall i)) with hkeep | ⟨hsome, -⟩
          · rw [hkeep _ rfl]; exact hne
          · exact hsome _ rfl
        · rw [hoff r'' hr'']; exact hne
      · rw [hfor i hi]; exact hne
    have hbI : BoundInvariant P x
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaRoundEvent r j ev))) := by
      refine ⟨fun r'' i hne => ?_, fun r'' i => ?_⟩
      · by_cases hi : i = j
        · subst hi
          by_cases hr'' : r'' = r
          · subst hr''
            rcases roundVariables_candidate_gbcaRoundEvent P
              (roundTransition_of_own rfl (hall i)) with hkeep | ⟨-, y, rfl⟩
            · exact writeGhost_bound _ (hB.1 r'' i (by rw [← hkeep _ rfl]; exact hne))
            · rw [writeGhost_ghost_self _ rfl]; simp [ghostStep]
          · rw [writeGhost_ghost_ne _ rfl hr'']
            exact hB.1 r'' i (by rw [← hoff r'' hr'']; exact hne)
        · rw [hfor i hi] at hne
          exact writeGhost_bound _ (hB.1 r'' i hne)
      · rcases hxg i r'' with heq | ⟨hne, hc⟩
        · refine ⟨fun ho => ?_, fun hs => hcandAt i r'' ((hB.2 r'' i).2 ?_)⟩
          · rw [heq]
            by_cases hi : i = j
            · subst hi
              by_cases hr'' : r'' = r
              · subst hr''
                rcases roundVariables_output_gbcaRoundEvent P
                  (roundTransition_of_own rfl (hall i)) with hkeep | hin
                · exact (hB.2 r'' i).1 (by rw [← hkeep _ rfl]; exact ho)
                · exact hin
              · exact (hB.2 r'' i).1 (by rw [← hoff r'' hr'']; exact ho)
            · rw [hfor i hi] at ho
              exact (hB.2 r'' i).1 ho
          · rw [← heq]; exact hs
        · exact ⟨fun _ => hne, fun _ => hcandAt i r'' hc⟩
    refine hrun rfl ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i => by
        rw [hCeq i]
        by_cases hi : i = j
        · subst hi; rw [hcore]
        · rw [hfor i hi], rfl, by rw [hA]; simp, hfam.symm, hbI⟩) ?_
    rw [hGv]
    exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hlow
  | gbcaSend r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaSend r j m) ν).mp hWs
    obtain rfl : w' = (w.recordGBCASend r j m).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.gbcaSend r j m)) := pure_inj (networkStep_gbcaSend hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pure_inj (programStep_gbcaSend_notOwn (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hcore, hoff, hgc, hgo, hgi, hlow⟩ :=
      roundVariables_match_gbcaSend P w (u := u) (j := j) rfl (roundTransition_of_own rfl (hall j))
    obtain rfl : x j = y := pure_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.roundVariables r'
        = ((Function.update u j (x j)) i).2.roundVariables r' := by
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
      refine boundInvariant_ofSecondGatherCall hB (fun i r'' => ?_) (fun i r'' => ?_)
        (fun i r'' => ?_) (fun _ hb => writeGhost_bound _ (by simpa using hb))
      · by_cases hi : i = j
        · subst hi; exact hgc r''
        · rw [hfor i hi]
      · by_cases hi : i = j
        · subst hi; exact hgo r''
        · rw [hfor i hi]
      · by_cases hi : i = j
        · subst hi
          by_cases hr'' : r'' = r
          · subst hr''; exact hgi
          · exact Or.inl (by rw [hoff r'' hr''])
        · exact Or.inl (by rw [hfor i hi])
    refine hrun rfl ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i => by
        rw [hCeq i]
        by_cases hi : i = j
        · subst hi; rw [hcore]
        · rw [hfor i hi], rfl, by rw [hA]; simp, hfam.symm, hbI⟩) ?_
    rw [hGv]
    exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hlow
  | gbcaDeliver r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaDeliver r i k m) ν).mp hWs
    obtain ⟨hsent, hw⟩ := networkStep_gbcaDeliver hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m)) :=
      pure_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pure_inj (programStep_gbcaDeliver_notOwn (Ne.symm hi) (hall i'))
    obtain ⟨y, hy, hcore, hoff, hga2, hgc, hgo, hlow⟩ :=
      roundVariables_match_gbcaDeliver P w (u := u) (j := i) rfl hsent
        (roundTransition_of_own rfl (hall i))
    obtain rfl : x i = y := pure_inj hy
    have hxc : ∀ (i' : Fin P.n) (r' : ℕ), (x i').2.roundVariables r'
        = ((Function.update u i (x i)) i').2.roundVariables r' := by
      intro i' r'
      by_cases hi : i' = i
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i' hi]
    have hxg : ∀ (i' : Fin P.n) (r'' : ℕ), (((x i').2.roundVariables
      r'').secondGather.processVariables).input
        = (((u i').2.roundVariables r'').secondGather.processVariables).input := by
      intro i' r''
      by_cases hi : i' = i
      · subst hi; exact hga2 r''
      · rw [hfor i' hi]
    have hxcand : ∀ (i' : Fin P.n) (r'' : ℕ), ((x i').2.roundVariables r'').candidate
        = ((u i').2.roundVariables r'').candidate := by
      intro i' r''
      by_cases hi : i' = i
      · subst hi; exact hgc r''
      · rw [hfor i' hi]
    have hxout : ∀ (i' : Fin P.n) (r'' : ℕ), ((x i').2.roundVariables r'').output
        = ((u i').2.roundVariables r'').output := by
      intro i' r''
      by_cases hi : i' = i
      · subst hi; exact hgo r''
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
        boundInvariant_of hB hxcand hxg hxout (fun _ hb => writeGhost_bound _ hb)⟩) ?_
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
      · exact pure_inj (programStep_decidedSend_notOwn (Ne.symm hi) (hall i))
    refine coupling_hiddenSynchronisation P (.decidedSend j b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, by rw [hA]; rfl, by
          rw [hGv]; funext r; exact (roundProjection_congr (fun i => by rw [hx i])).symm,
          boundInvariant_of hB (fun i r => by rw [hx i])
            (fun i r => by rw [hx i]) (fun i r => by rw [hx i]) (fun _ hb => hb)⟩)
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
      pure_inj (programStep_decidedDeliver_notOwn (Ne.symm hi) (hall i'))
    obtain ⟨hh, hr, hxi⟩ := programStep_decidedDeliver_self (hall i)
    have hsame : ∀ i', (x i').2 = (u i').2 := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [pure_inj hxi]
      · rw [hfor i' hi]
    refine coupling_hiddenSynchronisation P (.decidedDeliver i k b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact roundProjection_unchanged hsame w',
          boundInvariant_of hB (fun i' r => by rw [hsame i'])
            (fun i' r => by rw [hsame i']) (fun i' r => by rw [hsame i']) (fun _ hb => hb)⟩)
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
      pure_inj (programStep_retWPublish_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hh, hph, hr, hgr, hxi⟩ := programStep_retWPublish_self (hall id)
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; rw [pure_inj hxi]
      · rw [hfor i hi]
    have hprojection : ∀ r', roundProjection P x ((w.recordDecided id b).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.retWPublish r id cc b))) r' = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hsame i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.retWPublish r id cc b))
          (fun _ _ => rfl) u _ r')
    refine coupling_hiddenSynchronisation P (.retWPublish r id cc b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; rfl, by rw [hGv]; funext r'; exact (hprojection r').symm,
          boundInvariant_of hB (fun i r' => by rw [hsame i])
            (fun i r' => by rw [hsame i]) (fun i r' => by rw [hsame i])
            (fun _ hb => writeGhost_bound _ hb)⟩)
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
      pure_inj (programStep_gbcaCallLoop_notOwn (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hy2, hh, hph, hrr, hest, hx1, hlow⟩ :=
      roundVariables_match_gbcaCallLoop P w (u := u) (j := id) rfl
        (roundTransition_of_own rfl (hall id))
    obtain rfl : x id = y := pure_inj hy
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; exact hy2
      · rw [hfor i hi]
    have hprojection : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaCallLoop r id b))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hsame i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.gbcaCallLoop r id b))
          (fun _ _ => rfl) u w r')
    refine coupling_hiddenSynchronisation P (.gbcaCallLoop r id b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, by rw [hGv]; funext r'; exact (hprojection r').symm,
          boundInvariant_of hB (fun i r' => by rw [hsame i])
            (fun i r' => by rw [hsame i]) (fun i r' => by rw [hsame i])
            (fun _ hb => writeGhost_bound _ hb)⟩)
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
    have hprojection : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallGLoop r k b))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hx i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.byzantineCallGLoop r k b))
          (fun _ _ => rfl) u w r')
    refine coupling_hiddenSynchronisation P (.byzantineCallGLoop r k b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hprojection r').symm,
          boundInvariant_of hB (fun i r' => by rw [hx i])
            (fun i r' => by rw [hx i]) (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb)⟩)
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
    have hprojection : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallW r k))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hx i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.byzantineCallW r k))
          (fun _ _ => rfl) u w r')
    refine coupling_hiddenSynchronisation P (.byzantineCallW r k) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hprojection r').symm,
          boundInvariant_of hB (fun i r' => by rw [hx i])
            (fun i r' => by rw [hx i]) (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb)⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.byzantineCallW ⟨w.decidedSent, w.F⟩ r k hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineCallWIdle _ r k
  | byzantineRetW r k b =>
    obtain ⟨hF, hw⟩ := networkStep_byzantineRetW hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineRetW r k b)) :=
      pure_inj hw
    have hx : ∀ i, x i = u i := fun i => pure_inj (programStep_byzantineRetW (hall i))
    have hprojection : ∀ r', roundProjection P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineRetW r k b))) r'
          = roundProjection P u w r' := fun r' =>
      (roundProjection_congr (fun i => by rw [hx i])).trans
        (roundProjection_ghostId (Sum.inr (NetworkEvent.byzantineRetW r k b))
          (fun _ _ => rfl) u w r')
    refine coupling_hiddenSynchronisation P (.byzantineRetW r k b) (fun o' _ =>
      (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hprojection r').symm,
          boundInvariant_of hB (fun i r' => by rw [hx i])
            (fun i r' => by rw [hx i]) (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb)⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.byzantineRetW ⟨w.decidedSent, w.F⟩ r k b hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineRetWIdle _ r k b
  | byzantineCallG r k b => exact (programStep_byzantineCallG_noStep (hall k)).elim
  | byzantineRetG r k out bnd => exact (programStep_byzantineRetG_noStep (hall k)).elim


/-! ### The matching at the group and at the system -/

/-- **The matching at the group level**: the labels the components synchronise on are hidden in both
systems, so a hidden synchronisation of the implementation is matched by a silent run of the
composed group. -/
theorem coupling_hidden (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P s t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolHidden P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((l = Label.tau ∧ weakTau (composedHidden P) (PMF.pure t) (Ω.bind id)) ∨
          (l ≠ Label.tau ∧ weakStep (composedHidden P) (PMF.pure t) l (Ω.bind id))) := by
  obtain ⟨u, w, o⟩ := s
  obtain ⟨G, C, A, o'⟩ := t
  obtain ⟨hC, ho, hA, hGv, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  have hR' : ProtocolRelation P (u, w, o) (G, C, A, o) :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hGv, hB⟩
  rcases (systemHidden_step_iff _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := coupling_event P hR' e hstep
    exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
  · by_cases hl : l = Label.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := coupling_tau P hR' hstep
      exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
    · obtain ⟨Ω, hrel, hs⟩ := coupling_label P hR' hl hstep
      exact ⟨Ω, hrel, Or.inr ⟨hl, hs⟩⟩

/-- **The matching at the system level**: a hidden sub-protocol label is silent in both systems, and
every other label is matched on the nose or by a run. -/
theorem coupling_step (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P s t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (system_step_iff s l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := coupling_hidden P hR hg
    rcases hlay with ⟨rfl, -⟩ | ⟨-, hlay⟩
    · exact absurd hmem Label.tau_not_mem_hiddenAPI
    · exact ⟨Ω, hrel, Or.inl ⟨rfl,
        weakTau_of_weakStep_mem (composedHidden P) (Label.hiddenAPI P.n) hmem hlay⟩⟩
  · obtain ⟨Ω, hrel, hlay⟩ := coupling_hidden P hR hg
    rcases hlay with ⟨rfl, hlay⟩ | ⟨hne, hlay⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl,
        weakTau_abstract (composedHidden P) (Label.hiddenAPI P.n) hlay⟩⟩
    · exact ⟨Ω, hrel, Or.inr ⟨hne,
        weakStep_abstract (composedHidden P) (Label.hiddenAPI P.n) hnm hlay⟩⟩

/-- **The gather-based protocol forward-simulates into its composed system**,
along the Dirac lift of the projection. -/
theorem protocolSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (protocol P) (composed P)
      (diracRel (ProtocolRelation P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRelation_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact coupling_step P hR hstep

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
