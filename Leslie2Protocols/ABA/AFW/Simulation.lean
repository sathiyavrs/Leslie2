/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.SimulationOfEachTransition
import Leslie2Protocols.ABA.Composition.ABAState
import Leslie2Protocols.Framework.DiracRelationCoupling

/-!
# The gather-based protocol into its composed system

`AFW.protocol P` is the gather-based protocol as it runs, and `AFW.composed P` reads the same
protocol as a composition of components, with the broadcast instances beneath. This file carries
the first into the second, as `ABA/ABDY/Simulation.lean` does for ABDY22's protocol. This is where
the gather-based chain passes from implementation to specification, and `ABA/Results.lean` takes
the inclusion from here to the ABA specification.

## The relation

`AFW.ProtocolRelation` (`ABA/AFW/RoundProjection.lean`) determines the composed state from the
protocol state. The round loops and the common coin are shared. The ABA network is the protocol
network's DECIDED sets beside its corrupted set and its started rounds, and the rounds of the
family's map are the started rounds (D37). Every round of the family is the projection
`AFW.roundProjection`. The last three conjuncts are invariants of the protocol state. At a round
outside the started rounds no process has sent, the ghost holds nothing and no process holds
variables. Every process of the corrupted set has a replaced program (D23). `AFW.BoundInvariant`
states what the projection needs of the ghost.
`PLTS.coupling_pure` and `PLTS.coupling_map` (`Framework/DiracRelationCoupling.lean`) are the two
couplings the relation supplies: a Dirac protocol outcome is matched by a single composed state,
and an outcome whose only free coordinate is the coin's is matched outcome by outcome.

## The started rounds

A graded-agreement call by a process with an unreplaced program records the called round among the
started rounds, and the family enters that round in its map on the same call. Every other
transition at round `r` reads variables of round `r` other than the initial ones, a message sent
at round `r`, or the ghost of round `r`, so `r` is a started round and a round of the family's map,
where the family takes the round's silent transitions. The network's Byzantine injection and a
corrupted process's two calls fire at a started round (D11, D37).

## The matching, by label class

`AFW.coupling_tau`, `AFW.coupling_label` and `AFW.coupling_event` match the silent label, a
visible shared label and a synchronisation of the implementation, from the runs of
`ABA/AFW/SimulationOfEachTransition.lean`.

* A send, a delivery and a round event of a process at round `r` are matched by a silent run of
  round `r`. The first gather's return is matched by two hidden events of the round: the gather's
  return, on which the process records its candidate and the gather records its core, and the
  gather's announcement of that core, which the round's network records where none is recorded.
* The graded-agreement call and the graded return are matched by the round's own call and return
  on the same labels. The call is taken on two transitions (D36): at a first gather holding no
  input the round records the input, and at one holding an input the round takes its `callLoop`
  and its state stands.
* The announcement `boundG r b` of a round's bound bit is matched by the round's own announcement
  on the same label (`roundOverBracha_announceBound`, D29). Where the ghost of round `r` holds the
  bit `b`, the round's network state records a first gather's core `C` with
  `b = GBCA.boundOfCore P C` and records the round's return
  (`BoundInvariant.announceBound_networkProjection`), which is what the round's announcement asks.
  The state stands in both systems.
* A corrupted process's graded-agreement call leaves the protocol state where it stands, and it is
  matched by the empty run. A corrupted process's coin call moves the coin, and it is matched by
  the composed system's own `byzantineCallW` event: the ABA network outputs it under `k ∈ F` at a
  started round, and the coin takes it on the same transition (D11, D37).
* The replaced program's own ABA return and a round delivery at a replaced program are the
  program's self-loop (D23). The round loop matches the return on its own self-loop, and the
  delivery leaves the protocol state where it stands and is matched by the empty run. The
  termination of a process writes a flag the relation does not read, and it is matched by the
  empty run.

`AFW.coupling_hidden` concludes in a weak run of the composed group, and `AFW.coupling_step`
applies the sub-protocol hiding to that run with `weakTau_abstract`, `weakTau_of_weakStep_mem` and
`weakStep_abstract`. `AFW.protocolSimulation` is the forward simulation these matchings assemble,
and `AFW.protocol_composed` the trace inclusion it yields. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

/-! ### Assembling a matched run

Five shapes of matching run. A visible shared label is taken by the four components with one
transition each, the family by a run. A synchronisation the composed system has as an event of its
own is taken the same way and read as silent. A transition internal to the graded-agreement family
is matched by a silent run of the family alone, and a transition of one process at one round by a
silent run of that round. A transition that leaves the protocol state where it stands is matched by
the empty run. -/

/-- A visible shared label: the four components move together, the coin's
successor free. -/
private theorem coupling_visible (P : Parameters) {x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w' : NetworkState P.n} {G G' : RoundFamilyOverBrachaState P}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ν : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    {l : Label P.n} (hl : l ≠ Label.tau)
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

/-- An event of the composed system: the four components move together, and the composed group
reads the move as silent. -/
private theorem coupling_hiddenSynchronisation (P : Parameters)
    {x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w' : NetworkState P.n}
    {G G' : RoundFamilyOverBrachaState P} {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ν : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    (e : NetworkEvent P.n Empty)
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
    {w' : NetworkState P.n} {G G' : RoundFamilyOverBrachaState P}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hrel : ProtocolRelation P (x, w', o) (G', C, A, o))
    (hG : (roundFamilyOverBracha P).weakLSilent G G') :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure ((x, w', o) : ProtocolState P)) Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_pure hrel
  exact ⟨Ω, hr, hb ▸ composedHidden_weakTau P C A o hG⟩

/-- A protocol state that stands, matched by the empty run. -/
private theorem coupling_unchanged (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRelation P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure s) Ω ∧
      weakTau (composedHidden P) (PMF.pure t) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := coupling_pure h
  exact ⟨Ω, hr, hb ▸ weakTau_refl (composedHidden P) (PMF.pure t)⟩

/-- A transition of process `j` at a started round `r`, every other process idle and the coin
standing, matched by a silent run of round `r` of the family. -/
private theorem coupling_roundRun (P : Parameters) {u x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w v : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o)) {r : ℕ}
    {j : Fin P.n} {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    (hL : roundOf L = some r) (hstep : RoundStep P j (u j) L (PMF.pure (x j)))
    (hfor : ∀ i, i ≠ j → x i = u i) (hcore : (x j).1 = (u j).1) (hr : r ∈ w.startedRounds)
    (hd : v.decidedSent = w.decidedSent) (hF : v.F = w.F)
    (hStarted : v.startedRounds = w.startedRounds) (hsent : ∀ r', r' ≠ r → v.sent r' = w.sent r')
    (hghost : ∀ r', v.ghost r' = w.ghost r')
    (hrun : (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
      (roundProjection P (Function.update u j (x j)) (v.writeGhost (ghostStep P) L) r)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure (v.writeGhost (ghostStep P) L)) (PMF.pure o)))
        Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, -, hG, -, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hrel := relation_roundStep P hR (o' := o) (C' := C) (A' := A) hL hstep hfor
    (by rw [hcore])
    (fun i => by
      by_cases hi : i = j
      · subst hi; rw [hcore]; exact hC i
      · rw [hfor i hi]; exact hC i)
    (by rw [hA, hd, hF, hStarted]) (by rw [hStarted, Finset.insert_eq_of_mem hr]) hF hsent hghost
  obtain ⟨Ω, hΩ, hs⟩ := coupling_run P hrel
    (roundFamilyOverBracha_silentRun P (mem_keys_of_mem_startedRounds hR hr)
      (by rw [hG r]; exact hrun))
  exact ⟨Ω, by rwa [prodPMF_pure_pure, prodPMF_pure_pure], hs⟩

/-! ### The matching on the silent label

The implementation's own `terminate` transition writes no coordinate the relation reads, so it is
matched by the empty run. The network's Byzantine injection at a started round is a silent
transition of that round of the family, the Byzantine DECIDED injection a silent transition of the
ABA network, and the resolution of a round of the common coin a silent transition of the coin. -/

/-- The matching on the silent label: every silent transition of the implementation is matched
by a silent run of the composed group. -/
theorem coupling_tau (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl Label.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, -, hG, -, -, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  rcases systemExtended_tau_cases h with ⟨i, y, hstep, rfl⟩ | ⟨w', hn, rfl⟩ |
    ⟨r, hr, μw, hW, rfl⟩
  · obtain ⟨-, -, -, -, -, hy⟩ := programStep_tau_terminate hstep
    obtain rfl : y = ((u i).1, { (u i).2 with terminated := true }) := pure_inj hy
    refine coupling_unchanged P (protocolRelation_noRound hR (fun j => ?_) hA (fun j => ?_)
      (fun j => ?_) (fun _ => rfl) (fun _ => rfl) rfl rfl)
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact hC j
      · rw [Function.update_of_ne hj]; exact hC j
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]
      · rw [Function.update_of_ne hj]
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]
      · rw [Function.update_of_ne hj]
  · rcases networkStep_tau hn with ⟨r, k, m, hF, hr, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.recordGBCASend r k m := pure_inj hw
      have hrel : ProtocolRelation P (u, w.recordGBCASend r k m, o)
          (G.setInstanceState r (roundProjection P u (w.recordGBCASend r k m) r), C, A, o) :=
        protocolRelation_setInstanceState hR r rfl hC (by rw [hA]; rfl)
          (by rw [recordGBCASend_startedRounds, Finset.insert_eq_of_mem hr]) rfl
          (fun r' h => recordGBCASend_sent_ne w r k m h) (fun _ _ => rfl) (fun _ _ _ => rfl)
          (fun _ => rfl)
          (boundInvariant_of_roundVariables hB (fun _ _ => rfl)
            (fun _ => ⟨Sum.inl Label.tau, w, rfl⟩))
      exact coupling_run P hrel
        (roundFamilyOverBracha_silentRun P (mem_keys_of_mem_startedRounds hR hr)
          (by rw [hG r]; exact roundOverBracha_run_one (byzantine_match P u w r m hF)))
    · obtain rfl : w' = w.recordDecided k b := pure_inj hw
      obtain ⟨Ω, hΩ, hb⟩ := coupling_pure (protocolRelation_noRound hR (x := u)
        (w' := w.recordDecided k b) (o' := o) (C' := C) (A' := A.recordDecided k b) hC
        (by rw [hA]; rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl)
      refine ⟨Ω, hΩ, ?_⟩
      rw [hb]
      exact weakTau_of_step rfl (composedHidden_of_tau P (composedExtended_tau_ABANetwork P
        (ABANetworkStep.byzantineDecided A k b (by rw [hA]; exact hF))))
  · obtain ⟨Ω, hΩ, hb⟩ := coupling_map (μw.map (o.setInstanceState r))
      (fun o' => ((u, w, o') : ProtocolState P)) (fun o' => ((G, C, A, o') : ComposedState P))
      (fun o' _ => protocolRelation_noRound hR (x := u) (w' := w) (o' := o') hC hA
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl)
    rw [← prodPMF_two_pure_factors] at hΩ
    rw [← prodPMF_three_pure_factors] at hb
    refine ⟨Ω, hΩ, ?_⟩
    rw [hb]
    exact weakTau_of_step rfl (composedHidden_of_tau P (composedExtended_tau_coin P hr hW))

/-! ### The matching on a visible shared label

The ABA interface and the coin's calls and returns move no round, and the family idles on them.
Corruption is broadcast to every round of the family. The graded-agreement call and the graded
return are the round's own, and the family passes them to the round. The announcement of a round's
bound bit is the round's own announcement, and both states stand. -/

/-- The matching on a visible shared label: every one is matched by a weak transition of the
composed group on the same label. -/
theorem coupling_label (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {l : Label P.n} (hl : l ≠ Label.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakStep (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
        (Ω.bind id) := by
  obtain ⟨hC, -, hA, -, hG, -, hCorrupted, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := systemExtended_label_cases hl h
  have hWl : (coinOverRoundAlphabet P Empty).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (coinLabelMap_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : ExtendedLabel P.n Empty) ≠ Silent.τ := by
    simpa using hl
  have hLtau : (Sum.inl l : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) ≠
      Sum.inl Label.tau := by
    simpa using hl
  have hstand : (∀ i, ¬ roundOwn i
        (Sum.inl l : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))) →
      (∀ k, l ≠ Label.fail k) →
      (∀ i, (x i).2.roundVariablesMap = (u i).2.roundVariablesMap) ∧
        ∀ i, (x i).1.corrupted = (u i).1.corrupted := fun hown hf =>
    ⟨fun i => by
      rw [(programStep_notRound (hown i) hLtau (fun k hk => hf k (Sum.inl_injective hk))
        (hall i)).2],
      fun i => (programStep_notRound (hown i) hLtau (fun k hk => hf k (Sum.inl_injective hk))
        (hall i)).1⟩
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pure_inj (networkStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callABA_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hl (fun o' _ => protocolRelation_noRound hR (fun _ => rfl) hA hmap
        hrep (fun _ => rfl) (fun _ => rfl) rfl rfl)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne rfl not_false))
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
    obtain rfl : w' = w := pure_inj (networkStep_retABA hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retABA_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hl (fun o' _ => protocolRelation_noRound hR (fun _ => rfl) hA hmap
        hrep (fun _ => rfl) (fun _ => rfl) rfl rfl)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne rfl not_false))
      (fun i => ?_) (ABANetworkStep.retABAIdle A id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_retABA_own (hall i) with ⟨hh, -, hcnt, hsent, hret, hx⟩ | ⟨hc, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.ret _ b hh hcnt hsent hret
      · rw [pure_inj hx]; exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w' = w := pure_inj (networkStep_callW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callW_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hl (fun o' _ => protocolRelation_noRound hR (fun _ => rfl) hA hmap
        hrep (fun _ => rfl) (fun _ => rfl) rfl rfl)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne rfl not_false))
      (fun i => ?_) (ABANetworkStep.callWIdle A r id) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      obtain ⟨hh, hph, hrr, hx⟩ := programStep_callW_own (hall i)
      rw [pure_inj hx]; exact RoundLoopStep.callW _ r hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w' = w := pure_inj (networkStep_retW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retW_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hl (fun o' _ => protocolRelation_noRound hR (fun _ => rfl) hA hmap
        hrep (fun _ => rfl) (fun _ => rfl) rfl rfl)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne rfl not_false))
      (fun i => ?_) (ABANetworkStep.retWIdle A r id co) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_retW_own (hall i) with ⟨hh, hph, hrr, hx⟩ | ⟨hh, hnot, hx⟩ | ⟨hh, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.retW _ r co hh hph hrr
      · rw [pure_inj hx]; exact RoundLoopStep.retWLoop _ r co hh hnot
      · rw [pure_inj hx]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain ⟨hnew, hbud, hw⟩ := networkStep_fail hn
    obtain rfl : w' = Implementation.NetworkState.corrupt P k w := pure_inj hw
    have hfor : ∀ i, i ≠ k → x i = u i := fun i hi =>
      pure_inj (programStep_fail_notOwn (Ne.symm hi) (hall i))
    have hk : (x k).2 = (u k).2 ∧ (x k).1.corrupted = true := by
      rcases programStep_fail_own (hall k) with ⟨-, hxk⟩ | ⟨hh, hxk⟩ <;> rw [pure_inj hxk]
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, hh⟩
    have hsame : ∀ i, (x i).2 = (u i).2 := fun i => by
      by_cases hi : i = k
      · subst hi; exact hk.1
      · rw [hfor i hi]
    have hst : ∀ i r, (x i).2.roundVariables r = (u i).2.roundVariables r := fun i r => by
      rw [hsame i]
    have hF : (Implementation.NetworkState.corrupt P k w).F = insert k w.F := by
      simp [Implementation.NetworkState.corrupt, hnew, hbud]
    have hrel : ∀ o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P),
        ProtocolRelation P (x, Implementation.NetworkState.corrupt P k w, o')
          (G.applyBroadcast (Sum.inl (Label.fail k)), fun i => (x i).1,
            ABANetworkState.corrupt P k A, o') := fun o' =>
      protocolRelation_sameRounds hR (fun _ => rfl) (by rw [hA]; exact corrupt_abaNetwork w k)
        (InstanceFamilyState.keys_applyBroadcast _ _)
        (fun r => by
          rw [InstanceFamilyState.applyBroadcast_apply, hG r,
            roundProjection_congr (fun i => hst i r)]
          exact (roundProjection_fail u w r k).symm)
        (networkCorrupt_startedRounds w k) (fun r => by rw [networkCorrupt_sent])
        (fun r => by rw [networkCorrupt_ghost]) (fun i => by rw [hsame i])
        (fun j hj => by
          rw [hF, Finset.mem_insert] at hj
          by_cases hjk : j = k
          · subst hjk; exact hk.2
          · rw [hfor j hjk]; exact hCorrupted j (hj.resolve_left hjk))
        (boundInvariant_of_roundVariables hB hst
          fun r => ⟨Sum.inl Label.tau, w, congrFun (networkCorrupt_ghost w k) r⟩)
    refine coupling_visible P hl (fun o' _ => hrel o')
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_fail P G k)) (fun i => ?_)
      (ABANetworkStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    rw [hCeq i]
    by_cases hi : i = k
    · subst hi
      rcases programStep_fail_own (hall i) with ⟨hh, hxk⟩ | ⟨hh, hxk⟩
      · rw [pure_inj hxk]; exact RoundLoopStep.failSelf _ hh
      · rw [pure_inj hxk]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = (w.recordStartedRound r id).writeGhost (ghostStep P)
        (Sum.inl (Label.callG r id b)) := pure_inj (networkStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_callG_notOwn (Ne.symm hi) (hall i))
    have hstep := roundTransition_of_own (by exact rfl) (by simp) (hall id)
    obtain ⟨y, hy, hh, hph, hrr, hest, hx1, -, -, -, -, -, hlow⟩ :=
      roundVariables_match_callG P w (u := u) (j := id) rfl hstep
    obtain rfl : x id = y := pure_inj hy
    have hid : id ∉ w.F := notMem_F_of_corrupted hR hh
    refine coupling_visible P hl (fun o' _ => relation_roundStep P hR (o' := o')
        (A' := A.recordStartedRound r id) rfl hstep hfor (by rw [hx1]; rfl) (fun _ => rfl)
        (by
          rw [hA]
          simp [ABANetworkState.recordStartedRound,
            Implementation.NetworkState.recordStartedRound, hid])
        (startedRounds_recordStartedRound hR hh r) (recordStartedRound_F w r id)
        (fun r' _ => by rw [recordStartedRound_sent]) (fun r' => by rw [recordStartedRound_ghost]))
      (System.weakLStep_of_step hLne
        (roundFamilyOverBracha_owned P G r rfl (by rw [hG r]; exact hlow)))
      (fun i => ?_) (ABANetworkStep.callG A r id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [hx1]; exact RoundLoopStep.callG _ r b hh hph hrr hest
    · rw [hfor i hi]; exact RoundLoopStep.callGIdle _ r id b (Ne.symm hi)
  | retG r id out =>
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inl (Label.retG r id out)) :=
      pure_inj (networkStep_retG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_retG_notOwn (Ne.symm hi) (hall i))
    have hstep := roundTransition_of_own (by exact rfl) (by simp) (hall id)
    obtain ⟨y, hy, hh, hph, hrr, hx1, -, -, -, -, hlow⟩ :=
      roundVariables_match_retG P w (u := u) (j := id) rfl hB.firstGatherCore_of_output hstep
    obtain rfl : x id = y := pure_inj hy
    have hr : r ∈ w.startedRounds :=
      mem_startedRounds_of_roundVariables hR (roundVariables_ne_initial_retG P hstep)
    refine coupling_visible P hl (fun o' _ => relation_roundStep P hR (o' := o') (A' := A) rfl
        hstep hfor (by rw [hx1]; rfl) (fun _ => rfl) hA (Finset.insert_eq_of_mem hr).symm rfl
        (fun _ _ => rfl) (fun _ => rfl))
      (roundFamilyOverBracha_weakStep P rfl (mem_keys_of_mem_startedRounds hR hr)
        (by rw [hG r]; exact hlow))
      (fun i => ?_) (ABANetworkStep.retGIdle A r id out) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [hx1]; exact RoundLoopStep.retG _ r out hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.retGIdle _ r id out (Ne.symm hi)
  | boundG r b =>
    obtain ⟨hb, hw⟩ := networkStep_announceBound hn
    obtain rfl : w' = w := by
      rw [pure_inj hw]; exact writeGhost_ghostId _ (fun _ _ => rfl) w
    have hx : x = u := funext fun i => pure_inj (programStep_boundG (hall i))
    subst hx
    have hkey := mem_keys_of_mem_startedRounds hR (mem_startedRounds_of_bound hR hb)
    obtain ⟨D, hD, hret, rfl⟩ := hB.announceBound_networkProjection hb
    refine coupling_visible P hl (fun o' _ => protocolRelation_noRound hR (fun _ => rfl) hA
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_owned_id P G r hkey rfl
        (by rw [hG r]; exact roundOverBracha_announceBound _ D hD hret)))
      (fun i => ?_) (ABANetworkStep.boundGIdle A r _) hWl
    rw [hCeq i]; exact RoundLoopStep.boundGIdle _ r _

/-! ### The matching on a synchronisation of the implementation

A send, a delivery and a round event of a process at round `r` are internal to round `r`, and the
composed system matches each by a silent run of that round. The first gather's return is matched
by two hidden events of the round. A delivery at a replaced program is the program's self-loop
(D23), and a corrupted process's graded-agreement call leaves the protocol state where it stands.
Both are matched by the empty run. The DECIDED transitions and a corrupted process's coin call are
matched by the same event of the composed system. -/

/-- The matching on the labels the components synchronise on: every synchronisation of the
implementation is matched by a silent run of the composed group. -/
theorem coupling_event (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    (e : Implementation.NetworkEvent P.n (Message P.n) (RoundEvent P.n)) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, -, -, -, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := systemExtended_event_cases h
  have hstand : (∀ i, ¬ roundOwn i
        (Sum.inr e : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))) →
      (∀ i, (x i).2.roundVariablesMap = (u i).2.roundVariablesMap) ∧
        ∀ i, (x i).1.corrupted = (u i).1.corrupted := fun hown =>
    ⟨fun i => by rw [(programStep_notRound (hown i) (by simp) (by simp) (hall i)).2],
      fun i => (programStep_notRound (hown i) (by simp) (by simp) (hall i)).1⟩
  cases e with
  | gbcaRoundEvent r j ev =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaRoundEvent r j ev) ν).mp hWs
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (.gbcaRoundEvent r j ev)) :=
      pure_inj (networkStep_gbcaRoundEvent hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pure_inj (programStep_gbcaRoundEvent_notOwn (Ne.symm hi) (hall i))
    have hstep := roundTransition_of_own (by exact rfl) (by simp) (hall j)
    obtain ⟨y, hy, hcore, -, -, hrun⟩ :=
      roundVariables_match_gbcaRoundEvent P w (u := u) (j := j) rfl hstep
    obtain rfl : x j = y := pure_inj hy
    exact coupling_roundRun P hR rfl hstep hfor hcore
      (mem_startedRounds_of_roundVariables hR (roundVariables_ne_initial_gbcaRoundEvent P hstep))
      rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl) hrun
  | gbcaSend r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaSend r j m) ν).mp hWs
    obtain rfl : w' = (w.recordGBCASend r j m).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j m)) := pure_inj (networkStep_gbcaSend hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pure_inj (programStep_gbcaSend_notOwn (Ne.symm hi) (hall i))
    have hstep := roundTransition_of_own (by exact rfl) (by simp) (hall j)
    obtain ⟨y, hy, hcore, -, -, -, -, hrun⟩ :=
      roundVariables_match_gbcaSend P w (u := u) (j := j) rfl hstep
    obtain rfl : x j = y := pure_inj hy
    exact coupling_roundRun P hR rfl hstep hfor hcore
      (mem_startedRounds_of_roundVariables hR (roundVariables_ne_initial_gbcaSend P hstep))
      rfl rfl rfl (fun r' hr' => recordGBCASend_sent_ne w r j m hr') (fun _ => rfl) hrun
  | gbcaDeliver r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaDeliver r i k m) ν).mp hWs
    obtain ⟨hsent, hw⟩ := networkStep_gbcaDeliver hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r i k m)) := pure_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pure_inj (programStep_gbcaDeliver_notOwn (Ne.symm hi) (hall i'))
    by_cases hc : (u i).1.corrupted = true
    · have hx : x = u := funext fun i' => by
        by_cases hi : i' = i
        · subst hi; exact pure_inj (programStep_noStep hc (hall i'))
        · exact hfor i' hi
      subst hx
      rw [writeGhost_ghostId _ (fun _ _ => rfl) w, prodPMF_pure_pure, prodPMF_pure_pure]
      exact coupling_unchanged P hR
    · have hstep := roundTransition_of_correct (by exact rfl) (by simpa using hc) (hall i)
      obtain ⟨y, hy, hcore, -, -, -, -, hrun⟩ :=
        roundVariables_match_gbcaDeliver P w (u := u) (j := i) rfl hsent hstep
      obtain rfl : x i = y := pure_inj hy
      exact coupling_roundRun P hR rfl hstep hfor hcore (mem_startedRounds_of_sent hR hsent)
        rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl) hrun
  | decidedRelay j b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_decidedRelay j b) ν).mp hWs
    obtain rfl : w' = w.recordDecided j b := pure_inj (networkStep_decidedRelay hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pure_inj (programStep_decidedRelay_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn])
    refine coupling_hiddenSynchronisation P (.decidedRelay j b) (fun o' _ =>
        protocolRelation_noRound hR (fun _ => rfl) (by rw [hA]; rfl) hmap hrep (fun _ => rfl)
          (fun _ => rfl) rfl rfl)
      (roundFamilyOverBracha_idle P G (by simp) rfl not_false) (fun i => ?_)
      (ABANetworkStep.decidedRelay A j b)
      ((System.mapIdle_step_none (coinLabelMap_decidedRelay j b) _).mpr rfl)
    rw [hCeq i]
    by_cases hi : i = j
    · subst hi
      rcases programStep_decidedRelay_self (hall i) with ⟨hh, -, hcnt, hnot, hx⟩ | ⟨hh, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.decidedRelay _ b hh hcnt hnot
      · rw [pure_inj hx]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.decidedRelayIdle _ j b (Ne.symm hi)
  | decidedDeliver i k b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_decidedDeliver i k b) ν).mp hWs
    obtain ⟨hd, hw⟩ := networkStep_decidedDeliver hn
    obtain rfl : w' = w := pure_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pure_inj (programStep_decidedDeliver_notOwn (Ne.symm hi) (hall i'))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn])
    refine coupling_hiddenSynchronisation P (.decidedDeliver i k b) (fun o' _ =>
        protocolRelation_noRound hR (fun _ => rfl) hA hmap hrep (fun _ => rfl) (fun _ => rfl)
          rfl rfl)
      (roundFamilyOverBracha_idle P G (by simp) rfl not_false) (fun i' => ?_)
      (ABANetworkStep.decidedDeliver A i k b (by rw [hA]; exact hd))
      ((System.mapIdle_step_none (coinLabelMap_decidedDeliver i k b) _).mpr rfl)
    rw [hCeq i']
    by_cases hi : i' = i
    · subst hi
      rcases programStep_decidedDeliver_self (hall i') with ⟨hh, hnotin, hx⟩ |
        ⟨hh, hin, hx⟩ | ⟨hh, hx⟩
      · rw [pure_inj hx]; exact RoundLoopStep.decidedDeliverReceive _ k b hh hnotin
      · rw [pure_inj hx]; exact RoundLoopStep.decidedDeliverLoop _ k b hh hin
      · rw [pure_inj hx]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i' hi]; exact RoundLoopStep.decidedDeliverIdle _ i k b (Ne.symm hi)
  | decidedSend id b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_decidedSend id b) ν).mp hWs
    obtain rfl : w' = w.recordDecided id b := pure_inj (networkStep_decidedSend hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pure_inj (programStep_decidedSend_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn])
    refine coupling_hiddenSynchronisation P (.decidedSend id b) (fun o' _ =>
        protocolRelation_noRound hR (fun _ => rfl) (by rw [hA]; rfl) hmap hrep (fun _ => rfl)
          (fun _ => rfl) rfl rfl)
      (roundFamilyOverBracha_idle P G (by simp) rfl not_false) (fun i => ?_)
      (ABANetworkStep.decidedSend A id b)
      ((System.mapIdle_step_none (coinLabelMap_decidedSend id b) _).mpr rfl)
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      obtain ⟨hh, hph, hgr, hx⟩ := programStep_decidedSend_self (hall i)
      rw [pure_inj hx]; exact RoundLoopStep.decidedSend _ b hh hph hgr
    · rw [hfor i hi]; exact RoundLoopStep.decidedSendIdle _ id b (Ne.symm hi)
  | byzantineCallG r k b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_byzantineCallG r k b) ν).mp hWs
    obtain ⟨-, -, hw⟩ := networkStep_byzantineCallG hn
    obtain rfl : w' = w := by
      rw [pure_inj hw]; exact writeGhost_ghostId _ (fun _ _ => rfl) w
    have hx : x = u := funext fun i => pure_inj (programStep_byzantineCallG (hall i))
    subst hx
    rw [prodPMF_pure_pure, prodPMF_pure_pure]
    exact coupling_unchanged P hR
  | byzantineCallW r k =>
    obtain ⟨hF, hr, hw⟩ := networkStep_byzantineCallW hn
    obtain rfl : w' = w := by
      rw [pure_inj hw]; exact writeGhost_ghostId _ (fun _ _ => rfl) w
    have hx : x = u := funext fun i => pure_inj (programStep_byzantineCallW (hall i))
    subst hx
    exact coupling_hiddenSynchronisation P (.byzantineCallW r k) (fun o' _ =>
        protocolRelation_noRound hR (fun _ => rfl) hA (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ => rfl) rfl rfl)
      (roundFamilyOverBracha_idle P G (by simp) rfl not_false)
      (fun i => by rw [hCeq i]; exact RoundLoopStep.byzantineCallWIdle _ r k)
      (ABANetworkStep.byzantineCallW A r k (by rw [hA]; exact hF) (by rw [hA]; exact hr))
      ((System.mapIdle_step_some (coinLabelMap_byzantineCallW r k) ν).mpr
        ((System.mapIdle_step_some (coinLabelMap_byzantineCallW r k) ν).mp hWs))


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
  obtain ⟨-, ho, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  rcases (systemHidden_step_iff _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := coupling_event P hR e hstep
    exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
  · by_cases hl : l = Label.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := coupling_tau P hR hstep
      exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
    · obtain ⟨Ω, hrel, hs⟩ := coupling_label P hR hl hstep
      exact ⟨Ω, hrel, Or.inr ⟨hl, hs⟩⟩

/-- **The matching at the system level**: a hidden sub-protocol label is silent in both systems, and
every other label is matched by a weak transition on the same label. -/
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
