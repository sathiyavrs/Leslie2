/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ABDY.Composition
import Leslie2Protocols.ABA.ABDY.System
import Leslie2Protocols.ABA.Composition.ABAState
import Leslie2Protocols.Framework.DiracRelationCoupling
import Leslie2.Results

/-!
# The protocol under its composed system

The protocol of `ABA/ABDY/System.lean` and the composed system of
`ABA/ABDY/Composition.lean` present one protocol at two cuts. A process's variables
in the protocol carry the round-loop variables beside its variables in every round the process
has touched (D22). A composed state carries the round instances its family has touched in a finite
map, and reads every other round as the initial instance under the recorded corruptions. A
process's variables in round `r` are the entry of that process in the instance of round `r`, so the
two cuts hold the same round data indexed two ways: by process in one, by round in the other.

Everything here is read in the namespace `ABDY`, where each name is that of its
counterpart in the gather-based chain's `AFW`, and the qualifier is dropped below.

## The relation

`ProtocolRelation` has eight conjuncts. The first six relate the coordinates.

* The round loops are the first components of the process variables.
* The common coin is the same component in both systems.
* The ABA network is the protocol network's DECIDED sets beside its corrupted set and its started
  rounds.
* The rounds of the family's map are the started rounds (D37).
* The network state of round `r` is the protocol network's round-`r` message sets beside the same
  corrupted set and the network's ghost of round `r`. Corruption is one broadcast in both systems,
  so every copy of the corrupted set is the network's, and the round's bound bit is the ghost of
  that round.
* The entry of process `j` in the instance of round `r` is what `j` holds in its variables for
  round `r`. A round `j` has not touched reads as the initial variables in the protocol, and the
  equation asks the composed entry to be initial there too.

The relation reads the family through its accessor and its keys. It leaves the family's list of
broadcasts free: the composed family records the `fail` labels it has applied, which the protocol
state does not hold, and two family states with equal accessors and equal keys differ at most in
that list (`InstanceFamilyState.ext_of_keys`).

The last two conjuncts are invariants of the protocol state. At a round outside the started rounds
no process has sent, the ghost is `none` and no process holds variables. Every process of the
corrupted set has a replaced program. Together they place every round a transition of the protocol
touches among the started rounds, which is where the family takes its silent transitions: a send or
a return at round `r` reads variables of round `r` that hold an input, a delivery reads a message
sent at round `r`, an announcement reads the ghost of round `r`, and a call by an unreplaced program
is a call by a process outside `F`, which the network records.

`PLTS.coupling_pure` and `PLTS.coupling_map` (`Framework/DiracRelationCoupling.lean`) are the two
couplings the relation supplies: a Dirac protocol outcome is matched by a single composed state,
and an outcome whose only free coordinate is the coin's is matched outcome by outcome.

## The matching

A transition of the protocol is matched by a transition of the composed system on the same label,
by a silent transition of one round instance, or by a stutter of the composed system. The composed
system stutters at three transitions of the protocol, each silent in the protocol and each leaving
every coordinate the relation reads where it stands: a corrupted process's graded-agreement call,
which every program takes on an idle transition; a round delivery at a replaced or terminated
program, which the program takes on `corruptedIdle` or `deliverLoop`; and the termination of a
process, which writes a flag the relation does not read.

## What this file supplies

`protocolSimulation`, a probabilistic forward simulation of `composed P` by `protocol P` along
the Dirac lift of `ProtocolRelation P`, and the trace-distribution inclusion `protocol_composed`
it yields. The inclusion is one-directional because the composed system takes transitions the
protocol declines: a round instance records a corrupted process's call (D11) and files a delivery
at a replaced or terminated process, and its round transitions carry no termination guard (D22).
-/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

namespace ABDY

/-- **The relation of the protocol presentation to the composed one.** Writing
`u = (processes, w, o)` and `t = (G, C, A, o')`, the eight conjuncts are: the round loops agree;
the common coin is shared; the ABA network is the network's DECIDED sets beside its corrupted set
and its started rounds; the rounds of the family's map are the started rounds; each round's
network state is that round's messages out of the network's sent sets beside the same corrupted set
and the network's ghost of that round; the entry of process `j` in the instance of round `r` is
what `j` holds in its variables for round `r` (D22); at a round outside the started rounds no
process has sent, the ghost is `none` and no process holds variables; and every process of the
corrupted set has a replaced program (D23, D37). -/
def ProtocolRelation (P : Parameters) (u : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (u.1 j).1 = t.2.1 j) ∧
  u.2.2 = t.2.2.2 ∧
  t.2.2.1 = ⟨u.2.1.decidedSent, u.2.1.F, u.2.1.startedRounds⟩ ∧
  t.1.instanceMap.keys = u.2.1.startedRounds ∧
  (∀ r, (t.1 r).2 = ⟨u.2.1.sent r, u.2.1.F, u.2.1.ghost r⟩) ∧
  (∀ j r, (t.1 r).1 j = (u.1 j).2.roundVariables r) ∧
  (∀ r ∉ u.2.1.startedRounds, (∀ j, u.2.1.sent r j = ∅) ∧ u.2.1.ghost r = none ∧
    ∀ j, r ∉ (u.1 j).2.roundVariablesMap) ∧
  (∀ j ∈ u.2.1.F, (u.1 j).1.corrupted = true)

/-- The relation, read at an explicit pair of states. -/
theorem protocolRelation_mk (P : Parameters) (processes : ∀ _ : Fin P.n, ProcessVariables P.n)
    (w : NetworkState P.n) (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
    (G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P))
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) :
    ProtocolRelation P (processes, w, o) (G, C, A, o') ↔
      (∀ j, (processes j).1 = C j) ∧
      o = o' ∧
      A = ⟨w.decidedSent, w.F, w.startedRounds⟩ ∧
      G.instanceMap.keys = w.startedRounds ∧
      (∀ r, (G r).2 = ⟨w.sent r, w.F, w.ghost r⟩) ∧
      (∀ j r, (G r).1 j = (processes j).2.roundVariables r) ∧
      (∀ r ∉ w.startedRounds, (∀ j, w.sent r j = ∅) ∧ w.ghost r = none ∧
        ∀ j, r ∉ (processes j).2.roundVariablesMap) ∧
      (∀ j ∈ w.F, (processes j).1.corrupted = true) :=
  Iff.rfl

/-! ### The started rounds

The seventh conjunct, read backwards: a round at which some process holds an input, some process
has sent, or the ghost holds a bit is a started round. -/

section StartedRounds

variable {P : Parameters} {processes : ∀ _ : Fin P.n, ProcessVariables P.n}
  {w : NetworkState P.n}

/-- A round at which a process's variables hold an input is a started round. -/
private theorem startedRounds_of_input
    (hUntouched : ∀ r ∉ w.startedRounds, (∀ j, w.sent r j = ∅) ∧ w.ghost r = none ∧
      ∀ j, r ∉ (processes j).2.roundVariablesMap)
    {j : Fin P.n} {r : ℕ} (h : ((processes j).2.roundVariables r).processVariables.input ≠ none) :
    r ∈ w.startedRounds := by
  by_contra hr
  apply h
  simp only [Implementation.RoundVariablesMap.roundVariables,
    Finmap.lookup_eq_none.mpr ((hUntouched r hr).2.2 j), Option.getD_none]
  rfl

/-- A round at which some process has sent is a started round. -/
private theorem startedRounds_of_sent
    (hUntouched : ∀ r ∉ w.startedRounds, (∀ j, w.sent r j = ∅) ∧ w.ghost r = none ∧
      ∀ j, r ∉ (processes j).2.roundVariablesMap)
    {r : ℕ} {k : Fin P.n} {m : GBCA.ByABDY.Message} (h : m ∈ w.sent r k) :
    r ∈ w.startedRounds := by
  by_contra hr
  rw [(hUntouched r hr).1 k] at h
  exact Finset.notMem_empty m h

/-- A round whose ghost holds a bit is a started round. -/
private theorem startedRounds_of_ghost
    (hUntouched : ∀ r ∉ w.startedRounds, (∀ j, w.sent r j = ∅) ∧ w.ghost r = none ∧
      ∀ j, r ∉ (processes j).2.roundVariablesMap)
    {r : ℕ} {b : Bool} (h : w.ghost r = some b) : r ∈ w.startedRounds := by
  by_contra hr
  rw [(hUntouched r hr).2.1] at h
  cases h

end StartedRounds

/-! ### Corruption -/

/-- The network state of round `r` after a corruption, read from the protocol network. -/
private theorem corrupt_gbcaNetwork {P : Parameters} (w : NetworkState P.n) (k : Fin P.n) (r : ℕ) :
    (⟨w.sent r, w.F, w.ghost r⟩ : GBCA.ByABDY.NetworkState P.n).corrupt P k =
      ⟨(Implementation.NetworkState.corrupt P k w).sent r,
        (Implementation.NetworkState.corrupt P k w).F,
        (Implementation.NetworkState.corrupt P k w).ghost r⟩ := by
  unfold GBCA.ByABDY.NetworkState.corrupt Implementation.NetworkState.corrupt
  dsimp only
  split_ifs <;> rfl

/-! ### The relation across a transition

Two shapes of transition preserve the relation here: one that moves no round instance, and one
that moves the instance of a single round. A corruption is read in its own case below. In each,
the composed round loops and the ABA network after the transition are given as `C'` and `A'`. -/

/-- The relation across a transition that moves no round instance: the round variables, the
replacement flags, the message sets, the ghosts, the corrupted set and the started rounds stand. -/
private theorem relation_noRound (P : Parameters)
    {processes x : ∀ _ : Fin P.n, ProcessVariables P.n} {w w' : NetworkState P.n}
    {o o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    (hR : ProtocolRelation P (processes, w, o) (G, C, A, o))
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hmap : ∀ j, (x j).2.roundVariablesMap = (processes j).2.roundVariablesMap)
    (hReplacement : ∀ j, (x j).1.corrupted = (processes j).1.corrupted)
    (hsent : w'.sent = w.sent) (hghost : w'.ghost = w.ghost) (hF : w'.F = w.F)
    (hStarted : w'.startedRounds = w.startedRounds) :
    ProtocolRelation P (x, w', o') (G, C', A', o') := by
  obtain ⟨-, -, -, hKeys, hG, hst, hUntouched, hCorrupted⟩ :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hRoundVariables : ∀ j r, (x j).2.roundVariables r = (processes j).2.roundVariables r := by
    intro j r
    simp only [Implementation.RoundVariablesMap.roundVariables, hmap j]
  refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC', rfl, hA', by rw [hKeys, hStarted],
    fun r => by rw [hG r, hsent, hghost, hF], fun j r => by rw [hst j r, hRoundVariables],
    fun r hr => ?_, fun j hj => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hUntouched r (by rwa [hStarted] at hr)
    exact ⟨fun j => by rw [hsent]; exact h1 j, by rw [hghost]; exact h2,
      fun j => by rw [hmap j]; exact h3 j⟩
  · rw [hReplacement j]; exact hCorrupted j (by rwa [hF] at hj)

/-- The relation across a transition that moves the instance of round `r` alone, to `X`: the
started rounds gain `r`, the corrupted set stands, the message sets and the ghosts of every other
round stand, and every process's variables of every other round stand. -/
private theorem relation_oneRound (P : Parameters)
    {processes x : ∀ _ : Fin P.n, ProcessVariables P.n} {w w' : NetworkState P.n}
    {o o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    (hR : ProtocolRelation P (processes, w, o) (G, C, A, o)) (r : ℕ)
    (X : GBCA.ByABDY.RoundState P.n)
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hStarted : w'.startedRounds = insert r w.startedRounds) (hF : w'.F = w.F)
    (hsent : ∀ r', r' ≠ r → w'.sent r' = w.sent r')
    (hghost : ∀ r', r' ≠ r → w'.ghost r' = w.ghost r')
    (hX2 : X.2 = ⟨w'.sent r, w'.F, w'.ghost r⟩)
    (hX1 : ∀ j, X.1 j = (x j).2.roundVariables r)
    (hmap : ∀ j r', r' ≠ r →
      (x j).2.roundVariablesMap.lookup r' = (processes j).2.roundVariablesMap.lookup r')
    (hReplacement : ∀ j, (x j).1.corrupted = (processes j).1.corrupted) :
    ProtocolRelation P (x, w', o') (G.setInstanceState r X, C', A', o') := by
  obtain ⟨-, -, -, hKeys, hG, hst, hUntouched, hCorrupted⟩ :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC', rfl, hA', ?_, fun r' => ?_,
    fun j r' => ?_, fun r' hr' => ?_, fun j hj => ?_⟩
  · rw [InstanceFamilyState.keys_setInstanceState, hKeys, hStarted]
  · by_cases h : r' = r
    · subst h
      rw [InstanceFamilyState.setInstanceState_apply_same]
      exact hX2
    · rw [InstanceFamilyState.setInstanceState_apply_ne _ _ h, hG r', hsent r' h, hghost r' h,
        hF]
  · by_cases h : r' = r
    · subst h
      rw [InstanceFamilyState.setInstanceState_apply_same]
      exact hX1 j
    · rw [InstanceFamilyState.setInstanceState_apply_ne _ _ h, hst j r']
      simp only [Implementation.RoundVariablesMap.roundVariables, hmap j r' h]
  · have hne : r' ≠ r := fun h => hr' (by rw [h, hStarted]; exact Finset.mem_insert_self r _)
    have hold : r' ∉ w.startedRounds := fun h =>
      hr' (by rw [hStarted]; exact Finset.mem_insert_of_mem h)
    obtain ⟨h1, h2, h3⟩ := hUntouched r' hold
    refine ⟨fun j => by rw [hsent r' hne]; exact h1 j, by rw [hghost r' hne]; exact h2,
      fun j => ?_⟩
    rw [← Finmap.lookup_eq_none, hmap j r' hne, Finmap.lookup_eq_none]
    exact h3 j
  · rw [hReplacement j]; exact hCorrupted j (by rwa [hF] at hj)

/-- The one-round relation at a transition where process `id` writes its round-loop variables to
`c'` and its variables of round `r` to `nd`, every other process stands, and the network state of
round `r` becomes `Y`. -/
private theorem relation_oneProcess (P : Parameters)
    {processes x : ∀ _ : Fin P.n, ProcessVariables P.n} {w w' : NetworkState P.n}
    {o o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    (hR : ProtocolRelation P (processes, w, o) (G, C, A, o)) (r : ℕ) (id : Fin P.n)
    (c' : RoundLoopVariables P.n) (nd : GBCA.ByABDY.RoundVariables P.n)
    (Y : GBCA.ByABDY.NetworkState P.n)
    (hx : x id = (c', (processes id).2.setRoundVariables r nd))
    (hfor : ∀ i, i ≠ id → x i = processes i)
    (hReplacementOwn : c'.corrupted = (processes id).1.corrupted)
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hStarted : w'.startedRounds = insert r w.startedRounds) (hF : w'.F = w.F)
    (hsent : ∀ r', r' ≠ r → w'.sent r' = w.sent r')
    (hghost : ∀ r', r' ≠ r → w'.ghost r' = w.ghost r')
    (hY : Y = ⟨w'.sent r, w'.F, w'.ghost r⟩) :
    ProtocolRelation P (x, w', o')
      (G.setInstanceState r (Function.update ((G r).1) id nd, Y), C', A', o') := by
  have hst := ((protocolRelation_mk P _ _ _ _ _ _ _).mp hR).2.2.2.2.2.1
  refine relation_oneRound P hR r _ hC' hA' hStarted hF hsent hghost hY (fun i => ?_)
    (fun i r' hr' => ?_) (fun i => ?_)
  · dsimp only
    by_cases hi : i = id
    · subst hi
      rw [Function.update_self, hx]
      exact (Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self _ _ _).symm
    · rw [Function.update_of_ne hi, hst i r, hfor i hi]
  · by_cases hi : i = id
    · subst hi
      rw [hx]
      exact Finmap.lookup_insert_of_ne _ hr'
    · rw [hfor i hi]
  · by_cases hi : i = id
    · subst hi; rw [hx]; exact hReplacementOwn
    · rw [hfor i hi]

/-! ### Assembling a composed transition

Three shapes of matching run. A label both systems take is matched by the transitions of the four
composed components on that label. A round synchronisation has no transition at three of them: it
is internal to a round instance, and the family carries it as its own silent transition at a round
of its map. A protocol transition that leaves the protocol state where it stands is matched
by a stutter of the composed system. -/

/-- A visible label of the extended alphabet matched by the four composed
transitions, the coin's successor carried across. -/
private theorem coupling_visible (P : Parameters) {x : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w' : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    {G G' : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n} {L : ExtendedLabel P.n GBCA.ByABDY.Message} (hL : L ≠ Silent.τ)
    (hrel : ∀ o' ∈ ω.support, ProtocolRelation P (x, w', o') (G', C', A', o'))
    (hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G'))
    (hCs : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hAs : ABANetworkStep P A L (PMF.pure A'))
    (hWs : (coinOverRoundAlphabet P GBCA.ByABDY.Message).step o L ω) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedExtended P).step (G, C, A, o) L (Ω.bind id) := by
  obtain ⟨Ω, hr, hbind⟩ := coupling_map ω (fun o' => ((x, w', o') : ProtocolState P))
    (fun o' => ((G', C', A', o') : ComposedState P)) hrel
  rw [← prodPMF_two_pure_factors] at hr
  rw [← prodPMF_three_pure_factors] at hbind
  exact ⟨Ω, hr, hbind ▸ composedExtended_visible_step P hL hGs hCs hAs hWs⟩

/-- A synchronisation the composed system matches inside one round of the family's map: the
instance of round `r` takes it as its own silent transition. -/
private theorem coupling_round
    (P : Parameters) {x : ∀ _ : Fin P.n, ProcessVariables P.n} {w' : NetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ν : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n} {r : ℕ}
    {X : GBCA.ByABDY.RoundState P.n} (hν : ν = PMF.pure o) (hr : r ∈ G.instanceMap.keys)
    (hrel : ProtocolRelation P (x, w', o) (G.setInstanceState r X, C, A, o))
    (hsub : (GBCA.ByABDY.composition P r).step (G r) (Sum.inl Label.tau) (PMF.pure X)) :
    ∃ Ω : PMF (PMF (ComposedState P)), PMFRel (diracRel (ProtocolRelation P))
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      (composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) := by
  subst hν
  obtain ⟨Ω, hΩ, hbind⟩ := coupling_pure hrel
  refine ⟨Ω, ?_, ?_⟩
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]; exact hΩ
  · rw [hbind]
    exact composedHidden_of_tau P
      (composedExtended_tau_gbca P (gbcaInstanceFamily_tau P G r hr hsub))

/-- A protocol transition that leaves the protocol state where it stands, matched by a stutter of
the composed system. -/
private theorem coupling_stutter (P : Parameters) {x : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {t : ComposedState P} (hR : ProtocolRelation P (x, w, o) t) :
    ∃ Ω : PMF (PMF (ComposedState P)), PMFRel (diracRel (ProtocolRelation P))
      (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) (PMF.pure o))) Ω ∧ Ω.bind id = PMF.pure t := by
  obtain ⟨Ω, hΩ, hbind⟩ := coupling_pure hR
  exact ⟨Ω, by rw [prodPMF_pure_pure, prodPMF_pure_pure]; exact hΩ, hbind⟩

/-! ### The matching, by label class

A transition of the protocol group is a hidden synchronisation, a visible shared label, or the
silent label. Each is matched by a transition of the composed group on the same label, built from
the transitions of the four composed components, or by a stutter of the composed group. A
corrupted process's replaced program is matched loop for loop: where the protocol program
self-loops, the composed round loop takes `corruptedIdle`. -/

/-- The matching on the labels the components synchronise on. A corrupted process's
graded-agreement call and a round delivery at a replaced or terminated program leave the protocol
state where it stands, and the composed group stutters; every other synchronisation is matched by
a silent transition of the composed group. -/
theorem coupling_event (P : Parameters) {processes : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    (hR : ProtocolRelation P (processes, w, o) (G, C, A, o))
    (e : NetworkEvent P.n GBCA.ByABDY.Message) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (processes, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      ((composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) ∨
        Ω.bind id = PMF.pure (G, C, A, o)) := by
  obtain ⟨hC, -, hA, hKeys, hG, hst, hUntouched, -⟩ :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (processes i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := protocolExtended_event_cases P h
  have hLne : (Sum.inr e : ExtendedLabel P.n GBCA.ByABDY.Message) ≠ Silent.τ := by
    simp
  have hstand : (∀ i, ¬ roundOwn i (Sum.inr e : ExtendedLabel P.n GBCA.ByABDY.Message)) →
      (∀ i, (x i).2 = (processes i).2) ∧ ∀ i, (x i).1.corrupted = (processes i).1.corrupted :=
    fun hown => ⟨fun i => (programStep_notRound (hown i) (by simp) (by simp) (hall i)).2,
      fun i => (programStep_notRound (hown i) (by simp) (by simp) (hall i)).1⟩
  have hvis : ∀ {G' : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n)
        (GBCA.ByABDY.corruptionAct P)} {A' : ABANetworkState P.n},
      (∀ o' ∈ ν.support, ProtocolRelation P (x, w', o') (G', fun i => (x i).1, A', o')) →
      (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inr e) (PMF.pure G') →
      (∀ i, RoundLoopStep P i (C i) (Sum.inr e) (PMF.pure ((x i).1))) →
      ABANetworkStep P A (Sum.inr e) (PMF.pure A') →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRelation P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        ((composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) ∨
          Ω.bind id = PMF.pure (G, C, A, o)) := by
    intro G' A' hrel hGs hCs hAs
    obtain ⟨Ω, hΩ, hs⟩ := coupling_visible P hLne hrel hGs hCs hAs hWs
    exact ⟨Ω, hΩ, Or.inl (composedHidden_of_event P e hs)⟩
  cases e with
  | gbcaRoundEvent r j ev => exact ev.elim
  | gbcaSend r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaSend r j m) ν).mp hWs
    obtain rfl : w' = w.recordGBCASend r j m := by
      simpa using pure_inj (networkStep_gbcaSend hn)
    have hcol : (G r).1 j = (processes j).2.roundVariables r := hst j r
    have hstage : ∃ nd : GBCA.ByABDY.RoundVariables P.n,
        ((processes j).2.roundVariables r).processVariables.input ≠ none ∧
        GBCA.ByABDY.GBCAProgramStep P r j ((G r).1 j) (Sum.inr (GBCA.ByABDY.GBCAEvent.send j m))
          (PMF.pure nd) ∧
        x j = ((processes j).1, (processes j).2.setRoundVariables r nd) := by
      cases m with
      | input b =>
        obtain ⟨-, -, hcase, hsend, hxid⟩ := programStep_gbcaSend_input_self (hall j)
        rcases hcase with hin | ⟨hin, hcnt⟩
        · exact ⟨_, by simp [hin], GBCA.ByABDY.GBCAProgramStep.sendInput _ b
            (by rw [hcol]; exact hin) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        · exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendRelay _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
      | echo b =>
        obtain ⟨-, -, hin, hcnt, hsend, hxid⟩ := programStep_gbcaSend_echo_self (hall j)
        exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendEcho _ b (by rw [hcol]; exact hin)
          (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
          by rw [hcol]; exact pure_inj hxid⟩
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨-, -, hin, hcnt, hsend, hxid⟩ := programStep_gbcaSend_voteBit_self (hall j)
          exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendVoteBit _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        | none =>
          obtain ⟨-, -, hin, hnot, hcnt, hval, hsend, hxid⟩ :=
            programStep_gbcaSend_voteBot_self (hall j)
          exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendVoteBot _ (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hnot) (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hval)
            (by rw [hcol]; exact hsend), by rw [hcol]; exact pure_inj hxid⟩
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨-, -, hin, hlv, hcnt, hsend, hxid⟩ := programStep_gbcaSend_bindBit_self (hall j)
          exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendBindBit _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        | none =>
          obtain ⟨-, -, hin, hlv, hnot, hcnt, hval, hsend, hxid⟩ :=
            programStep_gbcaSend_bindBot_self (hall j)
          exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendBindBot _ (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnot) (by rw [hcol]; exact hcnt)
            (by rw [hcol]; exact hval) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
      | «echo5» v =>
        cases v with
        | some b =>
          obtain ⟨-, -, hin, hlv, hcnt, hsend, hxid⟩ :=
            programStep_gbcaSend_echo5Bit_self (hall j)
          exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendEcho5Bit _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        | none =>
          obtain ⟨-, -, hin, hlv, hnot, hcnt, hval, hsend, hxid⟩ :=
            programStep_gbcaSend_echo5Bot_self (hall j)
          exact ⟨_, hin, GBCA.ByABDY.GBCAProgramStep.sendEcho5Bot _ (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnot) (by rw [hcol]; exact hcnt)
            (by rw [hcol]; exact hval) (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
    obtain ⟨nd, hin, htransition, hx⟩ := hstage
    have hfor : ∀ i, i ≠ j → x i = processes i := fun i hi =>
      pure_inj (programStep_gbcaSend_notOwn (Ne.symm hi) (hall i))
    have hr : r ∈ w.startedRounds := startedRounds_of_input hUntouched hin
    have hrel := relation_oneProcess P hR (w' := w.recordGBCASend r j m) (o' := o) (C' := C)
      (A' := A) r j (processes j).1 nd
      (((G r).2).recordGBCASend j m) hx hfor rfl
      (fun i => by
        by_cases hi : i = j
        · subst hi; rw [hx]; exact hC i
        · rw [hfor i hi]; exact hC i)
      (by rw [hA]; rfl) (by rw [recordGBCASend_startedRounds, Finset.insert_eq_of_mem hr]) rfl
      (fun r' h => recordGBCASend_sent_ne w r j m h) (fun _ _ => rfl)
      (by rw [hG r]; simp [GBCA.ByABDY.NetworkState.recordGBCASend])
    obtain ⟨Ω, hΩ, hs⟩ := coupling_round P rfl (by rw [hKeys]; exact hr) hrel
      (GBCA.ByABDY.composition_event_step P r (GBCA.ByABDY.GBCAEvent.send j m)
        (gbcaProgramStep_family j nd htransition
          (fun i hi => GBCA.ByABDY.GBCAProgramStep.sendIdle _ j m (Ne.symm hi)))
        (GBCA.ByABDY.GBCANetworkStep.send _ j m))
    exact ⟨Ω, hΩ, Or.inl hs⟩
  | gbcaDeliver r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaDeliver r i k m) ν).mp hWs
    obtain ⟨hmem, hw⟩ := networkStep_gbcaDeliver hn
    obtain rfl : w = w' := by
      simpa using (pure_inj hw).symm
    have hfor : ∀ i', i' ≠ i → x i' = processes i' := fun i' hi' =>
      pure_inj (programStep_gbcaDeliver_notOwn (Ne.symm hi') (hall i'))
    rcases programStep_gbcaDeliver_self (hall i) with ⟨-, -, hxid⟩ | ⟨-, hxid⟩
    · have hcol : (G r).1 i = (processes i).2.roundVariables r := hst i r
      have hx : x i = ((processes i).1,
          (processes i).2.setRoundVariables r (((G r).1 i).deliverTo k m)) := by
        rw [hcol]; exact pure_inj hxid
      have hr : r ∈ w.startedRounds := startedRounds_of_sent hUntouched hmem
      have hrel := relation_oneProcess P hR (w' := w) (o' := o) (C' := C) (A' := A) r i
        (processes i).1
        (((G r).1 i).deliverTo k m) (G r).2 hx hfor rfl
        (fun i' => by
          by_cases hi' : i' = i
          · subst hi'; rw [hx]; exact hC i'
          · rw [hfor i' hi']; exact hC i')
        hA (Finset.insert_eq_of_mem hr).symm rfl (fun _ _ => rfl) (fun _ _ => rfl) (hG r)
      obtain ⟨Ω, hΩ, hs⟩ := coupling_round P rfl (by rw [hKeys]; exact hr) hrel
        (GBCA.ByABDY.composition_event_step P r (GBCA.ByABDY.GBCAEvent.deliver i k m)
          (gbcaProgramStep_family i _ (GBCA.ByABDY.GBCAProgramStep.deliverReceive _ k m)
            (fun i' hi' => GBCA.ByABDY.GBCAProgramStep.deliverIdle _ i k m (Ne.symm hi')))
          (GBCA.ByABDY.GBCANetworkStep.deliver _ i k m
            (by change m ∈ ((G r).2).sent k; rw [hG r]; exact hmem)))
      exact ⟨Ω, hΩ, Or.inl hs⟩
    · have hx : x = processes := funext fun i' => by
        by_cases hi' : i' = i
        · subst hi'; exact pure_inj hxid
        · exact hfor i' hi'
      subst hx
      obtain ⟨Ω, hΩ, hb⟩ := coupling_stutter P hR
      exact ⟨Ω, hΩ, Or.inr hb⟩
  | decidedRelay j b =>
    obtain rfl : w' = w.recordDecided j b := pure_inj (networkStep_decidedRelay hn)
    have hfor : ∀ i, i ≠ j → x i = processes i := fun i hi =>
      pure_inj (programStep_decidedRelay_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hRoundVariables, hReplacement⟩ := hstand fun _ => by simp [roundOwn]
    refine hvis (A' := A.recordDecided j b) (fun o' _ => relation_noRound P hR (fun _ => rfl)
      (by rw [hA]; rfl) (fun i => by rw [hRoundVariables i]) hReplacement rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.decidedRelay A j b)
    rw [hCeq i]
    by_cases hi : i = j
    · subst hi
      rcases programStep_decidedRelay_self (hall i) with ⟨hh, -, hcnt, hnot, hxid⟩ | ⟨hh, hxid⟩
      · rw [pure_inj hxid]; exact RoundLoopStep.decidedRelay _ b hh hcnt hnot
      · rw [pure_inj hxid]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.decidedRelayIdle _ j b (Ne.symm hi)
  | decidedDeliver i k b =>
    obtain ⟨hdp, hw⟩ := networkStep_decidedDeliver hn
    obtain rfl : w = w' := (pure_inj hw).symm
    have hfor : ∀ i', i' ≠ i → x i' = processes i' := fun i' hi' =>
      pure_inj (programStep_decidedDeliver_notOwn (Ne.symm hi') (hall i'))
    obtain ⟨hRoundVariables, hReplacement⟩ := hstand fun _ => by simp [roundOwn]
    refine hvis (A' := A) (fun o' _ => relation_noRound P hR (fun _ => rfl) hA
      (fun i' => by rw [hRoundVariables i']) hReplacement rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i' => ?_)
      (ABANetworkStep.decidedDeliver A i k b (by rw [hA]; exact hdp))
    rw [hCeq i']
    by_cases hi' : i' = i
    · subst hi'
      rcases programStep_decidedDeliver_self (hall i') with ⟨hh, hnotin, hxid⟩ |
        ⟨hh, hin, hxid⟩ | ⟨hh, hxid⟩
      · rw [pure_inj hxid]; exact RoundLoopStep.decidedDeliverReceive _ k b hh hnotin
      · rw [pure_inj hxid]; exact RoundLoopStep.decidedDeliverLoop _ k b hh hin
      · rw [pure_inj hxid]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i' hi']; exact RoundLoopStep.decidedDeliverIdle _ i k b (Ne.symm hi')
  | decidedSend id b =>
    obtain rfl : w' = w.recordDecided id b := pure_inj (networkStep_decidedSend hn)
    obtain ⟨hh, hph, hgr, hxid⟩ := programStep_decidedSend_self (hall id)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_decidedSend_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hRoundVariables, hReplacement⟩ := hstand fun _ => by simp [roundOwn]
    refine hvis (A' := A.recordDecided id b) (fun o' _ => relation_noRound P hR (fun _ => rfl)
      (by rw [hA]; rfl) (fun i => by rw [hRoundVariables i]) hReplacement rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.decidedSend A id b)
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [pure_inj hxid]; exact RoundLoopStep.decidedSend _ b hh hph hgr
    · rw [hfor i hi]; exact RoundLoopStep.decidedSendIdle _ id b (Ne.symm hi)
  | byzantineCallG r k b =>
    obtain ⟨-, -, hw⟩ := networkStep_byzantineCallG hn
    obtain rfl : w = w' := by
      simpa using (pure_inj hw).symm
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_byzantineCallG r k b) ν).mp hWs
    have hx : x = processes := funext fun i => pure_inj (programStep_byzantineCallG (hall i))
    subst hx
    obtain ⟨Ω, hΩ, hb⟩ := coupling_stutter P hR
    exact ⟨Ω, hΩ, Or.inr hb⟩
  | byzantineCallW r k =>
    obtain ⟨hF, hr, hw⟩ := networkStep_byzantineCallW hn
    obtain rfl : w = w' := by
      simpa using (pure_inj hw).symm
    have hx : x = processes := funext fun i => pure_inj (programStep_byzantineCallW (hall i))
    subst hx
    refine hvis (A' := A) (fun o' _ => relation_noRound P hR (fun _ => rfl) hA (fun _ => rfl)
      (fun _ => rfl) rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.byzantineCallW A r k (by rw [hA]; exact hF) (by rw [hA]; exact hr))
    rw [hCeq i]; exact RoundLoopStep.byzantineCallWIdle _ r k

/-- The matching on a visible shared label: every one is matched by the four components of the
composed system on the same label. -/
theorem coupling_label (P : Parameters) {processes : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    (hR : ProtocolRelation P (processes, w, o) (G, C, A, o))
    {l : Label P.n} (hl : l ≠ Label.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (processes, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      (composedHidden P).step (G, C, A, o) l (Ω.bind id) := by
  obtain ⟨hC, -, hA, hKeys, hG, hst, hUntouched, hCorrupted⟩ :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (processes i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := protocolExtended_label_cases P hl h
  have hWl : (coinOverRoundAlphabet P GBCA.ByABDY.Message).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (coinLabelMap_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : ExtendedLabel P.n GBCA.ByABDY.Message) ≠ Silent.τ := by
    simpa using hl
  have hLtau : (Sum.inl l : ExtendedLabel P.n GBCA.ByABDY.Message) ≠ Sum.inl Label.tau := by
    simpa using hl
  have hstand : (∀ i, ¬ roundOwn i (Sum.inl l : ExtendedLabel P.n GBCA.ByABDY.Message)) →
      (∀ k, l ≠ Label.fail k) →
      (∀ i, (x i).2.roundVariablesMap = (processes i).2.roundVariablesMap) ∧
        ∀ i, (x i).1.corrupted = (processes i).1.corrupted := fun hown hf =>
    ⟨fun i => by
      rw [(programStep_notRound (hown i) hLtau (fun k hk => hf k (Sum.inl_injective hk))
        (hall i)).2],
      fun i => (programStep_notRound (hown i) hLtau (fun k hk => hf k (Sum.inl_injective hk))
        (hall i)).1⟩
  suffices hsuf : ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedExtended P).step (G, C, A, o) (Sum.inl l) (Ω.bind id) by
    obtain ⟨Ω, hΩ, hs⟩ := hsuf
    exact ⟨Ω, hΩ, (composedHidden_step_iff P _ _ _).mpr (Or.inr hs)⟩
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w = w' := (pure_inj (networkStep_callABA hn)).symm
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_callABA_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hLne (fun o' _ => relation_noRound P hR (fun _ => rfl) hA hmap hrep
      rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.callABAIdle A id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_callABA_own (hall i) with ⟨hh, hin, hxid⟩ | ⟨hloop, hxid⟩
      · rw [pure_inj hxid]; exact RoundLoopStep.input _ b hh hin
      · rw [pure_inj hxid]
        by_cases hc : (processes i).1.corrupted = true
        · exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
        · exact RoundLoopStep.inputLoop _ b (by simpa using hc) (hloop.resolve_left hc)
    · rw [hfor i hi]; exact RoundLoopStep.callABAIdle _ id b (Ne.symm hi)
  | retABA id b =>
    obtain rfl : w = w' := (pure_inj (networkStep_retABA hn)).symm
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retABA_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hLne (fun o' _ => relation_noRound P hR (fun _ => rfl) hA hmap hrep
      rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.retABAIdle A id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_retABA_own (hall i) with ⟨hh, -, hcnt, hsent, hret, hxid⟩ | ⟨hh, hxid⟩
      · rw [pure_inj hxid]; exact RoundLoopStep.ret _ b hh hcnt hsent hret
      · rw [pure_inj hxid]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w = w' := (pure_inj (networkStep_callW hn)).symm
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_callW_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hLne (fun o' _ => relation_noRound P hR (fun _ => rfl) hA hmap hrep
      rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.callWIdle A r id) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      obtain ⟨hh, hph, hrr, hxid⟩ := programStep_callW_own (hall i)
      rw [pure_inj hxid]; exact RoundLoopStep.callW _ r hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w = w' := (pure_inj (networkStep_retW hn)).symm
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retW_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hmap, hrep⟩ := hstand (fun _ => by simp [roundOwn]) (by simp)
    refine coupling_visible P hLne (fun o' _ => relation_noRound P hR (fun _ => rfl) hA hmap hrep
      rfl rfl rfl rfl)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.retWIdle A r id co) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases programStep_retW_own (hall i) with ⟨hh, hph, hrr, hxid⟩ | ⟨hh, hnot, hxid⟩ |
        ⟨hh, hxid⟩
      · rw [pure_inj hxid]; exact RoundLoopStep.retW _ r co hh hph hrr
      · rw [pure_inj hxid]; exact RoundLoopStep.retWLoop _ r co hh hnot
      · rw [pure_inj hxid]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain ⟨hnew, hbud, hw⟩ := networkStep_fail hn
    obtain rfl : w' = Implementation.NetworkState.corrupt P k w := pure_inj hw
    have hfor : ∀ i, i ≠ k → x i = processes i := fun i hi =>
      pure_inj (programStep_fail_notOwn (Ne.symm hi) (hall i))
    have hk : (x k).2 = (processes k).2 ∧ (x k).1.corrupted = true := by
      rcases programStep_fail_own (hall k) with ⟨-, hxk⟩ | ⟨hh, hxk⟩ <;> rw [pure_inj hxk]
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, hh⟩
    have hRoundVariables : ∀ i, (x i).2 = (processes i).2 := fun i => by
      by_cases hi : i = k
      · subst hi; exact hk.1
      · rw [hfor i hi]
    have hF : (Implementation.NetworkState.corrupt P k w).F = insert k w.F := by
      simp [Implementation.NetworkState.corrupt, hnew, hbud]
    have hrel : ∀ o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P),
        ProtocolRelation P ((x, Implementation.NetworkState.corrupt P k w, o') : ProtocolState P)
          ((G.applyBroadcast (Sum.inl (Label.fail k)), fun i => (x i).1,
            ABANetworkState.corrupt P k A, o') : ComposedState P) := by
      intro o'
      refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨fun _ => rfl, rfl, ?_, ?_, fun r => ?_,
        fun j r => ?_, fun r hr => ?_, fun j hj => ?_⟩
      · rw [hA]; exact corrupt_abaNetwork w k
      · rw [InstanceFamilyState.keys_applyBroadcast, hKeys, networkCorrupt_startedRounds]
      · simp only [InstanceFamilyState.applyBroadcast_apply, GBCA.ByABDY.corruptionAct_fail]
        rw [hG r]
        exact corrupt_gbcaNetwork w k r
      · simp only [InstanceFamilyState.applyBroadcast_apply, GBCA.ByABDY.corruptionAct_fail]
        rw [hst j r, hRoundVariables j]
      · rw [networkCorrupt_startedRounds] at hr
        obtain ⟨h1, h2, h3⟩ := hUntouched r hr
        exact ⟨fun j => by rw [networkCorrupt_sent]; exact h1 j,
          by rw [networkCorrupt_ghost]; exact h2, fun j => by rw [hRoundVariables j]; exact h3 j⟩
      · rw [hF, Finset.mem_insert] at hj
        by_cases hjk : j = k
        · subst hjk; exact hk.2
        · rw [hfor j hjk]; exact hCorrupted j (hj.resolve_left hjk)
    refine coupling_visible P hLne (fun o' _ => hrel o') (gbcaInstanceFamily_fail P G k)
      (fun i => ?_)
      (ABANetworkStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    rw [hCeq i]
    by_cases hi : i = k
    · subst hi
      rcases programStep_fail_own (hall i) with ⟨hh, hxk⟩ | ⟨hh, hxk⟩
      · rw [pure_inj hxk]; exact RoundLoopStep.failSelf _ hh
      · rw [pure_inj hxk]; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = w.recordStartedRound r id := by
      simpa using pure_inj (networkStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_callG_notOwn (Ne.symm hi) (hall i))
    obtain ⟨hh, hph, hrr, hest, hcase⟩ := programStep_callG_own (hall id)
    have hid : id ∉ w.F := fun hF => by
      rw [hCorrupted id hF] at hh
      exact absurd hh (by decide)
    have hcol : (G r).1 id = (processes id).2.roundVariables r := hst id r
    have hA' : A.recordStartedRound r id = ⟨(w.recordStartedRound r id).decidedSent,
        (w.recordStartedRound r id).F, (w.recordStartedRound r id).startedRounds⟩ := by
      rw [hA]
      simp [ABANetworkState.recordStartedRound, Implementation.NetworkState.recordStartedRound,
        hid]
    have hCs : ∀ i, RoundLoopStep P i (C i)
        (Sum.inl (Label.callG r id b) : ExtendedLabel P.n GBCA.ByABDY.Message)
        (PMF.pure ((x i).1)) := by
      intro i
      rw [hCeq i]
      by_cases hi : i = id
      · subst hi
        rcases hcase with ⟨-, -, hxid⟩ | ⟨-, hxid⟩ <;> rw [pure_inj hxid] <;>
          exact RoundLoopStep.callG _ r b hh hph hrr hest
      · rw [hfor i hi]; exact RoundLoopStep.callGIdle _ r id b (Ne.symm hi)
    rcases hcase with ⟨-, hin, hxid⟩ | ⟨hin, hxid⟩
    · have hx : x id = ((processes id).1.setProcessVariables
          { (processes id).1.processVariables with phase := .awaitG },
          (processes id).2.setRoundVariables r (((G r).1 id).setProcessVariables
            { ((G r).1 id).processVariables with input := some b })) := by
        rw [hcol]; exact pure_inj hxid
      have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.callG r id b))
          (PMF.pure (G.setInstanceState r (Function.update ((G r).1) id
            (((G r).1 id).setProcessVariables
              { ((G r).1 id).processVariables with input := some b }), (G r).2))) :=
        gbcaInstanceFamily_owned P G r (by simp)
          (GBCA.ByABDY.composition_label_step P r (by simp)
            (gbcaProgramStep_family id _
              (GBCA.ByABDY.GBCAProgramStep.call ((G r).1 id) b (by rw [hcol]; exact hin))
              (fun i hi => GBCA.ByABDY.GBCAProgramStep.callIdle _ id b (Ne.symm hi)))
            (GBCA.ByABDY.GBCANetworkStep.callG _ id b))
      exact coupling_visible P hLne (fun o' _ => relation_oneProcess P hR
          (w' := w.recordStartedRound r id) (o' := o') r id _ _ (G r).2 hx hfor rfl
          (fun _ => rfl) hA' (recordStartedRound_startedRounds_of_notMem w hid)
          (recordStartedRound_F w r id) (fun _ _ => by rw [recordStartedRound_sent])
          (fun _ _ => by rw [recordStartedRound_ghost])
          (by rw [hG r, recordStartedRound_sent, recordStartedRound_F, recordStartedRound_ghost]))
        hGs hCs (ABANetworkStep.callG A r id b) hWl
    · have hr : r ∈ w.startedRounds := startedRounds_of_input hUntouched hin
      have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.callG r id b))
          (PMF.pure G) :=
        gbcaInstanceFamily_owned_id P G r (by rw [hKeys]; exact hr) (by simp)
          (GBCA.ByABDY.composition_label_step P r (u := (G r).1) (x := (G r).1) (w := (G r).2)
            (w' := (G r).2) (by simp)
            (fun i => by
              by_cases hi : i = id
              · subst hi
                exact GBCA.ByABDY.GBCAProgramStep.callLoop _ b (by rw [hcol]; exact hin)
              · exact GBCA.ByABDY.GBCAProgramStep.callIdle _ id b (Ne.symm hi))
            (GBCA.ByABDY.GBCANetworkStep.callG _ id b))
      have hmap : ∀ i, (x i).2.roundVariablesMap = (processes i).2.roundVariablesMap := fun i => by
        by_cases hi : i = id
        · subst hi; rw [pure_inj hxid]
        · rw [hfor i hi]
      exact coupling_visible P hLne (fun o' _ => relation_noRound P hR
          (w' := w.recordStartedRound r id) (o' := o') (fun _ => rfl) hA' hmap
          (fun i => by
            by_cases hi : i = id
            · subst hi; rw [pure_inj hxid]; rfl
            · rw [hfor i hi])
          (recordStartedRound_sent w r id) (recordStartedRound_ghost w r id)
          (recordStartedRound_F w r id)
          (by rw [recordStartedRound_startedRounds_of_notMem w hid, Finset.insert_eq_of_mem hr]))
        hGs hCs (ABANetworkStep.callG A r id b) hWl
  | retG r id out =>
    obtain rfl : w' = w.writeGhost (abdyGhostStep P) (Sum.inl (Label.retG r id out)) :=
      pure_inj (networkStep_retG hn)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retG_notOwn (Ne.symm hi) (hall i))
    have hcol : (G r).1 id = (processes id).2.roundVariables r := hst id r
    have hstage : (processes id).1.processVariables.phase = Phase.awaitG ∧
        (processes id).1.processVariables.round = r ∧ (processes id).1.corrupted = false ∧
        ((processes id).2.roundVariables r).processVariables.input ≠ none ∧
        GBCA.ByABDY.GBCAProgramStep P r id ((G r).1 id) (Sum.inl (Sum.inl (Label.retG r id out)))
          (PMF.pure (((G r).1 id).setProcessVariables
            { ((G r).1 id).processVariables with returned := true })) ∧
        x id = ((processes id).1.setProcessVariables { (processes id).1.processVariables with
          estimate := out.estimate, lastGrade := some out, phase := .toCallW },
          (processes id).2.setRoundVariables r (((G r).1 id).setProcessVariables
            { ((G r).1 id).processVariables with returned := true })) := by
      cases out with
      | grade2 v =>
        obtain ⟨hh, hph, hrr, -, hin, hlv, hcnt, hret, hxid⟩ :=
          programStep_retGGrade2_own (hall id)
        exact ⟨hph, hrr, hh, hin, GBCA.ByABDY.GBCAProgramStep.retGrade2 _ v
          (by rw [hcol]; exact hin) (by rw [hcol]; exact hlv) (by rw [hcol]; exact hcnt)
          (by rw [hcol]; exact hret), by rw [hcol]; exact pure_inj hxid⟩
      | grade1 v =>
        obtain ⟨hh, hph, hrr, -, hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hxid⟩ :=
          programStep_retGGrade1_own (hall id)
        exact ⟨hph, hrr, hh, hin, GBCA.ByABDY.GBCAProgramStep.retGrade1 _ v
          (by rw [hcol]; exact hin) (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnotGrade2)
          (by rw [hcol]; exact hcnt) (by rw [hcol]; exact honce) (by rw [hcol]; exact hbind)
          (by rw [hcol]; exact hval) (by rw [hcol]; exact hret),
          by rw [hcol]; exact pure_inj hxid⟩
      | grade0 =>
        obtain ⟨hh, hph, hrr, -, hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hxid⟩ :=
          programStep_retGGrade0_own (hall id)
        exact ⟨hph, hrr, hh, hin, GBCA.ByABDY.GBCAProgramStep.retGrade0 _
          (by rw [hcol]; exact hin) (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnotGrade2)
          (by rw [hcol]; exact hnotGrade1) (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hval)
          (by rw [hcol]; exact hret), by rw [hcol]; exact pure_inj hxid⟩
    obtain ⟨hph, hrr, hh, hin, htransition, hx⟩ := hstage
    have hr : r ∈ w.startedRounds := startedRounds_of_input hUntouched hin
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.retG r id out))
        (PMF.pure (G.setInstanceState r (Function.update ((G r).1) id
          (((G r).1 id).setProcessVariables
            { ((G r).1 id).processVariables with returned := true }),
          ((G r).2).setBound (((G r).2).bound.getD
            (GBCA.ByABDY.boundOf ((G r).2).sent ((G r).2).F out))))) :=
      gbcaInstanceFamily_owned P G r (by simp)
        (GBCA.ByABDY.composition_label_step P r (by simp)
          (gbcaProgramStep_family id _ htransition
            (fun i hi => GBCA.ByABDY.GBCAProgramStep.retIdle _ id out (Ne.symm hi)))
          (GBCA.ByABDY.GBCANetworkStep.retG _ id out))
    refine coupling_visible P hLne (fun o' _ => relation_oneProcess P hR
        (w' := w.writeGhost (abdyGhostStep P) (Sum.inl (Label.retG r id out))) (o' := o')
        r id _ _ _ hx hfor rfl (fun _ => rfl) (by rw [hA]; simp)
        (by simp [Finset.insert_eq_of_mem hr]) (by simp) (fun _ _ => by simp)
        (fun _ h => writeGhost_retG_ne P w r id out h)
        (by rw [hG r]; simp [GBCA.ByABDY.NetworkState.setBound]))
      hGs (fun i => ?_) (ABANetworkStep.retGIdle A r id out) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [hx]; exact RoundLoopStep.retG _ r out hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.retGIdle _ r id out (Ne.symm hi)
  | boundG r b =>
    obtain ⟨hb, hw⟩ := networkStep_announceBound hn
    obtain rfl : w = w' := by
      simpa using (pure_inj hw).symm
    have hx : x = processes := funext fun i => pure_inj (programStep_boundG (hall i))
    subst hx
    have hr : r ∈ w.startedRounds := startedRounds_of_ghost hUntouched hb
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.boundG r b))
        (PMF.pure G) :=
      gbcaInstanceFamily_owned_id P G r (by rw [hKeys]; exact hr) (by simp)
        (GBCA.ByABDY.composition_label_step P r (u := (G r).1) (x := (G r).1) (w := (G r).2)
          (w' := (G r).2) (by simp) (fun _ => GBCA.ByABDY.GBCAProgramStep.boundGIdle _ b)
          (GBCA.ByABDY.GBCANetworkStep.announceBound _ b (by rw [hG r]; exact hb)))
    refine coupling_visible P hLne (fun o' _ => relation_noRound P hR (fun _ => rfl) hA
      (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl) hGs (fun i => ?_)
      (ABANetworkStep.boundGIdle A r b) hWl
    rw [hCeq i]; exact RoundLoopStep.boundGIdle _ r b

/-- The matching on the silent label. The protocol's own `terminate` transition writes
no coordinate the relation reads, so the composed system matches it by a stutter; the
network's two injections and the resolution of a round of the common coin are matched by a
transition. -/
theorem coupling_tau (P : Parameters) {processes : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P)}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    (hR : ProtocolRelation P (processes, w, o) (G, C, A, o)) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (processes, w, o) (Sum.inl Label.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)), PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
    ((composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) ∨ Ω.bind id = PMF.pure (G, C, A, o))
    := by
  obtain ⟨hC, -, hA, hKeys, hG, hst, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  rcases protocolExtended_tau_cases P h with ⟨i, y, hy, rfl⟩ | ⟨w', hn, rfl⟩ |
    ⟨r, hr, μw, hW, rfl⟩
  · obtain ⟨-, -, -, -, -, hyeq⟩ := programStep_tau_terminate hy
    obtain rfl : y = ((processes i).1, { (processes i).2 with terminated := true }) :=
      pure_inj hyeq
    have hrel' : ProtocolRelation P
        ((Function.update processes i ((processes i).1,
          { (processes i).2 with terminated := true }), w, o) : ProtocolState P)
        ((G, C, A, o) : ComposedState P) := by
      refine relation_noRound P hR (fun j => ?_) hA (fun j => ?_) (fun j => ?_) rfl rfl rfl rfl
      · by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact hC j
        · rw [Function.update_of_ne hj]; exact hC j
      · by_cases hj : j = i
        · subst hj; rw [Function.update_self]
        · rw [Function.update_of_ne hj]
      · by_cases hj : j = i
        · subst hj; rw [Function.update_self]
        · rw [Function.update_of_ne hj]
    obtain ⟨Ω, hrel, hbind⟩ := coupling_pure hrel'
    exact ⟨Ω, hrel, Or.inr hbind⟩
  · rcases networkStep_tau hn with ⟨r, k, m, hF, hr, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.recordGBCASend r k m := pure_inj hw
      have hrel' := relation_oneRound P hR (x := processes) (w' := w.recordGBCASend r k m)
        (o' := o) (C' := C) (A' := A) r ((G r).1, ((G r).2).recordGBCASend k m) hC
        (by rw [hA]; rfl) (by rw [recordGBCASend_startedRounds, Finset.insert_eq_of_mem hr]) rfl
        (fun r' h => recordGBCASend_sent_ne w r k m h) (fun _ _ => rfl)
        (by rw [hG r]; simp [GBCA.ByABDY.NetworkState.recordGBCASend])
        (fun j => hst j r) (fun _ _ _ => rfl) (fun _ => rfl)
      obtain ⟨Ω, hrel, hbind⟩ := coupling_pure hrel'
      refine ⟨Ω, hrel, Or.inl ?_⟩
      rw [hbind]
      exact composedHidden_of_tau P (composedExtended_tau_gbca P (gbcaInstanceFamily_tau P G r
        (by rw [hKeys]; exact hr)
        (GBCA.ByABDY.composition_tau_network P r (u := (G r).1) (w := (G r).2)
          (GBCA.ByABDY.GBCANetworkStep.byzantineGBCA _ k m (by rw [hG r]; exact hF)))))
    · obtain rfl : w' = w.recordDecided k b := pure_inj hw
      have hrel' := relation_noRound P hR (x := processes) (w' := w.recordDecided k b) (o' := o)
        (C' := C) (A' := A.recordDecided k b) hC (by rw [hA]; rfl) (fun _ => rfl) (fun _ => rfl)
        rfl rfl rfl rfl
      obtain ⟨Ω, hrel, hbind⟩ := coupling_pure hrel'
      refine ⟨Ω, hrel, Or.inl ?_⟩
      rw [hbind]
      exact composedHidden_of_tau P (composedExtended_tau_ABANetwork P
        (ABANetworkStep.byzantineDecided A k b (by rw [hA]; exact hF)))
  · obtain ⟨Ω, hΩ, hbind⟩ := coupling_map (μw.map (o.setInstanceState r))
      (fun o' => ((processes, w, o') : ProtocolState P))
      (fun o' => ((G, C, A, o') : ComposedState P))
      (fun o' _ => relation_noRound P hR (x := processes) (w' := w) (o' := o') hC hA
        (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl)
    rw [← prodPMF_two_pure_factors] at hΩ
    rw [← prodPMF_three_pure_factors] at hbind
    exact ⟨Ω, hΩ, Or.inl (hbind ▸ composedHidden_of_tau P (composedExtended_tau_coin P hr hW))⟩

/-! ### The simulation -/

/-- The matching at the group level: the labels the components synchronise on are hidden in both
systems, so a hidden protocol synchronisation is matched by a silent transition of the composed
group or by a stutter of the composed group. The second disjunct is the stutter, under `τ`, after
a transition that leaves the protocol state related to the composed state it starts from. -/
theorem coupling_hidden (P : Parameters) {u : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P u t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolHidden P).step u l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)), PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
    ((composedHidden P).step t l (Ω.bind id) ∨ (l = Label.tau ∧ Ω.bind id = PMF.pure t)) := by
  obtain ⟨processes, w, o⟩ := u
  obtain ⟨G, C, A, o'⟩ := t
  obtain rfl : o = o' := ((protocolRelation_mk P _ _ _ _ _ _ _).mp hR).2.1
  rcases (protocolHidden_step_iff P _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := coupling_event P hR e hstep
    exact ⟨Ω, hrel, hs.imp id (fun hp => ⟨rfl, hp⟩)⟩
  · by_cases hl : l = Label.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := coupling_tau P hR hstep
      exact ⟨Ω, hrel, hs.imp id (fun hp => ⟨rfl, hp⟩)⟩
    · obtain ⟨Ω, hrel, hs⟩ := coupling_label P hR hl hstep
      exact ⟨Ω, hrel, Or.inl hs⟩

/-- The matching at the system level: a hidden sub-protocol label is silent in both systems, and
every other label is matched on the same label or by a stutter. A hidden label is never `τ`, so
the stutter arises only under `τ`, where the reflexivity of `weakTau` discharges it. -/
theorem coupling_step (P : Parameters) {u : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P u t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step u l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (protocol_step_iff P u l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := coupling_hidden P hR hg
    rcases hlay with hlay | ⟨rfl, -⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl, weakTau_of_step rfl
        ((System.abstract_step _ _ _ _ _).mpr (Or.inl ⟨rfl, l', hmem, hlay⟩))⟩⟩
    · exact absurd hmem Label.tau_not_mem_hiddenAPI
  · obtain ⟨Ω, hrel, hlay⟩ := coupling_hidden P hR hg
    rcases hlay with hlay | ⟨rfl, hpure⟩
    · have hstep : (composed P).step t l (Ω.bind id) :=
        (System.abstract_step _ _ _ _ _).mpr (Or.inr ⟨hnm, hlay⟩)
      by_cases hτ : l = Silent.τ
      · exact ⟨Ω, hrel, Or.inl ⟨hτ, weakTau_of_step hτ hstep⟩⟩
      · exact ⟨Ω, hrel, Or.inr ⟨hτ, weakStep_strong hstep⟩⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl, hpure ▸ weakTau_refl (composed P) (PMF.pure t)⟩⟩

/-- The two initial states are related: everything is initial, no round is started and none is
in the family's map, and every column is the initial round's variables, which is what an untouched
round reads as in the protocol. -/
theorem protocolRelation_init (P : Parameters) :
    ProtocolRelation P (protocol P).init (composed P).init :=
  ⟨fun _ => rfl, rfl, rfl, rfl, fun _ => rfl,
    fun _ r => (RoundVariablesMap.initial_roundVariables P.n r).symm,
    fun _ _ => ⟨fun _ => rfl, rfl, fun _ => Finmap.notMem_empty⟩,
    fun _ hj => absurd hj (Finset.notMem_empty _)⟩

/-- **The protocol forward-simulates into its composed system**
along the Dirac lift of `ProtocolRelation`. -/
theorem protocolSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (protocol P) (composed P)
      (diracRel (ProtocolRelation P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRelation_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact coupling_step P hR hstep

/-- **The composition inclusion**: every trace distribution the protocol
achieves is achieved by its composed system. -/
theorem protocol_composed (P : Parameters) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (composed P) :=
  (protocolSimulation P).achievableTraceDists_subset

/-! ### Mechanical axiom check

The composition step of the chain may not acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.ABDY.protocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_composed

end ABDY

end ABA
end PLTS
