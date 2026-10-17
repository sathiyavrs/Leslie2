/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.Implementation.InputEnabledness
import Leslie2Protocols.Framework.InputEnabledness

/-!
# The inputs and the outputs of the components of a composed system

The input labels and the output labels of the four components of a composed system, the `n` round
loops, the ABA network, the round family and the common coin (`ABA/Composition/Components.lean`),
over the extended alphabet `ExtendedLabel n M`. A component under full synchronisation takes as
inputs every non-silent label outside its outputs.

* The round loop of process `j` outputs its graded-agreement call `callG _ j _`, its coin call
  `callW _ j`, its DECIDED send `decidedSend j _`, its DECIDED relay `decidedRelay j _` and its
  return `retABA j _` (`roundLoopInputOutputLabels`).
* The ABA network outputs the DECIDED deliveries, `fail`, and a corrupted process's calls
  `byzantineCallG` and `byzantineCallW`; over the message type `M` it outputs the round multicast
  `gbcaSend` and the round delivery `gbcaDeliver`, on which it has no transition. Its DECIDED
  injection is silent. Its inputs are `callABA`, `retABA`, `callG`, `retG`, `boundG`, `callW`,
  `retW`, the DECIDED sends and the DECIDED relays (`abaNetworkInputOutputLabels`).
* The round family outputs the returns `retG` and the announcements `boundG`, and its inputs are
  every other non-silent label (`roundFamilyInputOutputLabels`). The family takes an input on the
  transition of the round instance that owns it or on its idle transition, so its
  input-enabledness is that of the round instance (`System.InputEnabled.family`).
* The common coin outputs its returns `retW` and takes every other non-silent label as an input.
  Its label sets and its input-enabledness are those of the implementation's coin, at the empty
  type of round-internal events (`Implementation.coinInputOutputLabels`,
  `Implementation.coin_inputEnabled`).

`roundLoop_inputEnabled` and `abaNetwork_inputEnabled` give each component a transition on every
input at every state. At an unreplaced round loop, the process's own call `callABA j _`
is taken on `input` at a process holding no input and on `inputLoop` at one holding an input; the
round's return `retG r j _` on `retG` at the phase `awaitG` of round `r` and on `retGLoop`
elsewhere; the coin's return on `retW` and `retWLoop` likewise; a DECIDED delivery to `j` on
`decidedDeliverReceive` at a payload not held from its sender and on `decidedDeliverLoop` at one
held; and `fail j` on `failSelf`. Every other input is taken on an idle transition. A replaced
round loop takes every input on `corruptedIdle`, since no input lies in `roundLoopActsAt j`. The
ABA network takes each of its inputs on one unguarded transition.

`composedComponents_compatible` states that the outputs of the `n` round loops, the ABA network,
the round family and the common coin are pairwise disjoint (the simulations paper, Definition 2):
the outputs of the round loop of `j` name `j` as the caller, the sender or the returner, and the
round loops, the network, the family and the coin output labels of distinct constructors.
-/

namespace PLTS
namespace ABA
namespace Composition

/-! ### The label sets -/

/-- The input labels and the output labels of the round loop of process `j`. The outputs are
`j`'s graded-agreement call, coin call, DECIDED send, DECIDED relay and return, and the inputs are
every other non-silent label. -/
def roundLoopInputOutputLabels (P : Parameters) (M : Type) (j : Fin P.n) :
    InputOutputLabels (ExtendedLabel P.n M) where
  inputLabels := {l | l ≠ Silent.τ ∧ (∀ r b, l ≠ Sum.inl (.callG r j b)) ∧
    (∀ r, l ≠ Sum.inl (.callW r j)) ∧ (∀ b, l ≠ Sum.inr (.decidedSend j b)) ∧
    (∀ b, l ≠ Sum.inr (.decidedRelay j b)) ∧ ∀ b, l ≠ Sum.inl (.retABA j b)}
  outputLabels := {l | (∃ r b, l = Sum.inl (.callG r j b)) ∨ (∃ r, l = Sum.inl (.callW r j)) ∨
    (∃ b, l = Sum.inr (.decidedSend j b)) ∨ (∃ b, l = Sum.inr (.decidedRelay j b)) ∨
    ∃ b, l = Sum.inl (.retABA j b)}

/-- The input labels and the output labels of the ABA network. The outputs are the DECIDED
deliveries, corruption, a corrupted process's two sub-protocol calls, and the round multicast and
the round delivery, on which the network has no transition. The inputs are the ABA calls and
returns, the graded-agreement calls, returns and announcements, the coin's calls and returns, and
the DECIDED sends and relays. -/
def abaNetworkInputOutputLabels (P : Parameters) (M : Type) :
    InputOutputLabels (ExtendedLabel P.n M) where
  inputLabels := {l | (∃ id b, l = Sum.inl (.callABA id b)) ∨ (∃ id b, l = Sum.inl (.retABA id b)) ∨
    (∃ r id b, l = Sum.inl (.callG r id b)) ∨ (∃ r id out, l = Sum.inl (.retG r id out)) ∨
    (∃ r b, l = Sum.inl (.boundG r b)) ∨ (∃ r id, l = Sum.inl (.callW r id)) ∨
    (∃ r id co, l = Sum.inl (.retW r id co)) ∨ (∃ j b, l = Sum.inr (.decidedSend j b)) ∨
    ∃ j b, l = Sum.inr (.decidedRelay j b)}
  outputLabels := {l | (∃ i j b, l = Sum.inr (.decidedDeliver i j b)) ∨
    (∃ k, l = Sum.inl (.fail k)) ∨ (∃ r k b, l = Sum.inr (.byzantineCallG r k b)) ∨
    (∃ r k, l = Sum.inr (.byzantineCallW r k)) ∨ (∃ r k m, l = Sum.inr (.gbcaSend r k m)) ∨
    ∃ r i k m, l = Sum.inr (.gbcaDeliver r i k m)}

/-- The input labels and the output labels of the round family. The outputs are the returns and
the announcements of every round, and the inputs are every other non-silent label. -/
def roundFamilyInputOutputLabels (P : Parameters) (M : Type) :
    InputOutputLabels (ExtendedLabel P.n M) where
  inputLabels := {l | l ≠ Silent.τ ∧ (∀ r id out, l ≠ Sum.inl (.retG r id out)) ∧
    ∀ r b, l ≠ Sum.inl (.boundG r b)}
  outputLabels := {l | (∃ r id out, l = Sum.inl (.retG r id out)) ∨
    ∃ r b, l = Sum.inl (.boundG r b)}

/-! ### Input-enabledness -/

/-- **The round loop of `j` is input-enabled.** At an unreplaced round loop, the process's own
call, the round's return, the coin's return and a DECIDED delivery to `j` are each taken on the
transition its guards admit or on the loop beside it, `fail j` on `failSelf`, and every other
input on an idle transition. A replaced round loop takes every input on `corruptedIdle`. -/
theorem roundLoop_inputEnabled (P : Parameters) (M : Type) [DecidableEq M] (j : Fin P.n) :
    (roundLoopProgram P M j).InputEnabled (roundLoopInputOutputLabels P M j).inputLabels := by
  refine System.InputEnabled.of_forall_step ?_
  rintro l ⟨hτ, hcallG, hcallW, hsend, hrelay, hret⟩ c
  cases hc : c.corrupted
  · rcases l with (_ | ⟨id, b⟩ | ⟨id, b⟩ | ⟨r, id, b⟩ | ⟨r, id, out⟩ | ⟨r, b⟩ | ⟨r, id⟩ |
        ⟨r, id, co⟩ | id) |
      (⟨r, k, m⟩ | ⟨r, i, k, m⟩ | ⟨k, b⟩ | ⟨k, b⟩ | ⟨i, k, b⟩ | ⟨r, k, e⟩ | ⟨r, k, b⟩ | ⟨r, k⟩)
    · exact absurd rfl hτ
    · by_cases hid : id = j
      · subst hid
        by_cases hin : c.processVariables.input = none
        · exact ⟨_, RoundLoopStep.input c b hc hin⟩
        · exact ⟨_, RoundLoopStep.inputLoop c b hc hin⟩
      · exact ⟨_, RoundLoopStep.callABAIdle c id b hid⟩
    · have hid : id ≠ j := by
        rintro rfl
        exact hret b rfl
      exact ⟨_, RoundLoopStep.retABAIdle c id b hid⟩
    · have hid : id ≠ j := by
        rintro rfl
        exact hcallG r b rfl
      exact ⟨_, RoundLoopStep.callGIdle c r id b hid⟩
    · by_cases hid : id = j
      · subst hid
        by_cases hw : c.processVariables.phase = .awaitG ∧ c.processVariables.round = r
        · exact ⟨_, RoundLoopStep.retG c r out hc hw.1 hw.2⟩
        · exact ⟨_, RoundLoopStep.retGLoop c r out hc hw⟩
      · exact ⟨_, RoundLoopStep.retGIdle c r id out hid⟩
    · exact ⟨_, RoundLoopStep.boundGIdle c r b⟩
    · have hid : id ≠ j := by
        rintro rfl
        exact hcallW r rfl
      exact ⟨_, RoundLoopStep.callWIdle c r id hid⟩
    · by_cases hid : id = j
      · subst hid
        by_cases hw : c.processVariables.phase = .awaitW ∧ c.processVariables.round = r
        · exact ⟨_, RoundLoopStep.retW c r co hc hw.1 hw.2⟩
        · exact ⟨_, RoundLoopStep.retWLoop c r co hc hw⟩
      · exact ⟨_, RoundLoopStep.retWIdle c r id co hid⟩
    · by_cases hid : id = j
      · subst hid
        exact ⟨_, RoundLoopStep.failSelf c hc⟩
      · exact ⟨_, RoundLoopStep.failIdle c id hid⟩
    · exact ⟨_, RoundLoopStep.gbcaSendIdle c r k m⟩
    · exact ⟨_, RoundLoopStep.gbcaDeliverIdle c r i k m⟩
    · have hk : k ≠ j := by
        rintro rfl
        exact hsend b rfl
      exact ⟨_, RoundLoopStep.decidedSendIdle c k b hk⟩
    · have hk : k ≠ j := by
        rintro rfl
        exact hrelay b rfl
      exact ⟨_, RoundLoopStep.decidedRelayIdle c k b hk⟩
    · by_cases hi : i = j
      · subst hi
        by_cases hb : b ∈ c.decidedDelivered k
        · exact ⟨_, RoundLoopStep.decidedDeliverLoop c k b hc hb⟩
        · exact ⟨_, RoundLoopStep.decidedDeliverReceive c k b hc hb⟩
      · exact ⟨_, RoundLoopStep.decidedDeliverIdle c i k b hi⟩
    · exact e.elim
    · exact ⟨_, RoundLoopStep.byzantineCallGIdle c r k b⟩
    · exact ⟨_, RoundLoopStep.byzantineCallWIdle c r k⟩
  · refine ⟨_, RoundLoopStep.corruptedIdle c l hc hτ fun hown => ?_⟩
    rcases l with (_ | _ | _ | ⟨r, id, b⟩ | _ | _ | ⟨r, id⟩ | _ | _) |
      (_ | _ | ⟨k, b⟩ | _ | _ | _ | _ | _) <;> simp only [roundLoopActsAt] at hown
    · subst hown
      exact hcallG r b rfl
    · subst hown
      exact hcallW r rfl
    · subst hown
      exact hsend b rfl

/-- **The ABA network is input-enabled**: it takes each of its inputs on one unguarded
transition. -/
theorem abaNetwork_inputEnabled (P : Parameters) (M : Type) [DecidableEq M] :
    (ABANetwork P M).InputEnabled (abaNetworkInputOutputLabels P M).inputLabels := by
  rintro a l (⟨id, b, rfl⟩ | ⟨id, b, rfl⟩ | ⟨r, id, b, rfl⟩ | ⟨r, id, out, rfl⟩ | ⟨r, b, rfl⟩ |
    ⟨r, id, rfl⟩ | ⟨r, id, co, rfl⟩ | ⟨j, b, rfl⟩ | ⟨j, b, rfl⟩)
  · exact ⟨_, ABANetworkStep.callABAIdle a id b⟩
  · exact ⟨_, ABANetworkStep.retABAIdle a id b⟩
  · exact ⟨_, ABANetworkStep.callG a r id b⟩
  · exact ⟨_, ABANetworkStep.retGIdle a r id out⟩
  · exact ⟨_, ABANetworkStep.boundGIdle a r b⟩
  · exact ⟨_, ABANetworkStep.callWIdle a r id⟩
  · exact ⟨_, ABANetworkStep.retWIdle a r id co⟩
  · exact ⟨_, ABANetworkStep.decidedSend a j b⟩
  · exact ⟨_, ABANetworkStep.decidedRelay a j b⟩

/-! ### Compatibility -/

/-- **The components of a composed system are compatible**: the outputs of the `n` round loops,
the ABA network, the round family and the common coin are pairwise disjoint (the simulations
paper, Definition 2). The outputs of the round loop of `j` name `j`, and the round loops, the
network, the family and the coin output labels of distinct constructors. -/
theorem composedComponents_compatible (P : Parameters) (M : Type) :
    Pairwise (fun i j : Fin P.n =>
      (roundLoopInputOutputLabels P M i).Compatible (roundLoopInputOutputLabels P M j)) ∧
    (∀ j : Fin P.n,
      (roundLoopInputOutputLabels P M j).Compatible (abaNetworkInputOutputLabels P M)) ∧
    (∀ j : Fin P.n,
      (roundLoopInputOutputLabels P M j).Compatible (roundFamilyInputOutputLabels P M)) ∧
    (∀ j : Fin P.n, (roundLoopInputOutputLabels P M j).Compatible
      (Implementation.coinInputOutputLabels P M Empty)) ∧
    (abaNetworkInputOutputLabels P M).Compatible (roundFamilyInputOutputLabels P M) ∧
    (abaNetworkInputOutputLabels P M).Compatible
      (Implementation.coinInputOutputLabels P M Empty) ∧
    (roundFamilyInputOutputLabels P M).Compatible
      (Implementation.coinInputOutputLabels P M Empty) := by
  refine ⟨fun i j hij => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_,
    fun j => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_,
    Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · rintro l (⟨r, b, rfl⟩ | ⟨r, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩)
      (⟨r', b', h⟩ | ⟨r', h⟩ | ⟨b', h⟩ | ⟨b', h⟩ | ⟨b', h⟩) <;> simp_all
  · rintro l (⟨r, b, rfl⟩ | ⟨r, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩)
      (⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩) <;>
      simp at h
  · rintro l (⟨r, b, rfl⟩ | ⟨r, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩)
      (⟨_, _, _, h⟩ | ⟨_, _, h⟩) <;> simp at h
  · rintro l (⟨r, b, rfl⟩ | ⟨r, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩) ⟨_, _, _, h⟩ <;>
      simp at h
  · rintro l (⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩) (⟨_, _, _, h⟩ | ⟨_, _, h⟩) <;> simp at h
  · rintro l (⟨_, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩) ⟨_, _, _, h⟩ <;> simp at h
  · rintro l (⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩) ⟨_, _, _, h⟩ <;> simp at h

end Composition
end ABA
end PLTS
