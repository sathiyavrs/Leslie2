/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Algorithm
import Leslie2Protocols.Framework.InputEnabledness

/-!
# The inputs and the outputs of the reliable-broadcast components

The input labels and the output labels of the `n` programs and the instance's network
(`ABA/ReliableBroadcast/Bracha/Components.lean`), over the instance-internal alphabet
`BroadcastLabel n M`. A component under full synchronisation takes as inputs every non-silent
label outside its outputs.

* Process `j`'s program outputs its multicasts `send j _` and its return `ret j _`. Its inputs are
  the call, a multicast or a return at another process, every delivery and corruption
  (`programInputOutputLabels`).
* The network outputs the deliveries, and its injections are silent. Its inputs are the call, the
  multicasts, the returns and corruption (`networkInputOutputLabels`).

`program_inputEnabled` and `network_inputEnabled` give each component a transition on every input
at every state. The leader's program takes the call on `ProgramStep.call` when it holds no input
and on `ProgramStep.callLoop` when it holds one, and every other program on
`ProgramStep.callIdle`. A delivery is taken by `deliverReceive` at the receiver and by
`deliverIdle` elsewhere, a multicast or a return at another process by `sendIdle` or `retIdle`,
and corruption by `failIdle`. The network takes each of its inputs on one unguarded transition.

`brachaInstance_inputEnabled` states that the instance is input-enabled on the inputs of the BRB
specification, the call and corruption, read through the algorithm
(`ABA/ReliableBroadcast/Bracha/Algorithm.lean`): the leader takes the call on
`BrachaAlgorithm.call` when it holds no input and on `BrachaAlgorithm.callLoop` when it holds one,
and corruption is taken on `BrachaAlgorithm.fail`.

`brachaInstance_compatible` states that the outputs of the `n` programs and the network are
pairwise disjoint (the simulations paper, Definition 2): the outputs of process `j`'s program name
`j`, and the network outputs only deliveries.
-/

namespace PLTS
namespace ABA
namespace BRB

/-! ### The label sets -/

/-- The input labels and the output labels of process `j`'s program. The outputs are `j`'s
multicasts and `j`'s return, and the inputs are every other non-silent label. -/
def programInputOutputLabels (n : ℕ) (M : Type) (j : Fin n) :
    InputOutputLabels (BroadcastLabel n M) where
  inputLabels := {l | l ≠ Silent.τ ∧ (∀ m, l ≠ Sum.inr (.send j m)) ∧ ∀ m, l ≠ Sum.inl (.ret j m)}
  outputLabels := {l | (∃ m, l = Sum.inr (.send j m)) ∨ ∃ m, l = Sum.inl (.ret j m)}

/-- The input labels and the output labels of the instance's network. The outputs are the
deliveries, and the inputs are the call, the multicasts, the returns and corruption. -/
def networkInputOutputLabels (n : ℕ) (M : Type) : InputOutputLabels (BroadcastLabel n M) where
  inputLabels := {l | (∃ m, l = Sum.inl (.call m)) ∨ (∃ j m, l = Sum.inr (.send j m)) ∨
    (∃ i m, l = Sum.inl (.ret i m)) ∨ ∃ i, l = Sum.inl (.fail i)}
  outputLabels := {l | ∃ i k m, l = Sum.inr (.deliver i k m)}

/-! ### Input-enabledness -/

variable {M : Type} [DecidableEq M]

/-- Process `j`'s program is input-enabled. The leader takes the call on `call` when it holds no
input and on `callLoop` when it holds one, and every other program on `callIdle`. A delivery is
taken by `deliverReceive` at `j` and by `deliverIdle` elsewhere, a multicast or a return at
another process by `sendIdle` or `retIdle`, and corruption by `failIdle`. -/
theorem program_inputEnabled (P : Parameters) (ldr j : Fin P.n) :
    (broadcastProgram P ldr j (M := M)).InputEnabled
      (programInputOutputLabels P.n M j).inputLabels := by
  rintro p l ⟨hτ, hsend, hret⟩
  rcases l with (_ | m | ⟨i, m⟩ | i) | (⟨i, x⟩ | ⟨i, k, x⟩)
  · exact absurd rfl hτ
  · by_cases hj : j = ldr
    · by_cases hin : p.processVariables.input = none
      · exact ⟨_, ProgramStep.call p m hj hin⟩
      · exact ⟨_, ProgramStep.callLoop p m hj hin⟩
    · exact ⟨_, ProgramStep.callIdle p m hj⟩
  · have hi : i ≠ j := by
      rintro rfl
      exact hret m rfl
    exact ⟨_, ProgramStep.retIdle p i m hi⟩
  · exact ⟨_, ProgramStep.failIdle p i⟩
  · have hi : i ≠ j := by
      rintro rfl
      exact hsend x rfl
    exact ⟨_, ProgramStep.sendIdle p i x hi⟩
  · by_cases hi : i = j
    · subst hi
      exact ⟨_, ProgramStep.deliverReceive p k x⟩
    · exact ⟨_, ProgramStep.deliverIdle p i k x hi⟩

/-- The instance's network is input-enabled: it takes the call, a multicast, a return and
corruption each on one unguarded transition. -/
theorem network_inputEnabled (P : Parameters) (ldr : Fin P.n) :
    (broadcastNetwork P ldr M).InputEnabled (networkInputOutputLabels P.n M).inputLabels := by
  rintro w l (⟨m, rfl⟩ | ⟨j, m, rfl⟩ | ⟨i, m, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨_, NetworkStep.call w m⟩
  · exact ⟨_, NetworkStep.send w j m⟩
  · exact ⟨_, NetworkStep.retIdle w i m⟩
  · exact ⟨_, NetworkStep.fail w i⟩

/-- **Bracha's instance is input-enabled** on the inputs of the BRB specification: the leader takes
the call on `BrachaAlgorithm.call` when it holds no input and on `BrachaAlgorithm.callLoop` when it
holds one, and corruption is taken on `BrachaAlgorithm.fail`. -/
theorem brachaInstance_inputEnabled (P : Parameters) (ldr : Fin P.n) :
    (brachaInstance P ldr M).InputEnabled (specInstInputOutputLabels P.n M).inputLabels := by
  rintro s l (⟨m, rfl⟩ | ⟨id, rfl⟩)
  · by_cases hin : (s.processVariables ldr).input = none
    · exact ⟨_, algorithm_brachaInstance_step P ldr s _ _ (BrachaAlgorithm.call s m hin)⟩
    · exact ⟨_, algorithm_brachaInstance_step P ldr s _ _ (BrachaAlgorithm.callLoop s m hin)⟩
  · exact ⟨_, algorithm_brachaInstance_step P ldr s _ _ (BrachaAlgorithm.fail s id)⟩

/-! ### Compatibility -/

/-- The outputs of the `n` programs and the network are pairwise disjoint (the simulations
paper, Definition 2). The outputs of process `j`'s program name `j`, and the network outputs only
deliveries, which no program outputs. -/
theorem brachaInstance_compatible (n : ℕ) (M : Type) :
    Pairwise (fun i j : Fin n =>
      (programInputOutputLabels n M i).Compatible (programInputOutputLabels n M j)) ∧
    ∀ j : Fin n, (programInputOutputLabels n M j).Compatible (networkInputOutputLabels n M) := by
  refine ⟨fun i j hij => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_⟩
  · rintro l (⟨m, rfl⟩ | ⟨m, rfl⟩) (⟨m', h⟩ | ⟨m', h⟩)
    · simp only [Sum.inr.injEq, BroadcastEvent.send.injEq] at h
      exact hij h.1
    · simp at h
    · simp at h
    · simp only [Sum.inl.injEq, Label.ret.injEq] at h
      exact hij h.1
  · rintro l (⟨m, rfl⟩ | ⟨m, rfl⟩) ⟨i, k, x, h⟩ <;> simp at h

end BRB
end ABA
end PLTS
