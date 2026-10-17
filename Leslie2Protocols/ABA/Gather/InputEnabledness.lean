/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Components
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.InputEnabledness
import Leslie2Protocols.Framework.InputEnabledness

/-!
# The inputs and the outputs of the gather components

The input labels and the output labels of the `n` gather programs, the gather network and the `n`
input broadcasts (`ABA/Gather/Components.lean`), over the instance-internal alphabet
`GatherLabel n X`. A component under full synchronisation takes as inputs every non-silent label
outside its outputs.

* Process `j`'s program outputs its multicasts `send j _`, its call of the instance broadcasting
  its input `inputBroadcastCall j _` and its return `ret j _` (`programInputOutputLabels`).
* The gather network outputs the deliveries and the announcement of the core, and its injections
  are silent. Its inputs are the calls, the multicasts, the returns, the calls and the returns of
  the input broadcasts, and corruption (`networkInputOutputLabels`).
* The instance broadcasting `k`'s input, read along `inputBroadcastLabelMap k`, outputs its
  returns `inputBroadcastRet k _ _` (`inputBroadcastInputOutputLabels`).

`program_inputEnabled` and `network_inputEnabled` give each gather component a transition on every
input at every state. The program of `id` takes the call on `ProgramStep.call` when it holds no
input and on `ProgramStep.callLoop` when it holds one, and every other program on
`ProgramStep.callIdle`. A delivery or a return of an input broadcast is taken by the receiver's
transition at `j` and by an idle transition elsewhere; a multicast, a call of an input broadcast
or a return at another process by an idle transition; the announcement of the core by `coreIdle`;
corruption by `failIdle`. The network takes each of its inputs on one unguarded transition.

`inputBroadcast_inputEnabled` carries the input-enabledness of a broadcast instance on the inputs
of the BRB specification, the call and corruption, along the pullback: the call of the instance is
the image of `inputBroadcastCall k _`, corruption is its own image, and every other input has no
image and is taken by the pullback's idle transition. `BRB.brachaInstance_inputEnabled`
(`ABA/ReliableBroadcast/Bracha/InputEnabledness.lean`) gives the hypothesis for Bracha's instance,
whose leader takes the call on `BRB.BrachaAlgorithm.call` or `BRB.BrachaAlgorithm.callLoop`, and
`BRB.specInst_inputEnabled` gives it for the specification.
`instanceOverBracha_inputBroadcast_inputEnabled` and
`instanceOverBroadcastSpecification_inputBroadcast_inputEnabled` are the two compositions.

`instanceOverBroadcastsExtended_compatible` states that the outputs of the `n` programs, the
network and the `n` input broadcasts are pairwise disjoint (the simulations paper, Definition 2):
the outputs of process `j`'s program name `j` as the sender, the caller or the returner, the
network outputs only deliveries and announcements, and the outputs of input broadcast `k` name `k`
as the broadcasting instance.
-/

namespace PLTS
namespace ABA
namespace Gather

/-! ### The label sets -/

/-- The input labels and the output labels of process `j`'s gather program. The outputs are `j`'s
multicasts, `j`'s call of the instance broadcasting its input and `j`'s return, and the inputs
are every other non-silent label. -/
def programInputOutputLabels (n : ℕ) (X : Type) (j : Fin n) :
    InputOutputLabels (GatherLabel n X) where
  inputLabels := {l | l ≠ Silent.τ ∧ (∀ m, l ≠ Sum.inr (.send j m)) ∧
    (∀ x, l ≠ Sum.inr (.inputBroadcastCall j x)) ∧ ∀ g, l ≠ Sum.inl (.ret j g)}
  outputLabels := {l | (∃ m, l = Sum.inr (.send j m)) ∨
    (∃ x, l = Sum.inr (.inputBroadcastCall j x)) ∨ ∃ g, l = Sum.inl (.ret j g)}

/-- The input labels and the output labels of the gather network. The outputs are the deliveries
and the announcement of the core, and the inputs are the calls, the multicasts, the returns, the
calls and the returns of the input broadcasts, and corruption. -/
def networkInputOutputLabels (n : ℕ) (X : Type) : InputOutputLabels (GatherLabel n X) where
  inputLabels := {l | (∃ id x, l = Sum.inl (.call id x)) ∨ (∃ j m, l = Sum.inr (.send j m)) ∨
    (∃ id g, l = Sum.inl (.ret id g)) ∨ (∃ j x, l = Sum.inr (.inputBroadcastCall j x)) ∨
    (∃ k j v, l = Sum.inr (.inputBroadcastRet k j v)) ∨ ∃ id, l = Sum.inl (.fail id)}
  outputLabels := {l | (∃ i j m, l = Sum.inr (.deliver i j m)) ∨ ∃ C, l = Sum.inl (.core C)}

/-- The input labels and the output labels of the instance broadcasting `k`'s input, read along
`inputBroadcastLabelMap k`. The outputs are its returns, and the inputs are every other non-silent
label: the call of the instance, corruption, and every label with no image, on which the pullback
idles. -/
def inputBroadcastInputOutputLabels (n : ℕ) (X : Type) (k : Fin n) :
    InputOutputLabels (GatherLabel n X) where
  inputLabels := {l | l ≠ Silent.τ ∧ ∀ j v, l ≠ Sum.inr (.inputBroadcastRet k j v)}
  outputLabels := {l | ∃ j v, l = Sum.inr (.inputBroadcastRet k j v)}

/-! ### Input-enabledness of the gather program and the gather network -/

variable {X : Type} [DecidableEq X]

/-- Process `j`'s gather program is input-enabled. The call is taken on `call` at a program
holding no input and on `callLoop` at a program holding one, and on `callIdle` at another
process. A delivery or a return of an input broadcast is taken by `deliverReceive` or
`inputBroadcastRetReceive` at `j` and by an idle transition elsewhere; a multicast, a call of an
input broadcast or a return at another process by `sendIdle`, `inputBroadcastCallIdle` or
`retIdle`; the announcement of the core by `coreIdle`; corruption by `failIdle`. -/
theorem program_inputEnabled (P : Parameters) (j : Fin P.n) :
    (gatherProgram P j (X := X)).InputEnabled (programInputOutputLabels P.n X j).inputLabels := by
  rintro p l ⟨hτ, hsend, hcall, hret⟩
  rcases l with (_ | ⟨i, x⟩ | ⟨i, g⟩ | C | i) | (⟨i, m⟩ | ⟨i, k, m⟩ | ⟨i, x⟩ | ⟨k, i, v⟩)
  · exact absurd rfl hτ
  · by_cases hi : i = j
    · subst hi
      by_cases hin : p.processVariables.input = none
      · exact ⟨_, ProgramStep.call p x hin⟩
      · exact ⟨_, ProgramStep.callLoop p x hin⟩
    · exact ⟨_, ProgramStep.callIdle p i x hi⟩
  · have hi : i ≠ j := by
      rintro rfl
      exact hret g rfl
    exact ⟨_, ProgramStep.retIdle p i g hi⟩
  · exact ⟨_, ProgramStep.coreIdle p C⟩
  · exact ⟨_, ProgramStep.failIdle p i⟩
  · have hi : i ≠ j := by
      rintro rfl
      exact hsend m rfl
    exact ⟨_, ProgramStep.sendIdle p i m hi⟩
  · by_cases hi : i = j
    · subst hi
      exact ⟨_, ProgramStep.deliverReceive p k m⟩
    · exact ⟨_, ProgramStep.deliverIdle p i k m hi⟩
  · have hi : i ≠ j := by
      rintro rfl
      exact hcall x rfl
    exact ⟨_, ProgramStep.inputBroadcastCallIdle p i x hi⟩
  · by_cases hi : i = j
    · subst hi
      exact ⟨_, ProgramStep.inputBroadcastRetReceive p k v⟩
    · exact ⟨_, ProgramStep.inputBroadcastRetIdle p k i v hi⟩

/-- The gather network is input-enabled: it takes a call, a multicast, a return, a call and a
return of an input broadcast, and corruption, each on one unguarded transition. -/
theorem network_inputEnabled (P : Parameters) :
    (gatherNetwork P X).InputEnabled (networkInputOutputLabels P.n X).inputLabels := by
  rintro w l (⟨id, x, rfl⟩ | ⟨j, m, rfl⟩ | ⟨id, g, rfl⟩ | ⟨j, x, rfl⟩ | ⟨k, j, v, rfl⟩ |
    ⟨id, rfl⟩)
  · exact ⟨_, NetworkStep.call w id x⟩
  · exact ⟨_, NetworkStep.send w j m⟩
  · exact ⟨_, NetworkStep.ret w id g⟩
  · exact ⟨_, NetworkStep.inputBroadcastCallIdle w j x⟩
  · exact ⟨_, NetworkStep.inputBroadcastRetIdle w k j v⟩
  · exact ⟨_, NetworkStep.fail w id⟩

/-! ### Input-enabledness of the input broadcasts -/

omit [DecidableEq X] in
/-- A broadcast instance input-enabled on the inputs of the BRB specification, read along
`inputBroadcastLabelMap k`, is input-enabled on every non-silent label outside its returns. The
call of the instance is the image of `inputBroadcastCall k _`, corruption is its own image, and
every other label has no image and is taken by the pullback's idle transition. -/
theorem inputBroadcast_inputEnabled (P : Parameters) {S : Type} {B : System S (BRB.Label P.n X)}
    (hB : B.InputEnabled (BRB.specInstInputOutputLabels P.n X).inputLabels) (k : Fin P.n) :
    (B.mapIdle (inputBroadcastLabelMap P.n X k)).InputEnabled
      (inputBroadcastInputOutputLabels P.n X k).inputLabels := by
  refine (hB.mapIdle (inputBroadcastLabelMap P.n X k)).mono ?_
  rintro l ⟨hτ, hret⟩
  rcases l with (_ | ⟨i, x⟩ | ⟨i, g⟩ | C | i) | (⟨i, m⟩ | ⟨i, j, m⟩ | ⟨j, x⟩ | ⟨k', j, v⟩)
  · exact absurd rfl hτ
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨.fail i, Or.inr ⟨i, rfl⟩, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · by_cases hkj : k = j
    · exact Or.inr ⟨.call x, Or.inl ⟨x, rfl⟩, by simp [inputBroadcastLabelMap, hkj]⟩
    · exact Or.inl (by simp [inputBroadcastLabelMap, hkj])
  · by_cases hkk : k = k'
    · subst hkk
      exact absurd rfl (hret j v)
    · exact Or.inl (by simp [inputBroadcastLabelMap, hkk])

/-- The input broadcasts of the gather instance over Bracha's broadcast are input-enabled. -/
theorem instanceOverBracha_inputBroadcast_inputEnabled (P : Parameters) (k : Fin P.n) :
    ((BRB.brachaInstance P k X).mapIdle (inputBroadcastLabelMap P.n X k)).InputEnabled
      (inputBroadcastInputOutputLabels P.n X k).inputLabels :=
  inputBroadcast_inputEnabled P (BRB.brachaInstance_inputEnabled P k) k

omit [DecidableEq X] in
/-- The input broadcasts of the gather instance over the broadcast specification are
input-enabled. -/
theorem instanceOverBroadcastSpecification_inputBroadcast_inputEnabled (P : Parameters)
    (k : Fin P.n) :
    ((BRB.specInst P k X).mapIdle (inputBroadcastLabelMap P.n X k)).InputEnabled
      (inputBroadcastInputOutputLabels P.n X k).inputLabels :=
  inputBroadcast_inputEnabled P (BRB.specInst_inputEnabled P k) k

/-! ### Compatibility -/

omit [DecidableEq X] in
/-- The outputs of the `n` gather programs, the gather network and the `n` input broadcasts are
pairwise disjoint (the simulations paper, Definition 2). The outputs of process `j`'s program name
`j` as the sender, the caller or the returner, the network outputs only deliveries and
announcements of the core, and the outputs of input broadcast `k` are returns that name `k` as the
broadcasting instance. -/
theorem instanceOverBroadcastsExtended_compatible (n : ℕ) (X : Type) :
    Pairwise (fun i j : Fin n =>
      (programInputOutputLabels n X i).Compatible (programInputOutputLabels n X j)) ∧
    (∀ j : Fin n, (programInputOutputLabels n X j).Compatible (networkInputOutputLabels n X)) ∧
    (∀ j k : Fin n,
      (programInputOutputLabels n X j).Compatible (inputBroadcastInputOutputLabels n X k)) ∧
    (∀ k : Fin n,
      (networkInputOutputLabels n X).Compatible (inputBroadcastInputOutputLabels n X k)) ∧
    Pairwise (fun k k' : Fin n =>
      (inputBroadcastInputOutputLabels n X k).Compatible
        (inputBroadcastInputOutputLabels n X k')) := by
  refine ⟨fun i j hij => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_,
    fun j k => Set.disjoint_left.mpr ?_, fun k => Set.disjoint_left.mpr ?_,
    fun k k' hkk => Set.disjoint_left.mpr ?_⟩
  · rintro l (⟨m, rfl⟩ | ⟨x, rfl⟩ | ⟨g, rfl⟩) (⟨m', h⟩ | ⟨x', h⟩ | ⟨g', h⟩) <;> simp_all
  · rintro l (⟨m, rfl⟩ | ⟨x, rfl⟩ | ⟨g, rfl⟩) (⟨i, k, m', h⟩ | ⟨C, h⟩) <;> simp at h
  · rintro l (⟨m, rfl⟩ | ⟨x, rfl⟩ | ⟨g, rfl⟩) ⟨i, v, h⟩ <;> simp at h
  · rintro l (⟨i, j, m, rfl⟩ | ⟨C, rfl⟩) ⟨i', v, h⟩ <;> simp at h
  · rintro l ⟨j, v, rfl⟩ ⟨j', v', h⟩
    simp_all

end Gather
end ABA
end PLTS
