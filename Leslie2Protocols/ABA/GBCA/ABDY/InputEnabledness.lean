/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.InputEnabledness
import Leslie2Protocols.ABA.GBCA.ABDY.Composition

/-!
# The inputs and the outputs of the round's graded-agreement instance

The input labels and the output labels of the `n` programs and the network of round `r`
(`ABA/GBCA/ABDY/Components.lean`), over the instance-internal alphabet `GBCALabel n`, and of the
round's composition and the round-indexed family over the round's alphabet
`ExtendedLabel n Message`. A component takes as inputs the labels of the round's interface and of
the two synchronisations outside its outputs: a round's instance has no transition at the labels of
another round, and the family idles there.

* The program of process `j` outputs its sends `send j _` and its returns `retG r j _`. Its inputs
  are the calls `callG r _ _`, a corrupted process's calls `byzantineCallG r _ _`, the
  announcements `boundG r _`, the deliveries, and the sends and returns of another process
  (`gbcaProgramInputOutputLabels`).
* The round's network outputs the deliveries and the announcements `boundG r _`, and its injection
  `byzantineGBCA` is silent. Its inputs are the sends, the calls, a corrupted process's calls and
  the returns (`gbcaNetworkInputOutputLabels`).
* The composition hides the two synchronisations. Its inputs are the calls `callG r _ _` and a
  corrupted process's calls `byzantineCallG r _ _`, the labels `roundOwnsLabel` assigns to round
  `r` that no component of the round outputs, and its outputs are the returns and the
  announcements (`compositionInputOutputLabels`).

`gbcaProgram_inputEnabled` and `gbcaNetwork_inputEnabled` give each component a transition on every
input at every state. A program takes its own call on `call` at variables holding no input and on
`callLoop` at variables holding one, and a corrupted process's call on `byzantineCall` and
`byzantineCallLoop` likewise; a delivery to `j` on `deliverReceive`; the announcement on
`boundGIdle`; every label at another process on an idle transition. The network takes each of its
inputs on one unguarded transition, the return on `retG`, which writes the round's bound bit.

`compositionExtended_compatible` states that the outputs of the `n` programs and the network are
pairwise disjoint (the simulations paper, Definition 2). `compositionExtended_inputEnabled` follows
from the two component theorems by `System.InputEnabled.synchronisedProduct_visible` and
`System.InputEnabled.parallel`, and `composition_inputEnabled` reads it through the hiding of the
two synchronisations. `gbcaInstanceFamily_inputEnabled` is the input-enabledness of the
round-indexed family on the inputs of `Composition.roundFamilyInputOutputLabels`
(`System.InputEnabled.family`): a call of round `r` is taken by the round-`r` instance, a
corruption by the broadcast, and every other label no round owns by the family's idle transition.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The label sets -/

/-- The input labels and the output labels of the program of process `j` in round `r`. The outputs
are `j`'s sends and returns. The inputs are the calls and a corrupted process's calls of round `r`,
the announcements of round `r`, the deliveries, and the sends and returns of another process. -/
def gbcaProgramInputOutputLabels (P : Parameters) (r : ℕ) (j : Fin P.n) :
    InputOutputLabels (GBCALabel P.n) where
  inputLabels := {l | (∃ id b, l = Sum.inl (Sum.inl (.callG r id b))) ∨
    (∃ k b, l = Sum.inl (Sum.inr (.byzantineCallG r k b))) ∨
    (∃ b, l = Sum.inl (Sum.inl (.boundG r b))) ∨
    (∃ id out, id ≠ j ∧ l = Sum.inl (Sum.inl (.retG r id out))) ∨
    (∃ k m, k ≠ j ∧ l = Sum.inr (.send k m)) ∨
    ∃ i k m, l = Sum.inr (.deliver i k m)}
  outputLabels := {l | (∃ m, l = Sum.inr (.send j m)) ∨
    ∃ out, l = Sum.inl (Sum.inl (.retG r j out))}

/-- The input labels and the output labels of the network of round `r`. The outputs are the
deliveries and the announcements of round `r`. The inputs are the sends, and the calls, a corrupted
process's calls and the returns of round `r`. -/
def gbcaNetworkInputOutputLabels (P : Parameters) (r : ℕ) :
    InputOutputLabels (GBCALabel P.n) where
  inputLabels := {l | (∃ j m, l = Sum.inr (.send j m)) ∨
    (∃ id b, l = Sum.inl (Sum.inl (.callG r id b))) ∨
    (∃ k b, l = Sum.inl (Sum.inr (.byzantineCallG r k b))) ∨
    ∃ id out, l = Sum.inl (Sum.inl (.retG r id out))}
  outputLabels := {l | (∃ i j m, l = Sum.inr (.deliver i j m)) ∨
    ∃ b, l = Sum.inl (Sum.inl (.boundG r b))}

/-- The input labels and the output labels of the round-`r` composition over the round's alphabet.
The inputs are the calls and a corrupted process's calls of round `r`; the outputs are the returns
and the announcements of round `r`. -/
def compositionInputOutputLabels (P : Parameters) (r : ℕ) :
    InputOutputLabels (ExtendedLabel P.n Message) where
  inputLabels := {l | (∃ id b, l = Sum.inl (.callG r id b)) ∨
    ∃ k b, l = Sum.inr (.byzantineCallG r k b)}
  outputLabels := {l | (∃ id out, l = Sum.inl (.retG r id out)) ∨
    ∃ b, l = Sum.inl (.boundG r b)}

/-! ### The two components -/

/-- **The program of `j` is input-enabled.** Its own call and a corrupted process's call at `j`
are taken on the transition its variables admit or on the loop beside it, a delivery to `j` on
`deliverReceive`, the announcement on `boundGIdle`, and every label at another process on an idle
transition. -/
theorem gbcaProgram_inputEnabled (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).InputEnabled (gbcaProgramInputOutputLabels P r j).inputLabels := by
  rintro p l (⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨b, rfl⟩ | ⟨id, out, hid, rfl⟩ | ⟨k, m, hk, rfl⟩ |
    ⟨i, k, m, rfl⟩)
  · by_cases hid : id = j
    · subst hid
      by_cases hin : p.processVariables.input = none
      · exact ⟨_, GBCAProgramStep.call p b hin⟩
      · exact ⟨_, GBCAProgramStep.callLoop p b hin⟩
    · exact ⟨_, GBCAProgramStep.callIdle p id b hid⟩
  · by_cases hk : k = j
    · subst hk
      by_cases hin : p.processVariables.input = none
      · exact ⟨_, GBCAProgramStep.byzantineCall p b hin⟩
      · exact ⟨_, GBCAProgramStep.byzantineCallLoop p b hin⟩
    · exact ⟨_, GBCAProgramStep.byzantineCallIdle p k b hk⟩
  · exact ⟨_, GBCAProgramStep.boundGIdle p b⟩
  · exact ⟨_, GBCAProgramStep.retIdle p id out hid⟩
  · exact ⟨_, GBCAProgramStep.sendIdle p k m hk⟩
  · by_cases hi : i = j
    · subst hi
      exact ⟨_, GBCAProgramStep.deliverReceive p k m⟩
    · exact ⟨_, GBCAProgramStep.deliverIdle p i k m hi⟩

/-- **The round's network is input-enabled**: it takes each of its inputs on one unguarded
transition. -/
theorem gbcaNetwork_inputEnabled (P : Parameters) (r : ℕ) :
    (GBCANetwork P r).InputEnabled (gbcaNetworkInputOutputLabels P r).inputLabels := by
  rintro w l (⟨j, m, rfl⟩ | ⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨id, out, rfl⟩)
  · exact ⟨_, GBCANetworkStep.send w j m⟩
  · exact ⟨_, GBCANetworkStep.callG w id b⟩
  · exact ⟨_, GBCANetworkStep.byzantineCallG w k b⟩
  · exact ⟨_, GBCANetworkStep.retG w id out⟩

/-! ### Compatibility -/

/-- **The components of the round are compatible**: the outputs of the `n` programs and the
network are pairwise disjoint (the simulations paper, Definition 2). The outputs of the program of
`j` name `j` as the sender or the returner, and the programs and the network output labels of
distinct constructors. -/
theorem compositionExtended_compatible (P : Parameters) (r : ℕ) :
    Pairwise (fun i j : Fin P.n =>
      (gbcaProgramInputOutputLabels P r i).Compatible (gbcaProgramInputOutputLabels P r j)) ∧
    ∀ j : Fin P.n,
      (gbcaProgramInputOutputLabels P r j).Compatible (gbcaNetworkInputOutputLabels P r) := by
  refine ⟨fun i j hij => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_⟩
  · rintro l (⟨m, rfl⟩ | ⟨out, rfl⟩) (⟨m', h⟩ | ⟨out', h⟩) <;> simp_all
  · rintro l (⟨m, rfl⟩ | ⟨out, rfl⟩) (⟨_, _, _, h⟩ | ⟨_, h⟩) <;> simp at h

/-! ### The composition -/

/-- The programs beside the network are input-enabled on every visible label that is an input of
every program and of the network. -/
theorem compositionExtended_inputEnabled (P : Parameters) (r : ℕ) :
    (compositionExtended P r).InputEnabled
      (((⋂ j, (gbcaProgramInputOutputLabels P r j).inputLabels) \ {Silent.τ}) ∩
        (gbcaNetworkInputOutputLabels P r).inputLabels) :=
  (System.InputEnabled.synchronisedProduct_visible (gbcaProgram_inputEnabled P r)).parallel
    (gbcaNetwork_inputEnabled P r)

/-- **The round's composition is input-enabled** on its inputs, the calls and a corrupted
process's calls of round `r`. Every program and the network take such a call
(`compositionExtended_inputEnabled`), and the label stays visible through the hiding of the two
synchronisations. -/
theorem composition_inputEnabled (P : Parameters) (r : ℕ) :
    (composition P r).InputEnabled (compositionInputOutputLabels P r).inputLabels := by
  rintro q l hl
  have hext : (Sum.inl l : GBCALabel P.n) ∈
      ((⋂ j, (gbcaProgramInputOutputLabels P r j).inputLabels) \ {Silent.τ}) ∩
        (gbcaNetworkInputOutputLabels P r).inputLabels := by
    rcases hl with ⟨id, b, rfl⟩ | ⟨k, b, rfl⟩
    · exact ⟨⟨Set.mem_iInter.mpr fun _ => Or.inl ⟨id, b, rfl⟩, by simp⟩,
        Or.inr (Or.inl ⟨id, b, rfl⟩)⟩
    · exact ⟨⟨Set.mem_iInter.mpr fun _ => Or.inr (Or.inl ⟨k, b, rfl⟩), by simp⟩,
        Or.inr (Or.inr (Or.inl ⟨k, b, rfl⟩))⟩
  obtain ⟨μ, hμ⟩ := compositionExtended_inputEnabled P r q (Sum.inl l) hext
  exact ⟨μ, (composition_step_iff P r q l μ).mpr (Or.inr hμ)⟩

/-! ### The round-indexed family -/

/-- **The round-indexed family is input-enabled** on the inputs of the round family: every
non-silent label other than a return and an announcement. A call of round `r` and a corrupted
process's call of round `r` are taken by the round-`r` instance (`composition_inputEnabled`),
`fail` by the broadcast, and every other such label by the family's idle transition
(`System.InputEnabled.family`). -/
theorem gbcaInstanceFamily_inputEnabled (P : Parameters) :
    (gbcaInstanceFamily P).InputEnabled (roundFamilyInputOutputLabels P Message).inputLabels := by
  refine (System.InputEnabled.family (composition_inputEnabled P) roundOwnsLabel isFailLabel
    (corruptionAct P) (GBCA.ByABDY.RoundState.initial P.n)).mono ?_
  rintro l ⟨hτ, hret, hbound⟩
  rcases l with (_ | ⟨id, b⟩ | ⟨id, b⟩ | ⟨r, id, b⟩ | ⟨r, id, out⟩ | ⟨r, b⟩ | ⟨r, id⟩ |
      ⟨r, id, co⟩ | id) |
    (⟨r, k, m⟩ | ⟨r, i, k, m⟩ | ⟨k, b⟩ | ⟨k, b⟩ | ⟨i, k, b⟩ | ⟨r, k, e⟩ | ⟨r, k, b⟩ | ⟨r, k⟩)
  · exact absurd rfl hτ
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inr ⟨r, rfl, Or.inl ⟨id, b, rfl⟩⟩
  · exact absurd rfl (hret r id out)
  · exact absurd rfl (hbound r b)
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact e.elim
  · exact Or.inr ⟨r, rfl, Or.inr ⟨k, b, rfl⟩⟩
  · exact Or.inl ⟨hτ, rfl⟩

end GBCA.ByABDY
end ABA
end PLTS
