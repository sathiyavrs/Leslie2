/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.AlgorithmOverGatherSpecifications
import Leslie2Protocols.ABA.Gather.AlgorithmOverBracha
import Leslie2Protocols.ABA.Gather.AlgorithmOverBroadcastSpecification
import Leslie2Protocols.Framework.InputEnabledness

/-!
# The inputs and the outputs of the components of the graded-agreement round

The input labels and the output labels of the `n` round programs, the round's network and the two
gather instances that `GBCA.ByAFW.roundOverGathersExtended` places in parallel
(`ABA/GBCA/AFW/Components.lean`, `ABA/GBCA/AFW/Composition.lean`), over the round-internal
alphabet `RoundLabel n`, and those of the round itself over the family alphabet.

* Process `j`'s program, read along `programLabelMap`, outputs its call of the second gather
  `secondGatherCall j _` and its return `retG r j _`. Its inputs are the round's call and a
  corrupted process's call, the first gather's return and its announcement, the second gather's
  return, the announcement of the bound bit, corruption, and the outputs of another process
  (`programInputOutputLabels`).
* The round's network, read along `programLabelMap`, outputs the announcement `boundG r _`. Its
  inputs are the calls, the four events, the returns and corruption (`networkInputOutputLabels`).
* The first gather, read along `firstGatherLabelMap`, outputs its returns `firstGatherReturn` and
  its announcement `firstGatherCore`. Its inputs are the calls `callG r _ _` and
  `byzantineCallG r _ _`, and corruption (`firstGatherInputOutputLabels`).
* The second gather, read along `secondGatherLabelMap`, outputs its returns `secondGatherReturn`.
  Its inputs are the calls `secondGatherCall` and corruption (`secondGatherInputOutputLabels`).
* The round outputs its returns `retG r _ _` and the announcement `boundG r _`. Its inputs are the
  labels the family of rounds assigns to it, `callG r _ _` and `byzantineCallG r _ _`, and
  corruption, the family's broadcast (`roundInputOutputLabels`).

`roundProgram_inputEnabled` and `roundNetwork_inputEnabled` give the program and the network a
transition on every input at every state. The program of `id` takes the call on `callG` at a
program holding no input and on `callLoop` at one holding one; a gather's return on the
transition its guards admit or on the loop beside it; the announcements on `firstGatherCoreIdle`
and `boundGIdle`; every label at another process on an idle transition; and corruption, which has
no image, on the pullback's idle. The network takes each of its inputs on one unguarded
transition.

`firstGather_inputEnabled` and `secondGather_inputEnabled` carry the input-enabledness of a
gather instance on the inputs of the gather specification, the call and corruption, along the
pullback (`System.InputEnabled.mapIdle`). `Gather.specInst_inputEnabled` supplies the hypothesis
for the gather specification, and `gatherInstanceOverBracha_inputEnabled` and
`gatherInstanceOverBroadcastSpecification_inputEnabled` for the gather instance over Bracha's
broadcast and over the broadcast specification, whose programs take the call on
`Gather.AlgorithmOverBracha.call` or `Gather.AlgorithmOverBracha.callLoop`.
`roundOverGathers_inputEnabled` is the round over any two such gather instances, and
`roundOverGatherSpecifications_inputEnabled`, `roundOverBroadcastSpecification_inputEnabled` and
`roundOverBracha_inputEnabled` are the three compositions.

`roundOverGathersExtended_compatible` states that the outputs of the `n` programs, the network and
the two gathers are pairwise disjoint (the simulations paper, Definition 2): the outputs of the
program of `j` name `j` as the caller or the returner, and the other three components output
labels of distinct constructors.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The label sets -/

/-- The input labels and the output labels of process `j`'s program in round `r`, read along
`programLabelMap`. The outputs are `j`'s call of the second gather and `j`'s return; the inputs are
the calls, the first gather's return and announcement, the second gather's return, the
announcement of the bound bit, corruption, and the outputs of another process. -/
def programInputOutputLabels (n r : ℕ) (j : Fin n) : InputOutputLabels (RoundLabel n) where
  inputLabels := {l | (∃ id b, l = Sum.inl (Sum.inl (.callG r id b))) ∨
    (∃ k b, l = Sum.inl (Sum.inr (.byzantineCallG r k b))) ∨
    (∃ id g, l = Sum.inr (.firstGatherReturn id g)) ∨ (∃ C, l = Sum.inr (.firstGatherCore C)) ∨
    (∃ i x, i ≠ j ∧ l = Sum.inr (.secondGatherCall i x)) ∨
    (∃ id g, l = Sum.inr (.secondGatherReturn id g)) ∨
    (∃ i out, i ≠ j ∧ l = Sum.inl (Sum.inl (.retG r i out))) ∨
    (∃ b, l = Sum.inl (Sum.inl (.boundG r b))) ∨ ∃ id, l = Sum.inl (Sum.inl (.fail id))}
  outputLabels := {l | (∃ x, l = Sum.inr (.secondGatherCall j x)) ∨
    ∃ out, l = Sum.inl (Sum.inl (.retG r j out))}

/-- The input labels and the output labels of the round's network in round `r`, read along
`programLabelMap`. The output is the announcement of the bound bit; the inputs are the calls, the
four events, the returns and corruption. -/
def networkInputOutputLabels (n r : ℕ) : InputOutputLabels (RoundLabel n) where
  inputLabels := {l | (∃ id b, l = Sum.inl (Sum.inl (.callG r id b))) ∨
    (∃ k b, l = Sum.inl (Sum.inr (.byzantineCallG r k b))) ∨
    (∃ id g, l = Sum.inr (.firstGatherReturn id g)) ∨ (∃ C, l = Sum.inr (.firstGatherCore C)) ∨
    (∃ id x, l = Sum.inr (.secondGatherCall id x)) ∨
    (∃ id g, l = Sum.inr (.secondGatherReturn id g)) ∨
    (∃ id out, l = Sum.inl (Sum.inl (.retG r id out))) ∨ ∃ id, l = Sum.inl (Sum.inl (.fail id))}
  outputLabels := {l | ∃ b, l = Sum.inl (Sum.inl (.boundG r b))}

/-- The input labels and the output labels of the first gather in round `r`, read along
`firstGatherLabelMap`. The outputs are its returns and its announcement; the inputs are the
round's call, a corrupted process's call and corruption. -/
def firstGatherInputOutputLabels (n r : ℕ) : InputOutputLabels (RoundLabel n) where
  inputLabels := {l | (∃ id b, l = Sum.inl (Sum.inl (.callG r id b))) ∨
    (∃ k b, l = Sum.inl (Sum.inr (.byzantineCallG r k b))) ∨
    ∃ id, l = Sum.inl (Sum.inl (.fail id))}
  outputLabels := {l | (∃ id g, l = Sum.inr (.firstGatherReturn id g)) ∨
    ∃ C, l = Sum.inr (.firstGatherCore C)}

/-- The input labels and the output labels of the second gather, read along
`secondGatherLabelMap`. The outputs are its returns; the inputs are its calls and corruption. -/
def secondGatherInputOutputLabels (n : ℕ) : InputOutputLabels (RoundLabel n) where
  inputLabels := {l | (∃ id x, l = Sum.inr (.secondGatherCall id x)) ∨
    ∃ id, l = Sum.inl (Sum.inl (.fail id))}
  outputLabels := {l | ∃ id g, l = Sum.inr (.secondGatherReturn id g)}

/-- The input labels and the output labels of the round `r` over the family alphabet. The outputs
are its returns and the announcement of its bound bit; the inputs are the labels the family of
rounds assigns to it, the round's call and a corrupted process's call, and corruption. -/
def roundInputOutputLabels (n r : ℕ) : InputOutputLabels (ExtendedLabel n Empty) where
  inputLabels := {l | (∃ id b, l = Sum.inl (.callG r id b)) ∨
    (∃ k b, l = Sum.inr (.byzantineCallG r k b)) ∨ ∃ id, l = Sum.inl (.fail id)}
  outputLabels := {l | (∃ id out, l = Sum.inl (.retG r id out)) ∨ ∃ b, l = Sum.inl (.boundG r b)}

/-! ### Input-enabledness of the program and the network -/

section Components
variable (P : Parameters) (r : ℕ)

/-- Process `j`'s program takes the round's call at every state: on `callG` where it holds no
input, on `callLoop` where it holds one, and on `callGIdle` at another process. -/
theorem programStep_callG_enabled (j : Fin P.n) (p : ProcessVariables P.n) (id : Fin P.n)
    (b : Bool) : ∃ ν, ProgramStep P r j p (.callG r id b) ν := by
  by_cases hi : id = j
  · subst hi
    by_cases hin : p.input = none
    · exact ⟨_, ProgramStep.callG p b hin⟩
    · exact ⟨_, ProgramStep.callLoop p b hin⟩
  · exact ⟨_, ProgramStep.callGIdle p id b hi⟩

/-- Every program takes the round's call together: the caller's program records the input or
loops, and every other program idles. -/
theorem programStep_callG_exists (u : ∀ _ : Fin P.n, ProcessVariables P.n) (id : Fin P.n)
    (b : Bool) : ∃ x : ∀ _ : Fin P.n, ProcessVariables P.n,
      ∀ i, ProgramStep P r i (u i) (.callG r id b) (PMF.pure (x i)) := by
  by_cases hin : (u id).input = none
  · exact ⟨_, dirac_steps_update (ProgramStep.callG (u id) b hin)
      (fun i hi => ProgramStep.callGIdle (u i) id b (Ne.symm hi))⟩
  · refine ⟨u, fun i => ?_⟩
    by_cases hi : i = id
    · subst hi
      exact ProgramStep.callLoop (u i) b hin
    · exact ProgramStep.callGIdle (u i) id b (Ne.symm hi)

/-- **Process `j`'s program is input-enabled.** The call is taken on `callG` or `callLoop`, a
gather's return to `j` on the transition its guards admit or on the loop beside it, the two
announcements on `firstGatherCoreIdle` and `boundGIdle`, every label at another process on an
idle transition, and corruption, which has no image, on the pullback's idle. -/
theorem roundProgram_inputEnabled (j : Fin P.n) :
    ((gbcaProgram P r j).mapIdle (programLabelMap P.n)).InputEnabled
      (programInputOutputLabels P.n r j).inputLabels := by
  have hsome : ∀ {l : RoundLabel P.n} {lp : ProgramLabel P.n} (p : ProcessVariables P.n),
      programLabelMap P.n l = some lp → (∃ ν, ProgramStep P r j p lp ν) →
        ∃ μ, ((gbcaProgram P r j).mapIdle (programLabelMap P.n)).step p l μ := by
    rintro l lp p hl ⟨ν, hν⟩
    exact ⟨ν, (System.mapIdle_step_some hl ν).mpr hν⟩
  rintro p l (⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨id, g, rfl⟩ | ⟨C, rfl⟩ | ⟨i, x, hi, rfl⟩ |
    ⟨id, g, rfl⟩ | ⟨i, out, hi, rfl⟩ | ⟨b, rfl⟩ | ⟨id, rfl⟩)
  · exact hsome p (programLabelMap_callG r id b) (programStep_callG_enabled P r j p id b)
  · exact hsome p (programLabelMap_byzantineCallG r k b) (programStep_callG_enabled P r j p k b)
  · refine hsome p (programLabelMap_firstGatherReturn id g) ?_
    by_cases hi : id = j
    · subst hi
      by_cases hg : p.input ≠ none ∧ p.candidate = none
      · exact ⟨_, ProgramStep.firstGatherReturn p g hg.1 hg.2⟩
      · exact ⟨_, ProgramStep.firstGatherReturnLoop p g hg⟩
    · exact ⟨_, ProgramStep.firstGatherReturnIdle p id g hi⟩
  · exact hsome p (programLabelMap_firstGatherCore C) ⟨_, ProgramStep.firstGatherCoreIdle p C⟩
  · exact hsome p (programLabelMap_secondGatherCall i x)
      ⟨_, ProgramStep.secondGatherCallIdle p i x hi⟩
  · refine hsome p (programLabelMap_secondGatherReturn id g) ?_
    by_cases hi : id = j
    · subst hi
      by_cases hg : p.secondGatherCalled = true ∧ p.output = none
      · exact ⟨_, ProgramStep.secondGatherReturn p g hg.1 hg.2⟩
      · exact ⟨_, ProgramStep.secondGatherReturnLoop p g hg⟩
    · exact ⟨_, ProgramStep.secondGatherReturnIdle p id g hi⟩
  · exact hsome p (programLabelMap_retG r i out) ⟨_, ProgramStep.retGIdle p i out hi⟩
  · exact hsome p (programLabelMap_boundG r b) ⟨_, ProgramStep.boundGIdle p b⟩
  · exact ⟨PMF.pure p, (System.mapIdle_step_none (programLabelMap_fail id) _).mpr rfl⟩

/-- **The round's network is input-enabled**: it takes each of its inputs on one unguarded
transition, and corruption, which has no image, on the pullback's idle. -/
theorem roundNetwork_inputEnabled :
    ((GBCANetwork P r).mapIdle (programLabelMap P.n)).InputEnabled
      (networkInputOutputLabels P.n r).inputLabels := by
  rintro w l (⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨id, g, rfl⟩ | ⟨C, rfl⟩ | ⟨id, x, rfl⟩ |
    ⟨id, g, rfl⟩ | ⟨id, out, rfl⟩ | ⟨id, rfl⟩)
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_callG r id b) _).mpr
      (NetworkStep.callG w id b)⟩
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_byzantineCallG r k b) _).mpr
      (NetworkStep.callG w k b)⟩
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_firstGatherReturn id g) _).mpr
      (NetworkStep.firstGatherReturn w id g)⟩
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_firstGatherCore C) _).mpr
      (NetworkStep.firstGatherCore w C)⟩
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_secondGatherCall id x) _).mpr
      (NetworkStep.secondGatherCall w id x)⟩
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_secondGatherReturn id g) _).mpr
      (NetworkStep.secondGatherReturn w id g)⟩
  · exact ⟨_, (System.mapIdle_step_some (programLabelMap_retG r id out) _).mpr
      (NetworkStep.retG w id out)⟩
  · exact ⟨PMF.pure w, (System.mapIdle_step_none (programLabelMap_fail id) _).mpr rfl⟩

end Components

/-! ### Input-enabledness of the two gathers -/

/-- A gather instance input-enabled on the inputs of the gather specification, read along
`firstGatherLabelMap`, is input-enabled on the round's call, a corrupted process's call and
corruption: the first two are the gather's call, the third its corruption. -/
theorem firstGather_inputEnabled (P : Parameters) (r : ℕ) {G₁ : Type}
    {firstGather : System G₁ (Gather.Label P.n Bool)}
    (h : firstGather.InputEnabled (Gather.specInstInputOutputLabels P.n Bool).inputLabels) :
    (firstGather.mapIdle (firstGatherLabelMap P.n)).InputEnabled
      (firstGatherInputOutputLabels P.n r).inputLabels := by
  refine (h.mapIdle (firstGatherLabelMap P.n)).mono ?_
  rintro l (⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨id, rfl⟩)
  · exact Or.inr ⟨.call id b, Or.inl ⟨id, b, rfl⟩, rfl⟩
  · exact Or.inr ⟨.call k b, Or.inl ⟨k, b, rfl⟩, rfl⟩
  · exact Or.inr ⟨.fail id, Or.inr ⟨id, rfl⟩, rfl⟩

/-- A gather instance input-enabled on the inputs of the gather specification, read along
`secondGatherLabelMap`, is input-enabled on the round's `secondGatherCall` events and on
corruption. -/
theorem secondGather_inputEnabled (P : Parameters) {G₂ : Type}
    {secondGather : System G₂ (Gather.Label P.n (Option Bool))}
    (h : secondGather.InputEnabled
      (Gather.specInstInputOutputLabels P.n (Option Bool)).inputLabels) :
    (secondGather.mapIdle (secondGatherLabelMap P.n)).InputEnabled
      (secondGatherInputOutputLabels P.n).inputLabels := by
  refine (h.mapIdle (secondGatherLabelMap P.n)).mono ?_
  rintro l (⟨id, x, rfl⟩ | ⟨id, rfl⟩)
  · exact Or.inr ⟨.call id x, Or.inl ⟨id, x, rfl⟩, rfl⟩
  · exact Or.inr ⟨.fail id, Or.inr ⟨id, rfl⟩, rfl⟩

/-- The gather instance over Bracha's broadcast is input-enabled on the inputs of the gather
specification: a program holding no input takes the call on `Gather.AlgorithmOverBracha.call`, one
holding an input on `Gather.AlgorithmOverBracha.callLoop`, and corruption is taken on
`Gather.AlgorithmOverBracha.fail`. -/
theorem gatherInstanceOverBracha_inputEnabled (P : Parameters) (X : Type) [DecidableEq X] :
    (Gather.instanceOverBracha P X).InputEnabled
      (Gather.specInstInputOutputLabels P.n X).inputLabels := by
  rintro s l (⟨id, x, rfl⟩ | ⟨id, rfl⟩)
  · by_cases hin : ((Gather.gatherProgramsAndNetwork s).processVariables id).input = none
    · exact ⟨_, (Gather.instanceOverBracha_step_iff_algorithm P s _ _).mpr
        (Gather.AlgorithmOverBracha.call s id x hin)⟩
    · exact ⟨_, (Gather.instanceOverBracha_step_iff_algorithm P s _ _).mpr
        (Gather.AlgorithmOverBracha.callLoop s id x hin)⟩
  · exact ⟨_, (Gather.instanceOverBracha_step_iff_algorithm P s _ _).mpr
      (Gather.AlgorithmOverBracha.fail s id)⟩

/-- The gather instance over the broadcast specification is input-enabled on the inputs of the
gather specification, by the same three transitions. -/
theorem gatherInstanceOverBroadcastSpecification_inputEnabled (P : Parameters) (X : Type)
    [DecidableEq X] :
    (Gather.instanceOverBroadcastSpecification P X).InputEnabled
      (Gather.specInstInputOutputLabels P.n X).inputLabels := by
  rintro s l (⟨id, x, rfl⟩ | ⟨id, rfl⟩)
  · by_cases hin : ((Gather.gatherProgramsAndNetwork s).processVariables id).input = none
    · exact ⟨_, (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P s _ _).mpr
        (Gather.AlgorithmOverBroadcastSpecification.call s id x hin)⟩
    · exact ⟨_, (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P s _ _).mpr
        (Gather.AlgorithmOverBroadcastSpecification.callLoop s id x hin)⟩
  · exact ⟨_, (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P s _ _).mpr
      (Gather.AlgorithmOverBroadcastSpecification.fail s id)⟩

/-! ### Input-enabledness of the round -/

/-- **The round over two gather instances is input-enabled** on the labels the family assigns to
it and on corruption, when the two gather instances are input-enabled on the inputs of the gather
specification. A call moves the caller's program on its call or its loop, every other program on
its idle, the network on its call, the first gather on its call, and the second gather on the
pullback's idle; corruption moves the two gathers alone. -/
theorem roundOverGathers_inputEnabled (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    {firstGather : System G₁ (Gather.Label P.n Bool)}
    {secondGather : System G₂ (Gather.Label P.n (Option Bool))}
    (hLTS₁ : firstGather.IsLTS) (hLTS₂ : secondGather.IsLTS)
    (h₁ : firstGather.InputEnabled (Gather.specInstInputOutputLabels P.n Bool).inputLabels)
    (h₂ : secondGather.InputEnabled
      (Gather.specInstInputOutputLabels P.n (Option Bool)).inputLabels) :
    (roundOverGathers P r firstGather secondGather).InputEnabled
      (roundInputOutputLabels P.n r).inputLabels := by
  have hcall : ∀ (s : RoundStateOverGathers P.n G₁ G₂) (l : ExtendedLabel P.n Empty)
      (id : Fin P.n) (b : Bool), GBCA.specificationLabelMap P.n l = some (.callG r id b) →
        ∃ μ, (roundOverGathers P r firstGather secondGather).step s l μ := by
    rintro ⟨⟨u, v⟩, c, d⟩ l id b hl
    obtain ⟨hp, hf1, hf2, hlτ⟩ := callLabel_maps hl
    obtain ⟨x, hx⟩ := programStep_callG_exists P r u id b
    obtain ⟨μ₁, hμ₁⟩ := h₁ c (.call id b) (Or.inl ⟨id, b, rfl⟩)
    obtain ⟨c', rfl⟩ := hLTS₁ _ _ _ hμ₁
    exact ⟨_, roundOverGathers_label_step hlτ
      (roundPrograms_label_step hp (by simp) hx (NetworkStep.callG v id b))
      (System.mapIdle_step_of_step hf1 hμ₁) (System.mapIdle_unchanged hf2)⟩
  rintro s l (⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨id, rfl⟩)
  · exact hcall s _ id b rfl
  · exact hcall s _ k b rfl
  · obtain ⟨⟨u, v⟩, c, d⟩ := s
    obtain ⟨μ₁, hμ₁⟩ := h₁ c (.fail id) (Or.inr ⟨id, rfl⟩)
    obtain ⟨c', rfl⟩ := hLTS₁ _ _ _ hμ₁
    obtain ⟨μ₂, hμ₂⟩ := h₂ d (.fail id) (Or.inr ⟨id, rfl⟩)
    obtain ⟨d', rfl⟩ := hLTS₂ _ _ _ hμ₂
    exact ⟨_, roundOverGathers_label_step (by simp) (roundPrograms_idle_step (by simp))
      (System.mapIdle_step_of_step (by simp) hμ₁) (System.mapIdle_step_of_step (by simp) hμ₂)⟩

/-- The round over the gather specifications is input-enabled. -/
theorem roundOverGatherSpecifications_inputEnabled (P : Parameters) (r : ℕ) :
    (roundOverGatherSpecifications P r).InputEnabled (roundInputOutputLabels P.n r).inputLabels :=
  roundOverGathers_inputEnabled P r (Gather.specInst_isLTS P) (Gather.specInst_isLTS P)
    (Gather.specInst_inputEnabled P) (Gather.specInst_inputEnabled P)

/-- The round over the gather instances over the broadcast specification is input-enabled. -/
theorem roundOverBroadcastSpecification_inputEnabled (P : Parameters) (r : ℕ) :
    (roundOverBroadcastSpecification P r).InputEnabled
      (roundInputOutputLabels P.n r).inputLabels :=
  roundOverGathers_inputEnabled P r (Gather.instanceOverBroadcastSpecification_isLTS P)
    (Gather.instanceOverBroadcastSpecification_isLTS P)
    (gatherInstanceOverBroadcastSpecification_inputEnabled P Bool)
    (gatherInstanceOverBroadcastSpecification_inputEnabled P (Option Bool))

/-- The round over the gather instances over Bracha's broadcast is input-enabled. -/
theorem roundOverBracha_inputEnabled (P : Parameters) (r : ℕ) :
    (roundOverBracha P r).InputEnabled (roundInputOutputLabels P.n r).inputLabels :=
  roundOverGathers_inputEnabled P r (Gather.instanceOverBracha_isLTS P)
    (Gather.instanceOverBracha_isLTS P) (gatherInstanceOverBracha_inputEnabled P Bool)
    (gatherInstanceOverBracha_inputEnabled P (Option Bool))

/-! ### Compatibility -/

/-- **The components of the round are compatible**: the outputs of the `n` programs, the round's
network and the two gathers are pairwise disjoint (the simulations paper, Definition 2). The
outputs of process `j`'s program name `j` as the caller of the second gather or as the returner,
the network outputs only the announcement of the bound bit, the first gather only its returns and
its announcement, and the second gather only its returns. -/
theorem roundOverGathersExtended_compatible (n r : ℕ) :
    Pairwise (fun i j : Fin n =>
      (programInputOutputLabels n r i).Compatible (programInputOutputLabels n r j)) ∧
    (∀ j : Fin n, (programInputOutputLabels n r j).Compatible (networkInputOutputLabels n r)) ∧
    (∀ j : Fin n,
      (programInputOutputLabels n r j).Compatible (firstGatherInputOutputLabels n r)) ∧
    (∀ j : Fin n, (programInputOutputLabels n r j).Compatible (secondGatherInputOutputLabels n)) ∧
    (networkInputOutputLabels n r).Compatible (firstGatherInputOutputLabels n r) ∧
    (networkInputOutputLabels n r).Compatible (secondGatherInputOutputLabels n) ∧
    (firstGatherInputOutputLabels n r).Compatible (secondGatherInputOutputLabels n) := by
  refine ⟨fun i j hij => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_,
    fun j => Set.disjoint_left.mpr ?_, fun j => Set.disjoint_left.mpr ?_,
    Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · rintro l (⟨x, rfl⟩ | ⟨out, rfl⟩) (⟨x', h⟩ | ⟨out', h⟩) <;> simp_all
  · rintro l (⟨x, rfl⟩ | ⟨out, rfl⟩) ⟨b, h⟩ <;> simp at h
  · rintro l (⟨x, rfl⟩ | ⟨out, rfl⟩) (⟨id, g, h⟩ | ⟨C, h⟩) <;> simp at h
  · rintro l (⟨x, rfl⟩ | ⟨out, rfl⟩) ⟨id, g, h⟩ <;> simp at h
  · rintro l ⟨b, rfl⟩ (⟨id, g, h⟩ | ⟨C, h⟩) <;> simp at h
  · rintro l ⟨b, rfl⟩ ⟨id, g, h⟩
    simp at h
  · rintro l (⟨id, g, rfl⟩ | ⟨C, rfl⟩) ⟨id', g', h⟩ <;> simp at h

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverGatherSpecifications_inputEnabled' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms roundOverGatherSpecifications_inputEnabled

end GBCA.ByAFW
end ABA
end PLTS
