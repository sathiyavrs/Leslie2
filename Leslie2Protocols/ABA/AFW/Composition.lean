/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.BroadcastSubstitution
import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitution
import Leslie2Protocols.ABA.GBCA.AFW.InputEnabledness
import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.WeakTransitionsFromChains
import Leslie2Protocols.Framework.Congruence

/-!
# The composed systems of the gather-based protocol

`AFW.protocol` (`ABA/AFW/System.lean`) is `n` programs beside one network and the common coin, and
runs AFW25's two-gather construction in each round. `AFW.composed` reads that same protocol as a
composition of four components: the round-indexed family of gather-based graded-agreement rounds,
the `n` round loops, the DECIDED sets beside the corrupted set, and the lifted common coin. The last
three and the pipeline over them (the labels the components synchronise on hidden, the result read
back over `Label n`, the sub-protocol API hidden) are the context term of `ABDY.composed` and of
`hybrid` (`ABA/Composition/Hybrid.lean`), character for character.

The graded-agreement component is taken at three compositions, which differ in what sits beneath a
round's two gather instances: Bracha's broadcast (`roundFamilyOverBracha`), the broadcast
specification (`roundFamilyOverBroadcastSpecification`) and the gather specifications
(`roundFamilyOverGatherSpecifications`). Each is a `System.family` over `InstanceFamilyState`, of
the shape of `gbcaSpecificationFamily`: a label a round owns moves that round alone, in the map or
not; `τ` moves one round of the map; `fail` is the broadcast applied at every round; every other
label idles. The round of a given index is itself a composition, the round's programs and the
round's network beside its two gather instances (`GBCA/AFW/Composition.lean`). Every round starts
from the same state, `initialRoundStateOverBracha` and its two companions, so a round outside the
map reads that state under the recorded corruptions. Each family through the pipeline gives
`AFW.composed`, `composedOverBroadcastSpecification` and `composedOverGatherSpecifications`.

Each family is input-enabled on the inputs of the round family of the composed level,
`roundFamilyInputOutputLabels` (`ABA/Composition/InputEnabledness.lean`): a call and a corrupted
process's call of round `r` are taken by the round of index `r`, which is input-enabled on them
(`GBCA.ByAFW.roundOverBracha_inputEnabled` and its two companions), `fail` by the broadcast, and
every other such label by the family's idle transition (`System.InputEnabled.family`). The three
theorems are `roundFamilyOverBracha_inputEnabled`,
`roundFamilyOverBroadcastSpecification_inputEnabled` and
`roundFamilyOverGatherSpecifications_inputEnabled`.

## The corruption actions

A family carries a broadcast action. The action on a round state corrupts the round's two gather
instances at once and leaves the programs and the round's network as they stand (D1).
`corruptionOverBracha`, `corruptionOverBroadcastSpecification` and
`corruptionOverGatherSpecifications` are `GBCA.ByAFW.corruptAll` over the corruption of that
composition's gather states.

## What this file supplies

The three families, the three composed systems, and the lemmas that read and build their
transitions. `roundFamilyOverBracha_owned`, `roundFamilyOverBracha_owned_id`,
`roundFamilyOverBracha_tau`, `roundFamilyOverBracha_idle` and `roundFamilyOverBracha_fail` place a
transition of one round in the family. `composedExtended_visible_step`,
`composedExtended_tau_overBracha`, `composedExtended_tau_ABANetwork` and `composedExtended_tau_coin`
assemble a transition of the four components out of transitions of each, and
`composedHidden_of_event` and `composedHidden_of_tau` carry one through the two hidings.
`roundFamilyOverBracha_silentRun` and `roundFamilyOverBracha_weakStep` place a run of a round of
the map in the family, `roundFamilyOverBracha_weakStep_of_step` a run of any round that begins
with a transition on a label the round owns, and `composedHidden_weakTau` and
`composedHidden_weakStep` carry a run of the family to the composed group. The protocol meets
`AFW.composed` in `ABA/AFW/Simulation.lean`, along the projection of
`ABA/AFW/RoundProjection.lean`, and `ABA/AFW/Substitution.lean` carries `AFW.composed` to `hybrid`
in three stages.
-/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

namespace AFW

/-! ## The broadcast corruption actions

Corruption reaches a round through its two gather instances. Each gather
instance passes it to its own network state and to every broadcast coordinate
it holds; the round's programs and its network are untouched (D1). -/

/-- The broadcast corruption action on a round over the gather instances over
Bracha's broadcast. -/
def corruptionOverBracha (P : Parameters) :
    ExtendedLabel P.n Empty → GBCA.ByAFW.RoundStateOverBracha P.n →
      GBCA.ByAFW.RoundStateOverBracha P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i))
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption action on a round over the gather instances over the
broadcast specification. -/
def corruptionOverBroadcastSpecification (P : Parameters) :
    ExtendedLabel P.n Empty → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n →
      GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i))
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption action on a round over the gather specifications. -/
def corruptionOverGatherSpecifications (P : Parameters) :
    ExtendedLabel P.n Empty → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n →
      GBCA.ByAFW.RoundStateOverGatherSpecifications P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s
  | _, s => s

/-- The corruption action on a round over the gather specifications leaves the programs as they
stand. -/
theorem programs_corruptionOverGatherSpecifications (P : Parameters) (l : ExtendedLabel P.n Empty)
    (s : GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) :
    GBCA.ByAFW.programs (corruptionOverGatherSpecifications P l s) = GBCA.ByAFW.programs s := by
  cases l with
  | inl l₀ => cases l₀ <;> rfl
  | inr e => rfl

/-! ## The initial state of a round

Every round of a family starts from the same state: every program at its initial variables, the
round's network at its initial state, and the two gather instances at their initial states. -/

/-- The initial state of a round over the gather instances over Bracha's broadcast. -/
noncomputable def initialRoundStateOverBracha (P : Parameters) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  (((fun _ => GBCA.ByAFW.ProcessVariables.initial P.n), GBCA.ByAFW.NetworkState.initial P.n),
    ((Gather.instanceOverBracha P Bool).init, (Gather.instanceOverBracha P (Option Bool)).init))

/-- The initial state of a round over the gather instances over the broadcast specification. -/
noncomputable def initialRoundStateOverBroadcastSpecification (P : Parameters) :
    GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n :=
  (((fun _ => GBCA.ByAFW.ProcessVariables.initial P.n), GBCA.ByAFW.NetworkState.initial P.n),
    ((Gather.instanceOverBroadcastSpecification P Bool).init,
      (Gather.instanceOverBroadcastSpecification P (Option Bool)).init))

/-- The initial state of a round over the gather specifications. -/
def initialRoundStateOverGatherSpecifications (P : Parameters) :
    GBCA.ByAFW.RoundStateOverGatherSpecifications P.n :=
  (((fun _ => GBCA.ByAFW.ProcessVariables.initial P.n), GBCA.ByAFW.NetworkState.initial P.n),
    (Gather.SpecState.initial P.n Bool, Gather.SpecState.initial P.n (Option Bool)))

/-- Every round over Bracha's broadcast starts from `initialRoundStateOverBracha`. -/
theorem roundOverBracha_init_eq (P : Parameters) (r : ℕ) :
    (GBCA.ByAFW.roundOverBracha P r).init = initialRoundStateOverBracha P := rfl

/-- Every round over the broadcast specification starts from
`initialRoundStateOverBroadcastSpecification`. -/
theorem roundOverBroadcastSpecification_init_eq (P : Parameters) (r : ℕ) :
    (GBCA.ByAFW.roundOverBroadcastSpecification P r).init =
      initialRoundStateOverBroadcastSpecification P := rfl

/-- Every round over the gather specifications starts from
`initialRoundStateOverGatherSpecifications`. -/
theorem roundOverGatherSpecifications_init_eq (P : Parameters) (r : ℕ) :
    (GBCA.ByAFW.roundOverGatherSpecifications P r).init =
      initialRoundStateOverGatherSpecifications P := rfl

/-- No program of the initial round state over the gather specifications holds an output. -/
theorem initialRoundStateOverGatherSpecifications_output (P : Parameters) (k : Fin P.n) :
    (GBCA.ByAFW.programs (initialRoundStateOverGatherSpecifications P) k).output = none := rfl

/-! ## The graded-agreement families

Three families over `InstanceFamilyState`, of the shape of `gbcaSpecificationFamily`: a label a
round owns moves that round alone, `τ` moves one round of the map, `fail` is the broadcast that
corrupts every round's gather instances together, and every other label idles. -/

/-- The state of `roundFamilyOverBracha`: the corruptions applied and the rounds the family has
touched. -/
abbrev RoundFamilyOverBrachaState (P : Parameters) : Type :=
  InstanceFamilyState (initialRoundStateOverBracha P) (corruptionOverBracha P)

/-- The state of `roundFamilyOverBroadcastSpecification`. -/
abbrev RoundFamilyOverBroadcastSpecificationState (P : Parameters) : Type :=
  InstanceFamilyState (initialRoundStateOverBroadcastSpecification P)
    (corruptionOverBroadcastSpecification P)

/-- The state of `roundFamilyOverGatherSpecifications`. -/
abbrev RoundFamilyOverGatherSpecificationsState (P : Parameters) : Type :=
  InstanceFamilyState (initialRoundStateOverGatherSpecifications P)
    (corruptionOverGatherSpecifications P)

/-- The gather-based graded-agreement family: the family of rounds over the gather instances over
Bracha's broadcast. -/
noncomputable def roundFamilyOverBracha (P : Parameters) :
    System (RoundFamilyOverBrachaState P) (ExtendedLabel P.n Empty) :=
  System.family (GBCA.ByAFW.roundOverBracha P) roundOwnsLabel isFailLabel (corruptionOverBracha P)
    (initialRoundStateOverBracha P)

/-- The family starts from the rounds' initial states. -/
theorem roundFamilyOverBracha_init_apply (P : Parameters) (r : ℕ) :
    (roundFamilyOverBracha P).init r = (GBCA.ByAFW.roundOverBracha P r).init :=
  System.family_init_apply _ _ _ (roundOverBracha_init_eq P) r

/-- The family is an LTS: every round is. -/
theorem roundFamilyOverBracha_isLTS (P : Parameters) : (roundFamilyOverBracha P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBracha_isLTS P) _ _ _ _

/-- Every input of the round family is a non-silent label the family assigns to no round, or a
call or a corrupted process's call of round `r`, which the family assigns to round `r` and which
is an input of round `r`. -/
private theorem roundFamily_inputLabels_subset (P : Parameters) :
    (roundFamilyInputOutputLabels P Empty).inputLabels ⊆
      {l | ¬ l = Silent.τ ∧ roundOwnsLabel l = none} ∪
        {l | ∃ r, roundOwnsLabel l = some r ∧
          l ∈ (GBCA.ByAFW.roundInputOutputLabels P.n r).inputLabels} := by
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
  · exact m.elim
  · exact m.elim
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact e.elim
  · exact Or.inr ⟨r, rfl, Or.inr (Or.inl ⟨k, b, rfl⟩)⟩
  · exact Or.inl ⟨hτ, rfl⟩

/-- **The family over Bracha's broadcast is input-enabled** on the inputs of the round family:
every non-silent label other than a return and an announcement. -/
theorem roundFamilyOverBracha_inputEnabled (P : Parameters) :
    (roundFamilyOverBracha P).InputEnabled (roundFamilyInputOutputLabels P Empty).inputLabels :=
  (System.InputEnabled.family (GBCA.ByAFW.roundOverBracha_inputEnabled P) roundOwnsLabel
    isFailLabel (corruptionOverBracha P) (initialRoundStateOverBracha P)).mono
      (roundFamily_inputLabels_subset P)

/-- The family over the gather instances over the broadcast specification. -/
noncomputable def roundFamilyOverBroadcastSpecification (P : Parameters) :
    System (RoundFamilyOverBroadcastSpecificationState P) (ExtendedLabel P.n Empty) :=
  System.family (GBCA.ByAFW.roundOverBroadcastSpecification P) roundOwnsLabel isFailLabel
    (corruptionOverBroadcastSpecification P) (initialRoundStateOverBroadcastSpecification P)

/-- The family starts from the rounds' initial states. -/
theorem roundFamilyOverBroadcastSpecification_init_apply (P : Parameters) (r : ℕ) :
    (roundFamilyOverBroadcastSpecification P).init r =
      (GBCA.ByAFW.roundOverBroadcastSpecification P r).init :=
  System.family_init_apply _ _ _ (roundOverBroadcastSpecification_init_eq P) r

/-- The family is an LTS. -/
theorem roundFamilyOverBroadcastSpecification_isLTS (P : Parameters) :
    (roundFamilyOverBroadcastSpecification P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBroadcastSpecification_isLTS P) _ _ _ _

/-- **The family over the broadcast specification is input-enabled** on the inputs of the round
family. -/
theorem roundFamilyOverBroadcastSpecification_inputEnabled (P : Parameters) :
    (roundFamilyOverBroadcastSpecification P).InputEnabled
      (roundFamilyInputOutputLabels P Empty).inputLabels :=
  (System.InputEnabled.family (GBCA.ByAFW.roundOverBroadcastSpecification_inputEnabled P)
    roundOwnsLabel isFailLabel (corruptionOverBroadcastSpecification P)
    (initialRoundStateOverBroadcastSpecification P)).mono (roundFamily_inputLabels_subset P)

/-- The family over the gather specifications. -/
noncomputable def roundFamilyOverGatherSpecifications (P : Parameters) :
    System (RoundFamilyOverGatherSpecificationsState P) (ExtendedLabel P.n Empty) :=
  System.family (GBCA.ByAFW.roundOverGatherSpecifications P) roundOwnsLabel isFailLabel
    (corruptionOverGatherSpecifications P) (initialRoundStateOverGatherSpecifications P)

/-- The family starts from the rounds' initial states. -/
theorem roundFamilyOverGatherSpecifications_init_apply (P : Parameters) (r : ℕ) :
    (roundFamilyOverGatherSpecifications P).init r =
      (GBCA.ByAFW.roundOverGatherSpecifications P r).init :=
  System.family_init_apply _ _ _ (roundOverGatherSpecifications_init_eq P) r

/-- The family is an LTS. -/
theorem roundFamilyOverGatherSpecifications_isLTS (P : Parameters) :
    (roundFamilyOverGatherSpecifications P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverGatherSpecifications_isLTS P) _ _ _ _

/-- **The family over the gather specifications is input-enabled** on the inputs of the round
family. -/
theorem roundFamilyOverGatherSpecifications_inputEnabled (P : Parameters) :
    (roundFamilyOverGatherSpecifications P).InputEnabled
      (roundFamilyInputOutputLabels P Empty).inputLabels :=
  (System.InputEnabled.family (GBCA.ByAFW.roundOverGatherSpecifications_inputEnabled P)
    roundOwnsLabel isFailLabel (corruptionOverGatherSpecifications P)
    (initialRoundStateOverGatherSpecifications P)).mono (roundFamily_inputLabels_subset P)

/-! ## The protocol-shaped systems

The composed system's pipeline (the graded-agreement family beside the round loops, the ABA network
and the common coin, the labels the components synchronise on hidden, the result read back over
`Label n`, the sub-protocol API hidden) taken at each of the three compositions of the gather-based
construction. -/

/-- The state of the gather-based composed system: the family of rounds, the round loops, the ABA
network and the family of coin instances. -/
abbrev ComposedState (P : Parameters) : Type :=
  RoundFamilyOverBrachaState P ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) ×
      (ABANetworkState P.n × InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)))

/-- The state over the broadcast specification. -/
abbrev ComposedOverBroadcastSpecificationState (P : Parameters) : Type :=
  RoundFamilyOverBroadcastSpecificationState P ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) ×
      (ABANetworkState P.n × InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)))

/-- The state over the gather specifications. -/
abbrev ComposedOverGatherSpecificationsState (P : Parameters) : Type :=
  RoundFamilyOverGatherSpecificationsState P ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) ×
      (ABANetworkState P.n × InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)))

/-- **The gather-based composed system**: the gather-based graded-agreement family beside the
composed system's other three components, through the two hidings. -/
noncomputable def composed (P : Parameters) : System (ComposedState P) (Label P.n) :=
  ((((roundFamilyOverBracha P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The composition over the broadcast specification, at the protocol shape. -/
noncomputable def composedOverBroadcastSpecification (P : Parameters) :
    System (ComposedOverBroadcastSpecificationState P) (Label P.n) :=
  ((((roundFamilyOverBroadcastSpecification P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The composition over the gather specifications, at the protocol shape. -/
noncomputable def composedOverGatherSpecifications (P : Parameters) :
    System (ComposedOverGatherSpecificationsState P) (Label P.n) :=
  ((((roundFamilyOverGatherSpecifications P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-! ## Building a transition of the composed system

The composed system's pipeline, read once so that every transition of the simulation can be
assembled from its components' transitions: the family of rounds beside the round loops, the ABA
network and the lifted common coin. -/

/-- The four components of the gather-based composed system, in parallel. -/
noncomputable def composedExtended (P : Parameters) :
    System (ComposedState P) (ExtendedLabel P.n Empty) :=
  (roundFamilyOverBracha P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))

/-- The composed group: the labels the components synchronise on hidden, read back over
`Label n`. -/
noncomputable def composedHidden (P : Parameters) :
    System (ComposedState P) (Label P.n) :=
  ((composedExtended P).abstract (networkEventLabels P.n)).relabel

theorem composed_eq (P : Parameters) :
    composed P = (composedHidden P).abstract (Label.hiddenAPI P.n) := rfl

/-! ### The graded-agreement family's transitions

The family passes a label a round owns to that round and enters the round in its map, takes `τ` at
a round of its map, broadcasts `fail`, and idles on everything else. -/

/-- The round-`r` state moves on a label it owns, in the map or not, and the family enters its
successor at `r`. -/
theorem roundFamilyOverBracha_owned (P : Parameters) (G : RoundFamilyOverBrachaState P)
    (r : ℕ) {L : ExtendedLabel P.n Empty} (hL : roundOwnsLabel L = some r)
    {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) L (PMF.pure q)) :
    (roundFamilyOverBracha P).step G L (PMF.pure (G.setInstanceState r q)) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure q, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose round is unchanged, at a round of the map: the family is unchanged. -/
theorem roundFamilyOverBracha_owned_id (P : Parameters) (G : RoundFamilyOverBrachaState P)
    (r : ℕ) (hr : r ∈ G.instanceMap.keys) {L : ExtendedLabel P.n Empty}
    (hL : roundOwnsLabel L = some r)
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) L (PMF.pure (G r))) :
    (roundFamilyOverBracha P).step G L (PMF.pure G) := by
  have hstep := roundFamilyOverBracha_owned P G r hL h
  rwa [InstanceFamilyState.setInstanceState_apply_self hr] at hstep

/-- The round-`r` state, at a round of the map, takes one of its own silent transitions. -/
theorem roundFamilyOverBracha_tau (P : Parameters) (G : RoundFamilyOverBrachaState P)
    (r : ℕ) (hr : r ∈ G.instanceMap.keys) {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) (Sum.inl Label.tau) (PMF.pure q)) :
    (roundFamilyOverBracha P).step G (Sum.inl Label.tau)
      (PMF.pure (G.setInstanceState r q)) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inl ⟨rfl, r, hr, PMF.pure q, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem roundFamilyOverBracha_idle (P : Parameters) (G : RoundFamilyOverBrachaState P)
    {L : ExtendedLabel P.n Empty} (hτ : L ≠ Silent.τ) (hown : roundOwnsLabel L = none)
    (hf : ¬ isFailLabel L) : (roundFamilyOverBracha P).step G L (PMF.pure G) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round, in the map or not. -/
theorem roundFamilyOverBracha_fail (P : Parameters) (G : RoundFamilyOverBrachaState P)
    (k : Fin P.n) :
    (roundFamilyOverBracha P).step G (Sum.inl (Label.fail k))
      (PMF.pure (G.applyBroadcast (Sum.inl (Label.fail k)))) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-! ### The four components -/

/-- The three components beside the graded-agreement family move together on a visible label, the
coin's successor left free. -/
theorem contextStep (P : Parameters) {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ν : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    {L : ExtendedLabel P.n Empty} (hL : L ≠ Silent.τ)
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P Empty).step o L ν) :
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel ((ABANetwork P Empty).parallel
      (coinOverRoundAlphabet P Empty))).step
      (C, A, o) L (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν)) := by
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ν, roundLoopProduct_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ν, hA, hW, rfl⟩

/-- Build a synchronised transition of the four components on a visible label, the
coin's successor left free. -/
theorem composedExtended_visible_step (P : Parameters)
    {G G' : RoundFamilyOverBrachaState P} {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ν : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    {L : ExtendedLabel P.n Empty} (hL : L ≠ Silent.τ)
    (hG : (roundFamilyOverBracha P).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A')) (hW : (coinOverRoundAlphabet P Empty).step o L ν) :
    (composedExtended P).step (G, C, A, o) L
    (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  rw [composedExtended, System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν),
    hG, contextStep P hL hC hA hW, rfl⟩

/-- Build a silent transition of the four components from a silent transition of the family. -/
theorem composedExtended_tau_overBracha (P : Parameters)
    {G G' : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hG : (roundFamilyOverBracha P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [composedExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA network injection. -/
theorem composedExtended_tau_ABANetwork (P : Parameters)
    {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hA : ABANetworkStep P A (Sum.inl Label.tau : ExtendedLabel P.n Empty) (PMF.pure A')) :
    (composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G, C, A', o)) := by
  rw [composedExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-- Build a silent transition of the four components from the resolution of one round of the
common coin, at a round of the coin family's map. -/
theorem composedExtended_tau_coin (P : Parameters)
    {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {r : ℕ} (hr : r ∈ o.instanceMap.keys) {μw : PMF (WCC.SpecState P.n)}
    (hW : WCC.Step P r (o r) Label.tau μw) :
    (composedExtended P).step (G, C, A, o) (Sum.inl Label.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
        (prodPMF (PMF.pure A) (μw.map (o.setInstanceState r))))) := by
  rw [composedExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, _, coinOverExtendedAlphabet_tau P Empty Empty o hr hW, rfl⟩)

/-! ### The two hidings -/

theorem composedHidden_step_iff (P : Parameters) (q : ComposedState P) (l : Label P.n)
    (μ : PMF (ComposedState P)) :
    (composedHidden P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n Empty, (composedExtended P).step q (Sum.inr e) μ) ∨
      (composedExtended P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

theorem composedHidden_of_event (P : Parameters) {q : ComposedState P}
    (e : NetworkEvent P.n Empty) {μ : PMF (ComposedState P)}
    (h : (composedExtended P).step q (Sum.inr e) μ) :
    (composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedHidden_of_tau (P : Parameters) {q : ComposedState P}
    {μ : PMF (ComposedState P)}
    (h : (composedExtended P).step q (Sum.inl Label.tau) μ) :
    (composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inr h)

/-! ## Runs of the graded-agreement family

Each transition of the implementation is matched by one transition of the composed system, silent
except at the round's graded return. The builders below carry a run of one round to the
graded-agreement family, and a run of that family to the composed group. A run of a round of the
map is a run of the family. A round outside the map takes no silent transition in the family, so a
run there is placed in the family when it begins with a transition on a label the round owns. -/

/-- A silent run of a round of the map is a silent run of the graded-agreement family, which
moves that round alone. -/
theorem roundFamilyOverBracha_silentRun (P : Parameters) {G : RoundFamilyOverBrachaState P}
    {r : ℕ} {q : GBCA.ByAFW.RoundStateOverBracha P.n} (hr : r ∈ G.instanceMap.keys)
    (h : (GBCA.ByAFW.roundOverBracha P r).weakLSilent (G r) q) :
    (roundFamilyOverBracha P).weakLSilent G (G.setInstanceState r q) :=
  System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hr h

/-- A run of a round of the map on a label that round owns is a weak transition of the
graded-agreement family, which moves that round alone. -/
theorem roundFamilyOverBracha_weakStep (P : Parameters) {G : RoundFamilyOverBrachaState P}
    {r : ℕ} {L : ExtendedLabel P.n Empty} {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (hL : roundOwnsLabel L = some r) (hr : r ∈ G.instanceMap.keys)
    (h : (GBCA.ByAFW.roundOverBracha P r).weakLStep (G r) L q) :
    (roundFamilyOverBracha P).weakLStep G L (G.setInstanceState r q) :=
  System.weakLStep_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hL hr h

/-- A run of a round, in the map or not, that begins with a transition on a label the round owns
and continues with a silent run, is a weak transition of the graded-agreement family. -/
theorem roundFamilyOverBracha_weakStep_of_step (P : Parameters) {G : RoundFamilyOverBrachaState P}
    {r : ℕ} {L : ExtendedLabel P.n Empty} {μ : PMF (GBCA.ByAFW.RoundStateOverBracha P.n)}
    {q₁ q : GBCA.ByAFW.RoundStateOverBracha P.n} (hL : roundOwnsLabel L = some r)
    (hτ : L ≠ Silent.τ) (hstep : (GBCA.ByAFW.roundOverBracha P r).step (G r) L μ)
    (hq₁ : q₁ ∈ μ.support) (h : (GBCA.ByAFW.roundOverBracha P r).weakLSilent q₁ q) :
    (roundFamilyOverBracha P).weakLStep G L (G.setInstanceState r q) :=
  System.weakLStep_family_of_step roundOwnsLabel isFailLabel (corruptionOverBracha P) hL hτ hstep
    hq₁ h

/-- **A silent run of the graded-agreement family is a silent weak transition of the composed
group**: the three other components stand at their states throughout. -/
theorem composedHidden_weakTau (P : Parameters) {G G' : RoundFamilyOverBrachaState P}
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
    (h : (roundFamilyOverBracha P).weakLSilent G G') :
    weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P))
      (PMF.pure ((G', C, A, o) : ComposedState P)) := by
  have h1 : weakTau (roundFamilyOverBracha P) (PMF.pure G) (PMF.pure G') :=
    weakTau_of_weakLSilent (roundFamilyOverBracha P) (roundFamilyOverBracha_isLTS P) h
  have h2 := weakTau_parallel_left (roundFamilyOverBracha P)
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel ((ABANetwork P Empty).parallel
      (coinOverRoundAlphabet P Empty)))
    ((C, A, o)) h1
  rw [prodPMF_pure_pure, prodPMF_pure_pure] at h2
  exact weakTau_relabel (weakTau_abstract (composedExtended P) (networkEventLabels P.n) h2)

/-- **A visible label the graded-agreement family takes by a run** and the three other components
by one transition each is a weak transition of the composed group. The coin's successor is left
free, so the resulting distribution has the shape the matching clause of a probabilistic
forward simulation consumes. -/
theorem composedHidden_weakStep (P : Parameters) {G G' : RoundFamilyOverBrachaState P}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ν : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))} {l : Label P.n}
    (hl : l ≠ Label.tau)
    (hG : (roundFamilyOverBracha P).weakLStep G (Sum.inl l) G')
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inl l : ExtendedLabel P.n Empty) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inl l : ExtendedLabel P.n Empty) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P Empty).step o (Sum.inl l) ν) :
    weakStep (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  have hL : (Sum.inl l : ExtendedLabel P.n Empty) ≠ Silent.τ := by
    rw [extendedLabel_tau]
    simpa using hl
  have h1 : weakStep (roundFamilyOverBracha P) (PMF.pure G) (Sum.inl l) (PMF.pure G') :=
    weakStep_of_weakLStep (roundFamilyOverBracha P) (roundFamilyOverBracha_isLTS P) hL hG
  have h2 := weakStep_parallel_sync (roundFamilyOverBracha P)
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel ((ABANetwork P Empty).parallel
      (coinOverRoundAlphabet P Empty)))
    hL h1 (contextStep P hL hC hA hW)
  rw [prodPMF_pure_pure] at h2
  exact weakStep_relabel
    (weakStep_abstract (composedExtended P) (networkEventLabels P.n) (by simp) h2)

end AFW

end ABA
end PLTS
