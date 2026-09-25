/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.BroadcastSubstitution
import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitution
import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.WeakTransitionsFromChains
import Leslie2Protocols.Framework.Congruence

/-!
# The composed systems of the gather-based protocol

`AFW.protocol` (`ABA/AFW/System.lean`) is `n` programs beside one network and the coin oracle, and
runs AFW25's two-gather construction in each round. `AFW.composed` reads that same protocol as a
composition of four components: the round-indexed family of gather-based graded-agreement rounds,
the `n` round loops, the DECIDED sets beside the corrupted set, and the lifted coin oracle. Those
last three and the pipeline over them — the rendezvous alphabet hidden, the result read back over
`Label n`, the sub-protocol API hidden — are the context term of `ABDY.composed` and of `hybrid`
(`ABA/Composition/Hybrid.lean`), character for character.

The graded-agreement component is taken at three tiers, which differ in what sits beneath a round's
two gather instances: Bracha's broadcast (`roundFamilyOverBracha`), the broadcast specification
(`roundFamilyOverBroadcastSpecification`) and the gather specifications
(`roundFamilyOverGatherSpecifications`). Each is an ℕ-indexed family over the shape of
`gbcaSpecificationFamily`: a round-tagged label moves its round alone, `τ` moves one round, `fail`
reaches every round, and every other label idles. The round of a given index is itself a
composition, the round's programs and the round's network beside its two gather instances
(`GBCA/AFW/Composition.lean`). Each family through the pipeline gives `AFW.composed`,
`composedOverBroadcastSpecification` and `composedOverGatherSpecifications`.

## The corruption acts

A family carries a broadcast act, and the act of a round state corrupts the round's two gather
instances at once while leaving the programs and the round's bound bit untouched (D1).
`corruptionOverBracha`, `corruptionOverBroadcastSpecification` and
`corruptionOverGatherSpecifications` are `GBCA.ByAFW.corruptAll` over the corruption of the tier's
gather states.

## What this file supplies

The three families, the three composed systems, and the lemmas that read and build their
transitions. `roundFamilyOverBracha_owned`, `roundFamilyOverBracha_tau`,
`roundFamilyOverBracha_idle` and `roundFamilyOverBracha_fail` place a transition of one round in
the family. `composedExtended_visible_step`, `composedExtended_tau_overBracha` and
`composedExtended_tau_ABANetwork` assemble a transition of the four components out of transitions
of each, and `composedHidden_of_event` and `composedHidden_of_tau` carry one through the hiding
frames. `roundFamilyOverBracha_silentRun`, `roundFamilyOverBracha_weakStep`,
`composedHidden_weakTau` and `composedHidden_weakStep` do the same for a run. The protocol meets
`AFW.composed` in `ABA/AFW/Simulation.lean`, along the view of `ABA/AFW/RoundProjection.lean`, and
`ABA/AFW/Substitution.lean` carries `AFW.composed` to `hybrid` in three stages.
-/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

namespace AFW

/-! ## The broadcast corruption acts

Corruption reaches a round through its two gather instances. Each gather
instance passes it to its own network state and to every broadcast coordinate
it holds; the round's programs and its bound bit are untouched (D1). -/

/-- The broadcast corruption act on a round over the gather instances over
Bracha's broadcast. -/
def corruptionOverBracha (P : Parameters) :
    ExtendedLabel P.n Empty → GBCA.ByAFW.RoundStateOverBracha P.n →
      GBCA.ByAFW.RoundStateOverBracha P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i))
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption act on a round over the gather instances over the
broadcast specification. -/
def corruptionOverBroadcastSpecification (P : Parameters) :
    ExtendedLabel P.n Empty → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n →
      GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption act on a round over the gather specifications. -/
def corruptionOverGatherSpecifications (P : Parameters) :
    ExtendedLabel P.n Empty → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n →
      GBCA.ByAFW.RoundStateOverGatherSpecifications P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s
  | _, s => s

/-! ## The graded-agreement families

Three ℕ-indexed families over the shape of `gbcaSpecificationFamily`: a round-tagged label moves its
round alone, `τ` moves one round, `fail` is the broadcast that keeps every round's gather instances
together, and everything else idles. -/

/-- The gather-based graded-agreement family: the family of rounds over the gather instances over
Bracha's broadcast. -/
noncomputable def roundFamilyOverBracha (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) (ExtendedLabel P.n Empty) :=
  System.family (GBCA.ByAFW.roundOverBracha P) roundOwnsLabel isFailLabel (corruptionOverBracha P)

/-- The family is an LTS: every round is. -/
theorem roundFamilyOverBracha_isLTS (P : Parameters) : (roundFamilyOverBracha P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBracha_isLTS P) _ _ _

/-- The family over the gather instances over the broadcast specification. -/
noncomputable def roundFamilyOverBroadcastSpecification (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) (ExtendedLabel P.n Empty) :=
  System.family (GBCA.ByAFW.roundOverBroadcastSpecification P) roundOwnsLabel isFailLabel
    (corruptionOverBroadcastSpecification
    P)

/-- The family is an LTS. -/
theorem roundFamilyOverBroadcastSpecification_isLTS (P : Parameters) :
  (roundFamilyOverBroadcastSpecification P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBroadcastSpecification_isLTS P) _ _ _

/-- The family over the gather specifications. -/
noncomputable def roundFamilyOverGatherSpecifications (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) (ExtendedLabel P.n Empty) :=
  System.family (GBCA.ByAFW.roundOverGatherSpecifications P) roundOwnsLabel isFailLabel
    (corruptionOverGatherSpecifications P)

/-- The family is an LTS. -/
theorem roundFamilyOverGatherSpecifications_isLTS (P : Parameters) :
  (roundFamilyOverGatherSpecifications P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverGatherSpecifications_isLTS P) _ _ _

/-! ## The protocol-shaped systems

The composed system's pipeline — the graded-agreement family beside the round loops, the ABA network
and the coin oracle, the rendezvous alphabet hidden, the result read back over `Label n`, the
sub-protocol API hidden — taken at each tier of the gather-based construction. -/

/-- The state of the gather-based composed system. -/
abbrev ComposedState (P : Parameters) : Type :=
  (ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the middle tier. -/
abbrev ComposedOverBroadcastSpecificationState (P : Parameters) : Type :=
  (ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the upper tier. -/
abbrev ComposedOverGatherSpecificationsState (P : Parameters) : Type :=
  (ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- **The gather-based composed system**: the gather-based graded-agreement family beside the
composed system's other three components, through the two hiding frames. -/
noncomputable def composed (P : Parameters) : System (ComposedState P) (Label P.n) :=
  ((((roundFamilyOverBracha P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The middle tier at the protocol shape. -/
noncomputable def composedOverBroadcastSpecification (P : Parameters) : System
  (ComposedOverBroadcastSpecificationState P) (Label P.n) :=
  ((((roundFamilyOverBroadcastSpecification P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The upper tier at the protocol shape. -/
noncomputable def composedOverGatherSpecifications (P : Parameters) : System
  (ComposedOverGatherSpecificationsState P) (Label P.n) :=
  ((((roundFamilyOverGatherSpecifications P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-! ## Building a transition of the composed system

The composed system's pipeline, read once so that every transition of the simulation can be
assembled from its components' transitions: the family of rounds beside the round loops, the ABA
network and the lifted oracle. -/

/-- The four components of the gather-based composed system, in parallel. -/
noncomputable def composedExtended (P : Parameters) :
    System (ComposedState P) (ExtendedLabel P.n Empty) :=
  (roundFamilyOverBracha P).parallel
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))

/-- The composed group: the rendezvous alphabet hidden, read back over
`Label n`. -/
noncomputable def composedHidden (P : Parameters) :
    System (ComposedState P) (Label P.n) :=
  ((composedExtended P).abstract (networkEventLabels P.n)).relabel

theorem composed_eq (P : Parameters) :
    composed P = (composedHidden P).abstract (Label.hiddenAPI P.n) := rfl

/-- The round-`r` state moves on a label it owns. -/
theorem roundFamilyOverBracha_owned (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (r : ℕ) {L : ExtendedLabel P.n Empty} (hL : roundOwnsLabel L = some r)
    {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) L (PMF.pure q)) :
    (roundFamilyOverBracha P).step G L (PMF.pure (Function.update G r q)) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure q, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose round is unchanged. -/
theorem roundFamilyOverBracha_owned_id (P : Parameters)
    (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) (r : ℕ) {L : ExtendedLabel P.n Empty}
    (hL : roundOwnsLabel L = some r)
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) L (PMF.pure (G r))) :
    (roundFamilyOverBracha P).step G L (PMF.pure G) := by
  have hstep := roundFamilyOverBracha_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` state takes one of its own silent transitions. -/
theorem roundFamilyOverBracha_tau (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (r : ℕ) {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) (Sum.inl Label.tau) (PMF.pure q)) :
    (roundFamilyOverBracha P).step G (Sum.inl Label.tau) (PMF.pure (Function.update G r q)) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure q, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem roundFamilyOverBracha_idle (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    {L : ExtendedLabel P.n Empty} (hτ : L ≠ Silent.τ) (hown : roundOwnsLabel L = none)
    (hf : ¬ isFailLabel L) : (roundFamilyOverBracha P).step G L (PMF.pure G) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's coordinate. -/
theorem roundFamilyOverBracha_fail (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (k : Fin P.n) :
    (roundFamilyOverBracha P).step G (Sum.inl (Label.fail k))
    (PMF.pure (fun r => corruptionOverBracha P (Sum.inl (Label.fail k)) (G r))) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- The three components beside the graded-agreement family move together on a visible label, the
oracle's successor left free. -/
theorem contextStep (P : Parameters) {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {L : ExtendedLabel P.n Empty} (hL : L ≠ Silent.τ)
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

/-- Build a joint transition of the four components on a visible label, the
oracle's successor left free. -/
theorem composedExtended_visible_step (P : Parameters)
    {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)}
    {L : ExtendedLabel P.n Empty} (hL : L ≠ Silent.τ)
    (hG : (roundFamilyOverBracha P).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A')) (hW : (coinOverRoundAlphabet P Empty).step o L ν) :
    (composedExtended P).step (G, C, A, o) L
    (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  rw [composedExtended, System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν),
    hG, contextStep P hL hC hA hW, rfl⟩

/-- Build a silent transition of the four components from a round's own. -/
theorem composedExtended_tau_overBracha (P : Parameters)
    {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    (hG : (roundFamilyOverBracha P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [composedExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA network injection. -/
theorem composedExtended_tau_ABANetwork (P : Parameters)
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n}
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

/-! ### The two hiding frames -/

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
graded-agreement family, and a run of that family to the composed group. -/

/-- A silent run of one round is a silent run of the graded-agreement family at that coordinate. -/
theorem roundFamilyOverBracha_silentRun (P : Parameters)
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {r : ℕ} {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).weakLSilent (G r) q) :
    (roundFamilyOverBracha P).weakLSilent G (Function.update G r q) := by
  rw [roundFamilyOverBracha]
  exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) h

/-- A run of one round on a label that round owns is a weak transition of the graded-agreement
family at that coordinate. -/
theorem roundFamilyOverBracha_weakStep (P : Parameters)
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {r : ℕ} {L : ExtendedLabel P.n Empty}
    {q : GBCA.ByAFW.RoundStateOverBracha P.n} (hL : roundOwnsLabel L = some r)
    (h : (GBCA.ByAFW.roundOverBracha P r).weakLStep (G r) L q) :
    (roundFamilyOverBracha P).weakLStep G L (Function.update G r q) := by
  rw [roundFamilyOverBracha]
  exact System.weakLStep_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hL h

/-- **A silent run of the graded-agreement family is a silent weak transition of the composed
group**: the three other components stand at their states throughout. -/
theorem composedHidden_weakTau (P : Parameters) {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : ℕ → WCC.SpecState P.n) (h : (roundFamilyOverBracha P).weakLSilent G G') :
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

/-- **A visible label the graded-agreement family answers by a run** and the three other components
by one transition each is a weak transition of the composed group. The oracle's successor is left
free, so the resulting distribution has the shape the matching clause of a probabilistic
forward simulation consumes. -/
theorem composedHidden_weakStep (P : Parameters) {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)} {l : Label P.n}
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
