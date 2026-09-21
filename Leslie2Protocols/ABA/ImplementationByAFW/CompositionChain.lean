/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitutions
import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution
import Leslie2Protocols.ABA.Results
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2.Results

/-!
# The gather-based chain at the protocol shape

The gather-based implementation is carried to the protocol-shaped
specification `hybrid` in three stages. Each stage replaces one tier of the
round by the tier above it, at every round at once:

1. `substSimLow` — the broadcast substitution, from the round over the gather
   instances over Bracha's broadcast to the round over the gather instances
   over the broadcast specification;
2. `substSimIdeal` — the gather substitution, into the round over the gather
   specifications;
3. `substSimPair` — the counting simulation, into the round specification.

The systems the stages run between are `composed`, `composedOverBroadcastSpecification`,
`composedOverGatherSpecifications` and `hybrid`. Each has a graded-agreement side and three further
components. The side is an ℕ-indexed family of rounds — `roundFamilyOverBracha`,
`roundFamilyOverBroadcastSpecification`, `roundFamilyOverGatherSpecifications` and
`gbcaSpecificationFamily` — in which a round-tagged label moves its round alone, `τ` moves one
round, `fail` reaches every round, and every other label idles. The round of a given index is itself
a composition: the layer of programs and the round's network beside the round's two gather instances
(`GBCA/AFW/Composition.lean`).

The three further components are the round loops, the ABA-side network and the
lifted coin oracle, and the pipeline over them — the rendezvous alphabet
hidden, the result read back over `Label n`, the sub-protocol API hidden — is the
context term of `ABDY.composed` and `hybrid`, character for character. The
third stage therefore lands on `hybrid P` itself, and the shared links
`hybrid_spec` and `coreSim` carry the gather-based chain to the ABA
specification from there.

Each side carries a broadcast act, and the act of a round state corrupts the
round's two gather instances at once while leaving the programs and the round's
bound bit untouched (D1): `gActLow`, `gActIdeal` and `gActPair` are
`GBCA.ByAFW.corruptAll` over the corruption of the tier's gather states, and
`GBCA.ByABDY.specificationCorruptionAct` is the act of the specification side. The three relations
survive those acts — `lowSim_failAct`, `idealSim_failAct`, `pairSim_failAct` —
which is the side condition `ForwardSimulation.family` consumes.

`substitution` is the three-stage inclusion, `composed_refines` chains it with
`hybrid_spec`, `composed_safe` reads off Validity and Agreement, and
`chainSimComposed` composes the simulations themselves.
-/

namespace PLTS
namespace ABA

open Implementation Composition GBCA.ByABDY

namespace AFW

/-! ## The broadcast corruption acts

Corruption reaches a round through its two gather instances. Each gather
instance passes it to its own network state and to every broadcast coordinate
it holds; the round's programs and its bound bit are untouched (D1). -/

/-- The broadcast corruption act on a round over the gather instances over
Bracha's broadcast. -/
def gActLow (P : Parameters) :
    ExtendedLabel P.n → GBCA.ByAFW.RoundStateOverBracha P.n → GBCA.ByAFW.RoundStateOverBracha P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i))
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption act on a round over the gather instances over the
broadcast specification. -/
def gActIdeal (P : Parameters) :
    ExtendedLabel P.n → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n →
      GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption act on a round over the gather specifications. -/
def gActPair (P : Parameters) :
    ExtendedLabel P.n → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n →
      GBCA.ByAFW.RoundStateOverGatherSpecifications P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s
  | _, s => s

/-! ### Broadcast compatibility

The three relations survive the corruption broadcast: the rounds' own
lockstep-corruption statements, taken on the extended `fail` label. -/

/-- Corruption preserves the broadcast substitution relation. -/
theorem lowSim_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n, isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBracha P.n)
      (y : GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n), GBCA.ByAFW.LowPairRel P x y →
      GBCA.ByAFW.LowPairRel P (gActLow P l x) (gActIdeal P l y) := by
  rintro l hl _ x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.ByAFW.lowPairRel_corrupt hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-- Corruption preserves the gather substitution relation. -/
theorem idealSim_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n,
      isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) (y :
        GBCA.ByAFW.RoundStateOverGatherSpecifications P.n), GBCA.ByAFW.IdealRel P x y →
      GBCA.ByAFW.IdealRel P (gActIdeal P l x) (gActPair P l y) := by
  rintro l hl _ x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.ByAFW.idealRel_corrupt hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-- Corruption preserves the counting relation. -/
theorem pairSim_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n,
      isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) (y :
        GBCA.SpecState P.n), GBCA.ByAFW.PairRel P x y →
      GBCA.ByAFW.PairRel P (gActPair P l x) (specificationCorruptionAct P l y) := by
  rintro l hl r x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.ByAFW.pairRel_corrupt (r := r) hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-! ## The graded-agreement sides

Three ℕ-indexed families over the shape of `gbcaSpecificationFamily`: a round-tagged label
moves its round alone, `τ` moves one round, `fail` is the broadcast that keeps
every round's gather instances in lockstep, and everything else idles. -/

/-- The gather-based graded-agreement side: the family of rounds over the
gather instances over Bracha's broadcast. -/
noncomputable def roundFamilyOverBracha (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByAFW.roundOverBracha P) roundOwnsLabel isFailLabel (gActLow P)

/-- The side is an LTS: every round is. -/
theorem roundFamilyOverBracha_isLTS (P : Parameters) : (roundFamilyOverBracha P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBracha_isLTS P) _ _ _

/-- The side over the gather instances over the broadcast specification. -/
noncomputable def roundFamilyOverBroadcastSpecification (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByAFW.roundOverBroadcastSpecification P) roundOwnsLabel isFailLabel (gActIdeal
    P)

/-- The side is an LTS. -/
theorem roundFamilyOverBroadcastSpecification_isLTS (P : Parameters) :
  (roundFamilyOverBroadcastSpecification P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBroadcastSpecification_isLTS P) _ _ _

/-- The side over the gather specifications. -/
noncomputable def roundFamilyOverGatherSpecifications (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByAFW.roundOverGatherSpecifications P) roundOwnsLabel isFailLabel (gActPair P)

/-- The side is an LTS. -/
theorem roundFamilyOverGatherSpecifications_isLTS (P : Parameters) :
  (roundFamilyOverGatherSpecifications P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverGatherSpecifications_isLTS P) _ _ _

/-! ### The family substitutions -/

/-- The pointwise round relation of the broadcast substitution. -/
def RlowAll (P : Parameters) (s : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (t : ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) : Prop :=
  ∀ r, GBCA.ByAFW.LowPairRel P (s r) (t r)

/-- The pointwise round relation of the gather substitution. -/
def RidealAll (P : Parameters) (s : ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n)
    (t : ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) : Prop :=
  ∀ r, GBCA.ByAFW.IdealRel P (s r) (t r)

/-- The pointwise round relation of the counting simulation. -/
def RpairAll (P : Parameters) (s : ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GBCA.ByAFW.PairRel P (s r) (t r)

/-- The family substitution of the first stage, round by round. -/
theorem famLowSim (P : Parameters) :
    ForwardSimulation (roundFamilyOverBracha P) (roundFamilyOverBroadcastSpecification P) (RlowAll
      P) :=
  ForwardSimulation.family roundOwnsLabel isFailLabel (gActLow P) (gActIdeal P)
    (GBCA.ByAFW.lowPairRefines P) (lowSim_failAct P)

/-- The family substitution of the second stage. -/
theorem famIdealSim (P : Parameters) :
    ForwardSimulation (roundFamilyOverBroadcastSpecification P) (roundFamilyOverGatherSpecifications
      P) (RidealAll P) :=
  ForwardSimulation.family roundOwnsLabel isFailLabel (gActIdeal P) (gActPair P)
    (GBCA.ByAFW.idealRefines P) (idealSim_failAct P)

/-- The family substitution of the third stage, into the specification
side. -/
theorem famPairSim (P : Parameters) :
    ForwardSimulation (roundFamilyOverGatherSpecifications P) (gbcaSpecificationFamily P) (RpairAll
      P) :=
  ForwardSimulation.family roundOwnsLabel isFailLabel (gActPair P) (specificationCorruptionAct P)
    (GBCA.ByAFW.pairRefines P) (pairSim_failAct P)

/-- The first family substitution, probabilistically. -/
theorem famLowSimProb (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverBracha P) (roundFamilyOverBroadcastSpecification
      P)
      (diracRel (RlowAll P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverBracha_isLTS P)
    (roundFamilyOverBroadcastSpecification_isLTS P)
    (fun r => GBCA.ByAFW.lowPairRel_init P r) (famLowSim P)

/-- The second family substitution, probabilistically. -/
theorem famIdealSimProb (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverBroadcastSpecification P)
      (roundFamilyOverGatherSpecifications P)
      (diracRel (RidealAll P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverBroadcastSpecification_isLTS P)
    (roundFamilyOverGatherSpecifications_isLTS P)
    (fun r => GBCA.ByAFW.idealRel_init P r) (famIdealSim P)

/-- The third family substitution, probabilistically. -/
theorem famPairSimProb (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverGatherSpecifications P) (gbcaSpecificationFamily
      P)
      (diracRel (RpairAll P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverGatherSpecifications_isLTS P)
    (gbcaSpecificationFamily_isLTS P)
    (fun r => GBCA.ByAFW.pairRel_init P r) (famPairSim P)

/-! ## The protocol-shaped systems

The composed reading's pipeline — the graded-agreement side beside the round
loops, the ABA-side network and the coin oracle, the rendezvous alphabet
hidden, the result read back over `Label n`, the sub-protocol API hidden — taken
at each tier of the gather-based construction. -/

/-- The state of the gather-based composed reading. -/
abbrev ComposedState (P : Parameters) : Type :=
  (ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the middle tier. -/
abbrev ComposedOverBroadcastSpecificationState (P : Parameters) : Type :=
  (ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the upper tier. -/
abbrev ComposedOverGatherSpecificationsState (P : Parameters) : Type :=
  (ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- **The gather-based composed reading**: the gather-based graded-agreement
side beside the composed reading's other three components, through the two
hiding frames. -/
noncomputable def composed (P : Parameters) : System (ComposedState P) (Label P.n) :=
  ((((roundFamilyOverBracha P).parallel
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The middle tier at the protocol shape. -/
noncomputable def composedOverBroadcastSpecification (P : Parameters) : System
  (ComposedOverBroadcastSpecificationState P) (Label P.n) :=
  ((((roundFamilyOverBroadcastSpecification P).parallel
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The upper tier at the protocol shape. -/
noncomputable def composedOverGatherSpecifications (P : Parameters) : System
  (ComposedOverGatherSpecificationsState P) (Label P.n) :=
  ((((roundFamilyOverGatherSpecifications P).parallel
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-! ### The three-stage substitution -/

/-- The first stage at the protocol shape: the four congruences applied to the
first family substitution under the composed reading's own context. -/
noncomputable def substSimLow (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (composedOverBroadcastSpecification P)
      (parallelRel (diracRel (RlowAll P))) :=
  ((((famLowSimProb P).parallel_right
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The second stage at the protocol shape. -/
noncomputable def substSimIdeal (P : Parameters) :
    ProbabilisticForwardSimulation (composedOverBroadcastSpecification P)
      (composedOverGatherSpecifications P)
      (parallelRel (diracRel (RidealAll P))) :=
  ((((famIdealSimProb P).parallel_right
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The third stage at the protocol shape, into the protocol-shaped
specification `hybrid P` — the point where the gather-based chain meets the
ABDY chain. -/
noncomputable def substSimPair (P : Parameters) :
    ProbabilisticForwardSimulation (composedOverGatherSpecifications P) (hybrid P)
      (parallelRel (diracRel (RpairAll P))) :=
  ((((famPairSimProb P).parallel_right
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- **The gather-based substitution simulation**: the three stages joined by
Result 2. -/
noncomputable def substSim (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (hybrid P)
      (compRel (parallelRel (diracRel (RlowAll P)))
        (compRel (parallelRel (diracRel (RidealAll P)))
          (parallelRel (diracRel (RpairAll P))))) :=
  (substSimLow P).trans ((substSimIdeal P).trans (substSimPair P))

/-- **The gather-based substitution inclusion**: every trace distribution
achievable by the gather-based composed reading is achievable by the
protocol-shaped specification. The three stage inclusions are chained by
`Set.Subset.trans`; the inclusion never invokes transitivity of
simulation. -/
theorem substitution (P : Parameters) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P) :=
  Set.Subset.trans (substSimLow P).achievableTraceDists_subset
    (Set.Subset.trans (substSimIdeal P).achievableTraceDists_subset
      (substSimPair P).achievableTraceDists_subset)

/-! ## The headlines -/

/-- **Trace-distribution refinement of the gather-based composed reading**:
every trace distribution achievable by it is achievable by the ABA
specification. The substitution gives the first inclusion, the shared core
simulation the second. -/
theorem composed_refines (P : Parameters) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (substitution P) (hybrid_spec P)

/-- **Safety of the gather-based reading**: every positive-probability trace
of every achievable trace distribution of the gather-based composed reading
satisfies Validity and Agreement. -/
theorem composed_safe (P : Parameters) :
    ∀ D ∈ achievableTraceDists (composed P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (composed_refines P) (spec_safe P)

/-- **The composed gather-based simulation** `composed ⊑ ABA.spec`: the
three-stage substitution joined with the shared core simulation by
Result 2. -/
noncomputable def chainSimComposed (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (spec P)
      (compRel
        (compRel (parallelRel (diracRel (RlowAll P)))
          (compRel (parallelRel (diracRel (RidealAll P)))
            (parallelRel (diracRel (RpairAll P)))))
        (coreRel P)) :=
  (substSim P).trans (coreSim P)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.AFW.substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substitution

/-- info: 'PLTS.ABA.AFW.composed_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composed_refines

/-- info: 'PLTS.ABA.AFW.composed_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composed_safe

/-- info: 'PLTS.ABA.AFW.chainSimComposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainSimComposed

end AFW

end ABA
end PLTS
