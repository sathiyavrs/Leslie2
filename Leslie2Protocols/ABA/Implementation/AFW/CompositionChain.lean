/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitutions
import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2.Results

/-!
# The gather-based chain at the protocol shape

The gather-based implementation is carried to the protocol-shaped
specification `hybrid` in three stages. Each stage replaces one tier of the
round by the tier above it, at every round at once:

1. `broadcastSubstitution` — the broadcast substitution, from the round over the gather
   instances over Bracha's broadcast to the round over the gather instances
   over the broadcast specification;
2. `gatherSubstitution` — the gather substitution, into the round over the gather
   specifications;
3. `roundSpecificationSubstitution` — the counting simulation, into the round specification.

The systems the stages run between are `composed`, `composedOverBroadcastSpecification`,
`composedOverGatherSpecifications` and `hybrid`. Each has a graded-agreement family and three
further components. The component is an ℕ-indexed family of rounds — `roundFamilyOverBracha`,
`roundFamilyOverBroadcastSpecification`, `roundFamilyOverGatherSpecifications` and
`gbcaSpecificationFamily` — in which a round-tagged label moves its round alone, `τ` moves one
round, `fail` reaches every round, and every other label idles. The round of a given index is itself
a composition: the round's programs of programs and the round's network beside the round's two
gather instances (`GBCA/AFW/Composition.lean`).

The three further components are the round loops, the ABA network and the lifted coin oracle, and
the pipeline over them — the rendezvous alphabet hidden, the result read back over `Label n`, the
sub-protocol API hidden — is the context term of `ABDY.composed` and `hybrid`, character for
character. The third stage therefore lands on `hybrid P` itself, which is where the gather-based
chain meets the chain of `ABDY.composed` and takes the shared simulation
`hybridRefinesSpecification` (`HybridRefinesSpecification/Simulation.lean`) to the ABA
specification.

Each family carries a broadcast act, and the act of a round state corrupts the round's two gather
instances at once while leaving the programs and the round's bound bit untouched (D1):
`corruptionOverBracha`, `corruptionOverBroadcastSpecification` and
`corruptionOverGatherSpecifications` are `GBCA.ByAFW.corruptAll` over the corruption of the tier's
gather states, and `GBCA.ByABDY.specificationCorruptionAct` is the act of the specification. The
three relations survive those acts — `broadcastSubstitution_failAct`, `gatherSubstitution_failAct`,
`roundSpecificationSubstitution_failAct` — which is the premise `ForwardSimulation.family` consumes.

`substitution` is the three-stage inclusion, and `ABA/Results.lean` chains it with the shared
inclusion to state the headlines of the gather-based chain.
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
def corruptionOverBracha (P : Parameters) :
    ExtendedLabel P.n → GBCA.ByAFW.RoundStateOverBracha P.n → GBCA.ByAFW.RoundStateOverBracha P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i))
      (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption act on a round over the gather instances over the
broadcast specification. -/
def corruptionOverBroadcastSpecification (P : Parameters) :
    ExtendedLabel P.n → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n →
      GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
      (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i)) s
  | _, s => s

/-- The broadcast corruption act on a round over the gather specifications. -/
def corruptionOverGatherSpecifications (P : Parameters) :
    ExtendedLabel P.n → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n →
      GBCA.ByAFW.RoundStateOverGatherSpecifications P.n
  | Sum.inl (.fail k), s =>
    GBCA.ByAFW.corruptAll P k (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s
  | _, s => s

/-! ### Broadcast compatibility

The three relations survive the corruption broadcast: the rounds' own simultaneous-corruption
statements, taken on the extended `fail` label. -/

/-- Corruption preserves the broadcast substitution relation. -/
theorem broadcastSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n, isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBracha P.n)
      (y : GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n),
        GBCA.ByAFW.BroadcastSubstitutionRelation P x y →
      GBCA.ByAFW.BroadcastSubstitutionRelation P (corruptionOverBracha P l x)
        (corruptionOverBroadcastSpecification P l y) := by
  rintro l hl _ x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.ByAFW.broadcastSubstitutionRelation_corrupt hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-- Corruption preserves the gather substitution relation. -/
theorem gatherSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n,
      isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n)
        (y : GBCA.ByAFW.RoundStateOverGatherSpecifications P.n),
          GBCA.ByAFW.GatherSubstitutionRelation P x y →
      GBCA.ByAFW.GatherSubstitutionRelation P (corruptionOverBroadcastSpecification P l x)
        (corruptionOverGatherSpecifications P l y) := by
  rintro l hl _ x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.ByAFW.gatherSubstitutionRelation_corrupt hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-- Corruption preserves the counting relation. -/
theorem roundSpecificationSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n,
      isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverGatherSpecifications P.n)
        (y : GBCA.SpecState P.n), GBCA.ByAFW.SpecificationRelation P x y →
      GBCA.ByAFW.SpecificationRelation P (corruptionOverGatherSpecifications P l x)
        (specificationCorruptionAct P l y) := by
  rintro l hl r x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.ByAFW.specificationRelation_corrupt (r := r) hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-! ## The graded-agreement families

Three ℕ-indexed families over the shape of `gbcaSpecificationFamily`: a round-tagged label moves its
round alone, `τ` moves one round, `fail` is the broadcast that keeps every round's gather instances
together, and everything else idles. -/

/-- The gather-based graded-agreement family: the family of rounds over the gather instances over
Bracha's broadcast. -/
noncomputable def roundFamilyOverBracha (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByAFW.roundOverBracha P) roundOwnsLabel isFailLabel (corruptionOverBracha P)

/-- The family is an LTS: every round is. -/
theorem roundFamilyOverBracha_isLTS (P : Parameters) : (roundFamilyOverBracha P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBracha_isLTS P) _ _ _

/-- The family over the gather instances over the broadcast specification. -/
noncomputable def roundFamilyOverBroadcastSpecification (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByAFW.roundOverBroadcastSpecification P) roundOwnsLabel isFailLabel
    (corruptionOverBroadcastSpecification
    P)

/-- The family is an LTS. -/
theorem roundFamilyOverBroadcastSpecification_isLTS (P : Parameters) :
  (roundFamilyOverBroadcastSpecification P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverBroadcastSpecification_isLTS P) _ _ _

/-- The family over the gather specifications. -/
noncomputable def roundFamilyOverGatherSpecifications (P : Parameters) :
    System (ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByAFW.roundOverGatherSpecifications P) roundOwnsLabel isFailLabel
    (corruptionOverGatherSpecifications P)

/-- The family is an LTS. -/
theorem roundFamilyOverGatherSpecifications_isLTS (P : Parameters) :
  (roundFamilyOverGatherSpecifications P).IsLTS :=
  System.family_isLTS (GBCA.ByAFW.roundOverGatherSpecifications_isLTS P) _ _ _

/-! ### The family substitutions -/

/-- The pointwise round relation of the broadcast substitution. -/
def broadcastSubstitutionRelationFamily (P : Parameters)
    (s : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (t : ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n) : Prop :=
  ∀ r, GBCA.ByAFW.BroadcastSubstitutionRelation P (s r) (t r)

/-- The pointwise round relation of the gather substitution. -/
def gatherSubstitutionRelationFamily (P : Parameters)
    (s : ℕ → GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n)
    (t : ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) : Prop :=
  ∀ r, GBCA.ByAFW.GatherSubstitutionRelation P (s r) (t r)

/-- The pointwise round relation of the counting simulation. -/
def roundSpecificationSubstitutionRelationFamily (P : Parameters)
    (s : ℕ → GBCA.ByAFW.RoundStateOverGatherSpecifications P.n) (t : ℕ → GBCA.SpecState P.n) :
    Prop :=
  ∀ r, GBCA.ByAFW.SpecificationRelation P (s r) (t r)

/-- The family substitution of the first stage, round by round. -/
theorem familyBroadcastSubstitution (P : Parameters) :
    ForwardSimulation (roundFamilyOverBracha P) (roundFamilyOverBroadcastSpecification P)
    (broadcastSubstitutionRelationFamily P) :=
  ForwardSimulation.family roundOwnsLabel isFailLabel (corruptionOverBracha P)
    (corruptionOverBroadcastSpecification P)
    (GBCA.ByAFW.broadcastSubstitution P) (broadcastSubstitution_failAct P)

/-- The family substitution of the second stage. -/
theorem familyGatherSubstitution (P : Parameters) :
    ForwardSimulation (roundFamilyOverBroadcastSpecification P)
    (roundFamilyOverGatherSpecifications P) (gatherSubstitutionRelationFamily P) :=
  ForwardSimulation.family roundOwnsLabel isFailLabel (corruptionOverBroadcastSpecification P)
    (corruptionOverGatherSpecifications P)
    (GBCA.ByAFW.gatherSubstitution P) (gatherSubstitution_failAct P)

/-- The family substitution of the third stage, into the specification. -/
theorem familyRoundSpecificationSubstitution (P : Parameters) :
    ForwardSimulation (roundFamilyOverGatherSpecifications P) (gbcaSpecificationFamily P)
    (roundSpecificationSubstitutionRelationFamily P) :=
  ForwardSimulation.family roundOwnsLabel isFailLabel (corruptionOverGatherSpecifications P)
    (specificationCorruptionAct P)
    (GBCA.ByAFW.refinesSpecification P) (roundSpecificationSubstitution_failAct P)

/-- The first family substitution, probabilistically. -/
theorem familyBroadcastSubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverBracha P)
    (roundFamilyOverBroadcastSpecification P) (diracRel (broadcastSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverBracha_isLTS P)
    (roundFamilyOverBroadcastSpecification_isLTS P)
    (fun r => GBCA.ByAFW.broadcastSubstitutionRelation_init P r) (familyBroadcastSubstitution P)

/-- The second family substitution, probabilistically. -/
theorem familyGatherSubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverBroadcastSpecification P)
      (roundFamilyOverGatherSpecifications P)
      (diracRel (gatherSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverBroadcastSpecification_isLTS P)
    (roundFamilyOverGatherSpecifications_isLTS P)
    (fun r => GBCA.ByAFW.gatherSubstitutionRelation_init P r) (familyGatherSubstitution P)

/-- The third family substitution, probabilistically. -/
theorem familyRoundSpecificationSubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverGatherSpecifications P)
    (gbcaSpecificationFamily P) (diracRel (roundSpecificationSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverGatherSpecifications_isLTS P)
    (gbcaSpecificationFamily_isLTS P)
    (fun r => GBCA.ByAFW.specificationRelation_init P r) (familyRoundSpecificationSubstitution P)

/-! ## The protocol-shaped systems

The composed system's pipeline — the graded-agreement family beside the round loops, the ABA network
and the coin oracle, the rendezvous alphabet hidden, the result read back over `Label n`, the
sub-protocol API hidden — taken at each tier of the gather-based construction. -/

/-- The state of the gather-based composed system. -/
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

/-- **The gather-based composed system**: the gather-based graded-agreement family beside the
composed system's other three components, through the two hiding frames. -/
noncomputable def composed (P : Parameters) : System (ComposedState P) (Label P.n) :=
  ((((roundFamilyOverBracha P).parallel
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The middle tier at the protocol shape. -/
noncomputable def composedOverBroadcastSpecification (P : Parameters) : System
  (ComposedOverBroadcastSpecificationState P) (Label P.n) :=
  ((((roundFamilyOverBroadcastSpecification P).parallel
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The upper tier at the protocol shape. -/
noncomputable def composedOverGatherSpecifications (P : Parameters) : System
  (ComposedOverGatherSpecificationsState P) (Label P.n) :=
  ((((roundFamilyOverGatherSpecifications P).parallel
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-! ### The three-stage substitution -/

/-- The first stage at the protocol shape: the four congruences applied to the
first family substitution under the composed system's own context. -/
noncomputable def broadcastSubstitution (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (composedOverBroadcastSpecification P)
      (parallelRel (diracRel (broadcastSubstitutionRelationFamily P))) :=
  ((((familyBroadcastSubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The second stage at the protocol shape. -/
noncomputable def gatherSubstitution (P : Parameters) :
    ProbabilisticForwardSimulation (composedOverBroadcastSpecification P)
      (composedOverGatherSpecifications P)
      (parallelRel (diracRel (gatherSubstitutionRelationFamily P))) :=
  ((((familyGatherSubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The third stage at the protocol shape, into the protocol-shaped
specification `hybrid P` — the point where the gather-based chain meets the
ABDY chain. -/
noncomputable def roundSpecificationSubstitution (P : Parameters) :
    ProbabilisticForwardSimulation (composedOverGatherSpecifications P) (hybrid P)
      (parallelRel (diracRel (roundSpecificationSubstitutionRelationFamily P))) :=
  ((((familyRoundSpecificationSubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- **The gather-based substitution simulation**: the three stages joined by
Result 2. -/
noncomputable def substitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (hybrid P)
      (compRel (parallelRel (diracRel (broadcastSubstitutionRelationFamily P)))
        (compRel (parallelRel (diracRel (gatherSubstitutionRelationFamily P)))
          (parallelRel (diracRel (roundSpecificationSubstitutionRelationFamily P))))) :=
  (broadcastSubstitution P).trans ((gatherSubstitution P).trans (roundSpecificationSubstitution P))

/-- **The gather-based substitution inclusion**: every trace distribution
achievable by the gather-based composed system is achievable by the
protocol-shaped specification. The three stage inclusions are chained by
`Set.Subset.trans`; the inclusion never invokes transitivity of
simulation. -/
theorem substitution (P : Parameters) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P) :=
  Set.Subset.trans (broadcastSubstitution P).achievableTraceDists_subset
    (Set.Subset.trans (gatherSubstitution P).achievableTraceDists_subset
      (roundSpecificationSubstitution P).achievableTraceDists_subset)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.AFW.substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substitution

end AFW

end ABA
end PLTS
