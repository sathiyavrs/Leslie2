/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.Composition
import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2.Results

/-!
# The three-stage substitution to the protocol-shaped specification

The three composed systems of `ABA/AFW/Composition.lean` and `hybrid`
(`ABA/Composition/Hybrid.lean`) run four components in one pipeline and differ in one of them, the
graded-agreement family. Each stage replaces that family by the family above it, at every round at
once:

1. `broadcastSubstitution` — from the rounds over the gather instances over Bracha's broadcast to
   the rounds over the gather instances over the broadcast specification;
2. `gatherSubstitution` — into the rounds over the gather specifications;
3. `roundSpecificationSubstitution` — the counting simulation, into the round specifications.

The third stage lands on `hybrid P` itself, which is where the gather-based chain meets the chain
of `ABDY.composed` and takes the shared simulation `hybridRefinesSpecification`
(`HybridRefinesSpecification/Simulation.lean`) to the ABA specification.

## How a stage is built

`familyBroadcastSubstitution` and its two companions lift a per-round simulation —
`GBCA.ByAFW.broadcastSubstitution`, `GBCA.ByAFW.gatherSubstitution` and
`GBCA.ByAFW.refinesSpecification` — to the family, under the family lifting of
`Framework/FamilySimulation.lean`. Its premise is that the relation survives the corruption
broadcast, and `broadcastSubstitution_failAct`, `gatherSubstitution_failAct` and
`roundSpecificationSubstitution_failAct` supply it: they are the rounds' own
simultaneous-corruption statements, taken on the extended `fail` label. The four congruences of the
pipeline then carry each family simulation under the composed system's own context —
`ProbabilisticForwardSimulation.parallel_right` for the three untouched components, `abstract` for
the rendezvous alphabet, `relabel` for the read-back over `Label n` (`Framework/Relabel.lean`), and
`abstract` again for the sub-protocol API.

`AFW.substitution` is the inclusion of the gather-based composed system's achievable trace
distributions in those of `hybrid`, the three stage inclusions chained by `Set.Subset.trans`, and
`ABA/Results.lean` chains it with the earlier and the later inclusions to state the headlines of
the gather-based chain.
-/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

namespace AFW

/-! ## Broadcast compatibility

The three relations survive the corruption broadcast: the rounds' own simultaneous-corruption
statements, taken on the extended `fail` label. -/

/-- Corruption preserves the broadcast substitution relation. -/
theorem broadcastSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n Empty, isFailLabel l →
      ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBracha P.n)
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
    ∀ l : ExtendedLabel P.n Empty,
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
    ∀ l : ExtendedLabel P.n Empty,
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

/-! ## The family substitutions -/

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
    ForwardSimulation (roundFamilyOverGatherSpecifications P) (gbcaSpecificationFamily P Empty)
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
    (gbcaSpecificationFamily P Empty) (diracRel (roundSpecificationSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverGatherSpecifications_isLTS P)
    (gbcaSpecificationFamily_isLTS P Empty)
    (fun r => GBCA.ByAFW.specificationRelation_init P r) (familyRoundSpecificationSubstitution P)

/-! ## The three-stage substitution -/

/-- The first stage at the protocol shape: the four congruences applied to the
first family substitution under the composed system's own context. -/
noncomputable def broadcastSubstitution (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (composedOverBroadcastSpecification P)
      (parallelRel (diracRel (broadcastSubstitutionRelationFamily P))) :=
  ((((familyBroadcastSubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The second stage at the protocol shape. -/
noncomputable def gatherSubstitution (P : Parameters) :
    ProbabilisticForwardSimulation (composedOverBroadcastSpecification P)
      (composedOverGatherSpecifications P)
      (parallelRel (diracRel (gatherSubstitutionRelationFamily P))) :=
  ((((familyGatherSubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- The third stage at the protocol shape, into the protocol-shaped
specification `hybrid P` — the point where the gather-based chain meets the
ABDY chain. -/
noncomputable def roundSpecificationSubstitution (P : Parameters) :
    ProbabilisticForwardSimulation (composedOverGatherSpecifications P) (hybrid P Empty)
      (parallelRel (diracRel (roundSpecificationSubstitutionRelationFamily P))) :=
  ((((familyRoundSpecificationSubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P Empty)).parallel
      ((ABANetwork P Empty).parallel (coinOverRoundAlphabet P Empty)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- **The gather-based substitution simulation**: the three stages joined by
Result 2. -/
noncomputable def substitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (hybrid P Empty)
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
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P Empty) :=
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
