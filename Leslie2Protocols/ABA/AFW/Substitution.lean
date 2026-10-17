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

1. `broadcastSubstitution`: from the rounds over the gather instances over Bracha's broadcast to
   the rounds over the gather instances over the broadcast specification;
2. `gatherSubstitution`: into the rounds over the gather specifications;
3. `roundSpecificationSubstitution`: the counting simulation, into the round specifications.

The third stage lands on `hybrid P` itself, which is where the gather-based chain meets the chain
of `ABDY.composed` and takes the shared simulation `hybridRefinesSpecification`
(`HybridRefinesSpecification/Simulation.lean`) to the ABA specification.

## How a stage is built

`familyBroadcastSubstitution` and its two companions lift a per-round simulation,
`GBCA.ByAFW.broadcastSubstitution`, `GBCA.ByAFW.gatherSubstitution` and
`GBCA.ByAFW.refinesSpecification`, to the family under the family congruence
`ForwardSimulation.family` of `Framework/FamilySimulation.lean`. Its relation asks that the two
families record the same broadcasts and have the same rounds in their maps, and that the per-round
relation hold at every round. It has two premises besides the per-round simulation. The relation
is preserved by the corruption broadcast: `broadcastSubstitution_failAct`,
`gatherSubstitution_failAct` and `roundSpecificationSubstitution_failAct` are the rounds' own
simultaneous-corruption statements, taken on the extended `fail` label. A transition at a round
outside the map is matched by a transition on its label followed by a silent run:
`GBCA.ByAFW.broadcastSubstitution_untouchedFirstStep`,
`GBCA.ByAFW.gatherSubstitution_untouchedFirstStep` and
`GBCA.ByAFW.refinesSpecification_untouchedFirstStep`, at the corruption actions and the initial
round states of `ABA/AFW/Composition.lean`. The four congruences of the pipeline then carry each
family simulation under the composed system's own context:
`ProbabilisticForwardSimulation.parallel_right` for the three untouched components, `abstract` for
the synchronisation labels, `relabel` for the read-back over `Label n`
(`Framework/Relabel.lean`), and `abstract` again for the sub-protocol API.

`AFW.substitution` is the inclusion of the gather-based composed system's achievable trace
distributions in those of `hybrid`, the three stage inclusions chained by `Set.Subset.trans`, and
`ABA/Results.lean` chains it with the inclusions on either side to state the headlines of the
gather-based chain.
-/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

namespace AFW

/-! ## Broadcast compatibility

The three relations are preserved by the corruption broadcast: the rounds' own
simultaneous-corruption statements, taken on the extended `fail` label. -/

/-- Corruption preserves the broadcast substitution relation. -/
theorem broadcastSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n Empty, isFailLabel l →
      ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBracha P.n)
      (y : GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n),
        GBCA.ByAFW.BroadcastSubstitutionRelation P x y →
      GBCA.ByAFW.BroadcastSubstitutionRelation P (corruptionOverBracha P l x)
        (corruptionOverBroadcastSpecification P l y) := by
  rintro l hl _ x y hR
  rcases l with l₀ | e
  · cases l₀ with
    | fail k => exact GBCA.ByAFW.broadcastSubstitutionRelation_corrupt hR k
    | _ => exact hl.elim
  · exact hl.elim

/-- Corruption preserves the gather substitution relation. -/
theorem gatherSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n Empty,
      isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverBroadcastSpecification P.n)
        (y : GBCA.ByAFW.RoundStateOverGatherSpecifications P.n),
          GBCA.ByAFW.GatherSubstitutionRelation P x y →
      GBCA.ByAFW.GatherSubstitutionRelation P (corruptionOverBroadcastSpecification P l x)
        (corruptionOverGatherSpecifications P l y) := by
  rintro l hl _ x y hR
  rcases l with l₀ | e
  · cases l₀ with
    | fail k => exact GBCA.ByAFW.gatherSubstitutionRelation_corrupt hR k
    | _ => exact hl.elim
  · exact hl.elim

/-- Corruption preserves the counting relation. -/
theorem roundSpecificationSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n Empty,
      isFailLabel l → ∀ (_ : ℕ) (x : GBCA.ByAFW.RoundStateOverGatherSpecifications P.n)
        (y : GBCA.SpecState P.n), GBCA.ByAFW.SpecificationRelation P x y →
      GBCA.ByAFW.SpecificationRelation P (corruptionOverGatherSpecifications P l x)
        (specificationCorruptionAct P l y) := by
  rintro l hl r x y hR
  rcases l with l₀ | e
  · cases l₀ with
    | fail k => exact GBCA.ByAFW.specificationRelation_corrupt (r := r) hR k
    | _ => exact hl.elim
  · exact hl.elim

/-! ## The family substitutions -/

/-- The relation of the first family substitution: the two families record the same broadcasts
and have the same rounds in their maps, and their rounds are related by the broadcast substitution
relation at every round. -/
def broadcastSubstitutionRelationFamily (P : Parameters) (s : RoundFamilyOverBrachaState P)
    (t : RoundFamilyOverBroadcastSpecificationState P) : Prop :=
  s.broadcasts = t.broadcasts ∧ s.instanceMap.keys = t.instanceMap.keys ∧
    ∀ r, GBCA.ByAFW.BroadcastSubstitutionRelation P (s r) (t r)

/-- The relation of the second family substitution, by the gather substitution relation. -/
def gatherSubstitutionRelationFamily (P : Parameters)
    (s : RoundFamilyOverBroadcastSpecificationState P)
    (t : RoundFamilyOverGatherSpecificationsState P) : Prop :=
  s.broadcasts = t.broadcasts ∧ s.instanceMap.keys = t.instanceMap.keys ∧
    ∀ r, GBCA.ByAFW.GatherSubstitutionRelation P (s r) (t r)

/-- The relation of the third family substitution, by the counting relation. -/
def roundSpecificationSubstitutionRelationFamily (P : Parameters)
    (s : RoundFamilyOverGatherSpecificationsState P) (t : GBCASpecificationFamilyState P Empty) :
    Prop :=
  s.broadcasts = t.broadcasts ∧ s.instanceMap.keys = t.instanceMap.keys ∧
    ∀ r, GBCA.ByAFW.SpecificationRelation P (s r) (t r)

/-- The family substitution of the first stage, round by round. -/
theorem familyBroadcastSubstitution (P : Parameters) :
    ForwardSimulation (roundFamilyOverBracha P) (roundFamilyOverBroadcastSpecification P)
    (broadcastSubstitutionRelationFamily P) :=
  ForwardSimulation.family (R := fun _ => GBCA.ByAFW.BroadcastSubstitutionRelation P)
    roundOwnsLabel isFailLabel (corruptionOverBracha P) (corruptionOverBroadcastSpecification P)
    (initialRoundStateOverBracha P) (initialRoundStateOverBroadcastSpecification P)
    (GBCA.ByAFW.broadcastSubstitution P) (broadcastSubstitution_failAct P)
    (GBCA.ByAFW.broadcastSubstitution_untouchedFirstStep P roundOwnsLabel rfl
      (corruptionOverBracha P) (corruptionOverBroadcastSpecification P)
      (initialRoundStateOverBracha P) (initialRoundStateOverBroadcastSpecification P))

/-- The family substitution of the second stage. -/
theorem familyGatherSubstitution (P : Parameters) :
    ForwardSimulation (roundFamilyOverBroadcastSpecification P)
    (roundFamilyOverGatherSpecifications P) (gatherSubstitutionRelationFamily P) :=
  ForwardSimulation.family (R := fun _ => GBCA.ByAFW.GatherSubstitutionRelation P)
    roundOwnsLabel isFailLabel (corruptionOverBroadcastSpecification P)
    (corruptionOverGatherSpecifications P) (initialRoundStateOverBroadcastSpecification P)
    (initialRoundStateOverGatherSpecifications P)
    (GBCA.ByAFW.gatherSubstitution P) (gatherSubstitution_failAct P)
    (GBCA.ByAFW.gatherSubstitution_untouchedFirstStep P roundOwnsLabel rfl
      (corruptionOverBroadcastSpecification P) (corruptionOverGatherSpecifications P)
      (initialRoundStateOverBroadcastSpecification P) (initialRoundStateOverGatherSpecifications P))

/-- The family substitution of the third stage, into the specification family. -/
theorem familyRoundSpecificationSubstitution (P : Parameters) :
    ForwardSimulation (roundFamilyOverGatherSpecifications P) (gbcaSpecificationFamily P Empty)
    (roundSpecificationSubstitutionRelationFamily P) :=
  ForwardSimulation.family (R := fun _ => GBCA.ByAFW.SpecificationRelation P)
    roundOwnsLabel isFailLabel (corruptionOverGatherSpecifications P)
    (specificationCorruptionAct P) (initialRoundStateOverGatherSpecifications P)
    (GBCA.SpecState.initial P.n)
    (GBCA.ByAFW.refinesSpecification P) (roundSpecificationSubstitution_failAct P)
    (GBCA.ByAFW.refinesSpecification_untouchedFirstStep P roundOwnsLabel rfl
      (corruptionOverGatherSpecifications P) (specificationCorruptionAct P)
      (initialRoundStateOverGatherSpecifications P) (GBCA.SpecState.initial P.n)
      (programs_corruptionOverGatherSpecifications P)
      (initialRoundStateOverGatherSpecifications_output P))

/-- The relation of the first stage holds at the two initial states: neither family records a
broadcast or holds a round in its map, and every round reads its initial state. -/
theorem broadcastSubstitutionRelationFamily_init (P : Parameters) :
    broadcastSubstitutionRelationFamily P (roundFamilyOverBracha P).init
      (roundFamilyOverBroadcastSpecification P).init :=
  ⟨rfl, rfl, fun r => GBCA.ByAFW.broadcastSubstitutionRelation_init P r⟩

/-- The relation of the second stage holds at the two initial states. -/
theorem gatherSubstitutionRelationFamily_init (P : Parameters) :
    gatherSubstitutionRelationFamily P (roundFamilyOverBroadcastSpecification P).init
      (roundFamilyOverGatherSpecifications P).init :=
  ⟨rfl, rfl, fun r => GBCA.ByAFW.gatherSubstitutionRelation_init P r⟩

/-- The relation of the third stage holds at the two initial states. -/
theorem roundSpecificationSubstitutionRelationFamily_init (P : Parameters) :
    roundSpecificationSubstitutionRelationFamily P (roundFamilyOverGatherSpecifications P).init
      (gbcaSpecificationFamily P Empty).init :=
  ⟨rfl, rfl, fun r => GBCA.ByAFW.specificationRelation_init P r⟩

/-- The first family substitution, probabilistically. -/
theorem familyBroadcastSubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverBracha P)
    (roundFamilyOverBroadcastSpecification P) (diracRel (broadcastSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverBracha_isLTS P)
    (roundFamilyOverBroadcastSpecification_isLTS P)
    (broadcastSubstitutionRelationFamily_init P) (familyBroadcastSubstitution P)

/-- The second family substitution, probabilistically. -/
theorem familyGatherSubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverBroadcastSpecification P)
      (roundFamilyOverGatherSpecifications P)
      (diracRel (gatherSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverBroadcastSpecification_isLTS P)
    (roundFamilyOverGatherSpecifications_isLTS P)
    (gatherSubstitutionRelationFamily_init P) (familyGatherSubstitution P)

/-- The third family substitution, probabilistically. -/
theorem familyRoundSpecificationSubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (roundFamilyOverGatherSpecifications P)
    (gbcaSpecificationFamily P Empty) (diracRel (roundSpecificationSubstitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (roundFamilyOverGatherSpecifications_isLTS P)
    (gbcaSpecificationFamily_isLTS P Empty)
    (roundSpecificationSubstitutionRelationFamily_init P) (familyRoundSpecificationSubstitution P)


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
specification `hybrid P`, where the gather-based chain meets the chain of
`ABDY.composed`. -/
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
`Set.Subset.trans`. -/
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
