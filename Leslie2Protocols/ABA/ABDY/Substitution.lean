/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ABDY.Composition
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# The substitution to the protocol-shaped specification

The composed system of `ABA/ABDY/Composition.lean` and `hybrid` (`ABA/Composition/Hybrid.lean`)
run the same four components in the same pipeline, and differ in one of them: the composed system
runs the round-indexed family of ABDY22's graded-agreement instances where `hybrid` runs the family
of round specifications. `ABDY.composed` is therefore carried to `hybrid` in one stage.

`familySubstitution` is that stage at the exchanged component. It replaces each round's instance by
that round's specification, round by round, under the family congruence `ForwardSimulation.family`
of `Framework/FamilySimulation.lean`. Its three premises are the per-round simulation
`GBCA.ByABDY.refinesSpecification`, the preservation of the relation by the corruption broadcast,
`GBCA.ByABDY.refinesSpecification_failAct`, and the first step at an untouched round,
`GBCA.ByABDY.refinesSpecification_untouchedFirstStep`. Its relation, `substitutionRelationFamily`,
asks that the two families record the same broadcasts and have the same rounds in their maps, and
that the per-round relation `GBCA.ByABDY.specificationRelation` hold at every round.

`ABDY.substitutionSimulation` applies the four congruences of the composed system's pipeline to
that family simulation, under the composed system's own context:
`ProbabilisticForwardSimulation.parallel_right` for the three untouched components, `abstract` for
the synchronisation labels, `relabel` for the read-back over `Label n`
(`Framework/Relabel.lean`), and `abstract` again for the sub-protocol API. `ABDY.substitution` is
the inclusion of the composed system's achievable trace distributions in those of `hybrid`, and
`ABA/Results.lean` chains it with the inclusions on either side to state the headlines.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-- The relation of the family substitution: the two families record the same broadcasts and have
the same rounds in their maps, and every round's instance state is related to that round's
specification state by `GBCA.ByABDY.specificationRelation`. -/
def substitutionRelationFamily (P : Parameters)
    (s : InstanceFamilyState (GBCA.ByABDY.RoundState.initial P.n) (GBCA.ByABDY.corruptionAct P))
    (t : GBCASpecificationFamilyState P GBCA.ByABDY.Message) : Prop :=
  s.broadcasts = t.broadcasts ∧ s.instanceMap.keys = t.instanceMap.keys ∧
    ∀ r, GBCA.ByABDY.specificationRelation P r (s r) (t r)

/-- **The family substitution**: the graded-agreement family of the protocol is forward simulated by
the specification family, round by round. The per-round simulation is
`GBCA.ByABDY.refinesSpecification`, the broadcast compatibility is
`GBCA.ByABDY.refinesSpecification_failAct`, and the first step at an untouched round is
`GBCA.ByABDY.refinesSpecification_untouchedFirstStep`. -/
theorem familySubstitution (P : Parameters) :
    ForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P)
      (gbcaSpecificationFamily P GBCA.ByABDY.Message)
      (substitutionRelationFamily P) :=
  ForwardSimulation.family GBCA.ByABDY.roundOwnsLabel GBCA.ByABDY.isFailLabel
    (GBCA.ByABDY.corruptionAct P) (GBCA.ByABDY.specificationCorruptionAct P)
    (GBCA.ByABDY.RoundState.initial P.n) (GBCA.SpecState.initial P.n)
    (GBCA.ByABDY.refinesSpecification P) (GBCA.ByABDY.refinesSpecification_failAct P)
    (GBCA.ByABDY.refinesSpecification_untouchedFirstStep P)

/-- The relation holds at the two initial states: neither family records a broadcast or holds a
round in its map, and every round reads the initial instance and the initial specification. -/
theorem substitutionRelationFamily_init (P : Parameters) :
    substitutionRelationFamily P (GBCA.ByABDY.gbcaInstanceFamily P).init
      (gbcaSpecificationFamily P GBCA.ByABDY.Message).init :=
  ⟨rfl, rfl, fun r => GBCA.ByABDY.specificationRelation_init P r⟩

/-- The family substitution as a probabilistic forward simulation: both systems are LTS, and the
relation holds at the initial states. -/
theorem familySubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P)
      (gbcaSpecificationFamily P GBCA.ByABDY.Message)
      (diracRel (substitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (GBCA.ByABDY.gbcaInstanceFamily_isLTS P)
    (gbcaSpecificationFamily_isLTS P GBCA.ByABDY.Message)
    (substitutionRelationFamily_init P) (familySubstitution P)

namespace ABDY

/-- **The substitution simulation at the protocol shape**: the four
congruences applied to the family substitution under the composed system's own
context: `parallel_right` for the three untouched components, `abstract` for
the synchronisation labels, `relabel` for the read-back over `Label n`, and
`abstract` for the sub-protocol API. -/
noncomputable def substitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (hybrid P GBCA.ByABDY.Message)
      (parallelRel (diracRel (substitutionRelationFamily P))) :=
  ((((familySubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P GBCA.ByABDY.Message)).parallel
      ((ABANetwork P GBCA.ByABDY.Message).parallel
        (coinOverRoundAlphabet P GBCA.ByABDY.Message)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- **The substitution inclusion**: every trace distribution achievable by the
composed system is achievable by the protocol-shaped specification. -/
theorem substitution (P : Parameters) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P GBCA.ByABDY.Message) :=
  (substitutionSimulation P).achievableTraceDists_subset

end ABDY

end ABA

end PLTS
