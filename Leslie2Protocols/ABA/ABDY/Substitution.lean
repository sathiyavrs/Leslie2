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
that round's specification, round by round, out of the per-round simulation
`GBCA.ByABDY.refinesSpecification` and the broadcast compatibility
`GBCA.ByABDY.refinesSpecification_failAct`, under the family lifting of
`Framework/FamilySimulation.lean`. Its relation, `substitutionRelationFamily`, asks the per-round
relation of `GBCA.ByABDY.specificationRelation` at every round and is unguarded.

`ABDY.substitutionSimulation` applies the four congruences of the composed system's pipeline to
that family simulation, under the composed system's own context:
`ProbabilisticForwardSimulation.parallel_right` for the three untouched components, `abstract` for
the synchronisation labels, `relabel` for the read-back over `Label n`
(`Framework/Relabel.lean`), and `abstract` again for the sub-protocol API. `ABDY.substitution` is
the inclusion of the composed system's achievable trace distributions in those of `hybrid`, and
`ABA/Results.lean` chains it with the earlier and the later inclusions to state the headlines.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-- The pointwise round relation: every round's instance state is related to
that round's specification state. -/
def substitutionRelationFamily (P : Parameters) (s : ℕ → GBCA.ByABDY.RoundState P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GBCA.ByABDY.specificationRelation P r (s r) (t r)

/-- **The family substitution**: the graded-agreement family of the protocol is forward simulated by
the specification, round by round. The per-round simulation is `GBCA.ByABDY.refinesSpecification`;
the broadcast compatibility is `GBCA.ByABDY.refinesSpecification_failAct`. -/
theorem familySubstitution (P : Parameters) :
    ForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P)
      (gbcaSpecificationFamily P GBCA.ByABDY.Message)
      (substitutionRelationFamily P) :=
  ForwardSimulation.family GBCA.ByABDY.roundOwnsLabel GBCA.ByABDY.isFailLabel
    (GBCA.ByABDY.corruptionAct P)
    (GBCA.ByABDY.specificationCorruptionAct P)
    (GBCA.ByABDY.refinesSpecification P) (GBCA.ByABDY.refinesSpecification_failAct P)

/-- The family substitution as a probabilistic forward simulation: both systems are LTS, and the
relation holds at the initial states. -/
theorem familySubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P)
      (gbcaSpecificationFamily P GBCA.ByABDY.Message)
      (diracRel (substitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (GBCA.ByABDY.gbcaInstanceFamily_isLTS P)
    (gbcaSpecificationFamily_isLTS P GBCA.ByABDY.Message)
    (fun r => GBCA.ByABDY.specificationRelation_init P r) (familySubstitution P)

namespace ABDY

/-- **The substitution simulation at the protocol shape**: the four
congruences applied to the family substitution under the composed system's own
context — `parallel_right` for the three untouched components, `abstract` for
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
