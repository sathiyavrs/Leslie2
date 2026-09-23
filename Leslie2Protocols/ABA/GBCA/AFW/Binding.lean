/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitutions
import Leslie2Protocols.ABA.GBCA.BindingOverRoundAlphabet
import Leslie2.Results

/-!
# Binding of the three tiers of the two-gather round

The three tiers of the two-gather round reach `GBCA.specificationOverRoundAlphabet`, the graded
agreement specification read over the family alphabet, through `GBCA.ByAFW.refinesSpecification`
and the two substitutions of `GBCA/AFW/GatherSubstitutions.lean`.
`roundOverGatherSpecifications_refines`, `roundOverBroadcastSpecification_specificationTraces` and
`roundOverBracha_specificationTraces` are the trace-distribution inclusions of the three, and
`roundOverBracha_refinesSpecification` is the composite simulation the lowest one rests on.

Binding is a property of the labels (`GBCA.BindingTraceExtended`), so each inclusion carries it
from `GBCA.specificationOverRoundAlphabet_binding`: `roundOverGatherSpecifications_binding`,
`roundOverBroadcastSpecification_binding` and `roundOverBracha_binding` are binding at the three
tiers.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

open Implementation Composition GBCA.ByAFW

variable {P : Parameters} {r : ℕ}

/-! ### Trace-distribution inclusion

The lifted specification is reached by two independent routes.
`roundOverGatherSpecifications_refines` and `roundOverBroadcastSpecification_specificationTraces`
chain inclusions by `Set.Subset.trans`; `roundOverBracha_refinesSpecification` composes the three
simulations themselves by `ProbabilisticForwardSimulation.trans`, and
`roundOverBracha_specificationTraces` is the inclusion it yields. The chained inclusions never
invoke transitivity of simulation. -/

/-- Trace-distribution inclusion of the round over the gather specifications in
the specification read over the round's interface, the soundness of
`refinesSpecification`. -/
theorem roundOverGatherSpecifications_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverGatherSpecifications P r) ⊆ achievableTraceDists
      (specificationOverRoundAlphabet P r) :=
  (ForwardSimulation.toProbabilistic (roundOverGatherSpecifications_isLTS P r)
    (specificationOverRoundAlphabet_isLTS P r)
    (specificationRelation_init P r) (refinesSpecification P r)).achievableTraceDists_subset

/-- **The round over the gather instances over Bracha's broadcast refines the
specification**: the two substitutions and the counting simulation, each taken
probabilistically, joined by Result 2
(`ProbabilisticForwardSimulation.trans`). -/
theorem roundOverBracha_refinesSpecification (P : Parameters) (r : ℕ) :
    ProbabilisticForwardSimulation (roundOverBracha P r) (specificationOverRoundAlphabet
      P r)
      (compRel (diracRel (BroadcastSubstitutionRelation P))
        (compRel (diracRel (GatherSubstitutionRelation P)) (diracRel (SpecificationRelation P)))) :=
  (ForwardSimulation.toProbabilistic (roundOverBracha_isLTS P r)
    (roundOverBroadcastSpecification_isLTS P r)
      (broadcastSubstitutionRelation_init P r) (broadcastSubstitution P r)).trans
    ((ForwardSimulation.toProbabilistic (roundOverBroadcastSpecification_isLTS P r)
      (roundOverGatherSpecifications_isLTS P r)
        (gatherSubstitutionRelation_init P r) (gatherSubstitution P r)).trans
      (ForwardSimulation.toProbabilistic (roundOverGatherSpecifications_isLTS P r)
        (specificationOverRoundAlphabet_isLTS P r)
        (specificationRelation_init P r) (refinesSpecification P r)))

/-- The soundness inclusion of the round: every trace distribution
achievable by the round over the gather instances over Bracha's broadcast is
achievable by the lifted specification. -/
theorem roundOverBracha_specificationTraces (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBracha P r) ⊆ achievableTraceDists
      (specificationOverRoundAlphabet P r) :=
  (roundOverBracha_refinesSpecification P r).achievableTraceDists_subset

/-- The soundness inclusion of the gather substitution above the counting
simulation: every trace distribution achievable by the round over the gather
instances over the broadcast specification is achievable by the lifted
specification. -/
theorem roundOverBroadcastSpecification_specificationTraces (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBroadcastSpecification P r) ⊆ achievableTraceDists
      (specificationOverRoundAlphabet P r) :=
  Set.Subset.trans (roundOverBroadcastSpecification_refines P r)
    (roundOverGatherSpecifications_refines P r)

/-! ### Binding of the three tiers -/

/-- **Binding of the round over the gather specifications, on a trace.** Every
positive-probability trace of the round is bound to one bit: all its round-`r`
returns announce that bit, and every one of them that hands out a value hands
out it. Binding is a property of the labels (`BindingTraceExtended`), so
`roundOverGatherSpecifications_refines` carries it from
`specificationOverRoundAlphabet_binding`. -/
theorem roundOverGatherSpecifications_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (roundOverGatherSpecifications P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t :=
  safety_transfer (roundOverGatherSpecifications_refines P r)
    (specificationOverRoundAlphabet_binding P r)

/-- **Binding of the round over the gather instances over the broadcast
specification, on a trace**, along the inclusion
`roundOverBroadcastSpecification_specificationTraces`. -/
theorem roundOverBroadcastSpecification_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (roundOverBroadcastSpecification P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t :=
  safety_transfer (roundOverBroadcastSpecification_specificationTraces P r)
    (specificationOverRoundAlphabet_binding P r)

/-- **Binding of the round over the gather instances over Bracha's broadcast,
on a trace**, along the three-tier inclusion `roundOverBracha_specificationTraces`. -/
theorem roundOverBracha_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (roundOverBracha P r), ∀ t, D t ≠ 0 →
      BindingTraceExtended P r t :=
  safety_transfer (roundOverBracha_specificationTraces P r) (specificationOverRoundAlphabet_binding
    P r)

/-! ### Mechanical axiom check

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.GBCA.specificationOverRoundAlphabet_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationOverRoundAlphabet_binding

/-- info: 'PLTS.ABA.GBCA.roundOverBracha_refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_refinesSpecification

/-- info: 'PLTS.ABA.GBCA.roundOverBracha_specificationTraces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_specificationTraces

/-- info: 'PLTS.ABA.GBCA.roundOverGatherSpecifications_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverGatherSpecifications_binding

/-- info: 'PLTS.ABA.GBCA.roundOverBroadcastSpecification_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBroadcastSpecification_binding

/-- info: 'PLTS.ABA.GBCA.roundOverBracha_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_binding

end GBCA
end ABA
end PLTS
