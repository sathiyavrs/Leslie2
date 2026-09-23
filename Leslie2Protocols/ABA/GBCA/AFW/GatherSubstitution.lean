/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Composition
import Leslie2Protocols.ABA.Gather.RefinesSpecification
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The gather substitution inside the round

`GBCA.ByAFW.gatherSubstitution`: the round over the gather instances over the broadcast
specification (`GBCA.ByAFW.roundOverBroadcastSpecification`) is forward simulated by the round over
the gather specifications (`GBCA.ByAFW.roundOverGatherSpecifications`), along
`GBCA.ByAFW.GatherSubstitutionRelation`: the round's programs and the round's bound bit held equal,
and each of the two gather coordinates related by the gather refinement relation
(`Gather.SpecificationRelation`).

The proof is the congruence argument alone. The two rounds are one expression over two gather
tiers, so the substitution of one gather instance is carried through the operators that expression
is built from: `ForwardSimulation.mapIdle` reads one gather instance over the round-internal
alphabet, `ForwardSimulation.parallel_right` and `ForwardSimulation.parallel_left` hold the other
gather instance and then the round's programs, and `ForwardSimulation.abstract` and
`ForwardSimulation.relabel` hide the round's events and read the result back over the family
alphabet. The two gather instances are replaced one after the other and the two steps are joined by
`ForwardSimulation.trans`. `ForwardSimulation.congr` then reshapes the composite relation: the
intermediate state the composite quantifies over is the first coordinate of the abstract system
beside the second coordinate of the concrete system.

Both rounds are LTS, so the substitution reads as an inclusion of achievable trace distributions,
`roundOverBroadcastSpecification_refines`. `gatherSubstitutionRelation_corrupt` states that the
relation is preserved by corrupting both rounds at once, in the shape the family congruence
consumes (`ForwardSimulation.family`, `hglob`); the gather instance's own compatibility lemma,
`Gather.specificationRelation_corrupt`, is in `ABA/Gather/SpecificationRelation.lean`.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

/-! ### The gather substitution -/

/-- The gather substitution relation of the round: the round's programs equal, and each gather
coordinate related to its specification coordinate by the gather refinement relation. -/
structure GatherSubstitutionRelation (P : Parameters) (s : RoundStateOverBroadcastSpecification P.n)
    (t : RoundStateOverGatherSpecifications P.n) : Prop where
  /-- The programs and the round's bound bit are untouched by the
  substitution. -/
  roundPrograms_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  firstGatherRelation : Gather.SpecificationRelation P (firstGather s) (firstGather t)
  /-- The second gather coordinate is substituted. -/
  secondGatherRelation : Gather.SpecificationRelation P (secondGather s) (secondGather t)

/-- The relation holds initially. -/
theorem gatherSubstitutionRelation_init (P : Parameters) (r : ℕ) :
    GatherSubstitutionRelation P (roundOverBroadcastSpecification P r).init
      (roundOverGatherSpecifications P r).init
      :=
  ⟨rfl, Gather.specificationRelation_init, Gather.specificationRelation_init⟩

/-- **The gather substitution inside the round.** The round over the gather
instances over the broadcast specification is forward simulated by the round
over the gather specifications. -/
theorem gatherSubstitution (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverBroadcastSpecification P r) (roundOverGatherSpecifications P r)
      (GatherSubstitutionRelation P) := by
  have h1 : ForwardSimulation ((Gather.instanceOverBroadcastSpecification P Bool).mapIdle
    (firstGatherLabelMap P.n))
      ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap P.n))
        (Gather.SpecificationRelation P) :=
    ForwardSimulation.mapIdle (firstGatherLabelMap P.n) (firstGatherLabelMap_tau P.n)
      (fun _ h => firstGatherLabelMap_eq_tau h) (Gather.refinesSpecification P Bool)
  have h2 : ForwardSimulation ((Gather.instanceOverBroadcastSpecification P (Option Bool)).mapIdle
    (secondGatherLabelMap P.n))
      ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle (secondGatherLabelMap
        P.n)) (Gather.SpecificationRelation P) :=
    ForwardSimulation.mapIdle (secondGatherLabelMap P.n) (secondGatherLabelMap_tau P.n)
      (fun _ h => secondGatherLabelMap_eq_tau h) (Gather.refinesSpecification P (Option Bool))
  have hGa := (h1.parallel_right ((Gather.instanceOverBroadcastSpecification P (Option
    Bool)).mapIdle (secondGatherLabelMap P.n))).trans
    (h2.parallel_left ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle
      (firstGatherLabelMap P.n)))
  have hRound := ((hGa.parallel_left (roundPrograms P r)).abstract (roundEvents P.n)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hRound
  constructor
  · rintro ⟨hRoundPrograms, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hRoundPrograms, h1', h2'⟩
  · rintro ⟨hRoundPrograms, h1', h2'⟩
    exact ⟨hRoundPrograms, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather instances over
the broadcast specification in the round over the gather specifications. -/
theorem roundOverBroadcastSpecification_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBroadcastSpecification P r) ⊆ achievableTraceDists
      (roundOverGatherSpecifications P r) :=
  (ForwardSimulation.toProbabilistic (roundOverBroadcastSpecification_isLTS P r)
    (roundOverGatherSpecifications_isLTS P r)
    (gatherSubstitutionRelation_init P r) (gatherSubstitution P r)).achievableTraceDists_subset

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility of the gather substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem gatherSubstitutionRelation_corrupt {P : Parameters}
    {s : RoundStateOverBroadcastSpecification P.n} {t : RoundStateOverGatherSpecifications P.n}
    (hR : GatherSubstitutionRelation P s t) (id : Fin P.n) :
    GatherSubstitutionRelation P
      (corruptAll P id
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        s)
      (corruptAll P id (fun i => Gather.SpecState.corrupt P i)
        (fun i => Gather.SpecState.corrupt P i) t) :=
  ⟨hR.roundPrograms_eq, Gather.specificationRelation_corrupt hR.firstGatherRelation id,
    Gather.specificationRelation_corrupt hR.secondGatherRelation id⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.gatherSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherSubstitution

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverBroadcastSpecification_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBroadcastSpecification_refines

end GBCA.ByAFW
end ABA
end PLTS
