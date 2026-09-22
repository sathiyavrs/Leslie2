/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Composition
import Leslie2Protocols.ABA.Gather.BroadcastSubstitution
import Leslie2Protocols.ABA.Gather.RefinesSpecification
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The two gather substitutions inside the round

The round over the gather instances over Bracha's broadcast (`GBCA.ByAFW.roundOverBracha`) is
forward simulated by the round over the gather instances over the broadcast specification
(`GBCA.ByAFW.roundOverBroadcastSpecification`), and that one by the round over the gather
specifications (`GBCA.ByAFW.roundOverGatherSpecifications`). The two relations are
`GBCA.ByAFW.BroadcastSubstitutionRelation` and `GBCA.ByAFW.GatherSubstitutionRelation`: the round's
programs held equal, and each of the two gather coordinates related by the substitution of that tier
(`Gather.BroadcastSubstitutionRelation`, `Gather.SpecificationRelation`).

Each proof is the congruence argument alone. The three rounds are one expression over three gather
tiers, so the gather substitution is carried through the operators that expression is built from:
`ForwardSimulation.mapIdle` reads one gather instance over the round-internal alphabet,
`ForwardSimulation.parallel_right` and `ForwardSimulation.parallel_left` hold the other gather
instance and then the round's programs, and `ForwardSimulation.abstract` and
`ForwardSimulation.relabel` hide the round's events and read the result back over the family
alphabet. The two gather instances are replaced one after the other and the two steps are joined by
`ForwardSimulation.trans`. `ForwardSimulation.congr` then reshapes the composite relation: the
intermediate state the composite quantifies over is the first coordinate of the abstract system
beside the second coordinate of the concrete system.

All three rounds are LTS, so each substitution reads as an inclusion of
achievable trace distributions.

`Gather.broadcastSubstitutionRelation_corrupt`, `GBCA.ByAFW.broadcastSubstitutionRelation_corrupt`
and `GBCA.ByAFW.gatherSubstitutionRelation_corrupt` state that each relation is preserved by
corrupting both systems at once, in the shape the family congruence consumes
(`ForwardSimulation.family`, `hglob`). -/

namespace PLTS
namespace ABA

namespace Gather

/-- **Broadcast compatibility at the gather instance**: the broadcast
substitution relation is preserved by corrupting both instances at once. -/
theorem broadcastSubstitutionRelation_corrupt {X : Type} [DecidableEq X] {P : Parameters} {s :
  StateOverBracha P.n X}
    {t : StateOverBroadcastSpecification P.n X} (hR : BroadcastSubstitutionRelation P s t) (id : Fin
      P.n) :
    BroadcastSubstitutionRelation P (corruptAll P id (InstanceState.corrupt P id)
      (InstanceState.corrupt P id) s)
      (corruptAll P id (BRB.SpecState.corrupt P id) (BRB.SpecState.corrupt P id) t) :=
  ⟨congrArg (fun x => (x.1, { x.2 with network := x.2.network.corrupt P id })) hR.gatherTier_eq,
    fun k => BRB.specificationRelation_corrupt (hR.inputBroadcastRelation k) id,
    fun q => BRB.specificationRelation_corrupt (hR.bindBroadcastRelation q) id⟩

end Gather

namespace GBCA.ByAFW

/-! ### The broadcast substitution -/

/-- The broadcast substitution relation of the round: the round's programs equal, and each gather
coordinate related to its broadcast-specification coordinate by the gather substitution relation. -/
structure BroadcastSubstitutionRelation (P : Parameters) (s : RoundStateOverBracha P.n) (t :
  RoundStateOverBroadcastSpecification P.n) : Prop where
  /-- The programs and the round's bound bit are untouched by the
  substitution. -/
  roundPrograms_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  firstGatherRelation : Gather.BroadcastSubstitutionRelation P (firstGather s) (firstGather t)
  /-- The second gather coordinate is substituted. -/
  secondGatherRelation : Gather.BroadcastSubstitutionRelation P (secondGather s) (secondGather t)

/-- The relation holds initially. -/
theorem broadcastSubstitutionRelation_init (P : Parameters) (r : ℕ) :
    BroadcastSubstitutionRelation P (roundOverBracha P r).init (roundOverBroadcastSpecification P
      r).init :=
  ⟨rfl, Gather.broadcastSubstitutionRelation_init, Gather.broadcastSubstitutionRelation_init⟩

/-- **The broadcast substitution inside the round.** The round over the gather
instances over Bracha's broadcast is forward simulated by the round over the
gather instances over the broadcast specification. Each gather coordinate
carries the substitution; the congruences carry it through the round. -/
theorem broadcastSubstitution (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverBracha P r) (roundOverBroadcastSpecification P r)
      (BroadcastSubstitutionRelation P) :=
      by
  have h1 : ForwardSimulation ((Gather.instanceOverBracha P Bool).mapIdle (firstGatherLabelMap P.n))
      ((Gather.instanceOverBroadcastSpecification P Bool).mapIdle (firstGatherLabelMap P.n))
        (Gather.BroadcastSubstitutionRelation P) :=
    ForwardSimulation.mapIdle (firstGatherLabelMap P.n) (firstGatherLabelMap_tau P.n)
      (fun _ h => firstGatherLabelMap_eq_tau h) (Gather.broadcastSubstitution P Bool)
  have h2 : ForwardSimulation ((Gather.instanceOverBracha P (Option Bool)).mapIdle
    (secondGatherLabelMap P.n))
      ((Gather.instanceOverBroadcastSpecification P (Option Bool)).mapIdle (secondGatherLabelMap
        P.n)) (Gather.BroadcastSubstitutionRelation P) :=
    ForwardSimulation.mapIdle (secondGatherLabelMap P.n) (secondGatherLabelMap_tau P.n)
      (fun _ h => secondGatherLabelMap_eq_tau h) (Gather.broadcastSubstitution P (Option Bool))
  have hGa := (h1.parallel_right ((Gather.instanceOverBracha P (Option Bool)).mapIdle
    (secondGatherLabelMap P.n))).trans
    (h2.parallel_left ((Gather.instanceOverBroadcastSpecification P Bool).mapIdle
      (firstGatherLabelMap P.n)))
  have hRound := ((hGa.parallel_left (roundPrograms P r)).abstract (roundEvents P.n)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hRound
  constructor
  · rintro ⟨hlayer, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hlayer, h1', h2'⟩
  · rintro ⟨hlayer, h1', h2'⟩
    exact ⟨hlayer, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### The gather substitution -/

/-- The gather substitution relation of the round: the round's programs equal, and each gather
coordinate related to its specification coordinate by the gather refinement relation. -/
structure GatherSubstitutionRelation (P : Parameters) (s : RoundStateOverBroadcastSpecification P.n)
  (t :
  RoundStateOverGatherSpecifications P.n) : Prop where
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
  · rintro ⟨hlayer, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hlayer, h1', h2'⟩
  · rintro ⟨hlayer, h1', h2'⟩
    exact ⟨hlayer, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather instances over
Bracha's broadcast in the round over the gather instances over the broadcast
specification. -/
theorem roundOverBracha_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBracha P r) ⊆ achievableTraceDists
      (roundOverBroadcastSpecification P r) :=
  (ForwardSimulation.toProbabilistic (roundOverBracha_isLTS P r)
    (roundOverBroadcastSpecification_isLTS P r)
    (broadcastSubstitutionRelation_init P r) (broadcastSubstitution P
      r)).achievableTraceDists_subset

/-- Trace-distribution inclusion of the round over the gather instances over
the broadcast specification in the round over the gather specifications. -/
theorem roundOverBroadcastSpecification_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBroadcastSpecification P r) ⊆ achievableTraceDists
      (roundOverGatherSpecifications P r) :=
  (ForwardSimulation.toProbabilistic (roundOverBroadcastSpecification_isLTS P r)
    (roundOverGatherSpecifications_isLTS P r)
    (gatherSubstitutionRelation_init P r) (gatherSubstitution P r)).achievableTraceDists_subset

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility of the broadcast substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem broadcastSubstitutionRelation_corrupt {P : Parameters} {s : RoundStateOverBracha P.n} {t :
  RoundStateOverBroadcastSpecification P.n}
    (hR : BroadcastSubstitutionRelation P s t) (id : Fin P.n) :
    BroadcastSubstitutionRelation P
      (corruptAll P id
        (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i))
        (fun i => Gather.corruptAll P i (InstanceState.corrupt P i) (InstanceState.corrupt P i)) s)
      (corruptAll P id
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        t) :=
  ⟨hR.roundPrograms_eq, Gather.broadcastSubstitutionRelation_corrupt hR.firstGatherRelation id,
    Gather.broadcastSubstitutionRelation_corrupt hR.secondGatherRelation id⟩

/-- **Broadcast compatibility of the gather substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem gatherSubstitutionRelation_corrupt {P : Parameters} {s :
  RoundStateOverBroadcastSpecification P.n} {t :
  RoundStateOverGatherSpecifications P.n}
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

/-- info: 'PLTS.ABA.GBCA.ByAFW.broadcastSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms broadcastSubstitution

/-- info: 'PLTS.ABA.GBCA.ByAFW.gatherSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherSubstitution

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverBracha_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_refines

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverBroadcastSpecification_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBroadcastSpecification_refines

end GBCA.ByAFW
end ABA
end PLTS
