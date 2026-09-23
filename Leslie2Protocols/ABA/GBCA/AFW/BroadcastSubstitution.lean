/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Composition
import Leslie2Protocols.ABA.Gather.BroadcastSubstitution
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The broadcast substitution inside the round

`GBCA.ByAFW.broadcastSubstitution`: the round over the gather instances over Bracha's broadcast
(`GBCA.ByAFW.roundOverBracha`) is forward simulated by the round over the gather instances over the
broadcast specification (`GBCA.ByAFW.roundOverBroadcastSpecification`), along
`GBCA.ByAFW.BroadcastSubstitutionRelation`: the round's programs and the round's bound bit held
equal, and each of the two gather coordinates related by the broadcast substitution of that tier
(`Gather.BroadcastSubstitutionRelation`).

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
`roundOverBracha_refines`. `broadcastSubstitutionRelation_corrupt` states that the relation is
preserved by corrupting both rounds at once, in the shape the family congruence consumes
(`ForwardSimulation.family`, `hglob`); the gather instance's own compatibility lemma,
`Gather.broadcastSubstitutionRelation_corrupt`, is in `ABA/Gather/BroadcastSubstitution.lean`.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

/-! ### The broadcast substitution -/

/-- The broadcast substitution relation of the round: the round's programs equal, and each gather
coordinate related to its broadcast-specification coordinate by the gather substitution relation. -/
structure BroadcastSubstitutionRelation (P : Parameters) (s : RoundStateOverBracha P.n)
    (t : RoundStateOverBroadcastSpecification P.n) : Prop where
  /-- The programs and the round's bound bit are untouched by the
  substitution. -/
  roundPrograms_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  firstGatherRelation : Gather.BroadcastSubstitutionRelation P (firstGather s) (firstGather t)
  /-- The second gather coordinate is substituted. -/
  secondGatherRelation : Gather.BroadcastSubstitutionRelation P (secondGather s) (secondGather t)

/-- The relation holds initially. -/
theorem broadcastSubstitutionRelation_init (P : Parameters) (r : ℕ) :
    BroadcastSubstitutionRelation P (roundOverBracha P r).init
    (roundOverBroadcastSpecification P r).init :=
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
  · rintro ⟨hRoundPrograms, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hRoundPrograms, h1', h2'⟩
  · rintro ⟨hRoundPrograms, h1', h2'⟩
    exact ⟨hRoundPrograms, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

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

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility of the broadcast substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem broadcastSubstitutionRelation_corrupt {P : Parameters} {s : RoundStateOverBracha P.n}
    {t : RoundStateOverBroadcastSpecification P.n} (hR : BroadcastSubstitutionRelation P s t)
    (id : Fin P.n) :
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

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.broadcastSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms broadcastSubstitution

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverBracha_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_refines

end GBCA.ByAFW
end ABA
end PLTS
