/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Composition
import Leslie2Protocols.ABA.Gather.RefinesSpecification
import Leslie2Protocols.ABA.ReliableBroadcast.BrachaRefinesSpecification
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The broadcast substitution inside the gather instance

`Gather.broadcastSubstitution`: the gather instance over Bracha's broadcast
(`Gather.instanceOverBracha`) is forward simulated by the gather instance over the broadcast
specification (`Gather.instanceOverBroadcastSpecification`), along
`Gather.BroadcastSubstitutionRelation` — the gather tier held equal, and each broadcast coordinate
related to its specification coordinate by the BRB refinement relation (`BRB.SpecificationRelation`,
`ABA/ReliableBroadcast/BrachaRefinesSpecification.lean`).

The proof is the congruence argument alone. The two instances are one expression over two broadcast
tiers, so the BRB refinement (`BRB.brachaRefinesSpecification`) is carried through the operators
that expression is built from: `ForwardSimulation.mapIdle` reads one coordinate over the
composition's alphabet, `ForwardSimulation.synchronisedProduct` collects the coordinates of one
family, `ForwardSimulation.parallel_right` and `ForwardSimulation.parallel_left` hold the other
family and then the gather tier, and `ForwardSimulation.abstract` and `ForwardSimulation.relabel`
hide the events and read the result back over the interface alphabet. The two families are replaced
one after the other and the two steps are joined by `ForwardSimulation.trans`.
`ForwardSimulation.congr` then reshapes the composite relation into `BroadcastSubstitutionRelation`:
the intermediate state the composite quantifies over is the input coordinates of the abstract system
beside the bind coordinates of the concrete system.

Both instances are LTS, so `instanceOverBracha_refines` reads the substitution as an
inclusion of achievable trace distributions.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The relation -/

/-- The broadcast substitution relation: the gather tier equal, and each
broadcast coordinate related to its specification coordinate by the BRB
refinement relation. -/
structure BroadcastSubstitutionRelation (P : Parameters) (s : StateOverBracha P.n X) (t :
  StateOverBroadcastSpecification
  P.n
  X) : Prop where
  /-- The gather programs and the gather network state are untouched by the
  substitution. -/
  gatherTier_eq : s.1 = t.1
  /-- Each input coordinate is BRB-refined. -/
  inputBroadcastRelation : ∀ k,
    BRB.SpecificationRelation P k (inputBroadcasts s k) (inputBroadcasts t k)
  /-- Each bind coordinate is BRB-refined. -/
  bindBroadcastRelation : ∀ q,
    BRB.SpecificationRelation P q (bindBroadcasts s q) (bindBroadcasts t q)

/-- The relation holds initially. -/
theorem broadcastSubstitutionRelation_init : BroadcastSubstitutionRelation P (instanceOverBracha P
  X).init (instanceOverBroadcastSpecification P
  X).init :=
  ⟨rfl, fun _ => BRB.specificationRelation_init, fun _ => BRB.specificationRelation_init⟩

/-! ### The substitution -/

/-- **The broadcast substitution.** The gather instance over Bracha's broadcast
is forward simulated by the gather instance over the broadcast specification.
Each coordinate carries the BRB refinement; the congruences carry it through
the composition. -/
theorem broadcastSubstitution (P : Parameters) (X : Type) [DecidableEq X] :
    ForwardSimulation (instanceOverBracha P X) (instanceOverBroadcastSpecification P X)
      (BroadcastSubstitutionRelation P)
      := by
  have hIn : ∀ k : Fin P.n,
      ForwardSimulation ((BRB.brachaInstance P k X).mapIdle (inputBroadcastLabelMap P.n X k))
        ((BRB.specificationOverInstanceAlphabet P k X).mapIdle (inputBroadcastLabelMap P.n X k))
          (BRB.SpecificationRelation P k) :=
    fun k => ForwardSimulation.mapIdle (inputBroadcastLabelMap P.n X k) (inputBroadcastLabelMap_tau
      P.n X k)
      (fun _ h => inputBroadcastLabelMap_eq_tau h) (BRB.brachaRefinesSpecification P k)
  have hBind : ∀ q : Fin P.n,
      ForwardSimulation ((BRB.brachaInstance P q (AcceptedPairs P.n X)).mapIdle
        (bindBroadcastLabelMap P.n X
        q))
        ((BRB.specificationOverInstanceAlphabet P q (AcceptedPairs P.n X)).mapIdle
          (bindBroadcastLabelMap
          P.n X q)) (BRB.SpecificationRelation P q) :=
    fun q => ForwardSimulation.mapIdle (bindBroadcastLabelMap P.n X q) (bindBroadcastLabelMap_tau
      P.n X q)
      (fun _ h => bindBroadcastLabelMap_eq_tau h) (BRB.brachaRefinesSpecification P q)
  have hSyncIn := ForwardSimulation.synchronisedProduct hIn
  have hSyncBind := ForwardSimulation.synchronisedProduct hBind
  have hBroad := (hSyncIn.parallel_right
      (System.synchronisedProduct fun q => (BRB.brachaInstance P q (AcceptedPairs P.n X)).mapIdle
        (bindBroadcastLabelMap P.n X q))).trans
    (hSyncBind.parallel_left
      (System.synchronisedProduct fun k => (BRB.specificationOverInstanceAlphabet P k X).mapIdle
        (inputBroadcastLabelMap P.n X k)))
  have hSub := ((hBroad.parallel_left (gatherPrograms P X)).abstract (gatherEvents P.n X)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hSub
  constructor
  · rintro ⟨hga, ⟨b₁, b₂⟩, ⟨hin, rfl⟩, rfl, hbind⟩
    exact ⟨hga, hin, hbind⟩
  · rintro ⟨hga, hin, hbind⟩
    exact ⟨hga, (t.2.1, s.2.2), ⟨hin, rfl⟩, rfl, hbind⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the gather instance over Bracha's broadcast
in the gather instance over the broadcast specification. -/
theorem instanceOverBracha_refines (P : Parameters) (X : Type) [DecidableEq X] :
    achievableTraceDists (instanceOverBracha P X) ⊆ achievableTraceDists
      (instanceOverBroadcastSpecification P X) :=
  (ForwardSimulation.toProbabilistic (instanceOverBracha_isLTS P)
    (instanceOverBroadcastSpecification_isLTS P)
    broadcastSubstitutionRelation_init (broadcastSubstitution P X)).achievableTraceDists_subset

/-- **The common core at the gather instance over Bracha's broadcasts**: every
return of a positive-probability trace names a set of at least `n − f` entries
below the returned map, and every return names the same set. The two
substitutions carry it down from the specification. -/
theorem instanceOverBracha_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (instanceOverBracha P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map toSpecificationLabel) :=
  safety_transfer (Set.Subset.trans (instanceOverBracha_refines P X)
    (instanceOverBroadcastSpecification_refines P X))
    (specificationOverInstanceAlphabet_core P X)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.broadcastSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms broadcastSubstitution

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_refines

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_core

end Gather
end ABA
end PLTS
