/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Composition
import Leslie2Protocols.ABA.Gather.RefinesSpecification
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.RefinesSpecification
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The broadcast substitution inside the gather instance

`Gather.broadcastSubstitution`: the gather instance over Bracha's broadcast
(`Gather.instanceOverBracha`) is forward simulated by the gather instance over the broadcast
specification (`Gather.instanceOverBroadcastSpecification`), along
`Gather.BroadcastSubstitutionRelation`: the gather programs and network are held equal, and each
input broadcast coordinate is related to its specification coordinate by the BRB refinement relation
(`BRB.SpecificationRelation`, `ABA/ReliableBroadcast/Bracha/RefinesSpecification.lean`).

The proof is the congruence argument alone. The two instances are one expression over one family
of input broadcast instances, so the BRB refinement (`BRB.brachaRefinesSpecification`) is carried
through the operators that expression is built from: `ForwardSimulation.mapIdle` reads one
coordinate over the composition's alphabet, `ForwardSimulation.synchronisedProduct` collects the
coordinates of the family, `ForwardSimulation.parallel_left` holds the gather programs, and
`ForwardSimulation.abstract` and `ForwardSimulation.relabel` hide the events and read the result
back over the interface alphabet. `ForwardSimulation.congr` then reshapes the composite relation
into `BroadcastSubstitutionRelation`.

Both instances are LTS, so `instanceOverBracha_refines` reads the substitution as an
inclusion of achievable trace distributions. `broadcastSubstitutionRelation_corrupt` states that
the relation is preserved by corrupting both instances at once, in the shape the family congruence
of `ABA/GBCA/AFW/BroadcastSubstitution.lean` consumes (`ForwardSimulation.family`, `hglob`).
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The relation -/

/-- The broadcast substitution relation: the gather programs and network equal, and each
input broadcast coordinate related to its specification coordinate by the BRB
refinement relation. -/
structure BroadcastSubstitutionRelation (P : Parameters) (s : StateOverBracha P.n X)
    (t : StateOverBroadcastSpecification P.n X) : Prop where
  /-- The gather programs and the gather network state are untouched by the
  substitution. -/
  gatherProgramsAndNetwork_eq : s.1 = t.1
  /-- Each input coordinate is BRB-refined. -/
  inputBroadcastRelation : ∀ k,
    BRB.SpecificationRelation P k (inputBroadcasts s k) (inputBroadcasts t k)

/-- The relation holds initially. -/
theorem broadcastSubstitutionRelation_init :
    BroadcastSubstitutionRelation P (instanceOverBracha P X).init
    (instanceOverBroadcastSpecification P X).init :=
  ⟨rfl, fun _ => BRB.specificationRelation_init⟩

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
  have hSyncIn := ForwardSimulation.synchronisedProduct hIn
  have hSub := ((hSyncIn.parallel_left (gatherPrograms P X)).abstract (gatherEvents P.n X)).relabel
  exact ForwardSimulation.congr (fun _ _ => ⟨fun ⟨hga, hin⟩ => ⟨hga, hin⟩,
    fun ⟨hga, hin⟩ => ⟨hga, hin⟩⟩) hSub

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the gather instance over Bracha's broadcast
in the gather instance over the broadcast specification. -/
theorem instanceOverBracha_refines (P : Parameters) (X : Type) [DecidableEq X] :
    achievableTraceDists (instanceOverBracha P X) ⊆ achievableTraceDists
      (instanceOverBroadcastSpecification P X) :=
  (ForwardSimulation.toProbabilistic (instanceOverBracha_isLTS P)
    (instanceOverBroadcastSpecification_isLTS P)
    broadcastSubstitutionRelation_init (broadcastSubstitution P X)).achievableTraceDists_subset

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility at the gather instance**: the broadcast
substitution relation is preserved by corrupting both instances at once. -/
theorem broadcastSubstitutionRelation_corrupt {X : Type} [DecidableEq X] {P : Parameters}
    {s : StateOverBracha P.n X} {t : StateOverBroadcastSpecification P.n X}
    (hR : BroadcastSubstitutionRelation P s t) (id : Fin P.n) :
    BroadcastSubstitutionRelation P
    (corruptAll P id (InstanceState.corrupt P id) s)
    (corruptAll P id (BRB.SpecState.corrupt P id) t) :=
  ⟨congrArg (fun x => (x.1, { x.2 with network := x.2.network.corrupt P id }))
    hR.gatherProgramsAndNetwork_eq,
    fun k => BRB.specificationRelation_corrupt (hR.inputBroadcastRelation k) id⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.broadcastSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms broadcastSubstitution

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_refines

end Gather
end ABA
end PLTS
