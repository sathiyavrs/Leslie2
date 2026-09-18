/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Sub
import Leslie2Protocols.ABA.Gather.SubSim
import Leslie2Protocols.ABA.Broadcast.ImplSim
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.MapIdleSim
import Leslie2.Results

/-!
# The broadcast substitution inside the gather instance

`Gather.Sub.gatherLow`: the gather instance over Bracha's broadcast
(`Gather.lowSub`) is forward simulated by the gather instance over the broadcast
specification (`Gather.idealSub`), along `Gather.Sub.LowRel` — the gather tier
held equal, and each broadcast coordinate related to its specification
coordinate by the BRB refinement relation (`BRB.InstRel`,
`ABA/Broadcast/ImplSim.lean`).

The proof is the congruence argument alone. The two instances are one
expression over two broadcast tiers, so the BRB refinement (`BRB.brbRefines`)
is carried through the operators that expression is built from:
`ForwardSimulation.mapIdle` reads one coordinate over the composition's
alphabet, `ForwardSimulation.syncProduct` collects the coordinates of one
family, `ForwardSimulation.parallel_right` and
`ForwardSimulation.parallel_left` hold the other family and then the gather
tier, and `ForwardSimulation.abstract` and `ForwardSimulation.relabel` hide the
events and read the result back over the interface alphabet. The two families
are replaced one after the other and the two steps are joined by
`ForwardSimulation.trans`. `ForwardSimulation.congr` then reshapes the
composite relation into `LowRel`: the intermediate state the composite
quantifies over is the input coordinates of the abstract side beside the bind
coordinates of the concrete side.

Both instances are LTS, so `lowSub_refines` reads the substitution as an
inclusion of achievable trace distributions.
-/

namespace PLTS
namespace ABA
namespace Gather
namespace Sub

variable {X : Type} [DecidableEq X] {P : Params}

/-! ### The relation -/

/-- The broadcast substitution relation: the gather tier equal, and each
broadcast coordinate related to its specification coordinate by the BRB
refinement relation. -/
structure LowRel (P : Params) (s : LowSubState P.n X) (t : IdealSubState P.n X) : Prop where
  /-- The gather programs and the gather network state are untouched by the
  substitution. -/
  ga_eq : s.1 = t.1
  /-- Each input coordinate is BRB-refined. -/
  inRel : ∀ k, BRB.InstRel P k (brbIn s k) (brbIn t k)
  /-- Each bind coordinate is BRB-refined. -/
  bindRel : ∀ q, BRB.InstRel P q (brbBind s q) (brbBind t q)

/-- The relation holds initially. -/
theorem lowRel_init : LowRel P (lowSub P X).init (idealSub P X).init :=
  ⟨rfl, fun _ => BRB.instRel_init, fun _ => BRB.instRel_init⟩

/-! ### The substitution -/

/-- **The broadcast substitution.** The gather instance over Bracha's broadcast
is forward simulated by the gather instance over the broadcast specification.
Each coordinate carries the BRB refinement; the congruences carry it through
the composition. -/
theorem gatherLow (P : Params) (X : Type) [DecidableEq X] :
    ForwardSimulation (lowSub P X) (idealSub P X) (LowRel P) := by
  have hIn : ∀ k : Fin P.n,
      ForwardSimulation ((BRB.sub P k X).mapIdle (inPull P.n X k))
        ((BRB.liftedSpec P k X).mapIdle (inPull P.n X k)) (BRB.InstRel P k) :=
    fun k => ForwardSimulation.mapIdle (inPull P.n X k) (inPull_tau P.n X k)
      (fun _ h => inPull_eq_tau h) (BRB.brbRefines P k)
  have hBind : ∀ q : Fin P.n,
      ForwardSimulation ((BRB.sub P q (APSet P.n X)).mapIdle (bindPull P.n X q))
        ((BRB.liftedSpec P q (APSet P.n X)).mapIdle (bindPull P.n X q)) (BRB.InstRel P q) :=
    fun q => ForwardSimulation.mapIdle (bindPull P.n X q) (bindPull_tau P.n X q)
      (fun _ h => bindPull_eq_tau h) (BRB.brbRefines P q)
  have hSyncIn := ForwardSimulation.syncProduct hIn
  have hSyncBind := ForwardSimulation.syncProduct hBind
  have hBroad := (hSyncIn.parallel_right
      (System.syncProduct fun q => (BRB.sub P q (APSet P.n X)).mapIdle (bindPull P.n X q))).trans
    (hSyncBind.parallel_left
      (System.syncProduct fun k => (BRB.liftedSpec P k X).mapIdle (inPull P.n X k)))
  have hSub := ((hBroad.parallel_left (gaPart P X)).abstract (gaEvents P.n X)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hSub
  constructor
  · rintro ⟨hga, ⟨b₁, b₂⟩, ⟨hin, rfl⟩, rfl, hbind⟩
    exact ⟨hga, hin, hbind⟩
  · rintro ⟨hga, hin, hbind⟩
    exact ⟨hga, (t.2.1, s.2.2), ⟨hin, rfl⟩, rfl, hbind⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the gather instance over Bracha's broadcast
in the gather instance over the broadcast specification. -/
theorem lowSub_refines (P : Params) (X : Type) [DecidableEq X] :
    achievableTraceDists (lowSub P X) ⊆ achievableTraceDists (idealSub P X) :=
  (ForwardSimulation.toProbabilistic (lowSub_isLTS P) (idealSub_isLTS P)
    lowRel_init (gatherLow P X)).achievableTraceDists_subset

/-- **The common core at the gather instance over Bracha's broadcasts**: every
return of a positive-probability trace names a set of at least `n − f` entries
below the returned map, and every return names the same set. The two
substitutions carry it down from the specification. -/
theorem lowSub_core (P : Params) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (lowSub P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map subDown) :=
  safety_transfer (Set.Subset.trans (lowSub_refines P X) (idealSub_refines P X))
    (liftedSpec_core P X)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.Sub.gatherLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherLow

/-- info: 'PLTS.ABA.Gather.Sub.lowSub_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowSub_refines

/-- info: 'PLTS.ABA.Gather.Sub.lowSub_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowSub_core

end Sub
end Gather
end ABA
end PLTS
