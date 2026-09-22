/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Simulation
import Leslie2Protocols.ABA.ImplementationByABDY.Simulation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# The main theorems of the ABA case study

The subject is the protocol `ABDY.protocol P`: `n` programs, one per process, beside two components
that are not processes — the network adversary, which owns the message sets, the DECIDED sets and
the corrupted set with its budget, and the common-coin oracle, the only component whose transitions
are not Dirac. A program reads its own records, its own recv and its own replacement flag, and
nothing else about corruption: not the corrupted set, not the budget, not another process's status.
A corruption replaces the program of the process it names (D23); whether another process may be
taken off-protocol is decided by the network's `k ∈ F` guard. A program holds its round loop beside
its round records — the round record of every round it has touched, in a finite map — and terminates
at `2f + 1` DECIDED receipts (D22).

The abstract system is `ABA.spec P`, the single-automaton system of agreement,
whose traces satisfy Validity and Agreement (`spec_safe`, `Specifications/ABASafety.lean`).

## The chain

Three probabilistic forward simulations carry the protocol to the
specification:

1. `ABDY.protocolSim` (`ImplementationByABDY/Simulation.lean`) — the protocol into the composed
   system, along the Dirac lift of `ABDY.ProtocolRelation`. The relation pins every
   composed coordinate against the protocol state; the inclusion is
   one-directional because a round instance also answers the Byzantine handshake rows
   (D11) and the processes the protocol has terminated (D22).
2. `ABDY.substitutionSimulation` (`Composition/HybridAndSubstitution.lean`) — replace each round's
graded-agreement
   instance by its specification, the other three components untouched: the
   family substitution carried by four congruences (`parallel_right`,
   `abstract`, `relabel`, `abstract`).
3. `hybridRefinesSpecification` (`HybridRefinesSpecification/Simulation.lean`) — the hand-built
simulation of the protocol-shaped specification against the ABA specification, read in the composed
coordinates: the round specifications, the `n` round loops, the ABA network and the coin oracle,
each still a component of the state the relation is defined on.

`ABDY.refines` chains the soundness inclusions of the three (Result 1) by
`Set.Subset.trans`; `ABDY.chainSim` composes the three simulations themselves by
`ProbabilisticForwardSimulation.trans` (Result 2). The two routes are
independent — the inclusion never invokes transitivity of simulation.

## Scope of the headline

Graded agreement is carried to implementation level: each round is a group of graded-agreement
programs beside that round's own network, moved by the same network adversary. Each round's graded
return announces that round's bound bit (D29), a ghost output that rides the `retG` label and that
no component's state records. `GBCA.BindingTrace` (`GBCA/SpecificationSafety.lean`) is the property
it carries. The **common coin is held at specification level** — the ε-coin is `Parameters.wccPMF`,
not a Gather/SRSD implementation — so the correct statement is *graded agreement verified to
implementation level; the coin assumed at specification level*.

`ValidityTrace` (`Specifications/ABASafety.lean`) is the paper-form predicate: a bit
returned by a never-corrupted process is the bit of the first `callABA` of a
*never-corrupted* (`NeverCorrupted`) caller, earlier in the trace. A process
has one input, and its first call is the event that carries it, so this is the
papers' correct-process Validity.
What is proven is safety — Validity and Agreement for every
positive-probability trace. Termination, liveness, unpredictability and
fairness are not claimed.

The `#guard_msgs`/`#print axioms` blocks below are the mechanical check:
the headlines, and the framework results the chain rests on, are pinned to the
clean axiom list `[propext, Classical.choice, Quot.sound]`.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-! ### The chain, inclusion by inclusion

Carry the protocol into the composed system (`ABDY.protocol_composed`),
substitute each round's graded-agreement instance by its specification at the
protocol shape (`ABDY.substitution`), then take the core simulation (`hybridRefinesSpecification`).
Every step is a simulation between systems the protocol itself
names. -/

/-- **The protocol-shaped specification refines the ABA specification**: the
soundness of the core simulation. -/
theorem hybrid_spec (P : Parameters) :
    achievableTraceDists (hybrid P) ⊆ achievableTraceDists (spec P) :=
  (hybridRefinesSpecification P).achievableTraceDists_subset

namespace ABDY

/-- **Safety of the protocol**: every positive-probability trace of
every achievable trace distribution of the `n` programs beside the network
adversary and the coin oracle satisfies Validity and Agreement. The corruption
budget is a guard of the network adversary's own `fail` row, so every protocol
execution is in budget by construction and nothing is assumed of the
traces. -/
theorem protocol_safe (P : Parameters) :
    ∀ D ∈ achievableTraceDists (protocol P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer
    (Set.Subset.trans (protocol_composed P)
      (Set.Subset.trans (substitution P) (hybrid_spec P)))
    (spec_safe P)

/-- **Trace conservativity of the protocol**: every
positive-probability trace of the protocol has positive probability
under an achievable trace distribution of the protocol-shaped
specification. -/
theorem protocol_traces (P : Parameters) :
    ∀ D ∈ achievableTraceDists (protocol P), ∀ t, D t ≠ 0 →
      ∃ D' ∈ achievableTraceDists (hybrid P), D' t ≠ 0 :=
  fun D hD _ ht => ⟨D, Set.Subset.trans (protocol_composed P) (substitution P) hD, ht⟩

/-- **Safety of the composed system**: the substitution and the core
simulation carry the composed system to the specification, so it inherits the
same guarantee. -/
theorem composed_safe (P : Parameters) :
    ∀ D ∈ achievableTraceDists (composed P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (Set.Subset.trans (substitution P) (hybrid_spec P)) (spec_safe P)

/-! ### The two routes -/

/-- **Trace-distribution refinement** (blueprint `thm:aba-main`, safety
fragment): every trace distribution achievable by the protocol is
achievable by the ABA specification. The composition and the substitution give
the first inclusion, the core simulation the second. -/
theorem refines (P : Parameters) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (protocol_composed P)
    (Set.Subset.trans (substitution P) (hybrid_spec P))

/-- **Correctness of ABA** (blueprint `thm:aba-main`, safety fragment): every positive-probability
trace of the protocol satisfies Validity and Agreement. No extra hypothesis on the traces: the
corruption budget is a guard of the network adversary's own `fail` row, so every protocol execution
is in budget by construction. -/
theorem main (P : Parameters) :
    ∀ D ∈ achievableTraceDists (protocol P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed simulation** `protocol ⊑ ABA.spec`: the three simulations of
the chain joined by Result 2 (`ProbabilisticForwardSimulation.trans`), along
the composite of their three relations — the Dirac lift of the composition
relation, the pointwise round substitution, and the core relation. -/
noncomputable def chainSim (P : Parameters) :
    ProbabilisticForwardSimulation (protocol P) (spec P)
      (compRel (diracRel (ProtocolRelation P))
        (compRel (parallelRel (diracRel (substitutionRelationFamily P)))
          (hybridSpecificationRelation P))) :=
  (protocolSim P).trans ((substitutionSimulation P).trans (hybridRefinesSpecification P))

/-! ### Mechanical axiom check

Neither the headlines nor the framework results the chain rests on may acquire
a `sorryAx` dependence. -/

/-- info: 'PLTS.ProbabilisticForwardSimulation.relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProbabilisticForwardSimulation.relabel

/-- info: 'PLTS.ABA.ABDY.substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substitution

/-- info: 'PLTS.ABA.hybrid_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hybrid_spec

/-- info: 'PLTS.ABA.ABDY.protocol_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_safe

/-- info: 'PLTS.ABA.ABDY.protocol_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_traces

/-- info: 'PLTS.ABA.ABDY.composed_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composed_safe

/-- info: 'PLTS.ABA.ABDY.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'PLTS.ABA.ABDY.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refines

/-- info: 'PLTS.ABA.ABDY.chainSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainSim

/-- info: 'PLTS.ProbabilisticForwardSimulation.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ProbabilisticForwardSimulation.trans

/-- info: 'PLTS.weakTau_lift_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weakTau_lift_pure

/-- info: 'PLTS.weakTau_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weakTau_flatten

end ABDY

end ABA
end PLTS
