/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GhostErasure.GhostFreeSystem
import Leslie2Protocols.ABA.ImplementationByAFW.Simulation

/-!
# The ghost-free gather-based protocol

The network adversary of `AFW.protocol` holds one record per round that no program
reads: the two gathers' frozen cores and the round's bound bit, written by
`AFW.ghostStep` and announced on every graded-agreement return by `AFW.announcedBound`.
`AFW.protocol₀` is the protocol as it runs with that record dropped and the adversary
free to announce either bit on a return.

`AFW.protocol_erasure` is the statement that the record costs nothing: the ghost never
blocks a step and never adds one, so the two readings have the same achievable trace
distributions. Every headline about the protocol therefore holds of the ghost-free
protocol, and the rest of this file re-derives them: the composition inclusion into
`AFW.composed`, trace-distribution refinement into the ABA specification, Validity and
Agreement of every positive-probability trace, and trace conservativity against the
protocol-shaped specification `hybrid`.

The proof is the state erasure of `ABA/GhostErasure/GhostFreeSystem.lean` carried through the
composition pipeline. Its hypothesis is that every round, process and graded outcome
admits an announced bit, which here is the equation `bnd = AFW.ghostOut P w r id out`
read at its own right-hand side. The announced bit is silent at protocol level — a
`retG` label lies in `Label.hiddenAPI` — which is why no label map appears in the
statement.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation

/-- **The ghost-free gather-based protocol**: the `n` programs and the coin oracle of
`AFW.protocol` beside the network adversary over the trivial ghost, whose
graded-agreement returns announce any bit. -/
noncomputable def protocol₀ (P : Params) :
    System (Implementation.State P (Msg P.n) (StageRec P.n) Unit) (Label P.n) :=
  Implementation.systemGhostFree P (Msg P.n) (StageRec P.n) (RoundStep P) (gCallPayload P)

/-- **The ghost costs nothing.** The record the network adversary keeps for each round is
written by no guard and read by no program, and the label that announces its bit is
hidden at protocol level, so the protocol and the ghost-free protocol achieve the same
trace distributions. -/
theorem protocol_erasure (P : Params) :
    achievableTraceDists (protocol P) = achievableTraceDists (protocol₀ P) :=
  Implementation.system_erasure P (Msg P.n) (StageRec P.n) (Ghost P.n) (RoundStep P)
    (gCallPayload P) (ghostStep P) (announcedBound P)
    (fun w r id out => ⟨ghostOut P w r id out, rfl⟩)

/-! ### The headlines at the ghost-free protocol -/

/-- **The composition inclusion for the ghost-free protocol.** -/
theorem protocol₀_composed (P : Params) :
    achievableTraceDists (protocol₀ P) ⊆ achievableTraceDists (composed P) :=
  Set.Subset.trans (protocol_erasure P).symm.subset (protocol_composed P)

/-- **Trace-distribution refinement of the ghost-free protocol**: every trace
distribution it achieves is achievable by the ABA specification. -/
theorem protocol₀_refines (P : Params) :
    achievableTraceDists (protocol₀ P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (protocol_erasure P).symm.subset (refines P)

/-- **Correctness of the ghost-free protocol**: every positive-probability trace
satisfies Validity and Agreement. -/
theorem protocol₀_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (protocol₀ P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (protocol₀_refines P) (spec_safe P)

/-- **Trace conservativity of the ghost-free protocol**: every
positive-probability trace has positive probability under an achievable trace
distribution of the protocol-shaped specification. -/
theorem protocol₀_traces (P : Params) :
    ∀ D ∈ achievableTraceDists (protocol₀ P), ∀ t, D t ≠ 0 →
      ∃ D' ∈ achievableTraceDists (hybrid P), D' t ≠ 0 :=
  fun D hD _ ht =>
    ⟨D, Set.Subset.trans (protocol₀_composed P) (substitution P) hD, ht⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.AFW.protocol_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_erasure

/-- info: 'PLTS.ABA.AFW.protocol₀_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol₀_composed

/-- info: 'PLTS.ABA.AFW.protocol₀_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol₀_refines

/-- info: 'PLTS.ABA.AFW.protocol₀_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol₀_safe

/-- info: 'PLTS.ABA.AFW.protocol₀_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol₀_traces

end AFW
end ABA
end PLTS
