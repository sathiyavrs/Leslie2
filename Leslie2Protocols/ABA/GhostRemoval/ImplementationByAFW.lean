/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GhostRemoval.GhostFreeSystem
import Leslie2Protocols.ABA.AFW.Simulation
import Leslie2Protocols.ABA.Results

/-!
# The ghost-free gather-based protocol

The network of `AFW.protocol` holds, for every round, a ghost of type `AFW.Ghost`: the first
gather's recorded core, the second gather's recorded core and the round's bound bit, each written
once (D30). `AFW.ghostStep` writes it at the first return of each of the two gathers and at the
round's first return, and no guard of a program reads it. The ghost enables one transition, the
network's announcement `boundG r b`, enabled exactly when `AFW.ghostBound` of the ghost of round
`r` is `some b` (D29). The announcement lies in `Label.hiddenAPI`, so it is hidden at protocol
level. `AFW.ghostFreeProtocol` is the protocol with the ghost removed: its network holds the
one-element ghost `Unit` and announces nothing.

`AFW.protocol_ghostRemoval` states that the protocol and the ghost-free protocol achieve the same
trace distributions. Every headline about the protocol therefore holds of the ghost-free protocol,
and the rest of this file derives them: the composition inclusion into `AFW.composed`,
trace-distribution refinement into the ABA specification, Validity and Agreement of every
positive-probability trace, and trace conservativity against the protocol-shaped specification
`hybrid`.

The proof is the removal of an auxiliary variable, `Implementation.system_ghostRemoval`
(`ABA/GhostRemoval/GhostFreeSystem.lean`), at the gather-based implementation's ghost: the type
`AFW.Ghost`, the write `AFW.ghostStep` and the read `AFW.ghostBound`, the arguments `AFW.protocol`
passes. Since the announcement labels are hidden, the removal is at the identity on labels, and no
label map appears in the statement.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation

/-- **The ghost-free gather-based protocol**: the `n` programs and the common coin of
`AFW.protocol` beside the network over the one-element ghost `Unit`, which holds no core and no
bit, so that the announcement `boundG` never fires. -/
noncomputable def ghostFreeProtocol (P : Parameters) :
    System (Implementation.State P (Message P.n) (RoundVariables P.n) Unit) (Label P.n) :=
  Implementation.systemGhostFree P (Message P.n) (RoundEvent P.n) (RoundVariables P.n) (RoundStep P)

/-- **The ghost changes no trace distribution.** The ghost of a round holds the two gathers'
recorded cores and the round's bound bit, no guard of a program reads it, and the network's
announcement `boundG` is the one transition it enables. The announcement is hidden at protocol
level, so the protocol and the ghost-free protocol achieve the same trace distributions. -/
theorem protocol_ghostRemoval (P : Parameters) :
    achievableTraceDists (protocol P) = achievableTraceDists (ghostFreeProtocol P) :=
  Implementation.system_ghostRemoval P (Message P.n) (RoundEvent P.n) (RoundVariables P.n)
    (Ghost P.n) (RoundStep P) (ghostStep P) ghostBound

/-! ### The headlines at the ghost-free protocol -/

/-- **The composition inclusion for the ghost-free protocol.** -/
theorem ghostFreeProtocol_composed (P : Parameters) :
    achievableTraceDists (ghostFreeProtocol P) ⊆ achievableTraceDists (composed P) :=
  Set.Subset.trans (protocol_ghostRemoval P).symm.subset (protocol_composed P)

/-- **Trace-distribution refinement of the ghost-free protocol**: every trace
distribution it achieves is achievable by the ABA specification. -/
theorem ghostFreeProtocol_refines (P : Parameters) :
    achievableTraceDists (ghostFreeProtocol P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (protocol_ghostRemoval P).symm.subset (refines P)

/-- **Correctness of the ghost-free protocol**: every positive-probability trace
satisfies Validity and Agreement. -/
theorem ghostFreeProtocol_safe (P : Parameters) :
    ∀ D ∈ achievableTraceDists (ghostFreeProtocol P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (ghostFreeProtocol_refines P) (spec_safe P)

/-- **Trace conservativity of the ghost-free protocol**: every
positive-probability trace has positive probability under an achievable trace
distribution of the protocol-shaped specification. -/
theorem ghostFreeProtocol_traces (P : Parameters) :
    ∀ D ∈ achievableTraceDists (ghostFreeProtocol P), ∀ t, D t ≠ 0 →
      ∃ D' ∈ achievableTraceDists (hybrid P Empty), D' t ≠ 0 :=
  fun D hD _ ht =>
    ⟨D, Set.Subset.trans (ghostFreeProtocol_composed P) (substitution P) hD, ht⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.AFW.protocol_ghostRemoval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_ghostRemoval

/-- info: 'PLTS.ABA.AFW.ghostFreeProtocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ghostFreeProtocol_composed

/-- info: 'PLTS.ABA.AFW.ghostFreeProtocol_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ghostFreeProtocol_refines

/-- info: 'PLTS.ABA.AFW.ghostFreeProtocol_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ghostFreeProtocol_safe

/-- info: 'PLTS.ABA.AFW.ghostFreeProtocol_traces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ghostFreeProtocol_traces

end AFW
end ABA
end PLTS
