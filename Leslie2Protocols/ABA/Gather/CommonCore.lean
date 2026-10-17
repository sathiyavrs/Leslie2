/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.BroadcastSubstitution

/-!
# The common core at the two gather implementations

The common core of a trace (`Gather.CoreTrace`, `ABA/Gather/SpecificationSafety.lean`) holds
at the gather instance over the broadcast specifications and at the gather instance over Bracha's
broadcast: `Gather.instanceOverBroadcastSpecification_core` and `Gather.instanceOverBracha_core`.
In every positive-probability trace, every announced core has at least `n − f` entries, two
announcements announce the same set, and every returned map contains every announced core.

`Gather.specInst_core` proves the predicate at the specification. The two implementations inherit
it along their refinements (`PLTS.safety_transfer`): the counting refinement
(`instanceOverBroadcastSpecification_refines`, `ABA/Gather/RefinesSpecification.lean`) and,
beneath it, the broadcast substitution (`instanceOverBracha_refines`,
`ABA/Gather/BroadcastSubstitution.lean`). All three systems are over the specification's alphabet
`Gather.Label n X`, so a trace of an implementation is read as a trace of the specification.

What makes that transfer say anything is that the core is announced on a label of its own (D29):
an implementation holds it in a field no process reads, and its refinements match its announcement
by the specification's.
-/

namespace PLTS
namespace ABA
namespace Gather

/-! ### The common core along the refinements -/

/-- **The composed gather instance binds one core.** -/
theorem instanceOverBroadcastSpecification_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (instanceOverBroadcastSpecification P X), ∀ t, D t ≠ 0 →
      CoreTrace P t :=
  safety_transfer (instanceOverBroadcastSpecification_refines P X) (specInst_core P X)

/-- **The common core at the gather instance over Bracha's broadcasts**: in every
positive-probability trace, every announced core has at least `n − f` entries, two announcements
announce the same set, and every returned map contains every announced core. The two refinements
carry it down from the specification. -/
theorem instanceOverBracha_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (instanceOverBracha P X), ∀ t, D t ≠ 0 → CoreTrace P t :=
  safety_transfer (Set.Subset.trans (instanceOverBracha_refines P X)
    (instanceOverBroadcastSpecification_refines P X)) (specInst_core P X)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.instanceOverBroadcastSpecification_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBroadcastSpecification_core

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_core

end Gather
end ABA
end PLTS
