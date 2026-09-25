/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Invariant
import Leslie2Protocols.Framework.FamilySimulation

/-!
# The relation between the reliable-broadcast instance and its specification

`BRB.SpecificationRelation P ldr s t` relates a state of the reliable-broadcast instance to a
state of the broadcast specification with the same leader. The call records, the return flags and
the corrupted sets agree, the instance invariant holds at `s`, and `val_witness` bounds the
specification's committed value by `BRB.EchoWitness`.

`specificationRelation_init` holds the relation at the two initial states, and
`specificationRelation_corrupt` carries it across a corruption of both systems at once, which is
the shape the family lifting consumes. The matching of the instance's transitions against runs of
the specification is `BRB.specificationRelation_transition`
(`ABA/ReliableBroadcast/Bracha/RefinesSpecification.lean`).
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-! ### The relation -/

/-- The relation the reliable-broadcast refinement runs along. `val_witness` bounds the
specification's committed value by the certificate; the other clauses are projections. -/
structure SpecificationRelation (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (t : SpecState P.n M) : Prop where
  /-- The implementation invariant. -/
  invariant : Invariant P ldr s
  /-- The call records agree. -/
  input_eq : t.input = (s.processVariables ldr).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = (s.processVariables id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- A committed value is echo-certified. -/
  val_witness : ∀ m, t.val = some m → EchoWitness P s m

/-- The relation holds initially. -/
theorem specificationRelation_init :
    SpecificationRelation P ldr (BrachaState.initial P.n M) (SpecState.initial P.n M) := by
  refine ⟨Invariant.initial, ?_, ?_, ?_, ?_⟩ <;>
    simp [BrachaState.initial, SpecState.initial, ProcessVariables.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both systems at once — the
abstract state the family lifting consumes. -/
theorem specificationRelation_corrupt {s : BrachaState P.n M} {t : SpecState P.n M}
    (hR : SpecificationRelation P ldr s t) (id : Fin P.n) :
    SpecificationRelation P ldr (s.corrupt P id) (t.corrupt P id) := by
  refine ⟨hR.invariant.step (BrachaAlgorithm.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · rw [corrupt_input, InstanceState.corrupt_processVariables]
    exact hR.input_eq
  · intro k
    rw [corrupt_ret, InstanceState.corrupt_processVariables]
    exact hR.ret_eq k
  · rw [SpecState.corrupt_F, InstanceState.corrupt_F, hR.F_eq]
  · intro m hm
    rw [corrupt_val] at hm
    rw [echoWitness_corrupt]
    exact hR.val_witness m hm

end BRB
end ABA
end PLTS
