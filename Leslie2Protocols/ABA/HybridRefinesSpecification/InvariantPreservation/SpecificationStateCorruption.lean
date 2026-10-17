/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# Corruption at a specification state

The readings of corruption at the graded-agreement and coin specification states that the `fail`
transition of `hybrid` consumes. Both families take `fail` on their broadcast, which applies the
corruption at every round, in the map or not, so the accessor of the family after the broadcast is
the accessor before it with every round corrupted (`GBCA.instanceState_applyBroadcast_fail`,
`WCC.instanceState_applyBroadcast_fail`). A coin corruption leaves `val` and `called` alone
(`WCC.corrupt_val`, `WCC.SpecState.corrupt_called`). A GBCA or WCC state that agrees with the ABA
state on `F` agrees with it again once both are corrupted at the same process
(`GBCA.corrupt_F_eq`, `WCC.corrupt_F_eq`), which is what keeps `F_gbca` and `F_wcc` together across
a `fail` broadcast.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- The corruption broadcast of the graded-agreement family corrupts the specification of every
round, in the map or not. -/
theorem GBCA.instanceState_applyBroadcast_fail {M : Type} (G : GBCASpecificationFamilyState P M)
    (id : Fin P.n) :
    ⇑(G.applyBroadcast (Sum.inl (Label.fail id))) = fun r => (G r).corrupt P id :=
  funext fun r => InstanceFamilyState.applyBroadcast_apply G _ r

/-- The corruption broadcast of the coin family corrupts the coin instance of every round, in the
map or not. -/
theorem WCC.instanceState_applyBroadcast_fail
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) (id : Fin P.n) :
    ⇑(o.applyBroadcast (Label.fail id)) = fun r => (o r).corrupt P id :=
  funext fun r => InstanceFamilyState.applyBroadcast_apply o _ r

/-- WCC corruption changes only `F`. -/
theorem WCC.corrupt_val {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold WCC.SpecState.corrupt; split <;> rfl

/-- The GBCA corruption of a state agreeing with the core on `F` agrees with the core's corruption
on `F` (keeps `F_gbca` together across a `fail` broadcast). -/
theorem GBCA.corrupt_F_eq {P : Parameters} (id : Fin P.n) (s : GBCA.SpecState P.n)
    (c : ABAState P) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold GBCA.SpecState.corrupt
  rw [ABAState.corrupt_F, h]; split_ifs <;> simp [h]

/-- The WCC corruption of a state agreeing with the core on `F` agrees with the core's corruption on
`F` (keeps `F_wcc` together across a `fail` broadcast). -/
theorem WCC.corrupt_F_eq {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n)
    (c : ABAState P) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold WCC.SpecState.corrupt
  rw [ABAState.corrupt_F, h]; split_ifs <;> simp [h]

end ABA
end PLTS
