/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# Corruption at a specification state

The four readings of corruption at a graded-agreement or coin specification state that the `fail`
row of `hybrid` consumes. A coin corruption leaves `val` and `called` alone (`WCC.corrupt_val`,
`WCC.corrupt_called`). A GBCA or WCC state that agrees with the ABA state on `F` agrees with it
again once both are corrupted at the same process (`GBCA.corrupt_F_eq`, `WCC.corrupt_F_eq`), which
is what keeps `F_gbca` and `F_wcc` together across a `fail` broadcast.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- WCC corruption changes only `F`. -/
theorem WCC.corrupt_val {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold WCC.SpecState.corrupt; split <;> rfl

theorem WCC.corrupt_called {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).called = s.called := by unfold WCC.SpecState.corrupt; split <;> rfl

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
