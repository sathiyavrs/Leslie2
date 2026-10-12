/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.CommonCoreCounting
import Leslie2Protocols.ABA.Gather.SpecificationSafety

/-!
# The relation between the composed gather instance and its specification

`Gather.SpecificationRelation P s t` relates a state of the gather instance over the broadcast
specifications (`Gather.instanceOverBroadcastSpecification`, `ABA/Gather/Composition.lean`) to a
state of the gather specification (`Gather.specInst`, blueprint TS 4). The return flags and the
corrupted sets agree, the specification's calls agree with the gather programs' inputs, the two
systems hold the same core, and the instance invariant of `ABA/Gather/Invariant.lean` holds at `s`.

The instance carries two witnesses: `val_witness` bounds a committed specification entry by the
input instance's commitment, and `withoutBindAbove_card` is the count that holds every return to
the recorded core. The count is that of `ABA/Gather/CommonCoreCounting.lean`: at most `f`
processes outside `F` have sent no `BIND` payload containing the recorded core
(`withoutBindAbove`). That set only loses members along every
transition and every corruption, so the count survives both.

`specificationRelation_init` holds the relation at the two initial states, and
`specificationRelation_corrupt` carries it across a corruption of both systems at once, which is
the shape the family lifting consumes.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The relation -/

/-- The refinement relation of the composed gather instance. `val_witness` bounds
the specification's committed entries by the input instances' commitments; `withoutBindAbove_card`
bounds the processes outside `F` that have sent no `BIND` payload containing the recorded core. -/
structure SpecificationRelation (P : Parameters) (s : StateOverBroadcastSpecification P.n X)
    (t : SpecState P.n X) : Prop where
  /-- The instance invariant. -/
  invariant : Invariant P s
  /-- The specification's calls agree with the gather programs' inputs. -/
  call_eq : ∀ k, t.call k = ((gatherProgramsAndNetwork s).processVariables k).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = ((gatherProgramsAndNetwork s).processVariables id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = (gatherProgramsAndNetwork s).F
  /-- A committed specification entry is a committed input entry. -/
  val_witness : ∀ k v, t.val k = some v → (inputBroadcasts s k).val = some v
  /-- The two systems hold the same core. -/
  core_eq : t.core = core s
  /-- At most `f` processes outside `F` have sent no `BIND` payload containing the recorded
  core. -/
  withoutBindAbove_card : ∀ C, core s = some C → (withoutBindAbove s C).card ≤ P.f

/-- The relation holds initially. -/
theorem specificationRelation_init :
    SpecificationRelation P ((instanceOverBroadcastSpecification P X).init)
    ((specificationOverInstanceAlphabet P X).init) := by
  refine ⟨Invariant.initial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gatherProgramsAndNetwork, inputBroadcasts, core, SpecState.initial, BRB.SpecState.initial,
      ProcessVariables.initial, BaseProcessVariables.initial, NetworkState.initial,
        InstanceState.processVariables, InstanceState.F]

omit [DecidableEq X] in
/-- **Broadcast compatibility**: the relation is preserved by corrupting both systems at once. -/
theorem specificationRelation_corrupt {s : StateOverBroadcastSpecification P.n X}
    {t : SpecState P.n X} (hR : SpecificationRelation P s t) (id : Fin P.n) :
    SpecificationRelation P
    (corruptAll P id (BRB.SpecState.corrupt P id) s)
    (t.corrupt P id) := by
  classical
  refine ⟨hR.invariant.step (AlgorithmOverBroadcastSpecification.fail s id) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [gatherProgramsAndNetwork_corruptAll, inputBroadcasts_corruptAll,
    core_corruptAll]
  · intro k
    rw [corrupt_call, InstanceState.corrupt_processVariables]
    exact hR.call_eq k
  · intro k
    rw [corrupt_ret, InstanceState.corrupt_processVariables]
    exact hR.ret_eq k
  · rw [SpecState.corrupt_F, InstanceState.corrupt_F, hR.F_eq]
  · intro k v hv
    rw [corrupt_val] at hv
    rw [BRB.corrupt_val]
    exact hR.val_witness k v hv
  · rw [corrupt_core]
    exact hR.core_eq
  · intro C hC
    exact le_trans (Finset.card_le_card (withoutBindAbove_corruptAll s id _ C))
      (hR.withoutBindAbove_card C hC)

end Gather
end ABA
end PLTS
