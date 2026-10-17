/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.FirstGatherReturn

/-!
# The round's graded return

`roundProjection_retG`: the projection of the composed round after the round returns the graded
outcome on record to the round loop. The transition clears the outcome from the round variables,
which is what marks the round returned, and its ghost write records the bound bit of the recorded
first core where no bit is recorded. The composed round's `retG` event writes the same: the program
drops the outcome and marks its variables returned, and the round's network records that the round
has returned. The projection computes whether the round has returned from whether the ghost holds
the bound bit, so the two agree where the first core is recorded. `afterRetG` names the state the
return reaches.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The round's graded return

The transition clears the graded outcome from the round variables. It sends nothing, and its ghost
write records the bound bit and leaves the two cores. -/

/-- **The round after its graded return to `j`**: the program drops the
grade and marks its variables returned, and the round's network records that
the round has returned. -/
def afterRetG (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) (j : Fin P.n) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setNetwork
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with output := none, returned := true }))
    { GBCA.ByAFW.network s with returned := true }

/-- **The graded return, read through the projection.** The round returns the graded outcome on
record to the round loop, the outcome leaves the round variables, and the round's network records
that the round has returned. The round's first core is recorded (`hcore`), which holds at a
process holding a graded outcome (`BoundInvariant.firstGatherCore_of_output`). -/
theorem roundProjection_retG (hu : (u j).2 = p) (r : ℕ) (out : GBCAOutput)
    (c' : RoundLoopVariables P.n)
    (hr2 : ((p.roundVariables r).secondGather.processVariables).returned = true)
    (hcore : (w.ghost r).1 ≠ none) :
    roundProjection P (Function.update u j (c', p.setRoundVariables r
        { p.roundVariables r with output := none }))
      (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out))) r
      = afterRetG P (roundProjection P u w r) j := by
  subst hu
  rw [roundProjection_writeGhost _ _
      (rfl : roundOf (Sum.inl (Label.retG r j out)) = some r),
    firstGatherProjection_writeNoSent, secondGatherProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterRetG, GBCA.ByAFW.programs_setNetwork, GBCA.ByAFW.programs_setPrograms,
      programs_roundProjection_eq, roundVariables_update_self rfl, locals_programProjection_if]
    simp [programs_mk, programProjection, hr2]
  · simp only [afterRetG, GBCA.ByAFW.network_setNetwork, network_roundProjection, network_mk,
      networkProjection_ghostStep_retG w (w.ghost r) r j out hcore]
  · simp only [afterRetG, GBCA.ByAFW.firstGather_setNetwork, GBCA.ByAFW.firstGather_setPrograms,
      firstGather_roundProjection]
    simp only [firstGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [Gather.gatherProgramsAndNetwork_setCore,
        gatherProgramsAndNetwork_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, core_firstGatherProjection]
  · simp only [afterRetG, GBCA.ByAFW.secondGather_setNetwork, GBCA.ByAFW.secondGather_setPrograms,
      secondGather_roundProjection]
    simp only [secondGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [Gather.gatherProgramsAndNetwork_setCore,
        gatherProgramsAndNetwork_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, core_secondGatherProjection]

end Transitions

end AFW
end ABA
end PLTS
