/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# The graded-agreement call and its loop

`roundProjection_callG` and `roundProjection_callGLoop`: the projection of the composed round after
a call of graded agreement. `callG` and `callGLoop` are the two transitions on the label
`callG r j b` (D36). At both the network records the started round and its ghost write leaves the
ghost, and the projection reads neither the started rounds nor the round loop. `callG` records the
input on the round's first gather and sends nothing, which is what the composed round's `callG`
writes, its program recording the input and its first gather taking
`Gather.AlgorithmOverBracha.call`. `callGLoop` is the call at a round whose first gather holds an
input: the round loop moves and the round variables stand, which the composed round's `callLoop`
matches.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The graded-agreement call and its loop

The call records the input on the round's first gather and sends nothing. The
composed round matches it on one label, whose program transition records the input and
whose first gather takes `Gather.AlgorithmOverBracha.call`. The call at a process whose
first gather holds an input moves the round loop alone, which the projection does not
read. -/

/-- The graded-agreement call, read through the projection. The network records the started
round, and the ghost write at `callG` leaves the ghost. -/
theorem roundProjection_callG (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGather := (p.roundVariables r).firstGather.setProcessVariables
            { ((p.roundVariables r).firstGather.processVariables) with input := some b } }))
      ((w.recordStartedRound r j).writeGhost (ghostStep P) (Sum.inl (.callG r j b))) r
      = GBCA.ByAFW.setFirstGather (GBCA.ByAFW.setPrograms (roundProjection P u w r)
            (Function.update (GBCA.ByAFW.programs (roundProjection P u w r)) j
              { GBCA.ByAFW.programs (roundProjection P u w r) j with input := some b }))
          (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
            ((Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).setProcessVariables j
              { (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).processVariables j
                with
                input := some b })) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inl (.callG r j b)) (fun _ _ => rfl),
    roundProjection_recordStartedRound, roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_)
  · simp only [programs_roundProjectionUpdate, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq]
    refine congrArg (Function.update (fun i => programProjection ((u i).2.roundVariables r)) j) ?_
    simp only [programProjection, LocalState.setProcessVariables]
  · simp
  · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather,
      Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [InstanceState.setProcessVariables]
    refine congrArg (Function.update (fun i => ((u i).2.roundVariables r).firstGather) j) ?_
    rfl
  · funext k
    simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.inputBroadcasts_setGatherProgramsAndNetwork,
        inputBroadcasts_firstGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · simp
  · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext k
    simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, inputBroadcasts_secondGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · simp

/-- The graded-agreement call at a round whose first gather holds an input, read through the
projection: the round loop moves, the round variables stand, and every round's projection is the
one before the call. The composed round matches the call by `callLoop`. -/
theorem roundProjection_callGLoop (hu : (u j).2 = p) (r r' : ℕ) (b : Bool)
    (c' : RoundLoopVariables P.n) :
    roundProjection P (Function.update u j (c', p))
      ((w.recordStartedRound r j).writeGhost (ghostStep P) (Sum.inl (.callG r j b))) r'
      = roundProjection P u w r' := by
  rw [roundProjection_ghostId (Sum.inl (.callG r j b)) (fun _ _ => rfl),
    roundProjection_recordStartedRound]
  refine roundProjection_congr (fun i => ?_)
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, ← hu]
  · rw [Function.update_of_ne hi]

end Transitions

end AFW
end ABA
end PLTS
