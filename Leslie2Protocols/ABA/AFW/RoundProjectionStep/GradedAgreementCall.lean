/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The graded-agreement call and its loop

`roundProjection_callG` and `roundProjection_gbcaCallLoop`: the projection of the composed round
after a call of graded agreement. The call records the input on the round's first gather and sends
nothing, which is what the composed round's `callG` writes, its program recording the input and
its first gather taking `Gather.AlgorithmOverBracha.call`. A call against an already-called record
moves the round loop alone, which the projection does not read.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### The graded-agreement call and its loop

The call records the input on the round's first gather and sends nothing. The
composed round answers on one label, whose program transition records the input and
whose first gather takes `Gather.AlgorithmOverBracha.call`. The call against an
already-called record moves the round loop alone, which the projection does not
read. -/

/-- The graded-agreement call, read through the projection. -/
theorem roundProjection_callG (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with input := some b } }))
      (w.writeGhost (ghostStep P) (Sum.inl (.callG r j b))) r
      = GBCA.ByAFW.setFirstGather (GBCA.ByAFW.setPrograms (roundProjection P u w r)
            (Function.update (GBCA.ByAFW.programs (roundProjection P u w r)) j
              { GBCA.ByAFW.programs (roundProjection P u w r) j with input := some b }))
          (Gather.setGatherTier (firstGatherProjection P u w r)
            ((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
              { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                input := some b })) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inl (.callG r j b)) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [programs_roundProjectionUpdate, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq]
    refine congrArg (Function.update (fun i => programProjection ((u i).2.roundRecord r)) j) ?_
    simp only [programProjection, LocalState.setProcess]
  · simp
  · simp only [gatherTier_firstGather_roundProjectionUpdate, GBCA.ByAFW.firstGather_setFirstGather,
      Gather.gatherTier_setGatherTier]
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [InstanceState.setProcess]
    refine congrArg (Function.update (fun i => ((u i).2.roundRecord r).firstGather) j) ?_
    rfl
  · funext k
    simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_firstGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext q
    simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_firstGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · simp
  · simp only [gatherTier_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext k
    simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, inputBroadcasts_secondGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext q
    simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, bindBroadcasts_secondGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · simp

/-- The graded-agreement call against an already-called record, read through
the projection: the round loop moves and the projection is unchanged. -/
theorem roundProjection_gbcaCallLoop (hu : (u j).2 = p) (r r' : ℕ) (b : Bool)
    (c' : RoundLoopRecord P.n) :
    roundProjection P (Function.update u j (c', p))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaCallLoop r j b))) r' = roundProjection P u w r' := by
  rw [roundProjection_ghostId (Sum.inr (.gbcaCallLoop r j b)) (fun _ _ => rfl)]
  refine roundProjection_congr (fun i => ?_)
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, ← hu]
  · rw [Function.update_of_ne hi]

end Transitions

end AFW
end ABA
end PLTS
