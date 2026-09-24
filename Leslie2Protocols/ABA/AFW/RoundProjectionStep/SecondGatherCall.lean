/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The second gather's call

`roundProjection_secondGatherCall`: the projection of the composed round after the acting process
calls the second gather with the candidate on record. The transition writes the second gather's
input and sends nothing, which is what the composed round's `secondGatherCall` event and the
gather's own call write. `afterSecondGatherCall` names the state the call reaches.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### The second gather's call

The transition writes the second gather's input. It sends nothing, and the ghost record stands. -/

/-- **The round after `j`'s call of the second gather with `x`**: the program
marks the call and the second gather records the payload. -/
noncomputable def afterSecondGatherCall (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (x : Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with secondGatherCalled := true }))
    (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
      ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
        { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with input := some x }))

/-- **The second gather's call, read through the projection.** The process calls the second gather
with the candidate on record, which that gather records. -/
theorem roundProjection_secondGatherCall (hu : (u j).2 = p) (r : ℕ) (x : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with input := some x } }))
      (w.writeGhost (ghostStep P) (Sum.inr (.gbcaRoundEvent r j (.secondGatherCall x)))) r
      = afterSecondGatherCall P (roundProjection P u w r) j x := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaRoundEvent r j (.secondGatherCall x)))
      (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [afterSecondGatherCall, programs_roundProjectionUpdate,
      GBCA.ByAFW.programs_setSecondGather, GBCA.ByAFW.programs_setPrograms,
        programs_roundProjection_eq]
    refine congrArg (Function.update (fun i => programProjection ((u i).2.roundRecord r)) j) ?_
    simp only [programProjection, LocalState.setProcess, Option.isSome_some]
  · simp [afterSecondGatherCall]
  · simp only [afterSecondGatherCall, gatherTier_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setSecondGather, GBCA.ByAFW.firstGather_setPrograms,
        firstGather_roundProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext k
    simp only [afterSecondGatherCall, inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setSecondGather, GBCA.ByAFW.firstGather_setPrograms,
        firstGather_roundProjection, inputBroadcasts_firstGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext q
    simp only [afterSecondGatherCall, bindBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setSecondGather, GBCA.ByAFW.firstGather_setPrograms,
        firstGather_roundProjection, bindBroadcasts_firstGatherProjection]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · simp [afterSecondGatherCall]
  · simp only [afterSecondGatherCall, gatherTier_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setSecondGather, Gather.gatherTier_setGatherTier]
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [InstanceState.setProcess]
    refine congrArg (Function.update (fun i => ((u i).2.roundRecord r).secondGather) j) ?_
    rfl
  · funext k
    simp only [afterSecondGatherCall, inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setSecondGather, Gather.inputBroadcasts_setGatherTier]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · funext q
    simp only [afterSecondGatherCall, bindBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setSecondGather, Gather.bindBroadcasts_setGatherTier]
    exact Prod.ext (Function.update_eq_self _ _) rfl
  · simp [afterSecondGatherCall]

end Transitions

end AFW
end ABA
end PLTS
