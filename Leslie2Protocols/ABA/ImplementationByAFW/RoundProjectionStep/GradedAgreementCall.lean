/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The graded-agreement call and its loop

`roundProjection_callG` and `roundProjection_gbcaCallLoop`: the view of the composed round after a
call of graded agreement. The call is fused (D28): the round's first gather records the input and
the caller's own input-broadcast instance of that gather is called with it, and the composed round
answers on one label whose program row records the input and whose first gather takes
`Gather.StepOverBracha.call`. A call against an already-called record moves the round loop alone,
which the view does not read.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### The graded-agreement call and its loop

The call is fused (D28): the round's first gather records the input and the
caller's own input-broadcast instance of that gather is called with it. The
composed round answers on one label, whose program row records the input and
whose first gather takes `Gather.StepOverBracha.call`. The call against an
already-called record moves the round loop alone, which the view does not
read. -/

/-- The graded-agreement call, read through the view. -/
theorem roundProjection_callG (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with input := some b }
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            j
            (((p.roundRecord r).firstGatherInputBroadcasts j).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts j).process) with input := some b })
                }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts j (.init b))).writeGhost (ghostStep P)
        (Sum.inl (.callG r j b))) r
      = GBCA.ByAFW.setFirstGather (GBCA.ByAFW.setPrograms (roundProjection P u w r)
            (Function.update (GBCA.ByAFW.programs (roundProjection P u w r)) j
              { GBCA.ByAFW.programs (roundProjection P u w r) j with input := some b }))
          (Gather.setInputBroadcasts (Gather.setGatherTier (firstGatherProjection P u w r)
              ((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with input := some b
                  }))
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) j).setProcess j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) j).process j with
                    input := some b }).multicast j (.init b)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inl (.callG r j b)) (fun _ _ => rfl), roundProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [programs_roundProjectionUpdate, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq]
    refine congrArg (Function.update (fun i => programProjection ((u i).2.roundRecord r)) j) ?_
    simp only [programProjection, LocalState.setProcess]
  · simp
  · simp only [gatherTier_firstGather_roundProjectionUpdate, GBCA.ByAFW.firstGather_setFirstGather,
    Gather.gatherTier_setInputBroadcasts,
      Gather.gatherTier_setGatherTier]
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [InstanceState.setProcess]
      refine congrArg (Function.update
        (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
          r).firstGatherInputBroadcasts
          ((u i).2.roundRecord r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_setProcess, InstanceState.process,
        gatherTier_firstGatherProjection_process, localState_setProcess_process,
          localState_setProcess_received]
      simp only [LocalState.setProcess]
    · exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherInputBroadcasts j (.init b)) rfl
  · funext k
    simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_firstGatherProjection]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.multicast, InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => broadcastLocalState P (((u i).2.roundRecord r).firstGatherInputBroadcasts k)) k)
            ?_
        simp only [InstanceState.process, broadcastLocalState, LocalState.setProcess,
          broadcastReturnsFor_mk_eq]
      · simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) k
          (.firstGatherInputBroadcasts k (.init b)) (.init b) (by simp
            [firstGatherInputBroadcastMessageOf])
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts j
          (.init b))
        (by simp [firstGatherInputBroadcastMessageOf, Ne.symm hk])
  · funext q
    simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.bindBroadcasts_setInputBroadcasts,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
      (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · simp
  · simp only [gatherTier_secondGather_roundProjectionUpdate,
    GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
      secondGather_roundProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext
        ?_ rfl)
    exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
      (.firstGatherInputBroadcasts j (.init b)) rfl
  · funext k
    simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, inputBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
      (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · funext q
    simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, bindBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
      (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · simp

/-- The graded-agreement call against an already-called record, read through
the view: the round loop moves and the view is unchanged. -/
theorem roundProjection_gbcaCallLoop (hu : (u j).2 = p) (r r' : ℕ) (b : Bool)
    (c' : RoundLoopRecord P.n) :
    roundProjection P (Function.update u j (c', p))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaCallLoop r j b))) r' = roundProjection P u w r' := by
  rw [roundProjection_ghostId (Sum.inr (.gbcaCallLoop r j b)) (fun _ _ => rfl)]
  refine roundProjection_congr (fun i => ?_)
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, ← hu]
  · rw [Function.update_of_ne hi]

end Rows

end AFW
end ABA
end PLTS
