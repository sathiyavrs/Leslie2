/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# A send of a gather instance

`roundProjection_firstGatherSend` and `roundProjection_secondGatherSend`: the view of the composed
round after a gather's `ECHO` or `VOTE`. The row writes the sender's gather record and records on
the gather's network state, and the composed round writes the same through
`Gather.setGatherTier`.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### A send of a gather instance

A gather's `ECHO` and `VOTE` write the sender's gather record and record on the
gather's network state. Each is the gather's `send` event, which
`Gather.StepOverBracha.echo` and `Gather.StepOverBracha.vote` write through
`Gather.setGatherTier`. -/

/-- A send of the first gather, read through the view. -/
theorem roundProjection_firstGatherSend (hu : (u j).2 = p) (r : ℕ)
    (pr : Gather.BaseProcessRecord P.n Bool) (m : Gather.Message P.n Bool)
    (hin : pr.input = ((p.roundRecord r).firstGather.process).input) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with firstGather := (p.roundRecord r).firstGather.setProcess pr }))
      (w.recordGBCASend r j (.firstGather m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r)
            (((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { pr with
                  inputBroadcastReturned := fun k => broadcastReturnsFor P ((p.roundRecord
                    r).firstGatherInputBroadcasts k)
                  bindBroadcastReturned := fun q => broadcastReturnsFor P ((p.roundRecord
                    r).firstGatherBindBroadcasts q) }).multicast j m)) := by
  rw [← hu] at hin ⊢
  rw [roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
      roundProjectionUpdate, programProjection, LocalState.setProcess, hin]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        gatherLocalState, InstanceState.multicast, InstanceState.setProcess, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        InstanceState.multicast, ABA.NetworkState.recordSent]
      exact messagesOf_recordSent_some firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGather m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
        (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGather m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGather m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none
          (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj k)
            (w.sent r) j (.firstGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          q) (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGather m) rfl

/-- A send of the second gather, read through the view. -/
theorem roundProjection_secondGatherSend (hu : (u j).2 = p) (r : ℕ)
    (pr : Gather.BaseProcessRecord P.n (Option Bool)) (m : Gather.Message P.n (Option Bool))
    (hin : pr.input = ((p.roundRecord r).secondGather.process).input)
    (hret : pr.returned = ((p.roundRecord r).secondGather.process).returned) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with secondGather := (p.roundRecord r).secondGather.setProcess pr }))
      (w.recordGBCASend r j (.secondGather m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r)
            (((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { pr with
                  inputBroadcastReturned := fun k => broadcastReturnsFor P ((p.roundRecord
                    r).secondGatherInputBroadcasts k)
                  bindBroadcastReturned := fun q => broadcastReturnsFor P ((p.roundRecord
                    r).secondGatherBindBroadcasts q) }).multicast j m)) := by
  rw [← hu] at hin hret ⊢
  rw [roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
      roundProjectionUpdate, programProjection, LocalState.setProcess, hin, hret]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf
          firstGatherMessageOf_inj (w.sent r) j (.secondGather m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          q) (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.secondGather m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        gatherLocalState, InstanceState.multicast, InstanceState.setProcess, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        InstanceState.multicast, ABA.NetworkState.recordSent]
      exact messagesOf_recordSent_some secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGather m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
        (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.secondGather m) rfl

end Rows

end AFW
end ABA
end PLTS
