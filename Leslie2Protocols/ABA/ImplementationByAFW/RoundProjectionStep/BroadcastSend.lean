/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# A send in a broadcast instance

`roundProjection_firstGatherInputBroadcastSend` and its three companions: the view of the composed
round after a Bracha send in one broadcast instance of either gather. The row writes the sender's
local state in that instance and records on the instance's network state, and the composed round
reaches the instance through `Gather.setInputBroadcasts` or `Gather.setBindBroadcasts`. The
returned value does not move, so the return flag the view supplies stands.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### A send in a broadcast instance

A Bracha row writes the sender's local state in one broadcast instance and records on that
instance's network state. Each is the instance's `send` event, which `BRB.BrachaStep.echo`,
`BRB.BrachaStep.voteQuorum` and `BRB.BrachaStep.voteAmplification` write, and the composed round
reaches it through `Gather.setInputBroadcasts` or `Gather.setBindBroadcasts`. The return flag the
view supplies is the returned value's, which a local write does not move. -/

/-- A send in an input-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherInputBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord Bool) (m : BRB.Message Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            i
            (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.firstGatherInputBroadcasts i m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).firstGatherInputBroadcasts
                        i)).isSome }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherInputBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.firstGatherInputBroadcasts k m) m (by simp [firstGatherInputBroadcastMessageOf])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts i m)
          (by simp [firstGatherInputBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k)
        (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts i m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGatherInputBroadcasts i m) rfl
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
            (w.sent r) j (.firstGatherInputBroadcasts i m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          k) (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts i
            m)
          rfl

/-- A send in a bind-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherBindBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord (Gather.AcceptedPairs P.n Bool)) (m : BRB.Message (Gather.AcceptedPairs
      P.n Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts i
            (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.firstGatherBindBroadcasts i m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).firstGatherBindBroadcasts i)).isSome
                        }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherBindBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j
          (.firstGatherBindBroadcasts k m) m (by simp [firstGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts i m)
          (by simp [firstGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGatherBindBroadcasts i m) rfl
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
            (w.sent r) j (.firstGatherBindBroadcasts i m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          k) (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts i
            m) rfl

/-- A send in an input-broadcast instance of the second gather, read through
the view. -/
theorem roundProjection_secondGatherInputBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord (Option Bool)) (m : BRB.Message (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts i
            (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.secondGatherInputBroadcasts i m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).secondGatherInputBroadcasts
                        i)).isSome }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection]
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
          firstGatherMessageOf_inj (w.sent r) j (.secondGatherInputBroadcasts i m) rfl
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
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i
            m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          k) (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i
            m)
          rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherInputBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherInputBroadcasts k m) m (by simp [secondGatherInputBroadcastMessageOf])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i
            m)
          (by simp [secondGatherInputBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k)
        (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i m)
          rfl

/-- A send in a bind-broadcast instance of the second gather, read through the
view. -/
theorem roundProjection_secondGatherBindBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord (Gather.AcceptedPairs P.n (Option Bool)))
    (m : BRB.Message (Gather.AcceptedPairs P.n (Option Bool))) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            i
            (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.secondGatherBindBroadcasts i m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).secondGatherBindBroadcasts
                        i)).isSome }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection]
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
          firstGatherMessageOf_inj (w.sent r) j (.secondGatherBindBroadcasts i m) rfl
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
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i
            m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          k) (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i
            m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherBindBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i m)
          rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherBindBroadcasts k m) m (by simp [secondGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i m)
          (by simp [secondGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]

end Rows

end AFW
end ABA
end PLTS
