/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.BroadcastSend
import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.GatherSend
import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The rows of the two gathers and of the broadcast instances

`roundProjection_firstGatherEcho` and its thirteen companions: the view of the composed round after
each `ECHO`, `VOTE` and `BIND` row of the two gathers and of their four broadcast families. Each is
the send of `RoundProjectionStep/GatherSend.lean` or `RoundProjectionStep/BroadcastSend.lean` read
at the label the implementation row carries, over the effect the composed round's own row
writes.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### The rows of the two gathers and of the broadcast instances

Each row below is one implementation row, read through the view over the effect the
composed round's own row writes. -/

/-- The first gather's `ECHO`, read through the view. -/
theorem roundProjection_firstGatherEcho (hu : (u j).2 = p) (r : ℕ)
    (A : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with sentEcho := some A } }))
      ((w.recordGBCASend r j (.firstGather (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGather (.echo A))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r)
            (((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                  sentEcho :=
                    some A }).multicast
              j (.echo A))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGather (.echo A)))) (fun _ _ => rfl)]
  exact roundProjection_firstGatherSend rfl r _ (.echo A) rfl

/-- The first gather's `VOTE`, read through the view. -/
theorem roundProjection_firstGatherVote (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with sentVote := some U } }))
      ((w.recordGBCASend r j (.firstGather (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGather (.vote U))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r)
            (((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                  sentVote :=
                    some U }).multicast
              j (.vote U))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGather (.vote U)))) (fun _ _ => rfl)]
  exact roundProjection_firstGatherSend rfl r _ (.vote U) rfl

/-- The second gather's `ECHO`, read through the view. -/
theorem roundProjection_secondGatherEcho (hu : (u j).2 = p) (r : ℕ)
    (A : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with sentEcho := some A } }))
      ((w.recordGBCASend r j (.secondGather (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGather (.echo A))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r)
            (((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (secondGatherProjection P u w r)).process j with
                  sentEcho :=
                    some A }).multicast
              j (.echo A))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGather (.echo A)))) (fun _ _ => rfl)]
  exact roundProjection_secondGatherSend rfl r _ (.echo A) rfl rfl

/-- The second gather's `VOTE`, read through the view. -/
theorem roundProjection_secondGatherVote (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with sentVote := some U } }))
      ((w.recordGBCASend r j (.secondGather (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGather (.vote U))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r)
            (((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (secondGatherProjection P u w r)).process j with
                  sentVote :=
                    some U }).multicast
              j (.vote U))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGather (.vote U)))) (fun _ _ => rfl)]
  exact roundProjection_secondGatherSend rfl r _ (.vote U) rfl rfl

/-- The first gather's `BIND`, read through the view: the payload is written to
the sender's gather record and is the input of the sender's own bind-broadcast
instance, which broadcasts it. -/
theorem roundProjection_firstGatherBind (hu : (u j).2 = p) (r : ℕ) (U : Gather.AcceptedPairs P.n
  Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with sentBind := some U }
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts j
            (((p.roundRecord r).firstGatherBindBroadcasts j).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts j).process) with input := some U })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts
            (Gather.setGatherTier (firstGatherProjection P u w r)
              ((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                  sentBind :=
                    some U }))
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) j).setProcess j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) j).process j with
                    input := some U }).multicast
                j (.init U)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))
    (fun _ _ => rfl),
    roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection,
      LocalState.setProcess]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection, gatherLocalState, broadcastReturnsFor_update_setProcess]
      simp only [InstanceState.setProcess, InstanceState.process, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherBindBroadcasts j (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts j (.init
          U)) rfl
  · funext k
    by_cases hk : k = j
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_self, InstanceState.multicast,
            InstanceState.setProcess,
        InstanceState.process, broadcastLocalState, LocalState.setProcess,
          broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_self, InstanceState.multicast,
            ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) k
          (.firstGatherBindBroadcasts k (.init U)) (.init U) (by simp
            [firstGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_self, InstanceState.multicast,
            InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_of_ne hk]
        exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts j
            (.init U))
          (by simp [firstGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_of_ne hk]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGatherBindBroadcasts j (.init U)) rfl
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
            (w.sent r) j (.firstGatherBindBroadcasts j
          (.init U)) rfl
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
          k) (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts j
            (.init
          U)) rfl

/-- The second gather's `BIND`, read through the view. -/
theorem roundProjection_secondGatherBind (hu : (u j).2 = p) (r : ℕ) (U : Gather.AcceptedPairs P.n
  (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with sentBind := some U }
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            j
            (((p.roundRecord r).secondGatherBindBroadcasts j).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts j).process) with input := some U })
                }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts
            (Gather.setGatherTier (secondGatherProjection P u w r)
              ((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (secondGatherProjection P u w r)).process j with
                  sentBind :=
                    some U }))
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) j
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) j).setProcess j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) j).process j with
                    input := some U }).multicast
                j (.init U)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))
    (fun _ _ => rfl),
    roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection,
      LocalState.setProcess]
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
          firstGatherMessageOf_inj (w.sent r) j (.secondGatherBindBroadcasts j (.init U)) rfl
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
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
          (.init U)) rfl
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
          k) (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
            (.init
          U)) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection, gatherLocalState, broadcastReturnsFor_update_setProcess]
      simp only [InstanceState.setProcess, InstanceState.process, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherBindBroadcasts j (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
          (.init U)) rfl
  · funext k
    by_cases hk : k = j
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_self,
            InstanceState.multicast, InstanceState.setProcess,
        InstanceState.process, broadcastLocalState, LocalState.setProcess,
          broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_self,
            InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) k
          (.secondGatherBindBroadcasts k (.init U)) (.init U) (by simp
            [secondGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_self,
            InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_of_ne hk]
        exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
            (.init U))
          (by simp [secondGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_of_ne hk]

/-- `ECHO` in an input-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherInputBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            i
            (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the first gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem roundProjection_firstGatherInputBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            i
            (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherBindBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts i
            (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentEcho := some m })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the first gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem roundProjection_firstGatherBindBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts i
            (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentVote := some m })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in an input-broadcast instance of the second gather, read through
the view. -/
theorem roundProjection_secondGatherInputBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts i
            (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the second gather, read through
the view. The quorum row and the amplification row write this record. -/
theorem roundProjection_secondGatherInputBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts i
            (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the second gather, read through the
view. -/
theorem roundProjection_secondGatherBindBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            i
            (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the second gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem roundProjection_secondGatherBindBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            i
            (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r i _ (.vote m)

end Rows

end AFW
end ABA
end PLTS
