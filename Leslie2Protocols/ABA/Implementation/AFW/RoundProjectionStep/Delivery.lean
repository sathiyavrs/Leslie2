/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# A delivery

`roundProjection_deliverFirstGather` and its nine companions: the view of the composed round after
a delivery. The row files the message in the receiver's own local state of the network state the
message's tag names. A gather message moves the gather instance alone. A broadcast message moves
the broadcast instance, and, where it completes a `2f + 1` `VOTE` quorum at the receiver, the
instance returns to the receiver as well: the return flag goes on and what the receiver's gather
instance returned records the value. The quorum lemmas carry the hypothesis that the returned value
holds the delivered value after the delivery, and the plain lemmas the hypothesis that the returned
value does not move; `AFW.broadcastReturnsFor_eq_of_quorum` supplies the first under
`AFW.BroadcastReturnsInvariant`. `afterFirstGatherInputBroadcastDeliver` and its seven companions
name the states between the two events.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### A delivery

A delivery of the implementation files the message in the receiver's own local state of the network
state the message's tag names. A gather message moves the gather instance alone. A broadcast message
moves the broadcast instance, and, where it completes a `2f + 1` `VOTE` quorum at the receiver, the
instance returns to the receiver as well: the return flag goes on and what the receiver's gather
instance returned records the value. -/

/-- A delivery on the first gather's network, read through the view. -/
theorem roundProjection_deliverFirstGather (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.Message P.n Bool) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGather mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGather mm)))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r) ((Gather.gatherTier
            (firstGatherProjection P u w r)).receiveMessage j k mm)) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGather mm))) (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
    programs_roundProjectionUpdate, programProjection, LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setGatherTier,
      InstanceState.receiveMessage, gatherTier_firstGatherProjection_network]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
          r).firstGatherInputBroadcasts
          ((u i).2.roundRecord r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, gatherTier_firstGatherProjection_process, LocalState.deliverTo]
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherTier, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery on the second gather's network, read through the view. -/
theorem roundProjection_deliverSecondGather (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.Message P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGather mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGather mm)))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r) ((Gather.gatherTier
            (secondGatherProjection P u w r)).receiveMessage j k mm)) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGather mm))) (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
    programs_roundProjectionUpdate, programProjection, LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate, Gather.gatherTier_setGatherTier,
      InstanceState.receiveMessage,
        gatherTier_secondGatherProjection_network]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
          i).2.roundRecord r).secondGatherInputBroadcasts
          ((u i).2.roundRecord r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, gatherTier_secondGatherProjection_process, LocalState.deliverTo]
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherTier, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in an input-broadcast instance of the first
gather.** -/
noncomputable def afterFirstGatherInputBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n) (m : BRB.Message Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setInputBroadcasts (GBCA.ByAFW.firstGather s)
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).receiveMessage j k m)))

/-- **The round after an input-broadcast instance of the first gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterFirstGatherInputBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with
            inputBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process
                j).inputBroadcastReturned i (some v) }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).setProcess j
          { (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).process j with returned := true
            })))

/-- A delivery in an input-broadcast instance of the first gather that leaves the returned value
where it stands, read through the view. -/
theorem roundProjection_deliverFirstGatherInputBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherInputBroadcasts i).deliverTo k mm) =
      broadcastReturnsFor P
    ((p.roundRecord r).firstGatherInputBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherInputBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm)))) r
    = afterFirstGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.programs_setFirstGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherInputBroadcastDeliver]
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.firstGather_setFirstGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setInputBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_firstGatherProjection_fst]
      have hv : gatherLocalState P Bool ((u j).2.roundRecord r).firstGather
          (Function.update ((u j).2.roundRecord r).firstGatherInputBroadcasts i
            ((((u j).2.roundRecord r).firstGatherInputBroadcasts i).deliverTo k mm)) ((u
              j).2.roundRecord r).firstGatherBindBroadcasts
          = gatherLocalState P Bool ((u j).2.roundRecord r).firstGather ((u j).2.roundRecord
            r).firstGatherInputBroadcasts
              ((u j).2.roundRecord r).firstGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.secondGather_setFirstGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in an input-broadcast instance of the first gather that
completes a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverFirstGatherInputBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message Bool) (v : Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherInputBroadcasts i).deliverTo k mm) =
      some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherInputBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i
          mm)))) r
      = afterFirstGatherInputBroadcastReturn P (afterFirstGatherInputBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver,
    GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver]
  · simp only [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver,
    GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection,
      Gather.gatherTier_setInputBroadcasts, Gather.inputBroadcasts_setInputBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate,
      Gather.gatherTier_setInputBroadcasts, Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_firstGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P Bool ((u i').2.roundRecord r).firstGather
          ((u i').2.roundRecord r).firstGatherInputBroadcasts ((u i').2.roundRecord
            r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_firstGatherProjection_process, LocalState.setProcess]
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_firstGather_roundProjectionUpdate, inputBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setInputBroadcasts, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_firstGather_roundProjectionUpdate, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver,
    GBCA.ByAFW.secondGather_setFirstGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in a bind-broadcast instance of the first
gather.** -/
noncomputable def afterFirstGatherBindBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n)
    (m : BRB.Message (Gather.AcceptedPairs P.n Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setBindBroadcasts (GBCA.ByAFW.firstGather s)
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).receiveMessage j k m)))

/-- **The round after a bind-broadcast instance of the first gather returns `v`
to `j`**: the instance's return flag goes on at `j` and `j`'s gather record
files the value. -/
noncomputable def afterFirstGatherBindBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Gather.AcceptedPairs P.n Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setBindBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with
            bindBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process
                j).bindBroadcastReturned i (some v) }))
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).setProcess j
          { (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).process j with returned := true
            })))

/-- A delivery in a bind-broadcast instance of the first gather that leaves the returned value where
it stands, read through the view. -/
theorem roundProjection_deliverFirstGatherBindBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n Bool))
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherBindBroadcasts i).deliverTo k mm) =
      broadcastReturnsFor P
    ((p.roundRecord r).firstGatherBindBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherBindBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm)))) r
    = afterFirstGatherBindBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherBindBroadcastDeliver, GBCA.ByAFW.programs_setFirstGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherBindBroadcastDeliver]
  · simp only [afterFirstGatherBindBroadcastDeliver, GBCA.ByAFW.firstGather_setFirstGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setBindBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_firstGatherProjection_fst]
      have hv : gatherLocalState P Bool ((u j).2.roundRecord r).firstGather
          ((u j).2.roundRecord r).firstGatherInputBroadcasts (Function.update ((u j).2.roundRecord
            r).firstGatherBindBroadcasts i
            ((((u j).2.roundRecord r).firstGatherBindBroadcasts i).deliverTo k mm))
          = gatherLocalState P Bool ((u j).2.roundRecord r).firstGather ((u j).2.roundRecord
            r).firstGatherInputBroadcasts
              ((u j).2.roundRecord r).firstGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext q
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts, bindBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherBindBroadcastDeliver, GBCA.ByAFW.secondGather_setFirstGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in a bind-broadcast instance of the first gather that completes
a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverFirstGatherBindBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message (Gather.AcceptedPairs P.n Bool))
    (v : Gather.AcceptedPairs P.n Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherBindBroadcasts i).deliverTo k mm) =
      some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherBindBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i
          mm)))) r
      = afterFirstGatherBindBroadcastReturn P (afterFirstGatherBindBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver,
    GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver]
  · simp only [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver,
    GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection,
      Gather.gatherTier_setBindBroadcasts, Gather.bindBroadcasts_setBindBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setBindBroadcasts,
      Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_firstGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P Bool ((u i').2.roundRecord r).firstGather
          ((u i').2.roundRecord r).firstGatherInputBroadcasts ((u i').2.roundRecord
            r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_firstGatherProjection_process, LocalState.setProcess]
    · funext q
      simp only [Gather.inputBroadcasts_setBindBroadcasts, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_firstGather_roundProjectionUpdate, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_firstGather_roundProjectionUpdate, bindBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver,
    GBCA.ByAFW.secondGather_setFirstGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in an input-broadcast instance of the second
gather.** -/
noncomputable def afterSecondGatherInputBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n) (m : BRB.Message (Option Bool)) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setInputBroadcasts (GBCA.ByAFW.secondGather s)
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).receiveMessage j k m)))

/-- **The round after an input-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterSecondGatherInputBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Option Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with
            inputBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process
                j).inputBroadcastReturned i (some v) }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).setProcess j
          { (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).process j with returned := true
            })))

/-- A delivery in an input-broadcast instance of the second gather that leaves the returned value
where it stands, read through the view. -/
theorem roundProjection_deliverSecondGatherInputBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Option Bool))
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherInputBroadcasts i).deliverTo k mm)
      = broadcastReturnsFor P
    ((p.roundRecord r).secondGatherInputBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherInputBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm))))
    r = afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))
    (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.programs_setSecondGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherInputBroadcastDeliver]
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.firstGather_setSecondGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.secondGather_setSecondGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
      Gather.gatherTier_setInputBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_secondGatherProjection_fst]
      have hv : gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather
          (Function.update ((u j).2.roundRecord r).secondGatherInputBroadcasts i
            ((((u j).2.roundRecord r).secondGatherInputBroadcasts i).deliverTo k mm)) ((u
              j).2.roundRecord r).secondGatherBindBroadcasts
          = gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather ((u
            j).2.roundRecord r).secondGatherInputBroadcasts
              ((u j).2.roundRecord r).secondGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in an input-broadcast instance of the second gather that
completes a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverSecondGatherInputBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message (Option Bool)) (v : Option Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherInputBroadcasts i).deliverTo k mm)
      = some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherInputBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i
          mm)))) r
      = afterSecondGatherInputBroadcastReturn P (afterSecondGatherInputBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))
    (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver,
    GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver]
  · simp only [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver,
    GBCA.ByAFW.firstGather_setSecondGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver,
    GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection,
      Gather.gatherTier_setInputBroadcasts, Gather.inputBroadcasts_setInputBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
      Gather.gatherTier_setInputBroadcasts, Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_secondGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P (Option Bool) ((u i').2.roundRecord r).secondGather
          ((u i').2.roundRecord r).secondGatherInputBroadcasts ((u i').2.roundRecord
            r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_secondGatherProjection_process, LocalState.setProcess]
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setInputBroadcasts, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in a bind-broadcast instance of the second
gather.** -/
noncomputable def afterSecondGatherBindBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n)
    (m : BRB.Message (Gather.AcceptedPairs P.n (Option Bool))) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setBindBroadcasts (GBCA.ByAFW.secondGather s)
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).receiveMessage j k m)))

/-- **The round after a bind-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterSecondGatherBindBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n)
    (v : Gather.AcceptedPairs P.n (Option Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setBindBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with
            bindBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process
                j).bindBroadcastReturned i (some v) }))
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).setProcess j
          { (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).process j with returned := true
            })))

/-- A delivery in a bind-broadcast instance of the second gather that leaves the returned value
where it stands, read through the view. -/
theorem roundProjection_deliverSecondGatherBindBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n (Option Bool)))
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherBindBroadcasts i).deliverTo k mm) =
      broadcastReturnsFor P
    ((p.roundRecord r).secondGatherBindBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherBindBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm)))) r
    = afterSecondGatherBindBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherBindBroadcastDeliver, GBCA.ByAFW.programs_setSecondGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherBindBroadcastDeliver]
  · simp only [afterSecondGatherBindBroadcastDeliver, GBCA.ByAFW.firstGather_setSecondGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherBindBroadcastDeliver, GBCA.ByAFW.secondGather_setSecondGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate, Gather.gatherTier_setBindBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_secondGatherProjection_fst]
      have hv : gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather
          ((u j).2.roundRecord r).secondGatherInputBroadcasts (Function.update ((u j).2.roundRecord
            r).secondGatherBindBroadcasts i
            ((((u j).2.roundRecord r).secondGatherBindBroadcasts i).deliverTo k mm))
          = gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather ((u
            j).2.roundRecord r).secondGatherInputBroadcasts
              ((u j).2.roundRecord r).secondGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext q
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts, bindBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in a bind-broadcast instance of the second gather that completes
a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverSecondGatherBindBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message (Gather.AcceptedPairs P.n (Option Bool)))
    (v : Gather.AcceptedPairs P.n (Option Bool))
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherBindBroadcasts i).deliverTo k mm) =
      some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherBindBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i
          mm)))) r
      = afterSecondGatherBindBroadcastReturn P (afterSecondGatherBindBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver,
    GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver]
  · simp only [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver,
    GBCA.ByAFW.firstGather_setSecondGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver,
    GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection,
      Gather.gatherTier_setBindBroadcasts, Gather.bindBroadcasts_setBindBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
      Gather.gatherTier_setBindBroadcasts, Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_secondGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P (Option Bool) ((u i').2.roundRecord r).secondGather
          ((u i').2.roundRecord r).secondGatherInputBroadcasts ((u i').2.roundRecord
            r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_secondGatherProjection_process, LocalState.setProcess]
    · funext q
      simp only [Gather.inputBroadcasts_setBindBroadcasts, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

end Rows

end AFW
end ABA
end PLTS
