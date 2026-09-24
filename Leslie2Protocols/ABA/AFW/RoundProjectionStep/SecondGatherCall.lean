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
input and the input-broadcast instance of that gather it calls, and records that instance's
`⟨INIT, x⟩` on the network, which is what the composed round's `secondGatherCall` event and the
gather's own call write. `afterSecondGatherCall` names the state the call reaches.
`firstGatherProjection_write` and its companion at the second gather read a write that records one
message through the projection of one gather instance.
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

The transition writes the second gather's input and the record of the instance broadcasting it,
and the network records that instance's `⟨INIT, x⟩`. The ghost record stands. -/

/-- The projection onto the first gather instance after a write that records one message. -/
theorem firstGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n)
    (m : Message P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.firstGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_write u w j c r sr m)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n)
    (m : Message P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.secondGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_write u w j c r sr m)

/-- **The round after `j`'s call of the second gather with `x`**: the program
marks the call and the second gather takes its call. -/
noncomputable def afterSecondGatherCall (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (x : Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with secondGatherCalled := true }))
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with input := some x }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) j
        (((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) j).setProcess j
            { (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) j).process j with input := some x
              }).multicast
          j (.init x))))

/-- **The second gather's call, read through the projection.** The process calls the second gather
with the candidate on record, broadcasting it through its own input-broadcast instance of that
gather. -/
theorem roundProjection_secondGatherCall (hu : (u j).2 = p) (r : ℕ) (x : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with input := some x }
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts j
            (((p.roundRecord r).secondGatherInputBroadcasts j).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts j).process) with
                input := some x }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init x))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))) r
      = afterSecondGatherCall P (roundProjection P u w r) j x := by
  subst hu
  rw [roundProjection_gbcaSendGhost, firstGatherProjection_write, secondGatherProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherCall, GBCA.ByAFW.programs_setSecondGather,
      GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq,
      roundRecord_update_self rfl, locals_programProjection_if]
    simp only [programs_mk, programProjection, LocalState.setProcess, Option.isSome_some]
  · simp only [afterSecondGatherCall, GBCA.ByAFW.bound_setSecondGather,
      GBCA.ByAFW.bound_setPrograms, bound_roundProjection]
    simp only [bound_mk, ghostStep]
  · simp only [afterSecondGatherCall, GBCA.ByAFW.firstGather_setSecondGather,
      GBCA.ByAFW.firstGather_setPrograms, firstGather_roundProjection]
    simp only [firstGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, gatherTier_firstGather_roundProjectionUpdate]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.secondGatherInputBroadcasts j (.init x)) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore,
        inputBroadcasts_firstGather_roundProjectionUpdate, inputBroadcasts_firstGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init x)) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
        (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init x)) rfl
    · simp only [Gather.core_setCore, core_firstGatherProjection]
  · simp only [afterSecondGatherCall, GBCA.ByAFW.secondGather_setSecondGather,
      secondGather_roundProjection]
    simp only [secondGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, Gather.gatherTier_setInputBroadcasts,
        Gather.gatherTier_setGatherTier, gatherTier_secondGather_roundProjectionUpdate]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => ((u i).2.roundRecord r).secondGather) j) ?_
        rfl
      · exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r)
          j (.secondGatherInputBroadcasts j (.init x)) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        refine Prod.ext ?_ (networkState_ext ?_ rfl)
        · simp only [InstanceState.multicast, InstanceState.setProcess]
          rfl
        · simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
          exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) k
            (.secondGatherInputBroadcasts k (.init x)) (.init x)
            (by simp [secondGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherInputBroadcasts j (.init x)) (by simp
            [secondGatherInputBroadcastMessageOf, Ne.symm hk])
    · funext q
      simp only [Gather.bindBroadcasts_setCore, Gather.bindBroadcasts_setInputBroadcasts,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
        (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init x)) rfl
    · simp only [Gather.core_setCore, Gather.core_setInputBroadcasts,
        Gather.core_setGatherTier, core_secondGatherProjection]

end Transitions

end AFW
end ABA
end PLTS
