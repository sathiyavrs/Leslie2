/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# The calls of the input-broadcast instances

`roundProjection_firstGatherInputBroadcastCall` and its companion at the second gather: the
projection of the composed round after the acting process calls the instance broadcasting its
input. The transition writes that instance's record and records its `⟨INIT, x⟩` on the network,
which is what the gather's own `inputBroadcastCall` event writes. The gather record and the round's
program stand. `firstGatherProjection_write` and its companion at the second gather read a write
that records one message through the projection of one gather instance.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The calls of the input-broadcast instances

Each transition writes the variables of the instance broadcasting the caller's input, and the
network
Each transition writes the variables of the instance broadcasting the caller's input, and the
network records that instance's `⟨INIT, x⟩`. The gather's variables, the round's program and the
ghost stand. -/

/-- The projection onto the first gather instance after a write that records one message. -/
theorem firstGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables
      P.n)
    (m : Message P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundVariables r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.firstGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_write u w j c r sr m)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables
      P.n)
    (m : Message P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundVariables r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.secondGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_write u w j c r sr m)

/-- **The call of the first gather's input-broadcast instance, read through the projection.** The
instance records the payload the gather record holds and multicasts its `⟨INIT, b⟩`. -/
theorem roundProjection_firstGatherInputBroadcastCall (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherInputBroadcasts := Function.update (p.roundVariables
            r).firstGatherInputBroadcasts
            j
            (((p.roundVariables r).firstGatherInputBroadcasts j).setProcessVariables
              { (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables) with
                input := some b })
                }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts j (.init b))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts j (.init b))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) j).processVariables j
                    with
                    input := some b }).multicast j (.init b)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts j (.init b))))
      (fun _ _ => rfl),
    roundProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [programs_roundProjectionUpdate, GBCA.ByAFW.programs_setFirstGather,
      programs_roundProjection_eq]
    exact Function.update_eq_self _ _
  · simp
  · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather,
      Gather.gatherProgramsAndNetwork_setInputBroadcasts]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
      (.firstGatherInputBroadcasts j (.init b)) rfl
  · funext k
    simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_firstGatherProjection]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.multicast, InstanceState.setProcessVariables]
        refine congrArg (Function.update
          (fun i => (((u i).2.roundVariables r).firstGatherInputBroadcasts k)) k) ?_
        rfl
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
        bindBroadcasts_firstGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
      (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · simp
  · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
      (.firstGatherInputBroadcasts j (.init b)) rfl
  · funext k
    simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection,
        inputBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
      (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · funext q
    simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection,
        bindBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
      (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · simp

/-- **The call of the second gather's input-broadcast instance, read through the projection.** -/
theorem roundProjection_secondGatherInputBroadcastCall (hu : (u j).2 = p) (r : ℕ)
    (x : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherInputBroadcasts := Function.update (p.roundVariables
            r).secondGatherInputBroadcasts j
            (((p.roundVariables r).secondGatherInputBroadcasts j).setProcessVariables
              { (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables) with
                  input := some x })
                }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init x))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) j
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) j).processVariables j
                    with
                    input := some x }).multicast j (.init x)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))
      (fun _ _ => rfl),
    roundProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [programs_roundProjectionUpdate, GBCA.ByAFW.programs_setSecondGather,
      programs_roundProjection_eq]
    exact Function.update_eq_self _ _
  · simp
  · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
      (.secondGatherInputBroadcasts j (.init x)) rfl
  · funext k
    simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection,
        inputBroadcasts_firstGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
      (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
      (.secondGatherInputBroadcasts j (.init x)) rfl
  · funext q
    simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection,
        bindBroadcasts_firstGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
      (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j
      (.secondGatherInputBroadcasts j (.init x)) rfl
  · simp
  · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setSecondGather, Gather.gatherProgramsAndNetwork_setInputBroadcasts]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
      (.secondGatherInputBroadcasts j (.init x)) rfl
  · funext k
    simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setSecondGather, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGatherProjection]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.multicast, InstanceState.setProcessVariables]
        refine congrArg (Function.update
          (fun i => (((u i).2.roundVariables r).secondGatherInputBroadcasts k)) k) ?_
        rfl
      · simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) k
          (.secondGatherInputBroadcasts k (.init x)) (.init x) (by simp
            [secondGatherInputBroadcastMessageOf])
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init x))
        (by simp [secondGatherInputBroadcastMessageOf, Ne.symm hk])
  · funext q
    simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setSecondGather, Gather.bindBroadcasts_setInputBroadcasts,
        bindBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
      (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j
      (.secondGatherInputBroadcasts j (.init x)) rfl
  · simp

end Transitions

end AFW
end ABA
end PLTS
