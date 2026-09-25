/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# A send in a broadcast instance

`roundProjection_firstGatherInputBroadcastSend` and its three companions: the projection of the
composed round after a Bracha send in one broadcast instance of either gather. The transition writes
the sender's local state in that instance and records on the instance's network state, and the
composed round reaches the instance through `Gather.setInputBroadcasts` or
`Gather.setBindBroadcasts`. The returned value does not move, so the return flag the projection
supplies stands.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### A send in a broadcast instance

A Bracha transition writes the sender's local state in one broadcast instance and records on that
instance's network state. Each is the instance's `send` event, which `BRB.BrachaAlgorithm.echo`,
`BRB.BrachaAlgorithm.voteQuorum` and `BRB.BrachaAlgorithm.voteAmplification` write, and the composed
round reaches it through `Gather.setInputBroadcasts` or `Gather.setBindBroadcasts`. The
return flag the projection supplies is the returned value's, which a local write does not move. -/

/-- A send in an input-broadcast instance of the first gather, read through the
projection. -/
theorem roundProjection_firstGatherInputBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessVariables Bool) (m : BRB.Message Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherInputBroadcasts := Function.update (p.roundVariables
            r).firstGatherInputBroadcasts
            i
            (((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables pr) }))
      (w.recordGBCASend r j (.firstGatherInputBroadcasts i m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcessVariables j
                  pr).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          ]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherInputBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
            
        LocalState.setProcessVariables, ]
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.firstGatherInputBroadcasts k m) m (by simp [firstGatherInputBroadcastMessageOf])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
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
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setFirstGather,
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
projection. -/
theorem roundProjection_firstGatherBindBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessVariables (Gather.AcceptedPairs P.n Bool)) (m : BRB.Message
      (Gather.AcceptedPairs
      P.n Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherBindBroadcasts := Function.update (p.roundVariables
            r).firstGatherBindBroadcasts i
            (((p.roundVariables r).firstGatherBindBroadcasts i).setProcessVariables pr) }))
      (w.recordGBCASend r j (.firstGatherBindBroadcasts i m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcessVariables j
                  pr).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        ]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
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
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
            
        LocalState.setProcessVariables, ]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j
          (.firstGatherBindBroadcasts k m) m (by simp [firstGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
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
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setFirstGather,
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
the projection. -/
theorem roundProjection_secondGatherInputBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessVariables (Option Bool)) (m : BRB.Message (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherInputBroadcasts := Function.update (p.roundVariables
            r).secondGatherInputBroadcasts i
            (((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables pr) }))
      (w.recordGBCASend r j (.secondGatherInputBroadcasts i m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcessVariables j
                  pr).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setSecondGather,
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
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setInputBroadcasts,
        GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          ]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setInputBroadcasts,
        GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherInputBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
            
        LocalState.setProcessVariables, ]
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherInputBroadcasts k m) m (by simp [secondGatherInputBroadcastMessageOf])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
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
projection. -/
theorem roundProjection_secondGatherBindBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessVariables (Gather.AcceptedPairs P.n (Option Bool)))
    (m : BRB.Message (Gather.AcceptedPairs P.n (Option Bool))) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherBindBroadcasts := Function.update (p.roundVariables
            r).secondGatherBindBroadcasts
            i
            (((p.roundVariables r).secondGatherBindBroadcasts i).setProcessVariables pr) }))
      (w.recordGBCASend r j (.secondGatherBindBroadcasts i m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcessVariables j
                  pr).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setSecondGather,
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
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        ]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
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
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
            
        LocalState.setProcessVariables, ]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherBindBroadcasts k m) m (by simp [secondGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcessVariables,
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

end Transitions

end AFW
end ABA
end PLTS
