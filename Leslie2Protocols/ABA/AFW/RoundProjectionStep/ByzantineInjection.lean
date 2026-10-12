/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# A Byzantine injection

`roundProjection_byzantineFirstGather` and its three companions: the projection of the composed
round after an injection. The adversary multicasts on behalf of a corrupted sender, the message
reaches the network state its tag names, and no process's variables move.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### A Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the network state its tag names and no process's variables move. -/

/-- A Byzantine injection on the first gather's network state, read through the
projection. -/
theorem roundProjection_byzantineFirstGather (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (mm : Gather.Message P.n Bool) :
    roundProjection P u (w.recordGBCASend r k (.firstGather mm)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
            ((Gather.gatherProgramsAndNetwork
            (firstGatherProjection P u w r)).multicast k mm)) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
        InstanceState.multicast,
        ABA.NetworkState.recordSent, gatherProgramsAndNetwork_firstGatherProjection_network,
          recordGBCASend_sent_self]
      exact messagesOf_recordSent_some firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.firstGather mm) mm rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setGatherProgramsAndNetwork,
        inputBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGather mm) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherProgramsAndNetwork_secondGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.firstGather mm) rfl
    · funext k'
      simp only [inputBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGather mm) rfl
    · simp

/-- A Byzantine injection on the second gather's network state, read through
the projection. -/
theorem roundProjection_byzantineSecondGather (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (mm : Gather.Message P.n (Option Bool)) :
    roundProjection P u (w.recordGBCASend r k (.secondGather mm)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (secondGatherProjection P u w r)
            ((Gather.gatherProgramsAndNetwork
            (secondGatherProjection P u w r)).multicast k mm)) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherProgramsAndNetwork_firstGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.secondGather mm) rfl
    · funext k'
      simp only [inputBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGather mm) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
        InstanceState.multicast,
        ABA.NetworkState.recordSent, gatherProgramsAndNetwork_secondGatherProjection_network,
          recordGBCASend_sent_self]
      exact messagesOf_recordSent_some secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.secondGather mm) mm rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setGatherProgramsAndNetwork,
        inputBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGather mm) rfl
    · simp

/-- A Byzantine injection on an input-broadcast instance of the first gather,
read through the projection. -/
theorem roundProjection_byzantineFirstGatherInputBroadcast
    (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n) (r : ℕ) (k : Fin P.n)
    (i : Fin P.n) (mm : BRB.Message Bool) :
    roundProjection P u (w.recordGBCASend r k (.firstGatherInputBroadcasts i mm)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              ((Gather.inputBroadcasts (firstGatherProjection P u w r) i).multicast k mm))) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherProgramsAndNetwork_setInputBroadcasts,
        gatherProgramsAndNetwork_firstGatherProjection_network,
        recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.firstGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf i)
          (firstGatherInputBroadcastMessageOf_inj i) (w.sent r) k
          (.firstGatherInputBroadcasts i mm) mm (by simp [firstGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [inputBroadcasts_firstGatherProjection]
        exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
          (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k
          (.firstGatherInputBroadcasts i mm) (by simp [firstGatherInputBroadcastMessageOf,
            Ne.symm hk])
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherProgramsAndNetwork_secondGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.firstGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [inputBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherInputBroadcasts i mm)
          rfl
    · simp

/-- A Byzantine injection on an input-broadcast instance of the second gather,
read through the projection. -/
theorem roundProjection_byzantineSecondGatherInputBroadcast
    (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n) (r : ℕ) (k : Fin P.n)
    (i : Fin P.n) (mm : BRB.Message (Option Bool)) :
    roundProjection P u (w.recordGBCASend r k (.secondGatherInputBroadcasts i mm)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              ((Gather.inputBroadcasts (secondGatherProjection P u w r) i).multicast k mm))) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherProgramsAndNetwork_firstGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.secondGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [inputBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherInputBroadcasts i mm)
          rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherProgramsAndNetwork_setInputBroadcasts,
        gatherProgramsAndNetwork_secondGatherProjection_network,
        recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.secondGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf i)
          (secondGatherInputBroadcastMessageOf_inj i) (w.sent r) k
          (.secondGatherInputBroadcasts i mm) mm (by simp [secondGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [inputBroadcasts_secondGatherProjection]
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
          (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k
          (.secondGatherInputBroadcasts i mm) (by simp [secondGatherInputBroadcastMessageOf,
            Ne.symm hk])
    · simp

end Transitions

end AFW
end ABA
end PLTS
