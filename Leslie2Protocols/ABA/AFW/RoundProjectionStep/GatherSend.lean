/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# A send of a gather instance

`roundProjection_firstGatherSend` and `roundProjection_secondGatherSend`: the projection onto the
composed round after a gather's `ECHO` or `VOTE`. The transition writes the sender's variables in
the gather and records on the gather's network state, and the composed round writes the same through
`Gather.setGatherProgramsAndNetwork`.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### A send of a gather instance

A gather's `ECHO` and `VOTE` write the sender's gather record and record on the
gather's network state. Each is the gather's `send` event, which
`Gather.AlgorithmOverBracha.echo` and `Gather.AlgorithmOverBracha.vote` write through
`Gather.setGatherProgramsAndNetwork`. -/

/-- A send of the first gather, read through the projection. -/
theorem roundProjection_firstGatherSend (hu : (u j).2 = p) (r : ℕ)
    (pr : Gather.ProcessVariables P.n Bool) (m : Gather.Message P.n Bool)
    (hin : pr.input = ((p.roundVariables r).firstGather.processVariables).input) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGather := (p.roundVariables r).firstGather.setProcessVariables pr }))
      (w.recordGBCASend r j (.firstGather m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
            (((Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).setProcessVariables
              j
                pr).multicast j m)) := by
  rw [← hu] at hin ⊢
  rw [roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
      roundProjectionUpdate, programProjection, LocalState.setProcessVariables, hin]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setGatherProgramsAndNetwork,
        GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        InstanceState.multicast, InstanceState.setProcessVariables, LocalState.setProcessVariables]
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setGatherProgramsAndNetwork,
        GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        InstanceState.multicast, ABA.NetworkState.recordSent]
      exact messagesOf_recordSent_some firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGather m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setGatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setGatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setGatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setGatherProgramsAndNetwork, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
        (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGather m) rfl
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

/-- A send of the second gather, read through the projection. -/
theorem roundProjection_secondGatherSend (hu : (u j).2 = p) (r : ℕ)
    (pr : Gather.ProcessVariables P.n (Option Bool)) (m : Gather.Message P.n (Option Bool))
    (hin : pr.input = ((p.roundVariables r).secondGather.processVariables).input)
    (hret : pr.returned = ((p.roundVariables r).secondGather.processVariables).returned) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGather := (p.roundVariables r).secondGather.setProcessVariables pr }))
      (w.recordGBCASend r j (.secondGather m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (secondGatherProjection P u w r)
            (((Gather.gatherProgramsAndNetwork (secondGatherProjection P u w r)).setProcessVariables
              j
                pr).multicast j m)) := by
  rw [← hu] at hin hret ⊢
  rw [roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
      roundProjectionUpdate, programProjection, LocalState.setProcessVariables, hin, hret]
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
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setGatherProgramsAndNetwork,
        GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        InstanceState.multicast, InstanceState.setProcessVariables, LocalState.setProcessVariables]
    · simp only [Gather.gatherProgramsAndNetwork, Gather.setGatherProgramsAndNetwork,
        GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        InstanceState.multicast, ABA.NetworkState.recordSent]
      exact messagesOf_recordSent_some secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGather m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setGatherProgramsAndNetwork,
        GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setGatherProgramsAndNetwork,
        GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setGatherProgramsAndNetwork, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setGatherProgramsAndNetwork, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
        (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.secondGather m) rfl

end Transitions

end AFW
end ABA
end PLTS
