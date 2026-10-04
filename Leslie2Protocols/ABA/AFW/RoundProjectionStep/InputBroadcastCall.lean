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
input.
The transition records the payload as that instance's input at the caller and sends nothing, which
is what the gather's own `inputBroadcastCall` event writes.
The gather's variables, the round's program and the ghost stand.
The leader's `⟨INIT, x⟩` that follows is a send of the instance, read in
`RoundProjectionStep/GatherAndBroadcastTransitions.lean`. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The calls of the input-broadcast instances

Each transition writes the caller's variables in the instance broadcasting its input. The network,
the gather's variables, the round's program and the ghost stand. -/

/-- **The call of the first gather's input-broadcast instance, read through the projection.** The
instance records the payload the gather's variables hold as the leader's input. -/
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
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastCall b)))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) j
              ((Gather.inputBroadcasts (firstGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) j).processVariables j
                    with
                    input := some b }))) := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastCall b))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setInputBroadcasts]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_firstGatherProjection]
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
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
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastCall x)))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) j
              ((Gather.inputBroadcasts (secondGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) j).processVariables j
                    with
                    input := some x }))) := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastCall x))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
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
    · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setInputBroadcasts]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_secondGatherProjection]
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

end Transitions

end AFW
end ABA
end PLTS
