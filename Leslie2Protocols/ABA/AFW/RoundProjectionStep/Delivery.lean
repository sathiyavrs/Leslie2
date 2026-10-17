/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# A delivery

`roundProjection_deliverFirstGather` and its three companions: the projection of the composed round
after a delivery at a program that has not terminated. The transition files the message in the
receiver's own local state of the network state the message's tag names. A gather message moves the
gather instance alone, and a broadcast message moves the broadcast instance alone.
`afterFirstGatherInputBroadcastDeliver` and its companion at the second gather name the state a
broadcast delivery reaches. `roundProjection_deliverLoop` is the delivery at a terminated program,
whose variables stand where they are (D22): every round projects as it did.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### A delivery

A delivery of the implementation at a program that has not terminated files the message in the
receiver's own local state of the network state the message's tag names. A gather message moves the
gather instance alone. A broadcast message moves the broadcast instance alone: the instance's return
to the receiver is a transition of its own, `AFW/RoundProjectionStep/BroadcastReturn.lean`. -/

/-- A delivery on the first gather's network, read through the projection. -/
theorem roundProjection_deliverFirstGather (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.Message P.n Bool) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGather mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGather mm)))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
            ((Gather.gatherProgramsAndNetwork
            (firstGatherProjection P u w r)).receiveMessage j k mm)) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGather mm))) (fun _ _ => rfl)]
  simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
    RoundVariables.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
    programs_roundProjectionUpdate, programProjection, LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      InstanceState.receiveMessage, gatherProgramsAndNetwork_firstGatherProjection_network]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => ((u i).2.roundVariables r).firstGather) j) ?_
      simp only [gatherProgramsAndNetwork_firstGatherProjection_processVariables,
        LocalState.deliverTo]
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherProgramsAndNetwork, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery on the second gather's network, read through the projection. -/
theorem roundProjection_deliverSecondGather (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.Message P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGather mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGather mm)))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (secondGatherProjection P u w r)
            ((Gather.gatherProgramsAndNetwork
            (secondGatherProjection P u w r)).receiveMessage j k mm)) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGather mm))) (fun _ _ => rfl)]
  simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
    RoundVariables.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
    programs_roundProjectionUpdate, programProjection, LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      InstanceState.receiveMessage,
        gatherProgramsAndNetwork_secondGatherProjection_network]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => ((u i).2.roundVariables r).secondGather) j) ?_
      simp only [gatherProgramsAndNetwork_secondGatherProjection_processVariables,
        LocalState.deliverTo]
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherProgramsAndNetwork, inputBroadcasts_secondGatherProjection]
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

/-- A delivery in an input-broadcast instance of the first gather that leaves the returned value
where it stands, read through the projection. -/
theorem roundProjection_deliverFirstGatherInputBroadcast (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n)
    (mm : BRB.Message Bool) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherInputBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm)))) r
    = afterFirstGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
    RoundVariables.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.programs_setFirstGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherInputBroadcastDeliver]
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.firstGather_setFirstGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setInputBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherProgramsAndNetwork_firstGatherProjection_fst]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => (((u i').2.roundVariables r).firstGatherInputBroadcasts i))
            j) ?_
        rfl
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.secondGather_setFirstGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
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

/-- A delivery in an input-broadcast instance of the second gather that leaves the returned value
where it stands, read through the projection. -/
theorem roundProjection_deliverSecondGatherInputBroadcast (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n)
    (mm : BRB.Message (Option Bool)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherInputBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm))))
    r = afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))
    (fun _ _ => rfl)]
  simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
    RoundVariables.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.programs_setSecondGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherInputBroadcastDeliver]
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.firstGather_setSecondGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.secondGather_setSecondGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_secondGather_roundProjectionUpdate,
      Gather.gatherProgramsAndNetwork_setInputBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherProgramsAndNetwork_secondGatherProjection_fst]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => (((u i').2.roundVariables r).secondGatherInputBroadcasts i))
            j) ?_
        rfl
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-! ### A delivery at a terminated program

A terminated program takes a round delivery on `RoundStep.deliverLoop`, and its variables stand
where they are (D22). The ghost write at a delivery is the identity, so every round projects as it
did, and the composed round matches the delivery by the empty silent run. -/

/-- A delivery at a terminated program, read through the projection: the program's round
variables stand where they are (D22), and every round projects as it did. -/
theorem roundProjection_deliverLoop (hu : (u j).2 = p) (r r' : ℕ) (k : Fin P.n) (m : Message P.n)
    (c' : RoundLoopVariables P.n) :
    roundProjection P (Function.update u j (c', p))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r'
      = roundProjection P u w r' := by
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k m)) (fun _ _ => rfl)]
  refine roundProjection_congr (fun i => ?_)
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, ← hu]
  · rw [Function.update_of_ne hi]

end Transitions

end AFW
end ABA
end PLTS
