/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.BroadcastSend
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GatherSend
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# The transitions of the two gathers and of the broadcast instances

`roundProjection_firstGatherEcho` and its seventeen companions: the projection of the composed
round after each `ECHO`, `VOTE` and `BIND` transition of the two gathers, and after each leader's
`INIT` and each `ECHO` and `VOTE` of their four broadcast families.
A send is the send of `RoundProjectionStep/GatherSend.lean` or
`RoundProjectionStep/BroadcastSend.lean` read at the label the implementation's transition carries,
over the effect the composed round's own transition writes.
A `BIND` sends nothing: it writes the payload to the caller's gather variables and records it as
the input of the caller's own bind-broadcast instance, which is what the gather's own `bindCall`
event writes.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The transitions of the two gathers and of the broadcast instances

Each lemma below reads one transition of the implementation through the projection, over the effect
the composed round's own transition writes. -/

/-- The first gather's `ECHO`, read through the projection. -/
theorem roundProjection_firstGatherEcho (hu : (u j).2 = p) (r : ℕ)
    (A : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGather := (p.roundVariables r).firstGather.setProcessVariables
            { ((p.roundVariables r).firstGather.processVariables) with sentEcho := some A } }))
      ((w.recordGBCASend r j (.firstGather (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGather (.echo A))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
            (((Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).setProcessVariables
              j
                { (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).processVariables
                  j with
                  sentEcho :=
                    some A }).multicast
              j (.echo A))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGather (.echo A)))) (fun _ _ => rfl)]
  exact roundProjection_firstGatherSend rfl r _ (.echo A) rfl

/-- The first gather's `VOTE`, read through the projection. -/
theorem roundProjection_firstGatherVote (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGather := (p.roundVariables r).firstGather.setProcessVariables
            { ((p.roundVariables r).firstGather.processVariables) with sentVote := some U } }))
      ((w.recordGBCASend r j (.firstGather (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGather (.vote U))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
            (((Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).setProcessVariables
              j
                { (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).processVariables
                  j with
                  sentVote :=
                    some U }).multicast
              j (.vote U))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGather (.vote U)))) (fun _ _ => rfl)]
  exact roundProjection_firstGatherSend rfl r _ (.vote U) rfl

/-- The second gather's `ECHO`, read through the projection. -/
theorem roundProjection_secondGatherEcho (hu : (u j).2 = p) (r : ℕ)
    (A : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGather := (p.roundVariables r).secondGather.setProcessVariables
            { ((p.roundVariables r).secondGather.processVariables) with sentEcho := some A } }))
      ((w.recordGBCASend r j (.secondGather (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGather (.echo A))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (secondGatherProjection P u w r)
            (((Gather.gatherProgramsAndNetwork (secondGatherProjection P u w r)).setProcessVariables
              j
                { (Gather.gatherProgramsAndNetwork (secondGatherProjection P u w
                  r)).processVariables j with
                  sentEcho :=
                    some A }).multicast
              j (.echo A))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGather (.echo A)))) (fun _ _ => rfl)]
  exact roundProjection_secondGatherSend rfl r _ (.echo A) rfl rfl

/-- The second gather's `VOTE`, read through the projection. -/
theorem roundProjection_secondGatherVote (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGather := (p.roundVariables r).secondGather.setProcessVariables
            { ((p.roundVariables r).secondGather.processVariables) with sentVote := some U } }))
      ((w.recordGBCASend r j (.secondGather (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGather (.vote U))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherProgramsAndNetwork (secondGatherProjection P u w r)
            (((Gather.gatherProgramsAndNetwork (secondGatherProjection P u w r)).setProcessVariables
              j
                { (Gather.gatherProgramsAndNetwork (secondGatherProjection P u w
                  r)).processVariables j with
                  sentVote :=
                    some U }).multicast
              j (.vote U))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGather (.vote U)))) (fun _ _ => rfl)]
  exact roundProjection_secondGatherSend rfl r _ (.vote U) rfl rfl

/-- The first gather's `BIND`, read through the projection: the payload is written to the caller's
gather variables and recorded as the input of the caller's own bind-broadcast instance. -/
theorem roundProjection_firstGatherBind (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGather := (p.roundVariables r).firstGather.setProcessVariables
            { ((p.roundVariables r).firstGather.processVariables) with sentBind := some U }
          firstGatherBindBroadcasts := Function.update (p.roundVariables
            r).firstGatherBindBroadcasts j
            (((p.roundVariables r).firstGatherBindBroadcasts j).setProcessVariables
              { (((p.roundVariables r).firstGatherBindBroadcasts j).processVariables) with
                input := some U })
                }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherBindBroadcastCall U)))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts
            (Gather.setGatherProgramsAndNetwork (firstGatherProjection P u w r)
              ((Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).setProcessVariables
                j
                { (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).processVariables
                  j with
                  sentBind :=
                    some U }))
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) j
              ((Gather.bindBroadcasts (firstGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) j).processVariables j
                    with
                    input := some U }))) := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.firstGatherBindBroadcastCall U))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setBindBroadcasts,
          Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
      exact Prod.ext rfl rfl
    · funext k
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts,
          Gather.inputBroadcasts_setGatherProgramsAndNetwork,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_firstGatherProjection]
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
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

/-- The second gather's `BIND`, read through the projection. -/
theorem roundProjection_secondGatherBind (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGather := (p.roundVariables r).secondGather.setProcessVariables
            { ((p.roundVariables r).secondGather.processVariables) with sentBind := some U }
          secondGatherBindBroadcasts := Function.update (p.roundVariables
            r).secondGatherBindBroadcasts j
            (((p.roundVariables r).secondGatherBindBroadcasts j).setProcessVariables
              { (((p.roundVariables r).secondGatherBindBroadcasts j).processVariables) with
                input := some U })
                }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherBindBroadcastCall U)))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts
            (Gather.setGatherProgramsAndNetwork (secondGatherProjection P u w r)
              ((Gather.gatherProgramsAndNetwork (secondGatherProjection P u w
                r)).setProcessVariables j
                { (Gather.gatherProgramsAndNetwork (secondGatherProjection P u w
                  r)).processVariables j with
                  sentBind :=
                    some U }))
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) j
              ((Gather.bindBroadcasts (secondGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) j).processVariables j
                    with
                    input := some U }))) := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.secondGatherBindBroadcastCall U))) (fun _ _ => rfl),
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
        Gather.gatherProgramsAndNetwork_setBindBroadcasts,
          Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
      exact Prod.ext rfl rfl
    · funext k
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts,
          Gather.inputBroadcasts_setGatherProgramsAndNetwork,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_secondGatherProjection]
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- `ECHO` in an input-broadcast instance of the first gather, read through the
projection. -/
theorem roundProjection_firstGatherInputBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherInputBroadcasts := Function.update (p.roundVariables
            r).firstGatherInputBroadcasts
            i
            (((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables
              { (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables) with
                  sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) i).processVariables j
                    with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the first gather, read through the
projection. The quorum transition and the amplification transition write the same field. -/
theorem roundProjection_firstGatherInputBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherInputBroadcasts := Function.update (p.roundVariables
            r).firstGatherInputBroadcasts
            i
            (((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables
              { (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables) with
                  sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) i).processVariables j
                    with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the first gather, read through the
projection. -/
theorem roundProjection_firstGatherBindBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherBindBroadcasts := Function.update (p.roundVariables
            r).firstGatherBindBroadcasts i
            (((p.roundVariables r).firstGatherBindBroadcasts i).setProcessVariables
              { (((p.roundVariables r).firstGatherBindBroadcasts i).processVariables) with
                  sentEcho := some m })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) i).processVariables j
                    with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the first gather, read through the
projection. The quorum transition and the amplification transition write the same field. -/
theorem roundProjection_firstGatherBindBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherBindBroadcasts := Function.update (p.roundVariables
            r).firstGatherBindBroadcasts i
            (((p.roundVariables r).firstGatherBindBroadcasts i).setProcessVariables
              { (((p.roundVariables r).firstGatherBindBroadcasts i).processVariables) with
                  sentVote := some m })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) i).processVariables j
                    with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in an input-broadcast instance of the second gather, read through
the projection. -/
theorem roundProjection_secondGatherInputBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherInputBroadcasts := Function.update (p.roundVariables
            r).secondGatherInputBroadcasts i
            (((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables
              { (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables) with
                sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) i).processVariables j
                    with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the second gather, read through
the projection. The quorum transition and the amplification transition write the same field. -/
theorem roundProjection_secondGatherInputBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherInputBroadcasts := Function.update (p.roundVariables
            r).secondGatherInputBroadcasts i
            (((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables
              { (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables) with
                sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) i).processVariables j
                    with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the second gather, read through the
projection. -/
theorem roundProjection_secondGatherBindBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherBindBroadcasts := Function.update (p.roundVariables
            r).secondGatherBindBroadcasts
            i
            (((p.roundVariables r).secondGatherBindBroadcasts i).setProcessVariables
              { (((p.roundVariables r).secondGatherBindBroadcasts i).processVariables) with
                  sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) i).processVariables j
                    with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the second gather, read through the
projection. The quorum transition and the amplification transition write the same field. -/
theorem roundProjection_secondGatherBindBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherBindBroadcasts := Function.update (p.roundVariables
            r).secondGatherBindBroadcasts
            i
            (((p.roundVariables r).secondGatherBindBroadcasts i).setProcessVariables
              { (((p.roundVariables r).secondGatherBindBroadcasts i).processVariables) with
                  sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcessVariables j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) i).processVariables j
                    with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r i _ (.vote m)

/-- The leader's `⟨INIT, b⟩` in the input-broadcast instance of the first gather, read through the
projection. -/
theorem roundProjection_firstGatherInputBroadcastInit (hu : (u j).2 = p) (r : ℕ)
    (b : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherInputBroadcasts := Function.update (p.roundVariables
            r).firstGatherInputBroadcasts j
            (((p.roundVariables r).firstGatherInputBroadcasts j).setProcessVariables
              { (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables) with
                  sentInit := some b })
                }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts j (.init b))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts j (.init b))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) j).processVariables j
                    with
                    sentInit := some b }).multicast
                j (.init b)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts j (.init b))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r j _ (.init b)

/-- The leader's `⟨INIT, U⟩` in the bind-broadcast instance of the first gather, read through the
projection. -/
theorem roundProjection_firstGatherBindBroadcastInit (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          firstGatherBindBroadcasts := Function.update (p.roundVariables
            r).firstGatherBindBroadcasts j
            (((p.roundVariables r).firstGatherBindBroadcasts j).setProcessVariables
              { (((p.roundVariables r).firstGatherBindBroadcasts j).processVariables) with
                  sentInit := some U })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) j).processVariables j
                    with
                    sentInit := some U }).multicast
                j (.init U)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r j _ (.init U)

/-- The leader's `⟨INIT, x⟩` in the input-broadcast instance of the second gather, read through the
projection. -/
theorem roundProjection_secondGatherInputBroadcastInit (hu : (u j).2 = p) (r : ℕ)
    (x : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherInputBroadcasts := Function.update (p.roundVariables
            r).secondGatherInputBroadcasts j
            (((p.roundVariables r).secondGatherInputBroadcasts j).setProcessVariables
              { (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables) with
                  sentInit := some x })
                }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init x))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) j
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) j).processVariables j
                    with
                    sentInit := some x }).multicast
                j (.init x)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r j _ (.init x)

/-- The leader's `⟨INIT, U⟩` in the bind-broadcast instance of the second gather, read through the
projection. -/
theorem roundProjection_secondGatherBindBroadcastInit (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          secondGatherBindBroadcasts := Function.update (p.roundVariables
            r).secondGatherBindBroadcasts j
            (((p.roundVariables r).secondGatherBindBroadcasts j).setProcessVariables
              { (((p.roundVariables r).secondGatherBindBroadcasts j).processVariables) with
                  sentInit := some U })
                }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) j
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) j).setProcessVariables j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) j).processVariables j
                    with
                    sentInit := some U }).multicast
                j (.init U)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r j _ (.init U)

end Transitions

end AFW
end ABA
end PLTS
