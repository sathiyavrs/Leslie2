/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# The first gather's return

`roundProjection_firstGatherReturn`: the projection of the composed round after the first gather
returns to the acting process. The transition records the candidate the returned entries determine
and marks the gather variables returned, and its ghost write records the first gather's core where
none is recorded. The composed round matches it by two events. On the first gather's return the
program records the candidate, and the gather records its core and marks the process returned
(`Gather.AlgorithmOverBracha.ret`). On the gather's announcement of that core, `firstGatherCore`,
the round's network records the core where none is recorded. The ghost write leaves the round's
bound bit, which the graded return writes and the round's network announces on `boundG` (D29).
`afterFirstGatherReturn` names the state the two events reach, and `firstGatherReturnCore` is the
core the first gather holds after the return. `firstGatherProjection_writeNoSent` and its companion
at the second gather read a write that records no message through the projection of one gather
instance.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The first gather's return

The transition records the candidate and marks the gather variables returned. It sends nothing, and
its ghost write records the first gather's core. -/

/-- The projection onto the first gather instance after a write that records nothing. -/
theorem firstGatherProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables
      P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundVariables r sr)) w r =
    GBCA.ByAFW.firstGather (roundProjectionUpdate P u w r j sr (w.sent r)) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_writeNoSent u w j c r sr)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables
      P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundVariables r sr)) w r =
    GBCA.ByAFW.secondGather (roundProjectionUpdate P u w r j sr (w.sent r)) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_writeNoSent u w j c r sr)

/-- The core the first gather holds after its return: the recorded one, and the core
of the gather's network state where none is recorded. -/
noncomputable def firstGatherReturnCore (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) :
    Gather.AcceptedPairs P.n Bool :=
  (Gather.core (GBCA.ByAFW.firstGather s)).getD (Gather.coreOfNetwork P
    (Gather.gatherProgramsAndNetwork
    (GBCA.ByAFW.firstGather s)).2)

/-- **The round after the first gather's return to `j` over `g` and the announcement of its
core**: the program records the candidate, the first gather takes `Gather.AlgorithmOverBracha.ret`,
and the round's network records the gather's core where none is recorded. -/
noncomputable def afterFirstGatherReturn (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    (j : Fin P.n) (g : Fin P.n → Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather
    (GBCA.ByAFW.setNetwork
      (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
        { GBCA.ByAFW.programs s j with candidate := some (GBCA.candidate P g) }))
      { GBCA.ByAFW.network s with
        firstGatherCore := some ((GBCA.ByAFW.network s).firstGatherCore.getD
          (firstGatherReturnCore P s)) })
    (Gather.setCore
      (Gather.setGatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)
        ((Gather.gatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)).setProcessVariables j
          { (Gather.gatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)).processVariables j with
            returned := true
            }))
      (some (firstGatherReturnCore P s)))

/-- **The first gather's return, read through the projection.** The first gather returns to `j`,
which records the candidate, and the round's network records the gather's core where none is
recorded. -/
theorem roundProjection_firstGatherReturn (hu : (u j).2 = p) (r : ℕ)
    (g : Fin P.n → Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          candidate := some (GBCA.candidate P g)
          firstGather := (p.roundVariables r).firstGather.setProcessVariables
            { ((p.roundVariables r).firstGather.processVariables) with returned := true } }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherReturn (GBCA.candidate P g))))) r
      = afterFirstGatherReturn P (roundProjection P u w r) j g := by
  subst hu
  have hcore : Gather.coreOf P (firstGatherOf P w r)
      = Gather.coreOfNetwork P (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).2
        :=
    (coreOfNetwork_firstGatherProjection u w r).symm
  rw [roundProjection_writeGhost _ _
      (rfl : roundOf (Sum.inr (NetworkEvent.gbcaRoundEvent r j
        (RoundEvent.firstGatherReturn (GBCA.candidate P g)))) = some r),
    firstGatherProjection_writeNoSent, secondGatherProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherReturn, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setNetwork, GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq,
      roundVariables_update_self rfl, locals_programProjection_if]
    simp only [programs_mk, programProjection, LocalState.setProcessVariables]
  · simp only [afterFirstGatherReturn, GBCA.ByAFW.network_setFirstGather,
      GBCA.ByAFW.network_setNetwork, network_roundProjection,
      firstGatherReturnCore, firstGather_roundProjection, core_firstGatherProjection, network_mk,
      networkProjection_ghostStep_firstGatherReturn, firstGatherCore_networkProjection, ← hcore]
    cases (w.ghost r).1 <;> rfl
  · simp only [afterFirstGatherReturn, GBCA.ByAFW.firstGather_setFirstGather,
      firstGather_roundProjection]
    simp only [firstGather_mk]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [Gather.gatherProgramsAndNetwork_setCore,
        gatherProgramsAndNetwork_firstGather_roundProjectionUpdate,
        Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcessVariables]
      refine congrArg (Function.update
        (fun i => ((u i).2.roundVariables r).firstGather) j) ?_
      rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherProgramsAndNetwork, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, firstGatherReturnCore, firstGather_roundProjection,
        core_firstGatherProjection]
      simp only [ghostStep, hcore]
  · simp only [afterFirstGatherReturn, GBCA.ByAFW.secondGather_setFirstGather,
      GBCA.ByAFW.secondGather_setNetwork, GBCA.ByAFW.secondGather_setPrograms,
      secondGather_roundProjection]
    simp only [secondGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_
    · simp only [Gather.gatherProgramsAndNetwork_setCore,
        gatherProgramsAndNetwork_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore,
        inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, core_secondGatherProjection]

end Transitions

end AFW
end ABA
end PLTS
