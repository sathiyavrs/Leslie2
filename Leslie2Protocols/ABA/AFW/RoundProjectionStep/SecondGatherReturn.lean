/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.FirstGatherReturn

/-!
# The second gather's return

`roundProjection_secondGatherReturn`: the projection of the composed round after the second gather
returns to the acting process. The transition records the graded outcome the returned entries
determine and marks the gather record returned, and its ghost write is the second gather's core,
which is what the composed round's `secondGatherReturn` event writes. `afterSecondGatherReturn`
names the state the return reaches, and `secondGatherReturnCore` is the core the return carries.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### The second gather's return

The transition records the graded outcome and marks the gather record returned. It sends nothing,
and its ghost write is the second gather's core. -/

/-- The core the second gather's return carries. -/
noncomputable def secondGatherReturnCore (P : Parameters)
  (s : GBCA.ByAFW.RoundStateOverBracha P.n) :
    Gather.AcceptedPairs P.n (Option Bool) :=
  (Gather.core (GBCA.ByAFW.secondGather s)).getD (Gather.coreOfNetwork P
    (Gather.gatherProgramsAndNetwork
    (GBCA.ByAFW.secondGather s)).2)

/-- **The round after the second gather's return to `j` over `g`**: the program
records the grade and the second gather takes `Gather.AlgorithmOverBracha.ret`. -/
noncomputable def afterSecondGatherReturn (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with output := some (GBCA.gradeOf P g) }))
    (Gather.setCore
      (Gather.setGatherProgramsAndNetwork (GBCA.ByAFW.secondGather s)
        ((Gather.gatherProgramsAndNetwork (GBCA.ByAFW.secondGather s)).setProcessVariables j
          { (Gather.gatherProgramsAndNetwork (GBCA.ByAFW.secondGather s)).processVariables j with
            returned := true
            }))
      (some (secondGatherReturnCore P s)))

/-- **The second gather's return, read through the projection.** The second gather returns to `j`,
which records the grade; the round's second core is written from the core the return carries. -/
theorem roundProjection_secondGatherReturn (hu : (u j).2 = p) (r : ℕ)
    (g : Fin P.n → Option (Option Bool))
    (hr2 : ((p.roundVariables r).secondGather.processVariables).returned = false) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r
        { p.roundVariables r with
          output := some (GBCA.gradeOf P g)
          secondGather := (p.roundVariables r).secondGather.setProcessVariables
            { ((p.roundVariables r).secondGather.processVariables) with returned := true } }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherReturn (GBCA.gradeOf P g))))) r
      = afterSecondGatherReturn P (roundProjection P u w r) j g := by
  subst hu
  rw [roundProjection_writeGhost _ _
      (rfl : roundOf (Sum.inr (NetworkEvent.gbcaRoundEvent r j
        (RoundEvent.secondGatherReturn (GBCA.gradeOf P g)))) = some r),
    firstGatherProjection_writeNoSent, secondGatherProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherReturn, GBCA.ByAFW.programs_setSecondGather,
      GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq,
      roundVariables_update_self rfl, locals_programProjection_if]
    simp [programs_mk, programProjection, LocalState.setProcessVariables, hr2]
  · simp only [afterSecondGatherReturn, GBCA.ByAFW.bound_setSecondGather,
      GBCA.ByAFW.bound_setPrograms, bound_roundProjection]
    simp only [bound_mk, ghostStep]
  · simp only [afterSecondGatherReturn, GBCA.ByAFW.firstGather_setSecondGather,
      GBCA.ByAFW.firstGather_setPrograms, firstGather_roundProjection]
    simp only [firstGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherProgramsAndNetwork_setCore,
        gatherProgramsAndNetwork_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, core_firstGatherProjection]
  · simp only [afterSecondGatherReturn, GBCA.ByAFW.secondGather_setSecondGather,
      secondGather_roundProjection]
    simp only [secondGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherProgramsAndNetwork_setCore,
        Gather.gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
        gatherProgramsAndNetwork_secondGather_roundProjectionUpdate]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcessVariables]
      refine congrArg (Function.update
        (fun i => ((u i).2.roundVariables r).secondGather) j) ?_
      rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, Gather.inputBroadcasts_setGatherProgramsAndNetwork,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, Gather.bindBroadcasts_setGatherProgramsAndNetwork,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, secondGatherReturnCore, secondGather_roundProjection,
        core_secondGatherProjection, coreOfNetwork_secondGatherProjection]

end Transitions

end AFW
end ABA
end PLTS
