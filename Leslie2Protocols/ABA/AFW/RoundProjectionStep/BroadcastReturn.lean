/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The return of a broadcast instance

`roundProjection_firstGatherInputBroadcastReturn` and its three companions: the projection of the
implementation's state onto the composed round after a broadcast instance of either gather returns
to the acting process. The transition writes that instance's return flag at the process and files
the returned value in the process's gather record, which is what
`Gather.AlgorithmOverBracha.inputBroadcastRet` and `Gather.AlgorithmOverBracha.bindRet` write. The
transition sends nothing, and `AFW.ghostStep` leaves the round's ghost record where it stands.
`afterFirstGatherInputBroadcastReturn` and its three companions name the state the return reaches.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### The return of a broadcast instance

A broadcast instance's return to the acting process writes that instance's return flag at the
process and files the returned value in the process's gather record. -/

/-- **The round after an input-broadcast instance of the first gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterFirstGatherInputBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with
            inputBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process
                j).inputBroadcastReturned i (some v) }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).setProcess j
          { (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).process j with returned := true
            })))

/-- An input-broadcast instance of the first gather returning, read through the projection. -/
theorem roundProjection_firstGatherInputBroadcastReturn (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (v : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with
              inputBroadcastReturned := Function.update
                ((p.roundRecord r).firstGather.process).inputBroadcastReturned i (some v) }
          firstGatherInputBroadcasts := Function.update
            (p.roundRecord r).firstGatherInputBroadcasts i
            ((((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with
                returned := true })) }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastReturn i v)))) r
      = afterFirstGatherInputBroadcastReturn P (roundProjection P u w r) i j v := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastReturn i v))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherInputBroadcastReturn, GBCA.ByAFW.programs_setFirstGather,
      programs_roundProjection_eq, programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherInputBroadcastReturn]
  · simp only [afterFirstGatherInputBroadcastReturn, GBCA.ByAFW.firstGather_setFirstGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate,
        Gather.gatherTier_setInputBroadcasts, Gather.gatherTier_setGatherTier]
      exact Prod.ext rfl rfl
    · funext k
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_firstGatherProjection]
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherInputBroadcastReturn, GBCA.ByAFW.secondGather_setFirstGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
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

/-- **The round after a bind-broadcast instance of the first gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterFirstGatherBindBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Gather.AcceptedPairs P.n Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setBindBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with
            bindBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process
                j).bindBroadcastReturned i (some v) }))
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).setProcess j
          { (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).process j with
            returned := true })))

/-- A bind-broadcast instance of the first gather returning, read through the projection. -/
theorem roundProjection_firstGatherBindBroadcastReturn (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (v : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with
              bindBroadcastReturned := Function.update
                ((p.roundRecord r).firstGather.process).bindBroadcastReturned i (some v) }
          firstGatherBindBroadcasts := Function.update
            (p.roundRecord r).firstGatherBindBroadcasts i
            ((((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with
                returned := true })) }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherBindBroadcastReturn i v)))) r
      = afterFirstGatherBindBroadcastReturn P (roundProjection P u w r) i j v := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.firstGatherBindBroadcastReturn i v))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherBindBroadcastReturn, GBCA.ByAFW.programs_setFirstGather,
      programs_roundProjection_eq, programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherBindBroadcastReturn]
  · simp only [afterFirstGatherBindBroadcastReturn, GBCA.ByAFW.firstGather_setFirstGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate,
        Gather.gatherTier_setBindBroadcasts, Gather.gatherTier_setGatherTier]
      exact Prod.ext rfl rfl
    · funext k
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_firstGatherProjection]
      by_cases hq : q = i
      · subst hq
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherBindBroadcastReturn, GBCA.ByAFW.secondGather_setFirstGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
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

/-- **The round after an input-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterSecondGatherInputBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Option Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with
            inputBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process
                j).inputBroadcastReturned i (some v) }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).setProcess j
          { (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).process j with
            returned := true })))

/-- An input-broadcast instance of the second gather returning, read through the projection. -/
theorem roundProjection_secondGatherInputBroadcastReturn (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (v : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with
              inputBroadcastReturned := Function.update
                ((p.roundRecord r).secondGather.process).inputBroadcastReturned i (some v) }
          secondGatherInputBroadcasts := Function.update
            (p.roundRecord r).secondGatherInputBroadcasts i
            ((((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with
                returned := true })) }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastReturn i v)))) r
      = afterSecondGatherInputBroadcastReturn P (roundProjection P u w r) i j v := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastReturn i v))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherInputBroadcastReturn, GBCA.ByAFW.programs_setSecondGather,
      programs_roundProjection_eq, programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherInputBroadcastReturn]
  · simp only [afterSecondGatherInputBroadcastReturn, GBCA.ByAFW.firstGather_setSecondGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
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
  · simp only [afterSecondGatherInputBroadcastReturn, GBCA.ByAFW.secondGather_setSecondGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
        Gather.gatherTier_setInputBroadcasts, Gather.gatherTier_setGatherTier]
      exact Prod.ext rfl rfl
    · funext k
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGatherProjection]
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a bind-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterSecondGatherBindBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n)
    (v : Gather.AcceptedPairs P.n (Option Bool)) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setBindBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with
            bindBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process
                j).bindBroadcastReturned i (some v) }))
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).setProcess j
          { (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).process j with
            returned := true })))

/-- A bind-broadcast instance of the second gather returning, read through the projection. -/
theorem roundProjection_secondGatherBindBroadcastReturn (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (v : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with
              bindBroadcastReturned := Function.update
                ((p.roundRecord r).secondGather.process).bindBroadcastReturned i (some v) }
          secondGatherBindBroadcasts := Function.update
            (p.roundRecord r).secondGatherBindBroadcasts i
            ((((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with
                returned := true })) }))
      (w.writeGhost (ghostStep P)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherBindBroadcastReturn i v)))) r
      = afterSecondGatherBindBroadcastReturn P (roundProjection P u w r) i j v := by
  subst hu
  rw [roundProjection_ghostId
      (Sum.inr (.gbcaRoundEvent r j (.secondGatherBindBroadcastReturn i v))) (fun _ _ => rfl),
    roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherBindBroadcastReturn, GBCA.ByAFW.programs_setSecondGather,
      programs_roundProjection_eq, programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherBindBroadcastReturn]
  · simp only [afterSecondGatherBindBroadcastReturn, GBCA.ByAFW.firstGather_setSecondGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
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
  · simp only [afterSecondGatherBindBroadcastReturn, GBCA.ByAFW.secondGather_setSecondGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
        Gather.gatherTier_setBindBroadcasts, Gather.gatherTier_setGatherTier]
      exact Prod.ext rfl rfl
    · funext k
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_secondGatherProjection]
      by_cases hq : q = i
      · subst hq
        rw [Function.update_self, Function.update_self]
        exact Prod.ext rfl rfl
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

end Transitions

end AFW
end ABA
end PLTS
