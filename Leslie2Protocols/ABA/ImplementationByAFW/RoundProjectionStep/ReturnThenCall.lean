/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The return-then-call step and the graded return

`roundProjection_firstGatherReturn_secondGatherCall` and `roundProjection_secondGatherReturn_retG`:
the view of the composed round after each of the two rows that two events answer. The
return-then-call step is `firstGatherReturn` and then `secondGatherCall`; the graded return is
`secondGatherReturn` and then `retG`. Each is stated as one equation with the two effects composed,
and the state between them is named (`afterFirstGatherReturn`, `afterSecondGatherCall`,
`afterSecondGatherReturn`, `afterRetG`) so that a run can be built through it.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### The return-then-call step and the graded return

The return-then-call step is answered by two events, `firstGatherReturn` and `secondGatherCall`; the
graded return by `secondGatherReturn` and `retG`. Each pair is stated as one equation with the two
effects composed, and the state between them is named so that a run can be built through it. -/

/-- The view of one gather instance after a write. -/
theorem firstGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n)
    (m : Message P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.firstGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_write u w j c r sr m)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n)
    (m : Message P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.secondGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_write u w j c r sr m)

/-- The core the first gather's return carries: the one on record, and the core
of the gather's network state where none is on record. -/
noncomputable def firstGatherReturnCore (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) :
    Gather.AcceptedPairs P.n Bool :=
  (Gather.core (GBCA.ByAFW.firstGather s)).getD (Gather.coreOfNetwork P (Gather.gatherTier
    (GBCA.ByAFW.firstGather s)).2)

/-- The core the second gather's return carries. -/
noncomputable def secondGatherReturnCore (P : Parameters)
  (s : GBCA.ByAFW.RoundStateOverBracha P.n) :
    Gather.AcceptedPairs P.n (Option Bool) :=
  (Gather.core (GBCA.ByAFW.secondGather s)).getD (Gather.coreOfNetwork P (Gather.gatherTier
    (GBCA.ByAFW.secondGather s)).2)

/-- **The round after the first gather's return to `j` over `g`**: the program
records the candidate, the round's bound bit is written from the core the
return carries, and the first gather takes `Gather.StepOverBracha.ret`. -/
noncomputable def afterFirstGatherReturn (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (g : Fin P.n → Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather
    (GBCA.ByAFW.setBound
      (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
        { GBCA.ByAFW.programs s j with candidate := some (GBCA.candidate P g) }))
      (some ((GBCA.ByAFW.bound s).getD (GBCA.boundOfCore P (firstGatherReturnCore P s)))))
    (Gather.setCore
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with returned := true }))
      (some (firstGatherReturnCore P s)))

/-- **The round after `j`'s call of the second gather with `x`**: the program
marks the call and the second gather takes `Gather.StepOverBracha.call`. -/
noncomputable def afterSecondGatherCall (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (x : Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with secondGatherCalled := true }))
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with input := some x }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) j
        (((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) j).setProcess j
            { (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) j).process j with input := some x
              }).multicast
          j (.init x))))

/-- **The round after the second gather's return to `j` over `g`**: the program
records the grade and the second gather takes `Gather.StepOverBracha.ret`. -/
noncomputable def afterSecondGatherReturn (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with output := some (GBCA.gradeOf P g) }))
    (Gather.setCore
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with returned := true }))
      (some (secondGatherReturnCore P s)))

/-- **The round after its graded return to `j`**: the program announces the
grade and marks the record returned. -/
def afterRetG (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) (j : Fin P.n) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
    { GBCA.ByAFW.programs s j with output := none, returned := true })

/-- **The return-then-call step, read through the view.** The first gather returns to `j`, which
records the candidate and calls the second gather with it; the round's bound bit is written from the
core the return carries. -/
theorem roundProjection_firstGatherReturn_secondGatherCall (hu : (u j).2 = p) (r : ℕ) (g : Fin P.n →
  Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with returned := true }
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with input := some (GBCA.candidate P g) }
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts j
            (((p.roundRecord r).secondGatherInputBroadcasts j).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts j).process) with
                input := some (GBCA.candidate P g) }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init (GBCA.candidate P
        g)))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g)))))) r
      = afterSecondGatherCall P (afterFirstGatherReturn P (roundProjection P u w r) j g) j
        (GBCA.candidate P g) := by
  subst hu
  have hcore : Gather.coreOf P
      (firstGatherOf P (w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init (GBCA.candidate
        P g)))) r)
      = Gather.coreOfNetwork P (Gather.gatherTier (firstGatherProjection P u w r)).2 := by
    rw [coreOfNetwork_firstGatherProjection]
    refine Gather.coreOf_networkState_only _ _ (networkState_ext ?_ rfl)
    simp only [firstGatherOf, recordGBCASend_sent_self]
    exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
      (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
  rw [roundProjection_gbcaSendGhost, firstGatherProjection_write, secondGatherProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherCall, afterFirstGatherReturn, GBCA.ByAFW.programs_setSecondGather,
    GBCA.ByAFW.programs_setPrograms, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setBound, programs_roundProjection_eq, Function.update_idem,
    roundRecord_update_self rfl, locals_programProjection_if, Function.update_self]
    simp only [programs_mk, programProjection, LocalState.setProcess, Option.isSome_some]
  · simp only [afterSecondGatherCall, afterFirstGatherReturn, GBCA.ByAFW.bound_setSecondGather,
    GBCA.ByAFW.bound_setPrograms, GBCA.ByAFW.bound_setFirstGather, GBCA.ByAFW.bound_setBound,
      bound_roundProjection, firstGatherReturnCore, firstGather_roundProjection,
        core_firstGatherProjection]
    simp only [bound_mk, ghostStep, hcore]
  · simp only [afterSecondGatherCall, afterFirstGatherReturn,
    GBCA.ByAFW.firstGather_setSecondGather, GBCA.ByAFW.firstGather_setPrograms,
      GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    simp only [firstGather_mk]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, gatherTier_firstGather_roundProjectionUpdate,
      Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
            r).firstGatherInputBroadcasts
            ((u i).2.roundRecord r).firstGatherBindBroadcasts) j) ?_
        simp only [gatherLocalState, InstanceState.process,
          gatherTier_firstGatherProjection_process, localState_setProcess_process,
            localState_setProcess_received]
        simp only [LocalState.setProcess]
      · exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
          (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherTier, inputBroadcasts_firstGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
        (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · simp only [Gather.core_setCore, firstGatherReturnCore, firstGather_roundProjection,
      core_firstGatherProjection]
      simp only [ghostStep, hcore]
  · simp only [afterSecondGatherCall, afterFirstGatherReturn,
    GBCA.ByAFW.secondGather_setSecondGather, GBCA.ByAFW.secondGather_setPrograms,
      GBCA.ByAFW.secondGather_setBound, GBCA.ByAFW.secondGather_setFirstGather,
        secondGather_roundProjection]
    simp only [secondGather_mk]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, Gather.gatherTier_setInputBroadcasts,
      Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
            i).2.roundRecord r).secondGatherInputBroadcasts
            ((u i).2.roundRecord r).secondGatherBindBroadcasts) j) ?_
        simp only [gatherLocalState, broadcastReturnsFor_update_setProcess, InstanceState.process,
          gatherTier_secondGatherProjection_process, localState_setProcess_process,
            localState_setProcess_received]
        simp only [LocalState.setProcess]
      · exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r)
          j
          (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        refine Prod.ext ?_ (networkState_ext ?_ rfl)
        · simp only [InstanceState.multicast, InstanceState.setProcess]
          refine congrArg (Function.update
            (fun i => broadcastLocalState P (((u i).2.roundRecord r).secondGatherInputBroadcasts k))
              k) ?_
          simp only [InstanceState.process, broadcastLocalState, LocalState.setProcess,
            broadcastReturnsFor_mk_eq]
        · simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
          exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) k
            (.secondGatherInputBroadcasts k (.init (GBCA.candidate P g))) (.init (GBCA.candidate P
              g)) (by simp [secondGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) (by simp
            [secondGatherInputBroadcastMessageOf, Ne.symm hk])
    · funext q
      simp only [Gather.bindBroadcasts_setCore, Gather.bindBroadcasts_setInputBroadcasts,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_secondGather_roundProjectionUpdate,
          bindBroadcasts_secondGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
        (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · simp only [Gather.core_setCore, Gather.core_setInputBroadcasts, Gather.core_setGatherTier,
      core_secondGatherProjection]
      simp only [ghostStep]

/-- The view of the first gather instance after a write that records
nothing. -/
theorem firstGatherProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr)) w r =
    GBCA.ByAFW.firstGather (roundProjectionUpdate P u w r j sr (w.sent r)) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_writeNoSent u w j c r sr)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr)) w r =
    GBCA.ByAFW.secondGather (roundProjectionUpdate P u w r j sr (w.sent r)) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_writeNoSent u w j c r sr)

/-- **The graded return, read through the view.** The second gather returns to
`j`, which records the grade and announces it; the round's return clears the
record and marks it returned. -/
theorem roundProjection_secondGatherReturn_retG (hu : (u j).2 = p) (r : ℕ)
    (g : Fin P.n → Option (Option Bool)) (c' : RoundLoopRecord P.n) (bnd : Bool) :
    roundProjection P (Function.update u j (c', p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with returned := true } }))
      (w.writeGhost (ghostStep P) (Sum.inl (.retG r j (GBCA.gradeOf P g) bnd))) r
      = afterRetG P (afterSecondGatherReturn P (roundProjection P u w r) j g) j := by
  subst hu
  rw [roundProjection_writeGhost _ _ (rfl : roundOf (Sum.inl
      (Label.retG r j (GBCA.gradeOf P g) bnd)) = some r),
    firstGatherProjection_writeNoSent, secondGatherProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.programs_setPrograms,
    GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq, Function.update_idem,
      Function.update_self, roundRecord_update_self rfl,
    locals_programProjection_if]
    simp only [programs_mk, programProjection, LocalState.setProcess]
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.bound_setPrograms,
      GBCA.ByAFW.bound_setSecondGather, bound_roundProjection]
    simp only [bound_mk, ghostStep]
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.firstGather_setPrograms,
    GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    simp only [firstGather_mk,
      ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, gatherTier_firstGather_roundProjectionUpdate]
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
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.secondGather_setPrograms,
    GBCA.ByAFW.secondGather_setSecondGather,
      secondGather_roundProjection]
    simp only [secondGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, Gather.gatherTier_setGatherTier,
      gatherTier_secondGather_roundProjectionUpdate]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess]
      refine congrArg (Function.update
        (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
          i).2.roundRecord r).secondGatherInputBroadcasts
          ((u i).2.roundRecord r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, InstanceState.process,
        gatherTier_secondGatherProjection_process, localState_setProcess_process,
          localState_setProcess_received]
      simp only [LocalState.setProcess]
    · funext k
      simp only [Gather.inputBroadcasts_setCore, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, secondGatherReturnCore, secondGather_roundProjection,
        core_secondGatherProjection, coreOfNetwork_secondGatherProjection]

end Rows

end AFW
end ABA
end PLTS
