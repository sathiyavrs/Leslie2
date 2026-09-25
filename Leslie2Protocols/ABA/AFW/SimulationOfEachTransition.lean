/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.CompositeTransitions
import Leslie2Protocols.ABA.AFW.RoundProjectionStep
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# Each transition of the implementation matched by a run of the composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed P` reads the same
protocol as a composition of components, down to the broadcast instances. Every transition of the
implementation is matched here by a run of the composed system from the state the projection
`AFW.roundProjection` reads: the readers that identify a transition off its label, the builders of
a transition of one gather instance and of one round, the broadcast invariant across a transition,
corruption read through the projection, and the matching runs for a send, for a delivery, for the
call
and the graded return, and for a Byzantine injection.
`ABA/AFW/Simulation.lean` assembles these runs into the matching.

## The clause that is not a projection

`AFW.boundInvariant_of` and `AFW.writeGhost_bound` carry the bound invariant. Its two open cases
are the first gather's return, where the ghost write records the round's bound bit, and the
second gather's return, where the graded outcome is recorded at a round whose second gather has
been called. `AFW.roundVariables_candidate_gbcaRoundEvent` and
`AFW.roundVariables_output_gbcaRoundEvent` are the two case splits those rest on. -/


namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

/-! ### Reading a transition off a label the process owns

A program's transition on a label of `roundOwn j` is a transition of the
implementation: every other transition of the implementation either carries a
label of another class, or carries one of these at another process, or is the
replaced program's self-loop, which has no transition on a label the process
acts on. -/

theorem roundTransition_of_own {P : Parameters} {j : Fin P.n} {q : AFW.ProcessVariables P.n}
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    {y : AFW.ProcessVariables P.n} (hown : roundOwn j L)
    (h : ProgramStep P j q L (PMF.pure y)) : RoundStep P j q L (PMF.pure y) := by
  generalize hμ : (PMF.pure y : PMF (AFW.ProcessVariables P.n)) = ν at h
  cases h
  case roundTransition h' => exact hμ ▸ h'
  case corruptedIdle hh hτ hown' => exact absurd (actsAt_of_roundOwn hown) hown'
  all_goals first
    | exact hown.elim
    | (rename_i hid; exact absurd hown hid)

/-- A write of the variables of round `r` that leaves the candidate standing leaves every
round's candidate standing. -/
theorem roundVariables_setRoundVariables_candidate {P : Parameters} {p : RoundVariablesMap P.n} {r :
  ℕ}
    {sr : RoundVariables P.n} (h : sr.candidate = (p.roundVariables r).candidate) (r' : ℕ) :
    ((p.setRoundVariables r sr).roundVariables r').candidate = (p.roundVariables r').candidate := by
  by_cases hr' : r' = r
  · subst hr'; rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]; exact h
  · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']

/-- The same for the graded outcome. -/
theorem roundVariables_setRoundVariables_output {P : Parameters} {p : RoundVariablesMap P.n} {r : ℕ}
    {sr : RoundVariables P.n} (h : sr.output = (p.roundVariables r).output) (r' : ℕ) :
    ((p.setRoundVariables r sr).roundVariables r').output = (p.roundVariables r').output := by
  by_cases hr' : r' = r
  · subst hr'; rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]; exact h
  · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']

/-- The same for the second gather's input. -/
theorem roundVariables_setRoundVariables_secondGatherInput {P : Parameters} {p : RoundVariablesMap
  P.n}
    {r : ℕ} {sr : RoundVariables P.n}
    (h : (sr.secondGather.processVariables).input = ((p.roundVariables
      r).secondGather.processVariables).input)
    (r' : ℕ) :
    (((p.setRoundVariables r sr).roundVariables r').secondGather.processVariables).input
      = (((p.roundVariables r').secondGather.processVariables)).input := by
  by_cases hr' : r' = r
  · subst hr'; rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]; exact h
  · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']

/-- The same, read as the disjunction the round events carry: the second gather's input stands. -/
theorem roundVariables_setRoundVariables_secondGatherInput_or {P : Parameters} {p :
  RoundVariablesMap P.n}
    {r : ℕ} {sr : RoundVariables P.n}
    (h : (sr.secondGather.processVariables).input = ((p.roundVariables
      r).secondGather.processVariables).input)
    (r' : ℕ) :
    ((((p.setRoundVariables r sr).roundVariables r').secondGather.processVariables).input
        = (((p.roundVariables r').secondGather.processVariables)).input) ∨
      (((((p.setRoundVariables r sr).roundVariables r').secondGather.processVariables).input ≠ none)
        ∧
        ((p.roundVariables r').candidate ≠ none)) :=
  Or.inl (roundVariables_setRoundVariables_secondGatherInput h r')

/-- **The candidate is written at the first gather's return alone**: a round-internal call or
return either leaves the round's candidate where it stands, or is the first gather's return, whose
label carries the candidate it records. -/
theorem roundVariables_candidate_gbcaRoundEvent (P : Parameters) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} {r : ℕ} {e : RoundEvent P.n}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j e)) μ) :
    (∀ x : AFW.ProcessVariables P.n, μ = PMF.pure x →
        (x.2.roundVariables r).candidate = (p.roundVariables r).candidate)
      ∨ ((∀ x : AFW.ProcessVariables P.n, μ = PMF.pure x →
            (x.2.roundVariables r).candidate ≠ none) ∧ ∃ y, e = RoundEvent.firstGatherReturn y) :=
              by
  cases h
  case firstGatherReturn g _ _ _ _ _ _ =>
    exact Or.inr ⟨fun x hx => by
      obtain rfl := pure_inj hx.symm
      simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self], _, rfl⟩
  all_goals
    exact Or.inl (fun x hx => by
      obtain rfl := pure_inj hx.symm
      simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self])

/-- **The graded outcome is written at the second gather's return alone**: a round-internal call or
return either leaves the round's graded outcome where it stands, or is the second gather's return,
which fires at variables whose second gather has been called. -/
theorem roundVariables_output_gbcaRoundEvent (P : Parameters) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} {r : ℕ} {e : RoundEvent P.n}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j e)) μ) :
    (∀ x : AFW.ProcessVariables P.n, μ = PMF.pure x →
        (x.2.roundVariables r).output = (p.roundVariables r).output)
      ∨ ((p.roundVariables r).secondGather.processVariables).input ≠ none := by
  cases h
  case secondGatherReturn g hh hterm hin hbind hsubap hQ hr2 hout => exact Or.inr hin
  all_goals
    exact Or.inl (fun x hx => by
      obtain rfl := pure_inj hx.symm
      simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self])

/-! ### Building a transition of one gather instance

A transition of `Gather.AlgorithmOverBracha` is a transition of the instance at the interface
label over its own. The call is the exception: the instance takes `call id x`
on two transitions, and the two sit at the two labels of the interface. -/

section GatherTransitions

variable {P : Parameters} {X : Type} [DecidableEq X]

/-- A transition at a label other than a call is a transition of the instance
at the interface label over it. -/
theorem transition_instanceOverBracha_inl {s : Gather.StateOverBracha P.n X} {l₀ : Gather.Label P.n
  X}
    {μ : PMF (Gather.StateOverBracha P.n X)}
    (h0 : ∀ (id : Fin P.n) (x : X), l₀ ≠ Gather.Label.call id x)
    (h : Gather.AlgorithmOverBracha P s l₀ μ) :
    (Gather.instanceOverBracha P X).step s (Sum.inl l₀) μ := by
  obtain ⟨l, hl, hstep⟩ := Gather.algorithm_instanceOverBracha_step P s l₀ μ h
  cases l with
  | inl y => rwa [Option.some.inj hl] at hstep
  | inr e => cases e with
    | callLoop id x => exact absurd (Option.some.inj hl).symm (h0 id x)

/-- Build the instance's call: the gather variables record the payload and the
caller's own input instance broadcasts it. -/
theorem transition_instanceOverBracha_call (s : Gather.StateOverBracha P.n X) (id : Fin P.n) (x : X)
    (h : ((Gather.gatherProgramsAndNetwork s).processVariables id).input = none) :
    (Gather.instanceOverBracha P X).step s (Sum.inl (Gather.Label.call id x))
      (PMF.pure (Gather.setGatherProgramsAndNetwork s ((Gather.gatherProgramsAndNetwork
        s).setProcessVariables id
        { (Gather.gatherProgramsAndNetwork s).processVariables id with input := some x }))) := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  exact Gather.instanceOverBroadcasts_label_step (a' := a) (b' := b) (by simp)
    (dirac_steps_update (Gather.ProgramStep.call (v id) x h)
      (fun i hi => Gather.ProgramStep.callIdle (v i) id x (Ne.symm hi)))
    (Gather.NetworkStep.call y id x)
    (fun _ => System.mapIdle_unchanged rfl)
    (fun _ => System.mapIdle_unchanged rfl)

/-- Build the call of the instance broadcasting the caller's input: that instance records the
payload the gather variables hold and multicasts its `⟨INIT, x⟩`. -/
theorem transition_instanceOverBracha_inputBroadcastCall (s : Gather.StateOverBracha P.n X)
    (id : Fin P.n) (x : X) (hin : ((Gather.gatherProgramsAndNetwork s).processVariables id).input =
      some x)
    (hb : ((Gather.inputBroadcasts s id).processVariables id).input = none) :
    (Gather.instanceOverBracha P X).step s (Sum.inl Gather.Label.tau)
      (PMF.pure (Gather.setInputBroadcasts s
        (Function.update (Gather.inputBroadcasts s) id
          (((Gather.inputBroadcasts s id).setProcessVariables id
            { (Gather.inputBroadcasts s id).processVariables id with input := some x }).multicast id
              (.init
              x))))) := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  exact Gather.instanceOverBroadcasts_event_step (x := v) (w' := y) (b' := b)
    (Gather.GatherEvent.inputBroadcastCall id x)
    (fun i => by
      by_cases hi : i = id
      · subst hi; exact Gather.ProgramStep.inputBroadcastCall (v i) x hin
      · exact Gather.ProgramStep.inputBroadcastCallIdle (v i) id x (Ne.symm hi))
    (Gather.NetworkStep.inputBroadcastCallIdle y id x)
    (System.mapIdle_step_update (by simp) (fun k hk => by simp [hk])
      (Gather.transition_brachaInstance_call_step P id (a id) x hb))
    (fun _ => System.mapIdle_unchanged rfl)

/-- Build the instance's input-enabledness loop. -/
theorem transition_instanceOverBracha_callLoop (s : Gather.StateOverBracha P.n X) (id : Fin P.n) (x
  : X) :
    (Gather.instanceOverBracha P X).step s (Sum.inr (Gather.LoopLabel.callLoop id x))
      (PMF.pure s) := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  refine Gather.instanceOverBroadcasts_label_step (x := v) (w' := y) (a' := a) (b' := b) (by simp)
    (fun i => ?_) (Gather.NetworkStep.callLoop y id x) (fun k => ?_)
    (fun _ => System.mapIdle_unchanged rfl)
  · by_cases hi : i = id
    · subst hi; exact Gather.ProgramStep.callLoop (v i) x
    · exact Gather.ProgramStep.callLoopIdle (v i) id x (Ne.symm hi)
  · exact System.mapIdle_unchanged rfl

end GatherTransitions

/-! ### Building a transition of one round

One transition of the round's programs beside one transition of a gather instance, at the label
the round takes them on. The three hidden events `firstGatherReturn`, `secondGatherCall` and
`secondGatherReturn` are silent transitions of the round; the call, the call loop and the graded
return are transitions on labels of the family alphabet. -/

section RoundTransitions

variable {P : Parameters} {r : ℕ}

/-- A silent transition of the first gather is a silent transition of the round. -/
theorem roundOverBracha_firstGatherTau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {c : Gather.StateOverBracha P.n Bool}
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.firstGather s) Gather.Label.tau (PMF.pure c)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (GBCA.ByAFW.setFirstGather s c)) :=
  GBCA.ByAFW.roundOverGathers_tau_firstGather (transition_instanceOverBracha_inl (by simp) h)

/-- A silent transition of the second gather is a silent transition of the round. -/
theorem roundOverBracha_secondGatherTau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {d : Gather.StateOverBracha P.n (Option Bool)}
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.secondGather s) Gather.Label.tau (PMF.pure d)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (GBCA.ByAFW.setSecondGather s d)) :=
  GBCA.ByAFW.roundOverGathers_tau_secondGather (transition_instanceOverBracha_inl (by simp) h)

/-- **The round's call**: the program records the input and the first gather
takes its call. -/
theorem roundOverBracha_callG (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n) (b : Bool)
    (h0 : (GBCA.ByAFW.programs s id).input = none)
    (hg : ((Gather.gatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)).processVariables id).input =
      none) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl (Label.callG r id b))
      (PMF.pure (GBCA.ByAFW.setFirstGather
        (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) id
          { GBCA.ByAFW.programs s id with input := some b }))
        (Gather.setGatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)
          ((Gather.gatherProgramsAndNetwork
          (GBCA.ByAFW.firstGather s)).setProcessVariables id
          { (Gather.gatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)).processVariables id with
            input := some b })))) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .callG r id b) (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.callG (v id) b h0)
        (fun i hi => GBCA.ByAFW.ProgramStep.callGIdle (v i) id b (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.callG y id b))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_call c id b hg))
    (System.mapIdle_unchanged (by simp))

/-- **The round's call loop**: no program moves and the first gather takes its
input-enabledness loop. -/
theorem roundOverBracha_callLoop (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
  (b : Bool) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inr (.gbcaCallLoop r id b)) (PMF.pure s) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  refine GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .callLoop r id b) (by simp) (by simp) (fun i => ?_)
      (GBCA.ByAFW.NetworkStep.callLoop y id b))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_callLoop c id b))
    (System.mapIdle_unchanged (by simp))
  by_cases hi : i = id
  · subst hi; exact GBCA.ByAFW.ProgramStep.callLoop (v i) b
  · exact GBCA.ByAFW.ProgramStep.callLoopIdle (v i) id b (Ne.symm hi)

/-- **The Byzantine call loop**: no program moves and the first gather takes its
input-enabledness loop. -/
theorem roundOverBracha_byzantineCallLoop (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
  (b : Bool) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inr (.byzantineCallGLoop r id b)) (PMF.pure s) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  refine GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .callLoop r id b) (by simp) (by simp) (fun i => ?_)
      (GBCA.ByAFW.NetworkStep.callLoop y id b))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_callLoop c id b))
    (System.mapIdle_unchanged (by simp))
  by_cases hi : i = id
  · subst hi; exact GBCA.ByAFW.ProgramStep.callLoop (v i) b
  · exact GBCA.ByAFW.ProgramStep.callLoopIdle (v i) id b (Ne.symm hi)

/-- **The first gather's return**: the program records the candidate, the
round's bound bit is written from the core the return carries, and the first
gather takes its return. -/
theorem roundOverBracha_firstGatherReturn (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (g : Fin P.n → Option Bool) (hin : (GBCA.ByAFW.programs s id).input ≠ none)
    (hc : (GBCA.ByAFW.programs s id).candidate = none)
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.firstGather s)
      (.ret id g (firstGatherReturnCore P s))
      (PMF.pure (GBCA.ByAFW.firstGather (afterFirstGatherReturn P s id g))))
    :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (afterFirstGatherReturn P s id g)) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_event_step (GBCA.ByAFW.RoundEvent.firstGatherReturn id g
    (firstGatherReturnCore P ((v, y), c, d)))
    (GBCA.ByAFW.roundPrograms_label_step (lp := .firstGatherReturn id g (firstGatherReturnCore P
      ((v, y), c,
      d))) (by simp) (by simp) (dirac_steps_update
        (GBCA.ByAFW.ProgramStep.firstGatherReturn (v id) g _
        hin hc)
        (fun i hi => GBCA.ByAFW.ProgramStep.firstGatherReturnIdle (v i) id g _ (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.firstGatherReturn y id g _))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_inl (by simp) h))
    (System.mapIdle_unchanged (by simp))

/-- **The second gather's call**: the program marks the call and the second
gather takes its call. -/
theorem roundOverBracha_secondGatherCall (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (x : Option Bool) (hc : (GBCA.ByAFW.programs s id).candidate = some x)
    (h2 : (GBCA.ByAFW.programs s id).secondGatherCalled = false)
    (hg : ((Gather.gatherProgramsAndNetwork (GBCA.ByAFW.secondGather s)).processVariables id).input
      = none) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (afterSecondGatherCall P s id x)) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_event_step (GBCA.ByAFW.RoundEvent.secondGatherCall id x)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .secondGatherCall id x) (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.secondGatherCall (v id) x hc h2)
        (fun i hi => GBCA.ByAFW.ProgramStep.secondGatherCallIdle (v i) id x (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.secondGatherCall y id x))
    (System.mapIdle_unchanged (by simp))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_call d id x hg))

/-- **The second gather's return**: the program records the grade and the
second gather takes its return. -/
theorem roundOverBracha_secondGatherReturn (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) (h2 : (GBCA.ByAFW.programs s id).secondGatherCalled = true)
    (ho : (GBCA.ByAFW.programs s id).output = none)
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.secondGather s)
      (.ret id g (secondGatherReturnCore P s))
      (PMF.pure (GBCA.ByAFW.secondGather (afterSecondGatherReturn P s id g))))
    :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (afterSecondGatherReturn P s id g)) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_event_step (GBCA.ByAFW.RoundEvent.secondGatherReturn id g
    (secondGatherReturnCore P ((v, y), c, d)))
    (GBCA.ByAFW.roundPrograms_label_step (lp := .secondGatherReturn id g (secondGatherReturnCore P
      ((v, y), c,
      d))) (by simp) (by simp) (dirac_steps_update
        (GBCA.ByAFW.ProgramStep.secondGatherReturn (v id) g _
        h2 ho)
        (fun i hi => GBCA.ByAFW.ProgramStep.secondGatherReturnIdle (v i) id g _ (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.secondGatherReturn y id g _))
    (System.mapIdle_unchanged (by simp))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_inl (by simp) h))

/-- **The round's graded return**: the program announces the grade it holds and
marks its variables returned, and the bit the label carries is the recorded
one. -/
theorem roundOverBracha_retG (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (out : GBCAOutput) (ho : (GBCA.ByAFW.programs s id).output = some out)
    (hr : (GBCA.ByAFW.programs s id).returned = false) :
    (GBCA.ByAFW.roundOverBracha P r).step s
    (Sum.inl (Label.retG r id out ((GBCA.ByAFW.bound s).getD (GBCA.boundOfCore P ∅))))
    (PMF.pure (afterRetG P s id)) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .retG r id out (y.getD (GBCA.boundOfCore P ∅)))
      (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.retG (v id) out _ ho hr)
        (fun i hi => GBCA.ByAFW.ProgramStep.retGIdle (v i) id out _ (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.retG y id out))
    (System.mapIdle_unchanged (by simp)) (System.mapIdle_unchanged (by simp))

/-! ### A run of one round -/

/-- One silent transition of the round is a silent run. -/
theorem roundOverBracha_run_one {q q' : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent q q' :=
  System.weakLSilent_stepCons (by rw [extendedLabel_tau]; exact h) (by simp)
    (System.weakLSilent_refl _ q')

end RoundTransitions

/-! ### Corruption, read through the projection

Corruption reaches the round through its two gather instances: the corrupted
set the adversary holds is the corrupted set of every network state the projection
assembles, and the programs and the round's bound bit are untouched (D1). -/

theorem roundProjection_fail {P : Parameters} (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) :
    roundProjection P u (Implementation.NetworkState.corrupt P k w) r
      = corruptionOverBracha P (Sum.inl (Label.fail k)) (roundProjection P u w r) := by
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [GBCA.ByAFW.programs, roundProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll,
      Implementation.NetworkState.corrupt]
  · simp only [GBCA.ByAFW.bound, roundProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll,
    Implementation.NetworkState.corrupt]
    split_ifs <;> rfl
  · refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather, roundProjection,
        firstGatherProjection,
        corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll, InstanceState.corrupt,
          Implementation.NetworkState.corrupt, ABA.NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
        firstGatherProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
          InstanceState.corrupt, Implementation.NetworkState.corrupt, ABA.NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
        firstGatherProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
          InstanceState.corrupt, Implementation.NetworkState.corrupt, ABA.NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · simp only [Gather.core, GBCA.ByAFW.firstGather, roundProjection, firstGatherProjection,
      corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
        Implementation.NetworkState.corrupt]
    split_ifs <;> rfl
  · refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather, roundProjection,
        secondGatherProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
          InstanceState.corrupt, Implementation.NetworkState.corrupt, ABA.NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
        secondGatherProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
          InstanceState.corrupt, Implementation.NetworkState.corrupt, ABA.NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
        secondGatherProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
          InstanceState.corrupt, Implementation.NetworkState.corrupt, ABA.NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · simp only [Gather.core, GBCA.ByAFW.secondGather, roundProjection, secondGatherProjection,
      corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
        Implementation.NetworkState.corrupt]
    split_ifs <;> rfl

/-- **The whole family of rounds after a Byzantine injection**: the round the
message names moves, the rest remain unchanged. -/
theorem roundProjectionFamily_byzantine {P : Parameters} (u : ∀ _ : Fin P.n, AFW.ProcessVariables
  P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (m : Message P.n) :
    (fun r' => roundProjection P u (w.recordGBCASend r k m) r') = Function.update
    (fun r' => roundProjection P u w r') r (roundProjection P u (w.recordGBCASend r k m) r) := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self]
  · rw [Function.update_of_ne hr]
    simp only [roundProjection, firstGatherProjection, secondGatherProjection,
      recordGBCASend_sent_ne w r k m hr, recordGBCASend_F, recordGBCASend_ghost]

/-- A transition that leaves every round's variables where they stand leaves the
whole family of rounds where it stands. -/
theorem roundProjection_unchanged {P : Parameters} {x u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    (h : ∀ i, (x i).2 = (u i).2) (w : NetworkState P.n) :
    (fun r => roundProjection P u w r) = fun r => roundProjection P x w r := by
  funext r
  exact (roundProjection_congr (fun i => by rw [h i])).symm

/-! ### Matching a send

A send of the implementation is a silent run of the round: the sender writes its own variables, the
network records the message, and the round the label tags moves as its own transitions move it. -/

theorem roundVariables_match_gbcaSend (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {m : Message P.n}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaSend r j m)) μ) :
    ∃ x : AFW.ProcessVariables P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.roundVariables r' = p.roundVariables r') ∧
      (∀ r', (x.2.roundVariables r').candidate = (p.roundVariables r').candidate) ∧
      (∀ r', (x.2.roundVariables r').output = (p.roundVariables r').output) ∧
      (((x.2.roundVariables r).secondGather.processVariables).input
          = ((p.roundVariables r).secondGather.processVariables).input ∨
        (((x.2.roundVariables r).secondGather.processVariables).input ≠ none ∧
          (p.roundVariables r).candidate ≠ none)) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j x)
          ((w.recordGBCASend r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) r) := by
  subst hu
  cases h with
  | firstGatherEcho _ _ _ hh hterm hin hcard hsend =>
    have htransition :=
      Gather.AlgorithmOverBracha.echo (firstGatherProjection P u w r) j hin hcard hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherEcho rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherVote _ _ _ U hh hterm hin hech happ hQ hsend =>
    have htransition := Gather.AlgorithmOverBracha.vote (firstGatherProjection P u w r) j U hin hech
      happ hQ hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherBind _ _ _ U hh hterm hin hvot hsnd hbc happ hQ =>
    have htransition := Gather.AlgorithmOverBracha.bindCall (firstGatherProjection P u w r) j U hin
      hvot
      hsnd happ hQ hbc
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherBind rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherEcho _ _ _ hh hterm hin hcard hsend =>
    have htransition :=
      Gather.AlgorithmOverBracha.echo (secondGatherProjection P u w r) j hin hcard hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherEcho rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherVote _ _ _ U hh hterm hin hech happ hQ hsend =>
    have htransition := Gather.AlgorithmOverBracha.vote (secondGatherProjection P u w r) j U hin
      hech
      happ hQ hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherBind _ _ _ U hh hterm hin hvot hsnd hbc happ hQ =>
    have htransition := Gather.AlgorithmOverBracha.bindCall (secondGatherProjection P u w r) j U hin
      hvot
      hsnd happ hQ hbc
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherBind rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherInputBroadcastCall _ _ _ b hh hterm hin hbin =>
    have htransition :=
      Gather.AlgorithmOverBracha.inputBroadcastCall (firstGatherProjection P u w r) j b hin hbin
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]),
          ?_⟩
    rw [roundProjection_firstGatherInputBroadcastCall rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherInputBroadcastCall _ _ _ x hh hterm hin2 hbin2 =>
    have htransition :=
      Gather.AlgorithmOverBracha.inputBroadcastCall (secondGatherProjection P u w r) j x hin2 hbin2
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]),
          ?_⟩
    rw [roundProjection_secondGatherInputBroadcastCall rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherInputBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.echo (Gather.inputBroadcasts (firstGatherProjection P u w r) i) j mm
        hrecv hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherInputBroadcastEcho rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherInputBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.voteQuorum (Gather.inputBroadcasts (firstGatherProjection P u w r) i) j
        mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherInputBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherInputBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.voteAmplification (Gather.inputBroadcasts (firstGatherProjection P u w r)
        i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherInputBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherBindBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.echo (Gather.bindBroadcasts (firstGatherProjection P u w r) i) j mm hrecv
        hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherBindBroadcastEcho rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherBindBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.voteQuorum (Gather.bindBroadcasts (firstGatherProjection P u w r) i) j mm
        hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherBindBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherBindBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.voteAmplification (Gather.bindBroadcasts (firstGatherProjection P u w r)
        i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_firstGatherBindBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherInputBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w
      r) i _
      (BRB.BrachaAlgorithm.echo (Gather.inputBroadcasts (secondGatherProjection P u w r) i) j mm
        hrecv hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherInputBroadcastEcho rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherInputBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w
      r) i _
      (BRB.BrachaAlgorithm.voteQuorum (Gather.inputBroadcasts (secondGatherProjection P u w r) i) j
        mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherInputBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherInputBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w
      r) i _
      (BRB.BrachaAlgorithm.voteAmplification (Gather.inputBroadcasts (secondGatherProjection P u w
        r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherInputBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherBindBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (secondGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.echo (Gather.bindBroadcasts (secondGatherProjection P u w r) i) j mm
        hrecv hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherBindBroadcastEcho rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherBindBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (secondGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.voteQuorum (Gather.bindBroadcasts (secondGatherProjection P u w r) i) j
        mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherBindBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherBindBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (secondGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.voteAmplification (Gather.bindBroadcasts (secondGatherProjection P u w r)
        i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherBindBroadcastVote rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)


/-! ### Matching a delivery

A delivery of the implementation files the message in the receiver's own local
state of the network state the message's tag names. A gather message moves the
gather instance alone, and a broadcast message moves the broadcast instance
alone: the instance's return to the receiver is a transition of its own. -/

/-- A delivery of the implementation is one silent transition of the round. -/
theorem roundVariables_match_gbcaDeliver (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables
  P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {k : Fin P.n}
    {m : Message P.n} {μ : PMF (AFW.ProcessVariables P.n)} (hsent : m ∈ w.sent r k)
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m)) μ) :
    ∃ x : AFW.ProcessVariables P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.roundVariables r' = p.roundVariables r') ∧
      (∀ r',
        ((x.2.roundVariables r').secondGather.processVariables).input = ((p.roundVariables
          r').secondGather.processVariables).input) ∧
      (∀ r', (x.2.roundVariables r').candidate = (p.roundVariables r').candidate) ∧
      (∀ r', (x.2.roundVariables r').output = (p.roundVariables r').output) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) := by
  subst hu
  cases h with
  | gbcaDeliverReceive _ _ _ _ _ hh hterm =>
    have hga2 : ∀ r', ((((u j).2.deliverTo r k m).roundVariables
      r').secondGather.processVariables).input
        = (((u j).2.roundVariables r').secondGather.processVariables).input := by
      intro r'
      by_cases hr' : r' = r
      · subst hr'
        simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
          RoundVariables.deliverTo,
            Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]
        cases m <;> simp [LocalState.deliverTo]
      · rw [Implementation.RoundVariablesMap.deliverTo,
          Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    have hrun :
        (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
          (roundProjection P (Function.update u j (c, (u j).2.deliverTo r k m))
            (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) := by
      cases m with
      | firstGather mm =>
        have htransition := Gather.AlgorithmOverBracha.deliver (firstGatherProjection P u w r) j k
          mm
          ((mem_messagesOf (hf := firstGatherMessageOf_inj)).mpr ⟨_, hsent, rfl⟩)
        rw [roundProjection_deliverFirstGather rfl]
        exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
          htransition)
      | secondGather mm =>
        have htransition := Gather.AlgorithmOverBracha.deliver (secondGatherProjection P u w r) j k
          mm
          ((mem_messagesOf (hf := secondGatherMessageOf_inj)).mpr ⟨_, hsent, rfl⟩)
        rw [roundProjection_deliverSecondGather rfl]
        exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
          htransition)
      | firstGatherInputBroadcasts i mm =>
        have hdlv : BRB.BrachaAlgorithm P i
            (Gather.inputBroadcasts (firstGatherProjection P u w r) i) .tau
            (PMF.pure ((Gather.inputBroadcasts (firstGatherProjection P u w r) i).receiveMessage
              j k mm)) :=
          BRB.BrachaAlgorithm.deliver _ j k mm
            ((mem_messagesOf (hf := firstGatherInputBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
              by simp [firstGatherInputBroadcastMessageOf]⟩)
        rw [roundProjection_deliverFirstGatherInputBroadcast rfl r i k mm]
        exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
          (Gather.AlgorithmOverBracha.inputBroadcastTau (firstGatherProjection P u w r) i _ hdlv))
      | firstGatherBindBroadcasts i mm =>
        have hdlv : BRB.BrachaAlgorithm P i
            (Gather.bindBroadcasts (firstGatherProjection P u w r) i) .tau
            (PMF.pure ((Gather.bindBroadcasts (firstGatherProjection P u w r) i).receiveMessage
              j k mm)) :=
          BRB.BrachaAlgorithm.deliver _ j k mm
            ((mem_messagesOf (hf := firstGatherBindBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
              by simp [firstGatherBindBroadcastMessageOf]⟩)
        rw [roundProjection_deliverFirstGatherBindBroadcast rfl r i k mm]
        exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
          (Gather.AlgorithmOverBracha.bindBroadcastTau (firstGatherProjection P u w r) i _ hdlv))
      | secondGatherInputBroadcasts i mm =>
        have hdlv : BRB.BrachaAlgorithm P i
            (Gather.inputBroadcasts (secondGatherProjection P u w r) i) .tau
            (PMF.pure ((Gather.inputBroadcasts (secondGatherProjection P u w r) i).receiveMessage
              j k mm)) :=
          BRB.BrachaAlgorithm.deliver _ j k mm
            ((mem_messagesOf (hf := secondGatherInputBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
              by simp [secondGatherInputBroadcastMessageOf]⟩)
        rw [roundProjection_deliverSecondGatherInputBroadcast rfl r i k mm]
        exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
          (Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w r) i _ hdlv))
      | secondGatherBindBroadcasts i mm =>
        have hdlv : BRB.BrachaAlgorithm P i
            (Gather.bindBroadcasts (secondGatherProjection P u w r) i) .tau
            (PMF.pure ((Gather.bindBroadcasts (secondGatherProjection P u w r) i).receiveMessage
              j k mm)) :=
          BRB.BrachaAlgorithm.deliver _ j k mm
            ((mem_messagesOf (hf := secondGatherBindBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
              by simp [secondGatherBindBroadcastMessageOf]⟩)
        rw [roundProjection_deliverSecondGatherBindBroadcast rfl r i k mm]
        exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
          (Gather.AlgorithmOverBracha.bindBroadcastTau (secondGatherProjection P u w r) i _ hdlv))
    have hcand : ∀ r', ((((u j).2.deliverTo r k m).roundVariables r').candidate)
        = (((u j).2.roundVariables r').candidate) := by
      intro r'
      by_cases hr' : r' = r
      · subst hr'
        simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
          RoundVariables.deliverTo,
            Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]
        cases m <;> simp
      · rw [Implementation.RoundVariablesMap.deliverTo,
          Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    have hout : ∀ r', ((((u j).2.deliverTo r k m).roundVariables r').output)
        = (((u j).2.roundVariables r').output) := by
      intro r'
      by_cases hr' : r' = r
      · subst hr'
        simp only [Implementation.RoundVariablesMap.deliverTo, roundVariables_deliverTo,
          RoundVariables.deliverTo,
            Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]
        cases m <;> simp
      · rw [Implementation.RoundVariablesMap.deliverTo,
          Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    exact ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        hga2,
        hcand, hout, hrun⟩

/-! ### Matching the return of a broadcast instance

A broadcast instance returns to the acting process: the instance's return flag goes on and the
process's gather variables file what it returned, which is the return event of that gather. -/

/-- A broadcast instance's return is one silent transition of the round. -/
theorem roundVariables_match_gbcaRoundEvent (P : Parameters)
    {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} (w : NetworkState P.n) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} (hu : (u j).2 = p) {r : ℕ}
    {e : RoundEvent P.n} {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j e)) μ) :
    ∃ x : AFW.ProcessVariables P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.roundVariables r' = p.roundVariables r') ∧
      (∀ r',
        ((x.2.roundVariables r').secondGather.processVariables).input = ((p.roundVariables
            r').secondGather.processVariables).input ∨
          (((x.2.roundVariables r').secondGather.processVariables).input ≠ none ∧
            (p.roundVariables r').candidate ≠ none)) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaRoundEvent r j e))) r) := by
  subst hu
  cases h with
  | firstGatherReturn _ _ _ g hh hterm hin hbind hsubap hQ hr1 hcand =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput_or rfl, ?_⟩
    rw [roundProjection_firstGatherReturn rfl r g]
    exact roundOverBracha_run_one
      (roundOverBracha_firstGatherReturn (roundProjection P u w r) j g hin hcand
        (Gather.AlgorithmOverBracha.ret _ j g hin hbind hsubap hQ hr1))
  | secondGatherCall _ _ _ x hh hterm hcand hin2 =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        fun r' => ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'
        exact Or.inr ⟨by simp
          [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables], by rw [hcand]; simp⟩
      · exact Or.inl (by
          rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr'])
    · rw [roundProjection_secondGatherCall rfl]
      exact roundOverBracha_run_one
        (roundOverBracha_secondGatherCall (roundProjection P u w r) j x hcand
          (by simp [programProjection, hin2]) hin2)
  | secondGatherReturn _ _ _ g hh hterm hin hbind hsubap hQ hr2 hout =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput_or rfl, ?_⟩
    rw [roundProjection_secondGatherReturn rfl r g hr2]
    refine roundOverBracha_run_one
      (roundOverBracha_secondGatherReturn (roundProjection P u w r) j g ?_ hout
        (Gather.AlgorithmOverBracha.ret _ j g hin hbind hsubap hQ hr2))
    change (((u j).2.roundVariables r).secondGather.processVariables).input.isSome = true
    exact Option.isSome_iff_ne_none.mpr hin
  | firstGatherInputBroadcastReturn _ _ _ i v hh hterm hcnt hret =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        fun r' => Or.inl ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp [LocalState.setProcessVariables]
      · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    · rw [roundProjection_firstGatherInputBroadcastReturn rfl r i v]
      refine roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        (Gather.AlgorithmOverBracha.inputBroadcastRet (firstGatherProjection P u w r) i j v _
          (BRB.BrachaAlgorithm.ret _ j v ?_ hret)))
      rw [InstanceState.receivedCount_eq_localState]
      exact hcnt
  | firstGatherBindBroadcastReturn _ _ _ q U hh hterm hcnt hret =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        fun r' => Or.inl ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp [LocalState.setProcessVariables]
      · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    · rw [roundProjection_firstGatherBindBroadcastReturn rfl r q U]
      refine roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        (Gather.AlgorithmOverBracha.bindRet (firstGatherProjection P u w r) q j U _
          (BRB.BrachaAlgorithm.ret _ j U ?_ hret)))
      rw [InstanceState.receivedCount_eq_localState]
      exact hcnt
  | secondGatherInputBroadcastReturn _ _ _ i v hh hterm hcnt hret =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        fun r' => Or.inl ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp [LocalState.setProcessVariables]
      · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    · rw [roundProjection_secondGatherInputBroadcastReturn rfl r i v]
      refine roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        (Gather.AlgorithmOverBracha.inputBroadcastRet (secondGatherProjection P u w r) i j v _
          (BRB.BrachaAlgorithm.ret _ j v ?_ hret)))
      rw [InstanceState.receivedCount_eq_localState]
      exact hcnt
  | secondGatherBindBroadcastReturn _ _ _ q U hh hterm hcnt hret =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        fun r' => Or.inl ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp [LocalState.setProcessVariables]
      · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
    · rw [roundProjection_secondGatherBindBroadcastReturn rfl r q U]
      refine roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        (Gather.AlgorithmOverBracha.bindRet (secondGatherProjection P u w r) q j U _
          (BRB.BrachaAlgorithm.ret _ j U ?_ hret)))
      rw [InstanceState.receivedCount_eq_localState]
      exact hcnt

/-! ### Matching the call, the graded return and the call loop -/

/-- The graded-agreement call of the implementation is the round's own call. -/
theorem roundVariables_match_callG (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {b : Bool}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inl (.callG r j b)) μ) :
    ∃ x : AFW.ProcessVariables P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.processVariables.phase = .toCallG ∧ c.processVariables.round = r ∧
      c.processVariables.estimate = some b ∧
      x.1 = c.setProcessVariables { c.processVariables with phase := .awaitG } ∧
      (∀ r', r' ≠ r → x.2.roundVariables r' = p.roundVariables r') ∧
      (∀ r',
        ((x.2.roundVariables r').secondGather.processVariables).input = ((p.roundVariables
          r').secondGather.processVariables).input) ∧
      (∀ r', (x.2.roundVariables r').candidate = (p.roundVariables r').candidate) ∧
      (∀ r', (x.2.roundVariables r').output = (p.roundVariables r').output) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (roundProjection P u w r) (Sum.inl (.callG r j b))
        (roundProjection P (Function.update u j x)
          ((w.recordGBCACall r j (gbcaCallPayload P j b)).writeGhost (ghostStep P)
            (Sum.inl (.callG r j b))) r) := by
  subst hu
  cases h with
  | callG _ _ _ _ hh hph hr hterm hest hin =>
    have htransition := Gather.AlgorithmOverBracha.call (firstGatherProjection P u w r) j b hin
    refine ⟨_, rfl, hh, hph, hr, hest, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput rfl,
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
          ?_⟩
    · rw [show w.recordGBCACall r j (gbcaCallPayload P j b) = w from rfl, roundProjection_callG rfl]
      exact System.weakLStep_of_step (by simp)
        (roundOverBracha_callG (roundProjection P u w r) j b hin hin)

/-- The graded-agreement return of the implementation is the round's own return, the graded
outcome read off what the second gather's return left in the variables. -/
theorem roundVariables_match_retG (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {out : GBCAOutput}
    {bnd : Bool} {μ : PMF (AFW.ProcessVariables P.n)} (hbnd : bnd = ghostOutput P w r j out)
    (hset : ∀ i, ((u i).2.roundVariables r).candidate ≠ none → (w.ghost r).2.2 ≠ none)
    (hcand : ∀ i, ((u i).2.roundVariables r).output ≠ none →
      ((u i).2.roundVariables r).candidate ≠ none)
    (h : RoundStep P j (c, p) (Sum.inl (.retG r j out bnd)) μ) :
    ∃ x : AFW.ProcessVariables P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.processVariables.phase = .awaitG ∧ c.processVariables.round = r ∧
      x.1 = c.setProcessVariables { c.processVariables with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW } ∧
      (∀ r', r' ≠ r → x.2.roundVariables r' = p.roundVariables r') ∧
      (∀ r',
        ((x.2.roundVariables r').secondGather.processVariables).input = ((p.roundVariables
          r').secondGather.processVariables).input) ∧
      (∀ r', (x.2.roundVariables r').candidate = (p.roundVariables r').candidate) ∧
      (∀ r', (x.2.roundVariables r').output ≠ none → (p.roundVariables r').output ≠ none) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (roundProjection P u w r) (Sum.inl (.retG r j out
        bnd))
        (roundProjection P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out bnd))) r) := by
  subst hu
  cases h with
  | retG _ _ _ _ _ hh hph hr hterm hout hr2 =>
    obtain ⟨β, hβ⟩ :=
      Option.ne_none_iff_exists'.mp (hset j (hcand j (by rw [hout]; simp)))
    have hb : bnd = (GBCA.ByAFW.bound (roundProjection P u w r)).getD (GBCA.boundOfCore P ∅) := by
      rw [hbnd]
      unfold ghostOutput
      simp only [bound_roundProjection, hβ, Option.getD_some]
    subst hb
    refine ⟨_, rfl, hh, hph, hr, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput rfl,
        roundVariables_setRoundVariables_candidate rfl, fun r' => ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'
        rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]
        exact fun hne => absurd rfl hne
      · rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr']
        exact id
    · rw [roundProjection_retG rfl r out _ _ hr2]
      exact System.weakLStep_of_step (by simp)
        (roundOverBracha_retG (roundProjection P u w r) j out
          (by simp only [programs_roundProjection, programProjection]; exact hout)
          (by simp [programProjection, hout]))

/-- The call against variables already called: the round loop moves, the round
takes its input-enabledness loop and the projection is unchanged. -/
theorem roundVariables_match_gbcaCallLoop (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables
  P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {b : Bool} {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaCallLoop r j b)) μ) :
    ∃ x : AFW.ProcessVariables P.n, μ = PMF.pure x ∧ x.2 = p ∧
      c.corrupted = false ∧ c.processVariables.phase = .toCallG ∧ c.processVariables.round = r ∧
      c.processVariables.estimate = some b ∧
      x.1 = c.setProcessVariables { c.processVariables with phase := .awaitG } ∧
      (GBCA.ByAFW.roundOverBracha P r).step (roundProjection P u w r) (Sum.inr (.gbcaCallLoop r j
        b))
        (PMF.pure (roundProjection P u w r)) := by
  subst hu
  cases h with
  | gbcaCallLoop _ _ _ _ hh hph hr hest hin =>
    exact ⟨_, rfl, rfl, hh, hph, hr, hest, rfl,
      roundOverBracha_callLoop (roundProjection P u w r) j b⟩

/-! ### Matching a Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the network state its tag names and no process's variables move. -/

theorem byzantine_match (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (r : ℕ) {k : Fin P.n}
    (m : Message P.n) (hF : k ∈ w.F) :
    (GBCA.ByAFW.roundOverBracha P r).step (roundProjection P u w r) (Sum.inl Label.tau)
    (PMF.pure (roundProjection P u (w.recordGBCASend r k m) r)) := by
  cases m with
  | firstGather mm =>
    have htransition := Gather.AlgorithmOverBracha.byzantine (firstGatherProjection P u w r) k mm hF
    rw [roundProjection_byzantineFirstGather]
    exact roundOverBracha_firstGatherTau (roundProjection P u w r) htransition
  | secondGather mm =>
    have htransition := Gather.AlgorithmOverBracha.byzantine (secondGatherProjection P u w r) k mm
      hF
    rw [roundProjection_byzantineSecondGather]
    exact roundOverBracha_secondGatherTau (roundProjection P u w r) htransition
  | firstGatherInputBroadcasts i mm =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.byzantine (Gather.inputBroadcasts (firstGatherProjection P u w r) i) k mm
        hF)
    rw [roundProjection_byzantineFirstGatherInputBroadcast]
    exact roundOverBracha_firstGatherTau (roundProjection P u w r) htransition
  | firstGatherBindBroadcasts i mm =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (firstGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.byzantine (Gather.bindBroadcasts (firstGatherProjection P u w r) i) k mm
        hF)
    rw [roundProjection_byzantineFirstGatherBindBroadcast]
    exact roundOverBracha_firstGatherTau (roundProjection P u w r) htransition
  | secondGatherInputBroadcasts i mm =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w
      r) i _
      (BRB.BrachaAlgorithm.byzantine (Gather.inputBroadcasts (secondGatherProjection P u w r) i) k
        mm hF)
    rw [roundProjection_byzantineSecondGatherInputBroadcast]
    exact roundOverBracha_secondGatherTau (roundProjection P u w r) htransition
  | secondGatherBindBroadcasts i mm =>
    have htransition := Gather.AlgorithmOverBracha.bindBroadcastTau (secondGatherProjection P u w r)
      i _
      (BRB.BrachaAlgorithm.byzantine (Gather.bindBroadcasts (secondGatherProjection P u w r) i) k mm
        hF)
    rw [roundProjection_byzantineSecondGatherBindBroadcast]
    exact roundOverBracha_secondGatherTau (roundProjection P u w r) htransition

end AFW

end ABA
end PLTS
