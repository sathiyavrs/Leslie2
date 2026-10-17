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
protocol as a composition of components, with the broadcast instances beneath. Each transition of
the implementation's rounds is matched here by a run of the composed round from the state the
projection `AFW.roundProjection` computes: the lemmas that read a round transition from its label,
the builders of a transition of one gather instance and of one round, and corruption read through
the projection. The matching runs follow the label classes.
A send is one silent transition of the round: an `ECHO`, `VOTE` or `BIND` multicast on a gather
network, or a step of an input instance.
A delivery is one silent transition of the gather instance or of the input instance the message's
tag names. At a terminated program the delivery leaves the variables where they stand (D22), and
the run is empty.
A round event is a call or a return of an input instance, or a hidden event of the round. The
first gather's return is matched by two hidden events. On the first, the gather returns to the
process, which records its candidate, and the gather records its core. On the second, the gather
announces that core, and the round's network records it where none is recorded.
The graded-agreement call and the graded return are the round's own call and return, on the same
labels. The call is taken on two transitions (D36): at a first gather holding no input the call
records the input, and at one holding an input the composed round takes its `callLoop`. The label
of the graded return carries the graded outcome alone, and the round's network records that the
round has returned. The announcement of the bound bit is the round network's own announcement
(`roundOverBracha_announceBound`).
A Byzantine injection is a message of a corrupted sender at a started round (D11, D37), and it is
one silent transition of the instance the message reaches.
`ABA/AFW/Simulation.lean` assembles these runs into the matching.

## The relation across a transition of one round

`relation_roundStep` carries `AFW.ProtocolRelation` across a transition of one process at one round
`r`, every other process idle: the family's round `r` is set to the projection of round `r` after
the transition. The conjuncts that are not projections are carried by the lemmas of
`AFW/RoundProjectionStep/ProtocolRelationConjuncts.lean` for a round transition
(`roundVariablesMap_lookup_roundStep`, `boundInvariant_roundStep`). -/


namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

/-! ### A transition determined by a label the process owns

A program's transition on a label of `roundOwn j` is a transition of the round, with one
exception: the replaced program takes a round delivery addressed to it on its self-loop (D23).
Every other transition of the program carries a label of another class, or one of these labels at
another process. -/

/-- A program's transition on a label of `roundOwn j` other than a delivery is a transition of the
round: the replaced program has no transition on such a label. -/
theorem roundTransition_of_own {P : Parameters} {j : Fin P.n} {q : AFW.ProcessVariables P.n}
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    {y : AFW.ProcessVariables P.n} (hown : roundOwn j L)
    (hdeliver : ∀ r k m, L ≠ Sum.inr (.gbcaDeliver r j k m))
    (h : ProgramStep P j q L (PMF.pure y)) : RoundStep P j q L (PMF.pure y) := by
  generalize hμ : (PMF.pure y : PMF (AFW.ProcessVariables P.n)) = ν at h
  cases h
  case roundTransition h' => exact hμ ▸ h'
  case corruptedIdle hh hτ hown' => exact absurd (actsAt_of_roundOwn hown hdeliver) hown'
  all_goals first
    | exact hown.elim
    | (rename_i hid; exact absurd hown hid)

/-- A program's transition on a label of `roundOwn j`, at an unreplaced program, is a transition
of the round. -/
theorem roundTransition_of_correct {P : Parameters} {j : Fin P.n} {q : AFW.ProcessVariables P.n}
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    {y : AFW.ProcessVariables P.n} (hown : roundOwn j L) (hc : q.1.corrupted = false)
    (h : ProgramStep P j q L (PMF.pure y)) : RoundStep P j q L (PMF.pure y) := by
  generalize hμ : (PMF.pure y : PMF (AFW.ProcessVariables P.n)) = ν at h
  cases h
  case roundTransition h' => exact hμ ▸ h'
  case corruptedIdle hh hτ hown' => simp_all
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

/-! ### The relation across a transition of one round

A transition of process `j` at round `r`, every other process idle, sets the family's round `r` to
the projection of round `r` after it. The network after the transition is the ghost write at its
label of a network `v` that holds the sent sets of every other round, the ghosts, the corrupted
set and the DECIDED sets of the network before it, with `r` among its started rounds. -/

/-- The relation across a transition of process `j` at round `r`, the family's round `r` set to
the projection of round `r` after the transition. -/
theorem relation_roundStep (P : Parameters) {u x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w v : NetworkState P.n}
    {o o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {G : RoundFamilyOverBrachaState P} {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A A' : ABANetworkState P.n} (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    {r : ℕ} {j : Fin P.n} {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    (hL : roundOf L = some r) (hstep : RoundStep P j (u j) L (PMF.pure (x j)))
    (hfor : ∀ i, i ≠ j → x i = u i) (hcorrupted : (x j).1.corrupted = (u j).1.corrupted)
    (hC' : ∀ i, (x i).1 = C' i) (hA' : A' = ⟨v.decidedSent, v.F, v.startedRounds⟩)
    (hStarted : v.startedRounds = insert r w.startedRounds) (hF : v.F = w.F)
    (hsent : ∀ r', r' ≠ r → v.sent r' = w.sent r') (hghost : ∀ r', v.ghost r' = w.ghost r') :
    ProtocolRelation P (x, v.writeGhost (ghostStep P) L, o')
      (G.setInstanceState r (roundProjection P (Function.update u j (x j))
        (v.writeGhost (ghostStep P) L) r), C', A', o') := by
  obtain ⟨-, -, -, -, -, -, -, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hx : x = Function.update u j (x j) := funext fun i => by
    by_cases hi : i = j
    · subst hi; simp
    · rw [Function.update_of_ne hi, hfor i hi]
  refine protocolRelation_setInstanceState hR r (by rw [← hx]) hC' (by rw [hA']; simp)
    (by rw [writeGhost_startedRounds, hStarted]) (by rw [writeGhost_F, hF])
    (fun r' hr' => by rw [writeGhost_sent, hsent r' hr'])
    (fun r' hr' => by rw [writeGhost_ghost_ne _ hL hr', hghost r'])
    (fun i r' hr' => ?_) (fun i => ?_) ?_
  · by_cases hi : i = j
    · subst hi; exact roundVariablesMap_lookup_roundStep hL hstep hr'
    · rw [hfor i hi]
  · by_cases hi : i = j
    · subst hi; exact hcorrupted
    · rw [hfor i hi]
  · rw [hx]; exact boundInvariant_roundStep hB rfl hstep hghost

/-! ### Building a transition of one gather instance

`Gather.instanceOverBracha_step_iff_algorithm` characterises the transitions of the instance by
`Gather.AlgorithmOverBracha`, label by label, on the same state and with the same distribution. The
builders below read that characterisation at the labels the round uses. The instance takes the call
`call id x` on two transitions: the call at a program holding no input, and the
input-enabledness loop at a program holding one. -/

section GatherTransitions

variable {P : Parameters} {X : Type} [DecidableEq X]

/-- Build the instance's call: the gather variables record the payload. -/
theorem transition_instanceOverBracha_call (s : Gather.StateOverBracha P.n X) (id : Fin P.n) (x : X)
    (h : ((Gather.gatherProgramsAndNetwork s).processVariables id).input = none) :
    (Gather.instanceOverBracha P X).step s (Gather.Label.call id x)
      (PMF.pure (Gather.setGatherProgramsAndNetwork s ((Gather.gatherProgramsAndNetwork
        s).setProcessVariables id
        { (Gather.gatherProgramsAndNetwork s).processVariables id with input := some x }))) :=
  Gather.algorithm_instanceOverBracha_step P _ _ _ (Gather.AlgorithmOverBracha.call s id x h)

/-- Build the call of the instance broadcasting the caller's input: that instance records the
payload the gather variables hold as the leader's input. -/
theorem transition_instanceOverBracha_inputBroadcastCall (s : Gather.StateOverBracha P.n X)
    (id : Fin P.n) (x : X) (hin : ((Gather.gatherProgramsAndNetwork s).processVariables id).input =
      some x)
    (hb : ((Gather.inputBroadcasts s id).processVariables id).input = none) :
    (Gather.instanceOverBracha P X).step s Gather.Label.tau
      (PMF.pure (Gather.setInputBroadcasts s
        (Function.update (Gather.inputBroadcasts s) id
          ((Gather.inputBroadcasts s id).setProcessVariables id
            { (Gather.inputBroadcasts s id).processVariables id with input := some x })))) :=
  Gather.algorithm_instanceOverBracha_step P _ _ _
    (Gather.AlgorithmOverBracha.inputBroadcastCall s id x hin hb)

/-- Build the instance's input-enabledness loop, at a program holding an input: nothing moves. -/
theorem transition_instanceOverBracha_callLoop (s : Gather.StateOverBracha P.n X) (id : Fin P.n)
    (x : X) (hin : ((Gather.gatherProgramsAndNetwork s).processVariables id).input ≠ none) :
    (Gather.instanceOverBracha P X).step s (Gather.Label.call id x) (PMF.pure s) :=
  Gather.algorithm_instanceOverBracha_step P _ _ _ (Gather.AlgorithmOverBracha.callLoop s id x hin)

end GatherTransitions

/-! ### Building a transition of one round

One transition of the round's programs and of the round's network beside one transition of a
gather instance, on the label the round takes them on. The round's hidden events
`firstGatherReturn`, `firstGatherCore`, `secondGatherCall` and `secondGatherReturn` are silent
transitions of the round. The call, its loop, the graded return and the announcement of the bound
bit are transitions on labels of the family alphabet. -/

section RoundTransitions

variable {P : Parameters} {r : ℕ}

/-- A silent transition of the first gather is a silent transition of the round. -/
theorem roundOverBracha_firstGatherTau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {c : Gather.StateOverBracha P.n Bool}
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.firstGather s) Gather.Label.tau (PMF.pure c)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (GBCA.ByAFW.setFirstGather s c)) :=
  GBCA.ByAFW.roundOverGathers_tau_firstGather (Gather.algorithm_instanceOverBracha_step P _ _ _ h)

/-- A silent transition of the second gather is a silent transition of the round. -/
theorem roundOverBracha_secondGatherTau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {d : Gather.StateOverBracha P.n (Option Bool)}
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.secondGather s) Gather.Label.tau (PMF.pure d)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (GBCA.ByAFW.setSecondGather s d)) :=
  GBCA.ByAFW.roundOverGathers_tau_secondGather (Gather.algorithm_instanceOverBracha_step P _ _ _ h)

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

/-- **The round's call loop**, on the label of the call (D36): at a program and a first gather
holding an input, the program and the first gather take their input-enabledness loops, and nothing
moves. -/
theorem roundOverBracha_callLoop (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (b : Bool) (hin : (GBCA.ByAFW.programs s id).input ≠ none)
    (hg : ((Gather.gatherProgramsAndNetwork (GBCA.ByAFW.firstGather s)).processVariables id).input
      ≠ none) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl (Label.callG r id b)) (PMF.pure s) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  refine GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .callG r id b) (by simp) (by simp) (fun i => ?_)
      (GBCA.ByAFW.NetworkStep.callG y id b))
    (System.mapIdle_step_of_step (by simp) (transition_instanceOverBracha_callLoop c id b hg))
    (System.mapIdle_unchanged (by simp))
  by_cases hi : i = id
  · subst hi; exact GBCA.ByAFW.ProgramStep.callLoop (v i) b hin
  · exact GBCA.ByAFW.ProgramStep.callGIdle (v i) id b (Ne.symm hi)

/-- **The first gather's return**, the first of its two events: the program records the candidate,
and the first gather marks the process returned and records its core where none is recorded. The
round's network stands. -/
theorem roundOverBracha_firstGatherReturnEvent (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    (id : Fin P.n) (g : Fin P.n → Option Bool) (hin : (GBCA.ByAFW.programs s id).input ≠ none)
    (hc : (GBCA.ByAFW.programs s id).candidate = none)
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.firstGather s) (.ret id g)
      (PMF.pure (GBCA.ByAFW.firstGather (afterFirstGatherReturn P s id g)))) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
      (PMF.pure (GBCA.ByAFW.setNetwork (afterFirstGatherReturn P s id g)
        (GBCA.ByAFW.network s))) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_event_step (GBCA.ByAFW.RoundEvent.firstGatherReturn id g)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .firstGatherReturn id g) (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.firstGatherReturn (v id) g hin hc)
        (fun i hi => GBCA.ByAFW.ProgramStep.firstGatherReturnIdle (v i) id g (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.firstGatherReturn y id g))
    (System.mapIdle_step_of_step (by simp) (Gather.algorithm_instanceOverBracha_step P _ _ _ h))
    (System.mapIdle_unchanged (by simp))

/-- **The first gather's announcement of its core** `C`: no program moves, and the round's network
records `C` where no core is recorded. -/
theorem roundOverBracha_firstGatherCore (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    (C : Gather.AcceptedPairs P.n Bool) (h : Gather.core (GBCA.ByAFW.firstGather s) = some C) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
      (PMF.pure (GBCA.ByAFW.setNetwork s { GBCA.ByAFW.network s with
        firstGatherCore := some ((GBCA.ByAFW.network s).firstGatherCore.getD C) })) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_event_step (GBCA.ByAFW.RoundEvent.firstGatherCore C)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .firstGatherCore C) (by simp) (by simp)
      (fun i => GBCA.ByAFW.ProgramStep.firstGatherCoreIdle (v i) C)
      (GBCA.ByAFW.NetworkStep.firstGatherCore y C))
    (System.mapIdle_step_of_step (by simp)
      (Gather.algorithm_instanceOverBracha_step P _ _ _
        (Gather.AlgorithmOverBracha.announceCore c C h)))
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


/-- **The second gather's return**: the program records the grade, and the second gather marks the
process returned and records its core where none is recorded. -/
theorem roundOverBracha_secondGatherReturn (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) (h2 : (GBCA.ByAFW.programs s id).secondGatherCalled = true)
    (ho : (GBCA.ByAFW.programs s id).output = none)
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.secondGather s) (.ret id g)
      (PMF.pure (GBCA.ByAFW.secondGather (afterSecondGatherReturn P s id g)))) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (afterSecondGatherReturn P s id g)) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_event_step (GBCA.ByAFW.RoundEvent.secondGatherReturn id g)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .secondGatherReturn id g) (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.secondGatherReturn (v id) g h2 ho)
        (fun i hi => GBCA.ByAFW.ProgramStep.secondGatherReturnIdle (v i) id g (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.secondGatherReturn y id g))
    (System.mapIdle_unchanged (by simp))
    (System.mapIdle_step_of_step (by simp) (Gather.algorithm_instanceOverBracha_step P _ _ _ h))

/-- **The round's graded return**: the program returns the grade it holds, drops it and marks its
variables returned, and the round's network records that the round has returned. -/
theorem roundOverBracha_retG (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (out : GBCAOutput) (ho : (GBCA.ByAFW.programs s id).output = some out)
    (hr : (GBCA.ByAFW.programs s id).returned = false) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl (Label.retG r id out))
      (PMF.pure (afterRetG P s id)) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .retG r id out) (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.retG (v id) out ho hr)
        (fun i hi => GBCA.ByAFW.ProgramStep.retGIdle (v i) id out (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.retG y id out))
    (System.mapIdle_unchanged (by simp)) (System.mapIdle_unchanged (by simp))

/-- **The announcement of the round's bound bit**: at a round whose network records the first
gather's core `C` and the round's return, the round's network announces the bit
`GBCA.boundOfCore P C`, and nothing moves (D29). -/
theorem roundOverBracha_announceBound (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    (C : Gather.AcceptedPairs P.n Bool) (hC : (GBCA.ByAFW.network s).firstGatherCore = some C)
    (hr : (GBCA.ByAFW.network s).returned = true) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl (Label.boundG r (GBCA.boundOfCore P C)))
      (PMF.pure s) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .boundG r (GBCA.boundOfCore P C)) (by simp)
      (by simp) (fun i => GBCA.ByAFW.ProgramStep.boundGIdle (v i) _)
      (GBCA.ByAFW.NetworkStep.announceBound y C hC hr))
    (System.mapIdle_unchanged (by simp)) (System.mapIdle_unchanged (by simp))

/-! ### A run of one round -/

/-- One silent transition of the round is a silent run. -/
theorem roundOverBracha_run_one {q q' : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent q q' :=
  System.weakLSilent_stepCons (by rw [extendedLabel_tau]; exact h) (by simp)
    (System.weakLSilent_refl _ q')

/-- **The first gather's return as a run of two events**: the gather's return to `id`, then the
gather's announcement of the core it records, on which the round's network records that core
where none is recorded. The run reaches `afterFirstGatherReturn P s id g`. -/
theorem roundOverBracha_firstGatherReturn (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    (id : Fin P.n) (g : Fin P.n → Option Bool) (hin : (GBCA.ByAFW.programs s id).input ≠ none)
    (hc : (GBCA.ByAFW.programs s id).candidate = none)
    (h : Gather.AlgorithmOverBracha P (GBCA.ByAFW.firstGather s) (.ret id g)
      (PMF.pure (GBCA.ByAFW.firstGather (afterFirstGatherReturn P s id g)))) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent s (afterFirstGatherReturn P s id g) :=
  System.weakLSilent_stepCons
    (by rw [extendedLabel_tau]; exact roundOverBracha_firstGatherReturnEvent s id g hin hc h)
    (by simp)
    (roundOverBracha_run_one (roundOverBracha_firstGatherCore
      (GBCA.ByAFW.setNetwork (afterFirstGatherReturn P s id g) (GBCA.ByAFW.network s))
      (firstGatherReturnCore P s) rfl))

end RoundTransitions

/-! ### Corruption, read through the projection

Corruption reaches the round through its two gather instances: the corrupted set the adversary
holds is the corrupted set of every network state the projection assembles, and the programs and
the round's network state are untouched (D1). The round's network state is computed from the
ghost, which corruption leaves. -/

theorem roundProjection_fail {P : Parameters} (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) :
    roundProjection P u (Implementation.NetworkState.corrupt P k w) r
      = corruptionOverBracha P (Sum.inl (Label.fail k)) (roundProjection P u w r) := by
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_)
  · simp only [GBCA.ByAFW.programs, roundProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll,
      Implementation.NetworkState.corrupt]
  · simp only [GBCA.ByAFW.network, roundProjection, corruptionOverBracha, GBCA.ByAFW.corruptAll,
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
  · simp only [Gather.core, GBCA.ByAFW.secondGather, roundProjection, secondGatherProjection,
      corruptionOverBracha, GBCA.ByAFW.corruptAll, Gather.corruptAll,
        Implementation.NetworkState.corrupt]
    split_ifs <;> rfl

/-! ### Matching a send

A send of the implementation is a silent run of the round: the sender writes its own variables, the
network records the message, and the round the label tags moves as its own transitions move it.
The gather multicasts `ECHO`, `VOTE` and `BIND` are transitions of the gather instance; every
other send is a step of an input instance. -/

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
  | firstGatherBind _ _ _ U hh hterm hin hvot happ hQ hsend =>
    have htransition :=
      Gather.AlgorithmOverBracha.bind (firstGatherProjection P u w r) j U hin hvot happ hQ hsend
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
  | secondGatherBind _ _ _ U hh hterm hin hvot happ hQ hsend =>
    have htransition :=
      Gather.AlgorithmOverBracha.bind (secondGatherProjection P u w r) j U hin hvot happ hQ hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self,
          LocalState.setProcessVariables]), ?_⟩
    rw [roundProjection_secondGatherBind rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
        htransition)
  | firstGatherInputBroadcastInit _ _ _ b hh hterm hin hsend =>
    have htransition :=
      Gather.AlgorithmOverBracha.inputBroadcastTau (firstGatherProjection P u w r) j _
      (BRB.BrachaAlgorithm.init (Gather.inputBroadcasts (firstGatherProjection P u w r) j) b
        hin hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]),
          ?_⟩
    rw [roundProjection_firstGatherInputBroadcastInit rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
        htransition)
  | secondGatherInputBroadcastInit _ _ _ x hh hterm hin hsend =>
    have htransition :=
      Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w r) j _
      (BRB.BrachaAlgorithm.init (Gather.inputBroadcasts (secondGatherProjection P u w r) j) x
        hin hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl (by simp [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self]),
          ?_⟩
    rw [roundProjection_secondGatherInputBroadcastInit rfl]
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


/-! ### Matching a delivery

A delivery of the implementation files the message in the receiver's own local
state of the network state the message's tag names. A gather message moves the
gather instance alone, and a broadcast message moves the broadcast instance
alone: the instance's return to the receiver is a transition of its own. A delivery
at a terminated program leaves its variables where they stand (D22), and the round
stands. -/

/-- A delivery of the implementation is one silent transition of the round, or the empty run at a
terminated program. -/
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
  | deliverLoop _ _ _ _ _ hh hterm =>
    refine ⟨_, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    rw [roundProjection_deliverLoop rfl r r k m c]
    exact System.weakLSilent_refl _ _

/-! ### Matching a round event

The acting process calls an input instance: the instance records the payload as the leader's
input, which is the call event of that gather. An input instance returns to the acting process:
the return flag is set and the process's gather variables file what it returned, which is the
return event of that gather. The first gather's return is matched by two hidden events of the
round: the gather's return, on which the process records its candidate and the gather records its
core, and the gather's announcement of that core, on which the round's network records it. The
second gather's call and its return are one hidden event each. A gather's return waits on `n − f`
senders' `BIND` payloads delivered on the gather network. -/

/-- A round event is a silent run of the round: one silent transition, or two at the first
gather's return. -/
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
    exact roundOverBracha_firstGatherReturn (roundProjection P u w r) j g hin hcand
      (Gather.AlgorithmOverBracha.ret (firstGatherProjection P u w r) j g hin hbind hsubap hQ hr1)
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
        (Gather.AlgorithmOverBracha.ret (secondGatherProjection P u w r) j g hin hbind hsubap hQ
          hr2))
    change (((u j).2.roundVariables r).secondGather.processVariables).input.isSome = true
    exact Option.isSome_iff_ne_none.mpr hin
  | firstGatherInputBroadcastCall _ _ _ b hh hterm hin hbin =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput_or rfl, ?_⟩
    rw [roundProjection_firstGatherInputBroadcastCall rfl]
    exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
      (Gather.AlgorithmOverBracha.inputBroadcastCall (firstGatherProjection P u w r) j b hin hbin))
  | secondGatherInputBroadcastCall _ _ _ x hh hterm hin2 hbin2 =>
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput_or rfl, ?_⟩
    rw [roundProjection_secondGatherInputBroadcastCall rfl]
    exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
      (Gather.AlgorithmOverBracha.inputBroadcastCall (secondGatherProjection P u w r) j x hin2
        hbin2))
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

/-! ### Matching the call and the graded return

The graded-agreement call and the graded return are transitions on labels of the family alphabet,
and the composed round takes each on the same label. The call is taken on two transitions (D36):
at a first gather holding no input the call records the input, and at a first gather holding one
the round variables stand and the round takes its `callLoop`. The label of the graded return
carries the graded outcome alone. The round's network records that the round has returned, and the
projection computes that record from the bound bit the ghost write records. -/

/-- **The graded-agreement call of the implementation is the round's own call**, one transition of
the round on the same label. At a first gather holding no input the call records the input and the
round takes its `callG`. At a first gather holding one the round variables stand, the round takes
its `callLoop`, and the projection is the projection before the call. -/
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
      (((p.roundVariables r).firstGather.processVariables).input = none ∨
        (((p.roundVariables r).firstGather.processVariables).input ≠ none ∧ x.2 = p)) ∧
      (GBCA.ByAFW.roundOverBracha P r).step (roundProjection P u w r) (Sum.inl (.callG r j b))
        (PMF.pure (roundProjection P (Function.update u j x)
          ((w.recordStartedRound r j).writeGhost (ghostStep P) (Sum.inl (.callG r j b))) r)) := by
  subst hu
  cases h with
  | callG _ _ _ _ hh hph hr hterm hest hin =>
    refine ⟨_, rfl, hh, hph, hr, hest, rfl,
      fun r' hr' => Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr',
        roundVariables_setRoundVariables_secondGatherInput rfl,
        roundVariables_setRoundVariables_candidate rfl, roundVariables_setRoundVariables_output rfl,
        Or.inl hin, ?_⟩
    rw [roundProjection_callG rfl]
    exact roundOverBracha_callG (roundProjection P u w r) j b hin hin
  | callGLoop _ _ _ _ hh hph hr hest hin =>
    refine ⟨_, rfl, hh, hph, hr, hest, rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl, Or.inr ⟨hin, rfl⟩, ?_⟩
    rw [roundProjection_callGLoop rfl r r b]
    exact roundOverBracha_callLoop (roundProjection P u w r) j b hin hin

/-- **The graded return of the implementation is the round's own return**, on the same label: the
program returns the graded outcome the second gather's return left in the variables and drops it.
The first gather's core of the round is recorded wherever the variables hold a graded outcome
(`hcore`, which `AFW.BoundInvariant.firstGatherCore_of_output` supplies), so the ghost write
records the bound bit and the projection records that the round has returned. -/
theorem roundVariables_match_retG (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {out : GBCAOutput} {μ : PMF (AFW.ProcessVariables P.n)}
    (hcore : (p.roundVariables r).output ≠ none → (w.ghost r).1 ≠ none)
    (h : RoundStep P j (c, p) (Sum.inl (.retG r j out)) μ) :
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
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (roundProjection P u w r)
        (Sum.inl (.retG r j out))
        (roundProjection P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out))) r) := by
  subst hu
  cases h with
  | retG _ _ _ _ hh hph hr hterm hout hr2 =>
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
    · rw [roundProjection_retG rfl r out _ hr2 (hcore (by rw [hout]; simp))]
      exact System.weakLStep_of_step (by simp)
        (roundOverBracha_retG (roundProjection P u w r) j out
          (by simp only [programs_roundProjection, programProjection]; exact hout)
          (by simp [programProjection, hout]))

/-! ### Matching a Byzantine injection

The network injects a message of a corrupted sender at a started round (D11, D37). The
message reaches the network state its tag names and no process's variables move. -/

/-- A Byzantine injection is one silent transition of the round. -/
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
  | secondGatherInputBroadcasts i mm =>
    have htransition := Gather.AlgorithmOverBracha.inputBroadcastTau (secondGatherProjection P u w
      r) i _
      (BRB.BrachaAlgorithm.byzantine (Gather.inputBroadcasts (secondGatherProjection P u w r) i) k
        mm hF)
    rw [roundProjection_byzantineSecondGatherInputBroadcast]
    exact roundOverBracha_secondGatherTau (roundProjection P u w r) htransition

end AFW

end ABA
end PLTS
