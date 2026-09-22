/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.CompositeTransitions
import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The implementation's rows answered by runs of the composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed P` reads the same
protocol as a composition of components, down to the broadcast instances. Every row of the
implementation is answered here by a run of the composed system from the state the view
`AFW.roundProjection` reads: the readers that identify a row off its label, the builders of a
transition of one gather instance and of one round, the broadcast invariant across a row,
corruption read through the view, and the answers on a send, on a delivery, on the call and the
graded return, and on a Byzantine injection.
`ABA/ImplementationByAFW/Simulation.lean` assembles these answers into the matching.

## Three of the implementation's rows against two composed events

The composed round is a composition, so an implementation row that fuses two of its events
is answered by a run of two transitions and not by one. There are three:

* the return-then-call step, answered by the hidden events `firstGatherReturn` and
  `secondGatherCall` of round `r`;
* the graded return, answered by the hidden event `secondGatherReturn` and then the visible `retG`;
* a broadcast delivery that completes a `2f + 1` `VOTE` receipt quorum,
  answered by the instance's delivery and then its return.

## The returned value against the implementation's receipt quorum

A gather program of the composed system holds what each broadcast instance has returned to it; the
implementation reads a `2f + 1` `VOTE` receipt quorum on the process's own local state instead.
`AFW.broadcastReturnsFor_eq_of_quorum` identifies the two under `AFW.BroadcastReturnsInvariant`, and
`AFW.holdsInputBroadcastReturn_firstGather` and its three companions are that identification at the
four broadcast families. A delivery moves the returned value in one way only:
`AFW.broadcastReturnsFor_deliver_cases` says that it either leaves the returned value where it
stands or fills an empty one, which is the dichotomy between the plain delivery lemmas of
`ABA/ImplementationByAFW/RoundProjectionStep/Delivery.lean` and their quorum companions.

## The two clauses that are not projections

`AFW.RoundInvariant` is `AFW.BroadcastReturnsInvariant` at one round, and
`AFW.broadcastReturnsInvariant_update` carries it across a row from the round the row names. Every
row of a gather instance moves each of its `2n` broadcast instances by `AFW.InvariantStep`
(`AFW.stepOverBracha_invariantStep`), so `AFW.roundInvariant_firstGather` and
`AFW.roundInvariant_secondGather` re-establish the invariant from the rows the answer fires.
`AFW.boundInvariant_of` and `AFW.writeGhost_bound` carry the bound invariant, whose one open case is
the return-then-call step: there the ghost write puts the round's bound bit on record, which is
`AFW.roundRecord_gbcaSend_secondGather`. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

/-! ### Reading a row off a label the process owns

A program's row on a label of `roundOwn j` is a row of the implementation:
every other row of the implementation either carries a label of another class,
or carries one of these at another process, or is the replaced program's
self-loop, which has no row on a label the process acts on. -/

theorem roundRow_of_own {P : Parameters} {j : Fin P.n} {q : AFW.ProcessRecord P.n}
    {L : ExtendedLabel P.n (Message P.n)} {y : AFW.ProcessRecord P.n} (hown : roundOwn j L)
    (h : ProgramStep P j q L (PMF.pure y)) : RoundStep P j q L (PMF.pure y) := by
  generalize hμ : (PMF.pure y : PMF (AFW.ProcessRecord P.n)) = ν at h
  cases h
  case roundRow h' => exact hμ ▸ h'
  case corruptedIdle hh hτ hown' => exact absurd (actsAt_of_roundOwn hown) hown'
  all_goals first
    | exact hown.elim
    | (rename_i hid; exact absurd hown hid)

/-- **The second gather's local input is written at the return-then-call step alone**: a send either
leaves every round's input where it stands, or carries the return-then-call step's `⟨INIT, ·⟩` in
the caller's own input-broadcast instance of the second gather. -/
theorem roundRecord_gbcaSend_secondGather (P : Parameters) {j : Fin P.n} {c : RoundLoopRecord P.n}
    {p : RoundRecordMap P.n} {r : ℕ} {m : Message P.n} {μ : PMF (AFW.ProcessRecord P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaSend r j m)) μ) :
    (∀ x : AFW.ProcessRecord P.n, μ = PMF.pure x → ∀ r',
        (((x.2.roundRecord r').secondGather.process)).input = ((p.roundRecord
          r').secondGather.process).input)
      ∨ ∃ q y, m = Message.secondGatherInputBroadcasts q (BRB.Message.init y) := by
  cases h <;> first
    | exact Or.inr ⟨_, _, rfl⟩
    | exact Or.inl (fun x hx r' =>
        by
        obtain rfl := pure_inj hx.symm
        by_cases hr' : r' = r
        · subst hr'; simp [LocalState.setProcess]
        · rw [Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr'])

/-! ### The returned value against the implementation's receipt quorum

A gather program of the composed system reads what the instances returned; the implementation reads
a `2f + 1` `VOTE` receipt quorum on the process's own local state in the instance. Under
`BroadcastReturnsInvariant` the two agree wherever the implementation's guard fires. -/

section BroadcastReturns

variable {P : Parameters} {X : Type} [DecidableEq X]

/-- The return flag the view supplies leaves the returned value where it stands. -/
theorem broadcastReturnsFor_broadcastLocalState (p : LocalState P.n (BRB.ProcessRecord X)
  (BRB.Message X)) :
    broadcastReturnsFor P (broadcastLocalState P p) = broadcastReturnsFor P p := rfl

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n}

/-- The first gather's input instance returned the value an implementation receipt quorum
carries. -/
theorem holdsInputBroadcastReturn_firstGather (hI : BroadcastReturnsInvariant P u w) (r : ℕ)
    (j k : Fin P.n) {x : Bool} (hq : firstGatherAcceptedInputs P ((u j).2.roundRecord r) k x) :
    Gather.holdsInputBroadcastReturn
    ((Gather.gatherTier (GBCA.ByAFW.firstGather (roundProjection P u w r))).process j) k x :=
  broadcastReturnsFor_eq_of_quorum P (hI r k).1 (j := j) hq

/-- The first gather's bind instance returned the payload an implementation receipt quorum
carries. -/
theorem holdsBindBroadcastReturn_firstGather (hI : BroadcastReturnsInvariant P u w) (r : ℕ)
    (j q : Fin P.n) {U : Gather.AcceptedPairs P.n Bool}
    (hq : firstGatherAcceptedBinds P ((u j).2.roundRecord r) q U) :
    Gather.holdsBindBroadcastReturn
    ((Gather.gatherTier (GBCA.ByAFW.firstGather (roundProjection P u w r))).process j) q U :=
  broadcastReturnsFor_eq_of_quorum P (hI r q).2.1 (j := j) hq

/-- The second gather's input instance returned the value an implementation receipt quorum
carries. -/
theorem holdsInputBroadcastReturn_secondGather (hI : BroadcastReturnsInvariant P u w) (r : ℕ)
    (j k : Fin P.n) {x : Option Bool}
    (hq : secondGatherAcceptedInputs P ((u j).2.roundRecord r) k x) :
    Gather.holdsInputBroadcastReturn
    ((Gather.gatherTier (GBCA.ByAFW.secondGather (roundProjection P u w r))).process j) k x :=
  broadcastReturnsFor_eq_of_quorum P (hI r k).2.2.1 (j := j) hq

/-- The second gather's bind instance returned the payload an implementation receipt quorum
carries. -/
theorem holdsBindBroadcastReturn_secondGather (hI : BroadcastReturnsInvariant P u w) (r : ℕ)
    (j q : Fin P.n) {U : Gather.AcceptedPairs P.n (Option Bool)}
    (hq : secondGatherAcceptedBinds P ((u j).2.roundRecord r) q U) :
    Gather.holdsBindBroadcastReturn
    ((Gather.gatherTier (GBCA.ByAFW.secondGather (roundProjection P u w r))).process j) q U :=
  broadcastReturnsFor_eq_of_quorum P (hI r q).2.2.2 (j := j) hq

/-- The receiver's own local state after a delivery. -/
theorem receiveMessage_self (s : BRB.BrachaState P.n X) (i k : Fin P.n) (m : BRB.Message X) :
    (s.receiveMessage i k m).1 i = (s.1 i).deliverTo k m := Function.update_self _ _ _

/-- The return flag the view supplies is on exactly where the instance has returned a value. -/
theorem broadcastLocalState_returned (p : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) :
    ((broadcastLocalState P p).process).returned = (broadcastReturnsFor P p).isSome := rfl

/-- **A delivery that supplies a first returned value licenses the instance's return to the
receiver.** -/
theorem brachaStep_ret_of_broadcastReturn {i j k : Fin P.n} {s : BRB.BrachaState P.n X}
    {m : BRB.Message X} {v : X} (hr : (s.process j).returned = false)
    (hst : broadcastReturnsFor P ((s.1 j).deliverTo k m) = some v) :
    BRB.BrachaStep P i (s.receiveMessage j k m) (.ret j v)
      (PMF.pure ((s.receiveMessage j k m).setProcess j
        { (s.receiveMessage j k m).process j with returned := true })) := by
  refine BRB.BrachaStep.ret _ j v ?_ ?_
  · rw [InstanceState.receivedCount_eq_localState, receiveMessage_self]
    exact broadcastReturnsFor_voteQuorum P hst
  · rw [InstanceState.receiveMessage_process]
    exact hr

/-- **A delivery moves the returned value in one way only.** Under the broadcast invariant at most
one value carries a receipt quorum, so a delivery either leaves the returned value where it stands
or fills an empty one. -/
theorem broadcastReturnsFor_deliver_cases {i j k : Fin P.n} {s : BRB.BrachaState P.n X}
    {m : BRB.Message X} (hInv : BRB.Invariant P i (s.receiveMessage j k m)) :
    broadcastReturnsFor P ((s.1 j).deliverTo k m) = broadcastReturnsFor P (s.1 j) ∨
      (broadcastReturnsFor P (s.1 j) = none ∧
        ∃ v, broadcastReturnsFor P ((s.1 j).deliverTo k m) = some v) := by
  have hpost : (s.receiveMessage j k m).1 j = (s.1 j).deliverTo k m := Function.update_self _ _ _
  have hmono : ∀ y : X, 2 * P.f + 1 ≤ (s.1 j).receivedCount (BRB.Message.vote y) →
      2 * P.f + 1 ≤ ((s.1 j).deliverTo k m).receivedCount (BRB.Message.vote y) := by
    intro y hy
    have h1 := InstanceState.receivedCount_le_receiveMessage s j k m j (BRB.Message.vote y)
    rw [InstanceState.receivedCount_eq_localState, InstanceState.receivedCount_eq_localState,
      hpost] at h1
    exact le_trans hy h1
  by_cases hq : ∃ y, 2 * P.f + 1 ≤ ((s.1 j).deliverTo k m).receivedCount (BRB.Message.vote y)
  · obtain ⟨v, hv⟩ := hq
    have hsome : broadcastReturnsFor P ((s.1 j).deliverTo k m) = some v := by
      have h := broadcastReturnsFor_eq_of_quorum P hInv (j := j) (x := v) (by rw [hpost]; exact hv)
      rwa [hpost] at h
    by_cases hb : broadcastReturnsFor P (s.1 j) = none
    · exact Or.inr ⟨hb, v, hsome⟩
    · obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp hb
      refine Or.inl ?_
      have h := broadcastReturnsFor_eq_of_quorum P hInv (j := j) (x := v')
        (by rw [hpost]; exact hmono v' (broadcastReturnsFor_voteQuorum P hv'))
      rw [hpost] at h
      rw [h, hv']
  · simp only [not_exists, not_le] at hq
    have hnone : broadcastReturnsFor P ((s.1 j).deliverTo k m) = none := by
      unfold broadcastReturnsFor
      rw [dif_neg]
      rintro ⟨y, hy⟩
      exact absurd hy (not_le.mpr (hq y))
    refine Or.inl ?_
    rw [hnone]
    unfold broadcastReturnsFor
    rw [dif_neg]
    rintro ⟨y, hy⟩
    exact absurd (hmono y hy) (not_le.mpr (hq y))

end BroadcastReturns

/-! ### Building a transition of one gather instance

A row of `Gather.StepOverBracha` is a transition of the instance at the interface
label over its own. The call is the exception: the instance answers `call id x`
on two rows, and the two sit at the two labels of the interface. -/

section GatherRows

variable {P : Parameters} {X : Type} [DecidableEq X]

/-- A row at a label other than a call is a transition of the instance at the
interface label over it. -/
theorem row_instanceOverBracha_inl {s : Gather.StateOverBracha P.n X} {l₀ : Gather.Label P.n X}
    {μ : PMF (Gather.StateOverBracha P.n X)}
    (h0 : ∀ (id : Fin P.n) (x : X), l₀ ≠ Gather.Label.call id x)
    (h : Gather.StepOverBracha P s l₀ μ) : (Gather.instanceOverBracha P X).step s (Sum.inl l₀) μ :=
      by
  obtain ⟨l, hl, hstep⟩ := Gather.row_instanceOverBracha_step P s l₀ μ h
  cases l with
  | inl y => rwa [Option.some.inj hl] at hstep
  | inr e => cases e with
    | callLoop id x => exact absurd (Option.some.inj hl).symm (h0 id x)

/-- Build the instance's call: the gather record records the payload and the
caller's own input instance broadcasts it. -/
theorem row_instanceOverBracha_call (s : Gather.StateOverBracha P.n X) (id : Fin P.n) (x : X)
    (h : ((Gather.gatherTier s).process id).input = none)
    (hb : ((Gather.inputBroadcasts s id).process id).input = none) :
    (Gather.instanceOverBracha P X).step s (Sum.inl (Gather.Label.call id x))
      (PMF.pure (Gather.setInputBroadcasts
        (Gather.setGatherTier s ((Gather.gatherTier s).setProcess id
          { (Gather.gatherTier s).process id with input := some x }))
        (Function.update (Gather.inputBroadcasts s) id
          (((Gather.inputBroadcasts s id).setProcess id
            { (Gather.inputBroadcasts s id).process id with input := some x }).multicast id (.init
              x))))) := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  exact Gather.instanceOverBroadcasts_label_step (b' := b) (by simp)
    (dirac_steps_update (Gather.ProgramStep.call (v id) x h)
      (fun i hi => Gather.ProgramStep.callIdle (v i) id x (Ne.symm hi)))
    (Gather.NetworkStep.call y id x)
    (System.mapIdle_step_update (by simp) (fun k hk => by simp [hk])
      (Gather.row_brachaInstance_call_step P id (a id) x hb))
    (fun _ => System.mapIdle_unchanged rfl)

/-- Build the instance's input-enabledness loop. -/
theorem row_instanceOverBracha_callLoop (s : Gather.StateOverBracha P.n X) (id : Fin P.n) (x : X) :
    (Gather.instanceOverBracha P X).step s (Sum.inr (Gather.LoopLabel.callLoop id x))
      (PMF.pure s) := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  refine Gather.instanceOverBroadcasts_label_step (x := v) (w' := y) (a' := a) (b' := b) (by simp)
    (fun i => ?_) (Gather.NetworkStep.callLoop y id x) (fun k => ?_)
    (fun _ => System.mapIdle_unchanged rfl)
  · by_cases hi : i = id
    · subst hi; exact Gather.ProgramStep.callLoop (v i) x
    · exact Gather.ProgramStep.callLoopIdle (v i) id x (Ne.symm hi)
  · by_cases hk : k = id
    · subst hk
      exact System.mapIdle_step_of_step (by simp)
        (Gather.row_brachaInstance_callLoop_step P k (a k) x)
    · exact System.mapIdle_unchanged (by simp [hk])

end GatherRows

/-! ### Building a transition of one round

One row of the round's programs beside one row of a gather instance, at the label the round takes
them on. The three hidden events `firstGatherReturn`, `secondGatherCall` and `secondGatherReturn`
are silent transitions of the round; the call, the call loop and the graded return are transitions
on labels of the family alphabet. -/

section RoundRows

variable {P : Parameters} {r : ℕ}

/-- A silent row of the first gather is a silent transition of the round. -/
theorem roundOverBracha_firstGatherTau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {c : Gather.StateOverBracha P.n Bool}
    (h : Gather.StepOverBracha P (GBCA.ByAFW.firstGather s) Gather.Label.tau (PMF.pure c)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (GBCA.ByAFW.setFirstGather s c)) :=
  GBCA.ByAFW.roundOverGathers_tau_firstGather (row_instanceOverBracha_inl (by simp) h)

/-- A silent row of the second gather is a silent transition of the round. -/
theorem roundOverBracha_secondGatherTau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {d : Gather.StateOverBracha P.n (Option Bool)}
    (h : Gather.StepOverBracha P (GBCA.ByAFW.secondGather s) Gather.Label.tau (PMF.pure d)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau)
    (PMF.pure (GBCA.ByAFW.setSecondGather s d)) :=
  GBCA.ByAFW.roundOverGathers_tau_secondGather (row_instanceOverBracha_inl (by simp) h)

/-- **The round's call**: the program records the input and the first gather
takes its call. -/
theorem roundOverBracha_callG (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n) (b : Bool)
    (h0 : (GBCA.ByAFW.programs s id).input = none)
    (hg : ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process id).input = none)
    (hb : ((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) id).process id).input = none) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl (Label.callG r id b))
      (PMF.pure (GBCA.ByAFW.setFirstGather
        (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) id
          { GBCA.ByAFW.programs s id with input := some b }))
        (Gather.setInputBroadcasts
          (Gather.setGatherTier (GBCA.ByAFW.firstGather s) ((Gather.gatherTier
            (GBCA.ByAFW.firstGather s)).setProcess id
            { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process id with input := some b }))
          (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s)) id
            (((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) id).setProcess id
              { (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) id).process id with
                input := some b }).multicast id (.init b)))))) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundOverGathers_label_step (by simp)
    (GBCA.ByAFW.roundPrograms_label_step (lp := .callG r id b) (by simp) (by simp)
      (dirac_steps_update (GBCA.ByAFW.ProgramStep.callG (v id) b h0)
        (fun i hi => GBCA.ByAFW.ProgramStep.callGIdle (v i) id b (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.callG y id b))
    (System.mapIdle_step_of_step (by simp) (row_instanceOverBracha_call c id b hg hb))
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
    (System.mapIdle_step_of_step (by simp) (row_instanceOverBracha_callLoop c id b))
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
    (System.mapIdle_step_of_step (by simp) (row_instanceOverBracha_callLoop c id b))
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
    (h : Gather.StepOverBracha P (GBCA.ByAFW.firstGather s) (.ret id g (firstGatherReturnCore P s))
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
    (System.mapIdle_step_of_step (by simp) (row_instanceOverBracha_inl (by simp) h))
    (System.mapIdle_unchanged (by simp))

/-- **The second gather's call**: the program marks the call and the second
gather takes its call. -/
theorem roundOverBracha_secondGatherCall (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (x : Option Bool) (hc : (GBCA.ByAFW.programs s id).candidate = some x)
    (h2 : (GBCA.ByAFW.programs s id).secondGatherCalled = false)
    (hg : ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process id).input = none)
    (hb : ((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) id).process id).input = none) :
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
    (System.mapIdle_step_of_step (by simp) (row_instanceOverBracha_call d id x hg hb))

/-- **The second gather's return**: the program records the grade and the
second gather takes its return. -/
theorem roundOverBracha_secondGatherReturn (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) (h2 : (GBCA.ByAFW.programs s id).secondGatherCalled = true)
    (ho : (GBCA.ByAFW.programs s id).output = none)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.secondGather s)
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
    (System.mapIdle_step_of_step (by simp) (row_instanceOverBracha_inl (by simp) h))

/-- **The round's graded return**: the program announces the grade it holds and
marks the record returned, and the bit the label carries is the one on
record. -/
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

/-! ### Runs of one round -/

/-- One silent transition of the round is a silent run. -/
theorem roundOverBracha_run_one {q q' : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent q q' :=
  System.weakLSilent_stepCons (by rw [extendedLabel_tau]; exact h) (by simp)
    (System.weakLSilent_refl _ q')

/-- Two silent transitions of the round are a silent run. -/
theorem roundOverBracha_run_two {q q₁ q' : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h₁ : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q₁))
    (h₂ : (GBCA.ByAFW.roundOverBracha P r).step q₁ (Sum.inl Label.tau) (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent q q' :=
  System.weakLSilent_stepCons (by rw [extendedLabel_tau]; exact h₁) (by simp)
    (roundOverBracha_run_one h₂)

/-- A silent transition followed by a visible one is a weak transition of the
round on that label. -/
theorem roundOverBracha_weakStep_two {L : ExtendedLabel P.n}
    {q q₁ q' : GBCA.ByAFW.RoundStateOverBracha P.n} (hL : L ≠ Silent.τ)
    (h₁ : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q₁))
    (h₂ : (GBCA.ByAFW.roundOverBracha P r).step q₁ L (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLStep q L q' :=
  System.weakLStep_stepCons (by rw [extendedLabel_tau]; exact h₁) (by simp)
    (System.weakLStep_of_step hL h₂)

end RoundRows

/-! ### The broadcast invariant across a row

`BroadcastReturnsInvariant` is the broadcast invariant at the `4n` instances of every round.
`RoundInvariant` is that clause at one round, `broadcastReturnsInvariant_update` carries it across a
row from the round the row names, and `roundInvariant_firstGather`, `roundInvariant_secondGather`
and `roundInvariant_of_unchanged` re-establish it from the rows the composed answer fires. -/

section Invariant

variable {P : Parameters}

/-- **The broadcast invariant at the `4n` instances of one round.** -/
def RoundInvariant (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) : Prop :=
  ∀ k : Fin P.n, BRB.Invariant P k (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) k) ∧
    BRB.Invariant P k (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) k) ∧
    BRB.Invariant P k (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) k) ∧
    BRB.Invariant P k (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) k)

/-- `BroadcastReturnsInvariant` is `RoundInvariant` at every round of the view. -/
theorem broadcastReturnsInvariant_iff_roundInvariant (u : ∀ _ : Fin P.n,
    AFW.ProcessRecord P.n) (w : NetworkState P.n) : BroadcastReturnsInvariant P u w ↔ ∀ r,
      RoundInvariant P (roundProjection P u w r) := Iff.rfl

/-- **Every row of a gather instance moves each of its `2n` broadcast instances
by one row or not at all.** -/
theorem stepOverBracha_invariantStep {X : Type} [DecidableEq X] {s : Gather.StateOverBracha P.n X}
    {l₀ : Gather.Label P.n X} {μ : PMF (Gather.StateOverBracha P.n X)}
    (h : Gather.StepOverBracha P s l₀ μ) {s' : Gather.StateOverBracha P.n X}
    (hs' : s' ∈ μ.support) (k : Fin P.n) :
    InvariantStep P k (Gather.inputBroadcasts s k) (Gather.inputBroadcasts s' k) ∧
      InvariantStep P k (Gather.bindBroadcasts s k) (Gather.bindBroadcasts s' k) := by
  cases h with
  | call id x hin hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨invariantStep_update _ id _ (BRB.BrachaStep.call (Gather.inputBroadcasts s id) x hb) k,
      InvariantStep.unchanged P k _⟩
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, InvariantStep.unchanged P k _⟩
  | inputBroadcastTau q c hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨invariantStep_update _ q c hb k, InvariantStep.unchanged P k _⟩
  | bindBroadcastTau q d hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, invariantStep_update _ q d hb k⟩
  | deliver i q m hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, InvariantStep.unchanged P k _⟩
  | echo q hin hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, InvariantStep.unchanged P k _⟩
  | vote q U hin hech happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, InvariantStep.unchanged P k _⟩
  | bindCall q U hin hvot hsnd happ hQ hbc =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _,
      invariantStep_update _ q _ (BRB.BrachaStep.call (Gather.bindBroadcasts s q) U hbc) k⟩
  | byzantine q m hF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, InvariantStep.unchanged P k _⟩
  | inputBroadcastRet q i v c hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨invariantStep_update _ q c hb k, InvariantStep.unchanged P k _⟩
  | bindRet q i U d hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, invariantStep_update _ q d hb k⟩
  | ret id g hin hbind hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.unchanged P k _, InvariantStep.unchanged P k _⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvariantStep.row (BRB.BrachaStep.fail (Gather.inputBroadcasts s k) id),
      InvariantStep.row (BRB.BrachaStep.fail (Gather.bindBroadcasts s k) id)⟩

variable {s t : GBCA.ByAFW.RoundStateOverBracha P.n}

/-- A row that leaves both gather instances where they stand keeps the
invariant. -/
theorem roundInvariant_of_unchanged (hR : RoundInvariant P s)
    (h1 : GBCA.ByAFW.firstGather t = GBCA.ByAFW.firstGather s)
    (h2 : GBCA.ByAFW.secondGather t = GBCA.ByAFW.secondGather s) : RoundInvariant P t := by
  intro k
  rw [h1, h2]
  exact hR k

/-- A row of the first gather keeps the invariant. -/
theorem roundInvariant_firstGather {l₀ : Gather.Label P.n Bool} (hR : RoundInvariant P s)
    (h2 : GBCA.ByAFW.secondGather t = GBCA.ByAFW.secondGather s)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.firstGather s) l₀ (PMF.pure (GBCA.ByAFW.firstGather
      t))) :
    RoundInvariant P t := by
  intro k
  obtain ⟨h1', h2'⟩ := stepOverBracha_invariantStep h (s' := GBCA.ByAFW.firstGather t) (by simp) k
  rw [h2]
  exact ⟨h1'.invariant (hR k).1, h2'.invariant (hR k).2.1, (hR k).2.2.1, (hR k).2.2.2⟩

/-- A row of the second gather keeps the invariant. -/
theorem roundInvariant_secondGather {l₀ : Gather.Label P.n (Option Bool)} (hR : RoundInvariant P s)
    (h1 : GBCA.ByAFW.firstGather t = GBCA.ByAFW.firstGather s)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.secondGather s) l₀ (PMF.pure (GBCA.ByAFW.secondGather
      t))) :
    RoundInvariant P t := by
  intro k
  obtain ⟨h1', h2'⟩ := stepOverBracha_invariantStep h (s' := GBCA.ByAFW.secondGather t) (by simp) k
  rw [h1]
  exact ⟨(hR k).1, (hR k).2.1, h1'.invariant (hR k).2.2.1, h2'.invariant (hR k).2.2.2⟩

/-- A row that moves both gather instances keeps the invariant. -/
theorem roundInvariant_both {l₁ : Gather.Label P.n Bool} {l₂ : Gather.Label P.n (Option Bool)}
    (hR : RoundInvariant P s)
    (h₁ : Gather.StepOverBracha P (GBCA.ByAFW.firstGather s) l₁ (PMF.pure (GBCA.ByAFW.firstGather
      t)))
    (h₂ : Gather.StepOverBracha P (GBCA.ByAFW.secondGather s) l₂ (PMF.pure (GBCA.ByAFW.secondGather
      t))) :
    RoundInvariant P t := by
  intro k
  obtain ⟨ha, hb⟩ := stepOverBracha_invariantStep h₁ (s' := GBCA.ByAFW.firstGather t) (by simp) k
  obtain ⟨hc, hd⟩ := stepOverBracha_invariantStep h₂ (s' := GBCA.ByAFW.secondGather t) (by simp) k
  exact ⟨ha.invariant (hR k).1, hb.invariant (hR k).2.1, hc.invariant (hR k).2.2.1,
    hd.invariant (hR k).2.2.2⟩

/-- The broadcast invariant at one round of the view. -/
theorem roundInvariant_of_broadcastReturnsInvariant {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w : NetworkState P.n} (hI : BroadcastReturnsInvariant P u w) (r : ℕ) :
    RoundInvariant P (roundProjection P u w r) :=
      hI r

/-- **The broadcast invariant across a row**: the round the row names carries
it, and every other round is unchanged. -/
theorem broadcastReturnsInvariant_update {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w v : NetworkState P.n} {r : ℕ} {Z : GBCA.ByAFW.RoundStateOverBracha P.n}
    (hI : BroadcastReturnsInvariant P u w)
    (hfam : (fun r' => roundProjection P x v r') = Function.update
      (fun r' => roundProjection P u w r') r Z)
    (hZ : RoundInvariant P Z) : BroadcastReturnsInvariant P x v := by
  intro r' k
  have h : roundProjection P x v r' = Function.update (fun r'' => roundProjection P u w r'') r Z r'
    :=
    congrFun hfam r'
  rw [h]
  by_cases hr : r' = r
  · subst hr
    rw [Function.update_self]
    exact hZ k
  · rw [Function.update_of_ne hr]
    exact hI r' k

end Invariant

/-! ### Corruption, read through the view

Corruption reaches the round through its two gather instances: the corrupted
set the adversary holds is the corrupted set of every network state the view
assembles, and the programs and the round's bound bit are untouched (D1). -/

theorem roundProjection_fail {P : Parameters} (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
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
      simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, roundProjection, firstGatherProjection,
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
      simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, roundProjection,
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
theorem roundProjectionFamily_byzantine {P : Parameters} (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (m : Message P.n) :
    (fun r' => roundProjection P u (w.recordGBCASend r k m) r') = Function.update
    (fun r' => roundProjection P u w r') r (roundProjection P u (w.recordGBCASend r k m) r) := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self]
  · rw [Function.update_of_ne hr]
    simp only [roundProjection, firstGatherProjection, secondGatherProjection,
      recordGBCASend_sent_ne w r k m hr, recordGBCASend_F, recordGBCASend_ghostRecord]

/-- A row that leaves every round record where it stands leaves the whole
family of rounds where it stands. -/
theorem roundProjection_unchanged {P : Parameters} {x u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    (h : ∀ i, (x i).2 = (u i).2) (w : NetworkState P.n) :
    (fun r => roundProjection P u w r) = fun r => roundProjection P x w r := by
  funext r
  exact (roundProjection_congr (fun i => by rw [h i])).symm

/-! ### Answering a send

A send of the implementation is a silent run of the round: the sender writes its own record, the
network records the message, and the round the label tags moves as its own rules move it. The
return-then-call step is the one send answered by two events. -/

theorem roundRecord_answer_gbcaSend (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}
    (hu : (u j).2 = p) (hI : BroadcastReturnsInvariant P u w) {r : ℕ} {m : Message P.n}
    {μ : PMF (AFW.ProcessRecord P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaSend r j m)) μ) :
    ∃ x : AFW.ProcessRecord P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.roundRecord r' = p.roundRecord r') ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j x)
          ((w.recordGBCASend r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j x)
        ((w.recordGBCASend r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) r) := by
  subst hu
  cases h with
  | firstGatherEcho _ _ _ hh hterm hin hcard hsend =>
    have hacc : ((Gather.gatherTier (firstGatherProjection P u w r)).process j).accepted
        = firstGatherAcceptedPairs P ((u j).2.roundRecord r) := accepted_firstGatherProjection u w r
          j
    have hrow := Gather.StepOverBracha.echo (firstGatherProjection P u w r) j hin
      (by rw [hacc]; exact hcard) hsend
    rw [hacc] at hrow
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherEcho rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherVote _ _ _ U hh hterm hin hech happ hQ hsend =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A,
          Gather.Message.echo A ∈ (Gather.gatherTier (firstGatherProjection P u w r)).received j q ∧
            Gather.approvedBy ((Gather.gatherTier (firstGatherProjection P u w r)).process j) A ∧ A
              ⊆
            U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨A, hA1, hA2, hA3⟩ := hmem q hq
      exact ⟨A, hA1, fun z hz => holdsInputBroadcastReturn_firstGather hI r j z.1 (hA2 z hz), hA3⟩
    have hrow := Gather.StepOverBracha.vote (firstGatherProjection P u w r) j U hin hech
      (fun q hq => holdsInputBroadcastReturn_firstGather hI r j q.1 (happ q hq)) hQ' hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherBind _ _ _ U hh hterm hin hvot hsnd hbc happ hQ =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Gather.Message.vote W ∈ (Gather.gatherTier (firstGatherProjection P u w r)).received j q ∧
            Gather.approvedBy ((Gather.gatherTier (firstGatherProjection P u w r)).process j) W ∧ W
              ⊆
            U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨W, hW1, hW2, hW3⟩ := hmem q hq
      exact ⟨W, hW1, fun z hz => holdsInputBroadcastReturn_firstGather hI r j z.1 (hW2 z hz), hW3⟩
    have hrow := Gather.StepOverBracha.bindCall (firstGatherProjection P u w r) j U hin hvot hsnd
      (fun q hq => holdsInputBroadcastReturn_firstGather hI r j q.1 (happ q hq)) hQ' hbc
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherBind rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherEcho _ _ _ hh hterm hin hcard hsend =>
    have hacc : ((Gather.gatherTier (secondGatherProjection P u w r)).process j).accepted
        = secondGatherAcceptedPairs P ((u j).2.roundRecord r) := accepted_secondGatherProjection u w
          r j
    have hrow := Gather.StepOverBracha.echo (secondGatherProjection P u w r) j hin
      (by rw [hacc]; exact hcard) hsend
    rw [hacc] at hrow
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherEcho rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherVote _ _ _ U hh hterm hin hech happ hQ hsend =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A,
          Gather.Message.echo A ∈ (Gather.gatherTier (secondGatherProjection P u w r)).received j q
            ∧ Gather.approvedBy ((Gather.gatherTier (secondGatherProjection P u w r)).process j) A ∧
              A ⊆
            U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨A, hA1, hA2, hA3⟩ := hmem q hq
      exact ⟨A, hA1, fun z hz => holdsInputBroadcastReturn_secondGather hI r j z.1 (hA2 z hz), hA3⟩
    have hrow := Gather.StepOverBracha.vote (secondGatherProjection P u w r) j U hin hech
      (fun q hq => holdsInputBroadcastReturn_secondGather hI r j q.1 (happ q hq)) hQ' hsend
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherBind _ _ _ U hh hterm hin hvot hsnd hbc happ hQ =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Gather.Message.vote W ∈ (Gather.gatherTier (secondGatherProjection P u w r)).received j q
            ∧ Gather.approvedBy ((Gather.gatherTier (secondGatherProjection P u w r)).process j) W ∧
              W ⊆
            U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨W, hW1, hW2, hW3⟩ := hmem q hq
      exact ⟨W, hW1, fun z hz => holdsInputBroadcastReturn_secondGather hI r j z.1 (hW2 z hz), hW3⟩
    have hrow := Gather.StepOverBracha.bindCall (secondGatherProjection P u w r) j U hin hvot hsnd
      (fun q hq => holdsInputBroadcastReturn_secondGather hI r j q.1 (happ q hq)) hQ' hbc
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherBind rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherReturnThenSecondGatherCall _ _ _ g hh hterm hin hbind hsubap hQ hr1 hin2 hbin2 =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          Gather.holdsBindBroadcastReturn ((Gather.gatherTier (firstGatherProjection P u w
            r)).process j) q U ∧ Gather.AcceptedPairs.subMap U g := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨U, hU1, hU2⟩ := hmem q hq
      exact ⟨U, holdsBindBroadcastReturn_firstGather hI r j q hU1, hU2⟩
    have hrow1 : Gather.StepOverBracha P (GBCA.ByAFW.firstGather (roundProjection P u w r))
        (.ret j g (firstGatherReturnCore P (roundProjection P u w r)))
        (PMF.pure (GBCA.ByAFW.firstGather (afterFirstGatherReturn P (roundProjection P u w r) j g)))
          :=
      Gather.StepOverBracha.ret _ j g hin hbind
        (fun k x hx => holdsInputBroadcastReturn_firstGather hI r j k (hsubap k x hx)) hQ' hr1
    have hrow2 : Gather.StepOverBracha P (GBCA.ByAFW.secondGather (afterFirstGatherReturn P
      (roundProjection P u w r) j g))
        (.call j (GBCA.candidate P g))
        (PMF.pure (GBCA.ByAFW.secondGather (afterSecondGatherCall P (afterFirstGatherReturn P
          (roundProjection P u w r) j g) j
          (GBCA.candidate P g)))) :=
      Gather.StepOverBracha.call _ j (GBCA.candidate P g) hin2 hbin2
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherReturn_secondGatherCall rfl]
    · exact roundOverBracha_run_two
        (roundOverBracha_firstGatherReturn (roundProjection P u w r) j g hin hin2 hrow1)
        (roundOverBracha_secondGatherCall (afterFirstGatherReturn P (roundProjection P u w r) j g) j
          (GBCA.candidate P g)
          (by simp [afterFirstGatherReturn]) (by simp [afterFirstGatherReturn, programProjection,
            hin2]) hin2 hbin2)
    · have hR1 : RoundInvariant P (afterFirstGatherReturn P (roundProjection P u w r) j g) :=
        roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow1
      exact roundInvariant_secondGather hR1 rfl hrow2
  | firstGatherInputBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.echo (Gather.inputBroadcasts (firstGatherProjection P u w r) i) j mm hrecv
        hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherInputBroadcastEcho rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherInputBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.inputBroadcasts (firstGatherProjection P u w r) i) j mm
        hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherInputBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherInputBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.voteAmplification (Gather.inputBroadcasts (firstGatherProjection P u w r) i) j
        mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherInputBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherBindBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.echo (Gather.bindBroadcasts (firstGatherProjection P u w r) i) j mm hrecv
        hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherBindBroadcastEcho rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherBindBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.bindBroadcasts (firstGatherProjection P u w r) i) j mm hcnt
        hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherBindBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | firstGatherBindBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.voteAmplification (Gather.bindBroadcasts (firstGatherProjection P u w r) i) j
        mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_firstGatherBindBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherInputBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.echo (Gather.inputBroadcasts (secondGatherProjection P u w r) i) j mm hrecv
        hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherInputBroadcastEcho rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherInputBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.inputBroadcasts (secondGatherProjection P u w r) i) j mm
        hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherInputBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherInputBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.voteAmplification (Gather.inputBroadcasts (secondGatherProjection P u w r) i)
        j mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherInputBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherBindBroadcastEcho _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.echo (Gather.bindBroadcasts (secondGatherProjection P u w r) i) j mm hrecv
        hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherBindBroadcastEcho rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherBindBroadcastVoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.bindBroadcasts (secondGatherProjection P u w r) i) j mm
        hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherBindBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
  | secondGatherBindBroadcastVoteAmplification _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.voteAmplification (Gather.bindBroadcasts (secondGatherProjection P u w r) i) j
        mm hcnt hsend)
    refine ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', ?_,
        ?_⟩ <;> rw [roundProjection_secondGatherBindBroadcastVote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow)
    · exact roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow


/-! ### Answering a delivery

A delivery of the implementation files the message in the receiver's own local
state of the network state the message's tag names. A gather message moves the
gather instance alone. A broadcast message moves the broadcast instance, and,
where it completes the receiver's `2f + 1` `VOTE` quorum, the instance returns
to the receiver as well, which is a second transition of the round. -/

/-- A delivery in an input-broadcast instance of the first gather, answered -/
theorem answer_deliverFirstGatherInputBroadcast (P : Parameters)
    {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} (w : NetworkState P.n) {j : Fin P.n}
    {c : RoundLoopRecord P.n} (hI : BroadcastReturnsInvariant P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message Bool) (hsent : Message.firstGatherInputBroadcasts i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j (c,
          (u j).2.deliverTo r k (.firstGatherInputBroadcasts i mm))) (w.writeGhost (ghostStep P)
            (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm)))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j (c,
        (u j).2.deliverTo r k (.firstGatherInputBroadcasts i mm))) (w.writeGhost (ghostStep P)
          (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.inputBroadcasts (firstGatherProjection P u w r) i) .tau
      (PMF.pure ((Gather.inputBroadcasts (firstGatherProjection P u w r) i).receiveMessage j k mm))
        :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_messagesOf (hf := firstGatherInputBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
        by simp [firstGatherInputBroadcastMessageOf]⟩)
  have hrow₁ := Gather.StepOverBracha.inputBroadcastTau (firstGatherProjection P u w r) i _ hdlv
  have hInv' : BRB.Invariant P i ((Gather.inputBroadcasts (firstGatherProjection P u w r)
    i).receiveMessage j k mm) :=
    (InvariantStep.row hdlv).invariant (roundInvariant_of_broadcastReturnsInvariant hI r i).1
  have hR₁ : RoundInvariant P (afterFirstGatherInputBroadcastDeliver P (roundProjection P u w r) i j
    k mm)
    :=
    roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow₁
  rcases broadcastReturnsFor_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v,
    hst⟩
  · rw [roundProjection_deliverFirstGatherInputBroadcast rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow₁),
      hR₁⟩
  · have hr₀ : ((Gather.inputBroadcasts (firstGatherProjection P u w r) i).process j).returned =
      false := by
      change (broadcastReturnsFor P ((Gather.inputBroadcasts (firstGatherProjection P u w r) i).1
        j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.inputBroadcasts (GBCA.ByAFW.firstGather (afterFirstGatherInputBroadcastDeliver
      P (roundProjection P u w r) i j k mm)) i
        = (Gather.inputBroadcasts (firstGatherProjection P u w r) i).receiveMessage j k mm := by
      simp [afterFirstGatherInputBroadcastDeliver]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.firstGather (afterFirstGatherInputBroadcastDeliver P (roundProjection P u w r) i
          j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.firstGather (afterFirstGatherInputBroadcastReturn P
          (afterFirstGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm) i j v))) :=
            by
      refine Gather.StepOverBracha.inputBroadcastRet _ i j v _ ?_
      rw [hbi]
      exact brachaStep_ret_of_broadcastReturn hr₀ hst
    rw [roundProjection_deliverFirstGatherInputBroadcast_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow₁)
        (roundOverBracha_firstGatherTau (afterFirstGatherInputBroadcastDeliver P (roundProjection P
          u w r) i j k mm) hrow₂),
      roundInvariant_firstGather hR₁ rfl hrow₂⟩

/-- A delivery in a bind-broadcast instance of the first gather, answered -/
theorem answer_deliverFirstGatherBindBroadcast (P : Parameters)
    {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} (w : NetworkState P.n) {j : Fin P.n}
    {c : RoundLoopRecord P.n} (hI : BroadcastReturnsInvariant P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n Bool))
    (hsent : Message.firstGatherBindBroadcasts i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j (c,
          (u j).2.deliverTo r k (.firstGatherBindBroadcasts i mm))) (w.writeGhost (ghostStep P)
            (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm)))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j (c,
        (u j).2.deliverTo r k (.firstGatherBindBroadcasts i mm))) (w.writeGhost (ghostStep P)
          (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.bindBroadcasts (firstGatherProjection P u w r) i) .tau
      (PMF.pure ((Gather.bindBroadcasts (firstGatherProjection P u w r) i).receiveMessage j k mm))
        :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_messagesOf (hf := firstGatherBindBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
        by simp [firstGatherBindBroadcastMessageOf]⟩)
  have hrow₁ := Gather.StepOverBracha.bindBroadcastTau (firstGatherProjection P u w r) i _ hdlv
  have hInv' : BRB.Invariant P i ((Gather.bindBroadcasts (firstGatherProjection P u w r)
    i).receiveMessage
    j k mm) :=
    (InvariantStep.row hdlv).invariant (roundInvariant_of_broadcastReturnsInvariant hI r i).2.1
  have hR₁ : RoundInvariant P (afterFirstGatherBindBroadcastDeliver P (roundProjection P u w r) i j
    k mm)
    :=
    roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow₁
  rcases broadcastReturnsFor_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v,
    hst⟩
  · rw [roundProjection_deliverFirstGatherBindBroadcast rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow₁),
      hR₁⟩
  · have hr₀ : ((Gather.bindBroadcasts (firstGatherProjection P u w r) i).process j).returned =
      false := by
      change (broadcastReturnsFor P ((Gather.bindBroadcasts (firstGatherProjection P u w r) i).1
        j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.bindBroadcasts (GBCA.ByAFW.firstGather (afterFirstGatherBindBroadcastDeliver P
      (roundProjection P u w r) i j k mm)) i
        = (Gather.bindBroadcasts (firstGatherProjection P u w r) i).receiveMessage j k mm := by
      simp [afterFirstGatherBindBroadcastDeliver]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.firstGather (afterFirstGatherBindBroadcastDeliver P (roundProjection P u w r) i
          j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.firstGather (afterFirstGatherBindBroadcastReturn P
          (afterFirstGatherBindBroadcastDeliver P (roundProjection P u w r) i j k mm) i j v))) := by
      refine Gather.StepOverBracha.bindRet _ i j v _ ?_
      rw [hbi]
      exact brachaStep_ret_of_broadcastReturn hr₀ hst
    rw [roundProjection_deliverFirstGatherBindBroadcast_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_firstGatherTau (roundProjection P u w r) hrow₁)
        (roundOverBracha_firstGatherTau (afterFirstGatherBindBroadcastDeliver P (roundProjection P u
          w r) i j k mm) hrow₂),
      roundInvariant_firstGather hR₁ rfl hrow₂⟩

/-- A delivery in an input-broadcast instance of the second gather, answered -/
theorem answer_deliverSecondGatherInputBroadcast (P : Parameters)
    {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} (w : NetworkState P.n) {j : Fin P.n}
    {c : RoundLoopRecord P.n} (hI : BroadcastReturnsInvariant P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Option Bool))
    (hsent : Message.secondGatherInputBroadcasts i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j (c,
          (u j).2.deliverTo r k (.secondGatherInputBroadcasts i mm))) (w.writeGhost (ghostStep P)
            (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j (c,
        (u j).2.deliverTo r k (.secondGatherInputBroadcasts i mm))) (w.writeGhost (ghostStep P)
          (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.inputBroadcasts (secondGatherProjection P u w r) i) .tau
      (PMF.pure ((Gather.inputBroadcasts (secondGatherProjection P u w r) i).receiveMessage j k mm))
        :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_messagesOf (hf := secondGatherInputBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
        by simp [secondGatherInputBroadcastMessageOf]⟩)
  have hrow₁ := Gather.StepOverBracha.inputBroadcastTau (secondGatherProjection P u w r) i _ hdlv
  have hInv' : BRB.Invariant P i ((Gather.inputBroadcasts (secondGatherProjection P u w r)
    i).receiveMessage j k mm) :=
    (InvariantStep.row hdlv).invariant (roundInvariant_of_broadcastReturnsInvariant hI r i).2.2.1
  have hR₁ : RoundInvariant P (afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r) i
    j k
    mm) :=
    roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow₁
  rcases broadcastReturnsFor_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v,
    hst⟩
  · rw [roundProjection_deliverSecondGatherInputBroadcast rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
      hrow₁), hR₁⟩
  · have hr₀ : ((Gather.inputBroadcasts (secondGatherProjection P u w r) i).process j).returned =
      false := by
      change (broadcastReturnsFor P ((Gather.inputBroadcasts (secondGatherProjection P u w r) i).1
        j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.inputBroadcasts (GBCA.ByAFW.secondGather
      (afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm)) i
        = (Gather.inputBroadcasts (secondGatherProjection P u w r) i).receiveMessage j k mm := by
      simp [afterSecondGatherInputBroadcastDeliver]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.secondGather (afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r)
          i j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.secondGather (afterSecondGatherInputBroadcastReturn P
          (afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm) i j v))) :=
            by
      refine Gather.StepOverBracha.inputBroadcastRet _ i j v _ ?_
      rw [hbi]
      exact brachaStep_ret_of_broadcastReturn hr₀ hst
    rw [roundProjection_deliverSecondGatherInputBroadcast_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow₁)
        (roundOverBracha_secondGatherTau (afterSecondGatherInputBroadcastDeliver P (roundProjection
          P u w r) i j k mm) hrow₂),
      roundInvariant_secondGather hR₁ rfl hrow₂⟩

/-- A delivery in a bind-broadcast instance of the second gather, answered -/
theorem answer_deliverSecondGatherBindBroadcast (P : Parameters)
    {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} (w : NetworkState P.n) {j : Fin P.n}
    {c : RoundLoopRecord P.n} (hI : BroadcastReturnsInvariant P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n (Option Bool)))
    (hsent : Message.secondGatherBindBroadcasts i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j (c,
          (u j).2.deliverTo r k (.secondGatherBindBroadcasts i mm))) (w.writeGhost (ghostStep P)
            (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm)))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j (c,
        (u j).2.deliverTo r k (.secondGatherBindBroadcasts i mm))) (w.writeGhost (ghostStep P)
          (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.bindBroadcasts (secondGatherProjection P u w r) i) .tau
      (PMF.pure ((Gather.bindBroadcasts (secondGatherProjection P u w r) i).receiveMessage j k mm))
        :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_messagesOf (hf := secondGatherBindBroadcastMessageOf_inj i)).mpr ⟨_, hsent,
        by simp [secondGatherBindBroadcastMessageOf]⟩)
  have hrow₁ := Gather.StepOverBracha.bindBroadcastTau (secondGatherProjection P u w r) i _ hdlv
  have hInv' : BRB.Invariant P i ((Gather.bindBroadcasts (secondGatherProjection P u w r)
    i).receiveMessage j k mm) :=
    (InvariantStep.row hdlv).invariant (roundInvariant_of_broadcastReturnsInvariant hI r i).2.2.2
  have hR₁ : RoundInvariant P (afterSecondGatherBindBroadcastDeliver P (roundProjection P u w r) i j
    k mm)
    :=
    roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow₁
  rcases broadcastReturnsFor_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v,
    hst⟩
  · rw [roundProjection_deliverSecondGatherBindBroadcast rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
      hrow₁), hR₁⟩
  · have hr₀ : ((Gather.bindBroadcasts (secondGatherProjection P u w r) i).process j).returned =
      false := by
      change (broadcastReturnsFor P ((Gather.bindBroadcasts (secondGatherProjection P u w r) i).1
        j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.bindBroadcasts (GBCA.ByAFW.secondGather (afterSecondGatherBindBroadcastDeliver
      P (roundProjection P u w r) i j k mm)) i
        = (Gather.bindBroadcasts (secondGatherProjection P u w r) i).receiveMessage j k mm := by
      simp [afterSecondGatherBindBroadcastDeliver]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.secondGather (afterSecondGatherBindBroadcastDeliver P (roundProjection P u w r)
          i j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.secondGather (afterSecondGatherBindBroadcastReturn P
          (afterSecondGatherBindBroadcastDeliver P (roundProjection P u w r) i j k mm) i j v))) :=
            by
      refine Gather.StepOverBracha.bindRet _ i j v _ ?_
      rw [hbi]
      exact brachaStep_ret_of_broadcastReturn hr₀ hst
    rw [roundProjection_deliverSecondGatherBindBroadcast_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_secondGatherTau (roundProjection P u w r) hrow₁)
        (roundOverBracha_secondGatherTau (afterSecondGatherBindBroadcastDeliver P (roundProjection P
          u w r) i j k mm) hrow₂),
      roundInvariant_secondGather hR₁ rfl hrow₂⟩

theorem roundRecord_answer_gbcaDeliver (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}
    (hu : (u j).2 = p) (hI : BroadcastReturnsInvariant P u w) {r : ℕ} {k : Fin P.n}
    {m : Message P.n} {μ : PMF (AFW.ProcessRecord P.n)} (hsent : m ∈ w.sent r k)
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m)) μ) :
    ∃ x : AFW.ProcessRecord P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.roundRecord r' = p.roundRecord r') ∧
      (∀ r',
        ((x.2.roundRecord r').secondGather.process).input = ((p.roundRecord
          r').secondGather.process).input) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
        (roundProjection P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j x)
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) := by
  subst hu
  cases h with
  | gbcaDeliverReceive _ _ _ _ _ hh hterm =>
    have hga2 : ∀ r', ((((u j).2.deliverTo r k m).roundRecord r').secondGather.process).input
        = (((u j).2.roundRecord r').secondGather.process).input := by
      intro r'
      by_cases hr' : r' = r
      · subst hr'
        simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo,
          RoundRecord.deliverTo, Implementation.RoundRecordMap.roundRecord_setRoundRecord_self]
        cases m <;> simp [LocalState.deliverTo]
      · rw [Implementation.RoundRecordMap.deliverTo,
          Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
    obtain ⟨hrun, hinv⟩ :
        (GBCA.ByAFW.roundOverBracha P r).weakLSilent (roundProjection P u w r)
            (roundProjection P (Function.update u j (c, (u j).2.deliverTo r k m))
              (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) ∧
          RoundInvariant P (roundProjection P (Function.update u j (c, (u j).2.deliverTo r k m))
            (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) := by
      cases m with
      | firstGather mm =>
        have hrow := Gather.StepOverBracha.deliver (firstGatherProjection P u w r) j k mm
          ((mem_messagesOf (hf := firstGatherMessageOf_inj)).mpr ⟨_, hsent, rfl⟩)
        rw [roundProjection_deliverFirstGather rfl]
        exact ⟨roundOverBracha_run_one (roundOverBracha_firstGatherTau (roundProjection P u w r)
          hrow),
          roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
      | secondGather mm =>
        have hrow := Gather.StepOverBracha.deliver (secondGatherProjection P u w r) j k mm
          ((mem_messagesOf (hf := secondGatherMessageOf_inj)).mpr ⟨_, hsent, rfl⟩)
        rw [roundProjection_deliverSecondGather rfl]
        exact ⟨roundOverBracha_run_one (roundOverBracha_secondGatherTau (roundProjection P u w r)
          hrow),
          roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
      | firstGatherInputBroadcasts i mm =>
        exact answer_deliverFirstGatherInputBroadcast P w hI r i k mm hsent
      | firstGatherBindBroadcasts i mm =>
        exact answer_deliverFirstGatherBindBroadcast P w hI r i k mm hsent
      | secondGatherInputBroadcasts i mm =>
        exact answer_deliverSecondGatherInputBroadcast P w hI r i k mm hsent
      | secondGatherBindBroadcasts i mm =>
        exact answer_deliverSecondGatherBindBroadcast P w hI r i k mm hsent
    exact ⟨_, rfl, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr', hga2,
        hrun, hinv⟩


/-! ### Answering the call, the graded return and the call loop -/

/-- The graded-agreement call of the implementation is the round's own call. -/
theorem roundRecord_answer_callG (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}
    (hu : (u j).2 = p) (hI : BroadcastReturnsInvariant P u w) {r : ℕ} {b : Bool}
    {μ : PMF (AFW.ProcessRecord P.n)}
    (h : RoundStep P j (c, p) (Sum.inl (.callG r j b)) μ) :
    ∃ x : AFW.ProcessRecord P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.process.phase = .toCallG ∧ c.process.round = r ∧
      c.process.estimate = some b ∧
      x.1 = c.setProcess { c.process with phase := .awaitG } ∧
      (∀ r', r' ≠ r → x.2.roundRecord r' = p.roundRecord r') ∧
      (∀ r',
        ((x.2.roundRecord r').secondGather.process).input = ((p.roundRecord
          r').secondGather.process).input) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (roundProjection P u w r) (Sum.inl (.callG r j b))
        (roundProjection P (Function.update u j x)
          ((w.recordGBCASend r j (gbcaCallPayload P j b)).writeGhost (ghostStep P)
            (Sum.inl (.callG r j b))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j x)
        ((w.recordGBCASend r j (gbcaCallPayload P j b)).writeGhost (ghostStep P)
          (Sum.inl (.callG r j b))) r) := by
  subst hu
  cases h with
  | callG _ _ _ _ hh hph hr hterm hest hin hbin =>
    have hrow := Gather.StepOverBracha.call (firstGatherProjection P u w r) j b hin hbin
    refine ⟨_, rfl, hh, hph, hr, hest, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr',
        fun r' => ?_, ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp
      · rw [Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
    · rw [gbcaCallPayload, roundProjection_callG rfl]
      exact System.weakLStep_of_step (by simp)
        (roundOverBracha_callG (roundProjection P u w r) j b hin hin hbin)
    · rw [gbcaCallPayload, roundProjection_callG rfl]
      exact roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow

/-- The graded-agreement return of the implementation is the second gather's
return followed by the round's own return, the grade read off the second
gather's output. -/
theorem roundRecord_answer_retG (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}
    (hu : (u j).2 = p) (hI : BroadcastReturnsInvariant P u w) {r : ℕ} {out : GBCAOutput}
    {bnd : Bool} {μ : PMF (AFW.ProcessRecord P.n)} (hbnd : bnd = ghostOutput P w r j out)
    (hset : ∀ i, (((u i).2.roundRecord r).secondGather.process).input ≠ none →
      (w.ghostRecord r).2.2 ≠ none)
    (h : RoundStep P j (c, p) (Sum.inl (.retG r j out bnd)) μ) :
    ∃ x : AFW.ProcessRecord P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.process.phase = .awaitG ∧ c.process.round = r ∧
      x.1 = c.setProcess { c.process with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW } ∧
      (∀ r', r' ≠ r → x.2.roundRecord r' = p.roundRecord r') ∧
      (∀ r',
        ((x.2.roundRecord r').secondGather.process).input = ((p.roundRecord
          r').secondGather.process).input) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (roundProjection P u w r) (Sum.inl (.retG r j out
        bnd))
        (roundProjection P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out bnd))) r) ∧
      RoundInvariant P (roundProjection P (Function.update u j x)
        (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out bnd))) r) := by
  subst hu
  cases h with
  | retG _ _ _ g _ hh hph hr hterm hin hbind hsubap hQ hr2 =>
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (hset j hin)
    have hb : bnd = (GBCA.ByAFW.bound (roundProjection P u w r)).getD (GBCA.boundOfCore P ∅) := by
      rw [hbnd]
      unfold ghostOutput
      simp only [bound_roundProjection, hβ, Option.getD_some]
    subst hb
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          Gather.holdsBindBroadcastReturn ((Gather.gatherTier (secondGatherProjection P u w
            r)).process j) q U ∧ Gather.AcceptedPairs.subMap U g := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨U, hU1, hU2⟩ := hmem q hq
      exact ⟨U, holdsBindBroadcastReturn_secondGather hI r j q hU1, hU2⟩
    have hrow : Gather.StepOverBracha P (GBCA.ByAFW.secondGather (roundProjection P u w r))
        (.ret j g (secondGatherReturnCore P (roundProjection P u w r)))
        (PMF.pure (GBCA.ByAFW.secondGather (afterSecondGatherReturn P (roundProjection P u w r) j
          g))) :=
      Gather.StepOverBracha.ret _ j g hin hbind
        (fun k x hx => holdsInputBroadcastReturn_secondGather hI r j k (hsubap k x hx)) hQ' hr2
    refine ⟨_, rfl, hh, hph, hr, rfl,
      fun r' hr' => Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr',
        fun r' => ?_, ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp [LocalState.setProcess]
      · rw [Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
    · rw [roundProjection_secondGatherReturn_retG rfl]
      have hprocs : GBCA.ByAFW.programs (afterSecondGatherReturn P (roundProjection P u w r) j g) j
          = { GBCA.ByAFW.programs (roundProjection P u w r) j with output := some (GBCA.gradeOf P g)
            }
            := by
        simp [afterSecondGatherReturn]
      refine roundOverBracha_weakStep_two (by simp)
        (roundOverBracha_secondGatherReturn (roundProjection P u w r) j g ?_ rfl hrow)
        (roundOverBracha_retG (afterSecondGatherReturn P (roundProjection P u w r) j g) j
          (GBCA.gradeOf P g)
          (by rw [hprocs]) (by rw [hprocs]; exact hr2))
      change (((u j).2.roundRecord r).secondGather.process).input.isSome = true
      exact Option.isSome_iff_ne_none.mpr hin
    · rw [roundProjection_secondGatherReturn_retG rfl]
      have hR₂ : RoundInvariant P (afterSecondGatherReturn P (roundProjection P u w r) j g) :=
        roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow
      exact roundInvariant_of_unchanged hR₂ rfl rfl

/-- The call against an already-called record: the round loop moves, the round
takes its input-enabledness loop and the view is unchanged. -/
theorem roundRecord_answer_gbcaCallLoop (P : Parameters) {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    (w : NetworkState P.n) {j : Fin P.n} {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}
    (hu : (u j).2 = p) {r : ℕ} {b : Bool} {μ : PMF (AFW.ProcessRecord P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaCallLoop r j b)) μ) :
    ∃ x : AFW.ProcessRecord P.n, μ = PMF.pure x ∧ x.2 = p ∧
      c.corrupted = false ∧ c.process.phase = .toCallG ∧ c.process.round = r ∧
      c.process.estimate = some b ∧
      x.1 = c.setProcess { c.process with phase := .awaitG } ∧
      (GBCA.ByAFW.roundOverBracha P r).step (roundProjection P u w r) (Sum.inr (.gbcaCallLoop r j
        b))
        (PMF.pure (roundProjection P u w r)) := by
  subst hu
  cases h with
  | gbcaCallLoop _ _ _ _ hh hph hr hest hin =>
    exact ⟨_, rfl, rfl, hh, hph, hr, hest, rfl,
      roundOverBracha_callLoop (roundProjection P u w r) j b⟩

/-! ### Answering a Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the network state its tag names and no record moves. -/

theorem byzantine_answer (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (hI : BroadcastReturnsInvariant P u w) (r : ℕ) {k : Fin P.n}
    (m : Message P.n) (hF : k ∈ w.F) :
    (GBCA.ByAFW.roundOverBracha P r).step (roundProjection P u w r) (Sum.inl Label.tau)
    (PMF.pure (roundProjection P u (w.recordGBCASend r k m) r)) ∧ RoundInvariant P
    (roundProjection P u (w.recordGBCASend r k m) r) := by
  cases m with
  | firstGather mm =>
    have hrow := Gather.StepOverBracha.byzantine (firstGatherProjection P u w r) k mm hF
    rw [roundProjection_byzantineFirstGather]
    exact ⟨roundOverBracha_firstGatherTau (roundProjection P u w r) hrow,
      roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
  | secondGather mm =>
    have hrow := Gather.StepOverBracha.byzantine (secondGatherProjection P u w r) k mm hF
    rw [roundProjection_byzantineSecondGather]
    exact ⟨roundOverBracha_secondGatherTau (roundProjection P u w r) hrow,
      roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
  | firstGatherInputBroadcasts i mm =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.inputBroadcasts (firstGatherProjection P u w r) i) k mm hF)
    rw [roundProjection_byzantineFirstGatherInputBroadcast]
    exact ⟨roundOverBracha_firstGatherTau (roundProjection P u w r) hrow,
      roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
  | firstGatherBindBroadcasts i mm =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (firstGatherProjection P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.bindBroadcasts (firstGatherProjection P u w r) i) k mm hF)
    rw [roundProjection_byzantineFirstGatherBindBroadcast]
    exact ⟨roundOverBracha_firstGatherTau (roundProjection P u w r) hrow,
      roundInvariant_firstGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
  | secondGatherInputBroadcasts i mm =>
    have hrow := Gather.StepOverBracha.inputBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.inputBroadcasts (secondGatherProjection P u w r) i) k mm hF)
    rw [roundProjection_byzantineSecondGatherInputBroadcast]
    exact ⟨roundOverBracha_secondGatherTau (roundProjection P u w r) hrow,
      roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩
  | secondGatherBindBroadcasts i mm =>
    have hrow := Gather.StepOverBracha.bindBroadcastTau (secondGatherProjection P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.bindBroadcasts (secondGatherProjection P u w r) i) k mm hF)
    rw [roundProjection_byzantineSecondGatherBindBroadcast]
    exact ⟨roundOverBracha_secondGatherTau (roundProjection P u w r) hrow,
      roundInvariant_secondGather (roundInvariant_of_broadcastReturnsInvariant hI r) rfl hrow⟩

end AFW

end ABA
end PLTS
