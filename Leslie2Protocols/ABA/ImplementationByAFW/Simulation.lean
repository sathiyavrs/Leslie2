/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjectionStep

/-!
# The gather-based protocol into its composed reading

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed
P` reads the same protocol as a composition of components, down to the
broadcast instances. This file carries the first into the second, which is
where the gather-based chain passes from implementation to specification, as
`ABA/ImplementationByABDY/Simulation.lean` does for ABDY22's.

## The relation is a function

`AFW.ProtocolRel` (`ABA/ImplementationByAFW/RoundProjection.lean`) determines the composed state
from the flat one: the round loops and the coin oracle are shared, the ABA-side
network is the DECIDED sets beside the corrupted set, and every round is the
view `AFW.toRound`. `AFW.match_pure` and `AFW.match_prod` are the
two couplings that answer a Dirac outcome and an outcome whose only free
coordinate is the oracle's.

## Three flat rows against two composed events

The composed round is a composition, so a flat row that fuses two of its events
is answered by a run of two transitions and not by one. There are three:

* the link, answered by the hidden events `ret1` and `call2` of round `r`;
* the graded return, answered by the hidden event `ret2` and then the visible
  `retG`;
* a broadcast delivery that completes a `2f + 1` `VOTE` receipt quorum,
  answered by the instance's delivery and then its return.

`AFW.match_group` therefore concludes in a weak run of the composed group,
and `AFW.match_step` carries that run through the sub-protocol hiding with
`weakTau_abstract`, `weakTau_of_weakStep_mem` and `weakStep_abstract`.

## The store against the flat receipt quorum

A gather program of the composed reading holds what each broadcast instance has
returned to it; the flat reading reads a `2f + 1` `VOTE` receipt quorum on the
process's own local state instead. `AFW.storeIn_eq_of_quorum` identifies the
two under `AFW.StoreInv`, and `AFW.holdsIn_ga1` and its three
companions are that identification at the four broadcast families. A delivery
moves the store in one way only: `AFW.storeIn_deliver_cases` says that it
either leaves the store where it stands or fills an empty store, which is the
dichotomy between the plain delivery lemmas of `ABA/ImplementationByAFW/RoundProjectionStep.lean`
and their quorum companions.

## The two clauses that are not readings

`AFW.RoundInv` is `AFW.StoreInv` at one round, and
`AFW.storeInv_update` carries it across a row from the round the row names.
Every row of a gather instance moves each of its `2n` broadcast instances by
`AFW.InvStep` (`AFW.lowStep_invStep`), so `AFW.roundInv_ga1` and
`AFW.roundInv_ga2` re-establish the invariant from the rows the answer
fires. `AFW.boundInv_of` and `AFW.writeGhost_bound` carry the bound
invariant, whose one open case is the link: there the ghost write puts the
round's bound bit on record, which is `AFW.stage_gbcaSend_ga2`.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

/-! ### The coupling

The relation is a function, so a Dirac outcome of the flat reading is matched
by the single composed state it is read as, and an outcome whose only free
coordinate is the oracle's is matched outcome by outcome. -/

/-- A Dirac outcome matched by the single composed state it is read as. -/
private theorem match_pure (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRel P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (PMF.pure s) Ω ∧ Ω.bind id = PMF.pure t := by
  refine ⟨PMF.pure (PMF.pure t), ⟨PMF.pure (s, PMF.pure t), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro q hq
    rw [PMF.mem_support_pure_iff] at hq
    subst hq
    exact ⟨t, rfl, h⟩
  · rw [PMF.pure_bind]
    rfl

/-- An outcome whose only free coordinate is the oracle's, matched outcome by
outcome. -/
private theorem match_prod (P : Params) {x : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w : NetState P.n} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)}
    (h : ∀ o ∈ ν.support, ProtocolRel P (x, w, o) (G, C, A, o)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) ν)) Ω ∧
      Ω.bind id =
        prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ν)) := by
  refine ⟨ν.map (fun o => PMF.pure ((G, C, A, o) : ComposedState P)),
    ⟨ν.map (fun o => (((x, w, o) : ProtocolState P),
      PMF.pure ((G, C, A, o) : ComposedState P))), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.map_comp, prodPMF_pure₂]
    rfl
  · rw [PMF.map_comp]
    rfl
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    exact ⟨(G, C, A, o), rfl, h o ho⟩
  · rw [PMF.bind_map, prodPMF_pure₃]
    rfl

/-! ### Reading a row off a label the process owns

A program's row on a label of `roundOwn j` is a row of the implementation:
every other row of the flat reading either carries a label of another class,
or carries one of these at another process, or is the replaced program's
self-loop, which has no row on a label the process acts on. -/

theorem stageRow_of_own {P : Params} {j : Fin P.n} {q : AFW.ProcRec P.n}
    {L : ExtendedLabel P.n (Msg P.n)} {y : AFW.ProcRec P.n} (hown : roundOwn j L)
    (h : ProgramStep P j q L (PMF.pure y)) : RoundStep P j q L (PMF.pure y) := by
  generalize hμ : (PMF.pure y : PMF (AFW.ProcRec P.n)) = ν at h
  cases h
  case stageRow h' => exact hμ ▸ h'
  case corruptedIdle hh hτ hown' => exact absurd (actsAt_of_roundOwn hown) hown'
  all_goals first
    | exact hown.elim
    | (rename_i hid; exact absurd hown hid)

/-- **The second gather's local input is written at the link alone**: a send
either leaves every round's input where it stands, or carries the link's
`⟨INIT, ·⟩` in the caller's own input-broadcast instance of the second
gather. -/
theorem stage_gbcaSend_ga2 (P : Params) {j : Fin P.n} {c : CoreRec P.n}
    {p : StageSideRec P.n} {r : ℕ} {m : Msg P.n} {μ : PMF (AFW.ProcRec P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaSend r j m)) μ) :
    (∀ x : AFW.ProcRec P.n, μ = PMF.pure x → ∀ r',
        (((x.2.stage r').ga2.proc)).input = ((p.stage r').ga2.proc).input)
      ∨ ∃ q y, m = Msg.brbIn2 q (BRB.BMsg.init y) := by
  cases h <;> first
    | exact Or.inr ⟨_, _, rfl⟩
    | exact Or.inl (fun x hx r' => by
        obtain rfl := pureN_inj hx.symm
        by_cases hr' : r' = r
        · subst hr'; simp [LocalState.setP]
        · rw [StageSideRecP.stage_setStage_ne _ _ _ hr'])

/-! ### The store against the flat receipt quorum

A gather program of the composed reading reads its store; the flat reading
reads a `2f + 1` `VOTE` receipt quorum on the process's own local state in the
instance. Under `StoreInv` the two agree wherever the flat guard fires. -/

section Store

variable {P : Params} {X : Type} [DecidableEq X]

/-- The return flag the view supplies leaves the store where it stands. -/
theorem storeIn_brbLocal (p : LocalState P.n (BRB.PState X) (BRB.BMsg X)) :
    storeIn P (brbLocal P p) = storeIn P p := rfl

variable {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w : NetState P.n}

/-- The first gather's input store holds the value a flat receipt quorum
carries. -/
theorem holdsIn_ga1 (hI : StoreInv P u w) (r : ℕ) (j k : Fin P.n) {x : Bool}
    (hq : apIn1 P ((u j).2.stage r) k x) :
    Gather.holdsIn ((Gather.ga (GBCA.ByAFW.ga1 (toRound P u w r))).proc j) k x :=
  storeIn_eq_of_quorum P (hI r k).1 (j := j) hq

/-- The first gather's bind store holds the payload a flat receipt quorum
carries. -/
theorem holdsBind_ga1 (hI : StoreInv P u w) (r : ℕ) (j q : Fin P.n)
    {U : Gather.APSet P.n Bool} (hq : apBind1 P ((u j).2.stage r) q U) :
    Gather.holdsBind ((Gather.ga (GBCA.ByAFW.ga1 (toRound P u w r))).proc j) q U :=
  storeIn_eq_of_quorum P (hI r q).2.1 (j := j) hq

/-- The second gather's input store holds the value a flat receipt quorum
carries. -/
theorem holdsIn_ga2 (hI : StoreInv P u w) (r : ℕ) (j k : Fin P.n) {x : Option Bool}
    (hq : apIn2 P ((u j).2.stage r) k x) :
    Gather.holdsIn ((Gather.ga (GBCA.ByAFW.ga2 (toRound P u w r))).proc j) k x :=
  storeIn_eq_of_quorum P (hI r k).2.2.1 (j := j) hq

/-- The second gather's bind store holds the payload a flat receipt quorum
carries. -/
theorem holdsBind_ga2 (hI : StoreInv P u w) (r : ℕ) (j q : Fin P.n)
    {U : Gather.APSet P.n (Option Bool)} (hq : apBind2 P ((u j).2.stage r) q U) :
    Gather.holdsBind ((Gather.ga (GBCA.ByAFW.ga2 (toRound P u w r))).proc j) q U :=
  storeIn_eq_of_quorum P (hI r q).2.2.2 (j := j) hq

/-- The receiver's own local state after a delivery. -/
theorem recvMsg_self (s : BRB.BrachaState P.n X) (i k : Fin P.n) (m : BRB.BMsg X) :
    (s.recvMsg i k m).1 i = (s.1 i).deliverTo k m := Function.update_self _ _ _

/-- The return flag the view supplies is on exactly where the store holds a
value. -/
theorem brbLocal_returned (p : LocalState P.n (BRB.PState X) (BRB.BMsg X)) :
    ((brbLocal P p).proc).returned = (storeIn P p).isSome := rfl

/-- **A delivery that fills an empty store licenses the instance's return to
the receiver.** -/
theorem implStep_ret_of_store {i j k : Fin P.n} {s : BRB.BrachaState P.n X}
    {m : BRB.BMsg X} {v : X} (hr : (s.proc j).returned = false)
    (hst : storeIn P ((s.1 j).deliverTo k m) = some v) :
    BRB.BrachaStep P i (s.recvMsg j k m) (.ret j v)
      (PMF.pure ((s.recvMsg j k m).setProc j
        { (s.recvMsg j k m).proc j with returned := true })) := by
  refine BRB.BrachaStep.ret _ j v ?_ ?_
  · rw [SubState.recvCount_eq_box, recvMsg_self]
    exact storeIn_spec P hst
  · rw [SubState.recvMsg_proc]
    exact hr

/-- **A delivery moves the store in one way only.** Under the broadcast
invariant at most one value carries a receipt quorum, so a delivery either
leaves the store where it stands or fills an empty store. -/
theorem storeIn_deliver_cases {i j k : Fin P.n} {s : BRB.BrachaState P.n X}
    {m : BRB.BMsg X} (hInv : BRB.Inv P i (s.recvMsg j k m)) :
    storeIn P ((s.1 j).deliverTo k m) = storeIn P (s.1 j) ∨
      (storeIn P (s.1 j) = none ∧
        ∃ v, storeIn P ((s.1 j).deliverTo k m) = some v) := by
  have hpost : (s.recvMsg j k m).1 j = (s.1 j).deliverTo k m := Function.update_self _ _ _
  have hmono : ∀ y : X, 2 * P.f + 1 ≤ (s.1 j).recvCount (BRB.BMsg.vote y) →
      2 * P.f + 1 ≤ ((s.1 j).deliverTo k m).recvCount (BRB.BMsg.vote y) := by
    intro y hy
    have h1 := SubState.recvCount_le_recvMsg s j k m j (BRB.BMsg.vote y)
    rw [SubState.recvCount_eq_box, SubState.recvCount_eq_box, hpost] at h1
    exact le_trans hy h1
  by_cases hq : ∃ y, 2 * P.f + 1 ≤ ((s.1 j).deliverTo k m).recvCount (BRB.BMsg.vote y)
  · obtain ⟨v, hv⟩ := hq
    have hsome : storeIn P ((s.1 j).deliverTo k m) = some v := by
      have h := storeIn_eq_of_quorum P hInv (j := j) (x := v) (by rw [hpost]; exact hv)
      rwa [hpost] at h
    by_cases hb : storeIn P (s.1 j) = none
    · exact Or.inr ⟨hb, v, hsome⟩
    · obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp hb
      refine Or.inl ?_
      have h := storeIn_eq_of_quorum P hInv (j := j) (x := v')
        (by rw [hpost]; exact hmono v' (storeIn_spec P hv'))
      rw [hpost] at h
      rw [h, hv']
  · simp only [not_exists, not_le] at hq
    have hnone : storeIn P ((s.1 j).deliverTo k m) = none := by
      unfold storeIn
      rw [dif_neg]
      rintro ⟨y, hy⟩
      exact absurd hy (not_le.mpr (hq y))
    refine Or.inl ?_
    rw [hnone]
    unfold storeIn
    rw [dif_neg]
    rintro ⟨y, hy⟩
    exact absurd (hmono y hy) (not_le.mpr (hq y))

end Store

/-! ### Building a transition of one gather instance

A row of `Gather.StepOverBracha` is a transition of the instance at the interface
label over its own. The call is the exception: the instance answers `call id x`
on two rows, and the two sit at the two labels of the interface. -/

section GatherRows

variable {P : Params} {X : Type} [DecidableEq X]

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
    (h : ((Gather.ga s).proc id).input = none)
    (hb : ((Gather.brbIn s id).proc id).input = none) :
    (Gather.instanceOverBracha P X).step s (Sum.inl (Gather.Label.call id x))
      (PMF.pure (Gather.setBrbIn
        (Gather.setGa s ((Gather.ga s).setProc id
          { (Gather.ga s).proc id with input := some x }))
        (Function.update (Gather.brbIn s) id
          (((Gather.brbIn s id).setProc id
            { (Gather.brbIn s id).proc id with input := some x }).mcast id (.init x))))) := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  exact Gather.instAt_lab_step (b' := b) (by simp)
    (Gather.procStep_update (Gather.ProgramStep.call (v id) x h)
      (fun i hi => Gather.ProgramStep.callIdle (v i) id x (Ne.symm hi)))
    (Gather.NetworkStep.call y id x)
    (Gather.lift_update (by simp) (fun k hk => by simp [hk])
      (Gather.row_brachaInstance_call_step P id (a id) x hb))
    (fun _ => Gather.lift_idle rfl)

/-- Build the instance's input-enabledness loop. -/
theorem row_instanceOverBracha_callLoop (s : Gather.StateOverBracha P.n X) (id : Fin P.n) (x : X) :
    (Gather.instanceOverBracha P X).step s (Sum.inr (Gather.LoopLabel.callLoop id x)) (PMF.pure s)
      := by
  obtain ⟨⟨v, y⟩, a, b⟩ := s
  refine Gather.instAt_lab_step (x := v) (w' := y) (a' := a) (b' := b) (by simp)
    (fun i => ?_) (Gather.NetworkStep.callLoop y id x) (fun k => ?_)
    (fun _ => Gather.lift_idle rfl)
  · by_cases hi : i = id
    · subst hi; exact Gather.ProgramStep.callLoop (v i) x
    · exact Gather.ProgramStep.callLoopIdle (v i) id x (Ne.symm hi)
  · by_cases hk : k = id
    · subst hk
      exact Gather.row_lift_step (by simp) (Gather.row_brachaInstance_callLoop_step P k (a k) x)
    · exact Gather.lift_idle (by simp [hk])

end GatherRows

/-! ### Building a transition of one round

One row of the layer beside one row of a gather instance, at the label the
round takes them on. The three hidden events `ret1`, `call2` and `ret2` are
silent transitions of the round; the call, the call loop and the graded return
are transitions on labels of the family alphabet. -/

section RoundRows

variable {P : Params} {r : ℕ}

/-- A silent row of the first gather is a silent transition of the round. -/
theorem roundOverBracha_ga1Tau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {c : Gather.StateOverBracha P.n Bool}
    (h : Gather.StepOverBracha P (GBCA.ByAFW.ga1 s) Gather.Label.tau (PMF.pure c)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau) (PMF.pure (GBCA.ByAFW.setGa1 s c))
      :=
  GBCA.ByAFW.roundAt_tau_ga1 (row_instanceOverBracha_inl (by simp) h)

/-- A silent row of the second gather is a silent transition of the round. -/
theorem roundOverBracha_ga2Tau (s : GBCA.ByAFW.RoundStateOverBracha P.n)
    {d : Gather.StateOverBracha P.n (Option Bool)}
    (h : Gather.StepOverBracha P (GBCA.ByAFW.ga2 s) Gather.Label.tau (PMF.pure d)) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau) (PMF.pure (GBCA.ByAFW.setGa2 s d))
      :=
  GBCA.ByAFW.roundAt_tau_ga2 (row_instanceOverBracha_inl (by simp) h)

/-- **The round's call**: the program records the input and the first gather
takes its call. -/
theorem roundOverBracha_callG (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n) (b : Bool)
    (h0 : (GBCA.ByAFW.procs s id).input = none)
    (hg : ((Gather.ga (GBCA.ByAFW.ga1 s)).proc id).input = none)
    (hb : ((Gather.brbIn (GBCA.ByAFW.ga1 s) id).proc id).input = none) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl (Label.callG r id b))
      (PMF.pure (GBCA.ByAFW.setGa1
        (GBCA.ByAFW.setProcs s (Function.update (GBCA.ByAFW.procs s) id
          { GBCA.ByAFW.procs s id with input := some b }))
        (Gather.setBrbIn
          (Gather.setGa (GBCA.ByAFW.ga1 s) ((Gather.ga (GBCA.ByAFW.ga1 s)).setProc id
            { (Gather.ga (GBCA.ByAFW.ga1 s)).proc id with input := some b }))
          (Function.update (Gather.brbIn (GBCA.ByAFW.ga1 s)) id
            (((Gather.brbIn (GBCA.ByAFW.ga1 s) id).setProc id
              { (Gather.brbIn (GBCA.ByAFW.ga1 s) id).proc id with
                input := some b }).mcast id (.init b)))))) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundAt_lab_step (by simp)
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .callG r id b) (by simp) (by simp)
      (GBCA.ByAFW.procStep_update (GBCA.ByAFW.ProgramStep.callG (v id) b h0)
        (fun i hi => GBCA.ByAFW.ProgramStep.callGIdle (v i) id b (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.callG y id b))
    (Gather.row_lift_step (by simp) (row_instanceOverBracha_call c id b hg hb))
    (Gather.lift_idle (by simp))

/-- **The round's call loop**: no program moves and the first gather takes its
input-enabledness loop. -/
theorem roundOverBracha_callLoop (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n) (b : Bool)
  :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inr (.gcallLoop r id b)) (PMF.pure s) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  refine GBCA.ByAFW.roundAt_lab_step (by simp)
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .callLoop r id b) (by simp) (by simp) (fun i => ?_)
      (GBCA.ByAFW.NetworkStep.callLoop y id b))
    (Gather.row_lift_step (by simp) (row_instanceOverBracha_callLoop c id b))
    (Gather.lift_idle (by simp))
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
  refine GBCA.ByAFW.roundAt_lab_step (by simp)
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .callLoop r id b) (by simp) (by simp) (fun i => ?_)
      (GBCA.ByAFW.NetworkStep.callLoop y id b))
    (Gather.row_lift_step (by simp) (row_instanceOverBracha_callLoop c id b))
    (Gather.lift_idle (by simp))
  by_cases hi : i = id
  · subst hi; exact GBCA.ByAFW.ProgramStep.callLoop (v i) b
  · exact GBCA.ByAFW.ProgramStep.callLoopIdle (v i) id b (Ne.symm hi)

/-- **The first gather's return**: the program records the candidate, the
round's bound bit is written from the core the return carries, and the first
gather takes its return. -/
theorem roundOverBracha_ret1 (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (g : Fin P.n → Option Bool)
    (hin : (GBCA.ByAFW.procs s id).input ≠ none) (hc : (GBCA.ByAFW.procs s id).cand = none)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.ga1 s) (.ret id g (ret1Core P s))
      (PMF.pure (GBCA.ByAFW.ga1 (afterRet1 P s id g)))) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau) (PMF.pure (afterRet1 P s id g)) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundAt_event_step (GBCA.ByAFW.RoundEvent.ret1 id g (ret1Core P ((v, y), c, d)))
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .ret1 id g (ret1Core P ((v, y), c,
      d))) (by simp) (by simp) (GBCA.ByAFW.procStep_update (GBCA.ByAFW.ProgramStep.ret1 (v id) g _
        hin hc)
        (fun i hi => GBCA.ByAFW.ProgramStep.ret1Idle (v i) id g _ (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.ret1 y id g _))
    (Gather.row_lift_step (by simp) (row_instanceOverBracha_inl (by simp) h))
    (Gather.lift_idle (by simp))

/-- **The second gather's call**: the program marks the call and the second
gather takes its call. -/
theorem roundOverBracha_call2 (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n) (x : Option
  Bool)
    (hc : (GBCA.ByAFW.procs s id).cand = some x) (h2 : (GBCA.ByAFW.procs s id).called2 = false)
    (hg : ((Gather.ga (GBCA.ByAFW.ga2 s)).proc id).input = none)
    (hb : ((Gather.brbIn (GBCA.ByAFW.ga2 s) id).proc id).input = none) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau) (PMF.pure (afterCall2 P s id x)) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundAt_event_step (GBCA.ByAFW.RoundEvent.call2 id x)
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .call2 id x) (by simp) (by simp)
      (GBCA.ByAFW.procStep_update (GBCA.ByAFW.ProgramStep.call2 (v id) x hc h2)
        (fun i hi => GBCA.ByAFW.ProgramStep.call2Idle (v i) id x (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.call2 y id x))
    (Gather.lift_idle (by simp))
    (Gather.row_lift_step (by simp) (row_instanceOverBracha_call d id x hg hb))

/-- **The second gather's return**: the program records the grade and the
second gather takes its return. -/
theorem roundOverBracha_ret2 (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n)
    (g : Fin P.n → Option (Option Bool))
    (h2 : (GBCA.ByAFW.procs s id).called2 = true) (ho : (GBCA.ByAFW.procs s id).out = none)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.ga2 s) (.ret id g (ret2Core P s))
      (PMF.pure (GBCA.ByAFW.ga2 (afterRet2 P s id g)))) :
    (GBCA.ByAFW.roundOverBracha P r).step s (Sum.inl Label.tau) (PMF.pure (afterRet2 P s id g)) :=
      by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundAt_event_step (GBCA.ByAFW.RoundEvent.ret2 id g (ret2Core P ((v, y), c, d)))
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .ret2 id g (ret2Core P ((v, y), c,
      d))) (by simp) (by simp) (GBCA.ByAFW.procStep_update (GBCA.ByAFW.ProgramStep.ret2 (v id) g _
        h2 ho)
        (fun i hi => GBCA.ByAFW.ProgramStep.ret2Idle (v i) id g _ (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.ret2 y id g _))
    (Gather.lift_idle (by simp))
    (Gather.row_lift_step (by simp) (row_instanceOverBracha_inl (by simp) h))

/-- **The round's graded return**: the program announces the grade it holds and
marks the record returned, and the bit the label carries is the one on
record. -/
theorem roundOverBracha_retG (s : GBCA.ByAFW.RoundStateOverBracha P.n) (id : Fin P.n) (out :
  GbcaOut)
    (ho : (GBCA.ByAFW.procs s id).out = some out) (hr : (GBCA.ByAFW.procs s id).returned = false) :
    (GBCA.ByAFW.roundOverBracha P r).step s
      (Sum.inl (Label.retG r id out ((GBCA.ByAFW.bound s).getD (GBCA.boundOfCore P ∅))))
      (PMF.pure (afterRetG P s id)) := by
  obtain ⟨⟨v, y⟩, c, d⟩ := s
  exact GBCA.ByAFW.roundAt_lab_step (by simp)
    (GBCA.ByAFW.roundPrograms_lab_step (lp := .retG r id out (y.getD (GBCA.boundOfCore P ∅)))
      (by simp) (by simp)
      (GBCA.ByAFW.procStep_update (GBCA.ByAFW.ProgramStep.retG (v id) out _ ho hr)
        (fun i hi => GBCA.ByAFW.ProgramStep.retGIdle (v i) id out _ (Ne.symm hi)))
      (GBCA.ByAFW.NetworkStep.retG y id out))
    (Gather.lift_idle (by simp)) (Gather.lift_idle (by simp))

/-! ### Runs of one round -/

/-- One silent transition of the round is a silent run. -/
theorem roundOverBracha_run_one {q q' : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent q q' :=
  System.weakLSilent_stepCons (by rw [nlab_tau]; exact h) (by simp)
    (System.weakLSilent_refl _ q')

/-- Two silent transitions of the round are a silent run. -/
theorem roundOverBracha_run_two {q q₁ q' : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h₁ : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q₁))
    (h₂ : (GBCA.ByAFW.roundOverBracha P r).step q₁ (Sum.inl Label.tau) (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent q q' :=
  System.weakLSilent_stepCons (by rw [nlab_tau]; exact h₁) (by simp)
    (roundOverBracha_run_one h₂)

/-- A silent transition followed by a visible one is a weak transition of the
round on that label. -/
theorem roundOverBracha_wstep_two {L : ExtendedLabel P.n} {q q₁ q' : GBCA.ByAFW.RoundStateOverBracha
  P.n}
    (hL : L ≠ Silent.τ)
    (h₁ : (GBCA.ByAFW.roundOverBracha P r).step q (Sum.inl Label.tau) (PMF.pure q₁))
    (h₂ : (GBCA.ByAFW.roundOverBracha P r).step q₁ L (PMF.pure q')) :
    (GBCA.ByAFW.roundOverBracha P r).weakLStep q L q' :=
  System.weakLStep_stepCons (by rw [nlab_tau]; exact h₁) (by simp)
    (System.weakLStep_of_step hL h₂)

end RoundRows

/-! ### The broadcast invariant across a row

`StoreInv` is the broadcast invariant at the `4n` instances of every round.
`RoundInv` is that clause at one round, `storeInv_update` carries it across a
row from the round the row names, and `roundInv_ga1`, `roundInv_ga2` and
`roundInv_frame` re-establish it from the rows the composed answer fires. -/

section Invariant

variable {P : Params}

/-- **The broadcast invariant at the `4n` instances of one round.** -/
def RoundInv (P : Params) (s : GBCA.ByAFW.RoundStateOverBracha P.n) : Prop :=
  ∀ k : Fin P.n, BRB.Inv P k (Gather.brbIn (GBCA.ByAFW.ga1 s) k) ∧
    BRB.Inv P k (Gather.brbBind (GBCA.ByAFW.ga1 s) k) ∧
    BRB.Inv P k (Gather.brbIn (GBCA.ByAFW.ga2 s) k) ∧
    BRB.Inv P k (Gather.brbBind (GBCA.ByAFW.ga2 s) k)

/-- `StoreInv` is `RoundInv` at every round of the view. -/
theorem storeInv_iff_roundInv (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n) :
    StoreInv P u w ↔ ∀ r, RoundInv P (toRound P u w r) := Iff.rfl

/-- **Every row of a gather instance moves each of its `2n` broadcast instances
by one row or not at all.** -/
theorem lowStep_invStep {X : Type} [DecidableEq X] {s : Gather.StateOverBracha P.n X}
    {l₀ : Gather.Label P.n X} {μ : PMF (Gather.StateOverBracha P.n X)}
    (h : Gather.StepOverBracha P s l₀ μ) {s' : Gather.StateOverBracha P.n X}
    (hs' : s' ∈ μ.support) (k : Fin P.n) :
    InvStep P k (Gather.brbIn s k) (Gather.brbIn s' k) ∧
      InvStep P k (Gather.brbBind s k) (Gather.brbBind s' k) := by
  cases h with
  | call id x hin hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨invStep_update _ id _ (BRB.BrachaStep.call (Gather.brbIn s id) x hb) k,
      InvStep.stand P k _⟩
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, InvStep.stand P k _⟩
  | brbInTau q c hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨invStep_update _ q c hb k, InvStep.stand P k _⟩
  | brbBindTau q d hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, invStep_update _ q d hb k⟩
  | deliver i q m hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, InvStep.stand P k _⟩
  | echo q hin hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, InvStep.stand P k _⟩
  | vote q U hin hech happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, InvStep.stand P k _⟩
  | bindCall q U hin hvot hsnd happ hQ hbc =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _,
      invStep_update _ q _ (BRB.BrachaStep.call (Gather.brbBind s q) U hbc) k⟩
  | byzantine q m hF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, InvStep.stand P k _⟩
  | inRet q i v c hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨invStep_update _ q c hb k, InvStep.stand P k _⟩
  | bindRet q i U d hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, invStep_update _ q d hb k⟩
  | ret id g hin hbind hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.stand P k _, InvStep.stand P k _⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact ⟨InvStep.row (BRB.BrachaStep.fail (Gather.brbIn s k) id),
      InvStep.row (BRB.BrachaStep.fail (Gather.brbBind s k) id)⟩

variable {s t : GBCA.ByAFW.RoundStateOverBracha P.n}

/-- A row that leaves both gather instances where they stand keeps the
invariant. -/
theorem roundInv_frame (hR : RoundInv P s) (h1 : GBCA.ByAFW.ga1 t = GBCA.ByAFW.ga1 s)
    (h2 : GBCA.ByAFW.ga2 t = GBCA.ByAFW.ga2 s) : RoundInv P t := by
  intro k
  rw [h1, h2]
  exact hR k

/-- A row of the first gather keeps the invariant. -/
theorem roundInv_ga1 {l₀ : Gather.Label P.n Bool} (hR : RoundInv P s)
    (h2 : GBCA.ByAFW.ga2 t = GBCA.ByAFW.ga2 s)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.ga1 s) l₀ (PMF.pure (GBCA.ByAFW.ga1 t))) :
    RoundInv P t := by
  intro k
  obtain ⟨h1', h2'⟩ := lowStep_invStep h (s' := GBCA.ByAFW.ga1 t) (by simp) k
  rw [h2]
  exact ⟨h1'.inv (hR k).1, h2'.inv (hR k).2.1, (hR k).2.2.1, (hR k).2.2.2⟩

/-- A row of the second gather keeps the invariant. -/
theorem roundInv_ga2 {l₀ : Gather.Label P.n (Option Bool)} (hR : RoundInv P s)
    (h1 : GBCA.ByAFW.ga1 t = GBCA.ByAFW.ga1 s)
    (h : Gather.StepOverBracha P (GBCA.ByAFW.ga2 s) l₀ (PMF.pure (GBCA.ByAFW.ga2 t))) :
    RoundInv P t := by
  intro k
  obtain ⟨h1', h2'⟩ := lowStep_invStep h (s' := GBCA.ByAFW.ga2 t) (by simp) k
  rw [h1]
  exact ⟨(hR k).1, (hR k).2.1, h1'.inv (hR k).2.2.1, h2'.inv (hR k).2.2.2⟩

/-- A row that moves both gather instances keeps the invariant. -/
theorem roundInv_both {l₁ : Gather.Label P.n Bool} {l₂ : Gather.Label P.n (Option Bool)}
    (hR : RoundInv P s)
    (h₁ : Gather.StepOverBracha P (GBCA.ByAFW.ga1 s) l₁ (PMF.pure (GBCA.ByAFW.ga1 t)))
    (h₂ : Gather.StepOverBracha P (GBCA.ByAFW.ga2 s) l₂ (PMF.pure (GBCA.ByAFW.ga2 t))) :
    RoundInv P t := by
  intro k
  obtain ⟨ha, hb⟩ := lowStep_invStep h₁ (s' := GBCA.ByAFW.ga1 t) (by simp) k
  obtain ⟨hc, hd⟩ := lowStep_invStep h₂ (s' := GBCA.ByAFW.ga2 t) (by simp) k
  exact ⟨ha.inv (hR k).1, hb.inv (hR k).2.1, hc.inv (hR k).2.2.1, hd.inv (hR k).2.2.2⟩

/-- The broadcast invariant at one round of the view. -/
theorem roundInv_of_storeInv {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w : NetState P.n}
    (hI : StoreInv P u w) (r : ℕ) : RoundInv P (toRound P u w r) := hI r

/-- **The broadcast invariant across a row**: the round the row names carries
it, and every other round stands still. -/
theorem storeInv_update {u x : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w v : NetState P.n}
    {r : ℕ} {Z : GBCA.ByAFW.RoundStateOverBracha P.n} (hI : StoreInv P u w)
    (hfam : (fun r' => toRound P x v r') = Function.update (fun r' => toRound P u w r') r Z)
    (hZ : RoundInv P Z) : StoreInv P x v := by
  intro r' k
  have h : toRound P x v r' = Function.update (fun r'' => toRound P u w r'') r Z r' :=
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

theorem toRound_fail {P : Params} (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (r : ℕ) (k : Fin P.n) :
    toRound P u (NetStateP.corrupt P k w) r
      = gActLow P (Sum.inl (Label.fail k)) (toRound P u w r) := by
  refine roundStateAt_ext ?_ ?_ (subStateAt_ext ?_ ?_ ?_ ?_) (subStateAt_ext ?_ ?_ ?_ ?_)
  · simp only [GBCA.ByAFW.procs, toRound, gActLow, GBCA.ByAFW.corruptAll, NetStateP.corrupt]
  · simp only [GBCA.ByAFW.bound, toRound, gActLow, GBCA.ByAFW.corruptAll, NetStateP.corrupt]
    split_ifs <;> rfl
  · refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.ga, GBCA.ByAFW.ga1, toRound, toGa1, gActLow, GBCA.ByAFW.corruptAll,
        Gather.corruptAll, SubState.corrupt, NetStateP.corrupt, NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.brbIn, GBCA.ByAFW.ga1, toRound, toGa1, gActLow, GBCA.ByAFW.corruptAll,
        Gather.corruptAll, SubState.corrupt, NetStateP.corrupt, NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.brbBind, GBCA.ByAFW.ga1, toRound, toGa1, gActLow, GBCA.ByAFW.corruptAll,
        Gather.corruptAll, SubState.corrupt, NetStateP.corrupt, NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · simp only [Gather.core, GBCA.ByAFW.ga1, toRound, toGa1, gActLow, GBCA.ByAFW.corruptAll,
      Gather.corruptAll, NetStateP.corrupt]
    split_ifs <;> rfl
  · refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.ga, GBCA.ByAFW.ga2, toRound, toGa2, gActLow, GBCA.ByAFW.corruptAll,
        Gather.corruptAll, SubState.corrupt, NetStateP.corrupt, NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.brbIn, GBCA.ByAFW.ga2, toRound, toGa2, gActLow, GBCA.ByAFW.corruptAll,
        Gather.corruptAll, SubState.corrupt, NetStateP.corrupt, NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · funext q
    refine Prod.ext rfl (networkState_ext ?_ ?_) <;>
      simp only [Gather.brbBind, GBCA.ByAFW.ga2, toRound, toGa2, gActLow, GBCA.ByAFW.corruptAll,
        Gather.corruptAll, SubState.corrupt, NetStateP.corrupt, NetworkState.corrupt] <;>
      split_ifs <;> rfl
  · simp only [Gather.core, GBCA.ByAFW.ga2, toRound, toGa2, gActLow, GBCA.ByAFW.corruptAll,
      Gather.corruptAll, NetStateP.corrupt]
    split_ifs <;> rfl

/-- **The whole family of rounds after a Byzantine injection**: the round the
message names moves, the rest stand still. -/
theorem toRoundFamByz {P : Params} (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (r : ℕ) (k : Fin P.n) (m : Msg P.n) :
    (fun r' => toRound P u (w.gsent r k m) r')
      = Function.update (fun r' => toRound P u w r') r (toRound P u (w.gsent r k m) r) := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self]
  · rw [Function.update_of_ne hr]
    simp only [toRound, toGa1, toGa2, gsent_sent_ne w r k m hr, gsent_F, gsent_ghostRec]

/-- A row that leaves every round record where it stands leaves the whole
family of rounds where it stands. -/
theorem view_unchanged {P : Params} {x u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    (h : ∀ i, (x i).2 = (u i).2) (w : NetState P.n) :
    (fun r => toRound P u w r) = fun r => toRound P x w r := by
  funext r
  exact (toRound_congr (fun i => by rw [h i])).symm

/-! ### Answering a send

A send of the flat reading is a silent run of the round: the sender writes its
own record, the network records the message, and the round the label tags moves
as its own rules move it. The link is the one send answered by two events. -/

theorem stage_answer_gbcaSend (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) (hI : StoreInv P u w) {r : ℕ} {m : Msg P.n}
    {μ : PMF (AFW.ProcRec P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaSend r j m)) μ) :
    ∃ x : AFW.ProcRec P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
        (toRound P (Function.update u j x)
          ((w.gsent r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) r) ∧
      RoundInv P (toRound P (Function.update u j x)
        ((w.gsent r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) r) := by
  subst hu
  cases h with
  | ga1Echo _ _ _ hh hterm hin hcard hsend =>
    have hacc : ((Gather.ga (toGa1 P u w r)).proc j).accepted
        = acceptedIn1 P ((u j).2.stage r) := accepted_toGa1 u w r j
    have hrow := Gather.StepOverBracha.echo (toGa1 P u w r) j hin
      (by rw [hacc]; exact hcard) hsend
    rw [hacc] at hrow
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ga1Echo rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | ga1Vote _ _ _ U hh hterm hin hech happ hQ hsend =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Gather.GaMsg.echo A ∈ (Gather.ga (toGa1 P u w r)).recv j q ∧
          Gather.approvedBy ((Gather.ga (toGa1 P u w r)).proc j) A ∧ A ⊆ U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨A, hA1, hA2, hA3⟩ := hmem q hq
      exact ⟨A, hA1, fun z hz => holdsIn_ga1 hI r j z.1 (hA2 z hz), hA3⟩
    have hrow := Gather.StepOverBracha.vote (toGa1 P u w r) j U hin hech
      (fun q hq => holdsIn_ga1 hI r j q.1 (happ q hq)) hQ' hsend
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ga1Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | ga1Bind _ _ _ U hh hterm hin hvot hsnd hbc happ hQ =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Gather.GaMsg.vote W ∈ (Gather.ga (toGa1 P u w r)).recv j q ∧
          Gather.approvedBy ((Gather.ga (toGa1 P u w r)).proc j) W ∧ W ⊆ U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨W, hW1, hW2, hW3⟩ := hmem q hq
      exact ⟨W, hW1, fun z hz => holdsIn_ga1 hI r j z.1 (hW2 z hz), hW3⟩
    have hrow := Gather.StepOverBracha.bindCall (toGa1 P u w r) j U hin hvot hsnd
      (fun q hq => holdsIn_ga1 hI r j q.1 (happ q hq)) hQ' hbc
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ga1Bind rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | ga2Echo _ _ _ hh hterm hin hcard hsend =>
    have hacc : ((Gather.ga (toGa2 P u w r)).proc j).accepted
        = acceptedIn2 P ((u j).2.stage r) := accepted_toGa2 u w r j
    have hrow := Gather.StepOverBracha.echo (toGa2 P u w r) j hin
      (by rw [hacc]; exact hcard) hsend
    rw [hacc] at hrow
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ga2Echo rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | ga2Vote _ _ _ U hh hterm hin hech happ hQ hsend =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Gather.GaMsg.echo A ∈ (Gather.ga (toGa2 P u w r)).recv j q ∧
          Gather.approvedBy ((Gather.ga (toGa2 P u w r)).proc j) A ∧ A ⊆ U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨A, hA1, hA2, hA3⟩ := hmem q hq
      exact ⟨A, hA1, fun z hz => holdsIn_ga2 hI r j z.1 (hA2 z hz), hA3⟩
    have hrow := Gather.StepOverBracha.vote (toGa2 P u w r) j U hin hech
      (fun q hq => holdsIn_ga2 hI r j q.1 (happ q hq)) hQ' hsend
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ga2Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | ga2Bind _ _ _ U hh hterm hin hvot hsnd hbc happ hQ =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Gather.GaMsg.vote W ∈ (Gather.ga (toGa2 P u w r)).recv j q ∧
          Gather.approvedBy ((Gather.ga (toGa2 P u w r)).proc j) W ∧ W ⊆ U := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨W, hW1, hW2, hW3⟩ := hmem q hq
      exact ⟨W, hW1, fun z hz => holdsIn_ga2 hI r j z.1 (hW2 z hz), hW3⟩
    have hrow := Gather.StepOverBracha.bindCall (toGa2 P u w r) j U hin hvot hsnd
      (fun q hq => holdsIn_ga2 hI r j q.1 (happ q hq)) hQ' hbc
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ga2Bind rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | link _ _ _ g hh hterm hin hbind hsubap hQ hr1 hin2 hbin2 =>
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, Gather.holdsBind ((Gather.ga (toGa1 P u w r)).proc j) q U ∧
          Gather.APSet.subMap U g := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨U, hU1, hU2⟩ := hmem q hq
      exact ⟨U, holdsBind_ga1 hI r j q hU1, hU2⟩
    have hrow1 : Gather.StepOverBracha P (GBCA.ByAFW.ga1 (toRound P u w r))
        (.ret j g (ret1Core P (toRound P u w r)))
        (PMF.pure (GBCA.ByAFW.ga1 (afterRet1 P (toRound P u w r) j g))) :=
      Gather.StepOverBracha.ret _ j g hin hbind
        (fun k x hx => holdsIn_ga1 hI r j k (hsubap k x hx)) hQ' hr1
    have hrow2 : Gather.StepOverBracha P (GBCA.ByAFW.ga2 (afterRet1 P (toRound P u w r) j g))
        (.call j (GBCA.cand P g))
        (PMF.pure (GBCA.ByAFW.ga2 (afterCall2 P (afterRet1 P (toRound P u w r) j g) j
          (GBCA.cand P g)))) :=
      Gather.StepOverBracha.call _ j (GBCA.cand P g) hin2 hbin2
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_ret1_call2 rfl]
    · exact roundOverBracha_run_two
        (roundOverBracha_ret1 (toRound P u w r) j g hin hin2 hrow1)
        (roundOverBracha_call2 (afterRet1 P (toRound P u w r) j g) j (GBCA.cand P g)
          (by simp [afterRet1]) (by simp [afterRet1, toProc, hin2]) hin2 hbin2)
    · have hR1 : RoundInv P (afterRet1 P (toRound P u w r) j g) :=
        roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow1
      exact roundInv_ga2 hR1 rfl hrow2
  | in1Echo _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa1 P u w r) i _
      (BRB.BrachaStep.echo (Gather.brbIn (toGa1 P u w r) i) j mm hrecv hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_in1Echo rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | in1VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa1 P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.brbIn (toGa1 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_in1Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | in1VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa1 P u w r) i _
      (BRB.BrachaStep.voteAmp (Gather.brbIn (toGa1 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_in1Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | bind1Echo _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa1 P u w r) i _
      (BRB.BrachaStep.echo (Gather.brbBind (toGa1 P u w r) i) j mm hrecv hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_bind1Echo rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | bind1VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa1 P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.brbBind (toGa1 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_bind1Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | bind1VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa1 P u w r) i _
      (BRB.BrachaStep.voteAmp (Gather.brbBind (toGa1 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_bind1Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow)
    · exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow
  | in2Echo _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa2 P u w r) i _
      (BRB.BrachaStep.echo (Gather.brbIn (toGa2 P u w r) i) j mm hrecv hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_in2Echo rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | in2VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa2 P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.brbIn (toGa2 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_in2Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | in2VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa2 P u w r) i _
      (BRB.BrachaStep.voteAmp (Gather.brbIn (toGa2 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_in2Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | bind2Echo _ _ _ i mm hh hterm hrecv hsend =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa2 P u w r) i _
      (BRB.BrachaStep.echo (Gather.brbBind (toGa2 P u w r) i) j mm hrecv hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_bind2Echo rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | bind2VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa2 P u w r) i _
      (BRB.BrachaStep.voteQuorum (Gather.brbBind (toGa2 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_bind2Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
  | bind2VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa2 P u w r) i _
      (BRB.BrachaStep.voteAmp (Gather.brbBind (toGa2 P u w r) i) j mm hcnt hsend)
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_, ?_⟩ <;>
      rw [toRound_bind2Vote rfl]
    · exact roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow)
    · exact roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow


/-! ### Answering a delivery

A delivery of the flat reading files the message in the receiver's own local
state of the network state the message's tag names. A gather message moves the
gather instance alone. A broadcast message moves the broadcast instance, and,
where it completes the receiver's `2f + 1` `VOTE` quorum, the instance returns
to the receiver as well, which is a second transition of the round. -/

/-- A delivery in an input-broadcast instance of the first gather, answered -/
theorem answer_dlvIn1 (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} (w : NetState P.n)
    {j : Fin P.n} {c : CoreRec P.n} (hI : StoreInv P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg Bool) (hsent : Msg.brbIn1 i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
        (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbIn1 i mm)))
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbIn1 i mm)))) r) ∧
      RoundInv P (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbIn1 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbIn1 i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.brbIn (toGa1 P u w r) i) .tau
      (PMF.pure ((Gather.brbIn (toGa1 P u w r) i).recvMsg j k mm)) :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_slice (hf := unIn1_inj i)).mpr ⟨_, hsent, by simp [unIn1]⟩)
  have hrow₁ := Gather.StepOverBracha.brbInTau (toGa1 P u w r) i _ hdlv
  have hInv' : BRB.Inv P i ((Gather.brbIn (toGa1 P u w r) i).recvMsg j k mm) :=
    (InvStep.row hdlv).inv (roundInv_of_storeInv hI r i).1
  have hR₁ : RoundInv P (afterDlvIn1 P (toRound P u w r) i j k mm) :=
    roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow₁
  rcases storeIn_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v, hst⟩
  · rw [toRound_dlvIn1 rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow₁), hR₁⟩
  · have hr₀ : ((Gather.brbIn (toGa1 P u w r) i).proc j).returned = false := by
      change (storeIn P ((Gather.brbIn (toGa1 P u w r) i).1 j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.brbIn (GBCA.ByAFW.ga1 (afterDlvIn1 P (toRound P u w r) i j k mm)) i
        = (Gather.brbIn (toGa1 P u w r) i).recvMsg j k mm := by
      simp [afterDlvIn1]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.ga1 (afterDlvIn1 P (toRound P u w r) i j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.ga1 (afterInRet1 P
          (afterDlvIn1 P (toRound P u w r) i j k mm) i j v))) := by
      refine Gather.StepOverBracha.inRet _ i j v _ ?_
      rw [hbi]
      exact implStep_ret_of_store hr₀ hst
    rw [toRound_dlvIn1_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_ga1Tau (toRound P u w r) hrow₁)
        (roundOverBracha_ga1Tau (afterDlvIn1 P (toRound P u w r) i j k mm) hrow₂),
      roundInv_ga1 hR₁ rfl hrow₂⟩

/-- A delivery in a bind-broadcast instance of the first gather, answered -/
theorem answer_dlvBind1 (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} (w : NetState P.n)
    {j : Fin P.n} {c : CoreRec P.n} (hI : StoreInv P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Gather.APSet P.n Bool)) (hsent : Msg.brbBind1 i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
        (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbBind1 i mm)))
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbBind1 i mm)))) r) ∧
      RoundInv P (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbBind1 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbBind1 i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.brbBind (toGa1 P u w r) i) .tau
      (PMF.pure ((Gather.brbBind (toGa1 P u w r) i).recvMsg j k mm)) :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_slice (hf := unBind1_inj i)).mpr ⟨_, hsent, by simp [unBind1]⟩)
  have hrow₁ := Gather.StepOverBracha.brbBindTau (toGa1 P u w r) i _ hdlv
  have hInv' : BRB.Inv P i ((Gather.brbBind (toGa1 P u w r) i).recvMsg j k mm) :=
    (InvStep.row hdlv).inv (roundInv_of_storeInv hI r i).2.1
  have hR₁ : RoundInv P (afterDlvBind1 P (toRound P u w r) i j k mm) :=
    roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow₁
  rcases storeIn_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v, hst⟩
  · rw [toRound_dlvBind1 rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow₁), hR₁⟩
  · have hr₀ : ((Gather.brbBind (toGa1 P u w r) i).proc j).returned = false := by
      change (storeIn P ((Gather.brbBind (toGa1 P u w r) i).1 j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.brbBind (GBCA.ByAFW.ga1 (afterDlvBind1 P (toRound P u w r) i j k mm)) i
        = (Gather.brbBind (toGa1 P u w r) i).recvMsg j k mm := by
      simp [afterDlvBind1]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.ga1 (afterDlvBind1 P (toRound P u w r) i j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.ga1 (afterBindRet1 P
          (afterDlvBind1 P (toRound P u w r) i j k mm) i j v))) := by
      refine Gather.StepOverBracha.bindRet _ i j v _ ?_
      rw [hbi]
      exact implStep_ret_of_store hr₀ hst
    rw [toRound_dlvBind1_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_ga1Tau (toRound P u w r) hrow₁)
        (roundOverBracha_ga1Tau (afterDlvBind1 P (toRound P u w r) i j k mm) hrow₂),
      roundInv_ga1 hR₁ rfl hrow₂⟩

/-- A delivery in an input-broadcast instance of the second gather, answered -/
theorem answer_dlvIn2 (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} (w : NetState P.n)
    {j : Fin P.n} {c : CoreRec P.n} (hI : StoreInv P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Option Bool)) (hsent : Msg.brbIn2 i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
        (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbIn2 i mm)))
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbIn2 i mm)))) r) ∧
      RoundInv P (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbIn2 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbIn2 i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.brbIn (toGa2 P u w r) i) .tau
      (PMF.pure ((Gather.brbIn (toGa2 P u w r) i).recvMsg j k mm)) :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_slice (hf := unIn2_inj i)).mpr ⟨_, hsent, by simp [unIn2]⟩)
  have hrow₁ := Gather.StepOverBracha.brbInTau (toGa2 P u w r) i _ hdlv
  have hInv' : BRB.Inv P i ((Gather.brbIn (toGa2 P u w r) i).recvMsg j k mm) :=
    (InvStep.row hdlv).inv (roundInv_of_storeInv hI r i).2.2.1
  have hR₁ : RoundInv P (afterDlvIn2 P (toRound P u w r) i j k mm) :=
    roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow₁
  rcases storeIn_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v, hst⟩
  · rw [toRound_dlvIn2 rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow₁), hR₁⟩
  · have hr₀ : ((Gather.brbIn (toGa2 P u w r) i).proc j).returned = false := by
      change (storeIn P ((Gather.brbIn (toGa2 P u w r) i).1 j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.brbIn (GBCA.ByAFW.ga2 (afterDlvIn2 P (toRound P u w r) i j k mm)) i
        = (Gather.brbIn (toGa2 P u w r) i).recvMsg j k mm := by
      simp [afterDlvIn2]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.ga2 (afterDlvIn2 P (toRound P u w r) i j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.ga2 (afterInRet2 P
          (afterDlvIn2 P (toRound P u w r) i j k mm) i j v))) := by
      refine Gather.StepOverBracha.inRet _ i j v _ ?_
      rw [hbi]
      exact implStep_ret_of_store hr₀ hst
    rw [toRound_dlvIn2_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_ga2Tau (toRound P u w r) hrow₁)
        (roundOverBracha_ga2Tau (afterDlvIn2 P (toRound P u w r) i j k mm) hrow₂),
      roundInv_ga2 hR₁ rfl hrow₂⟩

/-- A delivery in a bind-broadcast instance of the second gather, answered -/
theorem answer_dlvBind2 (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} (w : NetState P.n)
    {j : Fin P.n} {c : CoreRec P.n} (hI : StoreInv P u w) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Gather.APSet P.n (Option Bool))) (hsent : Msg.brbBind2 i mm ∈ w.sent r k) :
    (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
        (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbBind2 i mm)))
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbBind2 i mm)))) r) ∧
      RoundInv P (toRound P (Function.update u j (c, (u j).2.deliverTo r k (.brbBind2 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.brbBind2 i mm)))) r) := by
  have hdlv : BRB.BrachaStep P i (Gather.brbBind (toGa2 P u w r) i) .tau
      (PMF.pure ((Gather.brbBind (toGa2 P u w r) i).recvMsg j k mm)) :=
    BRB.BrachaStep.deliver _ j k mm
      ((mem_slice (hf := unBind2_inj i)).mpr ⟨_, hsent, by simp [unBind2]⟩)
  have hrow₁ := Gather.StepOverBracha.brbBindTau (toGa2 P u w r) i _ hdlv
  have hInv' : BRB.Inv P i ((Gather.brbBind (toGa2 P u w r) i).recvMsg j k mm) :=
    (InvStep.row hdlv).inv (roundInv_of_storeInv hI r i).2.2.2
  have hR₁ : RoundInv P (afterDlvBind2 P (toRound P u w r) i j k mm) :=
    roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow₁
  rcases storeIn_deliver_cases (i := i) (j := j) (k := k) hInv' with hst | ⟨hnone, v, hst⟩
  · rw [toRound_dlvBind2 rfl r i k mm hst]
    exact ⟨roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow₁), hR₁⟩
  · have hr₀ : ((Gather.brbBind (toGa2 P u w r) i).proc j).returned = false := by
      change (storeIn P ((Gather.brbBind (toGa2 P u w r) i).1 j)).isSome = false
      rw [hnone]
      rfl
    have hbi : Gather.brbBind (GBCA.ByAFW.ga2 (afterDlvBind2 P (toRound P u w r) i j k mm)) i
        = (Gather.brbBind (toGa2 P u w r) i).recvMsg j k mm := by
      simp [afterDlvBind2]
    have hrow₂ : Gather.StepOverBracha P
        (GBCA.ByAFW.ga2 (afterDlvBind2 P (toRound P u w r) i j k mm)) Gather.Label.tau
        (PMF.pure (GBCA.ByAFW.ga2 (afterBindRet2 P
          (afterDlvBind2 P (toRound P u w r) i j k mm) i j v))) := by
      refine Gather.StepOverBracha.bindRet _ i j v _ ?_
      rw [hbi]
      exact implStep_ret_of_store hr₀ hst
    rw [toRound_dlvBind2_ret rfl r i k mm v hst]
    exact ⟨roundOverBracha_run_two (roundOverBracha_ga2Tau (toRound P u w r) hrow₁)
        (roundOverBracha_ga2Tau (afterDlvBind2 P (toRound P u w r) i j k mm) hrow₂),
      roundInv_ga2 hR₁ rfl hrow₂⟩

theorem stage_answer_gbcaDeliver (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) (hI : StoreInv P u w) {r : ℕ} {k : Fin P.n} {m : Msg P.n}
    {μ : PMF (AFW.ProcRec P.n)} (hsent : m ∈ w.sent r k)
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m)) μ) :
    ∃ x : AFW.ProcRec P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      (∀ r', ((x.2.stage r').ga2.proc).input = ((p.stage r').ga2.proc).input) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
        (toRound P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) ∧
      RoundInv P (toRound P (Function.update u j x)
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) := by
  subst hu
  cases h with
  | gdlvRecv _ _ _ _ _ hh hterm =>
    have hga2 : ∀ r', ((((u j).2.deliverTo r k m).stage r').ga2.proc).input
        = (((u j).2.stage r').ga2.proc).input := by
      intro r'
      by_cases hr' : r' = r
      · subst hr'
        simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo,
          StageSideRecP.stage_setStage_self]
        cases m <;> simp [LocalState.deliverTo]
      · rw [StageSideRecP.deliverTo, StageSideRecP.stage_setStage_ne _ _ _ hr']
    obtain ⟨hrun, hinv⟩ :
        (GBCA.ByAFW.roundOverBracha P r).weakLSilent (toRound P u w r)
            (toRound P (Function.update u j (c, (u j).2.deliverTo r k m))
              (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) ∧
          RoundInv P (toRound P (Function.update u j (c, (u j).2.deliverTo r k m))
            (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k m))) r) := by
      cases m with
      | ga1 mm =>
        have hrow := Gather.StepOverBracha.deliver (toGa1 P u w r) j k mm
          ((mem_slice (hf := unGa1_inj)).mpr ⟨_, hsent, rfl⟩)
        rw [toRound_dlvGa1 rfl]
        exact ⟨roundOverBracha_run_one (roundOverBracha_ga1Tau (toRound P u w r) hrow),
          roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow⟩
      | ga2 mm =>
        have hrow := Gather.StepOverBracha.deliver (toGa2 P u w r) j k mm
          ((mem_slice (hf := unGa2_inj)).mpr ⟨_, hsent, rfl⟩)
        rw [toRound_dlvGa2 rfl]
        exact ⟨roundOverBracha_run_one (roundOverBracha_ga2Tau (toRound P u w r) hrow),
          roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow⟩
      | brbIn1 i mm => exact answer_dlvIn1 P w hI r i k mm hsent
      | brbBind1 i mm => exact answer_dlvBind1 P w hI r i k mm hsent
      | brbIn2 i mm => exact answer_dlvIn2 P w hI r i k mm hsent
      | brbBind2 i mm => exact answer_dlvBind2 P w hI r i k mm hsent
    exact ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', hga2,
      hrun, hinv⟩


/-! ### Answering the call, the graded return and the call loop -/

/-- The graded-agreement call of the flat reading is the round's own call. -/
theorem stage_answer_callG (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) (hI : StoreInv P u w) {r : ℕ} {b : Bool}
    {μ : PMF (AFW.ProcRec P.n)}
    (h : RoundStep P j (c, p) (Sum.inl (.callG r j b)) μ) :
    ∃ x : AFW.ProcRec P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.proc.phase = .toCallG ∧ c.proc.round = r ∧
      c.proc.est = some b ∧
      x.1 = c.setProc { c.proc with phase := .awaitG } ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      (∀ r', ((x.2.stage r').ga2.proc).input = ((p.stage r').ga2.proc).input) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (toRound P u w r) (Sum.inl (.callG r j b))
        (toRound P (Function.update u j x)
          ((w.gsent r j (gCallPayload P j b)).writeGhost (ghostStep P)
            (Sum.inl (.callG r j b))) r) ∧
      RoundInv P (toRound P (Function.update u j x)
        ((w.gsent r j (gCallPayload P j b)).writeGhost (ghostStep P)
          (Sum.inl (.callG r j b))) r) := by
  subst hu
  cases h with
  | callG _ _ _ _ hh hph hr hterm hest hin hbin =>
    have hrow := Gather.StepOverBracha.call (toGa1 P u w r) j b hin hbin
    refine ⟨_, rfl, hh, hph, hr, hest, rfl,
      fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', fun r' => ?_, ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp
      · rw [StageSideRecP.stage_setStage_ne _ _ _ hr']
    · rw [gCallPayload, toRound_callG rfl]
      exact System.weakLStep_of_step (by simp)
        (roundOverBracha_callG (toRound P u w r) j b hin hin hbin)
    · rw [gCallPayload, toRound_callG rfl]
      exact roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow

/-- The graded-agreement return of the flat reading is the second gather's
return followed by the round's own return, the grade read off the second
gather's output. -/
theorem stage_answer_retG (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) (hI : StoreInv P u w) {r : ℕ} {out : GbcaOut} {bnd : Bool}
    {μ : PMF (AFW.ProcRec P.n)} (hbnd : bnd = ghostOut P w r j out)
    (hset : ∀ i, (((u i).2.stage r).ga2.proc).input ≠ none →
      (w.ghostRec r).2.2 ≠ none)
    (h : RoundStep P j (c, p) (Sum.inl (.retG r j out bnd)) μ) :
    ∃ x : AFW.ProcRec P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.proc.phase = .awaitG ∧ c.proc.round = r ∧
      x.1 = c.setProc { c.proc with
        est := out.est, lastGrade := some out, phase := .toCallW } ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      (∀ r', ((x.2.stage r').ga2.proc).input = ((p.stage r').ga2.proc).input) ∧
      (GBCA.ByAFW.roundOverBracha P r).weakLStep (toRound P u w r) (Sum.inl (.retG r j out bnd))
        (toRound P (Function.update u j x)
          (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out bnd))) r) ∧
      RoundInv P (toRound P (Function.update u j x)
        (w.writeGhost (ghostStep P) (Sum.inl (.retG r j out bnd))) r) := by
  subst hu
  cases h with
  | retG _ _ _ g _ hh hph hr hterm hin hbind hsubap hQ hr2 =>
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp (hset j hin)
    have hb : bnd = (GBCA.ByAFW.bound (toRound P u w r)).getD (GBCA.boundOfCore P ∅) := by
      rw [hbnd]
      unfold ghostOut
      simp only [bound_toRound, hβ, Option.getD_some]
    subst hb
    have hQ' : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, Gather.holdsBind ((Gather.ga (toGa2 P u w r)).proc j) q U ∧
          Gather.APSet.subMap U g := by
      obtain ⟨Q, hcard, hmem⟩ := hQ
      refine ⟨Q, hcard, fun q hq => ?_⟩
      obtain ⟨U, hU1, hU2⟩ := hmem q hq
      exact ⟨U, holdsBind_ga2 hI r j q hU1, hU2⟩
    have hrow : Gather.StepOverBracha P (GBCA.ByAFW.ga2 (toRound P u w r))
        (.ret j g (ret2Core P (toRound P u w r)))
        (PMF.pure (GBCA.ByAFW.ga2 (afterRet2 P (toRound P u w r) j g))) :=
      Gather.StepOverBracha.ret _ j g hin hbind
        (fun k x hx => holdsIn_ga2 hI r j k (hsubap k x hx)) hQ' hr2
    refine ⟨_, rfl, hh, hph, hr, rfl,
      fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', fun r' => ?_, ?_, ?_⟩
    · by_cases hr' : r' = r
      · subst hr'; simp [LocalState.setP]
      · rw [StageSideRecP.stage_setStage_ne _ _ _ hr']
    · rw [toRound_ret2_retG rfl]
      have hprocs : GBCA.ByAFW.procs (afterRet2 P (toRound P u w r) j g) j
          = { GBCA.ByAFW.procs (toRound P u w r) j with out := some (GBCA.gradeOf P g) } := by
        simp [afterRet2]
      refine roundOverBracha_wstep_two (by simp)
        (roundOverBracha_ret2 (toRound P u w r) j g ?_ rfl hrow)
        (roundOverBracha_retG (afterRet2 P (toRound P u w r) j g) j (GBCA.gradeOf P g)
          (by rw [hprocs]) (by rw [hprocs]; exact hr2))
      change (((u j).2.stage r).ga2.proc).input.isSome = true
      exact Option.isSome_iff_ne_none.mpr hin
    · rw [toRound_ret2_retG rfl]
      have hR₂ : RoundInv P (afterRet2 P (toRound P u w r) j g) :=
        roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow
      exact roundInv_frame hR₂ rfl rfl

/-- The call against an already-called record: the round loop moves, the round
takes its input-enabledness loop and the view stands still. -/
theorem stage_answer_gcallLoop (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) {r : ℕ} {b : Bool} {μ : PMF (AFW.ProcRec P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gcallLoop r j b)) μ) :
    ∃ x : AFW.ProcRec P.n, μ = PMF.pure x ∧ x.2 = p ∧
      c.corrupted = false ∧ c.proc.phase = .toCallG ∧ c.proc.round = r ∧
      c.proc.est = some b ∧
      x.1 = c.setProc { c.proc with phase := .awaitG } ∧
      (GBCA.ByAFW.roundOverBracha P r).step (toRound P u w r) (Sum.inr (.gcallLoop r j b))
        (PMF.pure (toRound P u w r)) := by
  subst hu
  cases h with
  | gcallLoop _ _ _ _ hh hph hr hest hin =>
    exact ⟨_, rfl, rfl, hh, hph, hr, hest, rfl, roundOverBracha_callLoop (toRound P u w r) j b⟩

/-! ### Answering a Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the network state its tag names and no record moves. -/

theorem byzantine_answer (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (hI : StoreInv P u w) (r : ℕ) {k : Fin P.n} (m : Msg P.n)
    (hF : k ∈ w.F) :
    (GBCA.ByAFW.roundOverBracha P r).step (toRound P u w r) (Sum.inl Label.tau)
        (PMF.pure (toRound P u (w.gsent r k m) r)) ∧
      RoundInv P (toRound P u (w.gsent r k m) r) := by
  cases m with
  | ga1 mm =>
    have hrow := Gather.StepOverBracha.byzantine (toGa1 P u w r) k mm hF
    rw [toRound_byzGa1]
    exact ⟨roundOverBracha_ga1Tau (toRound P u w r) hrow,
      roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow⟩
  | ga2 mm =>
    have hrow := Gather.StepOverBracha.byzantine (toGa2 P u w r) k mm hF
    rw [toRound_byzGa2]
    exact ⟨roundOverBracha_ga2Tau (toRound P u w r) hrow,
      roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow⟩
  | brbIn1 i mm =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa1 P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.brbIn (toGa1 P u w r) i) k mm hF)
    rw [toRound_byzIn1]
    exact ⟨roundOverBracha_ga1Tau (toRound P u w r) hrow,
      roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow⟩
  | brbBind1 i mm =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa1 P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.brbBind (toGa1 P u w r) i) k mm hF)
    rw [toRound_byzBind1]
    exact ⟨roundOverBracha_ga1Tau (toRound P u w r) hrow,
      roundInv_ga1 (roundInv_of_storeInv hI r) rfl hrow⟩
  | brbIn2 i mm =>
    have hrow := Gather.StepOverBracha.brbInTau (toGa2 P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.brbIn (toGa2 P u w r) i) k mm hF)
    rw [toRound_byzIn2]
    exact ⟨roundOverBracha_ga2Tau (toRound P u w r) hrow,
      roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow⟩
  | brbBind2 i mm =>
    have hrow := Gather.StepOverBracha.brbBindTau (toGa2 P u w r) i _
      (BRB.BrachaStep.byzantine (Gather.brbBind (toGa2 P u w r) i) k mm hF)
    rw [toRound_byzBind2]
    exact ⟨roundOverBracha_ga2Tau (toRound P u w r) hrow,
      roundInv_ga2 (roundInv_of_storeInv hI r) rfl hrow⟩


/-! ### Assembling a matched run

Three shapes of answer: a visible shared label the four components answer with
one transition each, a hidden rendezvous they answer the same way, and a silent
run of the graded-agreement side alone. -/

/-- A visible shared label: the four components move together, the oracle's
successor free. -/
private theorem match_vis (P : Params) {x : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w' : NetState P.n} {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C' : ∀ _ : Fin P.n, CoreRec P.n} {A' : ANetState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {l : Label P.n} (hl : l ≠ Label.tau)
    (hrel : ∀ o' ∈ ν.support, ProtocolRel P (x, w', o') (G', C', A', o'))
    (hG : (roundFamilyOverBracha P).weakLStep G (Sum.inl l) G')
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inl l) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inl l) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o (Sum.inl l) ν) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      weakStep (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
        (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := match_prod P hrel
  exact ⟨Ω, hr, hb ▸ composedGroup_weakStep P hl hG hC hA hW⟩

/-- A hidden rendezvous: the four components move together and the composed
group reads the move as silent. -/
private theorem match_evt (P : Params) {x : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w' : NetState P.n} {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C' : ∀ _ : Fin P.n, CoreRec P.n} {A' : ANetState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} (e : NetworkEvent P.n)
    (hrel : ∀ o' ∈ ν.support, ProtocolRel P (x, w', o') (G', C', A', o'))
    (hG : (roundFamilyOverBracha P).step G (Sum.inr e) (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inr e) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inr e) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o (Sum.inr e) ν) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      weakTau (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := match_prod P hrel
  refine ⟨Ω, hr, ?_⟩
  rw [hb]
  exact weakTau_of_step rfl
    (composedGroup_of_event P e (composedPre_vis_step P (by simp) hG hC hA hW))

/-- A row internal to the graded-agreement side: the side takes a silent run
and nothing else moves. -/
private theorem match_run (P : Params) {x : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w' : NetState P.n} {G' G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hrel : ProtocolRel P (x, w', o) (G', C, A, o))
    (hG : (roundFamilyOverBracha P).weakLSilent G G') :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (PMF.pure ((x, w', o) : ProtocolState P)) Ω ∧
      weakTau (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := match_pure P hrel
  exact ⟨Ω, hr, hb ▸ composedGroup_weakTau P C A o hG⟩

/-- A composed state that stands still. -/
private theorem match_still (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRel P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (PMF.pure s) Ω ∧
      weakTau (composedGroup P) (PMF.pure t) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := match_pure P h
  exact ⟨Ω, hr, hb ▸ weakTau_refl (composedGroup P) (PMF.pure t)⟩

/-! ### The matching on the silent label

The flat reading's own `terminate` row writes no coordinate the relation reads,
so the composed answer to it is to stand still; the adversary's two injections
are answered by a transition. -/

theorem match_tau (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} (hR : ProtocolRel P (u, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl Label.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      weakTau (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB, hI⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  rcases systemExtended_tau_inv h with ⟨i, y, hstep, rfl⟩ | ⟨w', hn, rfl⟩
  · obtain ⟨b, hh, hret, hcnt, hterm, hy⟩ := stepN_tau_terminate hstep
    obtain rfl : y = ((u i).1, { (u i).2 with terminated := true }) := pureN_inj hy
    have hst : ∀ (j : Fin P.n) (r : ℕ),
        ((Function.update u i ((u i).1,
            { (u i).2 with terminated := true }) j).2.stage r) = ((u j).2.stage r) := by
      intro j r
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne hj]
    have hview : ∀ r, toRound P (Function.update u i ((u i).1,
        { (u i).2 with terminated := true })) w r = toRound P u w r :=
      fun r => toRound_congr (fun j => hst j r)
    refine match_still P ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun j => ?_, rfl, hA, ?_,
        boundInv_of hB (fun j r => by rw [hst j r]) (fun _ hb => hb),
        storeInv_congr hI hview⟩)
    · by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact hC j
      · rw [Function.update_of_ne hj]; exact hC j
    · rw [hGv]
      funext r
      exact (hview r).symm
  · rcases netStep_tau hn with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.gsent r k m := pureN_inj hw
      obtain ⟨hstep, hinv⟩ := byzantine_answer P u w hI r m hF
      have hfam := toRoundFamByz u w r k m
      refine match_run P ((protocolRel_mk P _ _ _ _ _ _ _).mpr
          ⟨hC, rfl, by simpa using hA, hfam.symm,
            boundInv_of hB (fun _ _ => rfl) (fun _ hb => hb),
            storeInv_update hI hfam hinv⟩) ?_
      rw [hGv]
      exact System.weakLSilent_family gOwns isFailN (gActLow P)
        (roundOverBracha_run_one hstep)
    · obtain rfl : w' = w.dput k b := pureN_inj hw
      have hrel : ProtocolRel P (u, w.dput k b, o)
          (G, C, ⟨(w.dput k b).dsent, (w.dput k b).F⟩, o) :=
        (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, rfl,
          by rw [hGv]; funext r; rfl,
          boundInv_of hB (fun _ _ => rfl) (fun _ hb => hb),
          storeInv_congr hI (fun _ => rfl)⟩
      obtain ⟨Ω, hr, hb⟩ := match_pure P hrel
      refine ⟨Ω, hr, ?_⟩
      rw [hb]
      refine weakTau_of_step rfl (composedGroup_of_tau P (composedPre_tau_ABANetwork P ?_))
      rw [hA]
      exact ABANetworkStep.byzantineD ⟨w.dsent, w.F⟩ k b hF


/-! ### The matching on a visible shared label -/

theorem match_lab (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} (hR : ProtocolRel P (u, w, o) (G, C, A, o))
    {l : Label P.n} (hl : l ≠ Label.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      weakStep (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
        (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB, hI⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := systemExtended_lab_inv hl h
  have hWl : (coinOverRoundAlphabet P).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (coinLabelMap_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : ExtendedLabel P.n) ≠ Silent.τ := by simpa using hl
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pureN_inj (netStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_callABA_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_callABA_own (hall i) with ⟨-, -, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w',
          boundInv_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          storeInv_congr hI (fun r => toRound_congr (fun i => by rw [hsame i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) (ABANetworkStep.callABAIdle A id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_callABA_own (hall i) with ⟨hh, hin, hx⟩ | ⟨hloop, hx⟩
      · rw [pureN_inj hx]; exact RoundLoopStep.input _ b hh hin
      · rw [pureN_inj hx]
        by_cases hc : (u i).1.corrupted = true
        · exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
        · exact RoundLoopStep.inputLoop _ b (by simpa using hc) (hloop.resolve_left hc)
    · rw [hfor i hi]; exact RoundLoopStep.callABAIdle _ id b (Ne.symm hi)
  | retABA id b =>
    obtain ⟨hdp, hw⟩ := netStep_retABA hn
    obtain rfl : w' = w := pureN_inj hw
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retABA_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_retABA_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;>
          rw [pureN_inj hx]
      · rw [hfor i hi]
    have hAn : ABANetworkStep P A (Sum.inl (Label.retABA id b)) (PMF.pure A) := by
      rw [hA]
      rcases hdp with hd | hf
      · exact ABANetworkStep.retABA ⟨w'.dsent, w'.F⟩ id b hd
      · exact ABANetworkStep.retByz ⟨w'.dsent, w'.F⟩ id b hf
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w',
          boundInv_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          storeInv_congr hI (fun r => toRound_congr (fun i => by rw [hsame i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) hAn hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_retABA_own (hall i) with ⟨hh, hin, hcnt, hret, hx⟩ | ⟨hc, hx⟩
      · rw [pureN_inj hx]; exact RoundLoopStep.ret _ b hh hcnt hret
      · rw [pureN_inj hx]
        exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w' = w := pureN_inj (netStep_callW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_callW_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_callW_own (hall i) with ⟨-, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w',
          boundInv_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          storeInv_congr hI (fun r => toRound_congr (fun i => by rw [hsame i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) (ABANetworkStep.callWIdle A r id) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_callW_own (hall i) with ⟨hh, hph, hr, hx⟩ | ⟨hc, hx⟩
      · rw [pureN_inj hx]; exact RoundLoopStep.callW _ r hh hph hr
      · rw [pureN_inj hx]
        exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w' = w := pureN_inj (netStep_retW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retW_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_retW_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w',
          boundInv_of hB (fun i r => by rw [hsame i]) (fun _ hb => hb),
          storeInv_congr hI (fun r => toRound_congr (fun i => by rw [hsame i]))⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_idle P G hLne (by simp) not_false))
      (fun i => ?_) (ABANetworkStep.retWIdle A r id co) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_retW_own (hall i) with ⟨hh, hph, hr, hgr, hx⟩ | ⟨hc, hx⟩
      · rw [pureN_inj hx]; exact RoundLoopStep.retW _ r co hh hph hr hgr
      · rw [pureN_inj hx]
        exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact RoundLoopStep.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain ⟨hnew, hbud, hw⟩ := netStep_fail hn
    obtain rfl : w' = NetStateP.corrupt P k w := pureN_inj hw
    have hfor : ∀ i, i ≠ k → x i = u i := fun i hi =>
      pureN_inj (stepN_fail_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = k
      · subst hi
        rcases stepN_fail_own (hall i) with ⟨-, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    have hview : ∀ r, toRound P x (NetStateP.corrupt P k w) r
        = gActLow P (Sum.inl (Label.fail k)) (toRound P u w r) := fun r =>
      (toRound_congr (fun i => by rw [hsame i])).trans (toRound_fail u w r k)
    have hSI : StoreInv P x (NetStateP.corrupt P k w) := by
      intro r
      rw [hview r]
      exact roundInv_both (roundInv_of_storeInv hI r) (Gather.StepOverBracha.fail _ k)
        (Gather.StepOverBracha.fail _ k)
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, ?_, ?_,
          boundInv_of hB (fun i r => by rw [hsame i]) (fun _ hb => by simpa using hb),
          hSI⟩)
      (System.weakLStep_of_step hLne (roundFamilyOverBracha_fail P G k)) (fun i => ?_)
      (ABANetworkStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    · rw [hA]
      unfold ANetState.corrupt NetStateP.corrupt
      split_ifs <;> rfl
    · funext r
      rw [hGv]
      exact (hview r).symm
    · by_cases hi : i = k
      · subst hi
        rcases stepN_fail_own (hall i) with ⟨hh, hx⟩ | ⟨hh, hx⟩
        · rw [hCeq i, pureN_inj hx]; exact RoundLoopStep.failSelf _ hh
        · rw [hCeq i, pureN_inj hx]
          exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = (w.gsent r id (gCallPayload P id b)).writeGhost (ghostStep P)
        (Sum.inl (Label.callG r id b)) := pureN_inj (netStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_callG_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hest, hx1, hoff, hga2, hlow, hinv⟩ :=
      stage_answer_callG P w (u := u) (j := id) rfl hI (stageRow_of_own rfl (hall id))
    obtain rfl : x id = y := pureN_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.stage r'
        = ((Function.update u id (x id)) i).2.stage r' := by
      intro i r'
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ), (((x i).2.stage r'').ga2.proc).input
        = (((u i).2.stage r'').ga2.proc).input := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hga2 r''
      · rw [hfor i hi]
    have hfam : (fun r' => toRound P x
          ((w.gsent r id (gCallPayload P id b)).writeGhost (ghostStep P)
            (Sum.inl (Label.callG r id b))) r')
        = Function.update (fun r' => toRound P u w r') r
          (toRound P (Function.update u id (x id))
            ((w.gsent r id (gCallPayload P id b)).writeGhost (ghostStep P)
              (Sum.inl (Label.callG r id b))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact toRound_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr']
        exact (toRound_congr (fun i => by
          by_cases hi : i = id
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])).trans (toRound_otherSent u w hr' id _ rfl)
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, hfam.symm,
          boundInv_of hB hxg (fun _ hb => writeGhost_bound _ (by simpa using hb)),
          storeInv_update hI hfam hinv⟩)
      (by rw [hGv]; exact roundFamilyOverBracha_weakStep P (by simp) hlow)
      (fun i => ?_) (ABANetworkStep.callGIdle A r id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rw [hx1]
      exact RoundLoopStep.callG _ r b hh hph hrr hest
    · rw [hfor i hi]; exact RoundLoopStep.callGIdle _ r id b (Ne.symm hi)
  | retG r id out bnd =>
    obtain ⟨hbnd, hw⟩ := netStep_retG hn
    obtain rfl : w' = w.writeGhost (ghostStep P)
        (Sum.inl (Label.retG r id out bnd)) := pureN_inj hw
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retG_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hx1, hoff, hga2, hlow, hinv⟩ :=
      stage_answer_retG P w (u := u) (j := id) rfl hI hbnd (hB r)
        (stageRow_of_own rfl (hall id))
    obtain rfl : x id = y := pureN_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.stage r'
        = ((Function.update u id (x id)) i).2.stage r' := by
      intro i r'
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hxg : ∀ (i : Fin P.n) (r'' : ℕ), (((x i).2.stage r'').ga2.proc).input
        = (((u i).2.stage r'').ga2.proc).input := by
      intro i r''
      by_cases hi : i = id
      · subst hi; exact hga2 r''
      · rw [hfor i hi]
    have hfam : (fun r' => toRound P x
          (w.writeGhost (ghostStep P) (Sum.inl (Label.retG r id out bnd))) r')
        = Function.update (fun r' => toRound P u w r') r
          (toRound P (Function.update u id (x id))
            (w.writeGhost (ghostStep P) (Sum.inl (Label.retG r id out bnd))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact toRound_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr',
          toRound_writeGhost_ne (L := Sum.inl (Label.retG r id out bnd)) _ _ rfl hr']
        exact toRound_congr (fun i => by
          by_cases hi : i = id
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])
    refine match_vis P hl (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, hfam.symm,
          boundInv_of hB hxg (fun _ hb => writeGhost_bound _ hb),
          storeInv_update hI hfam hinv⟩)
      (by rw [hGv]; exact roundFamilyOverBracha_weakStep P (by simp) hlow)
      (fun i => ?_) (ABANetworkStep.retGIdle A r id out bnd) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rw [hx1]
      exact RoundLoopStep.retG _ r out bnd hh hph hrr
    · rw [hfor i hi]; exact RoundLoopStep.retGIdle _ r id out bnd (Ne.symm hi)


/-! ### The matching on a rendezvous of the flat reading

A send and a delivery are internal to the round, so the composed reading
answers them with a silent run of the graded-agreement side; the DECIDED rows,
the fused coin return and the handshake rows are answered by the same
rendezvous. -/

theorem match_event (P : Params) {u : ∀ _ : Fin P.n, AFW.ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} (hR : ProtocolRel P (u, w, o) (G, C, A, o))
    (e : NetworkEvent P.n (Msg P.n)) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (u, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      weakTau (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv, hB, hI⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := systemExtended_event_inv h
  have hrun : ∀ {G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}, ν = PMF.pure o →
      ProtocolRel P (x, w', o) (G', C, A, o) →
      (roundFamilyOverBracha P).weakLSilent G G' →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRel P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        weakTau (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P))
          (Ω.bind id) := by
    intro G' hν hrel hGs
    subst hν
    obtain ⟨Ω, hr, hs⟩ := match_run P hrel hGs
    refine ⟨Ω, ?_, hs⟩
    rwa [prodPMF_pure_pure, prodPMF_pure_pure]
  cases e with
  | gbcaSend r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaSend r j m) ν).mp hWs
    obtain rfl : w' = (w.gsent r j m).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.gbcaSend r j m)) := pureN_inj (netStep_gbcaSend hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pureN_inj (stepN_gbcaSend_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hcore, hoff, hlow, hinv⟩ :=
      stage_answer_gbcaSend P w (u := u) (j := j) rfl hI (stageRow_of_own rfl (hall j))
    obtain rfl : x j = y := pureN_inj hy
    have hxc : ∀ (i : Fin P.n) (r' : ℕ), (x i).2.stage r'
        = ((Function.update u j (x j)) i).2.stage r' := by
      intro i r'
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    have hfam : (fun r' => toRound P x
          ((w.gsent r j m).writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaSend r j m))) r')
        = Function.update (fun r' => toRound P u w r') r
          (toRound P (Function.update u j (x j))
            ((w.gsent r j m).writeGhost (ghostStep P)
              (Sum.inr (NetworkEvent.gbcaSend r j m))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact toRound_congr (fun i => hxc i r')
      · rw [Function.update_of_ne hr']
        exact (toRound_congr (fun i => by
          by_cases hi : i = j
          · subst hi; exact hoff r' hr'
          · rw [hfor i hi])).trans (toRound_otherSent u w hr' j m rfl)
    have hbI : BoundInv P x
        ((w.gsent r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j m))) := by
      rcases stage_gbcaSend_ga2 P (stageRow_of_own rfl (hall j)) with hkeep | ⟨q, y, rfl⟩
      · refine boundInv_of hB (fun i r'' => ?_)
          (fun _ hb => writeGhost_bound _ (by simpa using hb))
        by_cases hi : i = j
        · subst hi; exact hkeep _ rfl r''
        · rw [hfor i hi]
      · intro r'' i hne
        by_cases hr'' : r'' = r
        · subst hr''
          rw [writeGhost_ghostRec_self _ rfl]
          simp [ghostStep]
        · rw [writeGhost_ghostRec_ne _ rfl hr'']
          refine hB r'' i ?_
          by_cases hi : i = j
          · subst hi; rwa [hoff r'' hr''] at hne
          · rwa [hfor i hi] at hne
    refine hrun rfl ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i => by
        rw [hCeq i]
        by_cases hi : i = j
        · subst hi; rw [hcore]
        · rw [hfor i hi], rfl, by rw [hA]; simp, hfam.symm, hbI,
        storeInv_update hI hfam hinv⟩) ?_
    rw [hGv]
    exact System.weakLSilent_family gOwns isFailN (gActLow P) hlow
  | gbcaDeliver r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaDeliver r i k m) ν).mp hWs
    obtain ⟨hsent, hw⟩ := netStep_gbcaDeliver hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m)) :=
      pureN_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pureN_inj (stepN_gbcaDeliver_foreign (Ne.symm hi) (hall i'))
    obtain ⟨y, hy, hcore, hoff, hga2, hlow, hinv⟩ :=
      stage_answer_gbcaDeliver P w (u := u) (j := i) rfl hI hsent
        (stageRow_of_own rfl (hall i))
    obtain rfl : x i = y := pureN_inj hy
    have hxc : ∀ (i' : Fin P.n) (r' : ℕ), (x i').2.stage r'
        = ((Function.update u i (x i)) i').2.stage r' := by
      intro i' r'
      by_cases hi : i' = i
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i' hi]
    have hxg : ∀ (i' : Fin P.n) (r'' : ℕ), (((x i').2.stage r'').ga2.proc).input
        = (((u i').2.stage r'').ga2.proc).input := by
      intro i' r''
      by_cases hi : i' = i
      · subst hi; exact hga2 r''
      · rw [hfor i' hi]
    have hfam : (fun r' => toRound P x
          (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m))) r')
        = Function.update (fun r' => toRound P u w r') r
          (toRound P (Function.update u i (x i))
            (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gbcaDeliver r i k m))) r) := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact toRound_congr (fun i' => hxc i' r')
      · rw [Function.update_of_ne hr',
          toRound_writeGhost_ne (L := Sum.inr (NetworkEvent.gbcaDeliver r i k m)) _ _ rfl hr']
        exact toRound_congr (fun i' => by
          by_cases hi : i' = i
          · subst hi; exact hoff r' hr'
          · rw [hfor i' hi])
    refine hrun rfl ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i' => by
        rw [hCeq i']
        by_cases hi : i' = i
        · subst hi; rw [hcore]
        · rw [hfor i' hi], rfl, by rw [hA]; simp, hfam.symm,
        boundInv_of hB hxg (fun _ hb => writeGhost_bound _ hb),
        storeInv_update hI hfam hinv⟩) ?_
    rw [hGv]
    exact System.weakLSilent_family gOwns isFailN (gActLow P) hlow
  | decidedSend j b =>
    obtain ⟨hd, hw⟩ := netStep_decidedSend hn
    obtain rfl : w' = w.dput j b := pureN_inj hw
    have hx : ∀ i, x i = u i := by
      intro i
      by_cases hi : i = j
      · subst hi
        rcases stepN_decidedSend_self (hall i) with ⟨-, -, -, hxi⟩ | ⟨-, hxi⟩ <;>
          exact pureN_inj hxi
      · exact pureN_inj (stepN_decidedSend_foreign (Ne.symm hi) (hall i))
    refine match_evt P (.decidedSend j b) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, by rw [hA]; rfl, by
          rw [hGv]; funext r; exact (toRound_congr (fun i => by rw [hx i])).symm,
          boundInv_of hB (fun i r => by rw [hx i]) (fun _ hb => hb),
          storeInv_congr hI (fun r => toRound_congr (fun i => by rw [hx i]))⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.decidedSend ⟨w.dsent, w.F⟩ j b hd) hWs
    rw [hCeq i]
    by_cases hi : i = j
    · subst hi
      rcases stepN_decidedSend_self (hall i) with ⟨hh, hin, hcnt, -⟩ | ⟨hc, -⟩
      · exact RoundLoopStep.dsndRelay _ b hh hcnt
      · exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
    · exact RoundLoopStep.dsndIdle _ j b (Ne.symm hi)
  | decidedDeliver i k b =>
    obtain ⟨hd, hw⟩ := netStep_decidedDeliver hn
    obtain rfl : w' = w := pureN_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pureN_inj (stepN_decidedDeliver_foreign (Ne.symm hi) (hall i'))
    obtain ⟨hh, hr, hxi⟩ := stepN_decidedDeliver_self (hall i)
    have hsame : ∀ i', (x i').2 = (u i').2 := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [pureN_inj hxi]
      · rw [hfor i' hi]
    refine match_evt P (.decidedDeliver i k b) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w',
          boundInv_of hB (fun i' r => by rw [hsame i']) (fun _ hb => hb),
          storeInv_congr hI (fun r => toRound_congr (fun i' => by rw [hsame i']))⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i' => ?_)
      (hA ▸ ABANetworkStep.decidedDeliver ⟨w'.dsent, w'.F⟩ i k b hd) hWs
    rw [hCeq i']
    by_cases hi : i' = i
    · subst hi; rw [pureN_inj hxi]; exact RoundLoopStep.ddlvRecv _ k b hh hr
    · rw [hfor i' hi]; exact RoundLoopStep.ddlvIdle _ i k b (Ne.symm hi)
  | retWPub r id cc b =>
    obtain rfl : w' = (w.dput id b).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.retWPub r id cc b)) := pureN_inj (netStep_retWPub hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retWPub_foreign (Ne.symm hi) (hall i))
    obtain ⟨hh, hph, hr, hgr, hxi⟩ := stepN_retWPub_self (hall id)
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; rw [pureN_inj hxi]
      · rw [hfor i hi]
    have hview : ∀ r', toRound P x ((w.dput id b).writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.retWPub r id cc b))) r' = toRound P u w r' := fun r' =>
      (toRound_congr (fun i => by rw [hsame i])).trans
        (toRound_ghostId (Sum.inr (NetworkEvent.retWPub r id cc b)) (fun _ _ => rfl) u _ r')
    refine match_evt P (.retWPub r id cc b) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; rfl, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInv_of hB (fun i r' => by rw [hsame i])
            (fun _ hb => writeGhost_bound _ hb),
          storeInv_congr hI hview⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.retWPub ⟨w.dsent, w.F⟩ r id cc b) hWs
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [pureN_inj hxi]
      exact RoundLoopStep.retWPub _ r cc b hh hph hr hgr
    · rw [hfor i hi]; exact RoundLoopStep.retWPubIdle _ r id cc b (Ne.symm hi)
  | gcallLoop r id b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gcallLoop r id b) ν).mp hWs
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gcallLoop r id b)) :=
      pureN_inj (netStep_gcallLoop hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_gcallLoop_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hy2, hh, hph, hrr, hest, hx1, hlow⟩ :=
      stage_answer_gcallLoop P w (u := u) (j := id) rfl
        (stageRow_of_own rfl (hall id))
    obtain rfl : x id = y := pureN_inj hy
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; exact hy2
      · rw [hfor i hi]
    have hview : ∀ r', toRound P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.gcallLoop r id b))) r'
          = toRound P u w r' := fun r' =>
      (toRound_congr (fun i => by rw [hsame i])).trans
        (toRound_ghostId (Sum.inr (NetworkEvent.gcallLoop r id b)) (fun _ _ => rfl) u w r')
    refine match_evt P (.gcallLoop r id b) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInv_of hB (fun i r' => by rw [hsame i])
            (fun _ hb => writeGhost_bound _ hb),
          storeInv_congr hI hview⟩)
      (roundFamilyOverBracha_owned_id P G r (by simp) (by rw [hGv]; exact hlow))
      (fun i => ?_) (ABANetworkStep.gcallLoop A r id b) hWs
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [hx1]; exact RoundLoopStep.gcallLoop _ r b hh hph hrr hest
    · rw [hfor i hi]; exact RoundLoopStep.gcallLoopIdle _ r id b (Ne.symm hi)
  | byzantineCallGLoop r k b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_byzantineCallGLoop r k b) ν).mp hWs
    obtain ⟨hF, hw⟩ := netStep_byzantineCallGLoop hn
    obtain rfl : w' = w.writeGhost (ghostStep P)
        (Sum.inr (NetworkEvent.byzantineCallGLoop r k b)) := pureN_inj hw
    have hx : ∀ i, x i = u i := fun i => pureN_inj (stepN_byzantineCallGLoop (hall i))
    have hview : ∀ r', toRound P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallGLoop r k b))) r'
          = toRound P u w r' := fun r' =>
      (toRound_congr (fun i => by rw [hx i])).trans
        (toRound_ghostId (Sum.inr (NetworkEvent.byzantineCallGLoop r k b)) (fun _ _ => rfl) u w r')
    refine match_evt P (.byzantineCallGLoop r k b) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInv_of hB (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb),
          storeInv_congr hI hview⟩)
      (roundFamilyOverBracha_owned_id P G r (by simp)
        (by rw [hGv]; exact roundOverBracha_byzantineCallLoop (toRound P u w r) k b))
      (fun i => ?_) (hA ▸ ABANetworkStep.byzantineCallGLoop ⟨w.dsent, w.F⟩ r k b hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineCallGLoopIdle _ r k b
  | byzantineCallW r k =>
    obtain ⟨hF, hw⟩ := netStep_byzantineCallW hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallW r k)) :=
      pureN_inj hw
    have hx : ∀ i, x i = u i := fun i => pureN_inj (stepN_byzantineCallW (hall i))
    have hview : ∀ r', toRound P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineCallW r k))) r'
          = toRound P u w r' := fun r' =>
      (toRound_congr (fun i => by rw [hx i])).trans
        (toRound_ghostId (Sum.inr (NetworkEvent.byzantineCallW r k)) (fun _ _ => rfl) u w r')
    refine match_evt P (.byzantineCallW r k) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInv_of hB (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb),
          storeInv_congr hI hview⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.byzantineCallW ⟨w.dsent, w.F⟩ r k hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineCallWIdle _ r k
  | byzantineRetW r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzantineRetW hn
    obtain rfl : w' = w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineRetW r k b)) :=
      pureN_inj hw
    have hx : ∀ i, x i = u i := fun i => pureN_inj (stepN_byzantineRetW (hall i))
    have hview : ∀ r', toRound P x
        (w.writeGhost (ghostStep P) (Sum.inr (NetworkEvent.byzantineRetW r k b))) r'
          = toRound P u w r' := fun r' =>
      (toRound_congr (fun i => by rw [hx i])).trans
        (toRound_ghostId (Sum.inr (NetworkEvent.byzantineRetW r k b)) (fun _ _ => rfl) u w r')
    refine match_evt P (.byzantineRetW r k b) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by rw [hGv]; funext r'; exact (hview r').symm,
          boundInv_of hB (fun i r' => by rw [hx i])
            (fun _ hb => writeGhost_bound _ hb),
          storeInv_congr hI hview⟩)
      (roundFamilyOverBracha_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ ABANetworkStep.byzantineRetW ⟨w.dsent, w.F⟩ r k b hF) hWs
    rw [hCeq i]
    exact RoundLoopStep.byzantineRetWIdle _ r k b
  | byzantineCallG r k b => exact (stepN_byzantineCallG_noStep (hall k)).elim
  | byzantineRetG r k out bnd => exact (stepN_byzantineRetG_noStep (hall k)).elim


/-! ### The matching at the group and at the system -/

/-- **The matching at the group level**: the rendezvous alphabet is hidden on
both sides, so a hidden rendezvous of the flat reading is answered by a silent
run of the composed group. -/
theorem match_group (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRel P s t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolHidden P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
        ((l = Label.tau ∧ weakTau (composedGroup P) (PMF.pure t) (Ω.bind id)) ∨
          (l ≠ Label.tau ∧ weakStep (composedGroup P) (PMF.pure t) l (Ω.bind id))) := by
  obtain ⟨u, w, o⟩ := s
  obtain ⟨G, C, A, o'⟩ := t
  obtain ⟨hC, ho, hA, hGv, hB, hI⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  have hR' : ProtocolRel P (u, w, o) (G, C, A, o) :=
    (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hGv, hB, hI⟩
  rcases (systemHidden_step_iff _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := match_event P hR' e hstep
    exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
  · by_cases hl : l = Label.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := match_tau P hR' hstep
      exact ⟨Ω, hrel, Or.inl ⟨rfl, hs⟩⟩
    · obtain ⟨Ω, hrel, hs⟩ := match_lab P hR' hl hstep
      exact ⟨Ω, hrel, Or.inr ⟨hl, hs⟩⟩

/-- **The matching at the system level**: a hidden sub-protocol label is silent
on both sides, and every other label is answered on the nose or by a run. -/
theorem match_step (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRel P s t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (system_step_iff s l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_group P hR hg
    rcases hlay with ⟨rfl, -⟩ | ⟨-, hlay⟩
    · exact absurd hmem Label.tau_not_mem_hiddenAPI
    · exact ⟨Ω, hrel, Or.inl ⟨rfl,
        weakTau_of_weakStep_mem (composedGroup P) (Label.hiddenAPI P.n) hmem hlay⟩⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_group P hR hg
    rcases hlay with ⟨rfl, hlay⟩ | ⟨hne, hlay⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl,
        weakTau_abstract (composedGroup P) (Label.hiddenAPI P.n) hlay⟩⟩
    · exact ⟨Ω, hrel, Or.inr ⟨hne,
        weakStep_abstract (composedGroup P) (Label.hiddenAPI P.n) hnm hlay⟩⟩

/-- **The gather-based protocol forward-simulates into its composed reading**,
along the Dirac lift of the view. -/
theorem protocolSim (P : Params) :
    ProbabilisticForwardSimulation (protocol P) (composed P)
      (diracRel (ProtocolRel P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRel_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact match_step P hR hstep

/-- **The composition inclusion**: every trace distribution the gather-based
protocol achieves is achieved by its composed reading. -/
theorem protocol_composed (P : Params) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (composed P) :=
  (protocolSim P).achievableTraceDists_subset

/-! ### The headlines

The gather-based protocol reaches the ABA specification along the composed
reading it was cut into, and safety transfers to it. -/

/-- **Trace-distribution refinement of the gather-based protocol**: every trace
distribution achievable by the protocol as it runs is achievable by the ABA
specification. The composition inclusion gives the first step, the substitution
and the core simulation the rest. -/
theorem refines (P : Params) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (protocol_composed P) (composed_refines P)

/-- **Correctness of the gather-based protocol**: every positive-probability
trace of the protocol as it runs satisfies Validity and Agreement. No side
condition on the trace: the corruption budget is a guard of the network
adversary's own `fail` row, so every execution is in budget by construction. -/
theorem main (P : Params) :
    ∀ D ∈ achievableTraceDists (protocol P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed gather-based simulation** `protocol ⊑ ABA.spec`: the
composition simulation joined with the chain from the composed reading by
Result 2. -/
noncomputable def chainSim (P : Params) :
    ProbabilisticForwardSimulation (protocol P) (spec P)
      (compRel (diracRel (ProtocolRel P))
        (compRel
          (compRel (parallelRel (diracRel (RlowAll P)))
            (compRel (parallelRel (diracRel (RidealAll P)))
              (parallelRel (diracRel (RpairAll P)))))
          (coreRel P))) :=
  (protocolSim P).trans (chainSimComposed P)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.AFW.protocolSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolSim

/-- info: 'PLTS.ABA.AFW.protocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_composed

/-- info: 'PLTS.ABA.AFW.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refines

/-- info: 'PLTS.ABA.AFW.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'PLTS.ABA.AFW.chainSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainSim


end AFW

end ABA
end PLTS
