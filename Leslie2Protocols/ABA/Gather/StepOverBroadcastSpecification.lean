/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.CompositionStepInversion
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The rows of the gather instance over the broadcast specification

`StepOverBroadcastSpecification` is the rule table of `Gather.instanceOverBroadcastSpecification`
(`ABA/Gather/Composition.lean`) — the `n` gather programs beside the gather network, in parallel
with `2n` lifted broadcast specifications — stated over the composition's state through the four
views `gatherTier`, `inputBroadcasts`, `bindBroadcasts`, `core`. It is a relation on that state; the
system is the composition.

`instanceOverBroadcastSpecification_step_iff_row` is the row characterisation: at a specification
label `l₀`, the transitions of the composition over the labels `specificationLabelMap` sends to
`l₀` are exactly the `l₀`-rows of `StepOverBroadcastSpecification`, on the same state and with the
same distribution.

## The four rows of a call

A broadcast specification answers `call x` on two rows, the call and the
input-enabledness loop, and the composition reads it along `inputBroadcastLabelMap id`, which
puts both rows under the gather label `call id x` and both under the gather call
loop. The gather program writes its record on the first label and is unchanged
on the second. The four combinations are four rows: `call` (both record),
`callSpecificationLoop` (the program records, the instance loops), `callProgramLoop` (the
instance records, the program loops) and `callLoop` (neither moves). The same
split reaches the bind call, whose two rows are `bindCall` and
`bindCallSpecificationLoop`.

## The corrupted set

Each broadcast specification carries its own corrupted set, kept equal to the gather network's by
the `fail` row. A commit guard therefore reads the corrupted set of the instance it commits in. -/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X]

/-! ### Reading a lifted broadcast specification

A lifted broadcast specification is the specification read along `BRB.specificationLabelMap`
and then along the composition's pullback. The lemmas below pass between its
transitions and the specification's rows. -/

/-- A transition of a lifted broadcast specification is a specification row at
the label `BRB.specificationLabelMap` projects to. -/
theorem specificationOverInstanceAlphabet_step_row {M : Type} {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.SpecState P.n M} {l : BRB.InstanceLabel P.n M} {l₀ : BRB.Label P.n M}
    (hl : BRB.specificationLabelMap P.n M l = some l₀)
    (h : (BRB.specificationOverInstanceAlphabet P ldr M).step s l (PMF.pure s')) : BRB.Step P ldr s
      l₀ (PMF.pure s') :=
  (System.mapIdle_step_some hl _).mp h

/-- A specification row is a transition of the lifted specification at any
label `BRB.specificationLabelMap` projects to it. -/
theorem row_specificationOverInstanceAlphabet_step {M : Type} {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.SpecState P.n M} {l : BRB.InstanceLabel P.n M} {l₀ : BRB.Label P.n M}
    (hl : BRB.specificationLabelMap P.n M l = some l₀)
    (h : BRB.Step P ldr s l₀ (PMF.pure s')) : (BRB.specificationOverInstanceAlphabet P ldr M).step s
      l (PMF.pure s') :=
  (System.mapIdle_step_some hl _).mpr h

section SpecInversion

variable {M : Type} {P : Parameters} {ldr : Fin P.n} {s : BRB.SpecState P.n M}
  {μ : PMF (BRB.SpecState P.n M)}

/-- The two rows of a call: the record write and the loop. -/
theorem specStep_call {m : M} (h : BRB.Step P ldr s (.call m) μ) :
    (s.input = none ∧ μ = PMF.pure { s with input := some m }) ∨ μ = PMF.pure s := by
  cases h
  case call => exact Or.inl ⟨by assumption, rfl⟩
  case callLoop => exact Or.inr rfl

/-- The one silent row: the commit. -/
theorem specStep_tau (h : BRB.Step P ldr s .tau μ) :
    ∃ m : M, s.val = none ∧ (ldr ∈ s.F ∨ s.input = some m) ∧
      μ = PMF.pure { s with val := some m } := by
  cases h
  case commit m hv hm => exact ⟨m, hv, hm, rfl⟩

/-- The one return row. -/
theorem specStep_ret {id : Fin P.n} {m : M} (h : BRB.Step P ldr s (.ret id m) μ) :
    s.val = some m ∧ s.ret id = false ∧
      μ = PMF.pure { s with ret := Function.update s.ret id true } := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

/-- The one corruption row. -/
theorem specStep_fail {id : Fin P.n} (h : BRB.Step P ldr s (.fail id) μ) :
    μ = PMF.pure (s.corrupt P id) := by
  cases h; rfl

end SpecInversion

/-! ### The rows -/

/-- The rows of the gather instance over the broadcast specification
(`Gather.instanceOverBroadcastSpecification`), stated over the composition's state: one constructor
per case of `Gather.instanceOverBroadcastSpecification_step_iff_row`. All transitions are Dirac. -/
inductive StepOverBroadcastSpecification (P : Parameters) :
    StateOverBroadcastSpecification P.n X → Label P.n X → PMF (StateOverBroadcastSpecification P.n
      X) → Prop
  /-- The call arrives: the gather record and the input instance both record
  the payload. -/
  | call (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (x : X)
      (h : ((gatherTier s).process id).input = none) (hb : (inputBroadcasts s id).input = none) :
      StepOverBroadcastSpecification P s (.call id x)
        (PMF.pure (setInputBroadcasts (setGatherTier s ((gatherTier s).setProcess id { (gatherTier
          s).process id with input := some x }))
          (Function.update (inputBroadcasts s) id { inputBroadcasts s id with input := some x })))
  /-- The call arrives and the input instance answers on its loop row: the
  gather record alone moves. -/
  | callSpecificationLoop (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (x : X)
      (h : ((gatherTier s).process id).input = none) :
      StepOverBroadcastSpecification P s (.call id x)
        (PMF.pure (setGatherTier s ((gatherTier s).setProcess id { (gatherTier s).process id with
          input := some x })))
  /-- The gather program answers on its loop row and the input instance records
  the payload: the input instance alone moves. -/
  | callProgramLoop (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (x : X)
      (hb : (inputBroadcasts s id).input = none) :
      StepOverBroadcastSpecification P s (.call id x)
        (PMF.pure (setInputBroadcasts s (Function.update (inputBroadcasts s) id
          { inputBroadcasts s id with input := some x })))
  /-- Input-enabledness loop for `call`: nothing moves. -/
  | callLoop (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (x : X) :
      StepOverBroadcastSpecification P s (.call id x) (PMF.pure s)
  /-- An input instance commits: anything under a corrupted leader, the
  leader's input otherwise. -/
  | commitInputEntry (s : StateOverBroadcastSpecification P.n X) (k : Fin P.n) (v : X)
      (hv : (inputBroadcasts s k).val = none) (hm : k ∈ (inputBroadcasts s k).F ∨ (inputBroadcasts s
        k).input = some v) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setInputBroadcasts s (Function.update (inputBroadcasts s) k { inputBroadcasts s k
          with val := some v })))
  /-- A bind instance commits. -/
  | commitBindEntry (s : StateOverBroadcastSpecification P.n X) (q : Fin P.n) (U : AcceptedPairs P.n
    X)
      (hv : (bindBroadcasts s q).val = none)
      (hm : q ∈ (bindBroadcasts s q).F ∨ (bindBroadcasts s q).input = some U) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setBindBroadcasts s (Function.update (bindBroadcasts s) q
          { bindBroadcasts s q with val := some U })))
  /-- Asynchronous delivery on the gather network. -/
  | deliver (s : StateOverBroadcastSpecification P.n X) (i j : Fin P.n) (m : Message P.n X)
      (h : m ∈ (gatherTier s).sent j) :
      StepOverBroadcastSpecification P s .tau (PMF.pure (setGatherTier s ((gatherTier
        s).receiveMessage i j m)))
  /-- `ECHO`: the process is called and its accepted pairs number at least
  `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is those pairs,
  `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | echo (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hcard : P.n - P.f ≤ ((gatherTier s).process j).accepted.card)
      (hsend : ((gatherTier s).process j).sentEcho = none) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherTier s (((gatherTier s).setProcess j
          { (gatherTier s).process j with sentEcho := some ((gatherTier s).process j).accepted
            }).multicast j
            (.echo ((gatherTier s).process j).accepted))))
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in the
  vote payload, are delivered here, and the process has multicast its own
  `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO` before `VOTE`. -/
  | vote (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hech : ((gatherTier s).process j).sentEcho ≠ none)
      (happ : approvedBy ((gatherTier s).process j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A,
          Message.echo A ∈ (gatherTier s).received j q ∧ approvedBy ((gatherTier s).process j) A ∧ A
            ⊆ U)
      (hsend : ((gatherTier s).process j).sentVote = none) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherTier s (((gatherTier s).setProcess j
          { (gatherTier s).process j with sentVote := some U }).multicast j (.vote U))))
  /-- `BIND`: `n − f` senders' approved `VOTE` payloads, each contained in the
  bind payload, are delivered here, and the bind instance records the payload.
  The process has multicast its own `VOTE` and has not called its own bind
  broadcast. The main thread of AFW25's Algorithm 5 sends `VOTE` before `BIND`,
  and sends `BIND` once, at line 17. The payload handed to the broadcast is
  written to the gather record. -/
  | bindCall (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hvot : ((gatherTier s).process j).sentVote ≠ none)
      (hsnd : ((gatherTier s).process j).sentBind = none)
      (happ : approvedBy ((gatherTier s).process j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Message.vote W ∈ (gatherTier s).received j q ∧ approvedBy ((gatherTier s).process j) W ∧ W
            ⊆ U)
      (hb : (bindBroadcasts s j).input = none) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setBindBroadcasts (setGatherTier s ((gatherTier s).setProcess j
            { (gatherTier s).process j with sentBind := some U }))
          (Function.update (bindBroadcasts s) j { bindBroadcasts s j with input := some U })))
  /-- `BIND` with the bind instance answering on its loop row: the payload handed
  to the broadcast is written to the gather record alone. The process has
  multicast its own `VOTE` and has not called its own bind broadcast. -/
  | bindCallSpecificationLoop (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (U : AcceptedPairs
    P.n X)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hvot : ((gatherTier s).process j).sentVote ≠ none)
      (hsnd : ((gatherTier s).process j).sentBind = none)
      (happ : approvedBy ((gatherTier s).process j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Message.vote W ∈ (gatherTier s).received j q ∧ approvedBy ((gatherTier s).process j) W ∧ W
            ⊆ U) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherTier s ((gatherTier s).setProcess j
          { (gatherTier s).process j with sentBind := some U })))
  /-- Byzantine injection on the gather network. -/
  | byzantine (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (m : Message P.n X) (h : j ∈
    (gatherTier s).F) :
      StepOverBroadcastSpecification P s .tau (PMF.pure (setGatherTier s ((gatherTier s).multicast j
        m)))
  /-- An input instance returns its committed value to `j`, which files it as its returned value. -/
  | inputBroadcastRet (s : StateOverBroadcastSpecification P.n X) (k j : Fin P.n) (v : X)
      (hv : (inputBroadcasts s k).val = some v) (hr : (inputBroadcasts s k).ret j = false) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setInputBroadcasts (setGatherTier s ((gatherTier s).setProcess j
            { (gatherTier s).process j with
              inputBroadcastReturned := Function.update ((gatherTier s).process
                j).inputBroadcastReturned k (some v) }))
          (Function.update (inputBroadcasts s) k
            { inputBroadcasts s k with ret := Function.update (inputBroadcasts s k).ret j true })))
  /-- A bind instance returns its committed payload to `j`, which files it as its returned value. -/
  | bindRet (s : StateOverBroadcastSpecification P.n X) (q j : Fin P.n) (U : AcceptedPairs P.n X)
      (hv : (bindBroadcasts s q).val = some U) (hr : (bindBroadcasts s q).ret j = false) :
      StepOverBroadcastSpecification P s .tau
        (PMF.pure (setBindBroadcasts (setGatherTier s ((gatherTier s).setProcess j
            { (gatherTier s).process j with
              bindBroadcastReturned := Function.update ((gatherTier s).process
                j).bindBroadcastReturned q (some U) }))
          (Function.update (bindBroadcasts s) q
            { bindBroadcasts s q with ret := Function.update (bindBroadcasts s q).ret j true })))
  /-- Return: the output's entries are held here, `n − f` bind payloads held
  here are sub-maps of it, and the returner has called its own bind broadcast.
  The `BIND` broadcast of AFW25's Algorithm 5, line 17, precedes the wait of line
  18. The label carries the instance's core, which this row writes if it is
  unwritten. -/
  | ret (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : ((gatherTier s).process id).input ≠ none)
      (hbind : ((gatherTier s).process id).sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn ((gatherTier s).process id) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          holdsBindBroadcastReturn ((gatherTier s).process id) q U ∧ AcceptedPairs.subMap U g)
      (hr : ((gatherTier s).process id).returned = false) :
      StepOverBroadcastSpecification P s (.ret id g ((core s).getD (coreOfNetwork P (gatherTier
        s).2)))
        (PMF.pure (setCore (setGatherTier s ((gatherTier s).setProcess id
          { (gatherTier s).process id with returned := true }))
          (some ((core s).getD (coreOfNetwork P (gatherTier s).2)))))
  /-- Corruption (deviation D1), together across the gather network state and every broadcast
  coordinate. -/
  | fail (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) :
      StepOverBroadcastSpecification P s (.fail id)
        (PMF.pure (corruptAll P id (BRB.SpecState.corrupt P id)
          (BRB.SpecState.corrupt P id) s))


omit [DecidableEq X] in
/-- A specification row read through the composition's pullback. -/
theorem liftSpecification_row {M : Type} {P : Parameters} {ldr : Fin P.n}
    {ψ : GatherLabel P.n X → Option (BRB.InstanceLabel P.n M)} {L : GatherLabel P.n X}
    {lb : BRB.InstanceLabel P.n M} {l₀ : BRB.Label P.n M} {s s' : BRB.SpecState P.n M}
    (hφ : ψ L = some lb) (hl : BRB.specificationLabelMap P.n M lb = some l₀)
    (h : ((BRB.specificationOverInstanceAlphabet P ldr M).mapIdle ψ).step s L (PMF.pure s')) :
    BRB.Step P ldr s l₀ (PMF.pure s') :=
  specificationOverInstanceAlphabet_step_row hl ((System.mapIdle_step_some hφ _).mp h)

omit [DecidableEq X] in
/-- A specification row is a transition of the instance read through the
composition's pullback. -/
theorem row_liftSpecification {M : Type} {P : Parameters} {ldr : Fin P.n}
    {ψ : GatherLabel P.n X → Option (BRB.InstanceLabel P.n M)} {L : GatherLabel P.n X}
    {lb : BRB.InstanceLabel P.n M} {l₀ : BRB.Label P.n M} {s s' : BRB.SpecState P.n M}
    (hφ : ψ L = some lb) (hl : BRB.specificationLabelMap P.n M lb = some l₀)
    (h : BRB.Step P ldr s l₀ (PMF.pure s')) :
    ((BRB.specificationOverInstanceAlphabet P ldr M).mapIdle ψ).step s L (PMF.pure s') :=
  (System.mapIdle_step_some hφ _).mpr (row_specificationOverInstanceAlphabet_step hl h)

/-! ### The row characterisation -/

/-- **The projection.** -/
theorem instanceOverBroadcastSpecification_step_row (P : Parameters) :
    ∀ (s : StateOverBroadcastSpecification P.n X) (l : InstanceLabel P.n X) (μ : PMF
      (StateOverBroadcastSpecification P.n X)),
      (instanceOverBroadcastSpecification P X).step s l μ →
      ∃ l₀, specificationLabelMap P.n X l = some l₀ ∧ StepOverBroadcastSpecification P s l₀ μ := by
  have hIn : ∀ k : Fin P.n,
    (BRB.specificationOverInstanceAlphabet P k X).IsLTS := fun k =>
      BRB.specificationOverInstanceAlphabet_isLTS P k
  have hBind : ∀ q : Fin P.n,
    (BRB.specificationOverInstanceAlphabet P q (AcceptedPairs P.n X)).IsLTS := fun q =>
      BRB.specificationOverInstanceAlphabet_isLTS P q
  rintro ⟨⟨u, w⟩, a, b⟩ l μ hstep
  rcases (instanceOverBroadcasts_step_iff P X (fun k => BRB.specificationOverInstanceAlphabet P k X)
      (fun q => BRB.specificationOverInstanceAlphabet P q (AcceptedPairs P.n X)) _ l μ).mp hstep
        with ⟨rfl,
        e, hev⟩ | hlab
  · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
      instanceOverBroadcastsExtended_joint_inversion hIn hBind (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_foreign (Ne.symm hi) (hproc i))
      have hw : w' = { w with network := w.network.recordSent j m } := PMF.pure_injective
        (networkStep_send hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw; subst ha; subst hb
      cases m with
      | echo A =>
        obtain ⟨rfl, hinp, hcard, hsend, hx⟩ := programStep_send_echo_own (hproc j)
        rw [stateOverBroadcasts_setProcess_recordSent (PMF.pure_injective hx) hfor]
        exact StepOverBroadcastSpecification.echo _ j hinp hcard hsend
      | vote U =>
        obtain ⟨hinp, hech, happ, hQ, hsend, hx⟩ := programStep_send_vote_own (hproc j)
        rw [stateOverBroadcasts_setProcess_recordSent (PMF.pure_injective hx) hfor]
        exact StepOverBroadcastSpecification.vote _ j U hinp hech happ hQ hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hnet
      have hw' : w' = w := PMF.pure_injective hw
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw'; subst ha; subst hb
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_foreign (Ne.symm hi') (hproc i'))
      rw [stateOverBroadcasts_deliver (PMF.pure_injective (programStep_deliver_own (hproc i))) hfor]
      exact StepOverBroadcastSpecification.deliver _ i j m hmem
    | inputBroadcastRet k j v =>
      have hw : w' = w := PMF.pure_injective (networkStep_inputBroadcastRet hnet)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw; subst hb
      obtain ⟨hval, hret, hak⟩ :=
        specStep_ret (liftSpecification_row (lb := Sum.inl (BRB.Label.ret j v)) (by simp) rfl (hin k))
      have haf : ∀ k', k' ≠ k → a' k' = a k' :=
        fun k' hk' => System.mapIdle_eq_of_step_none (by simp [hk']) (hin k')
      have ha : a' = Function.update a k { a k with ret := Function.update (a k).ret j true } :=
        funUpdate (PMF.pure_injective hak) haf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_inputBroadcastRet_foreign (Ne.symm hi) (hproc
          i))
      have hxj := PMF.pure_injective (programStep_inputBroadcastRet_own (hproc j))
      subst ha
      rw [programFunction_update hxj hfor]
      exact StepOverBroadcastSpecification.inputBroadcastRet _ k j v hval hret
    | bindCall j U =>
      have hw : w' = w := PMF.pure_injective (networkStep_bindCall hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hinp, hvot, hsnd, happ, hQ, hxj⟩ := programStep_bindCall_own (hproc j)
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_bindCall_foreign (Ne.symm hi) (hproc i))
      have hbf : ∀ q, q ≠ j → b' q = b q :=
        fun q hq => System.mapIdle_eq_of_step_none (by simp [hq]) (hbind q)
      rcases specStep_call (liftSpecification_row (lb := Sum.inl (BRB.Label.call U)) (by simp) rfl
          (hbind j)) with ⟨hbin, hbq⟩ | hbq
      · have hb : b' = Function.update b j { b j with input := some U } :=
          funUpdate (PMF.pure_injective hbq) hbf
        subst hb
        rw [programFunction_update (PMF.pure_injective hxj) hfor]
        exact StepOverBroadcastSpecification.bindCall _ j U hinp hvot hsnd happ hQ hbin
      · have hb : b' = b := funext fun q => by
          by_cases hq : q = j
          · subst hq; exact PMF.pure_injective hbq
          · exact hbf q hq
        subst hb
        rw [stateOverBroadcasts_setProcess (PMF.pure_injective hxj) hfor]
        exact StepOverBroadcastSpecification.bindCallSpecificationLoop _ j U hinp hvot hsnd happ hQ
    | bindRet q j U =>
      have hw : w' = w := PMF.pure_injective (networkStep_bindRet hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hval, hret, hbq⟩ :=
        specStep_ret (liftSpecification_row (lb := Sum.inl (BRB.Label.ret j U)) (by simp) rfl (hbind q))
      have hbf : ∀ q', q' ≠ q → b' q' = b q' :=
        fun q' hq' => System.mapIdle_eq_of_step_none (by simp [hq']) (hbind q')
      have hb : b' = Function.update b q { b q with ret := Function.update (b q).ret j true } :=
        funUpdate (PMF.pure_injective hbq) hbf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_bindRet_foreign (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (programStep_bindRet_own (hproc j))
      subst hb
      rw [programFunction_update hxj hfor]
      exact StepOverBroadcastSpecification.bindRet _ q j U hval hret
  · by_cases hlτ : l = Sum.inl Label.tau
    · subst hlτ
      refine ⟨Label.tau, rfl, ?_⟩
      rcases instanceOverBroadcastsExtended_tau_inversion hIn hBind hlab with
        ⟨v, rfl, hn⟩ | ⟨k, c, rfl, hs⟩ | ⟨q, d, rfl, hs⟩
      · obtain ⟨jj, m, hF, hv⟩ := networkStep_tau hn
        have hv' : v = { w with network := w.network.recordSent jj m } := PMF.pure_injective hv
        subst hv'
        rw [stateOverBroadcasts_recordSent]
        exact StepOverBroadcastSpecification.byzantine _ jj m hF
      · obtain ⟨v, hval, hm, hc⟩ := specStep_tau (specificationOverInstanceAlphabet_step_row rfl hs)
        have hc' : c = { a k with val := some v } := PMF.pure_injective hc
        subst hc'
        rw [stateOverBroadcasts_setInputBroadcasts]
        exact StepOverBroadcastSpecification.commitInputEntry _ k v hval hm
      · obtain ⟨U, hval, hm, hd⟩ := specStep_tau (specificationOverInstanceAlphabet_step_row rfl hs)
        have hd' : d = { b q with val := some U } := PMF.pure_injective hd
        subst hd'
        rw [stateOverBroadcasts_setBindBroadcasts]
        exact StepOverBroadcastSpecification.commitBindEntry _ q U hval hm
    · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
        instanceOverBroadcastsExtended_joint_inversion hIn hBind (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call id y =>
          have hw : w' = w := PMF.pure_injective (networkStep_call hnet)
          have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
          subst hw; subst hb
          obtain ⟨hinp, hxj⟩ := programStep_call_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_call_foreign (Ne.symm hi) (hproc i))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => System.mapIdle_eq_of_step_none (by simp [hk]) (hin k)
          refine ⟨Label.call id y, rfl, ?_⟩
          rcases specStep_call (liftSpecification_row (lb := Sum.inl (BRB.Label.call y)) (by simp) rfl
              (hin id)) with ⟨hbin, haq⟩ | haq
          · have ha : a' = Function.update a id { a id with input := some y } :=
              funUpdate (PMF.pure_injective haq) haf
            subst ha
            rw [programFunction_update (PMF.pure_injective hxj) hfor]
            exact StepOverBroadcastSpecification.call _ id y hinp hbin
          · have ha : a' = a := funext fun k => by
              by_cases hk : k = id
              · subst hk; exact PMF.pure_injective haq
              · exact haf k hk
            subst ha
            rw [stateOverBroadcasts_setProcess (PMF.pure_injective hxj) hfor]
            exact StepOverBroadcastSpecification.callSpecificationLoop _ id y hinp
        | ret id g C =>
          obtain ⟨hC, hw⟩ := networkStep_ret hnet
          subst hC
          have hw' : w' = { w with core := some (w.core.getD (coreOfNetwork P w.network)) } :=
            PMF.pure_injective hw
          have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
          have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
          subst hw'; subst ha; subst hb
          obtain ⟨hinp, hbnd, hsub, hQ, hr, hxj⟩ := programStep_ret_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_ret_foreign (Ne.symm hi) (hproc i))
          refine ⟨_, rfl, ?_⟩
          rw [stateOverBroadcasts_ret (PMF.pure_injective hxj) hfor]
          exact StepOverBroadcastSpecification.ret _ id g hinp hbnd hsub hQ hr
        | fail id =>
          have hw : w' = { w with network := w.network.corrupt P id } :=
            PMF.pure_injective (networkStep_fail hnet)
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hproc i))
          have ha : ∀ k, a' k = (a k).corrupt P id := fun k =>
            PMF.pure_injective (specStep_fail
              (liftSpecification_row (lb := Sum.inl (BRB.Label.fail id)) (by simp) rfl (hin k)))
          have hb : ∀ q, b' q = (b q).corrupt P id := fun q =>
            PMF.pure_injective (specStep_fail
              (liftSpecification_row (lb := Sum.inl (BRB.Label.fail id)) (by simp) rfl (hbind q)))
          subst hw
          refine ⟨_, rfl, ?_⟩
          rw [funext ha, funext hb, stateOverBroadcasts_corrupt hxall]
          exact StepOverBroadcastSpecification.fail _ id
      | inr ev =>
        cases ev with
        | callLoop id y =>
          have hw : w' = w := PMF.pure_injective (networkStep_callLoop hnet)
          have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
          subst hw; subst hb
          have hxall : ∀ i,
            x i = u i := fun i => PMF.pure_injective (programStep_callLoop (hproc i))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => System.mapIdle_eq_of_step_none (by simp [hk]) (hin k)
          refine ⟨Label.call id y, rfl, ?_⟩
          rcases specStep_call (liftSpecification_row (lb := Sum.inr (BRB.LoopLabel.callLoop y)) (by simp)
            rfl
              (hin id)) with ⟨hbin, haq⟩ | haq
          · have ha : a' = Function.update a id { a id with input := some y } :=
              funUpdate (PMF.pure_injective haq) haf
            subst ha
            rw [stateOverBroadcasts_idle hxall, stateOverBroadcasts_setInputBroadcasts]
            exact StepOverBroadcastSpecification.callProgramLoop _ id y hbin
          · have ha : a' = a := funext fun k => by
              by_cases hk : k = id
              · subst hk; exact PMF.pure_injective haq
              · exact haf k hk
            subst ha
            rw [stateOverBroadcasts_idle hxall]
            exact StepOverBroadcastSpecification.callLoop _ id y

/-- **The embedding.** -/
theorem row_instanceOverBroadcastSpecification_step (P : Parameters) :
    ∀ (s : StateOverBroadcastSpecification P.n X) (l₀ : Label P.n X) (μ : PMF
      (StateOverBroadcastSpecification P.n X)),
      StepOverBroadcastSpecification P s l₀ μ →
      ∃ l,
        specificationLabelMap P.n X l = some l₀ ∧ (instanceOverBroadcastSpecification P X).step s l
          μ := by
  rintro ⟨⟨u, w⟩, a, b⟩ l₀ μ hrow
  cases hrow with
  | call id x h hb =>
    exact ⟨Sum.inl (.call id x), rfl, instanceOverBroadcasts_label_step (by simp)
      (programStep_update (ProgramStep.call (u id) x h)
        (fun i hi => ProgramStep.callIdle (u i) id x (Ne.symm hi)))
      (NetworkStep.call w id x)
      (System.mapIdle_step_update (by simp) (fun k hk => by simp [hk])
        (row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.call x)) rfl
          (BRB.Step.call (a id) x hb)))
      (fun q => System.mapIdle_unchanged rfl)⟩
  | callSpecificationLoop id x h =>
    refine ⟨Sum.inl (.call id x), rfl,
      instanceOverBroadcasts_label_step (a' := a) (b' := b) (by simp) (programStep_update
        (ProgramStep.call (u id) x h)
        (fun i hi => ProgramStep.callIdle (u i) id x (Ne.symm hi)))
      (NetworkStep.call w id x) (fun k => ?_) (fun q => System.mapIdle_unchanged rfl)⟩
    by_cases hk : k = id
    · subst hk
      exact System.mapIdle_step_of_step (by simp)
        (row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.call x)) rfl
          (BRB.Step.callLoop (a k) x))
    · exact System.mapIdle_unchanged (by simp [hk])
  | callProgramLoop id x hb =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      instanceOverBroadcasts_label_step (x := u) (w' := w) (b' := b) (by simp) (fun i => ?_)
        (NetworkStep.callLoop w id x)
        (System.mapIdle_step_update (by simp) (fun k hk => by simp [hk])
          (row_specificationOverInstanceAlphabet_step (l := Sum.inr (BRB.LoopLabel.callLoop x)) rfl
            (BRB.Step.call (a id) x hb)))
        (fun q => System.mapIdle_unchanged rfl)⟩
    by_cases hi : i = id
    · subst hi; exact ProgramStep.callLoop (u i) x
    · exact ProgramStep.callLoopIdle (u i) id x (Ne.symm hi)
  | callLoop id x =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      instanceOverBroadcasts_label_step (x := u) (w' := w) (a' := a) (b' := b) (by simp) (fun i =>
        ?_)
        (NetworkStep.callLoop w id x) (fun k => ?_) (fun q => System.mapIdle_unchanged rfl)⟩
    · by_cases hi : i = id
      · subst hi; exact ProgramStep.callLoop (u i) x
      · exact ProgramStep.callLoopIdle (u i) id x (Ne.symm hi)
    · by_cases hk : k = id
      · subst hk
        exact System.mapIdle_step_of_step (by simp)
          (row_specificationOverInstanceAlphabet_step (l := Sum.inr (BRB.LoopLabel.callLoop x)) rfl
            (BRB.Step.callLoop (a k) x))
      · exact System.mapIdle_unchanged (by simp [hk])
  | commitInputEntry k v hv hm =>
    exact ⟨Sum.inl Label.tau, rfl, instanceOverBroadcasts_tau_input
      (row_specificationOverInstanceAlphabet_step (l := (Silent.τ : BRB.InstanceLabel P.n X)) rfl
        (BRB.Step.commit (a k) v hv hm))⟩
  | commitBindEntry q U hv hm =>
    exact ⟨Sum.inl Label.tau, rfl, instanceOverBroadcasts_tau_bind
      (row_specificationOverInstanceAlphabet_step (l := (Silent.τ : BRB.InstanceLabel P.n
        (AcceptedPairs P.n
        X))) rfl
        (BRB.Step.commit (b q) U hv hm))⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (a' := a) (b' := b) (GatherEvent.deliver i j m)
        (programStep_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h) (fun k => System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | echo j hin hcard hsend =>
    exact ⟨Sum.inl Label.tau, rfl, instanceOverBroadcasts_event_step (a' := a) (b' := b)
      (GatherEvent.send j (.echo (u j).process.accepted))
      (programStep_update (ProgramStep.sendEcho (u j) hin hcard hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo (u j).process.accepted) (Ne.symm hi)))
      (NetworkStep.send w j (.echo (u j).process.accepted)) (fun k => System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | vote j U hin hech happ hQ hsend =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (a' := a) (b' := b) (GatherEvent.send j (.vote U))
        (programStep_update
        (ProgramStep.sendVote (u j) U hin hech happ hQ hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote U) (Ne.symm hi)))
      (NetworkStep.send w j (.vote U)) (fun k => System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | bindCall j U hin hvot hsnd happ hQ hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (GatherEvent.bindCall j U)
        (programStep_update (ProgramStep.bindCall (u j) U hin hvot hsnd happ hQ)
          (fun i hi => ProgramStep.bindCallIdle (u i) j U (Ne.symm hi)))
        (NetworkStep.bindCallIdle w j U) (fun k => System.mapIdle_unchanged rfl)
        (System.mapIdle_step_update (by simp) (fun q hq => by simp [hq])
          (row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.call U)) rfl
            (BRB.Step.call (b j) U hb)))⟩
  | bindCallSpecificationLoop j U hin hvot hsnd happ hQ =>
    refine ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (b' := b) (GatherEvent.bindCall j U)
        (programStep_update (ProgramStep.bindCall (u j) U hin hvot hsnd happ hQ)
          (fun i hi => ProgramStep.bindCallIdle (u i) j U (Ne.symm hi)))
        (NetworkStep.bindCallIdle w j U) (fun k => System.mapIdle_unchanged rfl) (fun q => ?_)⟩
    · by_cases hq : q = j
      · subst hq
        exact System.mapIdle_step_of_step (by simp)
          (row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.call U)) rfl
            (BRB.Step.callLoop (b q) U))
      · exact System.mapIdle_unchanged (by simp [hq])
  | byzantine j m h =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_network (NetworkStep.byzantine w j m h)⟩
  | inputBroadcastRet k j v hv hr =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (b' := b) (GatherEvent.inputBroadcastRet k j v)
        (programStep_update (ProgramStep.inputBroadcastRetReceive (u j) k v)
        (fun i hi => ProgramStep.inputBroadcastRetIdle (u i) k j v (Ne.symm hi)))
      (NetworkStep.inputBroadcastRetIdle w k j v)
      (System.mapIdle_step_update (by simp) (fun k' hk' => by simp [hk'])
        (row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.ret j v)) rfl
          (BRB.Step.ret (a k) j v hv hr)))
      (fun q => System.mapIdle_unchanged rfl)⟩
  | bindRet q j U hv hr =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (GatherEvent.bindRet q j U)
        (programStep_update (ProgramStep.bindRetReceive (u j) q U)
        (fun i hi => ProgramStep.bindRetIdle (u i) q j U (Ne.symm hi)))
      (NetworkStep.bindRetIdle w q j U) (fun k => System.mapIdle_unchanged rfl)
      (System.mapIdle_step_update (by simp) (fun q' hq' => by simp [hq'])
        (row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.ret j U)) rfl
          (BRB.Step.ret (b q) j U hv hr)))⟩
  | ret id g hin hbind hsub hQ hr =>
    exact ⟨Sum.inl (.ret id g (w.core.getD (coreOfNetwork P w.network))), rfl,
      instanceOverBroadcasts_label_step (a' := a) (b' := b) (by simp)
        (programStep_update (ProgramStep.ret (u id) g _ hin hbind hsub hQ hr)
          (fun i hi => ProgramStep.retIdle (u i) id g _ (Ne.symm hi)))
        (NetworkStep.ret w id g) (fun k => System.mapIdle_unchanged rfl)
        (fun q => System.mapIdle_unchanged rfl)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, instanceOverBroadcasts_label_step (x := u) (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)
      (System.mapIdle_step_all (l₀ := fun _ => Sum.inl (BRB.Label.fail id)) (fun k => rfl)
        (fun k => row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.fail id)) rfl
          (BRB.Step.fail (a k) id)))
      (System.mapIdle_step_all (l₀ := fun _ => Sum.inl (BRB.Label.fail id)) (fun q => rfl)
        (fun q => row_specificationOverInstanceAlphabet_step (l := Sum.inl (BRB.Label.fail id)) rfl
          (BRB.Step.fail (b q) id)))⟩

/-- **The row characterisation.** At a specification label `l₀`, the
transitions of the instance over the labels `specificationLabelMap` sends to `l₀` are exactly
the `l₀`-rows of `StepOverBroadcastSpecification`, on the same state and with the same
distribution. -/
theorem instanceOverBroadcastSpecification_step_iff_row (P : Parameters)
    (s : StateOverBroadcastSpecification P.n X) (l₀ : Label P.n X)
    (μ : PMF (StateOverBroadcastSpecification P.n X)) :
    (∃ l, specificationLabelMap P.n X l = some l₀ ∧ (instanceOverBroadcastSpecification P X).step s
      l μ)
    ↔ StepOverBroadcastSpecification P s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := instanceOverBroadcastSpecification_step_row P s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n X)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_instanceOverBroadcastSpecification_step P s l₀ μ

/-- info: 'PLTS.ABA.Gather.instanceOverBroadcastSpecification_step_iff_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms instanceOverBroadcastSpecification_step_iff_row

end Gather
end ABA
end PLTS
