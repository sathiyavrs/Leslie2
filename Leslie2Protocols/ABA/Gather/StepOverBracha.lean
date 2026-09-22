/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Composition

/-!
# The rows of the gather instance over Bracha's broadcast

`StepOverBracha` is the rule table of `Gather.instanceOverBracha` (`ABA/Gather/Composition.lean`) —
the `n` gather programs beside the gather network, in parallel with `2n` composed
reliable-broadcast instances — stated over the composition's state through the
four views `gatherTier`, `inputBroadcasts`, `bindBroadcasts`, `core`. It is a relation on that
state; the system is the composition.

`instanceOverBracha_step_iff_row` is the row characterisation: at a specification label
`l₀`, the transitions of the composition over the labels `specificationLabelMap` sends to
`l₀` are exactly the `l₀`-rows of `StepOverBracha`, on the same state and with the
same distribution.

## The broadcast tier

A broadcast instance's own rows are `BRB.BrachaStep`
(`ABA/ReliableBroadcast/BrachaImplementation.lean`), and `BRB.brachaInstance_step_iff_row` matches
them against the instance's transitions. Each label of the composition reaches an instance at one
label of its interface alphabet, and the rows there carry over: a silent step, a return and a
corruption are the hypotheses `BRB.BrachaStep P k (inputBroadcasts s k) l₀ (PMF.pure c)` of
the rows `inputBroadcastTau`, `inputBroadcastRet` and `fail`.

The call is the exception. `BRB.BrachaStep` answers `call x` on two rows, the
broadcast of `⟨INIT, x⟩` and the input-enabledness loop, and the two sit at the
two labels of the instance's interface — the broadcast under `call x`, the loop
under `LoopLabel.callLoop x`. The composition puts the gather call over the first
and the gather call loop over the second, so the gather call carries the
broadcast and the gather call loop moves nothing. The rows `call` and
`callLoop` state that directly, as does `bindCall`.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X]

/-! ### Reading a composed broadcast instance -/

omit [DecidableEq X] in
/-- A transition of a composed broadcast instance is a `BRB.BrachaStep` row at the
label `BRB.specificationLabelMap` projects to. -/
theorem brachaInstance_step_at {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {l : BRB.InstanceLabel P.n M} {l₀ : BRB.Label P.n M}
    (hl : BRB.specificationLabelMap P.n M l = some l₀)
    (h : (BRB.brachaInstance P ldr M).step s l (PMF.pure s')) : BRB.BrachaStep P ldr s l₀ (PMF.pure
      s') := by
  obtain ⟨l₁, hl₁, hrow⟩ := BRB.brachaInstance_step_row P ldr s l _ h
  rwa [Option.some.inj (hl₁.symm.trans hl)] at hrow

omit [DecidableEq X] in
/-- A `BRB.BrachaStep` row at a label other than a call is a transition of the
instance at the interface label over it. -/
theorem row_brachaInstance_step_inl {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {l₀ : BRB.Label P.n M} (h0 : ∀ m : M, l₀ ≠ BRB.Label.call m)
    (h : BRB.BrachaStep P ldr s l₀ (PMF.pure s')) :
    (BRB.brachaInstance P ldr M).step s (Sum.inl l₀) (PMF.pure s') := by
  obtain ⟨l, hl, hstep⟩ := BRB.row_brachaInstance_step P ldr s l₀ _ h
  cases l with
  | inl y => rwa [Option.some.inj hl] at hstep
  | inr e => cases e with
    | callLoop m => exact absurd (Option.some.inj hl).symm (h0 m)

omit [DecidableEq X] in
/-- The one corruption row. -/
theorem brachaStep_fail {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s : BRB.BrachaState P.n M} {id : Fin P.n} {μ : PMF (BRB.BrachaState P.n M)}
    (h : BRB.BrachaStep P ldr s (.fail id) μ) : μ = PMF.pure (s.corrupt P id) := by
  cases h; rfl

omit [DecidableEq X] in
/-- At the call label the instance broadcasts: the leader records the payload
and the network records `⟨INIT, m⟩`. -/
theorem brachaInstance_call_row {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {m : M}
    (h : (BRB.brachaInstance P ldr M).step s (Sum.inl (BRB.Label.call m)) (PMF.pure s')) :
    (s.process ldr).input = none ∧
      s' = (s.setProcess ldr { s.process ldr with input := some m }).multicast ldr (.init m) := by
  obtain ⟨u, w⟩ := s
  rcases (BRB.brachaInstance_step_iff P ldr (u, w) (Sum.inl (BRB.Label.call m)) _).mp h with ⟨hτ,
    -⟩ | hlab
  · exact absurd hτ (by simp)
  · obtain ⟨x, w', hμ, hall, hn⟩ := BRB.brachaInstanceExtended_joint_inversion (by simp) hlab
    obtain ⟨hinp, hx⟩ := BRB.programStep_call_leader (hall ldr)
    have hfor : ∀ i, i ≠ ldr → x i = u i :=
      fun i hi => PMF.pure_injective (BRB.programStep_call_foreign hi (hall i))
    have hw : w' = w.recordSent ldr (.init m) := PMF.pure_injective (BRB.networkStep_call hn)
    subst hw
    refine ⟨hinp, ?_⟩
    rw [PMF.pure_injective hμ,
      BRB.brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
    rfl

omit [DecidableEq X] in
/-- At the call-loop label the instance stands still. -/
theorem brachaInstance_callLoop_row {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {m : M}
    (h : (BRB.brachaInstance P ldr M).step s (Sum.inr (BRB.LoopLabel.callLoop m)) (PMF.pure s')) :
      s' = s := by
  obtain ⟨u, w⟩ := s
  rcases (BRB.brachaInstance_step_iff P ldr (u, w) (Sum.inr (BRB.LoopLabel.callLoop m)) _).mp h with
    ⟨hτ, -⟩ | hlab
  · exact absurd hτ (by simp)
  · obtain ⟨x, w', hμ, hall, hn⟩ := BRB.brachaInstanceExtended_joint_inversion (by simp) hlab
    have hw : w' = w := PMF.pure_injective (BRB.networkStep_callLoop hn)
    subst hw
    have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (BRB.programStep_callLoop (hall i))
    rw [PMF.pure_injective hμ, BRB.brachaInstance_idle hidle]

omit [DecidableEq X] in
/-- Build the instance's broadcast at the call label. -/
theorem row_brachaInstance_call_step {M : Type} [DecidableEq M] (P : Parameters) (ldr : Fin P.n)
    (s : BRB.BrachaState P.n M) (m : M) (h : (s.process ldr).input = none) :
    (BRB.brachaInstance P ldr M).step s (Sum.inl (BRB.Label.call m))
      (PMF.pure ((s.setProcess ldr { s.process ldr with input := some m }).multicast ldr (.init m)))
        := by
  obtain ⟨u, w⟩ := s
  exact BRB.brachaInstance_label_step P ldr (by simp)
    (BRB.programStep_update (BRB.ProgramStep.call (u ldr) m rfl h)
      (fun i hi => BRB.ProgramStep.callIdle (u i) m hi))
    (BRB.NetworkStep.call w m)

omit [DecidableEq X] in
/-- Build the instance's stutter at the call-loop label. -/
theorem row_brachaInstance_callLoop_step {M : Type} [DecidableEq M] (P : Parameters) (ldr : Fin P.n)
    (s : BRB.BrachaState P.n M) (m : M) :
    (BRB.brachaInstance P ldr M).step s (Sum.inr (BRB.LoopLabel.callLoop m)) (PMF.pure s) := by
  obtain ⟨u, w⟩ := s
  exact BRB.brachaInstance_label_step P ldr (by simp) (fun i => BRB.ProgramStep.callLoop (u i) m)
    (BRB.NetworkStep.callLoop w m)

/-! ### The rows -/

/-- The rows of the gather instance over Bracha's broadcast (`Gather.instanceOverBracha`),
stated over the composition's state: one constructor per case of
`Gather.instanceOverBracha_step_iff_row`. All transitions are Dirac. -/
inductive StepOverBracha (P : Parameters) :
    StateOverBracha P.n X → Label P.n X → PMF (StateOverBracha P.n X) → Prop
  /-- The call arrives: the gather record records the payload and the input
  instance broadcasts it. -/
  | call (s : StateOverBracha P.n X) (id : Fin P.n) (x : X)
      (h : ((gatherTier s).process id).input = none) (hb : ((inputBroadcasts s id).process id).input
        = none) :
      StepOverBracha P s (.call id x)
        (PMF.pure (setInputBroadcasts (setGatherTier s ((gatherTier s).setProcess id { (gatherTier
          s).process id with input := some x }))
          (Function.update (inputBroadcasts s) id
            (((inputBroadcasts s id).setProcess id
              { (inputBroadcasts s id).process id with input := some x }).multicast id (.init x)))))
  /-- Input-enabledness loop for `call`: nothing moves. -/
  | callLoop (s : StateOverBracha P.n X) (id : Fin P.n) (x : X) :
      StepOverBracha P s (.call id x) (PMF.pure s)
  /-- A silent step of one input instance. -/
  | inputBroadcastTau (s : StateOverBracha P.n X) (k : Fin P.n) (c : BRB.BrachaState P.n X)
      (hb : BRB.BrachaStep P k (inputBroadcasts s k) .tau (PMF.pure c)) :
      StepOverBracha P s .tau (PMF.pure (setInputBroadcasts s (Function.update (inputBroadcasts s) k
        c)))
  /-- A silent step of one bind instance. -/
  | bindBroadcastTau (s : StateOverBracha P.n X) (q : Fin P.n) (d : BRB.BrachaState P.n
    (AcceptedPairs P.n X))
      (hb : BRB.BrachaStep P q (bindBroadcasts s q) .tau (PMF.pure d)) :
      StepOverBracha P s .tau (PMF.pure (setBindBroadcasts s (Function.update (bindBroadcasts s) q
        d)))
  /-- Asynchronous delivery on the gather network. -/
  | deliver (s : StateOverBracha P.n X) (i j : Fin P.n) (m : Message P.n X)
      (h : m ∈ (gatherTier s).sent j) :
      StepOverBracha P s .tau (PMF.pure (setGatherTier s ((gatherTier s).receiveMessage i j m)))
  /-- `ECHO`: the process is called and its accepted pairs number at least
  `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is those pairs,
  `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | echo (s : StateOverBracha P.n X) (j : Fin P.n)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hcard : P.n - P.f ≤ ((gatherTier s).process j).accepted.card)
      (hsend : ((gatherTier s).process j).sentEcho = none) :
      StepOverBracha P s .tau
        (PMF.pure (setGatherTier s (((gatherTier s).setProcess j
          { (gatherTier s).process j with sentEcho := some ((gatherTier s).process j).accepted
            }).multicast j
            (.echo ((gatherTier s).process j).accepted))))
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in the
  vote payload, are delivered here, and the process has multicast its own
  `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO` before `VOTE`. -/
  | vote (s : StateOverBracha P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hech : ((gatherTier s).process j).sentEcho ≠ none)
      (happ : approvedBy ((gatherTier s).process j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A,
          Message.echo A ∈ (gatherTier s).received j q ∧ approvedBy ((gatherTier s).process j) A ∧ A
            ⊆ U)
      (hsend : ((gatherTier s).process j).sentVote = none) :
      StepOverBracha P s .tau
        (PMF.pure (setGatherTier s (((gatherTier s).setProcess j
          { (gatherTier s).process j with sentVote := some U }).multicast j (.vote U))))
  /-- `BIND`: `n − f` senders' approved `VOTE` payloads, each contained in the
  bind payload, are delivered here, and the bind instance broadcasts the payload.
  The process has multicast its own `VOTE` and has not called its own bind
  broadcast. The main thread of AFW25's Algorithm 5 sends `VOTE` before `BIND`,
  and sends `BIND` once, at line 17. The payload handed to the broadcast is
  written to the gather record. -/
  | bindCall (s : StateOverBracha P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherTier s).process j).input ≠ none)
      (hvot : ((gatherTier s).process j).sentVote ≠ none)
      (hsnd : ((gatherTier s).process j).sentBind = none)
      (happ : approvedBy ((gatherTier s).process j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Message.vote W ∈ (gatherTier s).received j q ∧ approvedBy ((gatherTier s).process j) W ∧ W
            ⊆ U)
      (hbc : ((bindBroadcasts s j).process j).input = none) :
      StepOverBracha P s .tau
        (PMF.pure (setBindBroadcasts (setGatherTier s ((gatherTier s).setProcess j
            { (gatherTier s).process j with sentBind := some U }))
          (Function.update (bindBroadcasts s) j
            (((bindBroadcasts s j).setProcess j
              { (bindBroadcasts s j).process j with input := some U }).multicast j (.init U)))))
  /-- Byzantine injection on the gather network. -/
  | byzantine (s : StateOverBracha P.n X) (j : Fin P.n) (m : Message P.n X) (h : j ∈ (gatherTier
    s).F) :
      StepOverBracha P s .tau (PMF.pure (setGatherTier s ((gatherTier s).multicast j m)))
  /-- An input instance returns to `j`, which files the value it returned. -/
  | inputBroadcastRet (s : StateOverBracha P.n X) (k j : Fin P.n) (v : X) (c : BRB.BrachaState P.n
    X)
      (hb : BRB.BrachaStep P k (inputBroadcasts s k) (.ret j v) (PMF.pure c)) :
      StepOverBracha P s .tau
        (PMF.pure (setInputBroadcasts (setGatherTier s ((gatherTier s).setProcess j
            { (gatherTier s).process j with
              inputBroadcastReturned := Function.update ((gatherTier s).process
                j).inputBroadcastReturned k (some v) }))
          (Function.update (inputBroadcasts s) k c)))
  /-- A bind instance returns to `j`, which files the payload it returned. -/
  | bindRet (s : StateOverBracha P.n X) (q j : Fin P.n) (U : AcceptedPairs P.n X)
      (d : BRB.BrachaState P.n (AcceptedPairs P.n X))
      (hb : BRB.BrachaStep P q (bindBroadcasts s q) (.ret j U) (PMF.pure d)) :
      StepOverBracha P s .tau
        (PMF.pure (setBindBroadcasts (setGatherTier s ((gatherTier s).setProcess j
            { (gatherTier s).process j with
              bindBroadcastReturned := Function.update ((gatherTier s).process
                j).bindBroadcastReturned q (some U) }))
          (Function.update (bindBroadcasts s) q d)))
  /-- Return: the output's entries are held here, `n − f` bind payloads held
  here are sub-maps of it, and the returner has called its own bind broadcast.
  The `BIND` broadcast of AFW25's Algorithm 5, line 17, precedes the wait of line
  18. The label carries the instance's core, which this row writes if it is
  unwritten. -/
  | ret (s : StateOverBracha P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : ((gatherTier s).process id).input ≠ none)
      (hbind : ((gatherTier s).process id).sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn ((gatherTier s).process id) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          holdsBindBroadcastReturn ((gatherTier s).process id) q U ∧ AcceptedPairs.subMap U g)
      (hr : ((gatherTier s).process id).returned = false) :
      StepOverBracha P s (.ret id g ((core s).getD (coreOfNetwork P (gatherTier s).2)))
        (PMF.pure (setCore (setGatherTier s ((gatherTier s).setProcess id
          { (gatherTier s).process id with returned := true }))
          (some ((core s).getD (coreOfNetwork P (gatherTier s).2)))))
  /-- Corruption (deviation D1), together across the gather network state and every broadcast
  coordinate. -/
  | fail (s : StateOverBracha P.n X) (id : Fin P.n) :
      StepOverBracha P s (.fail id)
        (PMF.pure (corruptAll P id (InstanceState.corrupt P id) (InstanceState.corrupt P id) s))

/-! ### The row characterisation -/

/-- **The projection.** -/
theorem instanceOverBracha_step_row (P : Parameters) :
    ∀ (s : StateOverBracha P.n X) (l : InstanceLabel P.n X) (μ : PMF (StateOverBracha P.n X)),
      (instanceOverBracha P X).step s l μ →
      ∃ l₀, specificationLabelMap P.n X l = some l₀ ∧ StepOverBracha P s l₀ μ := by
  have hIn : ∀ k : Fin P.n,
    (BRB.brachaInstance P k X).IsLTS := fun k => BRB.brachaInstance_isLTS P k
  have hBind : ∀ q : Fin P.n,
    (BRB.brachaInstance P q (AcceptedPairs P.n X)).IsLTS := fun q => BRB.brachaInstance_isLTS P q
  rintro ⟨⟨u, w⟩, a, b⟩ l μ hstep
  rcases (instanceOverBroadcasts_step_iff P X (fun k => BRB.brachaInstance P k X)
      (fun q => BRB.brachaInstance P q (AcceptedPairs P.n X)) _ l μ).mp hstep with ⟨rfl, e,
        hev⟩ | hlab
  · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
      instanceOverBroadcastsExtended_joint_inversion hIn hBind (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_foreign (Ne.symm hi) (hproc i))
      have hw : w' = { w with network := w.network.recordSent j m } := PMF.pure_injective
        (networkStep_send hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw; subst ha; subst hb
      cases m with
      | echo A =>
        obtain ⟨rfl, hinp, hcard, hsend, hx⟩ := programStep_send_echo_own (hproc j)
        rw [stateOverBroadcasts_setProcess_recordSent (PMF.pure_injective hx) hfor]
        exact StepOverBracha.echo _ j hinp hcard hsend
      | vote U =>
        obtain ⟨hinp, hech, happ, hQ, hsend, hx⟩ := programStep_send_vote_own (hproc j)
        rw [stateOverBroadcasts_setProcess_recordSent (PMF.pure_injective hx) hfor]
        exact StepOverBracha.vote _ j U hinp hech happ hQ hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hnet
      have hw' : w' = w := PMF.pure_injective hw
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw'; subst ha; subst hb
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_foreign (Ne.symm hi') (hproc i'))
      rw [stateOverBroadcasts_deliver (PMF.pure_injective (programStep_deliver_own (hproc i))) hfor]
      exact StepOverBracha.deliver _ i j m hmem
    | inputBroadcastRet k j v =>
      have hw : w' = w := PMF.pure_injective (networkStep_inputBroadcastRet hnet)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw; subst hb
      have himpl : BRB.BrachaStep P k (a k) (.ret j v) (PMF.pure (a' k)) :=
        brachaInstance_step_at (l := Sum.inl (BRB.Label.ret j v)) rfl
          (lift_step_some (l₀ := Sum.inl (BRB.Label.ret j v)) (by simp) (hin k))
      have haf : ∀ k', k' ≠ k → a' k' = a k' :=
        fun k' hk' => lift_step_none (by simp [hk']) (hin k')
      have ha : a' = Function.update a k (a' k) := funUpdate rfl haf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_inputBroadcastRet_foreign (Ne.symm hi) (hproc
          i))
      have hxj := PMF.pure_injective (programStep_inputBroadcastRet_own (hproc j))
      rw [programFunction_update hxj hfor, ha]
      exact StepOverBracha.inputBroadcastRet _ k j v (a' k) himpl
    | bindCall j U =>
      have hw : w' = w := PMF.pure_injective (networkStep_bindCall hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hinp, hvot, hsnd, happ, hQ, hxj⟩ := programStep_bindCall_own (hproc j)
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_bindCall_foreign (Ne.symm hi) (hproc i))
      obtain ⟨hbc, hbj⟩ := brachaInstance_call_row
        (lift_step_some (l₀ := Sum.inl (BRB.Label.call U)) (by simp) (hbind j))
      have hbf : ∀ q, q ≠ j → b' q = b q :=
        fun q hq => lift_step_none (by simp [hq]) (hbind q)
      have hb : b' = Function.update b j
          (((b j).setProcess j { (b j).process j with input := some U }).multicast j (.init U)) :=
        funUpdate hbj hbf
      subst hb
      rw [programFunction_update (PMF.pure_injective hxj) hfor]
      exact StepOverBracha.bindCall _ j U hinp hvot hsnd happ hQ hbc
    | bindRet q j U =>
      have hw : w' = w := PMF.pure_injective (networkStep_bindRet hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      subst hw; subst ha
      have himpl : BRB.BrachaStep P q (b q) (.ret j U) (PMF.pure (b' q)) :=
        brachaInstance_step_at (l := Sum.inl (BRB.Label.ret j U)) rfl
          (lift_step_some (l₀ := Sum.inl (BRB.Label.ret j U)) (by simp) (hbind q))
      have hbf : ∀ q', q' ≠ q → b' q' = b q' :=
        fun q' hq' => lift_step_none (by simp [hq']) (hbind q')
      have hb : b' = Function.update b q (b' q) := funUpdate rfl hbf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_bindRet_foreign (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (programStep_bindRet_own (hproc j))
      rw [programFunction_update hxj hfor, hb]
      exact StepOverBracha.bindRet _ q j U (b' q) himpl
  · by_cases hlτ : l = Sum.inl Label.tau
    · subst hlτ
      refine ⟨Label.tau, rfl, ?_⟩
      rcases instanceOverBroadcastsExtended_tau_inversion hIn hBind hlab with ⟨v, rfl, hn⟩ | ⟨k, c, rfl,
        hs⟩ | ⟨q, d, rfl, hs⟩
      · obtain ⟨jj, m, hF, hv⟩ := networkStep_tau hn
        have hv' : v = { w with network := w.network.recordSent jj m } := PMF.pure_injective hv
        subst hv'
        rw [stateOverBroadcasts_recordSent]
        exact StepOverBracha.byzantine _ jj m hF
      · have himpl : BRB.BrachaStep P k (a k) BRB.Label.tau (PMF.pure c) :=
          brachaInstance_step_at (l := (Silent.τ : BRB.InstanceLabel P.n X)) rfl hs
        rw [stateOverBroadcasts_setInputBroadcasts]
        exact StepOverBracha.inputBroadcastTau _ k c himpl
      · have himpl : BRB.BrachaStep P q (b q) BRB.Label.tau (PMF.pure d) :=
          brachaInstance_step_at (l := (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X))) rfl
            hs
        rw [stateOverBroadcasts_setBindBroadcasts]
        exact StepOverBracha.bindBroadcastTau _ q d himpl
    · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
        instanceOverBroadcastsExtended_joint_inversion hIn hBind (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call id y =>
          have hw : w' = w := PMF.pure_injective (networkStep_call hnet)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw; subst hb
          obtain ⟨hinp, hxj⟩ := programStep_call_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_call_foreign (Ne.symm hi) (hproc i))
          obtain ⟨hbin, haid⟩ := brachaInstance_call_row
            (lift_step_some (l₀ := Sum.inl (BRB.Label.call y)) (by simp) (hin id))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => lift_step_none (by simp [hk]) (hin k)
          have ha : a' = Function.update a id
              (((a id).setProcess id { (a id).process id with input := some y }).multicast id (.init
                y)) :=
            funUpdate haid haf
          subst ha
          refine ⟨Label.call id y, rfl, ?_⟩
          rw [programFunction_update (PMF.pure_injective hxj) hfor]
          exact StepOverBracha.call _ id y hinp hbin
        | ret id g C =>
          obtain ⟨hC, hw⟩ := networkStep_ret hnet
          subst hC
          have hw' : w' = { w with core := some (w.core.getD (coreOfNetwork P w.network)) } :=
            PMF.pure_injective hw
          have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw'; subst ha; subst hb
          obtain ⟨hinp, hbnd, hsub, hQ, hr, hxj⟩ := programStep_ret_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_ret_foreign (Ne.symm hi) (hproc i))
          refine ⟨_, rfl, ?_⟩
          rw [stateOverBroadcasts_ret (PMF.pure_injective hxj) hfor]
          exact StepOverBracha.ret _ id g hinp hbnd hsub hQ hr
        | fail id =>
          have hw : w' = { w with network := w.network.corrupt P id } :=
            PMF.pure_injective (networkStep_fail hnet)
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hproc i))
          have ha : ∀ k, a' k = InstanceState.corrupt P id (a k) := fun k =>
            PMF.pure_injective (brachaStep_fail (brachaInstance_step_at (l := Sum.inl
              (BRB.Label.fail
              id)) rfl
              (lift_step_some (l₀ := Sum.inl (BRB.Label.fail id)) rfl (hin k))))
          have hb : ∀ q, b' q = InstanceState.corrupt P id (b q) := fun q =>
            PMF.pure_injective (brachaStep_fail (brachaInstance_step_at (l := Sum.inl
              (BRB.Label.fail
              id)) rfl
              (lift_step_some (l₀ := Sum.inl (BRB.Label.fail id)) rfl (hbind q))))
          subst hw
          refine ⟨_, rfl, ?_⟩
          rw [funext ha, funext hb, stateOverBroadcasts_corrupt hxall]
          exact StepOverBracha.fail _ id
      | inr ev =>
        cases ev with
        | callLoop id y =>
          have hw : w' = w := PMF.pure_injective (networkStep_callLoop hnet)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw; subst hb
          have hxall : ∀ i,
            x i = u i := fun i => PMF.pure_injective (programStep_callLoop (hproc i))
          have haid : a' id = a id := brachaInstance_callLoop_row
            (lift_step_some (l₀ := Sum.inr (BRB.LoopLabel.callLoop y)) (by simp) (hin id))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => lift_step_none (by simp [hk]) (hin k)
          have ha : a' = a := funext fun k => by
            by_cases hk : k = id
            · subst hk; exact haid
            · exact haf k hk
          subst ha
          refine ⟨Label.call id y, rfl, ?_⟩
          rw [stateOverBroadcasts_idle hxall]
          exact StepOverBracha.callLoop _ id y

/-- **The embedding.** -/
theorem row_instanceOverBracha_step (P : Parameters) :
    ∀ (s : StateOverBracha P.n X) (l₀ : Label P.n X) (μ : PMF (StateOverBracha P.n X)),
      StepOverBracha P s l₀ μ →
      ∃ l, specificationLabelMap P.n X l = some l₀ ∧ (instanceOverBracha P X).step s l μ := by
  rintro ⟨⟨u, w⟩, a, b⟩ l₀ μ hrow
  cases hrow with
  | call id x h hb =>
    exact ⟨Sum.inl (.call id x), rfl, instanceOverBroadcasts_label_step (b' := b) (by simp)
      (programStep_update (ProgramStep.call (u id) x h)
        (fun i hi => ProgramStep.callIdle (u i) id x (Ne.symm hi)))
      (NetworkStep.call w id x)
      (lift_update (by simp) (fun k hk => by simp [hk]) (row_brachaInstance_call_step P id (a id) x
        hb))
      (fun q => lift_idle rfl)⟩
  | callLoop id x =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      instanceOverBroadcasts_label_step (x := u) (w' := w) (a' := a) (b' := b) (by simp) (fun i =>
        ?_)
        (NetworkStep.callLoop w id x) (fun k => ?_) (fun q => lift_idle rfl)⟩
    · by_cases hi : i = id
      · subst hi; exact ProgramStep.callLoop (u i) x
      · exact ProgramStep.callLoopIdle (u i) id x (Ne.symm hi)
    · by_cases hk : k = id
      · subst hk; exact row_lift_step (by simp) (row_brachaInstance_callLoop_step P k (a k) x)
      · exact lift_idle (by simp [hk])
  | inputBroadcastTau k c hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_in (row_brachaInstance_step_inl (by simp) hb)⟩
  | bindBroadcastTau q d hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_bind (row_brachaInstance_step_inl (by simp) hb)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (a' := a) (b' := b) (GatherEvent.deliver i j m)
        (programStep_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | echo j hin hcard hsend =>
    exact ⟨Sum.inl Label.tau, rfl, instanceOverBroadcasts_event_step (a' := a) (b' := b)
      (GatherEvent.send j (.echo (u j).process.accepted))
      (programStep_update (ProgramStep.sendEcho (u j) hin hcard hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo (u j).process.accepted) (Ne.symm hi)))
      (NetworkStep.send w j (.echo (u j).process.accepted)) (fun k => lift_idle rfl)
      (fun q => lift_idle rfl)⟩
  | vote j U hin hech happ hQ hsend =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (a' := a) (b' := b) (GatherEvent.send j (.vote U))
        (programStep_update
        (ProgramStep.sendVote (u j) U hin hech happ hQ hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote U) (Ne.symm hi)))
      (NetworkStep.send w j (.vote U)) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | bindCall j U hin hvot hsnd happ hQ hbc =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (GatherEvent.bindCall j U)
        (programStep_update (ProgramStep.bindCall (u j) U hin hvot hsnd happ hQ)
          (fun i hi => ProgramStep.bindCallIdle (u i) j U (Ne.symm hi)))
        (NetworkStep.bindCallIdle w j U) (fun k => lift_idle rfl)
        (lift_update (by simp) (fun q hq => by simp [hq])
          (row_brachaInstance_call_step P j (b j) U hbc))⟩
  | byzantine j m h =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_network (NetworkStep.byzantine w j m h)⟩
  | inputBroadcastRet k j v c hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (b' := b) (GatherEvent.inputBroadcastRet k j v)
        (programStep_update (ProgramStep.inputBroadcastRetReceive (u j) k v)
        (fun i hi => ProgramStep.inputBroadcastRetIdle (u i) k j v (Ne.symm hi)))
      (NetworkStep.inputBroadcastRetIdle w k j v)
      (lift_update (by simp) (fun k' hk' => by simp [hk']) (row_brachaInstance_step_inl (by simp)
        hb))
      (fun q => lift_idle rfl)⟩
  | bindRet q j U d hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (GatherEvent.bindRet q j U)
        (programStep_update (ProgramStep.bindRetReceive (u j) q U)
        (fun i hi => ProgramStep.bindRetIdle (u i) q j U (Ne.symm hi)))
      (NetworkStep.bindRetIdle w q j U) (fun k => lift_idle rfl)
      (lift_update (by simp) (fun q' hq' => by simp [hq']) (row_brachaInstance_step_inl (by simp)
        hb))⟩
  | ret id g hin hbind hsub hQ hr =>
    exact ⟨Sum.inl (.ret id g (w.core.getD (coreOfNetwork P w.network))), rfl,
      instanceOverBroadcasts_label_step (a' := a) (b' := b) (by simp)
        (programStep_update (ProgramStep.ret (u id) g _ hin hbind hsub hQ hr)
          (fun i hi => ProgramStep.retIdle (u i) id g _ (Ne.symm hi)))
        (NetworkStep.ret w id g) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, instanceOverBroadcasts_label_step (x := u) (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)
      (lift_all (l₀ := fun _ => Sum.inl (BRB.Label.fail id)) (fun k => rfl)
        (fun k => row_brachaInstance_step_inl (by simp) (BRB.BrachaStep.fail (a k) id)))
      (lift_all (l₀ := fun _ => Sum.inl (BRB.Label.fail id)) (fun q => rfl)
        (fun q => row_brachaInstance_step_inl (by simp) (BRB.BrachaStep.fail (b q) id)))⟩

/-- **The row characterisation.** At a specification label `l₀`, the transitions
of the instance over the labels `specificationLabelMap` sends to `l₀` are exactly the
`l₀`-rows of `StepOverBracha`, on the same state and with the same distribution. -/
theorem instanceOverBracha_step_iff_row (P : Parameters) (s : StateOverBracha P.n X) (l₀ : Label P.n
  X)
    (μ : PMF (StateOverBracha P.n X)) :
    (∃ l,
      specificationLabelMap P.n X l = some l₀ ∧ (instanceOverBracha P X).step s l μ) ↔
        StepOverBracha P s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := instanceOverBracha_step_row P s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n X)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_instanceOverBracha_step P s l₀ μ

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_step_iff_row

end Gather
end ABA
end PLTS
