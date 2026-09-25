/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.CompositionStepCases
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Algorithm
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The algorithm of the gather instance over Bracha's broadcast

`AlgorithmOverBracha` states the transitions of `Gather.instanceOverBracha`
(`ABA/Gather/Composition.lean`) -- the `n` gather programs beside the gather network, in parallel
with `2n` composed reliable-broadcast instances -- over the composition's state, through the four
projections `gatherProgramsAndNetwork`, `inputBroadcasts`, `bindBroadcasts` and `core`, one
constructor per case of
`instanceOverBracha_step_iff_algorithm`. It is a relation on that state; the system is the
composition.

`instanceOverBracha_step_iff_algorithm` is the characterisation: at a specification label `l₀`, the
transitions of the composition over the labels `specificationLabelMap` sends to `l₀` are exactly
the `l₀`-transitions of `AlgorithmOverBracha`, on the same composed state and with the same
distribution.

## The broadcast instances

A broadcast instance's own transitions are `BRB.BrachaAlgorithm`
(`ABA/ReliableBroadcast/Bracha/Algorithm.lean`), and `BRB.brachaInstance_step_iff_algorithm` matches
them against the instance's transitions. Each label of the composition reaches an instance at one
label of its interface alphabet, and the transitions there carry over: a silent step, a return and
a corruption are the hypotheses `BRB.BrachaAlgorithm P k (inputBroadcasts s k) l₀ (PMF.pure c)` of
`inputBroadcastTau`, `inputBroadcastRet` and `fail`.

The call is the exception. `BRB.BrachaAlgorithm` answers `call x` on two transitions, the
broadcast of `⟨INIT, x⟩` and the input-enabledness loop, and the two sit at the
two labels of the instance's interface -- the broadcast under `call x`, the loop
under `LoopLabel.callLoop x`. Neither is reached by the gather's own call or by its call loop, which
leave every input instance where it stands. The broadcast of an input instance is reached by the
event `inputBroadcastCall`, which is where `inputBroadcastCall` and `bindCall` carry the
`⟨INIT, x⟩` of the instance they call.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X]

/-! ### Reading a composed broadcast instance -/

omit [DecidableEq X] in
/-- A transition of a composed broadcast instance is a transition of `BRB.BrachaAlgorithm` at
the label `BRB.specificationLabelMap` projects to. -/
theorem brachaInstance_step_at {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {l : BRB.InstanceLabel P.n M} {l₀ : BRB.Label P.n M}
    (hl : BRB.specificationLabelMap P.n M l = some l₀)
    (h : (BRB.brachaInstance P ldr M).step s l (PMF.pure s')) :
    BRB.BrachaAlgorithm P ldr s l₀ (PMF.pure s') := by
  obtain ⟨l₁, hl₁, htransition⟩ := BRB.brachaInstance_step_algorithm P ldr s l _ h
  rwa [Option.some.inj (hl₁.symm.trans hl)] at htransition

omit [DecidableEq X] in
/-- A transition of `BRB.BrachaAlgorithm` at a label other than a call is a transition of the
instance at the interface label over it. -/
theorem transition_brachaInstance_step_inl {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin
  P.n}
    {s s' : BRB.BrachaState P.n M} {l₀ : BRB.Label P.n M} (h0 : ∀ m : M, l₀ ≠ BRB.Label.call m)
    (h : BRB.BrachaAlgorithm P ldr s l₀ (PMF.pure s')) :
    (BRB.brachaInstance P ldr M).step s (Sum.inl l₀) (PMF.pure s') := by
  obtain ⟨l, hl, hstep⟩ := BRB.algorithm_brachaInstance_step P ldr s l₀ _ h
  cases l with
  | inl y => rwa [Option.some.inj hl] at hstep
  | inr e => cases e with
    | callLoop m => exact absurd (Option.some.inj hl).symm (h0 m)

omit [DecidableEq X] in
/-- The one corruption transition. -/
theorem brachaAlgorithm_fail {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s : BRB.BrachaState P.n M} {id : Fin P.n} {μ : PMF (BRB.BrachaState P.n M)}
    (h : BRB.BrachaAlgorithm P ldr s (.fail id) μ) : μ = PMF.pure (s.corrupt P id) := by
  cases h; rfl

omit [DecidableEq X] in
/-- At the call label the instance broadcasts: the leader records the payload
and the network records `⟨INIT, m⟩`. -/
theorem brachaInstance_call_transition {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {m : M}
    (h : (BRB.brachaInstance P ldr M).step s (Sum.inl (BRB.Label.call m)) (PMF.pure s')) :
    (s.processVariables ldr).input = none ∧
      s' = (s.setProcessVariables ldr { s.processVariables ldr with input := some m }).multicast ldr
        (.init m) := by
  obtain ⟨u, w⟩ := s
  rcases (BRB.brachaInstance_step_iff P ldr (u, w) (Sum.inl (BRB.Label.call m)) _).mp h with ⟨hτ,
    -⟩ | hlab
  · exact absurd hτ (by simp)
  · obtain ⟨x, w', hμ, hall, hn⟩ := BRB.brachaInstanceExtended_synchronised_cases (by simp) hlab
    obtain ⟨hinp, hx⟩ := BRB.programStep_call_leader (hall ldr)
    have hfor : ∀ i, i ≠ ldr → x i = u i :=
      fun i hi => PMF.pure_injective (BRB.programStep_call_notOwn hi (hall i))
    have hw : w' = w.recordSent ldr (.init m) := PMF.pure_injective (BRB.networkStep_call hn)
    subst hw
    refine ⟨hinp, ?_⟩
    rw [PMF.pure_injective hμ,
      BRB.brachaInstance_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
    rfl

omit [DecidableEq X] in
/-- Build the instance's broadcast at the call label. -/
theorem transition_brachaInstance_call_step {M : Type} [DecidableEq M] (P : Parameters) (ldr : Fin
  P.n)
    (s : BRB.BrachaState P.n M) (m : M) (h : (s.processVariables ldr).input = none) :
    (BRB.brachaInstance P ldr M).step s (Sum.inl (BRB.Label.call m))
      (PMF.pure ((s.setProcessVariables ldr
        { s.processVariables ldr with input := some m }).multicast ldr (.init m)))
        := by
  obtain ⟨u, w⟩ := s
  exact BRB.brachaInstance_label_step P ldr (by simp)
    (dirac_steps_update (BRB.ProgramStep.call (u ldr) m rfl h)
      (fun i hi => BRB.ProgramStep.callIdle (u i) m hi))
    (BRB.NetworkStep.call w m)

/-! ### The algorithm -/

/-- The transitions of the gather instance over Bracha's broadcast
(`Gather.instanceOverBracha`),
stated over the composition's state: one constructor per case of
`Gather.instanceOverBracha_step_iff_algorithm`. All transitions are Dirac. -/
inductive AlgorithmOverBracha (P : Parameters) :
    StateOverBracha P.n X → Label P.n X → PMF (StateOverBracha P.n X) → Prop
  /-- The call arrives: the gather program records the payload. -/
  | call (s : StateOverBracha P.n X) (id : Fin P.n) (x : X)
      (h : ((gatherProgramsAndNetwork s).processVariables id).input = none) :
      AlgorithmOverBracha P s (.call id x)
        (PMF.pure (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).setProcessVariables
          id
          { (gatherProgramsAndNetwork s).processVariables id with input := some x })))
  /-- Input-enabledness loop for `call`: nothing moves. -/
  | callLoop (s : StateOverBracha P.n X) (id : Fin P.n) (x : X) :
      AlgorithmOverBracha P s (.call id x) (PMF.pure s)
  /-- A silent step of one input instance. -/
  | inputBroadcastTau (s : StateOverBracha P.n X) (k : Fin P.n) (c : BRB.BrachaState P.n X)
      (hb : BRB.BrachaAlgorithm P k (inputBroadcasts s k) .tau (PMF.pure c)) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setInputBroadcasts s (Function.update (inputBroadcasts s) k c)))
  /-- A silent step of one bind instance. -/
  | bindBroadcastTau (s : StateOverBracha P.n X) (q : Fin P.n) (d : BRB.BrachaState P.n
    (AcceptedPairs P.n X))
      (hb : BRB.BrachaAlgorithm P q (bindBroadcasts s q) .tau (PMF.pure d)) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setBindBroadcasts s (Function.update (bindBroadcasts s) q d)))
  /-- Asynchronous delivery on the gather network. -/
  | deliver (s : StateOverBracha P.n X) (i j : Fin P.n) (m : Message P.n X)
      (h : m ∈ (gatherProgramsAndNetwork s).sent j) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).receiveMessage i j
          m)))
  /-- `ECHO`: the process is called and its accepted pairs number at least
  `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is those pairs,
  `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | echo (s : StateOverBracha P.n X) (j : Fin P.n)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input ≠ none)
      (hcard : P.n - P.f ≤ ((gatherProgramsAndNetwork s).processVariables j).accepted.card)
      (hsend : ((gatherProgramsAndNetwork s).processVariables j).sentEcho = none) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s (((gatherProgramsAndNetwork s).setProcessVariables
          j
          { (gatherProgramsAndNetwork s).processVariables j with
            sentEcho := some ((gatherProgramsAndNetwork s).processVariables
            j).accepted
            }).multicast j
            (.echo ((gatherProgramsAndNetwork s).processVariables j).accepted))))
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in the
  vote payload, are delivered here, and the process has multicast its own
  `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO` before `VOTE`. -/
  | vote (s : StateOverBracha P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input ≠ none)
      (hech : ((gatherProgramsAndNetwork s).processVariables j).sentEcho ≠ none)
      (happ : approvedBy ((gatherProgramsAndNetwork s).processVariables j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A,
          Message.echo A ∈ (gatherProgramsAndNetwork s).received j q ∧ approvedBy
            ((gatherProgramsAndNetwork s).processVariables
            j) A ∧ A
            ⊆ U)
      (hsend : ((gatherProgramsAndNetwork s).processVariables j).sentVote = none) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s (((gatherProgramsAndNetwork s).setProcessVariables
          j
          { (gatherProgramsAndNetwork s).processVariables j with sentVote := some U }).multicast j
            (.vote U))))
  /-- The process calls the instance broadcasting its input, and that instance broadcasts the
  payload its own variables hold. AFW25's Algorithm 5, line 6, and LeslieBP's Algorithm 4,
  `BRB_id.call(m)`. -/
  | inputBroadcastCall (s : StateOverBracha P.n X) (j : Fin P.n) (x : X)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input = some x)
      (hb : ((inputBroadcasts s j).processVariables j).input = none) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setInputBroadcasts s
          (Function.update (inputBroadcasts s) j
            (((inputBroadcasts s j).setProcessVariables j
              { (inputBroadcasts s j).processVariables j with input := some x }).multicast j (.init
                x)))))
  /-- `BIND`: `n − f` senders' approved `VOTE` payloads, each contained in the
  bind payload, are delivered here, and the bind instance broadcasts the payload.
  The process has multicast its own `VOTE` and has not called its own bind
  broadcast. The main thread of AFW25's Algorithm 5 sends `VOTE` before `BIND`,
  and sends `BIND` once, at line 17. The payload handed to the broadcast is
  written to the gather program's variables. -/
  | bindCall (s : StateOverBracha P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input ≠ none)
      (hvot : ((gatherProgramsAndNetwork s).processVariables j).sentVote ≠ none)
      (hsnd : ((gatherProgramsAndNetwork s).processVariables j).sentBind = none)
      (happ : approvedBy ((gatherProgramsAndNetwork s).processVariables j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Message.vote W ∈ (gatherProgramsAndNetwork s).received j q ∧ approvedBy
            ((gatherProgramsAndNetwork s).processVariables
            j) W ∧ W
            ⊆ U)
      (hbc : ((bindBroadcasts s j).processVariables j).input = none) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setBindBroadcasts (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork
          s).setProcessVariables j
            { (gatherProgramsAndNetwork s).processVariables j with sentBind := some U }))
          (Function.update (bindBroadcasts s) j
            (((bindBroadcasts s j).setProcessVariables j
              { (bindBroadcasts s j).processVariables j with input := some U }).multicast j (.init
                U)))))
  /-- Byzantine injection on the gather network. -/
  | byzantine (s : StateOverBracha P.n X) (j : Fin P.n) (m : Message P.n X) (h : j ∈
      (gatherProgramsAndNetwork
    s).F) :
      AlgorithmOverBracha P s .tau (PMF.pure (setGatherProgramsAndNetwork s
        ((gatherProgramsAndNetwork s).multicast j m)))
  /-- An input instance returns to `j`, which files the value it returned. -/
  | inputBroadcastRet (s : StateOverBracha P.n X) (k j : Fin P.n) (v : X) (c : BRB.BrachaState P.n
    X)
      (hb : BRB.BrachaAlgorithm P k (inputBroadcasts s k) (.ret j v) (PMF.pure c)) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setInputBroadcasts (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork
          s).setProcessVariables j
            { (gatherProgramsAndNetwork s).processVariables j with
              inputBroadcastReturned := Function.update ((gatherProgramsAndNetwork
                s).processVariables
                j).inputBroadcastReturned k (some v) }))
          (Function.update (inputBroadcasts s) k c)))
  /-- A bind instance returns to `j`, which files the payload it returned. -/
  | bindRet (s : StateOverBracha P.n X) (q j : Fin P.n) (U : AcceptedPairs P.n X)
      (d : BRB.BrachaState P.n (AcceptedPairs P.n X))
      (hb : BRB.BrachaAlgorithm P q (bindBroadcasts s q) (.ret j U) (PMF.pure d)) :
      AlgorithmOverBracha P s .tau
        (PMF.pure (setBindBroadcasts (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork
          s).setProcessVariables j
            { (gatherProgramsAndNetwork s).processVariables j with
              bindBroadcastReturned := Function.update ((gatherProgramsAndNetwork
                s).processVariables
                j).bindBroadcastReturned q (some U) }))
          (Function.update (bindBroadcasts s) q d)))
  /-- Return: the output's entries are held here, `n − f` bind payloads held
  here are sub-maps of it, and the returner has called its own bind broadcast.
  The `BIND` broadcast of AFW25's Algorithm 5, line 17, precedes the wait of line
  18. The label carries the instance's core, which this transition writes if it
  is unwritten. -/
  | ret (s : StateOverBracha P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : ((gatherProgramsAndNetwork s).processVariables id).input ≠ none)
      (hbind : ((gatherProgramsAndNetwork s).processVariables id).sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn ((gatherProgramsAndNetwork
        s).processVariables id) k
        x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          holdsBindBroadcastReturn ((gatherProgramsAndNetwork s).processVariables id) q U ∧
            AcceptedPairs.subMap U
            g)
      (hr : ((gatherProgramsAndNetwork s).processVariables id).returned = false) :
      AlgorithmOverBracha P s (.ret id g ((core s).getD (coreOfNetwork P (gatherProgramsAndNetwork
        s).2)))
        (PMF.pure (setCore (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork
          s).setProcessVariables id
          { (gatherProgramsAndNetwork s).processVariables id with returned := true }))
          (some ((core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2)))))
  /-- Corruption (deviation D1), together across the gather network state and every broadcast
  coordinate. -/
  | fail (s : StateOverBracha P.n X) (id : Fin P.n) :
      AlgorithmOverBracha P s (.fail id)
        (PMF.pure (corruptAll P id (InstanceState.corrupt P id) (InstanceState.corrupt P id) s))

/-! ### The characterisation by the algorithm -/

/-- **The projection.** -/
theorem instanceOverBracha_step_algorithm (P : Parameters) :
    ∀ (s : StateOverBracha P.n X) (l : InstanceLabel P.n X) (μ : PMF (StateOverBracha P.n X)),
      (instanceOverBracha P X).step s l μ →
      ∃ l₀, specificationLabelMap P.n X l = some l₀ ∧ AlgorithmOverBracha P s l₀ μ := by
  have hIn : ∀ k : Fin P.n,
    (BRB.brachaInstance P k X).IsLTS := fun k => BRB.brachaInstance_isLTS P k
  have hBind : ∀ q : Fin P.n,
    (BRB.brachaInstance P q (AcceptedPairs P.n X)).IsLTS := fun q => BRB.brachaInstance_isLTS P q
  rintro ⟨⟨u, w⟩, a, b⟩ l μ hstep
  rcases (instanceOverBroadcasts_step_iff P X (fun k => BRB.brachaInstance P k X)
      (fun q => BRB.brachaInstance P q (AcceptedPairs P.n X)) _ l μ).mp hstep with ⟨rfl, e,
        hev⟩ | hlab
  · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
      instanceOverBroadcastsExtended_synchronised_cases hIn hBind (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_notOwn (Ne.symm hi) (hproc i))
      have hw : w' = { w with network := w.network.recordSent j m } := PMF.pure_injective
        (networkStep_send hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw; subst ha; subst hb
      cases m with
      | echo A =>
        obtain ⟨rfl, hinp, hcard, hsend, hx⟩ := programStep_send_echo_own (hproc j)
        rw [stateOverBroadcasts_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact AlgorithmOverBracha.echo _ j hinp hcard hsend
      | vote U =>
        obtain ⟨hinp, hech, happ, hQ, hsend, hx⟩ := programStep_send_vote_own (hproc j)
        rw [stateOverBroadcasts_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact AlgorithmOverBracha.vote _ j U hinp hech happ hQ hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hnet
      have hw' : w' = w := PMF.pure_injective hw
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw'; subst ha; subst hb
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_notOwn (Ne.symm hi') (hproc i'))
      rw [stateOverBroadcasts_deliver (PMF.pure_injective (programStep_deliver_own (hproc i))) hfor]
      exact AlgorithmOverBracha.deliver _ i j m hmem
    | inputBroadcastRet k j v =>
      have hw : w' = w := PMF.pure_injective (networkStep_inputBroadcastRet hnet)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw; subst hb
      have himpl : BRB.BrachaAlgorithm P k (a k) (.ret j v) (PMF.pure (a' k)) :=
        brachaInstance_step_at (l := Sum.inl (BRB.Label.ret j v)) rfl
          (System.step_of_mapIdle_step (l₀ := Sum.inl (BRB.Label.ret j v)) (by simp) (hin k))
      have haf : ∀ k', k' ≠ k → a' k' = a k' :=
        fun k' hk' => System.mapIdle_eq_of_step_none (by simp [hk']) (hin k')
      have ha : a' = Function.update a k (a' k) := Function.eq_update_iff.mpr ⟨rfl, haf⟩
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_inputBroadcastRet_notOwn (Ne.symm hi) (hproc
          i))
      have hxj := PMF.pure_injective (programStep_inputBroadcastRet_own (hproc j))
      rw [Function.eq_update_iff.mpr ⟨hxj, hfor⟩, ha]
      exact AlgorithmOverBracha.inputBroadcastRet _ k j v (a' k) himpl
    | inputBroadcastCall j y =>
      have hw : w' = w := PMF.pure_injective (networkStep_inputBroadcastCall hnet)
      have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
      subst hw; subst hb
      obtain ⟨hinp, hxj⟩ := programStep_inputBroadcastCall_own (hproc j)
      have hxall : ∀ i, x i = u i := fun i => by
        by_cases hi : i = j
        · subst hi; exact PMF.pure_injective hxj
        · exact PMF.pure_injective
            (programStep_inputBroadcastCall_notOwn (Ne.symm hi) (hproc i))
      obtain ⟨hbin, haj⟩ := brachaInstance_call_transition
        (System.step_of_mapIdle_step (l₀ := Sum.inl (BRB.Label.call y)) (by simp) (hin j))
      have haf : ∀ k, k ≠ j → a' k = a k :=
        fun k hk => System.mapIdle_eq_of_step_none (by simp [hk]) (hin k)
      have ha : a' = Function.update a j
          (((a j).setProcessVariables j { (a j).processVariables j with input := some y }).multicast
            j (.init y)) :=
        Function.eq_update_iff.mpr ⟨haj, haf⟩
      subst ha
      rw [stateOverBroadcasts_idle hxall, stateOverBroadcasts_setInputBroadcasts]
      exact AlgorithmOverBracha.inputBroadcastCall _ j y hinp hbin
    | bindCall j U =>
      have hw : w' = w := PMF.pure_injective (networkStep_bindCall hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hinp, hvot, hsnd, happ, hQ, hxj⟩ := programStep_bindCall_own (hproc j)
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_bindCall_notOwn (Ne.symm hi) (hproc i))
      obtain ⟨hbc, hbj⟩ := brachaInstance_call_transition
        (System.step_of_mapIdle_step (l₀ := Sum.inl (BRB.Label.call U)) (by simp) (hbind j))
      have hbf : ∀ q, q ≠ j → b' q = b q :=
        fun q hq => System.mapIdle_eq_of_step_none (by simp [hq]) (hbind q)
      have hb : b' = Function.update b j
          (((b j).setProcessVariables j { (b j).processVariables j with input := some U }).multicast
            j (.init U)) :=
        Function.eq_update_iff.mpr ⟨hbj, hbf⟩
      subst hb
      rw [Function.eq_update_iff.mpr ⟨PMF.pure_injective hxj, hfor⟩]
      exact AlgorithmOverBracha.bindCall _ j U hinp hvot hsnd happ hQ hbc
    | bindRet q j U =>
      have hw : w' = w := PMF.pure_injective (networkStep_bindRet hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      subst hw; subst ha
      have himpl : BRB.BrachaAlgorithm P q (b q) (.ret j U) (PMF.pure (b' q)) :=
        brachaInstance_step_at (l := Sum.inl (BRB.Label.ret j U)) rfl
          (System.step_of_mapIdle_step (l₀ := Sum.inl (BRB.Label.ret j U)) (by simp) (hbind q))
      have hbf : ∀ q', q' ≠ q → b' q' = b q' :=
        fun q' hq' => System.mapIdle_eq_of_step_none (by simp [hq']) (hbind q')
      have hb : b' = Function.update b q (b' q) := Function.eq_update_iff.mpr ⟨rfl, hbf⟩
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_bindRet_notOwn (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (programStep_bindRet_own (hproc j))
      rw [Function.eq_update_iff.mpr ⟨hxj, hfor⟩, hb]
      exact AlgorithmOverBracha.bindRet _ q j U (b' q) himpl
  · by_cases hlτ : l = Sum.inl Label.tau
    · subst hlτ
      refine ⟨Label.tau, rfl, ?_⟩
      rcases instanceOverBroadcastsExtended_tau_cases hIn hBind hlab with
        ⟨v, rfl, hn⟩ | ⟨k, c, rfl, hs⟩ | ⟨q, d, rfl, hs⟩
      · obtain ⟨jj, m, hF, hv⟩ := networkStep_tau hn
        have hv' : v = { w with network := w.network.recordSent jj m } := PMF.pure_injective hv
        subst hv'
        rw [stateOverBroadcasts_recordSent]
        exact AlgorithmOverBracha.byzantine _ jj m hF
      · have himpl : BRB.BrachaAlgorithm P k (a k) BRB.Label.tau (PMF.pure c) :=
          brachaInstance_step_at (l := (Silent.τ : BRB.InstanceLabel P.n X)) rfl hs
        rw [stateOverBroadcasts_setInputBroadcasts]
        exact AlgorithmOverBracha.inputBroadcastTau _ k c himpl
      · have himpl : BRB.BrachaAlgorithm P q (b q) BRB.Label.tau (PMF.pure d) :=
          brachaInstance_step_at (l := (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X))) rfl
            hs
        rw [stateOverBroadcasts_setBindBroadcasts]
        exact AlgorithmOverBracha.bindBroadcastTau _ q d himpl
    · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
        instanceOverBroadcastsExtended_synchronised_cases hIn hBind (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call id y =>
          have hw : w' = w := PMF.pure_injective (networkStep_call hnet)
          have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
          have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
          subst hw; subst ha; subst hb
          obtain ⟨hinp, hxj⟩ := programStep_call_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_call_notOwn (Ne.symm hi) (hproc i))
          refine ⟨Label.call id y, rfl, ?_⟩
          rw [stateOverBroadcasts_setProcessVariables (PMF.pure_injective hxj) hfor]
          exact AlgorithmOverBracha.call _ id y hinp
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
            fun i hi => PMF.pure_injective (programStep_ret_notOwn (Ne.symm hi) (hproc i))
          refine ⟨_, rfl, ?_⟩
          rw [stateOverBroadcasts_ret (PMF.pure_injective hxj) hfor]
          exact AlgorithmOverBracha.ret _ id g hinp hbnd hsub hQ hr
        | fail id =>
          have hw : w' = { w with network := w.network.corrupt P id } :=
            PMF.pure_injective (networkStep_fail hnet)
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hproc i))
          have ha : ∀ k, a' k = InstanceState.corrupt P id (a k) := fun k =>
            PMF.pure_injective (brachaAlgorithm_fail (brachaInstance_step_at (l := Sum.inl
              (BRB.Label.fail
              id)) rfl
              (System.step_of_mapIdle_step (l₀ := Sum.inl (BRB.Label.fail id)) rfl (hin k))))
          have hb : ∀ q, b' q = InstanceState.corrupt P id (b q) := fun q =>
            PMF.pure_injective (brachaAlgorithm_fail (brachaInstance_step_at (l := Sum.inl
              (BRB.Label.fail
              id)) rfl
              (System.step_of_mapIdle_step (l₀ := Sum.inl (BRB.Label.fail id)) rfl (hbind q))))
          subst hw
          refine ⟨_, rfl, ?_⟩
          rw [funext ha, funext hb, stateOverBroadcasts_corrupt hxall]
          exact AlgorithmOverBracha.fail _ id
      | inr ev =>
        cases ev with
        | callLoop id y =>
          have hw : w' = w := PMF.pure_injective (networkStep_callLoop hnet)
          have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
          have hb : b' = b := funext fun q => System.mapIdle_eq_of_step_none rfl (hbind q)
          subst hw; subst ha; subst hb
          have hxall : ∀ i,
            x i = u i := fun i => PMF.pure_injective (programStep_callLoop (hproc i))
          refine ⟨Label.call id y, rfl, ?_⟩
          rw [stateOverBroadcasts_idle hxall]
          exact AlgorithmOverBracha.callLoop _ id y

/-- **The embedding.** -/
theorem algorithm_instanceOverBracha_step (P : Parameters) :
    ∀ (s : StateOverBracha P.n X) (l₀ : Label P.n X) (μ : PMF (StateOverBracha P.n X)),
      AlgorithmOverBracha P s l₀ μ →
      ∃ l, specificationLabelMap P.n X l = some l₀ ∧ (instanceOverBracha P X).step s l μ := by
  rintro ⟨⟨u, w⟩, a, b⟩ l₀ μ htransition
  cases htransition with
  | call id x h =>
    exact ⟨Sum.inl (.call id x), rfl,
      instanceOverBroadcasts_label_step (a' := a) (b' := b) (by simp)
      (dirac_steps_update (ProgramStep.call (u id) x h)
        (fun i hi => ProgramStep.callIdle (u i) id x (Ne.symm hi)))
      (NetworkStep.call w id x)
      (fun k => System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | callLoop id x =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      instanceOverBroadcasts_label_step (x := u) (w' := w) (a' := a) (b' := b) (by simp) (fun i =>
        ?_)
        (NetworkStep.callLoop w id x) (fun k => ?_) (fun q => System.mapIdle_unchanged rfl)⟩
    · by_cases hi : i = id
      · subst hi; exact ProgramStep.callLoop (u i) x
      · exact ProgramStep.callLoopIdle (u i) id x (Ne.symm hi)
    · exact System.mapIdle_unchanged rfl
  | inputBroadcastTau k c hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_input (transition_brachaInstance_step_inl (by simp) hb)⟩
  | bindBroadcastTau q d hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_bind (transition_brachaInstance_step_inl (by simp) hb)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (a' := a) (b' := b) (GatherEvent.deliver i j m)
        (dirac_steps_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h) (fun k => System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | echo j hin hcard hsend =>
    exact ⟨Sum.inl Label.tau, rfl, instanceOverBroadcasts_event_step (a' := a) (b' := b)
      (GatherEvent.send j (.echo (u j).processVariables.accepted))
      (dirac_steps_update (ProgramStep.sendEcho (u j) hin hcard hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo (u j).processVariables.accepted) (Ne.symm
          hi)))
      (NetworkStep.send w j (.echo (u j).processVariables.accepted)) (fun k =>
        System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | vote j U hin hech happ hQ hsend =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (a' := a) (b' := b) (GatherEvent.send j (.vote U))
        (dirac_steps_update
        (ProgramStep.sendVote (u j) U hin hech happ hQ hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote U) (Ne.symm hi)))
      (NetworkStep.send w j (.vote U)) (fun k => System.mapIdle_unchanged rfl)
      (fun q => System.mapIdle_unchanged rfl)⟩
  | inputBroadcastCall j x hin hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (x := u) (w' := w) (b' := b)
        (GatherEvent.inputBroadcastCall j x)
        (fun i => by
          by_cases hi : i = j
          · subst hi; exact ProgramStep.inputBroadcastCall (u i) x hin
          · exact ProgramStep.inputBroadcastCallIdle (u i) j x (Ne.symm hi))
        (NetworkStep.inputBroadcastCallIdle w j x)
        (System.mapIdle_step_update (by simp) (fun k hk => by simp [hk])
          (transition_brachaInstance_call_step P j (a j) x hb))
        (fun q => System.mapIdle_unchanged rfl)⟩
  | bindCall j U hin hvot hsnd happ hQ hbc =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (GatherEvent.bindCall j U)
        (dirac_steps_update (ProgramStep.bindCall (u j) U hin hvot hsnd happ hQ)
          (fun i hi => ProgramStep.bindCallIdle (u i) j U (Ne.symm hi)))
        (NetworkStep.bindCallIdle w j U) (fun k => System.mapIdle_unchanged rfl)
        (System.mapIdle_step_update (by simp) (fun q hq => by simp [hq])
          (transition_brachaInstance_call_step P j (b j) U hbc))⟩
  | byzantine j m h =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_tau_network (NetworkStep.byzantine w j m h)⟩
  | inputBroadcastRet k j v c hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (b' := b) (GatherEvent.inputBroadcastRet k j v)
        (dirac_steps_update (ProgramStep.inputBroadcastRetReceive (u j) k v)
        (fun i hi => ProgramStep.inputBroadcastRetIdle (u i) k j v (Ne.symm hi)))
      (NetworkStep.inputBroadcastRetIdle w k j v)
      (System.mapIdle_step_update (by simp) (fun k' hk' => by simp [hk'])
        (transition_brachaInstance_step_inl (by simp)
        hb))
      (fun q => System.mapIdle_unchanged rfl)⟩
  | bindRet q j U d hb =>
    exact ⟨Sum.inl Label.tau, rfl,
      instanceOverBroadcasts_event_step (w' := w) (a' := a) (GatherEvent.bindRet q j U)
        (dirac_steps_update (ProgramStep.bindRetReceive (u j) q U)
        (fun i hi => ProgramStep.bindRetIdle (u i) q j U (Ne.symm hi)))
      (NetworkStep.bindRetIdle w q j U) (fun k => System.mapIdle_unchanged rfl)
      (System.mapIdle_step_update (by simp) (fun q' hq' => by simp [hq'])
        (transition_brachaInstance_step_inl (by simp)
        hb))⟩
  | ret id g hin hbind hsub hQ hr =>
    exact ⟨Sum.inl (.ret id g (w.core.getD (coreOfNetwork P w.network))), rfl,
      instanceOverBroadcasts_label_step (a' := a) (b' := b) (by simp)
        (dirac_steps_update (ProgramStep.ret (u id) g _ hin hbind hsub hQ hr)
          (fun i hi => ProgramStep.retIdle (u i) id g _ (Ne.symm hi)))
        (NetworkStep.ret w id g) (fun k => System.mapIdle_unchanged rfl)
        (fun q => System.mapIdle_unchanged rfl)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, instanceOverBroadcasts_label_step (x := u) (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)
      (System.mapIdle_step_all (l₀ := fun _ => Sum.inl (BRB.Label.fail id)) (fun k => rfl)
        (fun k => transition_brachaInstance_step_inl (by simp) (BRB.BrachaAlgorithm.fail (a k) id)))
      (System.mapIdle_step_all (l₀ := fun _ => Sum.inl (BRB.Label.fail id)) (fun q => rfl)
        (fun q => transition_brachaInstance_step_inl (by simp) (BRB.BrachaAlgorithm.fail (b q)
          id)))⟩

/-- **The characterisation by the algorithm.** At a specification label `l₀`, the transitions
of the instance over the labels `specificationLabelMap` sends to `l₀` are exactly the `l₀`
transitions of `AlgorithmOverBracha`, on the same state and with the same distribution. -/
theorem instanceOverBracha_step_iff_algorithm (P : Parameters) (s : StateOverBracha P.n X)
    (l₀ : Label P.n X) (μ : PMF (StateOverBracha P.n X)) :
    (∃ l, specificationLabelMap P.n X l = some l₀ ∧ (instanceOverBracha P X).step s l μ) ↔
    AlgorithmOverBracha P s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, htransition⟩ := instanceOverBracha_step_algorithm P s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n X)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact htransition
  · exact algorithm_instanceOverBracha_step P s l₀ μ

/-- info: 'PLTS.ABA.Gather.instanceOverBracha_step_iff_algorithm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBracha_step_iff_algorithm

end Gather
end ABA
end PLTS
