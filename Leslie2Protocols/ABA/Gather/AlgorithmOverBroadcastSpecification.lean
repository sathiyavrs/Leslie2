/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.CompositionStepCases
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The algorithm of the gather instance over the broadcast specification

`AlgorithmOverBroadcastSpecification` states the transitions of
`Gather.instanceOverBroadcastSpecification` (`ABA/Gather/Composition.lean`) -- the `n` gather
programs beside the gather network, in parallel with `n` broadcast specifications, one per process,
each carrying that process's input -- over the composition's state, through the three projections
`gatherProgramsAndNetwork`, `inputBroadcasts` and `core`, one constructor per case of
`instanceOverBroadcastSpecification_step_iff_algorithm`. It is a relation on that state; the system
is the composition. The algorithm is blueprint Algorithm 4, the binding form of AFW25's
Algorithm 5.

`instanceOverBroadcastSpecification_step_iff_algorithm` is the characterisation: at every label
`l`, the `l`-transitions of the composition are exactly the `l`-transitions of
`AlgorithmOverBroadcastSpecification`, on the same composed state and with the same distribution.

The transitions are the gather's call and its input-enabledness loop (`call`, `callLoop`), the
commit of one input instance (`commitInputEntry`), delivery on the gather network (`deliver`), the
three multicasts of the gather network (`echo`, `vote`, `bind`), the call of an input instance on
its two transitions (`inputBroadcastCall`, `inputBroadcastCallLoop`), Byzantine injection
(`byzantine`), a return of an input instance (`inputBroadcastRet`), the gather's return (`ret`),
the announcement of the core (`announceCore`) and corruption (`fail`). `ECHO`, `VOTE` and `BIND`
are messages of the gather network, each multicast once by a correct sender and received by
delivery, as in AFW25's Algorithm 5, lines 10, 13 and 17.

## The two transitions of a call

The gather's `call id x` carries two transitions, as the specification's does: `call` records the
payload at a program holding no input, and `callLoop` moves nothing at a program holding one. A
broadcast specification takes its own `call x` on two transitions, the call at an empty input and
the unguarded input-enabledness loop. The composition reads an input instance along
`inputBroadcastLabelMap id`, which puts both under the event `inputBroadcastCall id x`, so that
event carries two transitions: `inputBroadcastCall`, where the instance records the payload, and
`inputBroadcastCallLoop`, where it loops and nothing moves. The gather's own `call id x` reaches no
instance.

## The return and the core

The gather network writes the core at the instance's first return: `ret` writes
`(core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2)` into the field `core`, and its
label carries the returned map alone. `announceCore` announces the written core on `core C`, and
nothing moves.

## The corrupted set

Each broadcast specification carries its own corrupted set, kept equal to the gather network's by
the `fail` transition. A commit guard therefore reads the corrupted set of the instance it commits
in. -/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X]

/-! ### The broadcast specification's transitions, by label class -/

section SpecificationStepCases
variable {M : Type} {P : Parameters} {ldr : Fin P.n} {s : BRB.SpecState P.n M}
  {μ : PMF (BRB.SpecState P.n M)}

/-- The two transitions of a call: the write and the loop. -/
theorem specStep_call {m : M} (h : BRB.Step P ldr s (.call m) μ) :
    (s.input = none ∧ μ = PMF.pure { s with input := some m }) ∨ μ = PMF.pure s := by
  cases h
  case call => exact Or.inl ⟨by assumption, rfl⟩
  case callLoop => exact Or.inr rfl

/-- The one silent transition: the commit. -/
theorem specStep_tau (h : BRB.Step P ldr s .tau μ) :
    ∃ m : M, s.val = none ∧ (ldr ∈ s.F ∨ s.input = some m) ∧
      μ = PMF.pure { s with val := some m } := by
  cases h
  case commit m hv hm => exact ⟨m, hv, hm, rfl⟩

/-- The one return transition. -/
theorem specStep_ret {id : Fin P.n} {m : M} (h : BRB.Step P ldr s (.ret id m) μ) :
    s.val = some m ∧ s.ret id = false ∧
      μ = PMF.pure { s with ret := Function.update s.ret id true } := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

/-- The one corruption transition. -/
theorem specStep_fail {id : Fin P.n} (h : BRB.Step P ldr s (.fail id) μ) :
    μ = PMF.pure (s.corrupt P id) := by
  cases h; rfl

end SpecificationStepCases
/-! ### The algorithm -/

/-- The transitions of the gather instance over the broadcast specification
(`Gather.instanceOverBroadcastSpecification`), stated over the composition's state: one constructor
per case of `Gather.instanceOverBroadcastSpecification_step_iff_algorithm`. All transitions are
Dirac. -/
inductive AlgorithmOverBroadcastSpecification (P : Parameters) :
    StateOverBroadcastSpecification P.n X → Label P.n X → PMF (StateOverBroadcastSpecification P.n
      X) → Prop
  /-- The call arrives at a program holding no input: the gather program records the payload. -/
  | call (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (x : X)
      (h : ((gatherProgramsAndNetwork s).processVariables id).input = none) :
      AlgorithmOverBroadcastSpecification P s (.call id x)
        (PMF.pure (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).setProcessVariables
          id { (gatherProgramsAndNetwork
          s).processVariables id with
          input := some x })))
  /-- Input-enabledness loop for `call`, at a program holding an input: nothing moves. -/
  | callLoop (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (x : X)
      (hin : ((gatherProgramsAndNetwork s).processVariables id).input ≠ none) :
      AlgorithmOverBroadcastSpecification P s (.call id x) (PMF.pure s)
  /-- An input instance commits: anything under a corrupted leader, the
  leader's input otherwise. -/
  | commitInputEntry (s : StateOverBroadcastSpecification P.n X) (k : Fin P.n) (v : X)
      (hv : (inputBroadcasts s k).val = none) (hm : k ∈ (inputBroadcasts s k).F ∨ (inputBroadcasts s
        k).input = some v) :
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setInputBroadcasts s (Function.update (inputBroadcasts s) k { inputBroadcasts s k
          with val := some v })))
  /-- Asynchronous delivery on the gather network. -/
  | deliver (s : StateOverBroadcastSpecification P.n X) (i j : Fin P.n) (m : Message P.n X)
      (h : m ∈ (gatherProgramsAndNetwork s).sent j) :
      AlgorithmOverBroadcastSpecification P s .tau (PMF.pure (setGatherProgramsAndNetwork s
        ((gatherProgramsAndNetwork
        s).receiveMessage i j m)))
  /-- `ECHO`: the process is called and its accepted pairs number at least
  `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is those pairs,
  `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | echo (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input ≠ none)
      (hcard : P.n - P.f ≤ ((gatherProgramsAndNetwork s).processVariables j).accepted.card)
      (hsend : ((gatherProgramsAndNetwork s).processVariables j).sentEcho = none) :
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s (((gatherProgramsAndNetwork s).setProcessVariables
          j
          { (gatherProgramsAndNetwork s).processVariables j with
            sentEcho := some ((gatherProgramsAndNetwork s).processVariables
            j).accepted
            }).multicast j
            (.echo ((gatherProgramsAndNetwork s).processVariables j).accepted))))
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in the
  vote payload, are delivered here, and the process has multicast its own
  `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO` before `VOTE` (D35). -/
  | vote (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
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
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s (((gatherProgramsAndNetwork s).setProcessVariables
          j
          { (gatherProgramsAndNetwork s).processVariables j with sentVote := some U }).multicast j
            (.vote U))))
  /-- `BIND U`: the process is called (D8), `n − f` senders' approved `VOTE` payloads, each
  contained in `U`, are delivered here, the process has multicast its own `VOTE`, and it has
  not multicast a `BIND`. It multicasts `U` once on the gather network and records it as
  `sentBind`. The main thread of AFW25's Algorithm 5 sends `VOTE` before `BIND`, and sends
  `BIND` to all processes once, at line 17. -/
  | bind (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (U : AcceptedPairs P.n X)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input ≠ none)
      (hvot : ((gatherProgramsAndNetwork s).processVariables j).sentVote ≠ none)
      (happ : approvedBy ((gatherProgramsAndNetwork s).processVariables j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W,
          Message.vote W ∈ (gatherProgramsAndNetwork s).received j q ∧
            approvedBy ((gatherProgramsAndNetwork s).processVariables j) W ∧ W ⊆ U)
      (hsend : ((gatherProgramsAndNetwork s).processVariables j).sentBind = none) :
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s (((gatherProgramsAndNetwork s).setProcessVariables
          j
          { (gatherProgramsAndNetwork s).processVariables j with sentBind := some U }).multicast j
            (.bind U))))
  /-- The process calls the instance broadcasting its input, and that instance records the payload
  its own variables hold. AFW25's Algorithm 5, line 6, and LeslieBP's Algorithm 4,
  `BRB_id.call(m)`. -/
  | inputBroadcastCall (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (x : X)
      (hin : ((gatherProgramsAndNetwork s).processVariables j).input = some x)
      (hb : (inputBroadcasts s j).input = none) :
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setInputBroadcasts s (Function.update (inputBroadcasts s) j
          { inputBroadcasts s j with input := some x })))
  /-- The call to an input instance with that instance taking it on its input-enabledness loop:
  nothing moves. -/
  | inputBroadcastCallLoop (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n)
      (x : X) (hin : ((gatherProgramsAndNetwork s).processVariables j).input = some x) :
      AlgorithmOverBroadcastSpecification P s .tau (PMF.pure s)
  /-- Byzantine injection on the gather network. -/
  | byzantine (s : StateOverBroadcastSpecification P.n X) (j : Fin P.n) (m : Message P.n X) (h : j ∈
    (gatherProgramsAndNetwork s).F) :
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).multicast j m)))
  /-- An input instance returns its committed value to `j`, which files it as its returned value. -/
  | inputBroadcastRet (s : StateOverBroadcastSpecification P.n X) (k j : Fin P.n) (v : X)
      (hv : (inputBroadcasts s k).val = some v) (hr : (inputBroadcasts s k).ret j = false) :
      AlgorithmOverBroadcastSpecification P s .tau
        (PMF.pure (setInputBroadcasts (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork
          s).setProcessVariables j
            { (gatherProgramsAndNetwork s).processVariables j with
              inputBroadcastReturned := Function.update ((gatherProgramsAndNetwork
                s).processVariables
                j).inputBroadcastReturned k (some v) }))
          (Function.update (inputBroadcasts s) k
            { inputBroadcasts s k with ret := Function.update (inputBroadcasts s k).ret j true })))
  /-- Return: the output's entries are held here, `n − f` senders' `BIND` payloads
  delivered here are sub-maps of it, and the returner has multicast its own
  `BIND`. The `BIND` multicast of AFW25's Algorithm 5, line 17, precedes the wait of line
  18. The transition writes the instance's core if it is unwritten, and the label carries the
  returned map alone. -/
  | ret (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : ((gatherProgramsAndNetwork s).processVariables id).input ≠ none)
      (hbind : ((gatherProgramsAndNetwork s).processVariables id).sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn ((gatherProgramsAndNetwork
        s).processVariables id) k
        x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          Message.bind U ∈ (gatherProgramsAndNetwork s).received id q ∧ AcceptedPairs.subMap U g)
      (hr : ((gatherProgramsAndNetwork s).processVariables id).returned = false) :
      AlgorithmOverBroadcastSpecification P s (.ret id g)
        (PMF.pure (setCore (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork
          s).setProcessVariables id
          { (gatherProgramsAndNetwork s).processVariables id with returned := true }))
          (some ((core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2)))))
  /-- The core `C` is announced (D29): nothing moves. -/
  | announceCore (s : StateOverBroadcastSpecification P.n X) (C : AcceptedPairs P.n X)
      (h : core s = some C) :
      AlgorithmOverBroadcastSpecification P s (.core C) (PMF.pure s)
  /-- Corruption (deviation D1), together across the gather network state and every input
  instance. -/
  | fail (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n) :
      AlgorithmOverBroadcastSpecification P s (.fail id)
        (PMF.pure (corruptAll P id (BRB.SpecState.corrupt P id) s))

/-! ### The characterisation by the algorithm -/

/-- **The projection.** -/
theorem instanceOverBroadcastSpecification_step_algorithm (P : Parameters) :
    ∀ (s : StateOverBroadcastSpecification P.n X) (l : Label P.n X)
      (μ : PMF (StateOverBroadcastSpecification P.n X)),
      (instanceOverBroadcastSpecification P X).step s l μ →
      AlgorithmOverBroadcastSpecification P s l μ := by
  have hIn : ∀ k : Fin P.n, (BRB.specInst P k X).IsLTS := fun k => BRB.specInst_isLTS P k
  rintro ⟨⟨u, w⟩, a⟩ l μ hstep
  rcases (instanceOverBroadcasts_step_iff P X (fun k => BRB.specInst P k X) _ l μ).mp
      hstep with ⟨rfl, e, hev⟩ | hlab
  · obtain ⟨x, w', a', rfl, hproc, hnet, hin⟩ :=
      instanceOverBroadcastsExtended_synchronised_cases hIn (by simp) hev
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_notOwn (Ne.symm hi) (hproc i))
      have hw : w' = { w with network := w.network.recordSent j m } := PMF.pure_injective
        (networkStep_send hnet)
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      subst hw; subst ha
      cases m with
      | echo A =>
        obtain ⟨rfl, hinp, hcard, hsend, hx⟩ := programStep_send_echo_own (hproc j)
        rw [stateOverBroadcasts_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact AlgorithmOverBroadcastSpecification.echo _ j hinp hcard hsend
      | vote U =>
        obtain ⟨hinp, hech, happ, hQ, hsend, hx⟩ := programStep_send_vote_own (hproc j)
        rw [stateOverBroadcasts_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact AlgorithmOverBroadcastSpecification.vote _ j U hinp hech happ hQ hsend
      | bind U =>
        obtain ⟨hinp, hvot, happ, hQ, hsend, hx⟩ := programStep_send_bind_own (hproc j)
        rw [stateOverBroadcasts_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact AlgorithmOverBroadcastSpecification.bind _ j U hinp hvot happ hQ hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hnet
      have hw' : w' = w := PMF.pure_injective hw
      have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
      subst hw'; subst ha
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_notOwn (Ne.symm hi') (hproc i'))
      rw [stateOverBroadcasts_deliver (PMF.pure_injective (programStep_deliver_own (hproc i))) hfor]
      exact AlgorithmOverBroadcastSpecification.deliver _ i j m hmem
    | inputBroadcastRet k j v =>
      have hw : w' = w := PMF.pure_injective (networkStep_inputBroadcastRet hnet)
      subst hw
      obtain ⟨hval, hret, hak⟩ :=
        specStep_ret (System.step_of_mapIdle_step (l₀ := BRB.Label.ret j v) (by simp) (hin k))
      have haf : ∀ k', k' ≠ k → a' k' = a k' :=
        fun k' hk' => System.mapIdle_eq_of_step_none (by simp [hk']) (hin k')
      have ha : a' = Function.update a k { a k with ret := Function.update (a k).ret j true } :=
        Function.eq_update_iff.mpr ⟨PMF.pure_injective hak, haf⟩
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_inputBroadcastRet_notOwn (Ne.symm hi) (hproc
          i))
      have hxj := PMF.pure_injective (programStep_inputBroadcastRet_own (hproc j))
      subst ha
      rw [Function.eq_update_iff.mpr ⟨hxj, hfor⟩]
      exact AlgorithmOverBroadcastSpecification.inputBroadcastRet _ k j v hval hret
    | inputBroadcastCall j y =>
      have hw : w' = w := PMF.pure_injective (networkStep_inputBroadcastCall hnet)
      subst hw
      obtain ⟨hinp, hxj⟩ := programStep_inputBroadcastCall_own (hproc j)
      have hxall : ∀ i, x i = u i := fun i => by
        by_cases hi : i = j
        · subst hi; exact PMF.pure_injective hxj
        · exact PMF.pure_injective
            (programStep_inputBroadcastCall_notOwn (Ne.symm hi) (hproc i))
      have haf : ∀ k, k ≠ j → a' k = a k :=
        fun k hk => System.mapIdle_eq_of_step_none (by simp [hk]) (hin k)
      rcases specStep_call (System.step_of_mapIdle_step (l₀ := BRB.Label.call y) (by simp)
          (hin j)) with ⟨hbin, haq⟩ | haq
      · have ha : a' = Function.update a j { a j with input := some y } :=
          Function.eq_update_iff.mpr ⟨PMF.pure_injective haq, haf⟩
        subst ha
        rw [stateOverBroadcasts_idle hxall, stateOverBroadcasts_setInputBroadcasts]
        exact AlgorithmOverBroadcastSpecification.inputBroadcastCall _ j y hinp hbin
      · have ha : a' = a := funext fun k => by
          by_cases hk : k = j
          · subst hk; exact PMF.pure_injective haq
          · exact haf k hk
        subst ha
        rw [stateOverBroadcasts_idle hxall]
        exact AlgorithmOverBroadcastSpecification.inputBroadcastCallLoop _ j y hinp
  · by_cases hlτ : l = Label.tau
    · subst hlτ
      rcases instanceOverBroadcastsExtended_tau_cases hIn hlab with
        ⟨v, rfl, hn⟩ | ⟨k, c, rfl, hs⟩
      · obtain ⟨jj, m, hF, hv⟩ := networkStep_tau hn
        have hv' : v = { w with network := w.network.recordSent jj m } := PMF.pure_injective hv
        subst hv'
        rw [stateOverBroadcasts_recordSent]
        exact AlgorithmOverBroadcastSpecification.byzantine _ jj m hF
      · obtain ⟨v, hval, hm, hc⟩ := specStep_tau hs
        have hc' : c = { a k with val := some v } := PMF.pure_injective hc
        subst hc'
        rw [stateOverBroadcasts_setInputBroadcasts]
        exact AlgorithmOverBroadcastSpecification.commitInputEntry _ k v hval hm
    · obtain ⟨x, w', a', rfl, hproc, hnet, hin⟩ :=
        instanceOverBroadcastsExtended_synchronised_cases hIn
          (fun h => hlτ (Sum.inl_injective h)) hlab
      cases l with
      | tau => exact absurd rfl hlτ
      | call id y =>
        have hw : w' = w := PMF.pure_injective (networkStep_call hnet)
        have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
        subst hw; subst ha
        have hfor : ∀ i, i ≠ id → x i = u i :=
          fun i hi => PMF.pure_injective (programStep_call_notOwn (Ne.symm hi) (hproc i))
        rcases programStep_call_own (hproc id) with ⟨hinp, hxj⟩ | ⟨hinp, hxj⟩
        · rw [stateOverBroadcasts_setProcessVariables (PMF.pure_injective hxj) hfor]
          exact AlgorithmOverBroadcastSpecification.call _ id y hinp
        · have hxall : ∀ i, x i = u i := fun i => by
            by_cases hi : i = id
            · subst hi; exact PMF.pure_injective hxj
            · exact hfor i hi
          rw [stateOverBroadcasts_idle hxall]
          exact AlgorithmOverBroadcastSpecification.callLoop _ id y hinp
      | ret id g =>
        have hw : w' = { w with core := some (w.core.getD (coreOfNetwork P w.network)) } :=
          PMF.pure_injective (networkStep_ret hnet)
        have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
        subst hw; subst ha
        obtain ⟨hinp, hbnd, hsub, hQ, hr, hxj⟩ := programStep_ret_own (hproc id)
        have hfor : ∀ i, i ≠ id → x i = u i :=
          fun i hi => PMF.pure_injective (programStep_ret_notOwn (Ne.symm hi) (hproc i))
        rw [stateOverBroadcasts_ret (PMF.pure_injective hxj) hfor]
        exact AlgorithmOverBroadcastSpecification.ret _ id g hinp hbnd hsub hQ hr
      | core C =>
        obtain ⟨hC, hw⟩ := networkStep_core hnet
        have hw' : w' = w := PMF.pure_injective hw
        have ha : a' = a := funext fun k => System.mapIdle_eq_of_step_none rfl (hin k)
        subst hw'; subst ha
        have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_core (hproc i))
        rw [stateOverBroadcasts_idle hxall]
        exact AlgorithmOverBroadcastSpecification.announceCore _ C hC
      | fail id =>
        have hw : w' = { w with network := w.network.corrupt P id } :=
          PMF.pure_injective (networkStep_fail hnet)
        have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hproc i))
        have ha : ∀ k, a' k = (a k).corrupt P id := fun k =>
          PMF.pure_injective (specStep_fail
            (System.step_of_mapIdle_step (l₀ := BRB.Label.fail id) rfl (hin k)))
        subst hw
        rw [funext ha, stateOverBroadcasts_corrupt hxall]
        exact AlgorithmOverBroadcastSpecification.fail _ id

/-- **The embedding.** -/
theorem algorithm_instanceOverBroadcastSpecification_step (P : Parameters) :
    ∀ (s : StateOverBroadcastSpecification P.n X) (l : Label P.n X)
      (μ : PMF (StateOverBroadcastSpecification P.n X)),
      AlgorithmOverBroadcastSpecification P s l μ →
      (instanceOverBroadcastSpecification P X).step s l μ := by
  rintro ⟨⟨u, w⟩, a⟩ l μ htransition
  cases htransition with
  | call id x h =>
    exact instanceOverBroadcasts_label_step (a' := a) (by simp)
      (dirac_steps_update (ProgramStep.call (u id) x h)
        (fun i hi => ProgramStep.callIdle (u i) id x (Ne.symm hi)))
      (NetworkStep.call w id x)
      (fun k => System.mapIdle_unchanged rfl)
  | callLoop id x hin =>
    refine instanceOverBroadcasts_label_step (x := u) (w' := w) (a' := a) (by simp) (fun i => ?_)
      (NetworkStep.call w id x) (fun k => System.mapIdle_unchanged rfl)
    by_cases hi : i = id
    · subst hi; exact ProgramStep.callLoop (u i) x hin
    · exact ProgramStep.callIdle (u i) id x (Ne.symm hi)
  | commitInputEntry k v hv hm =>
    exact instanceOverBroadcasts_tau_input (BRB.Step.commit (a k) v hv hm)
  | deliver i j m h =>
    exact instanceOverBroadcasts_event_step (a' := a) (GatherEvent.deliver i j m)
      (dirac_steps_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h) (fun k => System.mapIdle_unchanged rfl)
  | echo j hin hcard hsend =>
    exact instanceOverBroadcasts_event_step (a' := a)
      (GatherEvent.send j (.echo (u j).processVariables.accepted))
      (dirac_steps_update (ProgramStep.sendEcho (u j) hin hcard hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo (u j).processVariables.accepted) (Ne.symm
          hi)))
      (NetworkStep.send w j (.echo (u j).processVariables.accepted)) (fun k =>
        System.mapIdle_unchanged rfl)
  | vote j U hin hech happ hQ hsend =>
    exact instanceOverBroadcasts_event_step (a' := a) (GatherEvent.send j (.vote U))
      (dirac_steps_update (ProgramStep.sendVote (u j) U hin hech happ hQ hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote U) (Ne.symm hi)))
      (NetworkStep.send w j (.vote U)) (fun k => System.mapIdle_unchanged rfl)
  | bind j U hin hvot happ hQ hsend =>
    exact instanceOverBroadcasts_event_step (a' := a) (GatherEvent.send j (.bind U))
      (dirac_steps_update (ProgramStep.sendBind (u j) U hin hvot happ hQ hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.bind U) (Ne.symm hi)))
      (NetworkStep.send w j (.bind U)) (fun k => System.mapIdle_unchanged rfl)
  | inputBroadcastCall j x hin hb =>
    exact instanceOverBroadcasts_event_step (x := u) (w' := w)
      (GatherEvent.inputBroadcastCall j x)
      (fun i => by
        by_cases hi : i = j
        · subst hi; exact ProgramStep.inputBroadcastCall (u i) x hin
        · exact ProgramStep.inputBroadcastCallIdle (u i) j x (Ne.symm hi))
      (NetworkStep.inputBroadcastCallIdle w j x)
      (System.mapIdle_step_update (by simp) (fun k hk => by simp [hk])
        (BRB.Step.call (a j) x hb))
  | inputBroadcastCallLoop j x hin =>
    refine instanceOverBroadcasts_event_step (x := u) (w' := w) (a' := a)
      (GatherEvent.inputBroadcastCall j x)
      (fun i => by
        by_cases hi : i = j
        · subst hi; exact ProgramStep.inputBroadcastCall (u i) x hin
        · exact ProgramStep.inputBroadcastCallIdle (u i) j x (Ne.symm hi))
      (NetworkStep.inputBroadcastCallIdle w j x) (fun k => ?_)
    by_cases hk : k = j
    · subst hk
      exact System.mapIdle_step_of_step (by simp) (BRB.Step.callLoop (a k) x)
    · exact System.mapIdle_unchanged (by simp [hk])
  | byzantine j m h =>
    exact instanceOverBroadcasts_tau_network (NetworkStep.byzantine w j m h)
  | inputBroadcastRet k j v hv hr =>
    exact instanceOverBroadcasts_event_step (w' := w) (GatherEvent.inputBroadcastRet k j v)
      (dirac_steps_update (ProgramStep.inputBroadcastRetReceive (u j) k v)
        (fun i hi => ProgramStep.inputBroadcastRetIdle (u i) k j v (Ne.symm hi)))
      (NetworkStep.inputBroadcastRetIdle w k j v)
      (System.mapIdle_step_update (by simp) (fun k' hk' => by simp [hk'])
        (BRB.Step.ret (a k) j v hv hr))
  | ret id g hin hbind hsub hQ hr =>
    exact instanceOverBroadcasts_label_step (a' := a) (by simp)
      (dirac_steps_update (ProgramStep.ret (u id) g hin hbind hsub hQ hr)
        (fun i hi => ProgramStep.retIdle (u i) id g (Ne.symm hi)))
      (NetworkStep.ret w id g) (fun k => System.mapIdle_unchanged rfl)
  | announceCore C h =>
    exact instanceOverBroadcasts_label_step (x := u) (w' := w) (a' := a) (by simp)
      (fun i => ProgramStep.coreIdle (u i) C) (NetworkStep.announceCore w C h)
      (fun k => System.mapIdle_unchanged rfl)
  | fail id =>
    exact instanceOverBroadcasts_label_step (x := u) (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)
      (System.mapIdle_step_all (l₀ := fun _ => BRB.Label.fail id) (fun k => rfl)
        (fun k => BRB.Step.fail (a k) id))

/-- **The characterisation by the algorithm.** At every label `l`, the `l`-transitions of the
instance are exactly the `l`-transitions of `AlgorithmOverBroadcastSpecification`, on the same
state and with the same distribution. The call and the call loop are the two transitions of
`call id x`. -/
theorem instanceOverBroadcastSpecification_step_iff_algorithm (P : Parameters)
    (s : StateOverBroadcastSpecification P.n X) (l : Label P.n X)
    (μ : PMF (StateOverBroadcastSpecification P.n X)) :
    (instanceOverBroadcastSpecification P X).step s l μ ↔
      AlgorithmOverBroadcastSpecification P s l μ :=
  ⟨instanceOverBroadcastSpecification_step_algorithm P s l μ,
    algorithm_instanceOverBroadcastSpecification_step P s l μ⟩

/-- info: 'PLTS.ABA.Gather.instanceOverBroadcastSpecification_step_iff_algorithm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms instanceOverBroadcastSpecification_step_iff_algorithm

end Gather
end ABA
end PLTS
