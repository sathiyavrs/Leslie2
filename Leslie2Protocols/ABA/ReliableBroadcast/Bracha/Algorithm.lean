/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.CompositionStepCases

/-!
# Bracha's algorithm over the composed state

`BRB.BrachaAlgorithm` states the transitions of the reliable-broadcast instance
`BRB.brachaInstance` (`ABA/ReliableBroadcast/Bracha/Composition.lean`) over the composed state
`BrachaState n M`, one constructor per case of `BRB.brachaInstance_step_iff_algorithm`. It is a
relation on that state; the system is the composition.

The message pattern, per process:

* the leader, called with `m` while it holds no input, records `m` in `input`, and multicasts
  `⟨INIT, m⟩` in a transition of its own, once;
* `⟨ECHO, m⟩` is multicast on receiving `⟨INIT, m⟩` from the leader, on a quorum of received
  `ECHO m` messages, or on `f + 1` received `VOTE m` messages, once;
* `⟨VOTE, m⟩` is multicast on a quorum of received `ECHO m` messages, or amplified from `f + 1`
  received `VOTE m` messages, once;
* `m` is returned on `2f + 1` received `VOTE m` messages.

The `ECHO` quorum is `ABA.Parameters.receivedEchoQuorum`, more than `(n + f) / 2` senders. There is
no participation guard: only the leader is called, and every other process runs its handlers
unconditionally, Bracha's protocol having no per-process input. The write-once `sentInit` field
makes the leader's `INIT` a single multicast. The write-once `sentEcho` and
`sentVote` fields carry the "having not sent" guards of the source's `upon` clauses, and
`voteAmplification` and `voteQuorum` write the same field, so a process votes at most once
whichever of the two fires first.

`brachaInstance_step_algorithm` is the projection and `algorithm_brachaInstance_step` the embedding.
Together they give `brachaInstance_step_iff_algorithm`: at every label `l`, the `l`-transitions of
the composition are exactly the `l`-transitions of `BrachaAlgorithm`, on the same composed state
and with the same distribution.

## Model and deviations

* **D34 (Bracha after AFW25).** Bracha's protocol (Bracha 1987) is transcribed in the form of
  Algorithm 1 of AFW25: the echo step fires on a received `INIT`, on a quorum of received `ECHO m`
  messages or on `f + 1` received `VOTE m` messages, and the echo quorum is more than `(n + f) / 2`
  senders.
* **D1 (determinised corruption)** and **D5 (set-based network)** are the conventions of the
  composed state the algorithm runs on.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M]

/-- The transitions of the reliable-broadcast instance with leader `ldr`
(`BRB.brachaInstance`, `ABA/ReliableBroadcast/Bracha/Composition.lean`), stated over the composed
state: one constructor per case of `BRB.brachaInstance_step_iff_algorithm`. The call and the call
loop are the two transitions of `call m`, the call at a leader holding no input and the loop at a
leader holding one. Every transition is Dirac. -/
inductive BrachaAlgorithm (P : Parameters) (ldr : Fin P.n) :
    BrachaState P.n M → Label P.n M → PMF (BrachaState P.n M) → Prop
  /-- The environment call arrives at a leader holding no input: record the payload. -/
  | call (s : BrachaState P.n M) (m : M)
      (h : (s.processVariables ldr).input = none) :
      BrachaAlgorithm P ldr s (.call m)
        (PMF.pure (s.setProcessVariables ldr { s.processVariables ldr with input := some m }))
  /-- Input-enabledness loop for `call`, at a leader holding an input: nothing moves. -/
  | callLoop (s : BrachaState P.n M) (m : M)
      (h : (s.processVariables ldr).input ≠ none) :
      BrachaAlgorithm P ldr s (.call m) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : BrachaState P.n M) (i j : Fin P.n) (m : Message M)
      (h : m ∈ s.sent j) :
      BrachaAlgorithm P ldr s .tau (PMF.pure (s.receiveMessage i j m))
  /-- `INIT`: the leader holds the payload `m` it was called with and has sent no `INIT` yet.
  The source's `if p_id is leader: send ⟨init, m⟩ to all`. -/
  | init (s : BrachaState P.n M) (m : M)
      (hin : (s.processVariables ldr).input = some m)
      (hsend : (s.processVariables ldr).sentInit = none) :
      BrachaAlgorithm P ldr s .tau
        (PMF.pure ((s.setProcessVariables ldr
          { s.processVariables ldr with sentInit := some m }).multicast
          ldr (.init m)))
  /-- `ECHO`: `⟨INIT, m⟩` received from the leader, a quorum of received `ECHO m`
  messages, or `f + 1` received `VOTE m` messages; no `ECHO` sent yet. -/
  | echo (s : BrachaState P.n M) (j : Fin P.n) (m : M)
      (hrecv : Message.init m ∈ s.received j ldr ∨ P.receivedEchoQuorum ≤ s.receivedCount j (.echo
        m)
        ∨
        P.f + 1 ≤ s.receivedCount j (.vote m))
      (hsend : (s.processVariables j).sentEcho = none) :
      BrachaAlgorithm P ldr s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentEcho := some m }).multicast
          j (.echo m)))
  /-- `VOTE` (quorum case): a quorum of received `ECHO m` messages, no `VOTE` sent yet. -/
  | voteQuorum (s : BrachaState P.n M) (j : Fin P.n) (m : M)
      (hcnt : P.receivedEchoQuorum ≤ s.receivedCount j (.echo m))
      (hsend : (s.processVariables j).sentVote = none) :
      BrachaAlgorithm P ldr s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentVote := some m }).multicast
          j (.vote m)))
  /-- `VOTE` (amplification case): `f + 1` received `VOTE m` messages, no `VOTE` sent
  yet. -/
  | voteAmplification (s : BrachaState P.n M) (j : Fin P.n) (m : M)
      (hcnt : P.f + 1 ≤ s.receivedCount j (.vote m))
      (hsend : (s.processVariables j).sentVote = none) :
      BrachaAlgorithm P ldr s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentVote := some m }).multicast
          j (.vote m)))
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byzantine (s : BrachaState P.n M) (j : Fin P.n) (m : Message M) (h : j ∈ s.F) :
      BrachaAlgorithm P ldr s .tau (PMF.pure (s.multicast j m))
  /-- Return: `2f + 1` received `VOTE m` messages. -/
  | ret (s : BrachaState P.n M) (id : Fin P.n) (m : M)
      (hcnt : 2 * P.f + 1 ≤ s.receivedCount id (.vote m))
      (hr : (s.processVariables id).returned = false) :
      BrachaAlgorithm P ldr s (.ret id m)
        (PMF.pure (s.setProcessVariables id { s.processVariables id with returned := true }))
  /-- Corruption (deviation D1). -/
  | fail (s : BrachaState P.n M) (id : Fin P.n) :
      BrachaAlgorithm P ldr s (.fail id) (PMF.pure (s.corrupt P id))

/-! ### The transitions of the instance against the algorithm

Every transition of the instance is one transition of `BrachaAlgorithm` at the same state and the
same label, and the correspondence is strong: one step matches one step, with no stuttering
anywhere.

| instance | algorithm |
| --- | --- |
| `call` at a leader holding no input | `BrachaAlgorithm.call` |
| `call` at a leader holding an input | `BrachaAlgorithm.callLoop` |
| hidden `send` synchronisation, by level | `BrachaAlgorithm.init` / `echo` / `voteQuorum` /
`voteAmplification` |
| hidden `deliver` synchronisation | `BrachaAlgorithm.deliver` |
| network-local injection | `BrachaAlgorithm.byzantine` |
| `ret` | `BrachaAlgorithm.ret` |
| `fail` | `BrachaAlgorithm.fail` |

The two hidden synchronisations and the network's injection are silent in both systems. -/

/-- **The projection.** -/
theorem brachaInstance_step_algorithm (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l : Label P.n M) (μ : PMF (BrachaState P.n M)),
      (brachaInstance P ldr M).step s l μ → BrachaAlgorithm P ldr s l μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (brachaInstance_step_iff P ldr (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden synchronisation: an internal transition
    obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_synchronised_cases (by simp) hev
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_notOwn (Ne.symm hi) (hall i))
      have hw : w' = w.recordSent j m := PMF.pure_injective (networkStep_send hn)
      subst hw
      cases m with
      | init m =>
        obtain ⟨rfl, hin, hsend, hx⟩ := programStep_send_init_own (hall j)
        rw [brachaInstance_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact BrachaAlgorithm.init _ m hin hsend
      | echo m =>
        obtain ⟨hrecv, hsend, hx⟩ := programStep_send_echo_own (hall j)
        rw [brachaInstance_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        exact BrachaAlgorithm.echo _ j m hrecv hsend
      | vote m =>
        obtain ⟨hcnt, hsend, hx⟩ := programStep_send_vote_own (hall j)
        rw [brachaInstance_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
        rcases hcnt with hq | ha
        · exact BrachaAlgorithm.voteQuorum _ j m hq hsend
        · exact BrachaAlgorithm.voteAmplification _ j m ha hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_notOwn (Ne.symm hi') (hall i'))
      rw [brachaInstance_deliver (PMF.pure_injective (programStep_deliver_own (hall i))) hfor]
      exact BrachaAlgorithm.deliver _ i j m hmem
  · cases l with
    | tau =>
      -- the network's own injection
      obtain ⟨w', rfl, hn⟩ := brachaInstanceExtended_tau_cases hlab
      obtain ⟨j, m, hF, hw⟩ := networkStep_tau hn
      have hw' : w' = w.recordSent j m := PMF.pure_injective hw
      subst hw'
      rw [brachaInstance_recordSent]
      exact BrachaAlgorithm.byzantine _ j m hF
    | call m =>
      obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_synchronised_cases (by simp) hlab
      have hw : w' = w := PMF.pure_injective (networkStep_call hn)
      subst hw
      have hfor : ∀ i, i ≠ ldr → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_call_notOwn hi (hall i))
      rcases programStep_call_leader (hall ldr) with ⟨hin, hx⟩ | ⟨hin, hx⟩
      · rw [brachaInstance_setProcessVariables (PMF.pure_injective hx) hfor]
        exact BrachaAlgorithm.call _ m hin
      · have hidle : ∀ i, x i = u i := by
          intro i
          rcases eq_or_ne i ldr with rfl | hi
          · exact PMF.pure_injective hx
          · exact hfor i hi
        rw [brachaInstance_idle hidle]
        exact BrachaAlgorithm.callLoop _ m hin
    | ret id m =>
      obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_synchronised_cases (by simp) hlab
      have hw : w' = w := PMF.pure_injective (networkStep_ret hn)
      subst hw
      obtain ⟨hcnt, hr, hx⟩ := programStep_ret_own (hall id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_ret_notOwn (Ne.symm hi) (hall i))
      rw [brachaInstance_setProcessVariables (PMF.pure_injective hx) hfor]
      exact BrachaAlgorithm.ret _ id m hcnt hr
    | fail id =>
      obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_synchronised_cases (by simp) hlab
      have hw : w' = w.corrupt P id := PMF.pure_injective (networkStep_fail hn)
      subst hw
      have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hall i))
      rw [brachaInstance_idle hidle, brachaInstance_corrupt]
      exact BrachaAlgorithm.fail _ id

/-- **The embedding.** -/
theorem algorithm_brachaInstance_step (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l : Label P.n M) (μ : PMF (BrachaState P.n M)),
      BrachaAlgorithm P ldr s l μ → (brachaInstance P ldr M).step s l μ := by
  rintro ⟨u, w⟩ l μ htransition
  cases htransition with
  | call m h =>
    exact brachaInstance_label_step P ldr (by simp)
      (dirac_steps_update (ProgramStep.call (u ldr) m rfl h)
        (fun i hi => ProgramStep.callIdle (u i) m hi))
      (NetworkStep.call w m)
  | callLoop m h =>
    refine brachaInstance_label_step P ldr (x := u) (by simp) (fun i => ?_) (NetworkStep.call w m)
    rcases eq_or_ne i ldr with rfl | hi
    · exact ProgramStep.callLoop (u i) m rfl h
    · exact ProgramStep.callIdle (u i) m hi
  | init m hin hsend =>
    exact brachaInstance_event_step P ldr (BroadcastEvent.send ldr (.init m))
      (dirac_steps_update (ProgramStep.sendInit (u ldr) m rfl hin hsend)
        (fun i hi => ProgramStep.sendIdle (u i) ldr (.init m) (Ne.symm hi)))
      (NetworkStep.send w ldr (.init m))
  | deliver i j m h =>
    exact brachaInstance_event_step P ldr (BroadcastEvent.deliver i j m)
      (dirac_steps_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h)
  | echo j m hrecv hsend =>
    exact brachaInstance_event_step P ldr (BroadcastEvent.send j (.echo m))
      (dirac_steps_update (ProgramStep.sendEcho (u j) m hrecv hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo m) (Ne.symm hi)))
      (NetworkStep.send w j (.echo m))
  | voteQuorum j m hcnt hsend =>
    exact brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (dirac_steps_update (ProgramStep.sendVoteQuorum (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))
  | voteAmplification j m hcnt hsend =>
    exact brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (dirac_steps_update (ProgramStep.sendVoteAmplification (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))
  | byzantine j m h =>
    exact brachaInstance_tau_network P ldr (NetworkStep.byzantine w j m h)
  | ret id m hcnt hr =>
    exact brachaInstance_label_step P ldr (by simp)
      (dirac_steps_update (ProgramStep.ret (u id) m hcnt hr)
        (fun i hi => ProgramStep.retIdle (u i) id m (Ne.symm hi)))
      (NetworkStep.retIdle w id m)
  | fail id =>
    exact brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)

/-- **The characterisation.** At every label `l`, the `l`-transitions of the instance are exactly
the `l`-transitions of `BrachaAlgorithm`, on the same state and with the same distribution. The
call and the call loop are the two transitions of `call m`. -/
theorem brachaInstance_step_iff_algorithm (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (l : Label P.n M) (μ : PMF (BrachaState P.n M)) :
    (brachaInstance P ldr M).step s l μ ↔ BrachaAlgorithm P ldr s l μ :=
  ⟨brachaInstance_step_algorithm P ldr s l μ, algorithm_brachaInstance_step P ldr s l μ⟩

/-- info: 'PLTS.ABA.BRB.brachaInstance_step_iff_algorithm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaInstance_step_iff_algorithm

end BRB
end ABA
end PLTS
