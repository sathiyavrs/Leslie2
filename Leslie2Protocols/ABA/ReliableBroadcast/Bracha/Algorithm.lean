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

* the leader, on being called with `m`, multicasts `⟨INIT, m⟩`;
* `⟨ECHO, m⟩` is multicast on receiving `⟨INIT, m⟩` from the leader, on a quorum of received
  `ECHO m` messages, or on `f + 1` received `VOTE m` messages, once;
* `⟨VOTE, m⟩` is multicast on a quorum of received `ECHO m` messages, or amplified from `f + 1`
  received `VOTE m` messages, once;
* `m` is returned on `2f + 1` received `VOTE m` messages.

The `ECHO` quorum is `ABA.Parameters.receivedEchoQuorum`, more than `(n + f) / 2` senders. There is
no participation guard: only the leader is called, and every other process runs its handlers
unconditionally, Bracha's protocol having no per-process input. The write-once `sentEcho` and
`sentVote` fields carry the "having not sent" guards of the source's `upon` clauses, and
`voteAmplification` and `voteQuorum` write the same field, so a process votes at most once
whichever of the two fires first.

`brachaInstance_step_algorithm` is the projection and `algorithm_brachaInstance_step` the embedding.
Together they give `brachaInstance_step_iff_algorithm`: at a specification label `l₀`, the
transitions of the composition over the labels `BRB.specificationLabelMap` sends to `l₀` are exactly
the `l₀`-transitions of `BrachaAlgorithm`, on the same composed state and with the same
distribution.

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
loop are the two transitions of `call m`, which the instance takes at two labels. Every transition
is Dirac. -/
inductive BrachaAlgorithm (P : Parameters) (ldr : Fin P.n) :
    BrachaState P.n M → Label P.n M → PMF (BrachaState P.n M) → Prop
  /-- The environment call arrives at the leader: record the payload and
  multicast `⟨INIT, m⟩`. -/
  | call (s : BrachaState P.n M) (m : M)
      (h : (s.processVariables ldr).input = none) :
      BrachaAlgorithm P ldr s (.call m)
        (PMF.pure ((s.setProcessVariables ldr
          { s.processVariables ldr with input := some m }).multicast
          ldr (.init m)))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : BrachaState P.n M) (m : M) :
      BrachaAlgorithm P ldr s (.call m) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : BrachaState P.n M) (i j : Fin P.n) (m : Message M)
      (h : m ∈ s.sent j) :
      BrachaAlgorithm P ldr s .tau (PMF.pure (s.receiveMessage i j m))
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

Every transition of the instance is one transition of `BrachaAlgorithm` at the same state, and the
correspondence is strong: one step matches one step, at the specification label the interface
label projects to, with no stuttering anywhere.

| instance | algorithm |
| --- | --- |
| `call` (leader writes, network records) | `BrachaAlgorithm.call` |
| `callLoop` | `BrachaAlgorithm.callLoop` |
| hidden `send` synchronisation, by level | `BrachaAlgorithm.echo` / `voteQuorum` /
`voteAmplification` |
| hidden `deliver` synchronisation | `BrachaAlgorithm.deliver` |
| network-local injection | `BrachaAlgorithm.byzantine` |
| `ret` | `BrachaAlgorithm.ret` |
| `fail` | `BrachaAlgorithm.fail` |

The two hidden synchronisations and the network's injection are silent in both systems, and
`specificationLabelMap` takes `τ` to `τ`. -/

/-- **The projection.** -/
theorem brachaInstance_step_algorithm (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l : InstanceLabel P.n M) (μ : PMF (BrachaState P.n M)),
      (brachaInstance P ldr M).step s l μ →
      ∃ l₀, specificationLabelMap P.n M l = some l₀ ∧ BrachaAlgorithm P ldr s l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (brachaInstance_step_iff P ldr (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden synchronisation: an internal transition
    obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_synchronised_cases (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_notOwn (Ne.symm hi) (hall i))
      have hw : w' = w.recordSent j m := PMF.pure_injective (networkStep_send hn)
      subst hw
      cases m with
      | init m => exact (programStep_send_init_own (hall j)).elim
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
  · by_cases hlτ : l = Sum.inl Label.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := brachaInstanceExtended_tau_cases hlab
      obtain ⟨j, m, hF, hw⟩ := networkStep_tau hn
      have hw' : w' = w.recordSent j m := PMF.pure_injective hw
      subst hw'
      refine ⟨Label.tau, rfl, ?_⟩
      rw [brachaInstance_recordSent]
      exact BrachaAlgorithm.byzantine _ j m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ :=
        brachaInstanceExtended_synchronised_cases (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call m =>
          have hw : w' = w.recordSent ldr (.init m) := PMF.pure_injective (networkStep_call hn)
          subst hw
          obtain ⟨hin, hx⟩ := programStep_call_leader (hall ldr)
          have hfor : ∀ i, i ≠ ldr → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_call_notOwn hi (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_setProcessVariables_recordSent (PMF.pure_injective hx) hfor]
          exact BrachaAlgorithm.call _ m hin
        | ret id m =>
          have hw : w' = w := PMF.pure_injective (networkStep_ret hn)
          subst hw
          obtain ⟨hcnt, hr, hx⟩ := programStep_ret_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_ret_notOwn (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_setProcessVariables (PMF.pure_injective hx) hfor]
          exact BrachaAlgorithm.ret _ id m hcnt hr
        | fail id =>
          have hw : w' = w.corrupt P id := PMF.pure_injective (networkStep_fail hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_idle hidle, brachaInstance_corrupt]
          exact BrachaAlgorithm.fail _ id
      | inr e =>
        cases e with
        | callLoop m =>
          have hw : w' = w := PMF.pure_injective (networkStep_callLoop hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_callLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_idle hidle]
          exact BrachaAlgorithm.callLoop _ m

/-- **The embedding.** -/
theorem algorithm_brachaInstance_step (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l₀ : Label P.n M) (μ : PMF (BrachaState P.n M)),
      BrachaAlgorithm P ldr s l₀ μ →
      ∃ l, specificationLabelMap P.n M l = some l₀ ∧ (brachaInstance P ldr M).step s l μ := by
  rintro ⟨u, w⟩ l₀ μ htransition
  cases htransition with
  | call m h =>
    exact ⟨Sum.inl (.call m), rfl, brachaInstance_label_step P ldr (by simp)
      (dirac_steps_update (ProgramStep.call (u ldr) m rfl h)
        (fun i hi => ProgramStep.callIdle (u i) m hi))
      (NetworkStep.call w m)⟩
  | callLoop m =>
    exact ⟨Sum.inr (.callLoop m), rfl, brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.callLoop (u i) m) (NetworkStep.callLoop w m)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.deliver i j m)
      (dirac_steps_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h)⟩
  | echo j m hrecv hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.echo m))
      (dirac_steps_update (ProgramStep.sendEcho (u j) m hrecv hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo m) (Ne.symm hi)))
      (NetworkStep.send w j (.echo m))⟩
  | voteQuorum j m hcnt hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (dirac_steps_update (ProgramStep.sendVoteQuorum (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))⟩
  | voteAmplification j m hcnt hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (dirac_steps_update (ProgramStep.sendVoteAmplification (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))⟩
  | byzantine j m h =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_tau_network P ldr (NetworkStep.byzantine w j m h)⟩
  | ret id m hcnt hr =>
    exact ⟨Sum.inl (.ret id m), rfl, brachaInstance_label_step P ldr (by simp)
      (dirac_steps_update (ProgramStep.ret (u id) m hcnt hr)
        (fun i hi => ProgramStep.retIdle (u i) id m (Ne.symm hi)))
      (NetworkStep.retIdle w id m)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)⟩

/-- **The characterisation.** At a specification label `l₀`, the transitions of the instance
over the labels `specificationLabelMap` sends to `l₀` are exactly the `l₀`-transitions of
`BrachaAlgorithm`, on the same state and with the same distribution. The call and the call loop
are the two transitions of `call m`, taken at the two labels `specificationLabelMap` sends to it;
every other specification label has a single interface label over it. -/
theorem brachaInstance_step_iff_algorithm (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (l₀ : Label P.n M) (μ : PMF (BrachaState P.n M)) :
    (∃ l, specificationLabelMap P.n M l = some l₀ ∧ (brachaInstance P ldr M).step s l μ) ↔
    BrachaAlgorithm P ldr s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, htransition⟩ := brachaInstance_step_algorithm P ldr s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n M)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact htransition
  · exact algorithm_brachaInstance_step P ldr s l₀ μ

/-- info: 'PLTS.ABA.BRB.brachaInstance_step_iff_algorithm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaInstance_step_iff_algorithm

end BRB
end ABA
end PLTS
