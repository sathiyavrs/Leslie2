/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.AlgorithmOverBroadcastSpecification

/-!
# The inductive invariant of the composed gather instance

`Gather.Invariant` is what the gather instance over the broadcast specifications
(`Gather.instanceOverBroadcastSpecification`, `ABA/Gather/Composition.lean`) maintains, stated over
the composition's state through the projections `gatherProgramsAndNetwork`, `inputBroadcasts` and
`core`. `Invariant.initial` holds it at the initial state, and `Invariant.step` carries it along
every transition of `Gather.AlgorithmOverBroadcastSpecification`.

The invariant has two parts. `Conformance` collects what the composition records: the corruption
budget, the corrupted set of each of the `n` input instances, delivery soundness, the returned
values a program holds, where a committed entry comes from, and the message pattern of a process
outside `F`. A `*_confirmed` clause ties a sent `ECHO`, `VOTE` or `BIND` message to its write-once
field. A `*_backed` clause ties that field to what justified it: the `n − f` received `ECHO`
payloads contained in a `VOTE` payload, the `n − f` received `VOTE` payloads contained in a `BIND`
payload, and the caller's own variables for the payload of an input instance. `echo_card` gives a
correct echo payload its `n − f` entries. `echo_approved` is the second part: the payload set in a
process's `ECHO` field consists of committed input entries (`Gather.approved`). It carries no
correctness premise, because only `AlgorithmOverBroadcastSpecification.echo` writes the field and
a corrupted sender's accepted pairs are entries of its returned value too.

Committed entries are written once, so `approved` is monotone along every transition
(`approved_mono`), which is what makes `echo_approved` inductive. The counting argument of
`ABA/Gather/CommonCoreCounting.lean` runs on the invariant at the `ECHO`, `VOTE` and `BIND` levels.

## What the input instances returned

A gather program reads what an input instance returned to it out of its own variables. The clause
`inputBroadcastReturned_val` carries a returned value back to the commitment that wrote it: it is
established at the `inputBroadcastRet` transition, whose guard is the broadcast specification's
`val = some v`, and every later transition preserves it because a committed value is written once.

## The calls

A process calls the instance broadcasting its input on an event of its own, so the payload an
input instance records is the payload the caller's own variables hold
(`inputBroadcastCall_backed`), and a commitment is the payload the input instance was called with
(`inputBroadcastVal_of_instanceInput`).
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The conformance clauses -/

/-- The conformance clauses. The `*_confirmed` clauses tie a correct sender's sent to its write-once
field, the `*_backed` clauses tie the fields to the received messages that justified them, the
return clauses tie a program's returned value to the commitment that wrote it, and the
`*_of_instanceInput` clauses are the broadcast commit guards, recorded per instance. -/
structure Conformance (P : Parameters) (s : StateOverBroadcastSpecification P.n X) : Prop where
  /-- The corruption budget. -/
  F_card : (gatherProgramsAndNetwork s).F.card ≤ P.f
  /-- The input instances' corrupted sets are equal to the gather network state's. -/
  F_inputBroadcast_eq : ∀ k, (inputBroadcasts s k).F = (gatherProgramsAndNetwork s).F
  /-- Delivered messages were multicast. -/
  received_subset_sent : ∀ i k, (gatherProgramsAndNetwork s).received i k ⊆
    (gatherProgramsAndNetwork s).sent k
  /-- A value in what a program's input instance returned is the committed value of the instance
  that returned it. -/
  inputBroadcastReturned_val : ∀ j k v,
    ((gatherProgramsAndNetwork s).processVariables j).inputBroadcastReturned k = some v →
      (inputBroadcasts s k).val = some v
  /-- A committed input entry of a correct process is the payload its input
  instance recorded. -/
  inputBroadcastVal_of_instanceInput : ∀ k v, (inputBroadcasts s k).val = some v →
    k ∈ (gatherProgramsAndNetwork s).F ∨ (inputBroadcasts s k).input = some v
  /-- A correct sender's sent `ECHO` matches its write-once field. -/
  echo_confirmed : ∀ j ∉ (gatherProgramsAndNetwork s).F, ∀ A, Message.echo A ∈
    (gatherProgramsAndNetwork s).sent j →
    ((gatherProgramsAndNetwork s).processVariables j).sentEcho = some A
  /-- A correct echo payload has at least `n − f` entries. -/
  echo_card : ∀ j ∉ (gatherProgramsAndNetwork s).F, ∀ A, ((gatherProgramsAndNetwork
    s).processVariables j).sentEcho = some A →
    P.n - P.f ≤ A.card
  /-- A correct sender's sent `VOTE` matches its write-once field. -/
  vote_confirmed : ∀ j ∉ (gatherProgramsAndNetwork s).F, ∀ W, Message.vote W ∈
    (gatherProgramsAndNetwork s).sent j →
    ((gatherProgramsAndNetwork s).processVariables j).sentVote = some W
  /-- A correct process's `VOTE` payload contains an `ECHO` payload received from each of
  `n − f` senders. -/
  vote_backed : ∀ j ∉ (gatherProgramsAndNetwork s).F, ∀ W, ((gatherProgramsAndNetwork
    s).processVariables j).sentVote = some W →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ A, Message.echo A ∈ (gatherProgramsAndNetwork s).received j q ∧ A ⊆ W
  /-- A correct sender's sent `BIND` matches its write-once field. -/
  bind_confirmed : ∀ j ∉ (gatherProgramsAndNetwork s).F, ∀ U, Message.bind U ∈
    (gatherProgramsAndNetwork s).sent j →
    ((gatherProgramsAndNetwork s).processVariables j).sentBind = some U
  /-- A correct process's `BIND` payload contains a `VOTE` payload received from each of
  `n − f` senders. -/
  bind_backed : ∀ j ∉ (gatherProgramsAndNetwork s).F, ∀ U, ((gatherProgramsAndNetwork
    s).processVariables j).sentBind = some U →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ W, Message.vote W ∈ (gatherProgramsAndNetwork s).received j q ∧ W ⊆ U
  /-- The payload an input instance was called with is the payload its own process's
  variables hold. -/
  inputBroadcastCall_backed : ∀ k ∉ (gatherProgramsAndNetwork s).F, ∀ x,
    (inputBroadcasts s k).input = some x → ((gatherProgramsAndNetwork s).processVariables k).input =
      some x

/-- The conformance clauses hold initially. -/
theorem Conformance.initial : Conformance P ((instanceOverBroadcastSpecification P X).init) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gatherProgramsAndNetwork, inputBroadcasts, ProcessVariables.initial,
      BaseProcessVariables.initial, BRB.SpecState.initial, NetworkState.initial,
        InstanceState.processVariables, InstanceState.sent, InstanceState.received, InstanceState.F]

/-- The conformance clauses are preserved by every step. -/
theorem Conformance.step {s : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hInv : Conformance P s)
    (hstep : AlgorithmOverBroadcastSpecification P s l μ)
    {s' : StateOverBroadcastSpecification P.n X} (hs' : s' ∈ μ.support) : Conformance P s' := by
  cases hstep with
  | call id x h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i k m hm
      rw [InstanceState.setProcessVariables_received] at hm
      rw [InstanceState.setProcessVariables_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcessVariables_processVariables_self] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hj] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j hj A hA
      rw [InstanceState.setProcessVariables_sent] at hA
      have hpre := hInv.echo_confirmed j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [InstanceState.setProcessVariables_sent] at hW
      have hpre := hInv.vote_confirmed j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [InstanceState.setProcessVariables_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [InstanceState.setProcessVariables_sent] at hU
      have hpre := hInv.bind_confirmed j hj U hU
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j hj U hU
      rw [InstanceState.setProcessVariables_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hU
        exact hInv.bind_backed j hj U hU
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hU
        exact hInv.bind_backed j hj U hU
    · intro k hk y hy
      have h0 := hInv.inputBroadcastCall_backed k hk y hy
      by_cases hkid : k = id
      · subst hkid
        rw [h] at h0
        exact absurd h0 (by simp)
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkid]
        exact h0
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | inputBroadcastCall j x hin hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.received_subset_sent, ?_, ?_, hInv.echo_confirmed,
      hInv.echo_card, hInv.vote_confirmed, hInv.vote_backed, hInv.bind_confirmed,
      hInv.bind_backed, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setInputBroadcasts,
      inputBroadcasts_setInputBroadcasts]
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        exact hInv.F_inputBroadcast_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_inputBroadcast_eq k
    · intro j' k v hv
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        exact hInv.inputBroadcastReturned_val j' k v hv
      · rw [Function.update_of_ne hk]
        exact hInv.inputBroadcastReturned_val j' k v hv
    · intro k v hv
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self] at hv ⊢
        rcases hInv.inputBroadcastVal_of_instanceInput k v hv with hF | hin'
        · exact Or.inl hF
        · rw [hb] at hin'
          exact absurd hin' (by simp)
      · rw [Function.update_of_ne hk] at hv ⊢
        exact hInv.inputBroadcastVal_of_instanceInput k v hv
    · intro k hk y hy
      by_cases hkj : k = j
      · subst hkj
        rw [Function.update_self] at hy
        have hxy : some x = some y := hy
        obtain rfl : x = y := by injection hxy
        exact hin
      · rw [Function.update_of_ne hkj] at hy
        exact hInv.inputBroadcastCall_backed k hk y hy
  | inputBroadcastCallSpecificationLoop j x hin =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | commitInputEntry k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.received_subset_sent, ?_, ?_, hInv.echo_confirmed,
      hInv.echo_card, hInv.vote_confirmed, hInv.vote_backed, hInv.bind_confirmed,
      hInv.bind_backed, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setInputBroadcasts,
      inputBroadcasts_setInputBroadcasts]
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_inputBroadcast_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_inputBroadcast_eq k'
    · intro j k' v' hv'
      by_cases hk : k' = k
      · subst hk
        have hold := hInv.inputBroadcastReturned_val j k' v' hv'
        rw [hv] at hold
        exact absurd hold (by simp)
      · rw [Function.update_of_ne hk]
        exact hInv.inputBroadcastReturned_val j k' v' hv'
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hv' ⊢
        have hvv : some v = some v' := hv'
        obtain rfl : v = v' := by
          injection hvv
        rcases hm with hF | hin
        · exact Or.inl (hInv.F_inputBroadcast_eq k' ▸ hF)
        · exact Or.inr hin
      · rw [Function.update_of_ne hk] at hv' ⊢
        exact hInv.inputBroadcastVal_of_instanceInput k' v' hv'
    · intro k' hk' y hy
      by_cases hkk : k' = k
      · subst hkk
        rw [Function.update_self] at hy
        exact hInv.inputBroadcastCall_backed k' hk' y hy
      · rw [Function.update_of_ne hkk] at hy
        exact hInv.inputBroadcastCall_backed k' hk' y hy
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i' k m' hm'
      rw [InstanceState.mem_receiveMessage_received] at hm'
      rw [InstanceState.receiveMessage_sent]
      rcases hm' with ⟨-, rfl, rfl⟩ | hold
      · exact h
      · exact hInv.received_subset_sent i' k hold
    · intro j' k v hv
      rw [InstanceState.receiveMessage_processVariables] at hv
      exact hInv.inputBroadcastReturned_val j' k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j' hj A hA
      rw [InstanceState.receiveMessage_sent] at hA
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.echo_confirmed j' hj A hA
    · intro j' hj A hA
      rw [InstanceState.receiveMessage_processVariables] at hA
      exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.receiveMessage_sent] at hW
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.vote_confirmed j' hj W hW
    · intro j' hj W hW
      rw [InstanceState.receiveMessage_processVariables] at hW
      obtain ⟨Q, hQc, hQ⟩ := hInv.vote_backed j' hj W hW
      exact ⟨Q, hQc, fun q hq => by
        obtain ⟨A, hA, hAW⟩ := hQ q hq
        exact ⟨A, InstanceState.mem_receiveMessage_received.mpr (Or.inr hA), hAW⟩⟩
    · intro j' hj U hU
      rw [InstanceState.receiveMessage_sent] at hU
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.bind_confirmed j' hj U hU
    · intro j' hj U hU
      rw [InstanceState.receiveMessage_processVariables] at hU
      obtain ⟨Q, hQc, hQ⟩ := hInv.bind_backed j' hj U hU
      exact ⟨Q, hQc, fun q hq => by
        obtain ⟨W, hW, hWU⟩ := hQ q hq
        exact ⟨W, InstanceState.mem_receiveMessage_received.mpr (Or.inr hW), hWU⟩⟩
    · intro k hk y hy
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.inputBroadcastCall_backed k hk y hy
  | echo j hin hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i k m hm
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hm
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hm)
    · intro j' k v hv
      rw [InstanceState.multicast_processVariables] at hv
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j' hj A' hA'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hA'
      rcases hA' with ⟨rfl, hm'⟩ | hold
      · obtain rfl : A' = ((gatherProgramsAndNetwork s).processVariables j').accepted := by
          injection hm'
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
      · have hpre := hInv.echo_confirmed j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hA'
        obtain rfl : ((gatherProgramsAndNetwork s).processVariables j').accepted = A' := by
          injection hA'
        exact hcard
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hW
      rcases hW with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hU'
      rcases hU' with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.bind_confirmed j' hj U' hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj U' hU'
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hU'
        exact hInv.bind_backed j' hj U' hU'
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hU'
        exact hInv.bind_backed j' hj U' hU'
    · intro k hk y hy
      rw [InstanceState.multicast_processVariables]
      have h0 := hInv.inputBroadcastCall_backed k hk y hy
      by_cases hkj : k = j
      · subst hkj
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact h0
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkj]
        exact h0
  | vote j U hin hech happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i k m hm
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hm
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hm)
    · intro j' k v hv
      rw [InstanceState.multicast_processVariables] at hv
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j' hj A' hA'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hA'
      rcases hA' with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hA'
        exact hInv.echo_card j' hj A' hA'
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hW
      rcases hW with ⟨rfl, hm'⟩ | hold
      · obtain rfl : W = U := by injection hm'
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
      · have hpre := hInv.vote_confirmed j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hW
        obtain rfl : U = W := by
          injection hW
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨A, hA, -, hAU⟩ := hQm q hq
          exact ⟨A, hA, hAU⟩⟩
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hU'
      rcases hU' with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.bind_confirmed j' hj U' hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj U' hU'
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hU'
        exact hInv.bind_backed j' hj U' hU'
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hU'
        exact hInv.bind_backed j' hj U' hU'
    · intro k hk y hy
      rw [InstanceState.multicast_processVariables]
      have h0 := hInv.inputBroadcastCall_backed k hk y hy
      by_cases hkj : k = j
      · subst hkj
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact h0
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkj]
        exact h0
  | bind j U hin hvot happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i k m hm
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hm
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hm)
    · intro j' k v hv
      rw [InstanceState.multicast_processVariables] at hv
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j' hj A' hA'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hA'
      rcases hA' with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hA'
        exact hInv.echo_card j' hj A' hA'
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hW
      rcases hW with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hU'
      rcases hU' with ⟨rfl, hm'⟩ | hold
      · obtain rfl : U' = U := by injection hm'
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
      · have hpre := hInv.bind_confirmed j' hj U' hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
          exact hpre
    · intro j' hj U' hU'
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hU'
        obtain rfl : U = U' := by
          injection hU'
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨W, hW, -, hWU⟩ := hQm q hq
          exact ⟨W, hW, hWU⟩⟩
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hU'
        exact hInv.bind_backed j' hj U' hU'
    · intro k hk y hy
      rw [InstanceState.multicast_processVariables]
      have h0 := hInv.inputBroadcastCall_backed k hk y hy
      by_cases hkj : k = j
      · subst hkj
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact h0
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkj]
        exact h0
  | byzantine j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i k m' hm'
      rw [InstanceState.multicast_received] at hm'
      rw [InstanceState.mem_multicast_sent]
      exact Or.inr (hInv.received_subset_sent i k hm')
    · intro j' k v hv
      rw [InstanceState.multicast_processVariables] at hv
      exact hInv.inputBroadcastReturned_val j' k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j' hj A hA
      rw [InstanceState.mem_multicast_sent] at hA
      rw [InstanceState.multicast_processVariables]
      rcases hA with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.echo_confirmed j' hj A hold
    · intro j' hj A hA
      rw [InstanceState.multicast_processVariables] at hA
      exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent] at hW
      rw [InstanceState.multicast_processVariables]
      rcases hW with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.vote_confirmed j' hj W hold
    · intro j' hj W hW
      rw [InstanceState.multicast_processVariables] at hW
      rw [InstanceState.multicast_received]
      exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      rw [InstanceState.mem_multicast_sent] at hU
      rw [InstanceState.multicast_processVariables]
      rcases hU with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.bind_confirmed j' hj U hold
    · intro j' hj U hU
      rw [InstanceState.multicast_processVariables] at hU
      rw [InstanceState.multicast_received]
      exact hInv.bind_backed j' hj U hU
    · intro k hk y hy
      rw [InstanceState.multicast_processVariables]
      exact hInv.inputBroadcastCall_backed k hk y hy
  | inputBroadcastRet k j v hv hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setInputBroadcasts,
      gatherProgramsAndNetwork_setGatherProgramsAndNetwork, inputBroadcasts_setInputBroadcasts]
    · exact hInv.F_card
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_inputBroadcast_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_inputBroadcast_eq k'
    · intro i k' m hm
      rw [InstanceState.setProcessVariables_received] at hm
      rw [InstanceState.setProcessVariables_sent]
      exact hInv.received_subset_sent i k' hm
    · intro j' k' v' hv'
      by_cases hj : j' = j
      · subst hj
        rw [InstanceState.setProcessVariables_processVariables_self] at hv'
        dsimp only at hv'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self] at hv'
          rw [Function.update_self]
          obtain rfl : v = v' := by
            injection hv'
          exact hv
        · rw [Function.update_of_ne hk] at hv'
          rw [Function.update_of_ne hk]
          exact hInv.inputBroadcastReturned_val j' k' v' hv'
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hj] at hv'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self]
          exact hInv.inputBroadcastReturned_val j' k' v' hv'
        · rw [Function.update_of_ne hk]
          exact hInv.inputBroadcastReturned_val j' k' v' hv'
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hv' ⊢
        exact hInv.inputBroadcastVal_of_instanceInput k' v' hv'
      · rw [Function.update_of_ne hk] at hv' ⊢
        exact hInv.inputBroadcastVal_of_instanceInput k' v' hv'
    · intro j' hj A hA
      rw [InstanceState.setProcessVariables_sent] at hA
      have hpre := hInv.echo_confirmed j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hA
        exact hInv.echo_card j' hj A hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA
        exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.setProcessVariables_sent] at hW
      have hpre := hInv.vote_confirmed j' hj W hW
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j' hj W hW
      rw [InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      rw [InstanceState.setProcessVariables_sent] at hU
      have hpre := hInv.bind_confirmed j' hj U hU
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j' hj U hU
      rw [InstanceState.setProcessVariables_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hU
        exact hInv.bind_backed j' hj U hU
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hU
        exact hInv.bind_backed j' hj U hU
    · intro k' hk' y hy
      have h0 : (inputBroadcasts s k').input = some y := by
        by_cases hkk : k' = k
        · subst hkk
          rw [Function.update_self] at hy
          exact hy
        · rw [Function.update_of_ne hkk] at hy
          exact hy
      have h1 := hInv.inputBroadcastCall_backed k' hk' y h0
      by_cases hkj : k' = j
      · subst hkj
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact h1
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkj]
        exact h1
  | ret id g hin hbind hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setCore,
      gatherProgramsAndNetwork_setGatherProgramsAndNetwork, inputBroadcasts_setCore,
      inputBroadcasts_setGatherProgramsAndNetwork]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro i k m hm
      rw [InstanceState.setProcessVariables_received] at hm
      rw [InstanceState.setProcessVariables_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcessVariables_processVariables_self] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hj] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
    · exact hInv.inputBroadcastVal_of_instanceInput
    · intro j hj A hA
      rw [InstanceState.setProcessVariables_sent] at hA
      have hpre := hInv.echo_confirmed j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [InstanceState.setProcessVariables_sent] at hW
      have hpre := hInv.vote_confirmed j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [InstanceState.setProcessVariables_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [InstanceState.setProcessVariables_sent] at hU
      have hpre := hInv.bind_confirmed j hj U hU
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hpre
    · intro j hj U hU
      rw [InstanceState.setProcessVariables_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hU
        exact hInv.bind_backed j hj U hU
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hU
        exact hInv.bind_backed j hj U hU
    · intro k hk y hy
      have h0 := hInv.inputBroadcastCall_backed k hk y hy
      by_cases hkid : k = id
      · subst hkid
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact h0
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkid]
        exact h0
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hF : ∀ k, k ∉ (InstanceState.corrupt P id (gatherProgramsAndNetwork s)).F → k ∉
      (gatherProgramsAndNetwork s).F :=
      fun k hk hkF => hk (InstanceState.corrupt_F_subset (gatherProgramsAndNetwork s) id hkF)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_corruptAll, inputBroadcasts_corruptAll]
    · exact InstanceState.corrupt_card_le (gatherProgramsAndNetwork s) id hInv.F_card
    · intro k
      rw [BRB.SpecState.corrupt_F, InstanceState.corrupt_F, hInv.F_inputBroadcast_eq k]
    · intro i k m hm
      rw [InstanceState.corrupt_received] at hm
      rw [InstanceState.corrupt_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      rw [InstanceState.corrupt_processVariables] at hv
      rw [BRB.corrupt_val]
      exact hInv.inputBroadcastReturned_val j k v hv
    · intro k v hv
      rw [BRB.corrupt_val] at hv
      rw [BRB.corrupt_input]
      rcases hInv.inputBroadcastVal_of_instanceInput k v hv with hkF | hin
      · exact Or.inl (InstanceState.corrupt_F_subset (gatherProgramsAndNetwork s) id hkF)
      · exact Or.inr hin
    · intro j hj A hA
      rw [InstanceState.corrupt_sent] at hA
      rw [InstanceState.corrupt_processVariables]
      exact hInv.echo_confirmed j (hF j hj) A hA
    · intro j hj A hA
      rw [InstanceState.corrupt_processVariables] at hA
      exact hInv.echo_card j (hF j hj) A hA
    · intro j hj W hW
      rw [InstanceState.corrupt_sent] at hW
      rw [InstanceState.corrupt_processVariables]
      exact hInv.vote_confirmed j (hF j hj) W hW
    · intro j hj W hW
      rw [InstanceState.corrupt_processVariables] at hW
      rw [InstanceState.corrupt_received]
      exact hInv.vote_backed j (hF j hj) W hW
    · intro j hj U hU
      rw [InstanceState.corrupt_sent] at hU
      rw [InstanceState.corrupt_processVariables]
      exact hInv.bind_confirmed j (hF j hj) U hU
    · intro j hj U hU
      rw [InstanceState.corrupt_processVariables] at hU
      rw [InstanceState.corrupt_received]
      exact hInv.bind_backed j (hF j hj) U hU
    · intro k hk y hy
      rw [InstanceState.corrupt_processVariables]
      rw [BRB.corrupt_input] at hy
      exact hInv.inputBroadcastCall_backed k (hF k hk) y hy


/-! ### The approval of an echo field -/

omit [DecidableEq X] in
/-- A payload set approved by what one program's input instances returned is approved at the
instance: each returned value is the committed value of the instance that returned it. -/
theorem approved_of_approvedBy {s : StateOverBroadcastSpecification P.n X} (hConf : Conformance P s)
    {j : Fin P.n} {A : AcceptedPairs P.n X} (h : approvedBy ((gatherProgramsAndNetwork
      s).processVariables j) A) :
    approved s A :=
  fun p hp => hConf.inputBroadcastReturned_val j p.1 p.2 (h p hp)

/-- Committed input entries are write-once, so `approved` is monotone along
every transition. -/
theorem approved_mono {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)}
    (hstep : AlgorithmOverBroadcastSpecification P s l μ) (hs' : s' ∈ μ.support)
    {A : AcceptedPairs P.n X} (h : approved s A) : approved s' A := by
  have key : ∀ t : StateOverBroadcastSpecification P.n X,
      (∀ k v,
        (inputBroadcasts s k).val = some v → (inputBroadcasts t k).val = some v) → approved t A :=
    fun t ht p hp => ht p.1 p.2 (h p hp)
  cases hstep with
  | inputBroadcastCall j x hin hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [inputBroadcasts_setInputBroadcasts]
      by_cases hk : k = j
      · subst hk; rw [Function.update_self]; exact hv
      · rw [Function.update_of_ne hk]; exact hv
  | commitInputEntry k v hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k' v' hv' => ?_)
      dsimp only [inputBroadcasts_setInputBroadcasts]
      by_cases hk : k' = k
      · subst hk; rw [hv] at hv'; exact absurd hv' (by simp)
      · rw [Function.update_of_ne hk]; exact hv'
  | inputBroadcastRet k j v hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k' v' hv' => ?_)
      dsimp only [inputBroadcasts_setInputBroadcasts]
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self]; exact hv'
      · rw [Function.update_of_ne hk]; exact hv'
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [inputBroadcasts_corruptAll]
      rw [BRB.corrupt_val]; exact hv
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- The `ECHO` fields of the initial state are empty. -/
theorem echoApproved_initial :
    ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
      ((gatherProgramsAndNetwork ((instanceOverBroadcastSpecification P X).init)).processVariables
        j).sentEcho =
        some A →
        approved ((instanceOverBroadcastSpecification P X).init) A := by
  intro j A hA
  simp [gatherProgramsAndNetwork, InstanceState.processVariables, ProcessVariables.initial,
    BaseProcessVariables.initial] at hA

/-- **The approval of an `ECHO` field is inductive**: only the transition
`AlgorithmOverBroadcastSpecification.echo` writes the field, and the payload it writes is the
entries of what the writer's own input instances returned. -/
theorem echoApproved_step {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hConf : Conformance P s)
    (hEA : ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
      ((gatherProgramsAndNetwork s).processVariables j).sentEcho = some A → approved s A)
    (hstep : AlgorithmOverBroadcastSpecification P s l μ) (hs' : s' ∈ μ.support) :
    ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
      ((gatherProgramsAndNetwork s').processVariables j).sentEcho = some A → approved s' A := by
  intro j A hA
  refine approved_mono hstep hs' ?_
  cases hstep with
  | call id x hc =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      by_cases hk : j = id
      · subst hk; rw [InstanceState.setProcessVariables_processVariables_self] at hA; exact hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA; exact hA
  | echo j₀ hin hcard hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      rw [InstanceState.multicast_processVariables] at hA
      by_cases hk : j = j₀
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self] at hA
        obtain rfl : ((gatherProgramsAndNetwork s).processVariables j).accepted = A :=
          Option.some.inj hA
        exact approved_of_approvedBy hConf (ProcessVariables.accepted_subMap
          ((gatherProgramsAndNetwork
          s).processVariables
          j))
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA
        exact hEA j A hA
  | vote j₀ U hin hech happ hQ hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      rw [InstanceState.multicast_processVariables] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcessVariables_processVariables_self] at hA; exact hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA; exact hA
  | bind j₀ U hin hvot happ hQ hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      rw [InstanceState.multicast_processVariables] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcessVariables_processVariables_self] at hA; exact hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA; exact hA
  | inputBroadcastRet k j₀ v hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setInputBroadcasts,
        gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcessVariables_processVariables_self] at hA; exact hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA; exact hA
  | ret id g hin hbind hsub hQ hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setCore,
        gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      by_cases hk : j = id
      · subst hk; rw [InstanceState.setProcessVariables_processVariables_self] at hA; exact hA
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk] at hA; exact hA
  | deliver i j₀ m hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      rw [InstanceState.receiveMessage_processVariables] at hA; exact hA
  | byzantine j₀ m hj =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork] at hA
      rw [InstanceState.multicast_processVariables] at hA; exact hA
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherProgramsAndNetwork_corruptAll] at hA
      rw [InstanceState.corrupt_processVariables] at hA; exact hA
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hEA j A hA

/-! ### The invariant -/

/-- **The invariant of the composed gather instance**: the conformance clauses,
together with the approval of every `ECHO` field. -/
structure Invariant (P : Parameters) (s : StateOverBroadcastSpecification P.n X) : Prop extends
  Conformance
  P s where
  /-- The payload set in a process's `ECHO` field consists of committed input entries. No
  correctness premise: only the transition `AlgorithmOverBroadcastSpecification.echo` writes the
  field, and a corrupted sender's accepted pairs are entries of its returned value too. -/
  echo_approved : ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
    ((gatherProgramsAndNetwork s).processVariables j).sentEcho = some A → approved s A

/-- The invariant holds initially. -/
theorem Invariant.initial : Invariant P ((instanceOverBroadcastSpecification P X).init) :=
  ⟨Conformance.initial, echoApproved_initial⟩

/-- The invariant is preserved by every step. -/
theorem Invariant.step {s : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hInv : Invariant P s)
    (hstep : AlgorithmOverBroadcastSpecification P s l μ)
    {s' : StateOverBroadcastSpecification P.n X} (hs' : s' ∈ μ.support) : Invariant P s' :=
  ⟨hInv.toConformance.step hstep hs',
    echoApproved_step hInv.toConformance hInv.echo_approved hstep hs'⟩

end Gather
end ABA
end PLTS
