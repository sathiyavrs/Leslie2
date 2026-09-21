/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.StepOverBroadcastSpecification

/-!
# The core of the composed gather instance over broadcast specifications

The invariant of `Gather.instanceOverBroadcastSpecification` (`ABA/Gather/Composition.lean`), stated
over the composition's state through the views `gatherTier`, `inputBroadcasts`, `bindBroadcasts`,
`core`, and the argument that `coreOfNetwork` is a bound core. At every state at which some process
outside `F` holds a committed `BIND` payload, `coreOfNetwork` has at least `n − f`
entries, its entries are committed input entries, and it lies below the
committed `BIND` payload of every process outside `F`.

The counting is over one incidence on the gather network state, so the lemmas
that read that state alone — `mem_correct`, `mem_dominatedBy`,
`correct_filter_dominatedBy`, `sum_dominatedBy` — are the ones of
`ABA/Gather/MessagesAndCommonCore.lean`, applied to `networkOf`.

## The stores

A gather program reads what a broadcast instance returned to it out of its own
record. The clauses `inputBroadcastReturned_val` and `bindBroadcastReturned_val` carry a store entry
back to the commitment that wrote it: they are established at the `inputBroadcastRet` and
`bindRet` rows, whose guards are the broadcast specification's `val = some v`,
and they survive because a committed value is written once.

## The call records

The composition answers `call id x` on four rows and the call loop is a label
of its own, so an input instance may record a payload on a label at which the
gather record stands still. The provenance of a commitment therefore reads the
input instance's own call record, which is what `inputBroadcastVal_provenance` states.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-- The gather network state of the composition, read as an instance state over
the gather record. The core and the incidence read the sent sets and the
corrupted set, and no local record. -/
def networkOf {n : ℕ} (s : StateOverBroadcastSpecification n X) : InstanceState n (BaseProcessRecord
  n
  X) (Message n X) :=
  ((fun _ => LocalState.initial n (Message n X) (BaseProcessRecord.initial n X)), (gatherTier s).2)

omit [DecidableEq X] in
@[simp] theorem networkOf_sent {n : ℕ} (s : StateOverBroadcastSpecification n X) :
    (networkOf s).sent = (gatherTier s).sent := rfl

omit [DecidableEq X] in
@[simp] theorem networkOf_F {n : ℕ} (s : StateOverBroadcastSpecification n X) : (networkOf s).F =
  (gatherTier s).F
  := rfl

omit [DecidableEq X] in
/-- The core of the composition's gather network state. -/
theorem coreOf_networkOf (s : StateOverBroadcastSpecification P.n X) :
    coreOf P (networkOf s) = coreOfNetwork P (gatherTier s).2 := rfl

/-! ### The conformance clauses -/

/-- The conformance clauses. The `*_confirmed` clauses tie an honest sender's sent to
its write-once field, the `*_backed` clauses tie the fields to the receipts that
justified them, the store clauses tie a program's store to the commitment that
wrote it, and the provenance clauses are the broadcast commit guards, recorded
per instance. -/
structure Conformance (P : Parameters) (s : StateOverBroadcastSpecification P.n X) : Prop where
  /-- The corruption budget. -/
  F_card : (gatherTier s).F.card ≤ P.f
  /-- The input instances' corrupted sets are in lockstep with the gather
  network state's. -/
  F_inputBroadcast_eq : ∀ k, (inputBroadcasts s k).F = (gatherTier s).F
  /-- The bind instances' corrupted sets are in lockstep with the gather
  network state's. -/
  F_bind_eq : ∀ k, (bindBroadcasts s k).F = (gatherTier s).F
  /-- Delivered messages were multicast. -/
  received_subset_sent : ∀ i k, (gatherTier s).received i k ⊆ (gatherTier s).sent k
  /-- A value in a program's input store is the committed value of the instance
  that returned it. -/
  inputBroadcastReturned_val : ∀ j k v,
    ((gatherTier s).process j).inputBroadcastReturned k = some v → (inputBroadcasts s k).val = some
      v
  /-- A payload in a program's bind store is the committed payload of the
  instance that returned it. -/
  bindBroadcastReturned_val : ∀ j q U, ((gatherTier s).process j).bindBroadcastReturned q = some U →
    (bindBroadcasts s q).val = some U
  /-- A committed input entry of an honest process is the payload its input
  instance recorded. -/
  inputBroadcastVal_provenance : ∀ k v, (inputBroadcasts s k).val = some v →
    k ∈ (gatherTier s).F ∨ (inputBroadcasts s k).input = some v
  /-- A committed bind payload of an honest process is the payload its bind
  instance recorded. -/
  bindBroadcastVal_provenance : ∀ k U, (bindBroadcasts s k).val = some U →
    k ∈ (gatherTier s).F ∨ (bindBroadcasts s k).input = some U
  /-- An honest sender's sent `ECHO` matches its write-once field. -/
  echo_confirmed : ∀ j ∉ (gatherTier s).F, ∀ A, Message.echo A ∈ (gatherTier s).sent j →
    ((gatherTier s).process j).sentEcho = some A
  /-- An honest echo payload has at least `n − f` entries. -/
  echo_card : ∀ j ∉ (gatherTier s).F, ∀ A, ((gatherTier s).process j).sentEcho = some A →
    P.n - P.f ≤ A.card
  /-- An honest sender's sent `VOTE` matches its write-once field. -/
  vote_confirmed : ∀ j ∉ (gatherTier s).F, ∀ W, Message.vote W ∈ (gatherTier s).sent j →
    ((gatherTier s).process j).sentVote = some W
  /-- An honest vote is backed by `n − f` senders' echo payloads, each contained
  in it. -/
  vote_backed : ∀ j ∉ (gatherTier s).F, ∀ W, ((gatherTier s).process j).sentVote = some W →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ A, Message.echo A ∈ (gatherTier s).received j q ∧ A ⊆ W
  /-- An honest contributed bind payload is backed by `n − f` senders' vote
  payloads, each contained in it. -/
  bind_backed : ∀ j ∉ (gatherTier s).F, ∀ U, (bindBroadcasts s j).input = some U →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ W, Message.vote W ∈ (gatherTier s).received j q ∧ W ⊆ U

/-- The conformance clauses hold initially. -/
theorem Conformance.initial : Conformance P ((instanceOverBroadcastSpecification P X).init) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gatherTier, inputBroadcasts, bindBroadcasts, ProcessRecord.initial,
      BaseProcessRecord.initial, BRB.SpecState.initial, NetworkState.initial,
        InstanceState.process, InstanceState.sent, InstanceState.received, InstanceState.F]

omit [DecidableEq X] in
/-- **The conformance clauses are blind to the `BIND` field**: no clause reads
it, so a write to it at one program carries them over. -/
theorem Conformance.setSentBind {s : StateOverBroadcastSpecification P.n X} (hConf : Conformance P
  s) (j
  : Fin P.n)
    (U : AcceptedPairs P.n X) :
    Conformance P (setGatherTier s ((gatherTier s).setProcess j { (gatherTier s).process j with
      sentBind := some U })) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [gatherTier_setGatherTier, inputBroadcasts_setGatherTier,
    bindBroadcasts_setGatherTier, InstanceState.setProcess_F, InstanceState.setProcess_sent]
  · exact hConf.F_card
  · exact hConf.F_inputBroadcast_eq
  · exact hConf.F_bind_eq
  · simp only [InstanceState.setProcess_received]
    exact hConf.received_subset_sent
  · intro j' k v hv
    by_cases hk : j' = j
    · subst hk
      rw [InstanceState.setProcess_process_self] at hv
      exact hConf.inputBroadcastReturned_val j' k v hv
    · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hv
      exact hConf.inputBroadcastReturned_val j' k v hv
  · intro j' q U' hU'
    by_cases hk : j' = j
    · subst hk
      rw [InstanceState.setProcess_process_self] at hU'
      exact hConf.bindBroadcastReturned_val j' q U' hU'
    · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hU'
      exact hConf.bindBroadcastReturned_val j' q U' hU'
  · exact hConf.inputBroadcastVal_provenance
  · exact hConf.bindBroadcastVal_provenance
  · intro j' hj A hA
    by_cases hk : j' = j
    · subst hk
      rw [InstanceState.setProcess_process_self]
      exact hConf.echo_confirmed j' hj A hA
    · rw [InstanceState.setProcess_process_ne _ _ _ hk]
      exact hConf.echo_confirmed j' hj A hA
  · intro j' hj A hA
    by_cases hk : j' = j
    · subst hk
      rw [InstanceState.setProcess_process_self] at hA
      exact hConf.echo_card j' hj A hA
    · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
      exact hConf.echo_card j' hj A hA
  · intro j' hj W hW
    by_cases hk : j' = j
    · subst hk
      rw [InstanceState.setProcess_process_self]
      exact hConf.vote_confirmed j' hj W hW
    · rw [InstanceState.setProcess_process_ne _ _ _ hk]
      exact hConf.vote_confirmed j' hj W hW
  · simp only [InstanceState.setProcess_received]
    intro j' hj W hW
    by_cases hk : j' = j
    · subst hk
      rw [InstanceState.setProcess_process_self] at hW
      exact hConf.vote_backed j' hj W hW
    · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hW
      exact hConf.vote_backed j' hj W hW
  · simp only [InstanceState.setProcess_received]
    exact hConf.bind_backed

/-- The conformance clauses are preserved by every step. -/
theorem Conformance.step {s : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hInv : Conformance P s) (hstep :
      StepOverBroadcastSpecification P s l μ)
    {s' : StateOverBroadcastSpecification P.n X} (hs' : s' ∈ μ.support) : Conformance P s' := by
  cases hstep with
  | call id x h hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setInputBroadcasts, gatherTier_setGatherTier,
      inputBroadcasts_setInputBroadcasts, bindBroadcasts_setInputBroadcasts,
        bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.F_inputBroadcast_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_inputBroadcast_eq k
    · exact hInv.F_bind_eq
    · intro i k m hm
      rw [InstanceState.setProcess_received] at hm
      rw [InstanceState.setProcess_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      have hv0 : ((gatherTier s).process j).inputBroadcastReturned k = some v := by
        by_cases hj : j = id
        · subst hj
          rw [InstanceState.setProcess_process_self] at hv
          exact hv
        · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hv
          exact hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.inputBroadcastReturned_val j k v hv0
      · rw [Function.update_of_ne hk]
        exact hInv.inputBroadcastReturned_val j k v hv0
    · intro j q U hU
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcess_process_self] at hU
        exact hInv.bindBroadcastReturned_val j q U hU
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hU
        exact hInv.bindBroadcastReturned_val j q U hU
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self] at hv ⊢
        rcases hInv.inputBroadcastVal_provenance k v hv with hF | hin
        · exact Or.inl hF
        · rw [hb] at hin
          exact absurd hin (by simp)
      · rw [Function.update_of_ne hk] at hv ⊢
        exact hInv.inputBroadcastVal_provenance k v hv
    · exact hInv.bindBroadcastVal_provenance
    · intro j hj A hA
      rw [InstanceState.setProcess_sent] at hA
      have hpre := hInv.echo_confirmed j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [InstanceState.setProcess_sent] at hW
      have hpre := hInv.vote_confirmed j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [InstanceState.setProcess_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [InstanceState.setProcess_received]
      exact hInv.bind_backed j hj U hU
  | callSpecLoop id x h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setGatherTier, inputBroadcasts_setGatherTier,
      bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      rw [InstanceState.setProcess_received] at hm
      rw [InstanceState.setProcess_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcess_process_self] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
    · intro j q U hU
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcess_process_self] at hU
        exact hInv.bindBroadcastReturned_val j q U hU
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hU
        exact hInv.bindBroadcastReturned_val j q U hU
    · exact hInv.inputBroadcastVal_provenance
    · exact hInv.bindBroadcastVal_provenance
    · intro j hj A hA
      rw [InstanceState.setProcess_sent] at hA
      have hpre := hInv.echo_confirmed j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [InstanceState.setProcess_sent] at hW
      have hpre := hInv.vote_confirmed j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [InstanceState.setProcess_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [InstanceState.setProcess_received]
      exact hInv.bind_backed j hj U hU
  | callProgramLoop id x hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.F_bind_eq, hInv.received_subset_sent, ?_,
      hInv.bindBroadcastReturned_val, ?_, hInv.bindBroadcastVal_provenance, hInv.echo_confirmed,
        hInv.echo_card, hInv.vote_confirmed,
      hInv.vote_backed, hInv.bind_backed⟩
    all_goals dsimp only [gatherTier_setInputBroadcasts, inputBroadcasts_setInputBroadcasts]
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.F_inputBroadcast_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_inputBroadcast_eq k
    · intro j k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.inputBroadcastReturned_val j k v hv
      · rw [Function.update_of_ne hk]
        exact hInv.inputBroadcastReturned_val j k v hv
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self] at hv ⊢
        rcases hInv.inputBroadcastVal_provenance k v hv with hF | hin
        · exact Or.inl hF
        · rw [hb] at hin
          exact absurd hin (by simp)
      · rw [Function.update_of_ne hk] at hv ⊢
        exact hInv.inputBroadcastVal_provenance k v hv
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | commitInputEntry k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.F_bind_eq, hInv.received_subset_sent, ?_,
      hInv.bindBroadcastReturned_val, ?_, hInv.bindBroadcastVal_provenance, hInv.echo_confirmed,
        hInv.echo_card, hInv.vote_confirmed,
      hInv.vote_backed, hInv.bind_backed⟩
    all_goals dsimp only [gatherTier_setInputBroadcasts, inputBroadcasts_setInputBroadcasts]
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
        exact hInv.inputBroadcastVal_provenance k' v' hv'
  | commitBindEntry q U hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_inputBroadcast_eq, ?_, hInv.received_subset_sent,
      hInv.inputBroadcastReturned_val, ?_, hInv.inputBroadcastVal_provenance, ?_,
        hInv.echo_confirmed, hInv.echo_card, hInv.vote_confirmed,
      hInv.vote_backed, ?_⟩
    all_goals dsimp only [gatherTier_setBindBroadcasts, bindBroadcasts_setBindBroadcasts]
    · intro q'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self]
        exact hInv.F_bind_eq q'
      · rw [Function.update_of_ne hq]
        exact hInv.F_bind_eq q'
    · intro j q' U' hU'
      by_cases hq : q' = q
      · subst hq
        have hold := hInv.bindBroadcastReturned_val j q' U' hU'
        rw [hv] at hold
        exact absurd hold (by simp)
      · rw [Function.update_of_ne hq]
        exact hInv.bindBroadcastReturned_val j q' U' hU'
    · intro q' U' hU'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self] at hU' ⊢
        have hUU : some U = some U' := hU'
        obtain rfl : U = U' := by
          injection hUU
        rcases hm with hF | hin
        · exact Or.inl (hInv.F_bind_eq q' ▸ hF)
        · exact Or.inr hin
      · rw [Function.update_of_ne hq] at hU' ⊢
        exact hInv.bindBroadcastVal_provenance q' U' hU'
    · intro j hj U' hU'
      by_cases hq : j = q
      · subst hq
        rw [Function.update_self] at hU'
        exact hInv.bind_backed j hj U' hU'
      · rw [Function.update_of_ne hq] at hU'
        exact hInv.bind_backed j hj U' hU'
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setGatherTier, inputBroadcasts_setGatherTier,
      bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · exact hInv.F_bind_eq
    · intro i' k m' hm'
      rw [InstanceState.mem_receiveMessage_received] at hm'
      rw [InstanceState.receiveMessage_sent]
      rcases hm' with ⟨-, rfl, rfl⟩ | hold
      · exact h
      · exact hInv.received_subset_sent i' k hold
    · intro j' k v hv
      rw [InstanceState.receiveMessage_process] at hv
      exact hInv.inputBroadcastReturned_val j' k v hv
    · intro j' q U hU
      rw [InstanceState.receiveMessage_process] at hU
      exact hInv.bindBroadcastReturned_val j' q U hU
    · exact hInv.inputBroadcastVal_provenance
    · exact hInv.bindBroadcastVal_provenance
    · intro j' hj A hA
      rw [InstanceState.receiveMessage_sent] at hA
      rw [InstanceState.receiveMessage_process]
      exact hInv.echo_confirmed j' hj A hA
    · intro j' hj A hA
      rw [InstanceState.receiveMessage_process] at hA
      exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.receiveMessage_sent] at hW
      rw [InstanceState.receiveMessage_process]
      exact hInv.vote_confirmed j' hj W hW
    · intro j' hj W hW
      rw [InstanceState.receiveMessage_process] at hW
      obtain ⟨Q, hQc, hQ⟩ := hInv.vote_backed j' hj W hW
      exact ⟨Q, hQc, fun q hq => by
        obtain ⟨A, hA, hAW⟩ := hQ q hq
        exact ⟨A, InstanceState.mem_receiveMessage_received.mpr (Or.inr hA), hAW⟩⟩
    · intro j' hj U hU
      obtain ⟨Q, hQc, hQ⟩ := hInv.bind_backed j' hj U hU
      exact ⟨Q, hQc, fun q hq => by
        obtain ⟨W, hW, hWU⟩ := hQ q hq
        exact ⟨W, InstanceState.mem_receiveMessage_received.mpr (Or.inr hW), hWU⟩⟩
  | echo j hin hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setGatherTier, inputBroadcasts_setGatherTier,
      bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received] at hm
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent]
      exact Or.inr (hInv.received_subset_sent i k hm)
    · intro j' k v hv
      rw [InstanceState.multicast_process] at hv
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
    · intro j' q U hU
      rw [InstanceState.multicast_process] at hU
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hU
        exact hInv.bindBroadcastReturned_val j' q U hU
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hU
        exact hInv.bindBroadcastReturned_val j' q U hU
    · exact hInv.inputBroadcastVal_provenance
    · exact hInv.bindBroadcastVal_provenance
    · intro j' hj A' hA'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hA'
      rcases hA' with ⟨rfl, hm'⟩ | hold
      · obtain rfl : A' = ((gatherTier s).process j').accepted := by injection hm'
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
      · have hpre := hInv.echo_confirmed j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hA'
        obtain rfl : ((gatherTier s).process j').accepted = A' := by
          injection hA'
        exact hcard
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hW
      rcases hW with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received]
      exact hInv.bind_backed j' hj U hU
  | vote j U hin hech happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setGatherTier, inputBroadcasts_setGatherTier,
      bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received] at hm
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent]
      exact Or.inr (hInv.received_subset_sent i k hm)
    · intro j' k v hv
      rw [InstanceState.multicast_process] at hv
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hv
        exact hInv.inputBroadcastReturned_val j' k v hv
    · intro j' q U' hU'
      rw [InstanceState.multicast_process] at hU'
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hU'
        exact hInv.bindBroadcastReturned_val j' q U' hU'
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hU'
        exact hInv.bindBroadcastReturned_val j' q U' hU'
    · exact hInv.inputBroadcastVal_provenance
    · exact hInv.bindBroadcastVal_provenance
    · intro j' hj A' hA'
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hA'
      rcases hA' with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hA'
        exact hInv.echo_card j' hj A' hA'
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hW
      rcases hW with ⟨rfl, hm'⟩ | hold
      · obtain rfl : W = U := by injection hm'
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
      · have hpre := hInv.vote_confirmed j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hW
        obtain rfl : U = W := by
          injection hW
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨A, hA, -, hAU⟩ := hQm q hq
          exact ⟨A, hA, hAU⟩⟩
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received]
      exact hInv.bind_backed j' hj U' hU'
  | bindCall j U hin hvot hsnd happ hQ hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Conformance.setSentBind (s := setBindBroadcasts s (Function.update (bindBroadcasts s) j
      { bindBroadcasts s j with input := some U })) ?_ j U
    refine ⟨hInv.F_card, hInv.F_inputBroadcast_eq, ?_, hInv.received_subset_sent,
      hInv.inputBroadcastReturned_val, ?_, hInv.inputBroadcastVal_provenance, ?_,
        hInv.echo_confirmed, hInv.echo_card, hInv.vote_confirmed,
      hInv.vote_backed, ?_⟩
    all_goals dsimp only [gatherTier_setBindBroadcasts, bindBroadcasts_setBindBroadcasts]
    · intro q
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self]
        exact hInv.F_bind_eq q
      · rw [Function.update_of_ne hq]
        exact hInv.F_bind_eq q
    · intro j' q U' hU'
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self]
        exact hInv.bindBroadcastReturned_val j' q U' hU'
      · rw [Function.update_of_ne hq]
        exact hInv.bindBroadcastReturned_val j' q U' hU'
    · intro q U' hU'
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self] at hU' ⊢
        rcases hInv.bindBroadcastVal_provenance q U' hU' with hF | hin'
        · exact Or.inl hF
        · rw [hb] at hin'
          exact absurd hin' (by simp)
      · rw [Function.update_of_ne hq] at hU' ⊢
        exact hInv.bindBroadcastVal_provenance q U' hU'
    · intro j' hj U' hU'
      by_cases hq : j' = j
      · subst hq
        rw [Function.update_self] at hU'
        have hUU : some U = some U' := hU'
        obtain rfl : U = U' := by
          injection hUU
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨W, hW, -, hWU⟩ := hQm q hq
          exact ⟨W, hW, hWU⟩⟩
      · rw [Function.update_of_ne hq] at hU'
        exact hInv.bind_backed j' hj U' hU'
  | bindCallSpecLoop j U hin hvot hsnd happ hQ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv.setSentBind j U
  | byzantine j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setGatherTier, inputBroadcasts_setGatherTier,
      bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · exact hInv.F_bind_eq
    · intro i k m' hm'
      rw [InstanceState.multicast_received] at hm'
      rw [InstanceState.mem_multicast_sent]
      exact Or.inr (hInv.received_subset_sent i k hm')
    · intro j' k v hv
      rw [InstanceState.multicast_process] at hv
      exact hInv.inputBroadcastReturned_val j' k v hv
    · intro j' q U hU
      rw [InstanceState.multicast_process] at hU
      exact hInv.bindBroadcastReturned_val j' q U hU
    · exact hInv.inputBroadcastVal_provenance
    · exact hInv.bindBroadcastVal_provenance
    · intro j' hj A hA
      rw [InstanceState.mem_multicast_sent] at hA
      rw [InstanceState.multicast_process]
      rcases hA with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.echo_confirmed j' hj A hold
    · intro j' hj A hA
      rw [InstanceState.multicast_process] at hA
      exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.mem_multicast_sent] at hW
      rw [InstanceState.multicast_process]
      rcases hW with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.vote_confirmed j' hj W hold
    · intro j' hj W hW
      rw [InstanceState.multicast_process] at hW
      rw [InstanceState.multicast_received]
      exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      rw [InstanceState.multicast_received]
      exact hInv.bind_backed j' hj U hU
  | inputBroadcastRet k j v hv hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setInputBroadcasts, gatherTier_setGatherTier,
      inputBroadcasts_setInputBroadcasts, bindBroadcasts_setInputBroadcasts,
        bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_inputBroadcast_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_inputBroadcast_eq k'
    · exact hInv.F_bind_eq
    · intro i k' m hm
      rw [InstanceState.setProcess_received] at hm
      rw [InstanceState.setProcess_sent]
      exact hInv.received_subset_sent i k' hm
    · intro j' k' v' hv'
      by_cases hj : j' = j
      · subst hj
        rw [InstanceState.setProcess_process_self] at hv'
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
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hv'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self]
          exact hInv.inputBroadcastReturned_val j' k' v' hv'
        · rw [Function.update_of_ne hk]
          exact hInv.inputBroadcastReturned_val j' k' v' hv'
    · intro j' q U hU
      by_cases hj : j' = j
      · subst hj
        rw [InstanceState.setProcess_process_self] at hU
        exact hInv.bindBroadcastReturned_val j' q U hU
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hU
        exact hInv.bindBroadcastReturned_val j' q U hU
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hv' ⊢
        exact hInv.inputBroadcastVal_provenance k' v' hv'
      · rw [Function.update_of_ne hk] at hv' ⊢
        exact hInv.inputBroadcastVal_provenance k' v' hv'
    · exact hInv.bindBroadcastVal_provenance
    · intro j' hj A hA
      rw [InstanceState.setProcess_sent] at hA
      have hpre := hInv.echo_confirmed j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hA
        exact hInv.echo_card j' hj A hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
        exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.setProcess_sent] at hW
      have hpre := hInv.vote_confirmed j' hj W hW
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j' hj W hW
      rw [InstanceState.setProcess_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      rw [InstanceState.setProcess_received]
      exact hInv.bind_backed j' hj U hU
  | bindRet q j U hv hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setBindBroadcasts, gatherTier_setGatherTier,
      bindBroadcasts_setBindBroadcasts, inputBroadcasts_setBindBroadcasts,
        inputBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · intro q'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self]
        exact hInv.F_bind_eq q'
      · rw [Function.update_of_ne hq]
        exact hInv.F_bind_eq q'
    · intro i k m hm
      rw [InstanceState.setProcess_received] at hm
      rw [InstanceState.setProcess_sent]
      exact hInv.received_subset_sent i k hm
    · intro j' k v hv'
      by_cases hj : j' = j
      · subst hj
        rw [InstanceState.setProcess_process_self] at hv'
        exact hInv.inputBroadcastReturned_val j' k v hv'
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hv'
        exact hInv.inputBroadcastReturned_val j' k v hv'
    · intro j' q' U' hU'
      by_cases hj : j' = j
      · subst hj
        rw [InstanceState.setProcess_process_self] at hU'
        dsimp only at hU'
        by_cases hq : q' = q
        · subst hq
          rw [Function.update_self] at hU'
          rw [Function.update_self]
          obtain rfl : U = U' := by
            injection hU'
          exact hv
        · rw [Function.update_of_ne hq] at hU'
          rw [Function.update_of_ne hq]
          exact hInv.bindBroadcastReturned_val j' q' U' hU'
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hU'
        by_cases hq : q' = q
        · subst hq
          rw [Function.update_self]
          exact hInv.bindBroadcastReturned_val j' q' U' hU'
        · rw [Function.update_of_ne hq]
          exact hInv.bindBroadcastReturned_val j' q' U' hU'
    · exact hInv.inputBroadcastVal_provenance
    · intro q' U' hU'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self] at hU' ⊢
        exact hInv.bindBroadcastVal_provenance q' U' hU'
      · rw [Function.update_of_ne hq] at hU' ⊢
        exact hInv.bindBroadcastVal_provenance q' U' hU'
    · intro j' hj A hA
      rw [InstanceState.setProcess_sent] at hA
      have hpre := hInv.echo_confirmed j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hA
        exact hInv.echo_card j' hj A hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
        exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [InstanceState.setProcess_sent] at hW
      have hpre := hInv.vote_confirmed j' hj W hW
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j' hj W hW
      rw [InstanceState.setProcess_received]
      by_cases hk : j' = j
      · subst hk
        rw [InstanceState.setProcess_process_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      rw [InstanceState.setProcess_received]
      by_cases hq : j' = q
      · subst hq
        rw [Function.update_self] at hU'
        exact hInv.bind_backed j' hj U' hU'
      · rw [Function.update_of_ne hq] at hU'
        exact hInv.bind_backed j' hj U' hU'
  | ret id g hin hbind hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_setCore, gatherTier_setGatherTier, inputBroadcasts_setCore,
      inputBroadcasts_setGatherTier, bindBroadcasts_setCore, bindBroadcasts_setGatherTier]
    · exact hInv.F_card
    · exact hInv.F_inputBroadcast_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      rw [InstanceState.setProcess_received] at hm
      rw [InstanceState.setProcess_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcess_process_self] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hv
        exact hInv.inputBroadcastReturned_val j k v hv
    · intro j q U hU
      by_cases hj : j = id
      · subst hj
        rw [InstanceState.setProcess_process_self] at hU
        exact hInv.bindBroadcastReturned_val j q U hU
      · rw [InstanceState.setProcess_process_ne _ _ _ hj] at hU
        exact hInv.bindBroadcastReturned_val j q U hU
    · exact hInv.inputBroadcastVal_provenance
    · exact hInv.bindBroadcastVal_provenance
    · intro j hj A hA
      rw [InstanceState.setProcess_sent] at hA
      have hpre := hInv.echo_confirmed j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [InstanceState.setProcess_sent] at hW
      have hpre := hInv.vote_confirmed j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [InstanceState.setProcess_received]
      by_cases hk : j = id
      · subst hk
        rw [InstanceState.setProcess_process_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [InstanceState.setProcess_received]
      exact hInv.bind_backed j hj U hU
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hF : ∀ k, k ∉ (InstanceState.corrupt P id (gatherTier s)).F → k ∉ (gatherTier s).F :=
      fun k hk hkF => hk (InstanceState.corrupt_F_subset (gatherTier s) id hkF)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherTier_corruptAll, inputBroadcasts_corruptAll,
      bindBroadcasts_corruptAll]
    · exact InstanceState.corrupt_card_le (gatherTier s) id hInv.F_card
    · intro k
      rw [BRB.SpecState.corrupt_F, InstanceState.corrupt_F, hInv.F_inputBroadcast_eq k]
    · intro k
      rw [BRB.SpecState.corrupt_F, InstanceState.corrupt_F, hInv.F_bind_eq k]
    · intro i k m hm
      rw [InstanceState.corrupt_received] at hm
      rw [InstanceState.corrupt_sent]
      exact hInv.received_subset_sent i k hm
    · intro j k v hv
      rw [InstanceState.corrupt_process] at hv
      rw [BRB.corrupt_val]
      exact hInv.inputBroadcastReturned_val j k v hv
    · intro j q U hU
      rw [InstanceState.corrupt_process] at hU
      rw [BRB.corrupt_val]
      exact hInv.bindBroadcastReturned_val j q U hU
    · intro k v hv
      rw [BRB.corrupt_val] at hv
      rw [BRB.corrupt_input]
      rcases hInv.inputBroadcastVal_provenance k v hv with hkF | hin
      · exact Or.inl (InstanceState.corrupt_F_subset (gatherTier s) id hkF)
      · exact Or.inr hin
    · intro k U hU
      rw [BRB.corrupt_val] at hU
      rw [BRB.corrupt_input]
      rcases hInv.bindBroadcastVal_provenance k U hU with hkF | hin
      · exact Or.inl (InstanceState.corrupt_F_subset (gatherTier s) id hkF)
      · exact Or.inr hin
    · intro j hj A hA
      rw [InstanceState.corrupt_sent] at hA
      rw [InstanceState.corrupt_process]
      exact hInv.echo_confirmed j (hF j hj) A hA
    · intro j hj A hA
      rw [InstanceState.corrupt_process] at hA
      exact hInv.echo_card j (hF j hj) A hA
    · intro j hj W hW
      rw [InstanceState.corrupt_sent] at hW
      rw [InstanceState.corrupt_process]
      exact hInv.vote_confirmed j (hF j hj) W hW
    · intro j hj W hW
      rw [InstanceState.corrupt_process] at hW
      rw [InstanceState.corrupt_received]
      exact hInv.vote_backed j (hF j hj) W hW
    · intro j hj U hU
      rw [BRB.corrupt_input] at hU
      rw [InstanceState.corrupt_received]
      exact hInv.bind_backed j (hF j hj) U hU


/-! ### The approval of an echo field -/

omit [DecidableEq X] in
/-- A payload set approved by one program's input store is approved at the
instance: each entry of the store is the committed value of the instance that
returned it. -/
theorem approved_of_approvedBy {s : StateOverBroadcastSpecification P.n X} (hConf : Conformance P s)
    {j : Fin P.n} {A : AcceptedPairs P.n X} (h : approvedBy ((gatherTier s).process j) A) :
    approved s A :=
  fun p hp => hConf.inputBroadcastReturned_val j p.1 p.2 (h p hp)

/-- Committed input entries are write-once, so `approved` is monotone along
every rule. -/
theorem approved_mono {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hstep : StepOverBroadcastSpecification P s l
      μ)
    (hs' : s' ∈ μ.support) {A : AcceptedPairs P.n X} (h : approved s A) : approved s' A := by
  have key : ∀ t : StateOverBroadcastSpecification P.n X,
      (∀ k v,
        (inputBroadcasts s k).val = some v → (inputBroadcasts t k).val = some v) → approved t A :=
    fun t ht p hp => ht p.1 p.2 (h p hp)
  cases hstep with
  | call id x hc hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [inputBroadcasts_setInputBroadcasts]
      by_cases hk : k = id
      · subst hk; rw [Function.update_self]; exact hv
      · rw [Function.update_of_ne hk]; exact hv
  | callProgramLoop id x hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [inputBroadcasts_setInputBroadcasts]
      by_cases hk : k = id
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
      ((gatherTier ((instanceOverBroadcastSpecification P X).init)).process j).sentEcho = some A →
        approved ((instanceOverBroadcastSpecification P X).init) A := by
  intro j A hA
  simp [gatherTier, InstanceState.process, ProcessRecord.initial, BaseProcessRecord.initial] at hA

/-- **The approval of an `ECHO` field is inductive**: only `StepOverBroadcastSpecification.echo`
writes the field, and the payload it writes is the entries of the writer's own
store. -/
theorem echoApproved_step {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hConf : Conformance P s)
    (hEA : ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
      ((gatherTier s).process j).sentEcho = some A → approved s A)
    (hstep : StepOverBroadcastSpecification P s l μ) (hs' : s' ∈ μ.support) :
    ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
      ((gatherTier s').process j).sentEcho = some A → approved s' A := by
  intro j A hA
  refine approved_mono hstep hs' ?_
  cases hstep with
  | call id x hc hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setInputBroadcasts, gatherTier_setGatherTier] at hA
      by_cases hk : j = id
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | callSpecLoop id x hc =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setGatherTier] at hA
      by_cases hk : j = id
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | echo j₀ hin hcard hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [gatherTier_setGatherTier] at hA
      rw [InstanceState.multicast_process] at hA
      by_cases hk : j = j₀
      · subst hk
        rw [InstanceState.setProcess_process_self] at hA
        obtain rfl : ((gatherTier s).process j).accepted = A := Option.some.inj hA
        exact approved_of_approvedBy hConf (ProcessRecord.accepted_subMap ((gatherTier s).process
          j))
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA
        exact hEA j A hA
  | vote j₀ U hin hech happ hQ hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setGatherTier] at hA
      rw [InstanceState.multicast_process] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | bindCall j₀ U hin hvot hsnd happ hQ hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setBindBroadcasts, gatherTier_setGatherTier] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | bindCallSpecLoop j₀ U hin hvot hsnd happ hQ =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setGatherTier] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | inputBroadcastRet k j₀ v hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setInputBroadcasts, gatherTier_setGatherTier] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | bindRet q j₀ U hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setBindBroadcasts, gatherTier_setGatherTier] at hA
      by_cases hk : j = j₀
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | ret id g hin hbind hsub hQ hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setCore, gatherTier_setGatherTier] at hA
      by_cases hk : j = id
      · subst hk; rw [InstanceState.setProcess_process_self] at hA; exact hA
      · rw [InstanceState.setProcess_process_ne _ _ _ hk] at hA; exact hA
  | deliver i j₀ m hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setGatherTier] at hA
      rw [InstanceState.receiveMessage_process] at hA; exact hA
  | byzantine j₀ m hj =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_setGatherTier] at hA
      rw [InstanceState.multicast_process] at hA; exact hA
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [gatherTier_corruptAll] at hA
      rw [InstanceState.corrupt_process] at hA; exact hA
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hEA j A hA

/-! ### The invariant -/

/-- **The invariant of the composed gather instance**: the conformance clauses,
together with the approval of every `ECHO` field. -/
structure Invariant (P : Parameters) (s : StateOverBroadcastSpecification P.n X) : Prop extends
  Conformance
  P s where
  /-- The payload set in a process's `ECHO` field consists of committed input
  entries. No honesty side condition: only `StepOverBroadcastSpecification.echo` writes the field,
  and a corrupted sender's accepted pairs are entries of its store too. -/
  echo_approved : ∀ (j : Fin P.n) (A : AcceptedPairs P.n X),
    ((gatherTier s).process j).sentEcho = some A → approved s A

/-- The invariant holds initially. -/
theorem Invariant.initial : Invariant P ((instanceOverBroadcastSpecification P X).init) :=
  ⟨Conformance.initial, echoApproved_initial⟩

/-- The invariant is preserved by every step. -/
theorem Invariant.step {s : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hInv : Invariant P s) (hstep :
      StepOverBroadcastSpecification P s l μ)
    {s' : StateOverBroadcastSpecification P.n X} (hs' : s' ∈ μ.support) : Invariant P s' :=
  ⟨hInv.toConformance.step hstep hs',
    echoApproved_step hInv.toConformance hInv.echo_approved hstep hs'⟩


/-! ### The incidence on the gather network state

The rows of the incidence read the sent sets and the corrupted set, so
`mem_correct`, `card_correct`, `mem_dominatedBy`, `correct_filter_dominatedBy` and
`sum_dominatedBy` apply to `networkOf` as they stand. What the invariant supplies is
the width of a row. -/

omit [DecidableEq X] in
/-- The `ECHO` payload of a process outside `F` is the one its `sentEcho` field
holds. -/
theorem echoOf_eq {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) {j : Fin P.n}
    (hj : j ∉ (gatherTier s).F) {A : AcceptedPairs P.n X} (hA : Message.echo A ∈ (gatherTier s).sent
      j) :
    echoOf (networkOf s) j = A := by
  classical
  have hex : ∃ A : AcceptedPairs P.n X, Message.echo A ∈ (networkOf s).sent j := ⟨A, hA⟩
  rw [echoOf, dif_pos hex]
  have h1 := hInv.echo_confirmed j hj _ hex.choose_spec
  have h2 := hInv.echo_confirmed j hj A hA
  rw [h1] at h2
  exact Option.some.inj h2

omit [DecidableEq X] in
/-- **Every row is wide**: a process outside `F` dominates at least `n − f`
senders. Its `VOTE` payload, if it has one, is backed by `n − f` `ECHO`
receipts; if it has none the condition is vacuous and the row is
everything. -/
theorem dominatedBy_card {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) {q : Fin
  P.n}
    (hq : q ∉ (gatherTier s).F) : P.n - P.f ≤ (dominatedBy (networkOf s) q).card := by
  classical
  by_cases hv : ∃ W : AcceptedPairs P.n X, Message.vote W ∈ (gatherTier s).sent q
  · obtain ⟨W, hW⟩ := hv
    have hslot := hInv.vote_confirmed q hq W hW
    obtain ⟨Q, hQc, hQm⟩ := hInv.vote_backed q hq W hslot
    refine le_trans hQc (Finset.card_le_card fun j hj => ?_)
    rw [mem_dominatedBy]
    intro W' hW'
    have hslot' := hInv.vote_confirmed q hq W' hW'
    rw [hslot] at hslot'
    obtain rfl : W = W' := Option.some.inj hslot'
    obtain ⟨A, hA, hAW⟩ := hQm j hj
    exact ⟨A, hInv.received_subset_sent q j hA, hAW⟩
  · have hall : dominatedBy (networkOf s) q = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr fun j => ?_
      rw [mem_dominatedBy]
      intro W hW
      exact absurd ⟨W, hW⟩ hv
    rw [hall, Finset.card_univ, Fintype.card_fin]
    omega

open scoped Classical in
omit [DecidableEq X] in
/-- A row of a process outside `F` meets the processes outside `F` in at least
`n − f − |F|` of them. -/
theorem dominatedBy_correct_card {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {q : Fin P.n} (hq : q ∉ (gatherTier s).F) :
    P.n - P.f - (gatherTier s).F.card ≤
      ((correct (networkOf s)).filter (fun j => j ∈ dominatedBy (networkOf s) q)).card := by
  rw [correct_filter_dominatedBy, networkOf_F]
  have h1 := Finset.le_card_sdiff (gatherTier s).F (dominatedBy (networkOf s) q)
  have h2 := dominatedBy_card hInv hq
  omega

open scoped Classical in
omit [DecidableEq X] in
/-- **The pigeonhole.** Some sender outside `F` has at least `n − f − |F|`
dominators. -/
theorem exists_dominators {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) :
    ∃ j₀, j₀ ∈ correct (networkOf s) ∧
      P.n - P.f - (gatherTier s).F.card ≤ (dominators (networkOf s) j₀).card := by
  by_contra hc
  push Not at hc
  have hF := hInv.F_card
  have hf := P.hResilience
  set H : Finset (Fin P.n) := correct (networkOf s) with hH
  set m : ℕ := P.n - P.f - (gatherTier s).F.card with hm
  have hHcard : H.card = P.n - (gatherTier s).F.card := card_correct
  have hpos : 0 < H.card := by
    omega
  have hlow : ∀ q ∈ H, m ≤ ((correct (networkOf s)).filter
      (fun j => j ∈ dominatedBy (networkOf s) q)).card :=
    fun q hq => dominatedBy_correct_card hInv (mem_correct.mp (hH ▸ hq))
  have hsum2 : H.card * m
      ≤ ∑ q ∈ H, ((correct (networkOf s)).filter
        (fun j => j ∈ dominatedBy (networkOf s) q)).card := by
    simpa [smul_eq_mul] using Finset.card_nsmul_le_sum H _ m hlow
  rw [sum_dominatedBy, ← hH] at hsum2
  have hle : ∀ j ∈ H, (dominators (networkOf s) j).card ≤ m - 1 := fun j hj => by
    have := hc j (hH ▸ hj); omega
  have hsum1 : ∑ j ∈ H, (dominators (networkOf s) j).card ≤ H.card * (m - 1) := by
    simpa [smul_eq_mul] using Finset.sum_le_card_nsmul H _ (m - 1) hle
  have hstrict : H.card * (m - 1) < H.card * m :=
    mul_lt_mul_of_pos_left (by omega) hpos
  omega

/-! ### The single core -/

open scoped Classical in
omit [DecidableEq X] in
/-- **The transfer.** A sender outside `F` with at least `f + 1` dominators has
its `ECHO` payload below every committed `BIND` payload of a process outside
`F`: the dominators meet that payload's backing `VOTE` quorum of `n − f`, and
the meeting process's write-once `VOTE` payload lies above the `ECHO` payload
and below the `BIND` payload. -/
theorem transfer {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) {j₀ : Fin P.n}
    (hj₀ : j₀ ∉ (gatherTier s).F) (hcnt : P.f + 1 ≤ (dominators (networkOf s) j₀).card)
    {k : Fin P.n} (hk : k ∉ (gatherTier s).F) {U : AcceptedPairs P.n X}
    (hU : (bindBroadcasts s k).val = some U) :
    ∃ A, Message.echo A ∈ (gatherTier s).sent j₀ ∧ P.n - P.f ≤ A.card ∧ A ⊆ U := by
  obtain ⟨V, hVc, hVm⟩ :=
    hInv.bind_backed k hk U ((hInv.bindBroadcastVal_provenance k U hU).resolve_left hk)
  obtain ⟨q, hqK, hqV⟩ := InstanceState.exists_mem_inter_of_quorum hcnt hVc
  rw [dominators, Finset.mem_filter] at hqK
  obtain ⟨W, hWrecv, hWU⟩ := hVm q hqV
  obtain ⟨A, hA, hAW⟩ := mem_dominatedBy.mp hqK.2 W (hInv.received_subset_sent k q hWrecv)
  exact ⟨A, hA, hInv.echo_card j₀ hj₀ A (hInv.echo_confirmed j₀ hj₀ A hA),
    subset_trans hAW hWU⟩

open scoped Classical in
omit [DecidableEq X] in
/-- The core is the write-once `ECHO` payload of a sender outside `F` with at
least `f + 1` dominators, as soon as some process outside `F` holds a committed
`BIND` payload. -/
theorem core_witness {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherTier s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : (bindBroadcasts s k₀).val = some U₀) :
    ∃ j₁, j₁ ∉ (gatherTier s).F ∧ P.f + 1 ≤ (dominators (networkOf s) j₁).card ∧
      Message.echo (coreOfNetwork P (gatherTier s).2) ∈ (gatherTier s).sent j₁ ∧
      ((gatherTier s).process j₁).sentEcho = some (coreOfNetwork P (gatherTier s).2) := by
  have hF := hInv.F_card
  have hf := P.hResilience
  have hex : ∃ j, j ∈ correct (networkOf s) ∧ P.f + 1 ≤ (dominators (networkOf s) j).card := by
    obtain ⟨j₀, hj₀, hcnt⟩ := exists_dominators hInv
    exact ⟨j₀, hj₀, by omega⟩
  have hspec := hex.choose_spec
  have hj₁F : hex.choose ∉ (gatherTier s).F := mem_correct.mp hspec.1
  obtain ⟨A, hA, -, -⟩ := transfer hInv hj₁F hspec.2 hk₀ hU₀
  have hcore : coreOfNetwork P (gatherTier s).2 = A := by
    rw [← coreOf_networkOf, coreOf, dif_pos hex]
    exact echoOf_eq hInv hj₁F hA
  exact ⟨hex.choose, hj₁F, hspec.2, by rw [hcore]; exact hA,
    by rw [hcore]; exact hInv.echo_confirmed _ hj₁F A hA⟩

omit [DecidableEq X] in
/-- **The single core.** Once some process outside `F` holds a committed `BIND`
payload, the core has at least `n − f` entries and lies below the committed
`BIND` payload of every process outside `F`. -/
theorem single_core {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherTier s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : (bindBroadcasts s k₀).val = some U₀) :
    P.n - P.f ≤ (coreOfNetwork P (gatherTier s).2).card ∧
      ∀ k ∉ (gatherTier s).F, ∀ U : AcceptedPairs P.n X, (bindBroadcasts s k).val = some U →
        coreOfNetwork P (gatherTier s).2 ⊆ U := by
  obtain ⟨j₁, hj₁F, hcnt, hsent, hslot⟩ := core_witness hInv hk₀ hU₀
  refine ⟨hInv.echo_card j₁ hj₁F _ hslot, ?_⟩
  intro k hk U hU
  obtain ⟨A, hA, -, hAU⟩ := transfer hInv hj₁F hcnt hk hU
  have hEq : A = coreOfNetwork P (gatherTier s).2 := by
    have h1 := hInv.echo_confirmed j₁ hj₁F A hA
    rw [hslot] at h1
    exact (Option.some.inj h1).symm
  rw [← hEq]
  exact hAU

omit [DecidableEq X] in
/-- **The core is approved**: its entries are committed input entries, the
`ECHO` field it comes from carrying only such entries. -/
theorem single_core_approved {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherTier s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : (bindBroadcasts s k₀).val = some U₀) :
    approved s (coreOfNetwork P (gatherTier s).2) := by
  obtain ⟨j₁, -, -, -, hslot⟩ := core_witness hInv hk₀ hU₀
  exact hInv.echo_approved j₁ _ hslot

/-! ### The freeze certificate -/

open scoped Classical in
/-- The coordinates holding a committed `BIND` payload above `C`. The condition
is blind to `F`. -/
noncomputable def bindAbove (s : StateOverBroadcastSpecification P.n X) (C : AcceptedPairs P.n X) :
    Finset (Fin P.n) :=
  Finset.univ.filter (fun q => ∃ U, (bindBroadcasts s q).val = some U ∧ C ⊆ U)

open scoped Classical in
theorem mem_bindAbove {s : StateOverBroadcastSpecification P.n X} {C : AcceptedPairs P.n X} {q : Fin
  P.n} :
    q ∈ bindAbove s C ↔ ∃ U, (bindBroadcasts s q).val = some U ∧ C ⊆ U := by
  rw [bindAbove, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- A committed `BIND` payload is never rewritten. -/
theorem bindVal_mono {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hstep : StepOverBroadcastSpecification P s l
      μ) (hs' : s' ∈ μ.support)
    {q : Fin P.n} {U : AcceptedPairs P.n X} (h : (bindBroadcasts s q).val = some U) :
    (bindBroadcasts s' q).val = some U := by
  cases hstep with
  | commitBindEntry q' U' hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_setBindBroadcasts]
      by_cases hq : q = q'
      · subst hq; rw [hv] at h; exact absurd h (by simp)
      · rw [Function.update_of_ne hq]; exact h
  | bindCall j U' hin hvot hsnd happ hQ hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_setBindBroadcasts]
      by_cases hq : q = j
      · subst hq; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hq]; exact h
  | bindRet q' j U' hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_setBindBroadcasts]
      by_cases hq : q = q'
      · subst hq; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hq]; exact h
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_corruptAll]
      rw [BRB.corrupt_val]; exact h
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- **The certificate is monotone.** The coordinates holding a committed `BIND`
payload above `C` only accumulate, under every rule and every corruption. -/
theorem bindAbove_mono {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)} (hstep : StepOverBroadcastSpecification P s l
      μ) (hs' : s' ∈ μ.support)
    (C : AcceptedPairs P.n X) : bindAbove s C ⊆ bindAbove s' C := by
  intro q hq
  rw [mem_bindAbove] at hq ⊢
  obtain ⟨U, hU, hCU⟩ := hq
  exact ⟨U, bindVal_mono hstep hs' hU, hCU⟩

/-- **The freeze.** At a state where an `n − f` quorum of coordinates holds
committed `BIND` payloads, the core has at least `n − f` entries, its entries
are committed input entries, and at least `f + 1` coordinates hold a committed
`BIND` payload above it. The last is the certificate that holds the returns
after the first to this core: it is blind to `F` and monotone
(`bindAbove_mono`), and an `n − f` return quorum meets it. -/
theorem coreOf_recorded {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {Q : Finset (Fin P.n)} (hQc : P.n - P.f ≤ Q.card)
    (hQm : ∀ q ∈ Q, ∃ U : AcceptedPairs P.n X, (bindBroadcasts s q).val = some U) :
    P.n - P.f ≤ (coreOfNetwork P (gatherTier s).2).card ∧ approved s (coreOfNetwork P (gatherTier
      s).2) ∧
      P.f + 1 ≤ (bindAbove s (coreOfNetwork P (gatherTier s).2)).card := by
  classical
  have hF := hInv.F_card
  have hf := P.hResilience
  have hH : P.f + 1 ≤ (Q \ (gatherTier s).F).card := by
    have h1 := Finset.le_card_sdiff (gatherTier s).F Q
    omega
  obtain ⟨H, hHsub, hHcard⟩ := Finset.exists_subset_card_eq hH
  have hHQ : ∀ q ∈ H, q ∈ Q := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).1
  have hHF : ∀ q ∈ H, q ∉ (gatherTier s).F := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).2
  have hHne : H.Nonempty := by
    rw [← Finset.card_pos, hHcard]; omega
  obtain ⟨q₀, hq₀⟩ := hHne
  obtain ⟨U₀, hU₀⟩ := hQm q₀ (hHQ q₀ hq₀)
  obtain ⟨hcard, hsub⟩ := single_core hInv (hHF q₀ hq₀) hU₀
  refine ⟨hcard, single_core_approved hInv (hHF q₀ hq₀) hU₀, ?_⟩
  refine le_trans (le_of_eq hHcard.symm) (Finset.card_le_card fun q hq => ?_)
  obtain ⟨U, hU⟩ := hQm q (hHQ q hq)
  exact mem_bindAbove.mpr ⟨U, hU, hsub q (hHF q hq) U hU⟩


end Gather
end ABA
end PLTS
