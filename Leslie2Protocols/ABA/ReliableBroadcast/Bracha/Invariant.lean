/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Algorithm
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.EchoWitness

/-!
# The invariant of the reliable-broadcast instance

`BRB.Invariant P ldr s` is what the reliable-broadcast instance with leader `ldr` maintains. The
`*_confirmed` clauses tie a correct sender's sent message to its write-once field,
`echo_of_leaderInput` carries a correct echo back to a correct leader's call record, and
`vote_backed`
ties a correct vote to the receipts that justified it, with the amplification chain collapsed into
`BRB.EchoWitness`. `Invariant.initial` holds it at the initial state, and `Invariant.step`
carries it across every transition of `BRB.BrachaAlgorithm`.

`Invariant.correct_echoer` and `Invariant.correct_voter` are the counting steps: a receipt quorum
of either level exceeds the corruption budget, so it holds a sender outside the corrupted set,
whose write-once field the invariant reads. Three consequences follow.

* At most one value is ever echo-certified (`echoWitness_unique`): two `ECHO` receipt quorums
  share a correct sender, whose `sentEcho` field is write-once.
* Every return guard yields a certificate (`echoWitness_of_vote_quorum`): a `2f + 1` `VOTE m`
  receipt quorum holds a correct voter, and a correct vote is backed.
* Under a correct leader a certificate identifies the leader's input
  (`input_of_echoWitness`): the `ECHO` quorum holds a correct echoer, and a correct echo
  carries the leader's input, which is `echo_of_leaderInput` over the three disjuncts of the `ECHO`
  guard.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-! ### The invariant -/

/-- The BRB implementation invariant. The `*_confirmed` clauses tie a correct
sender's sent to its write-once field; `echo_of_leaderInput` carries a correct echo back
to a correct leader's call record, and `vote_backed` ties a correct vote to the
receipts that justified it, with the amplification chain collapsed into
`EchoWitness`. -/
structure Invariant (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M) : Prop where
  /-- The corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivered messages were multicast. -/
  received_subset_sent : ∀ i k, s.received i k ⊆ s.sent k
  /-- A correct leader's sent `INIT` carries its input. -/
  init_confirmed : ldr ∉ s.F → ∀ m, Message.init m ∈ s.sent ldr →
    (s.processVariables ldr).input = some m
  /-- A correct sender's sent `ECHO` matches its write-once field. -/
  echo_confirmed : ∀ k ∉ s.F, ∀ m, Message.echo m ∈ s.sent k →
    (s.processVariables k).sentEcho = some m
  /-- A correct echo of `m` carries the leader's input: under a correct leader,
  `m` is what the leader was called with. Each of the three disjuncts of the
  `ECHO` guard leads back to that call record. -/
  echo_of_leaderInput : ∀ k ∉ s.F, ∀ m, (s.processVariables k).sentEcho = some m →
    ldr ∈ s.F ∨ (s.processVariables ldr).input = some m
  /-- A correct sender's sent `VOTE` matches its write-once field. -/
  vote_confirmed : ∀ k ∉ s.F, ∀ m, Message.vote m ∈ s.sent k →
    (s.processVariables k).sentVote = some m
  /-- A correct vote is backed by an `ECHO` receipt quorum somewhere: the vote on a quorum
  witnesses itself, and the amplified vote inherits the witness from a correct backer. -/
  vote_backed : ∀ k ∉ s.F, ∀ m, (s.processVariables k).sentVote = some m → EchoWitness P s m

/-- The invariant holds initially. -/
theorem Invariant.initial : Invariant P ldr (BrachaState.initial P.n M) := by
  refine ⟨by simp [BrachaState.initial], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [BrachaState.initial, ProcessVariables.initial]

/-- An `ECHO m` receipt quorum holds a correct echoer of `m`: the quorum
exceeds the corruption budget (`f < receivedEchoQuorum`), and a correct sender's sent
`ECHO` matches its write-once field. -/
theorem Invariant.correct_echoer {s : BrachaState P.n M} (hInv : Invariant P ldr s) {i : Fin P.n}
    {m : M} (hcnt : P.receivedEchoQuorum ≤ s.receivedCount i (.echo m)) :
    ∃ k, k ∉ s.F ∧ (s.processVariables k).sentEcho = some m := by
  have hlt : s.F.card < s.receivedCount i (.echo m) :=
    lt_of_le_of_lt hInv.F_card (lt_of_lt_of_le P.f_lt_receivedEchoQuorum hcnt)
  obtain ⟨k, hkF, hkrecv⟩ := InstanceState.exists_sender_notMem s.F hlt
  exact ⟨k, hkF, hInv.echo_confirmed k hkF m (hInv.received_subset_sent i k hkrecv)⟩

/-- `f + 1` `VOTE m` receipts hold a correct voter for `m`: they exceed the
corruption budget, and a correct sender's sent `VOTE` matches its write-once
field. -/
theorem Invariant.correct_voter {s : BrachaState P.n M} (hInv : Invariant P ldr s) {i : Fin P.n}
    {m : M} (hcnt : P.f + 1 ≤ s.receivedCount i (.vote m)) :
    ∃ k, k ∉ s.F ∧ (s.processVariables k).sentVote = some m := by
  have hlt : s.F.card < s.receivedCount i (.vote m) :=
    lt_of_lt_of_le (Nat.lt_succ_of_le hInv.F_card) hcnt
  obtain ⟨k, hkF, hkrecv⟩ := InstanceState.exists_sender_notMem s.F hlt
  exact ⟨k, hkF, hInv.vote_confirmed k hkF m (hInv.received_subset_sent i k hkrecv)⟩

/-- The invariant is preserved by every transition of the algorithm. -/
theorem Invariant.step {s : BrachaState P.n M} {l : Label P.n M} {μ : PMF (BrachaState P.n M)}
    (hInv : Invariant P ldr s) (hstep : BrachaAlgorithm P ldr s l μ)
    {s' : BrachaState P.n M} (hs' : s' ∈ μ.support) : Invariant P ldr s' := by
  cases hstep with
  | call m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hin := hInv.init_confirmed (by simpa using hldr) m' hold
        rw [h] at hin
        exact absurd hin (by simp)
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = ldr
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      by_cases hldr : ldr ∈ s.F
      · exact Or.inl (by simpa using hldr)
      · exfalso
        have hslot' : (s.processVariables k).sentEcho = some m' := by
          by_cases hkl : k = ldr
          · subst hkl
            rw [InstanceState.multicast_processVariables,
              InstanceState.setProcessVariables_processVariables_self] at hslot
            exact hslot
          · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
            exact hslot
        rcases hInv.echo_of_leaderInput k (by simpa using hk) m' hslot' with hldrF | hin
        · exact hldr hldrF
        · rw [h] at hin
          exact absurd hin (by simp)
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = ldr
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      by_cases hkl : k = ldr
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | callLoop m =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' k x hx
      rw [InstanceState.mem_receiveMessage_received] at hx
      rw [InstanceState.receiveMessage_sent]
      rcases hx with ⟨-, rfl, rfl⟩ | hold
      · exact h
      · exact hInv.received_subset_sent i' k hold
    · intro hldr m' hmem
      rw [InstanceState.receiveMessage_sent] at hmem
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.init_confirmed (by simpa using hldr) m' hmem
    · intro k hk m' hmem
      rw [InstanceState.receiveMessage_sent] at hmem
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.echo_confirmed k (by simpa using hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.receiveMessage_processVariables] at hslot
      rw [InstanceState.receiveMessage_processVariables]
      simpa using hInv.echo_of_leaderInput k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [InstanceState.receiveMessage_sent] at hmem
      rw [InstanceState.receiveMessage_processVariables]
      exact hInv.vote_confirmed k (by simpa using hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.receiveMessage_processVariables] at hslot
      exact (hInv.vote_backed k (by simpa using hk) m' hslot).receiveMessage i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_confirmed (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_processVariables, hkl,
            InstanceState.setProcessVariables_processVariables_self]
          rw [hkl] at hpre
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      suffices h : ldr ∈ s.F ∨ (s.processVariables ldr).input = some m' by
        rcases h with h | h
        · exact Or.inl (by simpa using h)
        · refine Or.inr ?_
          by_cases hkl : ldr = j
          · rw [InstanceState.multicast_processVariables, hkl,
              InstanceState.setProcessVariables_processVariables_self]
            rw [hkl] at h
            exact h
          · rw [InstanceState.multicast_processVariables,
              InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
            exact h
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hslot
        obtain rfl : m = m' := by
          injection hslot
        by_cases hldr : ldr ∈ s.F
        · exact Or.inl hldr
        · rcases hrecv with hinit | hq | hv
          · exact Or.inr (hInv.init_confirmed hldr m (hInv.received_subset_sent _ ldr hinit))
          · obtain ⟨k', hk'F, hk'⟩ := hInv.correct_echoer hq
            exact hInv.echo_of_leaderInput k' hk'F m hk'
          · obtain ⟨k', hk'F, hk'⟩ := hInv.correct_voter hv
            obtain ⟨i, hi⟩ := hInv.vote_backed k' hk'F m hk'
            obtain ⟨k'', hk''F, hk''⟩ := hInv.correct_echoer hi
            exact hInv.echo_of_leaderInput k'' hk''F m hk''
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
        exact hInv.echo_of_leaderInput k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_confirmed (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_processVariables, hkl,
            InstanceState.setProcessVariables_processVariables_self]
          rw [hkl] at hpre
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      have hslot' : (s.processVariables k).sentEcho = some m' := by
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self] at hslot
          exact hslot
        · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
          exact hslot
      rcases hInv.echo_of_leaderInput k (by simpa using hk) m' hslot' with hldrF | hin
      · exact Or.inl (by simpa using hldrF)
      · refine Or.inr ?_
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_processVariables, hkl,
            InstanceState.setProcessVariables_processVariables_self]
          rw [hkl] at hin
          exact hin
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hin
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hslot
        obtain rfl : m = m' := by
          injection hslot
        exact ⟨k, hcnt⟩
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | voteAmplification j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcessVariables_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_confirmed (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_processVariables, hkl,
            InstanceState.setProcessVariables_processVariables_self]
          rw [hkl] at hpre
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self]
          exact hpre
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      have hslot' : (s.processVariables k).sentEcho = some m' := by
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_self] at hslot
          exact hslot
        · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
          exact hslot
      rcases hInv.echo_of_leaderInput k (by simpa using hk) m' hslot' with hldrF | hin
      · exact Or.inl (by simpa using hldrF)
      · refine Or.inr ?_
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_processVariables, hkl,
            InstanceState.setProcessVariables_processVariables_self]
          rw [hkl] at hin
          exact hin
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hin
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcessVariables_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_processVariables,
            InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoWitness_multicast, echoWitness_setProcessVariables]
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self] at hslot
        obtain rfl : m = m' := by
          injection hslot
        -- amplification: a correct backer supplies the certificate
        have hlt : s.F.card < s.receivedCount k (.vote m) :=
          lt_of_lt_of_le (Nat.lt_succ_of_le hInv.F_card) hcnt
        obtain ⟨k', hk'F, hk'recv⟩ := InstanceState.exists_sender_notMem s.F hlt
        have hk'sent := hInv.received_subset_sent k k' hk'recv
        have hk'field := hInv.vote_confirmed k' hk'F m hk'sent
        exact hInv.vote_backed k' hk'F m hk'field
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | byzantine j m hj =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [InstanceState.multicast_received] at hx
      rw [InstanceState.mem_multicast_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent] at hmem
      rw [InstanceState.multicast_processVariables]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hldr)
      · exact hInv.init_confirmed (by simpa using hldr) m' hold
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent] at hmem
      rw [InstanceState.multicast_processVariables]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hk)
      · exact hInv.echo_confirmed k (by simpa using hk) m' hold
    · intro k hk m' hslot
      rw [InstanceState.multicast_processVariables] at hslot
      rw [InstanceState.multicast_processVariables]
      simpa using hInv.echo_of_leaderInput k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent] at hmem
      rw [InstanceState.multicast_processVariables]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hk)
      · exact hInv.vote_confirmed k (by simpa using hk) m' hold
    · intro k hk m' hslot
      rw [InstanceState.multicast_processVariables] at hslot
      rw [echoWitness_multicast]
      exact hInv.vote_backed k (by simpa using hk) m' hslot
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [InstanceState.setProcessVariables_received] at hx
      rw [InstanceState.setProcessVariables_sent]
      exact hInv.received_subset_sent i k hx
    · intro hldr m' hmem
      rw [InstanceState.setProcessVariables_sent] at hmem
      have hpre := hInv.init_confirmed (by simpa using hldr) m' hmem
      by_cases hkl : ldr = id
      · rw [hkl, InstanceState.setProcessVariables_processVariables_self]
        rw [hkl] at hpre
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hmem
      rw [InstanceState.setProcessVariables_sent] at hmem
      have hpre := hInv.echo_confirmed k (by simpa using hk) m' hmem
      by_cases hkl : k = id
      · subst hkl
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hslot
      have hslot' : (s.processVariables k).sentEcho = some m' := by
        by_cases hkl : k = id
        · subst hkl
          rw [InstanceState.setProcessVariables_processVariables_self] at hslot
          exact hslot
        · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
          exact hslot
      rcases hInv.echo_of_leaderInput k (by simpa using hk) m' hslot' with hldrF | hin
      · exact Or.inl (by simpa using hldrF)
      · refine Or.inr ?_
        by_cases hkl : ldr = id
        · rw [hkl, InstanceState.setProcessVariables_processVariables_self]
          rw [hkl] at hin
          exact hin
        · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
          exact hin
    · intro k hk m' hmem
      rw [InstanceState.setProcessVariables_sent] at hmem
      have hpre := hInv.vote_confirmed k (by simpa using hk) m' hmem
      by_cases hkl : k = id
      · subst hkl
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hpre
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hslot
      rw [echoWitness_setProcessVariables]
      by_cases hkl : k = id
      · subst hkl
        rw [InstanceState.setProcessVariables_processVariables_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hF : ∀ k, k ∉ (s.corrupt P id).F → k ∉ s.F := fun k hk hkF =>
      hk (InstanceState.corrupt_F_subset s id hkF)
    refine ⟨InstanceState.corrupt_card_le s id hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [InstanceState.corrupt_received] at hx
      rw [InstanceState.corrupt_sent]
      exact hInv.received_subset_sent i k hx
    · intro hldr m' hmem
      rw [InstanceState.corrupt_sent] at hmem
      rw [InstanceState.corrupt_processVariables]
      exact hInv.init_confirmed (hF ldr hldr) m' hmem
    · intro k hk m' hmem
      rw [InstanceState.corrupt_sent] at hmem
      rw [InstanceState.corrupt_processVariables]
      exact hInv.echo_confirmed k (hF k hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.corrupt_processVariables] at hslot
      rw [InstanceState.corrupt_processVariables]
      rcases hInv.echo_of_leaderInput k (hF k hk) m' hslot with hldrF | hin
      · exact Or.inl (InstanceState.corrupt_F_subset s id hldrF)
      · exact Or.inr hin
    · intro k hk m' hmem
      rw [InstanceState.corrupt_sent] at hmem
      rw [InstanceState.corrupt_processVariables]
      exact hInv.vote_confirmed k (hF k hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.corrupt_processVariables] at hslot
      rw [echoWitness_corrupt]
      exact hInv.vote_backed k (hF k hk) m' hslot

/-! ### Deriving the certificate -/

/-- At most one value is ever echo-certified: two `ECHO` receipt quorums share
a correct sender, whose `sentEcho` field is write-once. -/
theorem echoWitness_unique {s : BrachaState P.n M} (hInv : Invariant P ldr s) {m m' : M}
    (h : EchoWitness P s m) (h' : EchoWitness P s m') : m = m' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨k, hkF, hkm,
    hkm'⟩ := InstanceState.exists_correct_received_of_two_echoQuorums hInv.F_card hi hi'
  have h1 := hInv.echo_confirmed k hkF m (hInv.received_subset_sent i k hkm)
  have h2 := hInv.echo_confirmed k hkF m' (hInv.received_subset_sent i' k hkm')
  rw [h1] at h2
  injection h2

/-- Every `2f + 1` `VOTE m` receipt quorum yields the certificate: it contains
a correct voter, and correct votes are backed. -/
theorem echoWitness_of_vote_quorum {s : BrachaState P.n M} (hInv : Invariant P ldr s)
    {i : Fin P.n} {m : M} (hcnt : 2 * P.f + 1 ≤ s.receivedCount i (.vote m)) :
    EchoWitness P s m := by
  obtain ⟨k, hkF, hkslot⟩ := hInv.correct_voter (le_trans (by omega) hcnt)
  exact hInv.vote_backed k hkF m hkslot

/-- Under a correct leader, the certificate identifies the leader's input: the
`ECHO` quorum contains a correct echoer, whose echo carries the leader's
input. -/
theorem input_of_echoWitness {s : BrachaState P.n M} (hInv : Invariant P ldr s)
    (hldr : ldr ∉ s.F) {m : M} (hc : EchoWitness P s m) :
    (s.processVariables ldr).input = some m := by
  obtain ⟨i, hi⟩ := hc
  obtain ⟨k, hkF, hkslot⟩ := hInv.correct_echoer hi
  rcases hInv.echo_of_leaderInput k hkF m hkslot with hldrF | hin
  · exact absurd hldrF hldr
  · exact hin

end BRB
end ABA
end PLTS
