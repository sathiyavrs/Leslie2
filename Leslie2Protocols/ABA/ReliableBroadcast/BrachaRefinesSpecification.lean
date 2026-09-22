/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.BrachaComposition
import Leslie2Protocols.Framework.FamilySimulation

/-!
# The BRB refinement: Bracha's protocol implements Transition System 6

`BRB.brachaRefinesSpecification`: the reliable-broadcast instance `BRB.brachaInstance`
(`ABA/ReliableBroadcast/BrachaComposition.lean`) is forward simulated by the BRB specification
instance with the same leader, read over the instance's interface
(`BRB.specificationOverInstanceAlphabet`), along `BRB.SpecificationRelation`.

The refinement runs in two steps. The first is strong and functional: a transition of the instance
is one row of `BRB.BrachaStep` at the same state, at the specification label the interface label
projects to (`BRB.brachaInstance_step_row`). The second is the row-level matching
`specificationRelation_row`, whose answer is a weak run of the specification over `BRB.Label`; it is
lifted to the interface along a section of `BRB.specificationLabelMap`, which is where the call loop
is answered by the specification's own loop row.

The one piece of abstract information the specification tracks and the
implementation does not is the committed value `val`. The refinement supplies
it as a receipt-pattern certificate, in the exclusion-on-demand style of the GBCA
refinement: the specification's `commit` is fired inside the return run, at
the first return that needs it.

* `BRB.EchoCertificate s m` — some receiver holds an `ECHO m` receipt quorum, more
  than `(n + f) / 2` senders. F-blind (it counts receipts, not correctness) and
  monotone (receipts only accumulate), so it survives every rule and every
  corruption.
* At most one value is ever echo-certified (`echoCertificate_unique`): two `ECHO`
  receipt quorums share a correct sender, whose `sentEcho` field is
  write-once.
* Every return guard yields a certificate (`echoCertificate_of_vote_quorum`): a
  `2f + 1` `VOTE m` receipt quorum contains a correct voter, whose vote is
  backed — through the amplification chain, collapsed by the invariant clause
  `vote_backed` — by an `ECHO m` receipt quorum.
* A certificate identifies the correct leader's input
  (`input_of_echoCertificate`): an `ECHO` quorum contains a correct echoer, and an
  correct echo carries the leader's input — the invariant clause `echo_provenance`,
  which covers the three disjuncts of the `ECHO` guard.

The matching: internal rules stutter; `call` and `fail` are answered by their
specification rows; `ret id m` is answered by `ret` alone when `val` is
already committed (the certificates identify the values), and by the two-step
run `commit ; ret` (`weakLStep_tauThen`) when it is not — with `commit`'s
guard discharged by `input_of_echoCertificate` under a correct leader and by
membership in `F` otherwise.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-! ### The certificate -/

/-- `m` is echo-certified: some receiver holds an `ECHO m` receipt quorum.
F-blind and monotone — receipts only accumulate. -/
def EchoCertificate (P : Parameters) (s : BrachaState P.n M) (m : M) : Prop :=
  ∃ i, P.echoReceiptQuorum ≤ s.receivedCount i (.echo m)

@[simp] theorem echoCertificate_setProcess (s : BrachaState P.n M) (j : Fin P.n)
    (p : ProcessRecord M) (m : M) :
    EchoCertificate P (s.setProcess j p) m ↔ EchoCertificate P s m := by
  simp [EchoCertificate]

@[simp] theorem echoCertificate_multicast (s : BrachaState P.n M) (j : Fin P.n)
    (x : Message M) (m : M) :
    EchoCertificate P (s.multicast j x) m ↔ EchoCertificate P s m := by
  simp [EchoCertificate]

@[simp] theorem echoCertificate_corrupt (s : BrachaState P.n M) (id : Fin P.n) (m : M) :
    EchoCertificate P (s.corrupt P id) m ↔ EchoCertificate P s m := by
  simp [EchoCertificate]

/-- Deliveries preserve the certificate: counts only grow. -/
theorem EchoCertificate.receiveMessage {s : BrachaState P.n M} {m : M} (h : EchoCertificate P s m)
    (i j : Fin P.n) (x : Message M) : EchoCertificate P (s.receiveMessage i j x) m := by
  obtain ⟨i', hi'⟩ := h
  exact ⟨i', le_trans hi' (InstanceState.receivedCount_le_receiveMessage s i j x i' _)⟩

/-! ### The invariant -/

/-- The BRB implementation invariant. The `*_confirmed` clauses tie a correct
sender's sent to its write-once field; `echo_provenance` carries a correct echo back
to a correct leader's call record, and `vote_backed` ties a correct vote to the
receipts that justified it, with the amplification chain collapsed into
`EchoCertificate`. -/
structure Invariant (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M) : Prop where
  /-- The corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivered messages were multicast. -/
  received_subset_sent : ∀ i k, s.received i k ⊆ s.sent k
  /-- A correct leader's sent `INIT` carries its input. -/
  init_confirmed : ldr ∉ s.F → ∀ m, Message.init m ∈ s.sent ldr →
    (s.process ldr).input = some m
  /-- A correct sender's sent `ECHO` matches its write-once field. -/
  echo_confirmed : ∀ k ∉ s.F, ∀ m, Message.echo m ∈ s.sent k →
    (s.process k).sentEcho = some m
  /-- A correct echo of `m` carries the leader's input: under a correct leader,
  `m` is what the leader was called with. Each of the three disjuncts of the
  `ECHO` guard leads back to that call record. -/
  echo_provenance : ∀ k ∉ s.F, ∀ m, (s.process k).sentEcho = some m →
    ldr ∈ s.F ∨ (s.process ldr).input = some m
  /-- A correct sender's sent `VOTE` matches its write-once field. -/
  vote_confirmed : ∀ k ∉ s.F, ∀ m, Message.vote m ∈ s.sent k →
    (s.process k).sentVote = some m
  /-- A correct vote is backed by an `ECHO` receipt quorum somewhere: the
  quorum rule witnesses itself, and the amplification rule inherits the
  witness from a correct backer. -/
  vote_backed : ∀ k ∉ s.F, ∀ m, (s.process k).sentVote = some m → EchoCertificate P s m

/-- The invariant holds initially. -/
theorem Invariant.initial : Invariant P ldr (BrachaState.initial P.n M) := by
  refine ⟨by simp [BrachaState.initial], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [BrachaState.initial, ProcessRecord.initial]

/-- An `ECHO m` receipt quorum holds a correct echoer of `m`: the quorum
exceeds the corruption budget (`f < echoReceiptQuorum`), and a correct sender's sent
`ECHO` matches its write-once field. -/
theorem Invariant.correct_echoer {s : BrachaState P.n M} (hInv : Invariant P ldr s) {i : Fin P.n} {m
  : M}
    (hcnt : P.echoReceiptQuorum ≤ s.receivedCount i (.echo m)) :
    ∃ k, k ∉ s.F ∧ (s.process k).sentEcho = some m := by
  have hlt : s.F.card < s.receivedCount i (.echo m) :=
    lt_of_le_of_lt hInv.F_card (lt_of_lt_of_le P.f_lt_echoReceiptQuorum hcnt)
  obtain ⟨k, hkF, hkrecv⟩ := InstanceState.exists_sender_notMem s.F hlt
  exact ⟨k, hkF, hInv.echo_confirmed k hkF m (hInv.received_subset_sent i k hkrecv)⟩

/-- `f + 1` `VOTE m` receipts hold a correct voter for `m`: they exceed the
corruption budget, and a correct sender's sent `VOTE` matches its write-once
field. -/
theorem Invariant.correct_voter {s : BrachaState P.n M} (hInv : Invariant P ldr s) {i : Fin P.n} {m
  : M}
    (hcnt : P.f + 1 ≤ s.receivedCount i (.vote m)) :
    ∃ k, k ∉ s.F ∧ (s.process k).sentVote = some m := by
  have hlt : s.F.card < s.receivedCount i (.vote m) :=
    lt_of_lt_of_le (Nat.lt_succ_of_le hInv.F_card) hcnt
  obtain ⟨k, hkF, hkrecv⟩ := InstanceState.exists_sender_notMem s.F hlt
  exact ⟨k, hkF, hInv.vote_confirmed k hkF m (hInv.received_subset_sent i k hkrecv)⟩

/-- The invariant is preserved by every implementation step. -/
theorem Invariant.step {s : BrachaState P.n M} {l : Label P.n M} {μ : PMF (BrachaState P.n M)}
    (hInv : Invariant P ldr s) (hstep : BrachaStep P ldr s l μ)
    {s' : BrachaState P.n M} (hs' : s' ∈ μ.support) : Invariant P ldr s' := by
  cases hstep with
  | call m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hin := hInv.init_confirmed (by simpa using hldr) m' hold
        rw [h] at hin
        exact absurd hin (by simp)
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = ldr
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      by_cases hldr : ldr ∈ s.F
      · exact Or.inl (by simpa using hldr)
      · exfalso
        have hslot' : (s.process k).sentEcho = some m' := by
          by_cases hkl : k = ldr
          · subst hkl
            rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
            exact hslot
          · rw [InstanceState.multicast_process,
            InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
            exact hslot
        rcases hInv.echo_provenance k (by simpa using hk) m' hslot' with hldrF | hin
        · exact hldr hldrF
        · rw [h] at hin
          exact absurd hin (by simp)
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = ldr
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      by_cases hkl : k = ldr
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
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
      rw [InstanceState.receiveMessage_process]
      exact hInv.init_confirmed (by simpa using hldr) m' hmem
    · intro k hk m' hmem
      rw [InstanceState.receiveMessage_sent] at hmem
      rw [InstanceState.receiveMessage_process]
      exact hInv.echo_confirmed k (by simpa using hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.receiveMessage_process] at hslot
      rw [InstanceState.receiveMessage_process]
      simpa using hInv.echo_provenance k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [InstanceState.receiveMessage_sent] at hmem
      rw [InstanceState.receiveMessage_process]
      exact hInv.vote_confirmed k (by simpa using hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.receiveMessage_process] at hslot
      exact (hInv.vote_backed k (by simpa using hk) m' hslot).receiveMessage i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_confirmed (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
          rw [hkl] at hpre
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      suffices h : ldr ∈ s.F ∨ (s.process ldr).input = some m' by
        rcases h with h | h
        · exact Or.inl (by simpa using h)
        · refine Or.inr ?_
          by_cases hkl : ldr = j
          · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
            rw [hkl] at h
            exact h
          · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
            exact h
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
        obtain rfl : m = m' := by
          injection hslot
        by_cases hldr : ldr ∈ s.F
        · exact Or.inl hldr
        · rcases hrecv with hinit | hq | hv
          · exact Or.inr (hInv.init_confirmed hldr m (hInv.received_subset_sent _ ldr hinit))
          · obtain ⟨k', hk'F, hk'⟩ := hInv.correct_echoer hq
            exact hInv.echo_provenance k' hk'F m hk'
          · obtain ⟨k', hk'F, hk'⟩ := hInv.correct_voter hv
            obtain ⟨i, hi⟩ := hInv.vote_backed k' hk'F m hk'
            obtain ⟨k'', hk''F, hk''⟩ := hInv.correct_echoer hi
            exact hInv.echo_provenance k'' hk''F m hk''
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
        exact hInv.echo_provenance k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_confirmed (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
          rw [hkl] at hpre
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      have hslot' : (s.process k).sentEcho = some m' := by
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
          exact hslot
        · rw [InstanceState.multicast_process,
          InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
          exact hslot
      rcases hInv.echo_provenance k (by simpa using hk) m' hslot' with hldrF | hin
      · exact Or.inl (by simpa using hldrF)
      · refine Or.inr ?_
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
          rw [hkl] at hin
          exact hin
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hin
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
        obtain rfl : m = m' := by
          injection hslot
        exact ⟨k, hcnt⟩
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | voteAmplification j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [InstanceState.multicast_received, InstanceState.setProcess_received] at hx
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent]
      exact Or.inr (hInv.received_subset_sent i k hx)
    · intro hldr m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_confirmed (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
          rw [hkl] at hpre
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
          exact hpre
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      have hslot' : (s.process k).sentEcho = some m' := by
        by_cases hkl : k = j
        · subst hkl
          rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
          exact hslot
        · rw [InstanceState.multicast_process,
          InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
          exact hslot
      rcases hInv.echo_provenance k (by simpa using hk) m' hslot' with hldrF | hin
      · exact Or.inl (by simpa using hldrF)
      · refine Or.inr ?_
        by_cases hkl : ldr = j
        · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
          rw [hkl] at hin
          exact hin
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hin
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent, InstanceState.setProcess_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.vote_confirmed k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self] at hslot
        obtain rfl : m = m' := by
          injection hslot
        -- amplification: a correct backer supplies the certificate
        have hlt : s.F.card < s.receivedCount k (.vote m) :=
          lt_of_lt_of_le (Nat.lt_succ_of_le hInv.F_card) hcnt
        obtain ⟨k', hk'F, hk'recv⟩ := InstanceState.exists_sender_notMem s.F hlt
        have hk'sent := hInv.received_subset_sent k k' hk'recv
        have hk'field := hInv.vote_confirmed k' hk'F m hk'sent
        exact hInv.vote_backed k' hk'F m hk'field
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
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
      rw [InstanceState.multicast_process]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hldr)
      · exact hInv.init_confirmed (by simpa using hldr) m' hold
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent] at hmem
      rw [InstanceState.multicast_process]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hk)
      · exact hInv.echo_confirmed k (by simpa using hk) m' hold
    · intro k hk m' hslot
      rw [InstanceState.multicast_process] at hslot
      rw [InstanceState.multicast_process]
      simpa using hInv.echo_provenance k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [InstanceState.mem_multicast_sent] at hmem
      rw [InstanceState.multicast_process]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hk)
      · exact hInv.vote_confirmed k (by simpa using hk) m' hold
    · intro k hk m' hslot
      rw [InstanceState.multicast_process] at hslot
      rw [echoCertificate_multicast]
      exact hInv.vote_backed k (by simpa using hk) m' hslot
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [InstanceState.setProcess_received] at hx
      rw [InstanceState.setProcess_sent]
      exact hInv.received_subset_sent i k hx
    · intro hldr m' hmem
      rw [InstanceState.setProcess_sent] at hmem
      have hpre := hInv.init_confirmed (by simpa using hldr) m' hmem
      by_cases hkl : ldr = id
      · rw [hkl, InstanceState.setProcess_process_self]
        rw [hkl] at hpre
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hmem
      rw [InstanceState.setProcess_sent] at hmem
      have hpre := hInv.echo_confirmed k (by simpa using hk) m' hmem
      by_cases hkl : k = id
      · subst hkl
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hslot
      have hslot' : (s.process k).sentEcho = some m' := by
        by_cases hkl : k = id
        · subst hkl
          rw [InstanceState.setProcess_process_self] at hslot
          exact hslot
        · rw [InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
          exact hslot
      rcases hInv.echo_provenance k (by simpa using hk) m' hslot' with hldrF | hin
      · exact Or.inl (by simpa using hldrF)
      · refine Or.inr ?_
        by_cases hkl : ldr = id
        · rw [hkl, InstanceState.setProcess_process_self]
          rw [hkl] at hin
          exact hin
        · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hin
    · intro k hk m' hmem
      rw [InstanceState.setProcess_sent] at hmem
      have hpre := hInv.vote_confirmed k (by simpa using hk) m' hmem
      by_cases hkl : k = id
      · subst hkl
        rw [InstanceState.setProcess_process_self]
        exact hpre
      · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hslot
      rw [echoCertificate_setProcess]
      by_cases hkl : k = id
      · subst hkl
        rw [InstanceState.setProcess_process_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [InstanceState.setProcess_process_ne _ _ _ hkl] at hslot
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
      rw [InstanceState.corrupt_process]
      exact hInv.init_confirmed (hF ldr hldr) m' hmem
    · intro k hk m' hmem
      rw [InstanceState.corrupt_sent] at hmem
      rw [InstanceState.corrupt_process]
      exact hInv.echo_confirmed k (hF k hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.corrupt_process] at hslot
      rw [InstanceState.corrupt_process]
      rcases hInv.echo_provenance k (hF k hk) m' hslot with hldrF | hin
      · exact Or.inl (InstanceState.corrupt_F_subset s id hldrF)
      · exact Or.inr hin
    · intro k hk m' hmem
      rw [InstanceState.corrupt_sent] at hmem
      rw [InstanceState.corrupt_process]
      exact hInv.vote_confirmed k (hF k hk) m' hmem
    · intro k hk m' hslot
      rw [InstanceState.corrupt_process] at hslot
      rw [echoCertificate_corrupt]
      exact hInv.vote_backed k (hF k hk) m' hslot

/-! ### Deriving the certificate -/

/-- At most one value is ever echo-certified: two `ECHO` receipt quorums share
a correct sender, whose `sentEcho` field is write-once. -/
theorem echoCertificate_unique {s : BrachaState P.n M} (hInv : Invariant P ldr s) {m m' : M}
    (h : EchoCertificate P s m) (h' : EchoCertificate P s m') : m = m' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨k, hkF, hkm,
    hkm'⟩ := InstanceState.exists_correct_received₂_echoReceiptQuorum hInv.F_card hi hi'
  have h1 := hInv.echo_confirmed k hkF m (hInv.received_subset_sent i k hkm)
  have h2 := hInv.echo_confirmed k hkF m' (hInv.received_subset_sent i' k hkm')
  rw [h1] at h2
  injection h2

/-- Every `2f + 1` `VOTE m` receipt quorum yields the certificate: it contains
a correct voter, and correct votes are backed. -/
theorem echoCertificate_of_vote_quorum {s : BrachaState P.n M} (hInv : Invariant P ldr s)
    {i : Fin P.n} {m : M} (hcnt : 2 * P.f + 1 ≤ s.receivedCount i (.vote m)) :
    EchoCertificate P s m := by
  obtain ⟨k, hkF, hkslot⟩ := hInv.correct_voter (le_trans (by omega) hcnt)
  exact hInv.vote_backed k hkF m hkslot

/-- Under a correct leader, the certificate identifies the leader's input: the
`ECHO` quorum contains a correct echoer, whose echo carries the leader's
input. -/
theorem input_of_echoCertificate {s : BrachaState P.n M} (hInv : Invariant P ldr s)
    (hldr : ldr ∉ s.F) {m : M} (hc : EchoCertificate P s m) :
    (s.process ldr).input = some m := by
  obtain ⟨i, hi⟩ := hc
  obtain ⟨k, hkF, hkslot⟩ := hInv.correct_echoer hi
  rcases hInv.echo_provenance k hkF m hkslot with hldrF | hin
  · exact absurd hldrF hldr
  · exact hin

/-! ### The relation -/

/-- The BRB refinement relation. `val_certificate` bounds the specification's
committed value by the certificate; the other clauses are projections. -/
structure SpecificationRelation (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (t : SpecState P.n M) : Prop where
  /-- The implementation invariant. -/
  invariant : Invariant P ldr s
  /-- The call records agree. -/
  input_eq : t.input = (s.process ldr).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = (s.process id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- A committed value is echo-certified. -/
  val_certificate : ∀ m, t.val = some m → EchoCertificate P s m

/-- The relation holds initially. -/
theorem specificationRelation_init :
    SpecificationRelation P ldr (BrachaState.initial P.n M) (SpecState.initial P.n M) := by
  refine ⟨Invariant.initial, ?_, ?_, ?_, ?_⟩ <;>
    simp [BrachaState.initial, SpecState.initial, ProcessRecord.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both systems at once — the
abstract state the family lifting consumes. -/
theorem specificationRelation_corrupt {s : BrachaState P.n M} {t : SpecState P.n M}
    (hR : SpecificationRelation P ldr s t) (id : Fin P.n) :
    SpecificationRelation P ldr (s.corrupt P id) (t.corrupt P id) := by
  refine ⟨hR.invariant.step (BrachaStep.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · rw [corrupt_input, InstanceState.corrupt_process]
    exact hR.input_eq
  · intro k
    rw [corrupt_ret, InstanceState.corrupt_process]
    exact hR.ret_eq k
  · rw [SpecState.corrupt_F, InstanceState.corrupt_F, hR.F_eq]
  · intro m hm
    rw [corrupt_val] at hm
    rw [echoCertificate_corrupt]
    exact hR.val_certificate m hm

/-- **The relation across one row**: every row of `BrachaStep` at a related pair
is answered by a weak run of the specification instance, and the answer is
again related. Internal rows stutter; `call` and `fail` are answered by their
specification rows; `ret id m` is answered by `ret` alone when `val` is already
committed, and by the two-step run `commit ; ret` when it is not. -/
theorem specificationRelation_row (P : Parameters) (ldr : Fin P.n) (q₁ : BrachaState P.n M)
    (q₂ : SpecState P.n M) (hR : SpecificationRelation P ldr q₁ q₂) (l : Label P.n M)
    (μ : PMF (BrachaState P.n M)) (hstep : BrachaStep P ldr q₁ l μ)
    (q₁' : BrachaState P.n M) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l = Silent.τ ∧ (specInst P ldr M).weakLSilent q₂ q₂') ∨
      (¬ l = Silent.τ ∧ (specInst P ldr M).weakLStep q₂ l q₂')) ∧
      SpecificationRelation P ldr q₁' q₂' := by
  have hInv' := hR.invariant.step hstep hq₁'
  cases hstep with
  | call m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨{ q₂ with input := some m },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ m (by rw [hR.input_eq]; exact h))⟩, hInv', ?_, ?_, ?_, ?_⟩
    · simp
    · intro k
      by_cases hkl : k = ldr
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | callLoop m =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ m)⟩, hR⟩
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.receiveMessage_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.receiveMessage_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_certificate m' hm').receiveMessage i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteAmplification j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | byzantine j m hj =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.multicast_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.multicast_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast]
      exact hR.val_certificate m' hm'
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hcert : EchoCertificate P q₁ m := echoCertificate_of_vote_quorum hR.invariant hcnt
    have hretQ : q₂.ret id = false := by
      rw [hR.ret_eq id]; exact hr
    have hRel : ∀ t' : SpecState P.n M, t'.val = some m →
        t'.input = q₂.input → t'.F = q₂.F →
        t'.ret = q₂.ret →
        SpecificationRelation P ldr (q₁.setProcess id { q₁.process id with returned := true })
          { t' with ret := Function.update t'.ret id true } := by
      intro t' hval hinput hF hret
      refine ⟨hInv', ?_, ?_, ?_, ?_⟩
      · rw [hinput]
        by_cases hkl : ldr = id
        · rw [hkl, InstanceState.setProcess_process_self]
          rw [hR.input_eq, hkl]
        · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hR.input_eq
      · intro k
        by_cases hkl : k = id
        · subst hkl
          rw [InstanceState.setProcess_process_self]
          change Function.update t'.ret k true k = true
          rw [Function.update_self]
        · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
          change Function.update t'.ret id true k = _
          rw [Function.update_of_ne hkl, hret]
          exact hR.ret_eq k
      · rw [InstanceState.setProcess_F]
        rw [hF]
        exact hR.F_eq
      · intro m' hm'
        rw [echoCertificate_setProcess]
        obtain rfl : m = m' := by
          have := hval
          rw [show ({ t' with ret := Function.update t'.ret id true } :
            SpecState P.n M).val = t'.val from rfl] at hm'
          rw [hval] at hm'
          injection hm'
        exact hcert
    cases hval : q₂.val with
    | some m' =>
      obtain rfl : m = m' :=
        echoCertificate_unique hR.invariant hcert (hR.val_certificate m' hval)
      refine ⟨{ q₂ with ret := Function.update q₂.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.ret q₂ id m hval hretQ)⟩, ?_⟩
      exact hRel q₂ hval rfl rfl rfl
    | none =>
      have hcommit : (specInst P ldr M).LStep q₂ Silent.τ
          { q₂ with val := some m } := by
        refine Step.commit q₂ m hval ?_
        by_cases hldr : ldr ∈ q₁.F
        · exact Or.inl (by rw [hR.F_eq]; exact hldr)
        · exact Or.inr (by
            rw [hR.input_eq]
            exact input_of_echoCertificate hR.invariant hldr hcert)
      have hret : (specInst P ldr M).LStep { q₂ with val := some m }
          (.ret id m)
          { q₂ with val := some m, ret := Function.update q₂.ret id true } :=
        Step.ret _ id m rfl hretQ
      refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hcommit hret (by simp)⟩, ?_⟩
      exact hRel { q₂ with val := some m } rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.fail q₂ id)⟩, specificationRelation_corrupt hR id⟩

/-- **The BRB refinement**: the reliable-broadcast instance is forward
simulated by the specification instance with the same leader, read over the
instance's interface. A transition of the instance is one row of `BrachaStep`
(`BRB.brachaInstance_step_row`), the row is answered by a weak run of the specification
(`specificationRelation_row`), and that run is lifted to the interface along a section of
`specificationLabelMap` — which is where the call loop is answered by the specification's
own loop row. -/
theorem brachaRefinesSpecification (P : Parameters) (ldr : Fin P.n) :
    ForwardSimulation (brachaInstance P ldr M) (specificationOverInstanceAlphabet P ldr M)
      (SpecificationRelation
      P ldr) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := brachaInstance_step_row P ldr q₁ l μ hstep
  obtain ⟨s', hdis, hrel⟩ := specificationRelation_row P ldr q₁ q₂ hR l₀ μ hrow q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨specificationLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_specificationOverInstanceAlphabet P ldr hweak⟩
  · refine Or.inr ⟨?_, weakLStep_specificationOverInstanceAlphabet P ldr hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : specificationLabelMap P.n M (Silent.τ : InstanceLabel P.n M) = some l₀ := by
      rw [← hl]; exact hpull
    rw [specificationLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### Step-level relation transports

The relation across one row, exported for systems that replay the BRB rows
inside a larger rule table: internal rows under a specification stutter, the
call across the fused effects, and the on-demand commit that a derived
delivery licenses. -/

/-- The relation across any internal row, the specification stuttering. -/
theorem specificationRelation_tau {P : Parameters} {ldr : Fin P.n} {s s' : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t)
    (hstep : BrachaStep P ldr s Label.tau (PMF.pure s')) : SpecificationRelation P ldr s' t := by
  have hInv' := hR.invariant.step hstep (by rw [PMF.mem_support_pure_iff])
  generalize hμ : (PMF.pure s' : PMF (BrachaState P.n M)) = μ at hstep
  cases hstep with
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.receiveMessage_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.receiveMessage_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_certificate m' hm').receiveMessage i j m
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteAmplification j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | byzantine j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.multicast_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.multicast_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast]
      exact hR.val_certificate m' hm'

/-- An internal row leaves the corrupted set alone. -/
theorem brachaStep_tau_F {P : Parameters} {ldr : Fin P.n} {s s' : BrachaState P.n M}
    (hstep : BrachaStep P ldr s Label.tau (PMF.pure s')) : s'.F = s.F := by
  generalize hμ : (PMF.pure s' : PMF (BrachaState P.n M)) = μ at hstep
  cases hstep with
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    rfl
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | voteAmplification j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | byzantine j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp

/-- The relation across the leader's call, the specification calling too. -/
theorem specificationRelation_call {P : Parameters} {ldr : Fin P.n} {s : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t) {m : M}
    (h : (s.process ldr).input = none) :
    SpecificationRelation P ldr
      ((s.setProcess ldr { s.process ldr with input := some m }).multicast ldr (.init m))
      { t with input := some m } := by
  refine ⟨hR.invariant.step (BrachaStep.call s m h) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
  · intro k
    by_cases hkl : k = ldr
    · subst hkl
      rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
      exact hR.ret_eq k
    · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
      exact hR.ret_eq k
  · simpa using hR.F_eq
  · intro m' hm'
    rw [echoCertificate_multicast, echoCertificate_setProcess]
    exact hR.val_certificate m' hm'

/-- **The on-demand commit.** A `VOTE` receipt quorum licenses the
specification's committed value: either it is already this value, or the
`commit` guard holds towards it, the relation restored either way. -/
theorem commitReach {P : Parameters} {ldr : Fin P.n} {s : BrachaState P.n M}
    {t : SpecState P.n M} (hR : SpecificationRelation P ldr s t) {id : Fin P.n} {m : M}
    (hcnt : 2 * P.f + 1 ≤ s.receivedCount id (.vote m)) :
    (t.val = some m ∧ SpecificationRelation P ldr s t) ∨
    (t.val = none ∧ (ldr ∈ t.F ∨ t.input = some m) ∧
      SpecificationRelation P ldr s { t with val := some m }) := by
  have hcert : EchoCertificate P s m := echoCertificate_of_vote_quorum hR.invariant hcnt
  rcases hval : t.val with _ | m'
  · right
    have hcommit : ldr ∈ t.F ∨ t.input = some m := by
      by_cases hldr : ldr ∈ s.F
      · exact Or.inl (by rw [hR.F_eq]; exact hldr)
      · exact Or.inr (by
          rw [hR.input_eq]
          exact input_of_echoCertificate hR.invariant hldr hcert)
    refine ⟨rfl, hcommit, hR.invariant, ?_, hR.ret_eq, hR.F_eq, ?_⟩
    · dsimp only
      exact hR.input_eq
    · intro m'' hm''
      dsimp only at hm''
      obtain rfl : m = m'' := by
        injection hm''
      exact hcert
  · left
    obtain rfl : m' = m :=
      echoCertificate_unique hR.invariant (hR.val_certificate m' hval) hcert
    exact ⟨rfl, hR⟩

/-- info: 'PLTS.ABA.BRB.brachaRefinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaRefinesSpecification

end BRB
end ABA
end PLTS
