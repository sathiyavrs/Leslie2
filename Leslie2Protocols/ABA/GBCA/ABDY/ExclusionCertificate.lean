/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Invariant

/-!
# The exclude certificates

An exclude certificate `ExclusionCertificate P s b` is receipt evidence that the bit `b` can never
gain grade-≥1 support: either the opposite bit owns the unique `n − f` `ECHO` receipt quorum
(`EchoReceiptQuorum P s (!b)`, Case A), or an `n − f` quorum of processes is each corrupted or
committed, write-once, to a `VOTE` payload other than `some b` (`VoteQuorumAgainst P s b`, Case B).
Both disjuncts make an `n − f` `VOTE b` receipt quorum — the only source of any grade-≥1
evidence for `b` — impossible forever: a `VOTE b` quorum against Case A yields a correct
double-`ECHO` sender (`echoReceiptQuorum_unique`, write-once `sentEcho`), and against Case B meets
the quorum only inside `F`, contradicting `2(n − f) > n + f` (`no_disjoint_quorums`).

A certificate is `F`-blind and receipt-monotone (`ExclusionCertificate.mono`), so it survives every
row of the implementation: a multicast (`exclusionCertificate_send`), a return
(`exclusionCertificate_ret`), and a write of the round's bound bit
(`exclusionCertificate_setBound`).

The derivation chains turn a return's own evidence into a certificate. `retGrade2`'s `ECHO5 v`
quorum and `retGrade1`'s `f + 1` `BIND v` receipts both route to an `n − f` `VOTE v` receipt
quorum at a correct process (`bind_receipts_of_echo5_quorum`, `voteQuorum_of_bind_receipts`),
which excludes `!v` — the quorum itself is a `VoteQuorumAgainst`
(`exclusionCertificate_of_voteQuorum`) — and certifies `v` alive
(`not_exclusionCertificate_of_voteQuorum`). The grade-0 return's `ECHO5 ⊥`
quorum yields a certificate for *some* bit (`exclusionCertificate_of_echo5Bot_quorum`): if a
correct bit-voter exists anywhere, its `vote_confirmed` receipt quorum is Case A for the opposite
bit; otherwise the correct vote prefix is all-⊥ and the `VoteQuorumAgainst` holds for both bits at
once (`exclusionCertificate_of_noCorrectVote`). `exclusionCertificate_boundOf_grade0` certifies the
complement of the bit a grade-0 return announces.

Two lemmas carry a Case A quorum between the `ECHO` level and its neighbours:
`echoReceiptQuorum_of_vote_receipts` reads one off `f + 1` `VOTE v` receipts, and
`inputQuorum_of_echoReceiptQuorum` refines one to an `n − f` `INPUT v` receipt quorum.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

variable {P : Parameters}

/-! ### The exclude certificates -/

/-- Case A carrier: some process holds an `n − f` `ECHO v` receipt quorum.
The certificate is `F`-blind and receipt-monotone, hence stable under `fail`
and under every implementation step, and at most one bit can carry it
(`echoReceiptQuorum_unique`). -/
def EchoReceiptQuorum (P : Parameters) (s : ImplementationState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.receivedCount i (.echo v)

/-- Derivation from `f + 1` `VOTE v` receipts: they contain a correct `VOTE v`
sender, whose `vote_confirmed` receipt quorum is the certificate. -/
theorem echoReceiptQuorum_of_vote_receipts {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.receivedCount i (.vote (some v))) :
    EchoReceiptQuorum P s v := by
  have hFc := hI.F_card
  have h' : s.F.card < s.receivedCount i (Message.vote (some v)) := by
    omega
  obtain ⟨k, hkF, hkr⟩ := ImplementationState.exists_sender_notMem s.F h'
  exact ⟨k, hI.vote_confirmed k v hkF (hI.received_subset_sent i k _ hkr)⟩

/-- The certificate refines to an `n − f` `INPUT v` receipt quorum. -/
theorem inputQuorum_of_echoReceiptQuorum {s : ImplementationState P.n} (hI : Invariant P s)
    {v : Bool} (h : EchoReceiptQuorum P s v) :
    ∃ m, P.n - P.f ≤ s.receivedCount m (.input v) := by
  obtain ⟨i, hi⟩ := h
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.receivedCount i (Message.echo v) := by
    omega
  obtain ⟨m, hmF, hmr⟩ := ImplementationState.exists_sender_notMem s.F h'
  exact ⟨m, hI.echo_confirmed m v hmF (hI.received_subset_sent i m _ hmr)⟩

/-- At most one bit carries an `n − f` `ECHO` quorum: the two quorums
intersect in a correct sender, and `sentEcho` is write-once. -/
theorem echoReceiptQuorum_unique {s : ImplementationState P.n} (hI : Invariant P s) {v v' : Bool}
    (h : EchoReceiptQuorum P s v) (h' : EchoReceiptQuorum P s v') : v = v' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨j, hjF, hj1, hj2⟩ :=
    ImplementationState.exists_correct_received_of_two_quorums hI.F_card hi hi'
  have e1 := hI.echo_once j v hjF (hI.received_subset_sent i j _ hj1)
  have e2 := hI.echo_once j v' hjF (hI.received_subset_sent i' j _ hj2)
  rw [e1] at e2
  exact Option.some.inj e2

/-- Case B carrier: an `n − f` quorum of processes each of which is corrupted or has committed its
write-once `VOTE` field to a payload other than `some b`. -/
def VoteQuorumAgainst (P : Parameters) (s : ImplementationState P.n) (b : Bool) : Prop :=
  P.n - P.f ≤ (Finset.univ.filter
    (fun j => j ∈ s.F ∨ ∃ w, (s.process j).sentVote = some w ∧ w ≠ some b)).card

/-- The exclude certificate licensing `b ∈ excluded` on the specification: either the opposite bit
owns the (unique) `n − f` `ECHO` receipt quorum, or a `VoteQuorumAgainst` blocks `b` at the `VOTE`
level. Both disjuncts make an `n − f` `VOTE b` receipt quorum — the only source of any grade-≥1
evidence for `b` — impossible forever. -/
def ExclusionCertificate (P : Parameters) (s : ImplementationState P.n) (b : Bool) : Prop :=
  EchoReceiptQuorum P s (!b) ∨ VoteQuorumAgainst P s b

/-- The counting core: two `n − f`-sized subsets of `Fin n` meeting only
inside `F` contradict `|F| ≤ f` and `3f < n` (`2(n − f) > n + f`). The same
arithmetic as `exists_correct_received_of_two_quorums`, exposed as a set statement because
`VoteQuorumAgainst` is a set of processes, not a receipt row. -/
theorem no_disjoint_quorums {Q D F : Finset (Fin P.n)}
    (hQ : P.n - P.f ≤ Q.card) (hD : P.n - P.f ≤ D.card)
    (hQD : Q ∩ D ⊆ F) (hF : F.card ≤ P.f) : False := by
  have hf := P.hResilience
  have hcard := Finset.card_union_add_card_inter Q D
  have hun : (Q ∪ D).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hint : (Q ∩ D).card ≤ F.card := Finset.card_le_card hQD
  omega

/-- **Certificate monotonicity**: receipts only grow, `sentVote` is
write-once, `F` only grows — so an exclusion certificate never expires. -/
theorem ExclusionCertificate.mono {s s' : ImplementationState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.received i j → m ∈ s'.received i j)
    (hvote : ∀ j w, (s.process j).sentVote = some w → (s'.process j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : ExclusionCertificate P s b → ExclusionCertificate P s' b := by
  rintro (⟨i, hi⟩ | hw)
  · refine Or.inl ⟨i, le_trans hi (Finset.card_le_card fun k hk => ?_)⟩
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hrecv i k _ hk.2⟩
  · refine Or.inr (le_trans hw (Finset.card_le_card fun k hk => ?_))
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    rcases hk.2 with hkF | ⟨w, hsv, hne⟩
    · exact Or.inl (hF hkF)
    · exact Or.inr ⟨w, hvote k w hsv, hne⟩

/-- `ExclusionCertificate` is stable under a correct send that respects the write-once
`sentVote` field. -/
theorem exclusionCertificate_send {s : ImplementationState P.n} {j : Fin P.n}
    {p : ProcessRecord} {m : Message}
    (hvote : ∀ w, (s.process j).sentVote = some w → p.sentVote = some w) {b : Bool}
    (h : ExclusionCertificate P s b) :
    ExclusionCertificate P ((s.setProcess j p).multicast j m) b :=
  ExclusionCertificate.mono (s := s) (fun _ _ _ hm => by simpa using hm)
    (fun k w hk => by
      by_cases hkj : k = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        exact hvote w hk
      · rw [process_send_ne hkj]
        exact hk)
    (Finset.Subset.refl _) h

/-- `ExclusionCertificate` is stable under a return (only `returned` flips). -/
theorem exclusionCertificate_ret {s : ImplementationState P.n} {id : Fin P.n} {b : Bool}
    (h : ExclusionCertificate P s b) :
    ExclusionCertificate P (s.setProcess id { s.process id with returned := true }) b :=
  ExclusionCertificate.mono (s := s) (fun _ _ _ hm => by simpa using hm)
    (fun k w hk => by
      by_cases hkj : k = id
      · subst hkj
        rw [ImplementationState.setProcess_process_self]
        exact hk
      · rw [ImplementationState.setProcess_process_ne _ _ _ hkj]
        exact hk)
    (Finset.Subset.refl _) h

/-- `ExclusionCertificate` is stable under the ghost write (no clause reads the bound
bit). -/
theorem exclusionCertificate_setBound {s : ImplementationState P.n} {b β : Bool}
    (h : ExclusionCertificate P s b) : ExclusionCertificate P (s.setBound β) b :=
  ExclusionCertificate.mono (s := s) (fun _ _ _ hm => hm) (fun _ _ hk => hk)
    (Finset.Subset.refl _) h

/-! ### The derivation chains -/

/-- `f + 1` `BIND v` receipts exceed the corruption budget, so they contain
a correct binder, whose `bind_confirmed` wait-condition is a correct `n − f`
`VOTE v` receipt quorum — the object the binding argument counts. -/
theorem voteQuorum_of_bind_receipts {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.receivedCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.receivedCount k (.vote (some v)) := by
  have hFc := hI.F_card
  have h' : s.F.card < s.receivedCount i (Message.bind (some v)) := by
    omega
  obtain ⟨k, hkF, hkr⟩ := ImplementationState.exists_sender_notMem s.F h'
  exact ⟨k, hkF, hI.bind_confirmed k v hkF (hI.received_subset_sent i k _ hkr)⟩

/-- An `n − f` `ECHO5 v` receipt quorum contains a correct `ECHO5` sender, whose
`echo5_confirmed` wait-condition is a correct `n − f` `BIND v` receipt quorum. -/
theorem bind_receipts_of_echo5_quorum {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.receivedCount i (.echo5 (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.receivedCount k (.bind (some v)) := by
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.receivedCount i (Message.echo5 (some v)) := by
    omega
  obtain ⟨k, hkF, hkr⟩ := ImplementationState.exists_sender_notMem s.F h'
  exact ⟨k, hkF, hI.echo5_confirmed k v hkF (hI.received_subset_sent i k _ hkr)⟩

/-- **Availability, the excluded bit**: any `n − f` `VOTE v` receipt quorum excludes the opposite
bit — the quorum's members are each corrupted or committed (write-once) to `some v`, so the quorum
itself is a `VoteQuorumAgainst` for `!v`. -/
theorem exclusionCertificate_of_voteQuorum {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.receivedCount i (.vote (some v))) :
    ExclusionCertificate P s (!v) := by
  refine Or.inr (le_trans h (Finset.card_le_card fun k hk => ?_))
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  by_cases hkF : k ∈ s.F
  · exact Or.inl hkF
  · refine Or.inr ⟨some v, hI.vote_once k (some v) hkF (hI.received_subset_sent i k _ hk.2), ?_⟩
    intro hc
    injection hc with hc
    cases v <;> simp at hc

/-- **Availability, the live bit**: an `n − f` `VOTE v` receipt quorum refutes both certificate
cases for `v` itself — against Case A the derived `ECHO v` quorum meets the `ECHO (!v)` quorum in a
correct double-echoer, and against Case B the quorum meets the quorum only inside `F`. -/
theorem not_exclusionCertificate_of_voteQuorum {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.receivedCount i (.vote (some v))) :
    ¬ ExclusionCertificate P s v := by
  have hfn := P.f_lt_n_sub_f
  rintro (hq | hw)
  · have hv : EchoReceiptQuorum P s v := echoReceiptQuorum_of_vote_receipts hI (i := i) (by omega)
    have hvv := echoReceiptQuorum_unique hI hv hq
    cases v <;> simp at hvv
  · refine no_disjoint_quorums (F := s.F) h hw ?_ hI.F_card
    intro k hk
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hk
    obtain ⟨⟨-, hrecv⟩, -, hd⟩ := hk
    rcases hd with hkF | ⟨w, hsv, hne⟩
    · exact hkF
    · by_contra hkF
      have hcommit := hI.vote_once k (some v) hkF (hI.received_subset_sent i k _ hrecv)
      rw [hsv] at hcommit
      exact hne (Option.some.inj hcommit)

/-- **Availability at the grade-0 return**: an `n − f` `ECHO5 ⊥` receipt quorum
certifies *some* excluded bit. Classical dichotomy on "a correct bit-voter
exists somewhere": if yes, its `vote_confirmed` receipt quorum is Case A for the
opposite bit; if no, the quorum's correct `ECHO5` sender holds `n − f` any-`BIND`
receipts, its correct `BIND` sender can only have sent `BIND ⊥` (a bit `BIND`
needs a correct bit-voter), and that sender's `bindBot_confirmed` receipts identify an
`n − f` set of processes each corrupted or committed to `VOTE ⊥` — a
`VoteQuorumAgainst` for both bits at once. -/
theorem exclusionCertificate_of_noCorrectVote {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.receivedCount i (.echo5 none))
    (hcase : ¬ ∃ (k : Fin P.n) (b : Bool), k ∉ s.F ∧ Message.vote (some b) ∈ s.sent k)
    (b : Bool) : ExclusionCertificate P s b := by
  classical
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  · have h1 : s.F.card < s.receivedCount i (Message.echo5 none) := by omega
    obtain ⟨p, hpF, hpr⟩ := ImplementationState.exists_sender_notMem s.F h1
    have hbc : P.n - P.f ≤ s.bindCount p :=
      hI.echo5Bot_confirmed p hpF (hI.received_subset_sent i p _ hpr)
    have h2 : s.F.card < s.bindCount p := by
      omega
    obtain ⟨k, w, hkF, hkr⟩ := ImplementationState.exists_bind_sender_notMem s.F h2
    have hksent := hI.received_subset_sent p k _ hkr
    have hw : w = none := by
      cases w with
      | none => rfl
      | some v' =>
        exfalso
        have hvq := hI.bind_confirmed k v' hkF hksent
        have h3 : s.F.card < s.receivedCount k (Message.vote (some v')) := by
          omega
        obtain ⟨m', hmF, hmr⟩ := ImplementationState.exists_sender_notMem s.F h3
        exact hcase ⟨m', v', hmF, hI.received_subset_sent k m' _ hmr⟩
    subst hw
    have hvc : P.n - P.f ≤ s.voteCount k := hI.bindBot_confirmed k hkF hksent
    refine Or.inr (le_trans hvc (Finset.card_le_card fun q hq => ?_))
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    obtain ⟨wv, hwv⟩ := hq.2
    by_cases hqF : q ∈ s.F
    · exact Or.inl hqF
    · have hqs := hI.received_subset_sent k q _ hwv
      have hnone : wv = none := by
        cases wv with
        | none => rfl
        | some v' => exact absurd ⟨q, v', hqF, hqs⟩ hcase
      subst hnone
      exact Or.inr ⟨none, hI.vote_once q none hqF hqs, by simp⟩

/-- **Availability at the grade-0 return**: an `n − f` `ECHO5 ⊥` receipt quorum certifies *some*
excluded bit. Classical dichotomy on "a correct bit-voter exists somewhere": if yes, its
`vote_confirmed` receipt quorum is Case A for the opposite bit; if no, the all-⊥ quorum of
`exclusionCertificate_of_noCorrectVote` answers. -/
theorem exclusionCertificate_of_echo5Bot_quorum {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.receivedCount i (.echo5 none)) :
    ∃ b, ExclusionCertificate P s b := by
  classical
  by_cases hcase : ∃ (k : Fin P.n) (b : Bool), k ∉ s.F ∧ Message.vote (some b) ∈ s.sent k
  · obtain ⟨k, b, hkF, hks⟩ := hcase
    refine ⟨!b, Or.inl ?_⟩
    rw [Bool.not_not]
    exact ⟨k, hI.vote_confirmed k b hkF hks⟩
  · exact ⟨false, exclusionCertificate_of_noCorrectVote hI h hcase false⟩

/-- **The grade-0 return's announced bit is certified.** At an `n − f` `ECHO5 ⊥` receipt quorum the
complement of `boundOf … C` carries an exclude certificate. Where a correct bit-voter exists its
`vote_confirmed` receipt quorum is Case A for the opposite bit, which is the bit `boundOf` names;
where none exists the quorum covers both bits at once. -/
theorem exclusionCertificate_boundOf_grade0 {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.receivedCount i (.echo5 none)) :
    ExclusionCertificate P s (!(boundOf s.sent s.F .grade0)) := by
  classical
  rw [boundOf_grade0]
  split_ifs with h1 h2
  · obtain ⟨k, hkF, hks⟩ := h1
    exact Or.inl ⟨k, hI.vote_confirmed k true hkF hks⟩
  · obtain ⟨k, hkF, hks⟩ := h2
    exact Or.inl ⟨k, hI.vote_confirmed k false hkF hks⟩
  · refine exclusionCertificate_of_noCorrectVote hI h (fun hc => ?_) _
    obtain ⟨k, b, hkF, hks⟩ := hc
    cases b
    · exact h2 ⟨k, hkF, hks⟩
    · exact h1 ⟨k, hkF, hks⟩

end GBCA.ByABDY
end ABA
end PLTS
