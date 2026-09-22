/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Implementation
import Leslie2Protocols.ABA.GBCA.SpecificationSafety
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2.Results

/-!
# The per-instance GBCA refinement

The round-`r` implementation instance (`GBCA.ByABDY.implementation`, ABDY22 Algorithm 6 —
all five message levels, D18) forward-simulates the round-`r` specification
instance (`GBCA.specInst`, the exclusion-set specification, D19):
`GBCA.ByABDY.refinesSpecification`.

Binding is stated on the labels of a trace (`GBCA.BindingTrace`), so the
soundness inclusion of that simulation carries it: `GBCA.ByABDY.implementation_refines` is
the inclusion and `GBCA.ByABDY.implementation_binding` is the specification's
`GBCA.specInst_binding` at the implementation instance.

The implementation state is the protocol's own data, so only `call`, `ret` and `F` are read off it
directly (`SpecificationRelation.call_eq`, `ret_eq`, `F_eq`). The specification's `excluded` and
`grade` are bookkeeping the protocol records nothing; the relation carries receipt evidence for them
instead:

* `exclusion_certificate` — every excluded bit `b` is covered by a monotone *exclude certificate*
  `ExclusionCertificate P s b`: either the opposite bit owns the unique `n − f` `ECHO` receipt
  quorum (`EchoReceiptQuorum P s (!b)`, Case A), or an `n − f` quorum of processes is each corrupted
  or committed, write-once, to a `VOTE` payload other than `some b` (`VoteQuorumAgainst P s b`, Case
  B). Both disjuncts make an `n − f` `VOTE b` receipt quorum — the only source of any grade-≥1
  evidence for `b` — impossible forever: a `VOTE b` quorum against Case A yields a correct
  double-`ECHO` sender (`echoReceiptQuorum_unique`, write-once `sentEcho`), and against Case B meets
  the quorum only inside `F`, contradicting `2(n − f) > n + f` (`no_disjoint_quorums`). The relation
  bounds `excluded` from above and never from below: which bits are actually excluded is recovered
  by case analysis at the return rows, not recorded.
* `grade2_evidence` / `grade0_evidence` — a grade-2 lock is backed by an `n − f`
  `ECHO5 v` receipt quorum, a grade-0 lock by an `n − f` `ECHO5 ⊥` quorum. Two
  opposing quorums intersect in a correct process that would have multicast
  two different `ECHO5` payloads, contradicting the write-once `echo5_once` —
  which is the grade-2 / grade-0 exclusivity the specification's grade guard demands
  (`grade_ne_false_of_echo5_quorum`, `grade_ne_true_of_echo5Bot_quorum`).
* `bound_excluded` — the round's bound bit and the specification's `excluded` determine each other:
  `excluded = excludedOf bound`, empty while the bit is unwritten and the singleton of its
  complement once a return has written it. This is the one clause that bounds `excluded` from below,
  and it holds because the exclusion fires with the round's first return. It supplies the guard
  `(!bnd) ∈ excluded` of a return that announces a bit already on record, and with
  `exclusion_certificate` it yields `SpecificationRelation.bound_certificate`: the bit on record
  carries an exclude certificate for its complement. A value-bearing return then announces its own
  value (`SpecificationRelation.retBound_eq`) — the return's `n − f` `VOTE v` receipt quorum refutes
  a certificate for `v` (`not_exclusionCertificate_of_voteQuorum`), so a bit on record is `v`, and a
  bit computed here is `v` by `boundOf`. A grade-0 return announces `boundOf`'s bit, whose
  complement is certified by `exclusionCertificate_boundOf_grade0`: a correct bit-voter's
  `vote_confirmed` receipt quorum is Case A for the opposite bit, and where there is no correct
  bit-voter the all-⊥ quorum (`exclusionCertificate_of_noCorrectVote`) certifies both bits at once.

The specification excludes a bit by the internal τ-transition `bindUnset`, so an
implementation return that needs a not-yet-excluded bit excluded is answered by a
two-step weak run (`weakLStep_tauThen`; `excludeThenRetGrade2_run`,
`excludeThenRetGrade1_run`, `excludeThenRetGrade0_run`). Every return row does the same
decidable case split on the specification's `excluded`, and the run fires
whenever the exclusion is missing. Each return's own evidence derives the
certificate: `retGrade2`'s `ECHO5 v` quorum and `retGrade1`'s `f + 1` `BIND v` receipts
both route to an `n − f` `VOTE v` receipt quorum at a correct process
(`bind_receipts_of_echo5_quorum`, `voteQuorum_of_bind_receipts`), which excludes
`!v` — the quorum itself is a `VoteQuorumAgainst` (`exclusionCertificate_of_voteQuorum`) — and
certifies `v` alive (`not_exclusionCertificate_of_voteQuorum`, which is what discharges
the guard pair `v ∉ excluded ∧ (!v) ∈ excluded` and with it value agreement between
successive returns). The grade-0 return's `ECHO5 ⊥` quorum yields a certificate
for *some* bit (`exclusionCertificate_of_echo5Bot_quorum`): if a correct bit-voter exists
anywhere, its `vote_confirmed` receipt quorum is Case A for the opposite bit; otherwise the correct
vote prefix is all-⊥ and the `VoteQuorumAgainst` holds for both
bits at once.

Both `bindUnset` guards come from one `ECHO` certificate (`bindUnset_guards`): refine it to an `n −
f` `INPUT v` receipt quorum (`inputQuorum_of_echoReceiptQuorum`), whose correct senders hold an
input (`input_called`, D8) — that is the quorum guard (`quorum_of_messageQuorum`) — and whose count
feeds `Invariant.support_of_input_receipts` for the `f + 1` InputSupport count (D15). At the grade-0
return the guards read the returner's own `|Valid| > 1` evidence instead
(`inputSupport_of_bothValid` closes both bits at once), so they are available whichever bit the
certificate names. `SpecificationRelation.callSupport` transports the counts to the specification
along `call_eq`/`F_eq`.

The invariant carries

* the corruption budget (`F_card`) and delivery soundness (`received_subset_sent`); * protocol
conformance of correct multicasts (`echo_confirmed`, `vote_input`,
  `vote_confirmed`, `bind_confirmed`, `bindBot_confirmed`, `echo5_input`, `echo5_confirmed`,
  `echo5Bot_confirmed`): each correct `ECHO`/`VOTE`/`BIND`/`ECHO5` is backed by the
  receipt evidence that Algorithm 6 demands (receipts only grow, so the
  historical evidence persists in the current state);
* write-once recording of correct multicasts (`echo_once`, `vote_once`,
  `bind_once`, `echo5_once`): a correct process's payload is the one held in the
  sender's write-once field, so a correct process speaks at most one payload
  per level — `echo_once` carries Case A, `vote_once` the `VoteQuorumAgainst`
  counting, `echo5_once` the grade exclusivity;
* participation (`input_called`, D8): a correct `INPUT` sender has been
  called;
* the *budget-robust* input-origin clause (`input_origin`): for **every**
  potential corruption superset `G ⊇ F` within the budget, an `INPUT b`
  multicast by a sender outside `G` traces back to a process outside `G`
  whose own input is `b`. The quantification over `G` is what makes the
  clause inductive: the classical "first correct sender of `INPUT b` is an
  originator" argument is temporal, but a relayer's `f + 1` receipt quorum
  always contains a sender outside `G`, so the pre-state clause — already
  quantified over the same `G` — supplies the witness, and corruption steps
  only shrink the range of `G`;
* the first-relayer support clause (`input_support`, D15): a correct
  `INPUT b` multicast is by a genuine holder of `b` or already certifies
  `f + 1` F-blind genuine-holder support (`InputSupport`) — inductive because
  the first correct relayer's `f + 1` `INPUT b` receipt senders are each in
  `F` or genuine holders, and the count is monotone under every step.

`Framework/FamilySimulation.lean` is imported for the downstream tree: the family
congruence `ForwardSimulation.family` reaches `ABA/Composition/GBCAInstanceByABDY.lean` and
`ABA/Composition/HybridAndSubstitution.lean` along this file, which also supplies the broadcast
ingredient that congruence consumes (`specificationRelation_corrupt`).
-/

set_option linter.style.longFile 2200

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

/-! ### The counting lemmas: any-payload monotonicity and derivation variants -/

/-- Deliveries only grow the any-payload `VOTE` count. -/
theorem ImplementationState.voteCount_le_receiveMessage {n : ℕ} (s : ImplementationState n)
    (i j : Fin n) (m : Message) (i' : Fin n) :
    s.voteCount i' ≤ (s.receiveMessage i j m).voteCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplementationState.mem_receiveMessage_received.mpr (Or.inr hv)⟩

/-- Deliveries only grow the any-payload `BIND` count. -/
theorem ImplementationState.bindCount_le_receiveMessage {n : ℕ} (s : ImplementationState n)
    (i j : Fin n) (m : Message) (i' : Fin n) :
    s.bindCount i' ≤ (s.receiveMessage i j m).bindCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplementationState.mem_receiveMessage_received.mpr (Or.inr hv)⟩

/-- Corruption is blind to the any-payload `VOTE` count. -/
theorem ImplementationState.corrupt_voteCount {P : Parameters} (s : ImplementationState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).voteCount i = s.voteCount i := by
  unfold ImplementationState.voteCount
  rw [ImplementationState.corrupt_received]

/-- Corruption is blind to the any-payload `BIND` count. -/
theorem ImplementationState.corrupt_bindCount {P : Parameters} (s : ImplementationState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).bindCount i = s.bindCount i := by
  unfold ImplementationState.bindCount
  rw [ImplementationState.corrupt_received]

/-- Any-payload analogue of `exists_sender_notMem` at the `BIND` level: a
`bindCount` exceeding `|G|` yields a sender outside `G` together with its
payload. -/
theorem ImplementationState.exists_bind_sender_notMem {P : Parameters} {s : ImplementationState P.n}
    (G : Finset (Fin P.n)) {i : Fin P.n} (h : G.card < s.bindCount i) :
    ∃ j w, j ∉ G ∧ Message.bind w ∈ s.received i j := by
  unfold ImplementationState.bindCount at h
  obtain ⟨j, hjQ, hjG⟩ := ImplementationState.exists_correct_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  obtain ⟨w, hw⟩ := hjQ.2
  exact ⟨j, w, hjG, hw⟩

/-! ### The concrete inductive invariant -/

variable {P : Parameters}

/-- `f + 1` F-blind genuine-holder support for `b` (D15): the implementation counterpart of the spec
guards' InputSupport counts — the specification count follows along `call_eq`/`F_eq`
(`SpecificationRelation.callSupport`). -/
def InputSupport (P : Parameters) (s : ImplementationState P.n) (b : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter
    (fun id => (s.process id).input = some b ∨ id ∈ s.F)).card

/-- The support count is monotone: it survives any step that preserves
genuine holders and grows `F`. -/
theorem InputSupport.mono {s s' : ImplementationState P.n} {b : Bool}
    (hproc : ∀ id, (s.process id).input = some b → (s'.process id).input = some b)
    (hF : s.F ⊆ s'.F) (h : InputSupport P s b) : InputSupport P s' b := by
  unfold InputSupport at h ⊢
  refine le_trans h (Finset.card_le_card fun id hid => ?_)
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hproc id) (fun hm => hF hm)⟩

/-- The inductive invariant of the GBCA implementation instance. See the
module docstring for the role of each clause. -/
structure Invariant (P : Parameters) (s : ImplementationState P.n) : Prop where
  /-- Corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivery soundness: everything delivered was multicast. -/
  received_subset_sent : ∀ i j m, m ∈ s.received i j → m ∈ s.sent j
  /-- Correct `ECHO b` is backed by an `n − f` `INPUT b` receipt quorum. -/
  echo_confirmed : ∀ j b, j ∉ s.F → Message.echo b ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.input b)
  /-- Correct `ECHO` multicasts are recorded in the write-once `sentEcho`
  field; in particular a correct process echoes at most one payload. -/
  echo_once : ∀ j b, j ∉ s.F → Message.echo b ∈ s.sent j →
    (s.process j).sentEcho = some b
  /-- Correct voters hold an input (D8). -/
  vote_input : ∀ j w, j ∉ s.F → Message.vote w ∈ s.sent j → (s.process j).input ≠ none
  /-- Correct `VOTE b` is backed by an `n − f` `ECHO b` receipt quorum. -/
  vote_confirmed : ∀ j b, j ∉ s.F → Message.vote (some b) ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.echo b)
  /-- Correct `VOTE` multicasts are recorded in the write-once `sentVote`
  field; this is the level the `VoteQuorumAgainst` certificate counts. -/
  vote_once : ∀ j w, j ∉ s.F → Message.vote w ∈ s.sent j →
    (s.process j).sentVote = some w
  /-- Correct `BIND` multicasts are recorded in the write-once `sentBind`
  field; in particular a correct process multicasts at most one payload. -/
  bind_once : ∀ j w, j ∉ s.F → Message.bind w ∈ s.sent j →
    (s.process j).sentBind = some w
  /-- Correct `BIND b` is backed by an `n − f` `VOTE b` receipt quorum. -/
  bind_confirmed : ∀ j b, j ∉ s.F → Message.bind (some b) ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.vote (some b))
  /-- Correct `BIND ⊥` is backed by `n − f` any-payload `VOTE` receipts. -/
  bindBot_confirmed : ∀ j, j ∉ s.F → Message.bind none ∈ s.sent j →
    P.n - P.f ≤ s.voteCount j
  /-- Correct `ECHO5` senders hold an input (D8, one level up). -/
  echo5_input : ∀ j w, j ∉ s.F → Message.echo5 w ∈ s.sent j → (s.process j).input ≠ none
  /-- Correct `ECHO5` multicasts are recorded in the write-once `sentEcho5` field; this is the level
  that carries the grade-2/grade-0 exclusivity. -/
  echo5_once : ∀ j w, j ∉ s.F → Message.echo5 w ∈ s.sent j →
    (s.process j).sentEcho5 = some w
  /-- Correct `ECHO5 b` is backed by an `n − f` `BIND b` receipt quorum. -/
  echo5_confirmed : ∀ j b, j ∉ s.F → Message.echo5 (some b) ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.bind (some b))
  /-- Correct `ECHO5 ⊥` is backed by `n − f` any-payload `BIND` receipts. -/
  echo5Bot_confirmed : ∀ j, j ∉ s.F → Message.echo5 none ∈ s.sent j →
    P.n - P.f ≤ s.bindCount j
  /-- Budget-robust input origin: for every corruption superset `G` within
  the budget, an `INPUT b` multicast outside `G` traces back to an input `b`
  outside `G`. -/
  input_origin : ∀ (b : Bool) (G : Finset (Fin P.n)), s.F ⊆ G → G.card ≤ P.f →
    ∀ j, j ∉ G → Message.input b ∈ s.sent j →
    ∃ m, m ∉ G ∧ (s.process m).input = some b
  /-- Relayer-inductivized first-relayer support (D15): a correct `INPUT b`
  multicast is by a genuine holder of `b`, or certifies the `f + 1` F-blind
  genuine-holder support outright — the first correct relayer's `f + 1`
  `INPUT b` receipt senders are each in `F` or genuine holders. -/
  input_support : ∀ (b : Bool) (j : Fin P.n), j ∉ s.F → Message.input b ∈ s.sent j →
    (s.process j).input = some b ∨ InputSupport P s b
  /-- Participation one level down (D8): a correct `INPUT` sender has been
  called. -/
  input_called : ∀ j b, j ∉ s.F → Message.input b ∈ s.sent j →
    (s.process j).input ≠ none

theorem Invariant.initial (P : Parameters) : Invariant P (ImplementationState.initial P.n) where
  F_card := by
    simp [ImplementationState.initial]
  received_subset_sent := fun i j m h => absurd h (by simp [ImplementationState.initial])
  echo_confirmed := fun j b _ h => absurd h (by simp [ImplementationState.initial])
  echo_once := fun j b _ h => absurd h (by simp [ImplementationState.initial])
  vote_input := fun j w _ h => absurd h (by simp [ImplementationState.initial])
  vote_confirmed := fun j b _ h => absurd h (by simp [ImplementationState.initial])
  vote_once := fun j w _ h => absurd h (by simp [ImplementationState.initial])
  bind_once := fun j w _ h => absurd h (by simp [ImplementationState.initial])
  bind_confirmed := fun j b _ h => absurd h (by simp [ImplementationState.initial])
  bindBot_confirmed := fun j _ h => absurd h (by simp [ImplementationState.initial])
  echo5_input := fun j w _ h => absurd h (by simp [ImplementationState.initial])
  echo5_once := fun j w _ h => absurd h (by simp [ImplementationState.initial])
  echo5_confirmed := fun j b _ h => absurd h (by simp [ImplementationState.initial])
  echo5Bot_confirmed := fun j _ h => absurd h (by simp [ImplementationState.initial])
  input_origin := fun b G _ _ j _ h => absurd h (by simp [ImplementationState.initial])
  input_support := fun b j _ h => absurd h (by simp [ImplementationState.initial])
  input_called := fun j b _ h => absurd h (by simp [ImplementationState.initial])

/-- Derivation (D15): any `f + 1` `INPUT b` receipt count yields the F-blind
genuine-holder support — some correct non-holder sender's `input_support` clause
closes, or else every sender is a holder-or-`F`-member and the senders
themselves witness the count. -/
theorem Invariant.support_of_input_receipts {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} {b : Bool} (h : P.f + 1 ≤ s.receivedCount i (.input b)) :
    InputSupport P s b := by
  by_cases hc : ∃ k, Message.input b ∈ s.received i k ∧ k ∉ s.F ∧ (s.process k).input ≠ some b
  · obtain ⟨k, hkr, hkF, hkin⟩ := hc
    rcases hI.input_support b k hkF (hI.received_subset_sent i k _ hkr) with h' | h'
    · exact absurd h' hkin
    · exact h'
  · push Not at hc
    unfold ImplementationState.receivedCount at h
    unfold InputSupport
    refine le_trans h (Finset.card_le_card fun k hk => ?_)
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    by_cases hkF : k ∈ s.F
    · exact Or.inr hkF
    · exact Or.inl (hc k hk.2 hkF)

/-- The sender's `setProcess` in a send step does not affect other processes. -/
private theorem process_send_ne {s : ImplementationState P.n} {j : Fin P.n} {p : ProcessRecord}
    {m : Message} {k : Fin P.n} (hk : k ≠ j) :
    ((s.setProcess j p).multicast j m).process k = s.process k := by
  rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_ne _ _ _ hk]

/-- **Invariant preservation, correct-send schema.** Process `j` updates its
local state to `p` and multicasts `m`. The hypotheses collect, clause by
clause, what the new message and the touched field must satisfy; every frame
condition is discharged here once for all nine send rules (`call`, `relay`,
`echo`, `voteBit`, `voteBot`, `bindBit`, `bindBot`, `echo5Bit`, `echo5Bot`). -/
private theorem Invariant.send {s : ImplementationState P.n} (hI : Invariant P s) {j : Fin P.n}
    {p : ProcessRecord} {m : Message}
    (hpne : p.input ≠ none)
    (hpmono : ∀ b, (s.process j).input = some b → p.input = some b)
    (hInp : ∀ b, m = .input b →
      p.input = some b ∨ P.f + 1 ≤ s.receivedCount j (.input b))
    (hEchoC : ∀ b, m = .echo b → P.n - P.f ≤ s.receivedCount j (.input b))
    (hVoteC : ∀ b, m = .vote (some b) → P.n - P.f ≤ s.receivedCount j (.echo b))
    (hBindC : ∀ b, m = .bind (some b) →
      P.n - P.f ≤ s.receivedCount j (.vote (some b)))
    (hBindBotC : m = .bind none → P.n - P.f ≤ s.voteCount j)
    (hEcho5C : ∀ b, m = .echo5 (some b) →
      P.n - P.f ≤ s.receivedCount j (.bind (some b)))
    (hEcho5BotC : m = .echo5 none → P.n - P.f ≤ s.bindCount j)
    (hEchoO : ((∀ b, m ≠ .echo b) ∧ p.sentEcho = (s.process j).sentEcho) ∨
      (∃ b, m = .echo b ∧ p.sentEcho = some b ∧ (s.process j).sentEcho = none))
    (hVoteO : ((∀ w, m ≠ .vote w) ∧ p.sentVote = (s.process j).sentVote) ∨
      (∃ w, m = .vote w ∧ p.sentVote = some w ∧ (s.process j).sentVote = none))
    (hBindO : ((∀ w, m ≠ .bind w) ∧ p.sentBind = (s.process j).sentBind) ∨
      (∃ w, m = .bind w ∧ p.sentBind = some w ∧ (s.process j).sentBind = none))
    (hEcho5O : ((∀ w, m ≠ .echo5 w) ∧ p.sentEcho5 = (s.process j).sentEcho5) ∨
      (∃ w, m = .echo5 w ∧ p.sentEcho5 = some w ∧ (s.process j).sentEcho5 = none)) :
    Invariant P ((s.setProcess j p).multicast j m) := by
  have htrans : ∀ (b : Bool) (k : Fin P.n), (s.process k).input = some b →
      (((s.setProcess j p).multicast j m).process k).input = some b := by
    intro b k hk
    by_cases hkj : k = j
    · subst hkj
      rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      exact hpmono b hk
    · rw [process_send_ne hkj]
      exact hk
  refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- received_subset_sent
    intro i' j' m' hm'
    rw [ImplementationState.multicast_received, ImplementationState.setProcess_received] at hm'
    exact ImplementationState.sent_subset_multicast _ _ _ _ (hI.received_subset_sent i' j' m' hm')
  · -- echo_conf
    intro j' b hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEchoC b heq.symm
    · simpa using hI.echo_confirmed j' b hF hold
  · -- echo_once
    intro j' b hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      rcases hEchoO with ⟨hne, _⟩ | ⟨b₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne b)
      · rw [hm0] at heq
        injection heq with hb
        rw [hpe, hb]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        have hbase := hI.echo_once j' b hF hold
        rcases hEchoO with ⟨_, hpe⟩ | ⟨b₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [process_send_ne hkj]
        exact hI.echo_once j' b hF hold
  · -- vote_input
    intro j' w hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        exact hpne
      · rw [process_send_ne hkj]
        exact hI.vote_input j' w hF hold
  · -- vote_conf
    intro j' b hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hVoteC b heq.symm
    · simpa using hI.vote_confirmed j' b hF hold
  · -- vote_once
    intro j' w hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      rcases hVoteO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        have hbase := hI.vote_once j' w hF hold
        rcases hVoteO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [process_send_ne hkj]
        exact hI.vote_once j' w hF hold
  · -- bind_once
    intro j' w hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      rcases hBindO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        have hbase := hI.bind_once j' w hF hold
        rcases hBindO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [process_send_ne hkj]
        exact hI.bind_once j' w hF hold
  · -- bind_conf
    intro j' b hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hBindC b heq.symm
    · simpa using hI.bind_confirmed j' b hF hold
  · -- bindBot_conf
    intro j' hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hBindBotC heq.symm
    · simpa using hI.bindBot_confirmed j' hF hold
  · -- echo5_input
    intro j' w hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        exact hpne
      · rw [process_send_ne hkj]
        exact hI.echo5_input j' w hF hold
  · -- echo5_once
    intro j' w hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      rcases hEcho5O with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        have hbase := hI.echo5_once j' w hF hold
        rcases hEcho5O with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [process_send_ne hkj]
        exact hI.echo5_once j' w hF hold
  · -- echo5_conf
    intro j' b hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEcho5C b heq.symm
    · simpa using hI.echo5_confirmed j' b hF hold
  · -- echo5Bot_conf
    intro j' hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEcho5BotC heq.symm
    · simpa using hI.echo5Bot_confirmed j' hF hold
  · -- input_origin
    intro b G hFG hGc j' hjG hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · refine ⟨j', hjG, ?_⟩
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        exact hp
      · have hcnt' : G.card < s.receivedCount j' (Message.input b) := by omega
        obtain ⟨k, hkG, hkr⟩ := ImplementationState.exists_sender_notMem G hcnt'
        obtain ⟨m0, hmG, hmi⟩ :=
          hI.input_origin b G hFG hGc k hkG (hI.received_subset_sent j' k _ hkr)
        exact ⟨m0, hmG, htrans b m0 hmi⟩
    · obtain ⟨m0, hmG, hmi⟩ := hI.input_origin b G hFG hGc j' hjG hold
      exact ⟨m0, hmG, htrans b m0 hmi⟩
  · -- input_supp
    intro b j' hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · left
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        exact hp
      · right
        exact InputSupport.mono (fun k hk => htrans b k hk) (fun _ hh => hh)
          (hI.support_of_input_receipts hcnt)
    · rcases hI.input_support b j' hF hold with hin | hsupp
      · left
        by_cases hkj : j' = j
        · subst hkj
          rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
          exact hpmono b hin
        · rw [process_send_ne hkj]
          exact hin
      · right
        exact InputSupport.mono (fun k hk => htrans b k hk) (fun _ hh => hh) hsupp
  · -- input_called
    intro j' b hF hm'
    rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplementationState.multicast_process, ImplementationState.setProcess_process_self]
        exact hpne
      · rw [process_send_ne hkj]
        exact hI.input_called j' b hF hold

/-- **Invariant preservation, local-frame schema.** A `setProcess` that keeps
the input and all four write-once fields (the return rules, which flip only
`returned`) preserves every clause. -/
private theorem Invariant.setProcess_unchanged {s : ImplementationState P.n} (hI : Invariant P s)
    {id : Fin P.n} {p : ProcessRecord}
    (h1 : p.input = (s.process id).input)
    (h2 : p.sentEcho = (s.process id).sentEcho)
    (h3 : p.sentVote = (s.process id).sentVote)
    (h4 : p.sentBind = (s.process id).sentBind)
    (h5 : p.sentEcho5 = (s.process id).sentEcho5) :
    Invariant P (s.setProcess id p) := by
  have hin : ∀ k, ((s.setProcess id p).process k).input = (s.process k).input := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplementationState.setProcess_process_self, h1]
    · rw [ImplementationState.setProcess_process_ne _ _ _ hk]
  have hech : ∀ k, ((s.setProcess id p).process k).sentEcho = (s.process k).sentEcho := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplementationState.setProcess_process_self, h2]
    · rw [ImplementationState.setProcess_process_ne _ _ _ hk]
  have hvot : ∀ k, ((s.setProcess id p).process k).sentVote = (s.process k).sentVote := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplementationState.setProcess_process_self, h3]
    · rw [ImplementationState.setProcess_process_ne _ _ _ hk]
  have hbin : ∀ k, ((s.setProcess id p).process k).sentBind = (s.process k).sentBind := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplementationState.setProcess_process_self, h4]
    · rw [ImplementationState.setProcess_process_ne _ _ _ hk]
  have hsea : ∀ k, ((s.setProcess id p).process k).sentEcho5 = (s.process k).sentEcho5 := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplementationState.setProcess_process_self, h5]
    · rw [ImplementationState.setProcess_process_ne _ _ _ hk]
  refine ⟨hI.F_card, by simpa using hI.received_subset_sent, by simpa using hI.echo_confirmed, ?_,
    ?_, by simpa using hI.vote_confirmed, ?_, ?_, by simpa using hI.bind_confirmed,
    by simpa using hI.bindBot_confirmed, ?_, ?_, by simpa using hI.echo5_confirmed,
    by simpa using hI.echo5Bot_confirmed, ?_, ?_, ?_⟩
  · intro j' b hF hm'
    rw [hech j']
    exact hI.echo_once j' b hF hm'
  · intro j' w hF hm'
    rw [hin j']
    exact hI.vote_input j' w hF hm'
  · intro j' w hF hm'
    rw [hvot j']
    exact hI.vote_once j' w hF hm'
  · intro j' w hF hm'
    rw [hbin j']
    exact hI.bind_once j' w hF hm'
  · intro j' w hF hm'
    rw [hin j']
    exact hI.echo5_input j' w hF hm'
  · intro j' w hF hm'
    rw [hsea j']
    exact hI.echo5_once j' w hF hm'
  · intro b G hFG hGc j' hjG hm'
    obtain ⟨m0, hmG, hmi⟩ := hI.input_origin b G hFG hGc j' hjG hm'
    exact ⟨m0, hmG, by rw [hin m0]; exact hmi⟩
  · intro b j' hF hm'
    rcases hI.input_support b j' hF hm' with hji | hsupp
    · left
      rw [hin j']
      exact hji
    · right
      exact InputSupport.mono (s := s) (fun k hk => by rw [hin k]; exact hk)
        (fun _ hh => hh) hsupp
  · intro j' b hF hm'
    rw [hin j']
    exact hI.input_called j' b hF hm'

/-- **Frame lemma for the bound bit.** The ghost write touches the network
state's own field alone, and no clause of `Invariant` reads it. -/
private theorem Invariant.setBound {s : ImplementationState P.n} (hI : Invariant P s) (β : Bool) :
    Invariant P (s.setBound β) := { hI with }

/-- **Invariant preservation.** `Invariant` is preserved by every implementation
step. -/
theorem Invariant.step {r : ℕ} {s : ImplementationState P.n} {l : Label P.n}
    {μ : PMF (ImplementationState P.n)} {s' : ImplementationState P.n} (hI : Invariant P s)
    (hstep : ImplementationStep P r s l μ) (hs' : s' ∈ μ.support) : Invariant P s' := by
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send (by simp) (fun b' hb' => absurd hb' (by rw [h]; simp))
      (fun b' heq => by injection heq with hb; subst hb; exact Or.inl rfl)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hI
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hI.F_card, ?_, ?_, by simpa using hI.echo_once,
      by simpa using hI.vote_input, ?_, by simpa using hI.vote_once,
      by simpa using hI.bind_once, ?_, ?_, by simpa using hI.echo5_input,
      by simpa using hI.echo5_once, ?_, ?_, by simpa using hI.input_origin,
      by simpa [InputSupport] using hI.input_support, by simpa using hI.input_called⟩
    · intro i' j' m' hm'
      rcases ImplementationState.mem_receiveMessage_received.mp hm' with ⟨rfl, rfl, rfl⟩ | hold
      · exact hsent
      · exact hI.received_subset_sent i' j' m' hold
    · intro j' b hF hm'
      exact le_trans (hI.echo_confirmed j' b hF hm')
        (ImplementationState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.vote_confirmed j' b hF hm')
        (ImplementationState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.bind_confirmed j' b hF hm')
        (ImplementationState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.bindBot_confirmed j' hF hm')
        (ImplementationState.voteCount_le_receiveMessage s i j m j')
    · intro j' b hF hm'
      exact le_trans (hI.echo5_confirmed j' b hF hm')
        (ImplementationState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.echo5Bot_confirmed j' hF hm')
        (ImplementationState.bindCount_le_receiveMessage s i j m j')
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb)
      (fun b' heq => by injection heq with hb; subst hb; exact Or.inr hcnt)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by injection heq with hb; subst hb; exact hcnt)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun heq => by simp at heq)
      (Or.inr ⟨b, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq)
      (fun b' heq => by
        injection heq with hw; injection hw with hb; subst hb; exact hcnt)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inr ⟨some b, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | voteBot j hin _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inr ⟨none, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | bindBit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by
        injection heq with hw; injection hw with hb; subst hb; exact hcnt)
      (fun heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨some b, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | bindBot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun _ => hcnt)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨none, rfl, rfl, hsend⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
  | echo5Bit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by
        injection heq with hw; injection hw with hb; subst hb; exact hcnt)
      (fun heq => by simp at heq)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨some b, rfl, rfl, hsend⟩)
  | echo5Bot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine hI.send hin (fun _ hb => hb) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun b' heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun heq => by simp at heq)
      (fun b' heq => by simp at heq) (fun _ => hcnt)
      (Or.inl ⟨fun b' heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inl ⟨fun w heq => by simp at heq, rfl⟩)
      (Or.inr ⟨none, rfl, rfl, hsend⟩)
  | byzantine j m hjF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsentG : ∀ (G : Finset (Fin P.n)), s.F ⊆ G → ∀ j' m', j' ∉ G →
        m' ∈ (s.multicast j m).sent j' → m' ∈ s.sent j' := by
      intro G hFG j' m' hjG hm'
      rcases ImplementationState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
      · exact absurd (hFG hjF) hjG
      · exact hold
    have hs := fun j' m' (hF : j' ∉ s.F) =>
      hsentG s.F (Finset.Subset.refl _) j' m' hF
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplementationState.sent_subset_multicast _ _ _ _ (hI.received_subset_sent i' j' m' hm')
    · exact fun j' b hF hm' => hI.echo_confirmed j' b hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.echo_once j' b hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.vote_input j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.vote_confirmed j' b hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.vote_once j' w hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.bind_once j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.bind_confirmed j' b hF (hs j' _ hF hm')
    · exact fun j' hF hm' => hI.bindBot_confirmed j' hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.echo5_input j' w hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.echo5_once j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.echo5_confirmed j' b hF (hs j' _ hF hm')
    · exact fun j' hF hm' => hI.echo5Bot_confirmed j' hF (hs j' _ hF hm')
    · exact fun b G hFG hGc j' hjG hm' =>
        hI.input_origin b G hFG hGc j' hjG (hsentG G hFG j' _ hjG hm')
    · exact fun b j' hF hm' => hI.input_support b j' hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.input_called j' b hF (hs j' _ hF hm')
  | retGrade2 id v bnd _hin _hlv hcnt hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Invariant.setBound ?_ bnd
    exact hI.setProcess_unchanged rfl rfl rfl rfl rfl
  | retGrade1 id v bnd _hin _hlv _hnotGrade2 hcnt honce hbind hval hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Invariant.setBound ?_ bnd
    exact hI.setProcess_unchanged rfl rfl rfl rfl rfl
  | retGrade0 id bnd _hin _hlv _hnotGrade2 _hnotGrade1 hcnt hval hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Invariant.setBound ?_ bnd
    exact hI.setProcess_unchanged rfl rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsub := ImplementationState.corrupt_F_subset s id
    have hFtr : ∀ j' : Fin P.n, j' ∉ (s.corrupt P id).F → j' ∉ s.F :=
      fun j' hF hj => hF (hsub hj)
    refine ⟨ImplementationState.corrupt_card_le s id hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      rw [ImplementationState.corrupt_received] at hm'
      rw [ImplementationState.corrupt_sent]
      exact hI.received_subset_sent i' j' m' hm'
    · intro j' b hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_receivedCount]
      exact hI.echo_confirmed j' b (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.echo_once j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.vote_input j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_receivedCount]
      exact hI.vote_confirmed j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.vote_once j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.bind_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_receivedCount]
      exact hI.bind_confirmed j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_voteCount]
      exact hI.bindBot_confirmed j' (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.echo5_input j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.echo5_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_receivedCount]
      exact hI.echo5_confirmed j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_bindCount]
      exact hI.echo5Bot_confirmed j' (hFtr j' hF) hm'
    · intro b G hFG hGc j' hjG hm'
      rw [ImplementationState.corrupt_sent] at hm'
      obtain ⟨m0, hmG, hmi⟩ :=
        hI.input_origin b G (Finset.Subset.trans hsub hFG) hGc j' hjG hm'
      exact ⟨m0, hmG, by rw [ImplementationState.corrupt_process]; exact hmi⟩
    · intro b j' hF' hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rcases hI.input_support b j' (hFtr j' hF') hm' with hin | hsupp
      · left
        rw [ImplementationState.corrupt_process]
        exact hin
      · right
        refine InputSupport.mono (s := s) (fun k hk => ?_) hsub hsupp
        rw [ImplementationState.corrupt_process]
        exact hk
    · intro j' b hF hm'
      rw [ImplementationState.corrupt_sent] at hm'
      rw [ImplementationState.corrupt_process]
      exact hI.input_called j' b (hFtr j' hF) hm'

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
private theorem exclusionCertificate_send {s : ImplementationState P.n} {j : Fin P.n}
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
private theorem exclusionCertificate_ret {s : ImplementationState P.n} {id : Fin P.n} {b : Bool}
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
private theorem exclusionCertificate_setBound {s : ImplementationState P.n} {b β : Bool}
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

/-! ### The simulation relation -/

/-- The exclusion set the specification holds against a bound bit: empty while
the bit is unwritten, and the singleton of its complement once it is written. -/
def excludedOf : Option Bool → Finset Bool
  | none => ∅
  | some β => {!β}

@[simp] theorem excludedOf_none : excludedOf none = (∅ : Finset Bool) := rfl

@[simp] theorem excludedOf_some (β : Bool) : excludedOf (some β) = {!β} := rfl

/-- The simulation relation: the concrete invariant, the abstraction map for
the fields the protocol itself holds (spec `call` = concrete input, spec
`ret` = concrete return flags, spec `F` = concrete `F`), and receipt evidence
for the two fields it does not. `exclusion_certificate` bounds `excluded` from above — an exclusion
certificate for every excluded bit — and never from below. -/
structure SpecificationRelation (P : Parameters) (s : ImplementationState P.n) (t : SpecState P.n) :
  Prop where
  /-- The concrete inductive invariant. -/
  invariant : Invariant P s
  /-- Spec inputs are the concrete inputs. -/
  call_eq : ∀ id, t.call id = (s.process id).input
  /-- Spec return flags are the concrete return flags. -/
  ret_eq : ∀ id, t.ret id = (s.process id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- Every excluded bit carries a monotone exclude certificate. -/
  exclusion_certificate : ∀ b, b ∈ t.excluded → ExclusionCertificate P s b
  /-- A grade-2 lock is backed by an `n − f` `ECHO5 v` receipt quorum
  for some bit `v`. -/
  grade2_evidence : t.grade = some true →
    ∃ v i, P.n - P.f ≤ s.receivedCount i (.echo5 (some v))
  /-- A grade-0 lock is backed by an `n − f` `ECHO5 ⊥` receipt
  quorum. -/
  grade0_evidence : t.grade = some false →
    ∃ i, P.n - P.f ≤ s.receivedCount i (.echo5 none)
  /-- The round's bound bit determines the exclusion set: nothing is excluded
  while the bit is unwritten, and the complement of the bit is the one excluded
  bit once a return has written it. The exclusion fires with the round's first
  return, so the two records move together. -/
  bound_excluded : t.excluded = excludedOf s.bound

/-- The simulation relation of the round-`r` instance (the round index is
phantom: every round runs the same protocol). -/
def specificationRelation (P : Parameters) (_r : ℕ) (s : ImplementationState P.n)
    (t : SpecState P.n) : Prop :=
  SpecificationRelation P s t

/-- The initial states are related. -/
theorem specificationRelation_init (P : Parameters) (r : ℕ) :
    specificationRelation P r (implementation P r).init (specInst P r).init where
  invariant := Invariant.initial P
  call_eq := fun _ => rfl
  ret_eq := fun _ => rfl
  F_eq := rfl
  exclusion_certificate := fun b hb => absurd hb (Finset.notMem_empty b)
  grade2_evidence := fun h => absurd h (by simp [SpecState.initial])
  grade0_evidence := fun h => absurd h (by simp [SpecState.initial])
  bound_excluded := rfl

/-- The bound bit on record carries an exclude certificate for its complement:
the specification has excluded that complement, and every excluded bit is
certified. -/
theorem SpecificationRelation.bound_certificate {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) (β : Bool) (hb : s.bound = some β) :
    ExclusionCertificate P s (!β) := by
  refine hR.exclusion_certificate (!β) ?_
  rw [hR.bound_excluded, hb, excludedOf_some]
  exact Finset.mem_singleton_self _

/-- **The announced bit of a value-bearing return.** A return of `v` carries an
`n − f` `VOTE v` receipt quorum, which refutes an exclude certificate for `v`; so a bound bit
already on record, whose complement is certified, is `v` itself,
and one computed here is `v` by `boundOf`. -/
theorem SpecificationRelation.retBound_eq {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {i : Fin P.n} {v : Bool} {out : GBCAOutput}
    (hvq : P.n - P.f ≤ s.receivedCount i (.vote (some v)))
    (hout : boundOf s.sent s.F out = v) :
    s.bound.getD (boundOf s.sent s.F out) = v := by
  cases hb : s.bound with
  | none => exact hout
  | some β =>
    refine Option.getD_some.trans ?_
    by_contra hne
    refine not_exclusionCertificate_of_voteQuorum hR.invariant hvq ?_
    have hv : (!β) = v := by
      cases β <;> cases v <;> simp_all
    rw [← hv]
    exact hR.bound_certificate β hb

/-! ### Deriving the spec guards -/

/-- D15 derivation at `retGrade1`/`retGrade0`: `|Valid| > 1` evidence yields the
`f + 1` F-blind genuine-holder support for either bit — its `n − f ≥ f + 1`
`INPUT` receipt quorum for that bit sits at the returner itself. -/
theorem inputSupport_of_bothValid {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} (hv : s.bothValid P i) (b : Bool) : InputSupport P s b := by
  have hfn := P.f_lt_n_sub_f
  exact hI.support_of_input_receipts
    (le_trans (by omega) (ImplementationState.bothValid_le hv b))

/-- Transport an implementation support count to the specification along `call_eq`/`F_eq`: the spec
guards' InputSupport counts (D15). -/
theorem SpecificationRelation.callSupport {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {b : Bool} (h : InputSupport P s b) :
    P.f + 1 ≤ (Finset.univ.filter (fun id => t.call id = some b ∨ id ∈ t.F)).card := by
  unfold InputSupport at h
  refine le_trans h (Finset.card_le_card fun k hk => ?_)
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  rw [hR.call_eq, hR.F_eq]
  exact hk.2

/-- D8 quorum derivation: any `n − f` receipt quorum of a message whose correct
senders must hold an input yields the spec's call quorum; corrupted senders
are absorbed into the `∪ F`. -/
theorem quorum_of_messageQuorum {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {i : Fin P.n} {m : Message}
    (hpart : ∀ j, j ∉ s.F → m ∈ s.sent j → (s.process j).input ≠ none)
    (h : P.n - P.f ≤ s.receivedCount i m) : t.quorum P := by
  unfold SpecState.quorum
  unfold ImplementationState.receivedCount at h
  refine le_trans h (Finset.card_le_card ?_)
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [Finset.mem_union]
  by_cases hkF : k ∈ t.F
  · exact Or.inr hkF
  · refine Or.inl ?_
    rw [Finset.mem_filter]
    have hkF' : k ∉ s.F := by
      rwa [hR.F_eq] at hkF
    refine ⟨Finset.mem_univ _, hkF, ?_⟩
    rw [hR.call_eq]
    exact hpart k hkF' (hR.invariant.received_subset_sent i k _ hk.2)

/-- **Both `bindUnset` guards from the single certificate.** -/
theorem bindUnset_guards {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {v : Bool} (hq : EchoReceiptQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter (fun id => t.call id = some v ∨ id ∈ t.F)).card := by
  obtain ⟨m, hm⟩ := inputQuorum_of_echoReceiptQuorum hR.invariant hq
  have hfn := P.f_lt_n_sub_f
  refine ⟨quorum_of_messageQuorum hR
    (fun j hj hm' => hR.invariant.input_called j v hj hm') hm, ?_⟩
  exact hR.callSupport (hR.invariant.support_of_input_receipts (le_trans (by omega) hm))

/-- Grade exclusivity, grade 2: an `n − f` `ECHO5 v` receipt quorum rules out a grade-0 lock (the
two `ECHO5` quorums would intersect in a correct process with two different `ECHO5` payloads,
against `echo5_once`). -/
theorem grade_ne_false_of_echo5_quorum {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 (some v))) :
    t.grade ≠ some false := by
  intro hg
  obtain ⟨i', hc⟩ := hR.grade0_evidence hg
  obtain ⟨j, hjF, hj1,
    hj2⟩ := ImplementationState.exists_correct_received_of_two_quorums hR.invariant.F_card hcnt hc
  have e1 := hR.invariant.echo5_once j (some v) hjF (hR.invariant.received_subset_sent id j _ hj1)
  have e2 := hR.invariant.echo5_once j none hjF (hR.invariant.received_subset_sent i' j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-- Grade exclusivity, grade 0: an `n − f` `ECHO5 ⊥` receipt quorum rules out a grade-2 lock. -/
theorem grade_ne_true_of_echo5Bot_quorum {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 none)) :
    t.grade ≠ some true := by
  intro hg
  obtain ⟨v', i', hc⟩ := hR.grade2_evidence hg
  obtain ⟨j, hjF, hj1,
    hj2⟩ := ImplementationState.exists_correct_received_of_two_quorums hR.invariant.F_card hc hcnt
  have e1 := hR.invariant.echo5_once j (some v') hjF (hR.invariant.received_subset_sent i' j _ hj1)
  have e2 := hR.invariant.echo5_once j none hjF (hR.invariant.received_subset_sent id j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-! ### Answering a return by an exclusion run -/

/-- A `Finset Bool` that omits both `v` and `!v` omits everything. -/
theorem excluded_empty_of_both {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∉ d) : d = ∅ := by
  ext b; cases b <;> cases v <;> simp_all

/-- A `Finset Bool` that holds `!v` and not `v` is the singleton `{!v}`. -/
theorem excluded_eq_singleton {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∈ d) : d = {!v} := by
  ext b; cases b <;> cases v <;> simp_all

/-- `bindUnset (!v) ; retGrade2 v` from an all-alive state (`excluded = ∅`, the
`bindUnset` guard). The `bindUnset (!v)` support guard reads `some (!(!v))`; `Bool.not_not` rewrites
it to `hw`'s `some v`. The exclusion of `!v` is also
the announced bit's guard, so the return announces `v`. -/
theorem excludeThenRetGrade2_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hg : t.grade = none ∨ t.grade = some true)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.grade2 v) v)
      { t with
        excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with excluded := insert (!v) t.excluded } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!v) t.excluded }
      (.retG r id (.grade2 v) v)
      { t with
        excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true } := by
    refine Step.retGrade2 { t with excluded := insert (!v) t.excluded } id v v ?_
      (Finset.mem_insert_self (!v) t.excluded)
      (Finset.mem_insert_self (!v) t.excluded) hg hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!v) ; retGrade1 v`: the same run with the dissent count in
place of the grade guard. -/
theorem excludeThenRetGrade1_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hd : P.f + 1 ≤ (Finset.univ.filter (fun k => t.call k = some (!v) ∨ k ∈ t.F)).card)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.grade1 v) v)
    { t with excluded := insert (!v) t.excluded, ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with excluded := insert (!v) t.excluded } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!v) t.excluded }
      (.retG r id (.grade1 v) v)
      { t with
        excluded := insert (!v) t.excluded,
               ret := Function.update t.ret id true } := by
    refine Step.retGrade1 { t with excluded := insert (!v) t.excluded } id v v ?_
      (Finset.mem_insert_self (!v) t.excluded)
      (Finset.mem_insert_self (!v) t.excluded) hd hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!bnd) ; retGrade0` from an all-alive state (`excluded = ∅`, the
`bindUnset` guard): the exclusion of `!bnd` is the announced bit's guard, so the
return announces `bnd`. -/
theorem excludeThenRetGrade0_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {bnd : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some bnd ∨ k ∈ t.F)).card)
    (hd0 : t.excluded = ∅)
    (hwT : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some true ∨ k ∈ t.F)).card)
    (hwF : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some false ∨ k ∈ t.F)).card)
    (hg : t.grade = none ∨ t.grade = some false)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id .grade0 bnd)
      { t with
        excluded := insert (!bnd) t.excluded, grade := some false,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ
      { t with excluded := insert (!bnd) t.excluded } :=
    Step.bindUnset t (!bnd) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!bnd) t.excluded }
      (.retG r id .grade0 bnd)
      { t with
        excluded := insert (!bnd) t.excluded, grade := some false,
               ret := Function.update t.ret id true } :=
    Step.retGrade0 { t with excluded := insert (!bnd) t.excluded } id bnd
      (Finset.mem_insert_self (!bnd) t.excluded) hwT hwF hg hr
  exact weakLStep_tauThen h1 h2 (by simp)

/-! ### The refinement -/

/-- The two `corrupt` functions stay equal on aligned corrupted sets (a strong per-coordinate `fail`
match, as required by the family lift). -/
private theorem implementationSpecification_corrupt_F_eq {t : SpecState P.n} {s : ImplementationState P.n}
    (hF : t.F = s.F) (id : Fin P.n) :
    (t.corrupt P id).F = (s.corrupt P id).F := by
  rw [ImplementationState.corrupt_F]
  unfold SpecState.corrupt
  by_cases hc : id ∉ s.F ∧ s.F.card < P.f
  · rw [if_pos (by rw [hF]; exact hc), if_pos hc]
    simp [hF]
  · rw [if_neg (by rw [hF]; exact hc), if_neg hc]
    exact hF

/-- **The per-instance GBCA refinement**: the round-`r` implementation
instance refines the round-`r` specification instance — a forward simulation
of the implementation by the specification along `specificationRelation`. -/
theorem refinesSpecification (P : Parameters) (r : ℕ) :
    ForwardSimulation (implementation P r) (specInst P r) (specificationRelation P r) := by
  constructor
  intro q1 q2 hR l μ1 hstep q1' hq1'
  have hRR : SpecificationRelation P q1 q2 := hR
  have hI' : Invariant P q1' := hRR.invariant.step hstep hq1'
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨{ q2 with call := Function.update q2.call id (some b) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q2 id b (by rw [hRR.call_eq]; exact h))⟩,
      hI', ?_, ?_, hRR.F_eq, ?_,
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      change Function.update q2.call id (some b) k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
    · intro b' hb'
      exact exclusionCertificate_send (by intro w hw; exact hw) (hRR.exclusion_certificate b' hb')
  | callLoop id b =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inr ⟨by simp,
      System.weakLStep_of_step (by simp) (Step.callLoop q2 id b)⟩, hRR⟩
  | deliver i j m hsent =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', by simpa using hRR.call_eq, by simpa using hRR.ret_eq, hRR.F_eq, ?_, ?_, ?_,
      hRR.bound_excluded⟩
    · intro b hb
      exact ExclusionCertificate.mono (s := q1)
        (fun i' j' m' hm' => ImplementationState.mem_receiveMessage_received.mpr (Or.inr hm'))
        (fun k w hk => by simpa using hk) (Finset.Subset.refl _) (hRR.exclusion_certificate b hb)
    · intro hg
      obtain ⟨v0, i0, hi0⟩ := hRR.grade2_evidence hg
      exact ⟨v0, i0,
        le_trans hi0 (ImplementationState.receivedCount_le_receiveMessage q1 i j m i0 _)⟩
    · intro hg
      obtain ⟨i0, hi0⟩ := hRR.grade0_evidence hg
      exact ⟨i0, le_trans hi0 (ImplementationState.receivedCount_le_receiveMessage q1 i j m i0 _)⟩
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | voteBot j hin _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | bindBit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | bindBot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => exclusionCertificate_send (by intro w hw; exact hw)
        (hRR.exclusion_certificate b' hb'),
      by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [process_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [process_send_ne hk]
        exact hRR.ret_eq k
  | byzantine j m hjF =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, hRR.exclusion_certificate, hRR.grade2_evidence,
      hRR.grade0_evidence, hRR.bound_excluded⟩
  | retGrade2 id v bnd _hin _hlv hcnt hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k₁, hk₁F, hbq⟩ := bind_receipts_of_echo5_quorum hRR.invariant hcnt
    obtain ⟨k, hkF, hvq⟩ :=
      voteQuorum_of_bind_receipts hRR.invariant (i := k₁) (v := v) (by omega)
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_grade2 q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_exclusionCertificate_of_voteQuorum hRR.invariant hvq (hRR.exclusion_certificate v hv)
    have hgr : q2.grade = none ∨ q2.grade = some true := by
      have hne := grade_ne_false_of_echo5_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact absurd hg hne
        · exact Or.inr rfl
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with
      grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade2 q2 id v v hlive hexcluded hexcluded hgr hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => exclusionCertificate_setBound (exclusionCertificate_ret
          (hRR.exclusion_certificate b hb)),
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoReceiptQuorum_of_vote_receipts hRR.invariant (i := k) (v := v) (by omega))
      refine ⟨{ q2 with
        excluded := insert (!v) q2.excluded, grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade2_run hq hw hlive hd0 hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact exclusionCertificate_setBound
            (exclusionCertificate_ret (exclusionCertificate_of_voteQuorum hRR.invariant hvq))
        · exact exclusionCertificate_setBound (exclusionCertificate_ret (hRR.exclusion_certificate b
            hb))
  | retGrade1 id v bnd _hin _hlv _hnotGrade2 hcnt honce hbind hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k, hkF, hvq⟩ := voteQuorum_of_bind_receipts hRR.invariant hbind
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_grade1 q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_exclusionCertificate_of_voteQuorum hRR.invariant hvq (hRR.exclusion_certificate v hv)
    have hd : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some (!v) ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval (!v))
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade1 q2 id v v hlive hexcluded hexcluded hd hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => exclusionCertificate_setBound (exclusionCertificate_ret
          (hRR.exclusion_certificate b hb)),
        by simpa using hRR.grade2_evidence, by simpa using hRR.grade0_evidence,
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoReceiptQuorum_of_vote_receipts hRR.invariant (i := k) (v := v) (by omega))
      refine ⟨{ q2 with
        excluded := insert (!v) q2.excluded,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade1_run hq hw hlive hd0 hd hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, by simpa using hRR.grade2_evidence,
        by simpa using hRR.grade0_evidence, by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact exclusionCertificate_setBound
            (exclusionCertificate_ret (exclusionCertificate_of_voteQuorum hRR.invariant hvq))
        · exact exclusionCertificate_setBound (exclusionCertificate_ret (hRR.exclusion_certificate b
            hb))
  | retGrade0 id bnd _hin _hlv _hnotGrade2 _hnotGrade1 hcnt hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by
      rw [hRR.ret_eq]; exact hr
    have hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some true ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval true)
    have hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some false ∨ k' ∈ q2.F)).card :=
      hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval false)
    have hgr : q2.grade = none ∨ q2.grade = some false := by
      have hne := grade_ne_true_of_echo5Bot_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact Or.inr rfl
        · exact absurd hg hne
    have hex := hRR.bound_excluded
    cases hb : q1.bound with
    | none =>
      -- the round has not returned yet: exclude the announced bit's complement
      rw [hb, excludedOf_none] at hex
      have hbv : bnd = boundOf q1.sent q1.F .grade0 := by
        rw [hbnd, hb]; rfl
      have hcert : ExclusionCertificate P q1 (!bnd) := by
        rw [hbv]; exact exclusionCertificate_boundOf_grade0 hRR.invariant hcnt
      have hq : q2.quorum P := quorum_of_messageQuorum hRR
        (fun j hj hm' => hRR.invariant.input_called j true hj hm')
        (ImplementationState.bothValid_le hval true)
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun k' => q2.call k' = some bnd ∨ k' ∈ q2.F)).card :=
        hRR.callSupport (inputSupport_of_bothValid hRR.invariant hval bnd)
      refine ⟨{ q2 with
        excluded := insert (!bnd) q2.excluded, grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetGrade0_run hq hw hex hwT hwF hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simp [hex]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b' hb'
        rw [Finset.mem_insert] at hb'
        rcases hb' with rfl | hb'
        · exact exclusionCertificate_setBound (exclusionCertificate_ret hcert)
        · exact exclusionCertificate_setBound (exclusionCertificate_ret (hRR.exclusion_certificate
            b' hb'))
    | some β =>
      -- the round has returned before: it announces the bit on record
      rw [hb, excludedOf_some] at hex
      have hbv : bnd = β := by
        rw [hbnd, hb]; rfl
      subst hbv
      have hmem : (!bnd) ∈ q2.excluded := by
        rw [hex]; exact Finset.mem_singleton_self _
      refine ⟨{ q2 with
        grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retGrade0 q2 id bnd hmem hwT hwF hgr hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb' => exclusionCertificate_setBound (exclusionCertificate_ret
          (hRR.exclusion_certificate b hb')),
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simpa using hex⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplementationState.setBound_process,
          ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplementationState.setBound_process,
            ImplementationState.setProcess_process_ne _ _ _ hk]
          exact hRR.ret_eq k'
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2.corrupt P id,
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp) (Step.fail q2 id)⟩,
      hI', ?_, ?_, implementationSpecification_corrupt_F_eq hRR.F_eq id, ?_, ?_, ?_, ?_⟩
    · intro k
      rw [corrupt_call, ImplementationState.corrupt_process]
      exact hRR.call_eq k
    · intro k
      rw [corrupt_ret, ImplementationState.corrupt_process]
      exact hRR.ret_eq k
    · intro b hb
      rw [corrupt_excluded] at hb
      refine ExclusionCertificate.mono (s := q1) (fun i' j' m' hm' => ?_) (fun k w hk => ?_)
        (ImplementationState.corrupt_F_subset q1 id) (hRR.exclusion_certificate b hb)
      · rw [ImplementationState.corrupt_received]
        exact hm'
      · rw [ImplementationState.corrupt_process]
        exact hk
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨v0, i0, hi0⟩ := hRR.grade2_evidence hg
      exact ⟨v0, i0, by rw [ImplementationState.corrupt_receivedCount]; exact hi0⟩
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨i0, hi0⟩ := hRR.grade0_evidence hg
      exact ⟨i0, by rw [ImplementationState.corrupt_receivedCount]; exact hi0⟩
    · rw [corrupt_excluded, ImplementationState.corrupt_bound]
      exact hRR.bound_excluded

/-! ### Broadcast compatibility of the simulation relation

The round-indexed family lift of the refinement takes `fail` as a broadcast act, applied to every
round at once. It needs the per-round relation to be preserved by that act. The specification
corruption projections (`corrupt_call`/`corrupt_ret`/`corrupt_excluded`/`corrupt_grade`) come from
`ABA/GBCA/Specification.lean`; the two `corrupt` functions stay equal by
`implementationSpecification_corrupt_F_eq`. The statement is proved directly rather than through
`refinesSpecification`, whose `fail` case only yields an existential match. Its consumer is the
round instance's family lifting (`ABA/Composition/GBCAInstanceByABDY.lean`). -/

/-- **Broadcast compatibility**: `specificationRelation` is preserved by the synchronized corruption
of both systems. The two `corrupt`s share the guard `id ∉ F ∧ |F| < f` and `specificationRelation`
aligns the `F`s, so the `if`-conditions agree; every other field is untouched by corruption. -/
theorem specificationRelation_corrupt (P : Parameters) (r : ℕ) (id : Fin P.n)
    {x : ImplementationState P.n} {y : SpecState P.n} (h : specificationRelation P r x y) :
    specificationRelation P r (x.corrupt P id) (y.corrupt P id) := by
  have hR : SpecificationRelation P x y := h
  exact
    { invariant := hR.invariant.step (ImplementationStep.fail (r := r) x id)
        (by rw [PMF.mem_support_pure_iff])
      call_eq := fun k => by
        rw [corrupt_call, ImplementationState.corrupt_process]
        exact hR.call_eq k
      ret_eq := fun k => by
        rw [corrupt_ret, ImplementationState.corrupt_process]
        exact hR.ret_eq k
      F_eq := implementationSpecification_corrupt_F_eq hR.F_eq id
      exclusion_certificate := fun b hb => by
        rw [corrupt_excluded] at hb
        exact ExclusionCertificate.mono
          (fun i j m hm => by rw [ImplementationState.corrupt_received]; exact hm)
          (fun j w hw => by rw [ImplementationState.corrupt_process]; exact hw)
          (ImplementationState.corrupt_F_subset x id)
          (hR.exclusion_certificate b hb)
      grade2_evidence := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨v, i, hi⟩ := hR.grade2_evidence hg
        exact ⟨v, i, by rw [ImplementationState.corrupt_receivedCount]; exact hi⟩
      grade0_evidence := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨i, hi⟩ := hR.grade0_evidence hg
        exact ⟨i, by rw [ImplementationState.corrupt_receivedCount]; exact hi⟩
      bound_excluded := by
        rw [corrupt_excluded, ImplementationState.corrupt_bound]
        exact hR.bound_excluded }

/-! ### Binding at the implementation instance

Binding is stated on the labels of a trace (`BindingTrace`, `ABA/GBCA/SpecificationSafety.lean`),
so a trace-distribution inclusion carries it. The inclusion is the soundness of
`refinesSpecification`, and `safety_transfer` moves the property across it. -/

/-- The soundness inclusion of the per-instance refinement: every trace
distribution achievable by the round-`r` implementation instance is achievable
by the round-`r` specification instance. -/
theorem implementation_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (implementation P r) ⊆ achievableTraceDists (specInst P r) :=
  (ForwardSimulation.toProbabilistic (implementation_isLTS P r) (specInst_isLTS P r)
    (specificationRelation_init P r) (refinesSpecification P r)).achievableTraceDists_subset

/-- **Binding of the implementation instance, on a trace.** Every
positive-probability trace of the round-`r` implementation instance is bound to
one bit: all its round-`r` returns announce that bit, and every one of them that
hands out a value hands out it. The specification has the property
(`specInst_binding`) and `implementation_refines` includes the trace distributions. -/
theorem implementation_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (implementation P r), ∀ t, D t ≠ 0 →
      BindingTrace P r t :=
  safety_transfer (implementation_refines P r) (specInst_binding P r)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.implementation_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implementation_refines

/-- info: 'PLTS.ABA.GBCA.ByABDY.implementation_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implementation_binding

end GBCA.ByABDY
end ABA
end PLTS
