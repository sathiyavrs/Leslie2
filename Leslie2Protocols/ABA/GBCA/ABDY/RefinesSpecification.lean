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

The round-`r` implementation instance (`GBCA.ByABDY.implInst`, ABDY22 Algorithm 6 —
all five message levels, D18) forward-simulates the round-`r` specification
instance (`GBCA.specInst`, the exclusion-set specification, D19):
`GBCA.ByABDY.implRefines`.

Binding is stated on the labels of a trace (`GBCA.BindingTrace`), so the
soundness inclusion of that simulation carries it: `GBCA.ByABDY.implInst_refines` is
the inclusion and `GBCA.ByABDY.implInst_binding` is the specification's
`GBCA.specInst_binding` at the implementation instance.

The implementation state is the protocol's own data, so only `call`, `ret` and
`F` are read off it directly (`InstRel.call_eq`, `ret_eq`, `F_eq`). The
specification's `excluded` and `grade` are bookkeeping the protocol never stores;
the relation carries receipt evidence for them instead:

* `excluded_cert` — every excluded bit `b` is covered by a monotone *exclude certificate*
  `ExcludedCert P s b`: either the opposite bit owns the unique `n − f` `ECHO`
  receipt quorum (`EchoQuorum P s (!b)`, Case A), or an `n − f` wall of
  processes is each corrupted or committed, write-once, to a `VOTE` payload
  other than `some b` (`VoteWall P s b`, Case B). Both disjuncts make an
  `n − f` `VOTE b` receipt quorum — the only source of any grade-≥1 evidence
  for `b` — impossible forever: a `VOTE b` quorum against Case A yields an
  honest double-`ECHO` sender (`echoQuorum_unique`, write-once `sentEcho`),
  and against Case B meets the wall only inside `F`, contradicting
  `2(n − f) > n + f` (`no_disjoint_quorums`). The relation bounds `excluded` from
  above and never from below: which bits are actually excluded is recovered by
  case analysis at the return rows, not stored.
* `gradeA_ev` / `gradeC_ev` — an `A`-side grade lock is backed by an `n − f`
  `ECHO5 v` receipt quorum, a `C`-side lock by an `n − f` `ECHO5 ⊥` quorum. Two
  opposing quorums intersect in an honest process that would have multicast
  two different `ECHO5` payloads, contradicting the write-once `echo5_once` —
  which is the A/C exclusivity the specification's grade guard demands
  (`grade_ne_false_of_echo5_quorum`, `grade_ne_true_of_echo5Bot_quorum`).
* `bound_excluded` — the round's bound bit and the specification's `excluded`
  determine each other: `excluded = excludedOf bound`, empty while the bit is
  unwritten and the singleton of its complement once a return has written it.
  This is the one clause that pins `excluded` from below, and it holds because
  the exclusion fires with the round's first return. It supplies the guard
  `(!bnd) ∈ excluded` of a return that announces a bit already on record, and
  with `excluded_cert` it yields `InstRel.bound_cert`: the bit on record carries
  an exclude certificate for its complement. A value-bearing return then
  announces its own value (`InstRel.retBound_eq`) — the return's `n − f`
  `VOTE v` receipt quorum refutes a certificate for `v`
  (`not_excludedCert_of_voteQuorum`), so a bit on record is `v`, and a bit
  computed here is `v` by `boundOf`. A `C`-return announces
  `boundOf`'s bit, whose complement is certified by `excludedCert_boundOf_C`:
  an honest bit-voter's `vote_conf` receipt quorum is Case A for the opposite
  bit, and where there is no honest bit-voter the all-⊥ wall
  (`excludedCert_of_noHonestVote`) certifies both bits at once.

The specification excludes a bit by the internal τ-transition `bindUnset`, so an
implementation return that needs a not-yet-excluded bit excluded is answered by a
two-step weak run (`weakLStep_tauThen`; `excludeThenRetA_run`,
`excludeThenRetB_run`, `excludeThenRetC_run`). Every return row does the same
decidable case split on the specification's `excluded`, and the run fires
whenever the exclusion is missing. Each return's own evidence derives the
certificate: `retA`'s `ECHO5 v` quorum and `retB`'s `f + 1` `BIND v` receipts
both route to an `n − f` `VOTE v` receipt quorum at an honest process
(`bind_receipts_of_echo5_quorum`, `voteQuorum_of_bind_receipts`), which excludes
`!v` — the quorum itself is a `VoteWall` (`excludedCert_of_voteQuorum`) — and
certifies `v` alive (`not_excludedCert_of_voteQuorum`, which is what discharges
the guard pair `v ∉ excluded ∧ (!v) ∈ excluded` and with it value agreement between
successive returns). The `C`-return's `ECHO5 ⊥` quorum yields a certificate
for *some* bit (`excludedCert_of_echo5Bot_quorum`): if an honest bit-voter exists
anywhere, its `vote_conf` receipt quorum is Case A for the opposite bit;
otherwise the honest vote prefix is all-⊥ and the `VoteWall` holds for both
bits at once.

Both `bindUnset` guards come from one `ECHO` certificate (`bindUnset_guards`):
refine it to an `n − f` `INPUT v` receipt quorum (`inputQuorum_of_echoQuorum`),
whose honest senders hold an input (`input_called`, D8) — that is the quorum
guard (`quorum_of_msg_quorum`) — and whose count feeds
`Inv.supp_of_input_receipts` for the `f + 1` SuppOK count (D15). At the
`C`-return the guards read the returner's own `|Valid| > 1` evidence instead
(`suppI_of_valid` closes both bits at once), so they are available whichever
bit the certificate names. `InstRel.spec_supp` transports the counts to the
specification side along `call_eq`/`F_eq`.

The invariant carries

* the corruption budget (`F_card`) and delivery soundness (`recv_sub`);
* protocol conformance of honest multicasts (`echo_conf`, `vote_input`,
  `vote_conf`, `bind_conf`, `bindBot_conf`, `echo5_input`, `echo5_conf`,
  `echo5Bot_conf`): each honest `ECHO`/`VOTE`/`BIND`/`ECHO5` is backed by the
  receipt evidence that Algorithm 6 demands (receipts only grow, so the
  historical evidence persists in the current state);
* write-once recording of honest multicasts (`echo_once`, `vote_once`,
  `bind_once`, `echo5_once`): an honest payload is the one held in the
  sender's write-once field, so an honest process speaks at most one payload
  per level — `echo_once` carries Case A, `vote_once` the `VoteWall`
  counting, `echo5_once` the grade exclusivity;
* participation (`input_called`, D8): an honest `INPUT` sender has been
  called;
* the *budget-robust* input-origin clause (`input_orig`): for **every**
  potential corruption superset `G ⊇ F` within the budget, an `INPUT b`
  multicast by a sender outside `G` traces back to a process outside `G`
  whose own input is `b`. The quantification over `G` is what makes the
  clause inductive: the classical "first honest sender of `INPUT b` is an
  originator" argument is temporal, but a relayer's `f + 1` receipt quorum
  always contains a sender outside `G`, so the pre-state clause — already
  quantified over the same `G` — supplies the witness, and corruption steps
  only shrink the range of `G`;
* the first-relayer support clause (`input_supp`, D15): an honest
  `INPUT b` multicast is by a genuine holder of `b` or already certifies
  `f + 1` F-blind genuine-holder support (`ImplSupp`) — inductive because
  the first honest relayer's `f + 1` `INPUT b` receipt senders are each in
  `F` or genuine holders, and the count is monotone under every step.

`Framework/FamilySimulation.lean` is imported for the downstream tree: the family
congruence `ForwardSimulation.family` reaches `ABA/Composition/GBCAInstanceByABDY.lean` and
`ABA/Composition/HybridAndSubstitution.lean` along this file, which also supplies the broadcast
ingredient that congruence consumes (`instRel_corrupt`).
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

/-! ### Counting kit: any-payload monotonicity and derivation variants -/

/-- Deliveries only grow the any-payload `VOTE` count. -/
theorem ImplState.voteCount_le_recvMsg {n : ℕ} (s : ImplState n) (i j : Fin n)
    (m : Msg) (i' : Fin n) : s.voteCount i' ≤ (s.recvMsg i j m).voteCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplState.mem_recvMsg_recv.mpr (Or.inr hv)⟩

/-- Deliveries only grow the any-payload `BIND` count. -/
theorem ImplState.bindCount_le_recvMsg {n : ℕ} (s : ImplState n) (i j : Fin n)
    (m : Msg) (i' : Fin n) : s.bindCount i' ≤ (s.recvMsg i j m).bindCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, ImplState.mem_recvMsg_recv.mpr (Or.inr hv)⟩

/-- Corruption is blind to the any-payload `VOTE` count. -/
theorem ImplState.corrupt_voteCount {P : Params} (s : ImplState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).voteCount i = s.voteCount i := by
  unfold ImplState.voteCount
  rw [ImplState.corrupt_recv]

/-- Corruption is blind to the any-payload `BIND` count. -/
theorem ImplState.corrupt_bindCount {P : Params} (s : ImplState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).bindCount i = s.bindCount i := by
  unfold ImplState.bindCount
  rw [ImplState.corrupt_recv]

/-- Any-payload analogue of `exists_sender_notMem` at the `BIND` level: a
`bindCount` exceeding `|G|` yields a sender outside `G` together with its
payload. -/
theorem ImplState.exists_bind_sender_notMem {P : Params} {s : ImplState P.n}
    (G : Finset (Fin P.n)) {i : Fin P.n} (h : G.card < s.bindCount i) :
    ∃ j w, j ∉ G ∧ Msg.bind w ∈ s.recv i j := by
  unfold ImplState.bindCount at h
  obtain ⟨j, hjQ, hjG⟩ := ImplState.exists_honest_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  obtain ⟨w, hw⟩ := hjQ.2
  exact ⟨j, w, hjG, hw⟩

/-! ### The concrete inductive invariant -/

variable {P : Params}

/-- `f + 1` F-blind genuine-holder support for `b` (D15): the impl-side
counterpart of the spec guards' SuppOK counts — the spec-side count follows
along `call_eq`/`F_eq` (`InstRel.spec_supp`). -/
def ImplSupp (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter
    (fun id => (s.proc id).input = some b ∨ id ∈ s.F)).card

/-- The support count is monotone: it survives any step that preserves
genuine holders and grows `F`. -/
theorem ImplSupp.mono {s s' : ImplState P.n} {b : Bool}
    (hproc : ∀ id, (s.proc id).input = some b → (s'.proc id).input = some b)
    (hF : s.F ⊆ s'.F) (h : ImplSupp P s b) : ImplSupp P s' b := by
  unfold ImplSupp at h ⊢
  refine le_trans h (Finset.card_le_card fun id hid => ?_)
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hproc id) (fun hm => hF hm)⟩

/-- The inductive invariant of the GBCA implementation instance. See the
module docstring for the role of each clause. -/
structure Inv (P : Params) (s : ImplState P.n) : Prop where
  /-- Corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivery soundness: everything delivered was multicast. -/
  recv_sub : ∀ i j m, m ∈ s.recv i j → m ∈ s.sent j
  /-- Honest `ECHO b` is backed by an `n − f` `INPUT b` receipt quorum. -/
  echo_conf : ∀ j b, j ∉ s.F → Msg.echo b ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.input b)
  /-- Honest `ECHO` multicasts are recorded in the write-once `sentEcho`
  field; in particular an honest process echoes at most one payload. -/
  echo_once : ∀ j b, j ∉ s.F → Msg.echo b ∈ s.sent j →
    (s.proc j).sentEcho = some b
  /-- Honest voters hold an input (D8). -/
  vote_input : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j → (s.proc j).input ≠ none
  /-- Honest `VOTE b` is backed by an `n − f` `ECHO b` receipt quorum. -/
  vote_conf : ∀ j b, j ∉ s.F → Msg.vote (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.echo b)
  /-- Honest `VOTE` multicasts are recorded in the write-once `sentVote`
  field; this is the level the `VoteWall` certificate counts. -/
  vote_once : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j →
    (s.proc j).sentVote = some w
  /-- Honest `BIND` multicasts are recorded in the write-once `sentBind`
  field; in particular an honest process multicasts at most one payload. -/
  bind_once : ∀ j w, j ∉ s.F → Msg.bind w ∈ s.sent j →
    (s.proc j).sentBind = some w
  /-- Honest `BIND b` is backed by an `n − f` `VOTE b` receipt quorum. -/
  bind_conf : ∀ j b, j ∉ s.F → Msg.bind (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.vote (some b))
  /-- Honest `BIND ⊥` is backed by `n − f` any-payload `VOTE` receipts. -/
  bindBot_conf : ∀ j, j ∉ s.F → Msg.bind none ∈ s.sent j →
    P.n - P.f ≤ s.voteCount j
  /-- Honest `ECHO5` senders hold an input (D8, one level up). -/
  echo5_input : ∀ j w, j ∉ s.F → Msg.echo5 w ∈ s.sent j → (s.proc j).input ≠ none
  /-- Honest `ECHO5` multicasts are recorded in the write-once `sentEcho5`
  field; this is the level that carries the A/C grade exclusivity. -/
  echo5_once : ∀ j w, j ∉ s.F → Msg.echo5 w ∈ s.sent j →
    (s.proc j).sentEcho5 = some w
  /-- Honest `ECHO5 b` is backed by an `n − f` `BIND b` receipt quorum. -/
  echo5_conf : ∀ j b, j ∉ s.F → Msg.echo5 (some b) ∈ s.sent j →
    P.n - P.f ≤ s.recvCount j (.bind (some b))
  /-- Honest `ECHO5 ⊥` is backed by `n − f` any-payload `BIND` receipts. -/
  echo5Bot_conf : ∀ j, j ∉ s.F → Msg.echo5 none ∈ s.sent j →
    P.n - P.f ≤ s.bindCount j
  /-- Budget-robust input origin: for every corruption superset `G` within
  the budget, an `INPUT b` multicast outside `G` traces back to an input `b`
  outside `G`. -/
  input_orig : ∀ (b : Bool) (G : Finset (Fin P.n)), s.F ⊆ G → G.card ≤ P.f →
    ∀ j, j ∉ G → Msg.input b ∈ s.sent j →
    ∃ m, m ∉ G ∧ (s.proc m).input = some b
  /-- Relayer-inductivized first-relayer support (D15): an honest `INPUT b`
  multicast is by a genuine holder of `b`, or certifies the `f + 1` F-blind
  genuine-holder support outright — the first honest relayer's `f + 1`
  `INPUT b` receipt senders are each in `F` or genuine holders. -/
  input_supp : ∀ (b : Bool) (j : Fin P.n), j ∉ s.F → Msg.input b ∈ s.sent j →
    (s.proc j).input = some b ∨ ImplSupp P s b
  /-- Participation one level down (D8): an honest `INPUT` sender has been
  called. -/
  input_called : ∀ j b, j ∉ s.F → Msg.input b ∈ s.sent j →
    (s.proc j).input ≠ none

theorem Inv.initial (P : Params) : Inv P (ImplState.initial P.n) where
  F_card := by simp [ImplState.initial]
  recv_sub := fun i j m h => absurd h (by simp [ImplState.initial])
  echo_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  echo_once := fun j b _ h => absurd h (by simp [ImplState.initial])
  vote_input := fun j w _ h => absurd h (by simp [ImplState.initial])
  vote_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  vote_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  bind_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  bind_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  bindBot_conf := fun j _ h => absurd h (by simp [ImplState.initial])
  echo5_input := fun j w _ h => absurd h (by simp [ImplState.initial])
  echo5_once := fun j w _ h => absurd h (by simp [ImplState.initial])
  echo5_conf := fun j b _ h => absurd h (by simp [ImplState.initial])
  echo5Bot_conf := fun j _ h => absurd h (by simp [ImplState.initial])
  input_orig := fun b G _ _ j _ h => absurd h (by simp [ImplState.initial])
  input_supp := fun b j _ h => absurd h (by simp [ImplState.initial])
  input_called := fun j b _ h => absurd h (by simp [ImplState.initial])

/-- Derivation (D15): any `f + 1` `INPUT b` receipt count yields the F-blind
genuine-holder support — some honest non-holder sender's `input_supp` clause
closes, or else every sender is a holder-or-`F`-member and the senders
themselves witness the count. -/
theorem Inv.supp_of_input_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {b : Bool} (h : P.f + 1 ≤ s.recvCount i (.input b)) :
    ImplSupp P s b := by
  by_cases hc : ∃ k, Msg.input b ∈ s.recv i k ∧ k ∉ s.F ∧ (s.proc k).input ≠ some b
  · obtain ⟨k, hkr, hkF, hkin⟩ := hc
    rcases hI.input_supp b k hkF (hI.recv_sub i k _ hkr) with h' | h'
    · exact absurd h' hkin
    · exact h'
  · push Not at hc
    unfold ImplState.recvCount at h
    unfold ImplSupp
    refine le_trans h (Finset.card_le_card fun k hk => ?_)
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    by_cases hkF : k ∈ s.F
    · exact Or.inr hkF
    · exact Or.inl (hc k hk.2 hkF)

/-- The sender's `setProc` in a send step does not affect other processes. -/
private theorem proc_send_ne {s : ImplState P.n} {j : Fin P.n} {p : ProcState}
    {m : Msg} {k : Fin P.n} (hk : k ≠ j) :
    ((s.setProc j p).mcast j m).proc k = s.proc k := by
  rw [ImplState.mcast_proc, ImplState.setProc_proc_ne _ _ _ hk]

/-- **Invariant preservation, honest-send schema.** Process `j` updates its
local state to `p` and multicasts `m`. The hypotheses collect, clause by
clause, what the new message and the touched field must satisfy; every frame
condition is discharged here once for all nine send rules (`call`, `relay`,
`echo`, `voteBit`, `voteBot`, `bindBit`, `bindBot`, `echo5Bit`, `echo5Bot`). -/
private theorem Inv.send {s : ImplState P.n} (hI : Inv P s) {j : Fin P.n}
    {p : ProcState} {m : Msg}
    (hpne : p.input ≠ none)
    (hpmono : ∀ b, (s.proc j).input = some b → p.input = some b)
    (hInp : ∀ b, m = .input b →
      p.input = some b ∨ P.f + 1 ≤ s.recvCount j (.input b))
    (hEchoC : ∀ b, m = .echo b → P.n - P.f ≤ s.recvCount j (.input b))
    (hVoteC : ∀ b, m = .vote (some b) → P.n - P.f ≤ s.recvCount j (.echo b))
    (hBindC : ∀ b, m = .bind (some b) →
      P.n - P.f ≤ s.recvCount j (.vote (some b)))
    (hBindBotC : m = .bind none → P.n - P.f ≤ s.voteCount j)
    (hEcho5C : ∀ b, m = .echo5 (some b) →
      P.n - P.f ≤ s.recvCount j (.bind (some b)))
    (hEcho5BotC : m = .echo5 none → P.n - P.f ≤ s.bindCount j)
    (hEchoO : ((∀ b, m ≠ .echo b) ∧ p.sentEcho = (s.proc j).sentEcho) ∨
      (∃ b, m = .echo b ∧ p.sentEcho = some b ∧ (s.proc j).sentEcho = none))
    (hVoteO : ((∀ w, m ≠ .vote w) ∧ p.sentVote = (s.proc j).sentVote) ∨
      (∃ w, m = .vote w ∧ p.sentVote = some w ∧ (s.proc j).sentVote = none))
    (hBindO : ((∀ w, m ≠ .bind w) ∧ p.sentBind = (s.proc j).sentBind) ∨
      (∃ w, m = .bind w ∧ p.sentBind = some w ∧ (s.proc j).sentBind = none))
    (hEcho5O : ((∀ w, m ≠ .echo5 w) ∧ p.sentEcho5 = (s.proc j).sentEcho5) ∨
      (∃ w, m = .echo5 w ∧ p.sentEcho5 = some w ∧ (s.proc j).sentEcho5 = none)) :
    Inv P ((s.setProc j p).mcast j m) := by
  have htrans : ∀ (b : Bool) (k : Fin P.n), (s.proc k).input = some b →
      (((s.setProc j p).mcast j m).proc k).input = some b := by
    intro b k hk
    by_cases hkj : k = j
    · subst hkj
      rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpmono b hk
    · rw [proc_send_ne hkj]
      exact hk
  refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- recv_sub
    intro i' j' m' hm'
    rw [ImplState.mcast_recv, ImplState.setProc_recv] at hm'
    exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
  · -- echo_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEchoC b heq.symm
    · simpa using hI.echo_conf j' b hF hold
  · -- echo_once
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hEchoO with ⟨hne, _⟩ | ⟨b₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne b)
      · rw [hm0] at heq
        injection heq with hb
        rw [hpe, hb]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.echo_once j' b hF hold
        rcases hEchoO with ⟨_, hpe⟩ | ⟨b₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.echo_once j' b hF hold
  · -- vote_input
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hpne
      · rw [proc_send_ne hkj]
        exact hI.vote_input j' w hF hold
  · -- vote_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hVoteC b heq.symm
    · simpa using hI.vote_conf j' b hF hold
  · -- vote_once
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hVoteO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.vote_once j' w hF hold
        rcases hVoteO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.vote_once j' w hF hold
  · -- bind_once
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hBindO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.bind_once j' w hF hold
        rcases hBindO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.bind_once j' w hF hold
  · -- bind_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hBindC b heq.symm
    · simpa using hI.bind_conf j' b hF hold
  · -- bindBot_conf
    intro j' hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hBindBotC heq.symm
    · simpa using hI.bindBot_conf j' hF hold
  · -- echo5_input
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hpne
      · rw [proc_send_ne hkj]
        exact hI.echo5_input j' w hF hold
  · -- echo5_once
    intro j' w hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      rcases hEcho5O with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        have hbase := hI.echo5_once j' w hF hold
        rcases hEcho5O with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [proc_send_ne hkj]
        exact hI.echo5_once j' w hF hold
  · -- echo5_conf
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEcho5C b heq.symm
    · simpa using hI.echo5_conf j' b hF hold
  · -- echo5Bot_conf
    intro j' hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEcho5BotC heq.symm
    · simpa using hI.echo5Bot_conf j' hF hold
  · -- input_orig
    intro b G hFG hGc j' hjG hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · refine ⟨j', hjG, ?_⟩
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hp
      · have hcnt' : G.card < s.recvCount j' (Msg.input b) := by omega
        obtain ⟨k, hkG, hkr⟩ := ImplState.exists_sender_notMem G hcnt'
        obtain ⟨m0, hmG, hmi⟩ :=
          hI.input_orig b G hFG hGc k hkG (hI.recv_sub j' k _ hkr)
        exact ⟨m0, hmG, htrans b m0 hmi⟩
    · obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b G hFG hGc j' hjG hold
      exact ⟨m0, hmG, htrans b m0 hmi⟩
  · -- input_supp
    intro b j' hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · left
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hp
      · right
        exact ImplSupp.mono (fun k hk => htrans b k hk) (fun _ hh => hh)
          (hI.supp_of_input_receipts hcnt)
    · rcases hI.input_supp b j' hF hold with hin | hsupp
      · left
        by_cases hkj : j' = j
        · subst hkj
          rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
          exact hpmono b hin
        · rw [proc_send_ne hkj]
          exact hin
      · right
        exact ImplSupp.mono (fun k hk => htrans b k hk) (fun _ hh => hh) hsupp
  · -- input_called
    intro j' b hF hm'
    rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hpne
      · rw [proc_send_ne hkj]
        exact hI.input_called j' b hF hold

/-- **Invariant preservation, local-frame schema.** A `setProc` that keeps
the input and all four write-once fields (the return rules, which flip only
`returned`) preserves every clause. -/
private theorem Inv.setProc_frame {s : ImplState P.n} (hI : Inv P s)
    {id : Fin P.n} {p : ProcState}
    (h1 : p.input = (s.proc id).input)
    (h2 : p.sentEcho = (s.proc id).sentEcho)
    (h3 : p.sentVote = (s.proc id).sentVote)
    (h4 : p.sentBind = (s.proc id).sentBind)
    (h5 : p.sentEcho5 = (s.proc id).sentEcho5) :
    Inv P (s.setProc id p) := by
  have hin : ∀ k, ((s.setProc id p).proc k).input = (s.proc k).input := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h1]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hech : ∀ k, ((s.setProc id p).proc k).sentEcho = (s.proc k).sentEcho := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h2]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hvot : ∀ k, ((s.setProc id p).proc k).sentVote = (s.proc k).sentVote := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h3]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hbin : ∀ k, ((s.setProc id p).proc k).sentBind = (s.proc k).sentBind := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h4]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  have hsea : ∀ k, ((s.setProc id p).proc k).sentEcho5 = (s.proc k).sentEcho5 := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [ImplState.setProc_proc_self, h5]
    · rw [ImplState.setProc_proc_ne _ _ _ hk]
  refine ⟨hI.F_card, by simpa using hI.recv_sub, by simpa using hI.echo_conf, ?_, ?_,
    by simpa using hI.vote_conf, ?_, ?_, by simpa using hI.bind_conf,
    by simpa using hI.bindBot_conf, ?_, ?_, by simpa using hI.echo5_conf,
    by simpa using hI.echo5Bot_conf, ?_, ?_, ?_⟩
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
    obtain ⟨m0, hmG, hmi⟩ := hI.input_orig b G hFG hGc j' hjG hm'
    exact ⟨m0, hmG, by rw [hin m0]; exact hmi⟩
  · intro b j' hF hm'
    rcases hI.input_supp b j' hF hm' with hji | hsupp
    · left
      rw [hin j']
      exact hji
    · right
      exact ImplSupp.mono (s := s) (fun k hk => by rw [hin k]; exact hk)
        (fun _ hh => hh) hsupp
  · intro j' b hF hm'
    rw [hin j']
    exact hI.input_called j' b hF hm'

/-- **Frame lemma for the bound bit.** The ghost write touches the network
state's own field alone, and no clause of `Inv` reads it. -/
private theorem Inv.setBound {s : ImplState P.n} (hI : Inv P s) (β : Bool) :
    Inv P (s.setBound β) := { hI with }

/-- **Invariant preservation.** `Inv` is preserved by every implementation
step. -/
theorem Inv.step {r : ℕ} {s : ImplState P.n} {l : Lab P.n}
    {μ : PMF (ImplState P.n)} {s' : ImplState P.n} (hI : Inv P s)
    (hstep : ImplStep P r s l μ) (hs' : s' ∈ μ.support) : Inv P s' := by
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
      by simpa using hI.echo5_once, ?_, ?_, by simpa using hI.input_orig,
      by simpa [ImplSupp] using hI.input_supp, by simpa using hI.input_called⟩
    · intro i' j' m' hm'
      rcases ImplState.mem_recvMsg_recv.mp hm' with ⟨rfl, rfl, rfl⟩ | hold
      · exact hsent
      · exact hI.recv_sub i' j' m' hold
    · intro j' b hF hm'
      exact le_trans (hI.echo_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.vote_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.bind_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.bindBot_conf j' hF hm')
        (ImplState.voteCount_le_recvMsg s i j m j')
    · intro j' b hF hm'
      exact le_trans (hI.echo5_conf j' b hF hm')
        (ImplState.recvCount_le_recvMsg s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.echo5Bot_conf j' hF hm')
        (ImplState.bindCount_le_recvMsg s i j m j')
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
  | byz j m hjF =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsentG : ∀ (G : Finset (Fin P.n)), s.F ⊆ G → ∀ j' m', j' ∉ G →
        m' ∈ (s.mcast j m).sent j' → m' ∈ s.sent j' := by
      intro G hFG j' m' hjG hm'
      rcases ImplState.mem_mcast_sent.mp hm' with ⟨rfl, _⟩ | hold
      · exact absurd (hFG hjF) hjG
      · exact hold
    have hs := fun j' m' (hF : j' ∉ s.F) =>
      hsentG s.F (Finset.Subset.refl _) j' m' hF
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact ImplState.sent_subset_mcast _ _ _ _ (hI.recv_sub i' j' m' hm')
    · exact fun j' b hF hm' => hI.echo_conf j' b hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.echo_once j' b hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.vote_input j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.vote_conf j' b hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.vote_once j' w hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.bind_once j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.bind_conf j' b hF (hs j' _ hF hm')
    · exact fun j' hF hm' => hI.bindBot_conf j' hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.echo5_input j' w hF (hs j' _ hF hm')
    · exact fun j' w hF hm' => hI.echo5_once j' w hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.echo5_conf j' b hF (hs j' _ hF hm')
    · exact fun j' hF hm' => hI.echo5Bot_conf j' hF (hs j' _ hF hm')
    · exact fun b G hFG hGc j' hjG hm' =>
        hI.input_orig b G hFG hGc j' hjG (hsentG G hFG j' _ hjG hm')
    · exact fun b j' hF hm' => hI.input_supp b j' hF (hs j' _ hF hm')
    · exact fun j' b hF hm' => hI.input_called j' b hF (hs j' _ hF hm')
  | retA id v bnd _hin _hlv hcnt hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Inv.setBound ?_ bnd
    exact hI.setProc_frame rfl rfl rfl rfl rfl
  | retB id v bnd _hin _hlv _hnotA hcnt honce hbind hval hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Inv.setBound ?_ bnd
    exact hI.setProc_frame rfl rfl rfl rfl rfl
  | retC id bnd _hin _hlv _hnotA _hnotB hcnt hval hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Inv.setBound ?_ bnd
    exact hI.setProc_frame rfl rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsub := ImplState.corrupt_F_subset s id
    have hFtr : ∀ j' : Fin P.n, j' ∉ (s.corrupt P id).F → j' ∉ s.F :=
      fun j' hF hj => hF (hsub hj)
    refine ⟨ImplState.corrupt_card_le s id hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      rw [ImplState.corrupt_recv] at hm'
      rw [ImplState.corrupt_sent]
      exact hI.recv_sub i' j' m' hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.echo_conf j' b (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.echo_once j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.vote_input j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.vote_conf j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.vote_once j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.bind_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.bind_conf j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_voteCount]
      exact hI.bindBot_conf j' (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.echo5_input j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.echo5_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_recvCount]
      exact hI.echo5_conf j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_bindCount]
      exact hI.echo5Bot_conf j' (hFtr j' hF) hm'
    · intro b G hFG hGc j' hjG hm'
      rw [ImplState.corrupt_sent] at hm'
      obtain ⟨m0, hmG, hmi⟩ :=
        hI.input_orig b G (Finset.Subset.trans hsub hFG) hGc j' hjG hm'
      exact ⟨m0, hmG, by rw [ImplState.corrupt_proc]; exact hmi⟩
    · intro b j' hF' hm'
      rw [ImplState.corrupt_sent] at hm'
      rcases hI.input_supp b j' (hFtr j' hF') hm' with hin | hsupp
      · left
        rw [ImplState.corrupt_proc]
        exact hin
      · right
        refine ImplSupp.mono (s := s) (fun k hk => ?_) hsub hsupp
        rw [ImplState.corrupt_proc]
        exact hk
    · intro j' b hF hm'
      rw [ImplState.corrupt_sent] at hm'
      rw [ImplState.corrupt_proc]
      exact hI.input_called j' b (hFtr j' hF) hm'

/-! ### The exclude certificates -/

/-- Case A carrier: some process holds an `n − f` `ECHO v` receipt quorum.
The certificate is `F`-blind and receipt-monotone, hence stable under `fail`
and under every implementation step, and at most one bit can carry it
(`echoQuorum_unique`). -/
def EchoQuorum (P : Params) (s : ImplState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.recvCount i (.echo v)

/-- Derivation from `f + 1` `VOTE v` receipts: they contain an honest `VOTE v`
sender, whose `vote_conf` receipt quorum is the certificate. -/
theorem echoQuorum_of_vote_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.vote (some v))) :
    EchoQuorum P s v := by
  have hFc := hI.F_card
  have h' : s.F.card < s.recvCount i (Msg.vote (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hI.vote_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- The certificate refines to an `n − f` `INPUT v` receipt quorum. -/
theorem inputQuorum_of_echoQuorum {s : ImplState P.n} (hI : Inv P s)
    {v : Bool} (h : EchoQuorum P s v) :
    ∃ m, P.n - P.f ≤ s.recvCount m (.input v) := by
  obtain ⟨i, hi⟩ := h
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.recvCount i (Msg.echo v) := by omega
  obtain ⟨m, hmF, hmr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨m, hI.echo_conf m v hmF (hI.recv_sub i m _ hmr)⟩

/-- At most one bit carries an `n − f` `ECHO` quorum: the two quorums
intersect in an honest sender, and `sentEcho` is write-once. -/
theorem echoQuorum_unique {s : ImplState P.n} (hI : Inv P s) {v v' : Bool}
    (h : EchoQuorum P s v) (h' : EchoQuorum P s v') : v = v' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hI.F_card hi hi'
  have e1 := hI.echo_once j v hjF (hI.recv_sub i j _ hj1)
  have e2 := hI.echo_once j v' hjF (hI.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact Option.some.inj e2

/-- Case B carrier: an `n − f` wall of processes each of which is corrupted
or has committed its write-once `VOTE` field to a payload other than
`some b`. -/
def VoteWall (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  P.n - P.f ≤ (Finset.univ.filter
    (fun j => j ∈ s.F ∨ ∃ w, (s.proc j).sentVote = some w ∧ w ≠ some b)).card

/-- The exclude certificate licensing `b ∈ excluded` on the specification side:
either the opposite bit owns the (unique) `n − f` `ECHO` receipt quorum, or
a `VoteWall` blocks `b` at the `VOTE` level. Both disjuncts make an `n − f`
`VOTE b` receipt quorum — the only source of any grade-≥1 evidence for `b`
— impossible forever. -/
def ExcludedCert (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  EchoQuorum P s (!b) ∨ VoteWall P s b

/-- The counting core: two `n − f`-sized subsets of `Fin n` meeting only
inside `F` contradict `|F| ≤ f` and `3f < n` (`2(n − f) > n + f`). The same
arithmetic as `exists_honest_recv₂`, exposed as a set statement because
`VoteWall` is a set of processes, not a receipt row. -/
theorem no_disjoint_quorums {Q D F : Finset (Fin P.n)}
    (hQ : P.n - P.f ≤ Q.card) (hD : P.n - P.f ≤ D.card)
    (hQD : Q ∩ D ⊆ F) (hF : F.card ≤ P.f) : False := by
  have hf := P.hf
  have hcard := Finset.card_union_add_card_inter Q D
  have hun : (Q ∪ D).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hint : (Q ∩ D).card ≤ F.card := Finset.card_le_card hQD
  omega

/-- **Certificate monotonicity**: receipts only grow, `sentVote` is
write-once, `F` only grows — so an exclusion certificate never expires. -/
theorem ExcludedCert.mono {s s' : ImplState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.recv i j → m ∈ s'.recv i j)
    (hvote : ∀ j w, (s.proc j).sentVote = some w → (s'.proc j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : ExcludedCert P s b → ExcludedCert P s' b := by
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

/-- `ExcludedCert` is stable under an honest send that respects the write-once
`sentVote` field. -/
private theorem excludedCert_send {s : ImplState P.n} {j : Fin P.n} {p : ProcState}
    {m : Msg} (hvote : ∀ w, (s.proc j).sentVote = some w → p.sentVote = some w)
    {b : Bool} (h : ExcludedCert P s b) :
    ExcludedCert P ((s.setProc j p).mcast j m) b :=
  ExcludedCert.mono (s := s) (fun _ _ _ hm => by simpa using hm)
    (fun k w hk => by
      by_cases hkj : k = j
      · subst hkj
        rw [ImplState.mcast_proc, ImplState.setProc_proc_self]
        exact hvote w hk
      · rw [proc_send_ne hkj]
        exact hk)
    (Finset.Subset.refl _) h

/-- `ExcludedCert` is stable under a return (only `returned` flips). -/
private theorem excludedCert_ret {s : ImplState P.n} {id : Fin P.n} {b : Bool}
    (h : ExcludedCert P s b) :
    ExcludedCert P (s.setProc id { s.proc id with returned := true }) b :=
  ExcludedCert.mono (s := s) (fun _ _ _ hm => by simpa using hm)
    (fun k w hk => by
      by_cases hkj : k = id
      · subst hkj
        rw [ImplState.setProc_proc_self]
        exact hk
      · rw [ImplState.setProc_proc_ne _ _ _ hkj]
        exact hk)
    (Finset.Subset.refl _) h

/-- `ExcludedCert` is stable under the ghost write (no clause reads the bound
bit). -/
private theorem excludedCert_setBound {s : ImplState P.n} {b β : Bool}
    (h : ExcludedCert P s b) : ExcludedCert P (s.setBound β) b :=
  ExcludedCert.mono (s := s) (fun _ _ _ hm => hm) (fun _ _ hk => hk)
    (Finset.Subset.refl _) h

/-! ### The derivation chains -/

/-- `f + 1` `BIND v` receipts exceed the corruption budget, so they contain
an honest binder, whose `bind_conf` wait-condition is an honest `n − f`
`VOTE v` receipt quorum — the object the binding argument counts. -/
theorem voteQuorum_of_bind_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.vote (some v)) := by
  have hFc := hI.F_card
  have h' : s.F.card < s.recvCount i (Msg.bind (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hkF, hI.bind_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- An `n − f` `ECHO5 v` receipt quorum contains an honest `ECHO5` sender, whose
`echo5_conf` wait-condition is an honest `n − f` `BIND v` receipt quorum. -/
theorem bind_receipts_of_echo5_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.echo5 (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.bind (some v)) := by
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  have h' : s.F.card < s.recvCount i (Msg.echo5 (some v)) := by omega
  obtain ⟨k, hkF, hkr⟩ := ImplState.exists_sender_notMem s.F h'
  exact ⟨k, hkF, hI.echo5_conf k v hkF (hI.recv_sub i k _ hkr)⟩

/-- **Availability, exclude side**: any `n − f` `VOTE v` receipt quorum excludes
the opposite bit — the quorum's members are each corrupted or committed
(write-once) to `some v`, so the quorum itself is a `VoteWall` for `!v`. -/
theorem excludedCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    ExcludedCert P s (!v) := by
  refine Or.inr (le_trans h (Finset.card_le_card fun k hk => ?_))
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  by_cases hkF : k ∈ s.F
  · exact Or.inl hkF
  · refine Or.inr ⟨some v, hI.vote_once k (some v) hkF (hI.recv_sub i k _ hk.2), ?_⟩
    intro hc
    injection hc with hc
    cases v <;> simp at hc

/-- **Availability, live side**: an `n − f` `VOTE v` receipt quorum refutes
both certificate cases for `v` itself — against Case A the derived
`ECHO v` quorum meets the `ECHO (!v)` quorum in an honest double-echoer, and
against Case B the quorum meets the wall only inside `F`. -/
theorem not_excludedCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    ¬ ExcludedCert P s v := by
  have hfn := P.f_lt_n_sub_f
  rintro (hq | hw)
  · have hv : EchoQuorum P s v := echoQuorum_of_vote_receipts hI (i := i) (by omega)
    have hvv := echoQuorum_unique hI hv hq
    cases v <;> simp at hvv
  · refine no_disjoint_quorums (F := s.F) h hw ?_ hI.F_card
    intro k hk
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hk
    obtain ⟨⟨-, hrecv⟩, -, hd⟩ := hk
    rcases hd with hkF | ⟨w, hsv, hne⟩
    · exact hkF
    · by_contra hkF
      have hcommit := hI.vote_once k (some v) hkF (hI.recv_sub i k _ hrecv)
      rw [hsv] at hcommit
      exact hne (Option.some.inj hcommit)

/-- **Availability at the `C`-return**: an `n − f` `ECHO5 ⊥` receipt quorum
certifies *some* excluded bit. Classical dichotomy on "an honest bit-voter
exists somewhere": if yes, its `vote_conf` receipt quorum is Case A for the
opposite bit; if no, the quorum's honest `ECHO5` sender holds `n − f` any-`BIND`
receipts, its honest `BIND` sender can only have sent `BIND ⊥` (a bit `BIND`
needs an honest bit-voter), and that sender's `bindBot_conf` receipts pin an
`n − f` set of processes each corrupted or committed to `VOTE ⊥` — a
`VoteWall` for both bits at once. -/
theorem excludedCert_of_noHonestVote {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.recvCount i (.echo5 none))
    (hcase : ¬ ∃ (k : Fin P.n) (b : Bool), k ∉ s.F ∧ Msg.vote (some b) ∈ s.sent k)
    (b : Bool) : ExcludedCert P s b := by
  classical
  have hFc := hI.F_card
  have hfn := P.f_lt_n_sub_f
  · have h1 : s.F.card < s.recvCount i (Msg.echo5 none) := by omega
    obtain ⟨p, hpF, hpr⟩ := ImplState.exists_sender_notMem s.F h1
    have hbc : P.n - P.f ≤ s.bindCount p :=
      hI.echo5Bot_conf p hpF (hI.recv_sub i p _ hpr)
    have h2 : s.F.card < s.bindCount p := by omega
    obtain ⟨k, w, hkF, hkr⟩ := ImplState.exists_bind_sender_notMem s.F h2
    have hksent := hI.recv_sub p k _ hkr
    have hw : w = none := by
      cases w with
      | none => rfl
      | some v' =>
        exfalso
        have hvq := hI.bind_conf k v' hkF hksent
        have h3 : s.F.card < s.recvCount k (Msg.vote (some v')) := by omega
        obtain ⟨m', hmF, hmr⟩ := ImplState.exists_sender_notMem s.F h3
        exact hcase ⟨m', v', hmF, hI.recv_sub k m' _ hmr⟩
    subst hw
    have hvc : P.n - P.f ≤ s.voteCount k := hI.bindBot_conf k hkF hksent
    refine Or.inr (le_trans hvc (Finset.card_le_card fun q hq => ?_))
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    obtain ⟨wv, hwv⟩ := hq.2
    by_cases hqF : q ∈ s.F
    · exact Or.inl hqF
    · have hqs := hI.recv_sub k q _ hwv
      have hnone : wv = none := by
        cases wv with
        | none => rfl
        | some v' => exact absurd ⟨q, v', hqF, hqs⟩ hcase
      subst hnone
      exact Or.inr ⟨none, hI.vote_once q none hqF hqs, by simp⟩

/-- **Availability at the `C`-return**: an `n − f` `ECHO5 ⊥` receipt quorum
certifies *some* excluded bit. Classical dichotomy on "an honest bit-voter
exists somewhere": if yes, its `vote_conf` receipt quorum is Case A for the
opposite bit; if no, the all-⊥ wall of `excludedCert_of_noHonestVote`
answers. -/
theorem excludedCert_of_echo5Bot_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.recvCount i (.echo5 none)) :
    ∃ b, ExcludedCert P s b := by
  classical
  by_cases hcase : ∃ (k : Fin P.n) (b : Bool), k ∉ s.F ∧ Msg.vote (some b) ∈ s.sent k
  · obtain ⟨k, b, hkF, hks⟩ := hcase
    refine ⟨!b, Or.inl ?_⟩
    rw [Bool.not_not]
    exact ⟨k, hI.vote_conf k b hkF hks⟩
  · exact ⟨false, excludedCert_of_noHonestVote hI h hcase false⟩

/-- **The `C`-return's announced bit is certified.** At an `n − f` `ECHO5 ⊥`
receipt quorum the complement of `boundOf … C` carries an exclude certificate.
Where an honest bit-voter exists its `vote_conf` receipt quorum is Case A for
the opposite bit, which is the bit `boundOf` names; where none exists the wall
covers both bits at once. -/
theorem excludedCert_boundOf_C {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.recvCount i (.echo5 none)) :
    ExcludedCert P s (!(boundOf s.sent s.F .C)) := by
  classical
  rw [boundOf_C]
  split_ifs with h1 h2
  · obtain ⟨k, hkF, hks⟩ := h1
    exact Or.inl ⟨k, hI.vote_conf k true hkF hks⟩
  · obtain ⟨k, hkF, hks⟩ := h2
    exact Or.inl ⟨k, hI.vote_conf k false hkF hks⟩
  · refine excludedCert_of_noHonestVote hI h (fun hc => ?_) _
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
for the two fields it does not. `excluded_cert` bounds `excluded` from above — an exclusion
certificate for every excluded bit — and never from below. -/
structure InstRel (P : Params) (s : ImplState P.n) (t : SpecState P.n) : Prop where
  /-- The concrete inductive invariant. -/
  inv : Inv P s
  /-- Spec inputs are the concrete inputs. -/
  call_eq : ∀ id, t.call id = (s.proc id).input
  /-- Spec return flags are the concrete return flags. -/
  ret_eq : ∀ id, t.ret id = (s.proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- Every excluded bit carries a monotone exclude certificate. -/
  excluded_cert : ∀ b, b ∈ t.excluded → ExcludedCert P s b
  /-- An `A`-side grade lock is backed by an `n − f` `ECHO5 v` receipt quorum
  for some bit `v`. -/
  gradeA_ev : t.grade = some true →
    ∃ v i, P.n - P.f ≤ s.recvCount i (.echo5 (some v))
  /-- A `C`-side grade lock is backed by an `n − f` `ECHO5 ⊥` receipt
  quorum. -/
  gradeC_ev : t.grade = some false →
    ∃ i, P.n - P.f ≤ s.recvCount i (.echo5 none)
  /-- The round's bound bit determines the exclusion set: nothing is excluded
  while the bit is unwritten, and the complement of the bit is the one excluded
  bit once a return has written it. The exclusion fires with the round's first
  return, so the two records move together. -/
  bound_excluded : t.excluded = excludedOf s.bound

/-- The simulation relation of the round-`r` instance (the round index is
phantom: every round runs the same protocol). -/
def instRel (P : Params) (_r : ℕ) (s : ImplState P.n) (t : SpecState P.n) : Prop :=
  InstRel P s t

/-- The initial states are related. -/
theorem instRel_init (P : Params) (r : ℕ) :
    instRel P r (implInst P r).init (specInst P r).init where
  inv := Inv.initial P
  call_eq := fun _ => rfl
  ret_eq := fun _ => rfl
  F_eq := rfl
  excluded_cert := fun b hb => absurd hb (Finset.notMem_empty b)
  gradeA_ev := fun h => absurd h (by simp [SpecState.initial])
  gradeC_ev := fun h => absurd h (by simp [SpecState.initial])
  bound_excluded := rfl

/-- The bound bit on record carries an exclude certificate for its complement:
the specification has excluded that complement, and every excluded bit is
certified. -/
theorem InstRel.bound_cert {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) (β : Bool) (hb : s.bound = some β) :
    ExcludedCert P s (!β) := by
  refine hR.excluded_cert (!β) ?_
  rw [hR.bound_excluded, hb, excludedOf_some]
  exact Finset.mem_singleton_self _

/-- **The announced bit of a value-bearing return.** A return of `v` carries an
`n − f` `VOTE v` receipt quorum, which refutes an exclude certificate for `v`;
so a bound bit already on record, whose complement is certified, is `v` itself,
and one computed here is `v` by `boundOf`. -/
theorem InstRel.retBound_eq {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {i : Fin P.n} {v : Bool} {out : GbcaOut}
    (hvq : P.n - P.f ≤ s.recvCount i (.vote (some v)))
    (hout : boundOf s.sent s.F out = v) :
    s.bound.getD (boundOf s.sent s.F out) = v := by
  cases hb : s.bound with
  | none => exact hout
  | some β =>
    refine Option.getD_some.trans ?_
    by_contra hne
    refine not_excludedCert_of_voteQuorum hR.inv hvq ?_
    have hv : (!β) = v := by cases β <;> cases v <;> simp_all
    rw [← hv]
    exact hR.bound_cert β hb

/-! ### Deriving the spec guards -/

/-- D15 derivation at `retB`/`retC`: `|Valid| > 1` evidence yields the
`f + 1` F-blind genuine-holder support for either bit — its `n − f ≥ f + 1`
`INPUT` receipt quorum for that bit sits at the returner itself. -/
theorem suppI_of_valid {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (hv : s.bothValid P i) (b : Bool) : ImplSupp P s b := by
  have hfn := P.f_lt_n_sub_f
  exact hI.supp_of_input_receipts
    (le_trans (by omega) (ImplState.bothValid_le hv b))

/-- Transport an impl-side support count to the spec side along
`call_eq`/`F_eq`: the spec guards' SuppOK counts (D15). -/
theorem InstRel.spec_supp {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {b : Bool} (h : ImplSupp P s b) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some b ∨ id ∈ t.F)).card := by
  unfold ImplSupp at h
  refine le_trans h (Finset.card_le_card fun k hk => ?_)
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  rw [hR.call_eq, hR.F_eq]
  exact hk.2

/-- D8 quorum derivation: any `n − f` receipt quorum of a message whose honest
senders must hold an input yields the spec's call quorum; corrupted senders
are absorbed into the `∪ F`. -/
theorem quorum_of_msg_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {i : Fin P.n} {m : Msg}
    (hpart : ∀ j, j ∉ s.F → m ∈ s.sent j → (s.proc j).input ≠ none)
    (h : P.n - P.f ≤ s.recvCount i m) : t.quorum P := by
  unfold SpecState.quorum
  unfold ImplState.recvCount at h
  refine le_trans h (Finset.card_le_card ?_)
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [Finset.mem_union]
  by_cases hkF : k ∈ t.F
  · exact Or.inr hkF
  · refine Or.inl ?_
    rw [Finset.mem_filter]
    have hkF' : k ∉ s.F := by rwa [hR.F_eq] at hkF
    refine ⟨Finset.mem_univ _, hkF, ?_⟩
    rw [hR.call_eq]
    exact hpart k hkF' (hR.inv.recv_sub i k _ hk.2)

/-- **Both `bindUnset` guards from the single certificate.** -/
theorem bindUnset_guards {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {v : Bool} (hq : EchoQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some v ∨ id ∈ t.F)).card := by
  obtain ⟨m, hm⟩ := inputQuorum_of_echoQuorum hR.inv hq
  have hfn := P.f_lt_n_sub_f
  refine ⟨quorum_of_msg_quorum hR
    (fun j hj hm' => hR.inv.input_called j v hj hm') hm, ?_⟩
  exact hR.spec_supp (hR.inv.supp_of_input_receipts (le_trans (by omega) hm))

/-- A/C-exclusivity, `A`-side: an `n − f` `ECHO5 v` receipt quorum rules out
a `C`-side grade lock (the two `ECHO5` quorums would intersect in an honest
process with two different `ECHO5` payloads, against `echo5_once`). -/
theorem grade_ne_false_of_echo5_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.recvCount id (.echo5 (some v))) :
    t.grade ≠ some false := by
  intro hg
  obtain ⟨i', hc⟩ := hR.gradeC_ev hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hR.inv.F_card hcnt hc
  have e1 := hR.inv.echo5_once j (some v) hjF (hR.inv.recv_sub id j _ hj1)
  have e2 := hR.inv.echo5_once j none hjF (hR.inv.recv_sub i' j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-- A/C-exclusivity, `C`-side: an `n − f` `ECHO5 ⊥` receipt quorum rules out
an `A`-side grade lock. -/
theorem grade_ne_true_of_echo5Bot_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.recvCount id (.echo5 none)) :
    t.grade ≠ some true := by
  intro hg
  obtain ⟨v', i', hc⟩ := hR.gradeA_ev hg
  obtain ⟨j, hjF, hj1, hj2⟩ := ImplState.exists_honest_recv₂ hR.inv.F_card hc hcnt
  have e1 := hR.inv.echo5_once j (some v') hjF (hR.inv.recv_sub i' j _ hj1)
  have e2 := hR.inv.echo5_once j none hjF (hR.inv.recv_sub id j _ hj2)
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

/-- `bindUnset (!v) ; retA v` from an all-alive state (`excluded = ∅`, the
`bindUnset` guard). The `bindUnset (!v)` support guard reads `some (!(!v))`;
`Bool.not_not` rewrites it to `hw`'s `some v`. The exclusion of `!v` is also
the announced bit's guard, so the return announces `v`. -/
theorem excludeThenRetA_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hg : t.grade = none ∨ t.grade = some true)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.A v) v)
      { t with excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with excluded := insert (!v) t.excluded } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!v) t.excluded }
      (.retG r id (.A v) v)
      { t with excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true } := by
    refine Step.retA { t with excluded := insert (!v) t.excluded } id v v ?_
      (Finset.mem_insert_self (!v) t.excluded)
      (Finset.mem_insert_self (!v) t.excluded) hg hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!v) ; retB v`: the same run with the dissent count in
place of the grade guard. -/
theorem excludeThenRetB_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hd : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!v) ∨ k ∈ t.F)).card)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.B v) v)
      { t with excluded := insert (!v) t.excluded,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with excluded := insert (!v) t.excluded } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!v) t.excluded }
      (.retG r id (.B v) v)
      { t with excluded := insert (!v) t.excluded,
               ret := Function.update t.ret id true } := by
    refine Step.retB { t with excluded := insert (!v) t.excluded } id v v ?_
      (Finset.mem_insert_self (!v) t.excluded)
      (Finset.mem_insert_self (!v) t.excluded) hd hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!bnd) ; retC` from an all-alive state (`excluded = ∅`, the
`bindUnset` guard): the exclusion of `!bnd` is the announced bit's guard, so the
return announces `bnd`. -/
theorem excludeThenRetC_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {bnd : Bool}
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
    (specInst P r).weakLStep t (.retG r id .C bnd)
      { t with excluded := insert (!bnd) t.excluded, grade := some false,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ
      { t with excluded := insert (!bnd) t.excluded } :=
    Step.bindUnset t (!bnd) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!bnd) t.excluded }
      (.retG r id .C bnd)
      { t with excluded := insert (!bnd) t.excluded, grade := some false,
               ret := Function.update t.ret id true } :=
    Step.retC { t with excluded := insert (!bnd) t.excluded } id bnd
      (Finset.mem_insert_self (!bnd) t.excluded) hwT hwF hg hr
  exact weakLStep_tauThen h1 h2 (by simp)

/-! ### The refinement -/

/-- The two `corrupt` functions stay in lockstep on aligned corrupted sets
(a strong per-coordinate `fail` match, as required by the family lift). -/
private theorem implSpec_corrupt_F_eq {t : SpecState P.n} {s : ImplState P.n}
    (hF : t.F = s.F) (id : Fin P.n) :
    (t.corrupt P id).F = (s.corrupt P id).F := by
  rw [ImplState.corrupt_F]
  unfold SpecState.corrupt
  by_cases hc : id ∉ s.F ∧ s.F.card < P.f
  · rw [if_pos (by rw [hF]; exact hc), if_pos hc]
    simp [hF]
  · rw [if_neg (by rw [hF]; exact hc), if_neg hc]
    exact hF

/-- **The per-instance GBCA refinement**: the round-`r` implementation
instance refines the round-`r` specification instance — a forward simulation
of the implementation by the specification along `instRel`. -/
theorem implRefines (P : Params) (r : ℕ) :
    ForwardSimulation (implInst P r) (specInst P r) (instRel P r) := by
  constructor
  intro q1 q2 hR l μ1 hstep q1' hq1'
  have hRR : InstRel P q1 q2 := hR
  have hI' : Inv P q1' := hRR.inv.step hstep hq1'
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨{ q2 with call := Function.update q2.call id (some b) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q2 id b (by rw [hRR.call_eq]; exact h))⟩,
      hI', ?_, ?_, hRR.F_eq, ?_,
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      change Function.update q2.call id (some b) k = _
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne hk, proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
    · intro b' hb'
      exact excludedCert_send (by intro w hw; exact hw) (hRR.excluded_cert b' hb')
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
      exact ExcludedCert.mono (s := q1)
        (fun i' j' m' hm' => ImplState.mem_recvMsg_recv.mpr (Or.inr hm'))
        (fun k w hk => by simpa using hk) (Finset.Subset.refl _) (hRR.excluded_cert b hb)
    · intro hg
      obtain ⟨v0, i0, hi0⟩ := hRR.gradeA_ev hg
      exact ⟨v0, i0, le_trans hi0 (ImplState.recvCount_le_recvMsg q1 i j m i0 _)⟩
    · intro hg
      obtain ⟨i0, hi0⟩ := hRR.gradeC_ev hg
      exact ⟨i0, le_trans hi0 (ImplState.recvCount_le_recvMsg q1 i j m i0 _)⟩
  | relay j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send (by intro w hw; exact hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | echo j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send (by intro w hw; exact hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | voteBit j b hin hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | voteBot j hin _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send
        (by intro w hw; rw [hsend] at hw; simp at hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | bindBit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send (by intro w hw; exact hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | bindBot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send (by intro w hw; exact hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bit j b hin _hlv hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send (by intro w hw; exact hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | echo5Bot j hin _hlv _hnot hcnt hval hsend =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', ?_, ?_, hRR.F_eq,
      fun b' hb' => excludedCert_send (by intro w hw; exact hw)
        (hRR.excluded_cert b' hb'),
      by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
      hRR.bound_excluded⟩
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.call_eq k
      · rw [proc_send_ne hk]
        exact hRR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        simpa using hRR.ret_eq k
      · rw [proc_send_ne hk]
        exact hRR.ret_eq k
  | byz j m hjF =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    exact ⟨q2, Or.inl ⟨rfl, System.weakLSilent_refl _ q2⟩,
      hI', hRR.call_eq, hRR.ret_eq, hRR.F_eq, hRR.excluded_cert, hRR.gradeA_ev,
      hRR.gradeC_ev, hRR.bound_excluded⟩
  | retA id v bnd _hin _hlv hcnt hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k₁, hk₁F, hbq⟩ := bind_receipts_of_echo5_quorum hRR.inv hcnt
    obtain ⟨k, hkF, hvq⟩ :=
      voteQuorum_of_bind_receipts hRR.inv (i := k₁) (v := v) (by omega)
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_A q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_excludedCert_of_voteQuorum hRR.inv hvq (hRR.excluded_cert v hv)
    have hgr : q2.grade = none ∨ q2.grade = some true := by
      have hne := grade_ne_false_of_echo5_quorum hRR hcnt
      cases hg : q2.grade with
      | none => exact Or.inl rfl
      | some gb =>
        cases gb
        · exact absurd hg hne
        · exact Or.inr rfl
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retA q2 id v v hlive hexcluded hexcluded hgr hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => excludedCert_setBound (excludedCert_ret (hRR.excluded_cert b hb)),
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setBound_proc, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setBound_proc,
            ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoQuorum_of_vote_receipts hRR.inv (i := k) (v := v) (by omega))
      refine ⟨{ q2 with excluded := insert (!v) q2.excluded, grade := some true,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetA_run hq hw hlive hd0 hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun _ => ⟨v, id, by simpa using hcnt⟩,
        fun hgf => absurd hgf (by simp),
        by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setBound_proc, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setBound_proc,
            ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact excludedCert_setBound
            (excludedCert_ret (excludedCert_of_voteQuorum hRR.inv hvq))
        · exact excludedCert_setBound (excludedCert_ret (hRR.excluded_cert b hb))
  | retB id v bnd _hin _hlv _hnotA hcnt honce hbind hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hfn := P.f_lt_n_sub_f
    obtain ⟨k, hkF, hvq⟩ := voteQuorum_of_bind_receipts hRR.inv hbind
    have hbv : v = bnd :=
      (hbnd.trans (hRR.retBound_eq hvq (boundOf_B q1.sent q1.F v))).symm
    subst hbv
    have hlive : v ∉ q2.excluded := fun hv =>
      not_excludedCert_of_voteQuorum hRR.inv hvq (hRR.excluded_cert v hv)
    have hd : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some (!v) ∨ k' ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval (!v))
    by_cases hexcluded : (!v) ∈ q2.excluded
    · refine ⟨{ q2 with ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retB q2 id v v hlive hexcluded hexcluded hd hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb => excludedCert_setBound (excludedCert_ret (hRR.excluded_cert b hb)),
        by simpa using hRR.gradeA_ev, by simpa using hRR.gradeC_ev,
        by simpa using excluded_eq_singleton hlive hexcluded⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setBound_proc, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setBound_proc,
            ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
    · have hd0 : q2.excluded = ∅ := excluded_empty_of_both hlive hexcluded
      obtain ⟨hq, hw⟩ := bindUnset_guards hRR
        (echoQuorum_of_vote_receipts hRR.inv (i := k) (v := v) (by omega))
      refine ⟨{ q2 with excluded := insert (!v) q2.excluded,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetB_run hq hw hlive hd0 hd hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_, by simpa using hRR.gradeA_ev,
        by simpa using hRR.gradeC_ev, by simp [hd0]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setBound_proc, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setBound_proc,
            ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact excludedCert_setBound
            (excludedCert_ret (excludedCert_of_voteQuorum hRR.inv hvq))
        · exact excludedCert_setBound (excludedCert_ret (hRR.excluded_cert b hb))
  | retC id bnd _hin _hlv _hnotA _hnotB hcnt hval hr hbnd =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    have hret : q2.ret id = false := by rw [hRR.ret_eq]; exact hr
    have hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some true ∨ k' ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval true)
    have hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun k' => q2.call k' = some false ∨ k' ∈ q2.F)).card :=
      hRR.spec_supp (suppI_of_valid hRR.inv hval false)
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
      have hbv : bnd = boundOf q1.sent q1.F .C := by rw [hbnd, hb]; rfl
      have hcert : ExcludedCert P q1 (!bnd) := by
        rw [hbv]; exact excludedCert_boundOf_C hRR.inv hcnt
      have hq : q2.quorum P := quorum_of_msg_quorum hRR
        (fun j hj hm' => hRR.inv.input_called j true hj hm')
        (ImplState.bothValid_le hval true)
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun k' => q2.call k' = some bnd ∨ k' ∈ q2.F)).card :=
        hRR.spec_supp (suppI_of_valid hRR.inv hval bnd)
      refine ⟨{ q2 with excluded := insert (!bnd) q2.excluded, grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, excludeThenRetC_run hq hw hex hwT hwF hgr hret⟩,
        hI', ?_, ?_, hRR.F_eq, ?_,
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simp [hex]⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setBound_proc, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setBound_proc,
            ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
      · intro b' hb'
        rw [Finset.mem_insert] at hb'
        rcases hb' with rfl | hb'
        · exact excludedCert_setBound (excludedCert_ret hcert)
        · exact excludedCert_setBound (excludedCert_ret (hRR.excluded_cert b' hb'))
    | some β =>
      -- the round has returned before: it announces the bit on record
      rw [hb, excludedOf_some] at hex
      have hbv : bnd = β := by rw [hbnd, hb]; rfl
      subst hbv
      have hmem : (!bnd) ∈ q2.excluded := by
        rw [hex]; exact Finset.mem_singleton_self _
      refine ⟨{ q2 with grade := some false,
                        ret := Function.update q2.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.retC q2 id bnd hmem hwT hwF hgr hret)⟩,
        hI', ?_, ?_, hRR.F_eq,
        fun b hb' => excludedCert_setBound (excludedCert_ret (hRR.excluded_cert b hb')),
        fun hgt => absurd hgt (by simp),
        fun _ => ⟨id, by simpa using hcnt⟩,
        by simpa using hex⟩
      · intro k'
        by_cases hk : k' = id
        · subst hk
          simpa using hRR.call_eq k'
        · rw [ImplState.setBound_proc, ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.call_eq k'
      · intro k'
        change Function.update q2.ret id true k' = _
        by_cases hk : k' = id
        · subst hk
          rw [Function.update_self]
          simp
        · rw [Function.update_of_ne hk, ImplState.setBound_proc,
            ImplState.setProc_proc_ne _ _ _ hk]
          exact hRR.ret_eq k'
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq1'
    subst hq1'
    refine ⟨q2.corrupt P id,
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp) (Step.fail q2 id)⟩,
      hI', ?_, ?_, implSpec_corrupt_F_eq hRR.F_eq id, ?_, ?_, ?_, ?_⟩
    · intro k
      rw [corrupt_call, ImplState.corrupt_proc]
      exact hRR.call_eq k
    · intro k
      rw [corrupt_ret, ImplState.corrupt_proc]
      exact hRR.ret_eq k
    · intro b hb
      rw [corrupt_excluded] at hb
      refine ExcludedCert.mono (s := q1) (fun i' j' m' hm' => ?_) (fun k w hk => ?_)
        (ImplState.corrupt_F_subset q1 id) (hRR.excluded_cert b hb)
      · rw [ImplState.corrupt_recv]
        exact hm'
      · rw [ImplState.corrupt_proc]
        exact hk
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨v0, i0, hi0⟩ := hRR.gradeA_ev hg
      exact ⟨v0, i0, by rw [ImplState.corrupt_recvCount]; exact hi0⟩
    · intro hg
      rw [corrupt_grade] at hg
      obtain ⟨i0, hi0⟩ := hRR.gradeC_ev hg
      exact ⟨i0, by rw [ImplState.corrupt_recvCount]; exact hi0⟩
    · rw [corrupt_excluded, ImplState.corrupt_bound]
      exact hRR.bound_excluded

/-! ### Broadcast compatibility of the simulation relation

The round-indexed family lift of the refinement takes `fail` as a broadcast
act, applied to every round at once. It needs the per-round relation to be
preserved by that act. The spec-side corruption projections
(`corrupt_call`/`corrupt_ret`/`corrupt_excluded`/`corrupt_grade`) come from
`ABA/GBCA/Specification.lean`; the two `corrupt` functions stay in lockstep by
`implSpec_corrupt_F_eq`. The statement is proved directly rather than through
`implRefines`, whose `fail` case only yields an existential match. Its
consumer is the round instance's family lifting (`ABA/Composition/GBCAInstanceByABDY.lean`). -/

/-- **Broadcast compatibility**: `instRel` is preserved by the synchronized
corruption of both sides. The two `corrupt`s share the guard
`id ∉ F ∧ |F| < f` and `instRel` aligns the `F`s, so the `if`-conditions
agree; every other field is untouched by corruption. -/
theorem instRel_corrupt (P : Params) (r : ℕ) (id : Fin P.n)
    {x : ImplState P.n} {y : SpecState P.n} (h : instRel P r x y) :
    instRel P r (x.corrupt P id) (y.corrupt P id) := by
  have hR : InstRel P x y := h
  exact
    { inv := hR.inv.step (ImplStep.fail (r := r) x id)
        (by rw [PMF.mem_support_pure_iff])
      call_eq := fun k => by
        rw [corrupt_call, ImplState.corrupt_proc]
        exact hR.call_eq k
      ret_eq := fun k => by
        rw [corrupt_ret, ImplState.corrupt_proc]
        exact hR.ret_eq k
      F_eq := implSpec_corrupt_F_eq hR.F_eq id
      excluded_cert := fun b hb => by
        rw [corrupt_excluded] at hb
        exact ExcludedCert.mono
          (fun i j m hm => by rw [ImplState.corrupt_recv]; exact hm)
          (fun j w hw => by rw [ImplState.corrupt_proc]; exact hw)
          (ImplState.corrupt_F_subset x id)
          (hR.excluded_cert b hb)
      gradeA_ev := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨v, i, hi⟩ := hR.gradeA_ev hg
        exact ⟨v, i, by rw [ImplState.corrupt_recvCount]; exact hi⟩
      gradeC_ev := fun hg => by
        rw [corrupt_grade] at hg
        obtain ⟨i, hi⟩ := hR.gradeC_ev hg
        exact ⟨i, by rw [ImplState.corrupt_recvCount]; exact hi⟩
      bound_excluded := by
        rw [corrupt_excluded, ImplState.corrupt_bound]
        exact hR.bound_excluded }

/-! ### Binding at the implementation instance

Binding is stated on the labels of a trace (`BindingTrace`, `ABA/GBCA/SpecificationSafety.lean`),
so a trace-distribution inclusion carries it. The inclusion is the soundness of
`implRefines`, and `safety_transfer` moves the property across it. -/

/-- The soundness inclusion of the per-instance refinement: every trace
distribution achievable by the round-`r` implementation instance is achievable
by the round-`r` specification instance. -/
theorem implInst_refines (P : Params) (r : ℕ) :
    achievableTraceDists (implInst P r) ⊆ achievableTraceDists (specInst P r) :=
  (ForwardSimulation.toProbabilistic (implInst_isLTS P r) (specInst_isLTS P r)
    (instRel_init P r) (implRefines P r)).achievableTraceDists_subset

/-- **Binding of the implementation instance, on a trace.** Every
positive-probability trace of the round-`r` implementation instance is bound to
one bit: all its round-`r` returns announce that bit, and every one of them that
hands out a value hands out it. The specification has the property
(`specInst_binding`) and `implInst_refines` includes the trace distributions. -/
theorem implInst_binding (P : Params) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (implInst P r), ∀ t, D t ≠ 0 →
      BindingTrace P r t :=
  safety_transfer (implInst_refines P r) (specInst_binding P r)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.implInst_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implInst_refines

/-- info: 'PLTS.ABA.GBCA.ByABDY.implInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implInst_binding

end GBCA.ByABDY
end ABA
end PLTS
