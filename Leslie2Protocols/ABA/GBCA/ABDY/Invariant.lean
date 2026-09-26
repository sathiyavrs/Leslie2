/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Algorithm
import Leslie2Protocols.ABA.GBCA.SpecificationSafety
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2.Results

/-!
# The inductive invariant of the round's graded-agreement composition

`Invariant P s` is the inductive invariant of the composed state a round of the protocol runs on
(`GBCA.ByABDY.RoundState`). `Invariant.initial` holds it at the initial state, and
`Invariant.step` carries it along every transition of the algorithm (`Algorithm`, ABDY22
Algorithm 6 over all five message levels, D18). `InputSupport P s b` is the `f + 1` F-blind
genuine-holder support for `b` (D15); it is monotone under every step that preserves genuine
holders and grows `F`. The counting lemmas
at the head of the file state that the any-payload `VOTE` and `BIND` counts grow under delivery and
that a corruption leaves them alone.

The invariant carries

* the corruption budget (`F_card`) and delivery soundness (`received_subset_sent`);
* protocol conformance of correct multicasts (`echo_confirmed`, `vote_input`,
  `vote_confirmed`, `bind_confirmed`, `bindBot_confirmed`, `echo5_input`, `echo5_confirmed`,
  `echo5Bot_confirmed`): each correct `ECHO`/`VOTE`/`BIND`/`ECHO5` is backed by the
  received messages that Algorithm 6 demands (the received messages only grow, so a witness once
  present persists in the current state);
* write-once recording of correct multicasts (`echo_once`, `vote_once`,
  `bind_once`, `echo5_once`): a correct process's payload is the one held in the
  sender's write-once field, so a correct process multicasts at most one payload
  per level — `echo_once` carries the unique quorum of received `ECHO` messages and `vote_once` the
  `VOTE` quorum count of the exclusion witnesses in `GBCA/ABDY/ExclusionWitness.lean`, and
  `echo5_once` the grade exclusivity;
* participation (`input_called`, D8): a correct `INPUT` sender has been
  called;
* the *budget-robust* input-origin clause (`input_origin`): for **every**
  potential corruption superset `G ⊇ F` within the budget, an `INPUT b`
  multicast by a sender outside `G` traces back to a process outside `G`
  whose own input is `b`. The quantification over `G` is what makes the
  clause inductive: the classical "first correct sender of `INPUT b` is an
  originator" argument is temporal, but a relayer's `f + 1` quorum of received messages
  always contains a sender outside `G`, so the pre-state clause — already
  quantified over the same `G` — supplies the witness, and corruption steps
  only shrink the range of `G`;
* the first-relayer support clause (`input_support`, D15): a correct
  `INPUT b` multicast is by a genuine holder of `b` or already witnesses
  `f + 1` F-blind genuine-holder support (`InputSupport`) — inductive because
  the senders of the first correct relayer's `f + 1` received `INPUT b` messages are each in
  `F` or genuine holders, and the count is monotone under every step.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

/-! ### The counting lemmas: any-payload monotonicity and derivation variants -/

/-- Deliveries only grow the any-payload `VOTE` count. -/
theorem RoundState.voteCount_le_receiveMessage {n : ℕ} (s : RoundState n)
    (i j : Fin n) (m : Message) (i' : Fin n) :
    s.voteCount i' ≤ (s.receiveMessage i j m).voteCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, RoundState.mem_receiveMessage_received.mpr (Or.inr hv)⟩

/-- Deliveries only grow the any-payload `BIND` count. -/
theorem RoundState.bindCount_le_receiveMessage {n : ℕ} (s : RoundState n)
    (i j : Fin n) (m : Message) (i' : Fin n) :
    s.bindCount i' ≤ (s.receiveMessage i j m).bindCount i' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  obtain ⟨v, hv⟩ := hk.2
  exact ⟨hk.1, v, RoundState.mem_receiveMessage_received.mpr (Or.inr hv)⟩

/-- Corruption is blind to the any-payload `VOTE` count. -/
theorem RoundState.corrupt_voteCount {P : Parameters} (s : RoundState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).voteCount i = s.voteCount i := by
  unfold RoundState.voteCount
  rw [RoundState.corrupt_received]

/-- Corruption is blind to the any-payload `BIND` count. -/
theorem RoundState.corrupt_bindCount {P : Parameters} (s : RoundState P.n)
    (id : Fin P.n) (i : Fin P.n) :
    (s.corrupt P id).bindCount i = s.bindCount i := by
  unfold RoundState.bindCount
  rw [RoundState.corrupt_received]

/-- Any-payload analogue of `exists_sender_notMem` at the `BIND` level: a
`bindCount` exceeding `|G|` yields a sender outside `G` together with its
payload. -/
theorem RoundState.exists_bind_sender_notMem {P : Parameters} {s : RoundState P.n}
    (G : Finset (Fin P.n)) {i : Fin P.n} (h : G.card < s.bindCount i) :
    ∃ j w, j ∉ G ∧ Message.bind w ∈ s.received i j := by
  unfold RoundState.bindCount at h
  obtain ⟨j, hjQ, hjG⟩ := RoundState.exists_correct_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  obtain ⟨w, hw⟩ := hjQ.2
  exact ⟨j, w, hjG, hw⟩

/-! ### The concrete inductive invariant -/

variable {P : Parameters}

/-- `f + 1` F-blind genuine-holder support for `b` (D15): the composed state's counterpart of the
spec guards' InputSupport counts — the simulation relation of
`GBCA/ABDY/SpecificationRelation.lean` reads the count at the specification along
`call_eq`/`F_eq`. -/
def InputSupport (P : Parameters) (s : RoundState P.n) (b : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter
    (fun id => (s.processVariables id).input = some b ∨ id ∈ s.F)).card

/-- The support count is monotone: it survives any step that preserves
genuine holders and grows `F`. -/
theorem InputSupport.mono {s s' : RoundState P.n} {b : Bool}
    (hproc : ∀ id, (s.processVariables id).input = some b → (s'.processVariables id).input = some b)
    (hF : s.F ⊆ s'.F) (h : InputSupport P s b) : InputSupport P s' b := by
  unfold InputSupport at h ⊢
  refine le_trans h (Finset.card_le_card fun id hid => ?_)
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hproc id) (fun hm => hF hm)⟩

/-- The inductive invariant of the composed state a round runs on. See the
module docstring for the role of each clause. -/
structure Invariant (P : Parameters) (s : RoundState P.n) : Prop where
  /-- Corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivery soundness: everything delivered was multicast. -/
  received_subset_sent : ∀ i j m, m ∈ s.received i j → m ∈ s.sent j
  /-- Correct `ECHO b` is backed by an `n − f` quorum of received `INPUT b` messages. -/
  echo_confirmed : ∀ j b, j ∉ s.F → Message.echo b ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.input b)
  /-- Correct `ECHO` multicasts are recorded in the write-once `sentEcho`
  field; in particular a correct process echoes at most one payload. -/
  echo_once : ∀ j b, j ∉ s.F → Message.echo b ∈ s.sent j →
    (s.processVariables j).sentEcho = some b
  /-- Correct voters hold an input (D8). -/
  vote_input : ∀ j w, j ∉ s.F → Message.vote w ∈ s.sent j → (s.processVariables j).input ≠ none
  /-- Correct `VOTE b` is backed by an `n − f` quorum of received `ECHO b` messages. -/
  vote_confirmed : ∀ j b, j ∉ s.F → Message.vote (some b) ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.echo b)
  /-- Correct `VOTE` multicasts are recorded in the write-once `sentVote`
  field; this is the level the exclusion witnesses of
  `GBCA/ABDY/ExclusionWitness.lean` count. -/
  vote_once : ∀ j w, j ∉ s.F → Message.vote w ∈ s.sent j →
    (s.processVariables j).sentVote = some w
  /-- Correct `BIND` multicasts are recorded in the write-once `sentBind`
  field; in particular a correct process multicasts at most one payload. -/
  bind_once : ∀ j w, j ∉ s.F → Message.bind w ∈ s.sent j →
    (s.processVariables j).sentBind = some w
  /-- Correct `BIND b` is backed by an `n − f` quorum of received `VOTE b` messages. -/
  bind_confirmed : ∀ j b, j ∉ s.F → Message.bind (some b) ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.vote (some b))
  /-- Correct `BIND ⊥` is backed by `n − f` received any-payload `VOTE` messages. -/
  bindBot_confirmed : ∀ j, j ∉ s.F → Message.bind none ∈ s.sent j →
    P.n - P.f ≤ s.voteCount j
  /-- Correct `ECHO5` senders hold an input (D8, one level up). -/
  echo5_input : ∀ j w, j ∉ s.F → Message.echo5 w ∈ s.sent j → (s.processVariables j).input ≠ none
  /-- Correct `ECHO5` multicasts are recorded in the write-once `sentEcho5` field; this is the level
  that carries the grade-2/grade-0 exclusivity. -/
  echo5_once : ∀ j w, j ∉ s.F → Message.echo5 w ∈ s.sent j →
    (s.processVariables j).sentEcho5 = some w
  /-- Correct `ECHO5 b` is backed by an `n − f` quorum of received `BIND b` messages. -/
  echo5_confirmed : ∀ j b, j ∉ s.F → Message.echo5 (some b) ∈ s.sent j →
    P.n - P.f ≤ s.receivedCount j (.bind (some b))
  /-- Correct `ECHO5 ⊥` is backed by `n − f` received any-payload `BIND` messages. -/
  echo5Bot_confirmed : ∀ j, j ∉ s.F → Message.echo5 none ∈ s.sent j →
    P.n - P.f ≤ s.bindCount j
  /-- Budget-robust input origin: for every corruption superset `G` within
  the budget, an `INPUT b` multicast outside `G` traces back to an input `b`
  outside `G`. -/
  input_origin : ∀ (b : Bool) (G : Finset (Fin P.n)), s.F ⊆ G → G.card ≤ P.f →
    ∀ j, j ∉ G → Message.input b ∈ s.sent j →
    ∃ m, m ∉ G ∧ (s.processVariables m).input = some b
  /-- Relayer-inductivized first-relayer support (D15): a correct `INPUT b`
  multicast is by a genuine holder of `b`, or witnesses the `f + 1` F-blind
  genuine-holder support outright — the senders of the first correct relayer's
  `f + 1` received `INPUT b` messages are each in `F` or genuine holders. -/
  input_support : ∀ (b : Bool) (j : Fin P.n), j ∉ s.F → Message.input b ∈ s.sent j →
    (s.processVariables j).input = some b ∨ InputSupport P s b
  /-- Participation one level down (D8): a correct `INPUT` sender has been
  called. -/
  input_called : ∀ j b, j ∉ s.F → Message.input b ∈ s.sent j →
    (s.processVariables j).input ≠ none

theorem Invariant.initial (P : Parameters) : Invariant P (RoundState.initial P.n) where
  F_card := by
    simp [RoundState.initial]
  received_subset_sent := fun i j m h => absurd h (by simp [RoundState.initial])
  echo_confirmed := fun j b _ h => absurd h (by simp [RoundState.initial])
  echo_once := fun j b _ h => absurd h (by simp [RoundState.initial])
  vote_input := fun j w _ h => absurd h (by simp [RoundState.initial])
  vote_confirmed := fun j b _ h => absurd h (by simp [RoundState.initial])
  vote_once := fun j w _ h => absurd h (by simp [RoundState.initial])
  bind_once := fun j w _ h => absurd h (by simp [RoundState.initial])
  bind_confirmed := fun j b _ h => absurd h (by simp [RoundState.initial])
  bindBot_confirmed := fun j _ h => absurd h (by simp [RoundState.initial])
  echo5_input := fun j w _ h => absurd h (by simp [RoundState.initial])
  echo5_once := fun j w _ h => absurd h (by simp [RoundState.initial])
  echo5_confirmed := fun j b _ h => absurd h (by simp [RoundState.initial])
  echo5Bot_confirmed := fun j _ h => absurd h (by simp [RoundState.initial])
  input_origin := fun b G _ _ j _ h => absurd h (by simp [RoundState.initial])
  input_support := fun b j _ h => absurd h (by simp [RoundState.initial])
  input_called := fun j b _ h => absurd h (by simp [RoundState.initial])

/-- Derivation (D15): any count of `f + 1` received `INPUT b` messages yields the F-blind
genuine-holder support — some correct non-holder sender's `input_support` clause
closes, or else every sender is a holder-or-`F`-member and the senders
themselves witness the count. -/
theorem Invariant.support_of_received_inputs {s : RoundState P.n} (hI : Invariant P s)
    {i : Fin P.n} {b : Bool} (h : P.f + 1 ≤ s.receivedCount i (.input b)) :
    InputSupport P s b := by
  by_cases hc : ∃ k, Message.input b ∈ s.received i k ∧ k ∉ s.F ∧ (s.processVariables k).input ≠
    some b
  · obtain ⟨k, hkr, hkF, hkin⟩ := hc
    rcases hI.input_support b k hkF (hI.received_subset_sent i k _ hkr) with h' | h'
    · exact absurd h' hkin
    · exact h'
  · push Not at hc
    unfold RoundState.receivedCount at h
    unfold InputSupport
    refine le_trans h (Finset.card_le_card fun k hk => ?_)
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    by_cases hkF : k ∈ s.F
    · exact Or.inr hkF
    · exact Or.inl (hc k hk.2 hkF)

/-- The sender's `setProcessVariables` in a send step does not affect other processes. -/
theorem processVariables_send_ne {s : RoundState P.n} {j : Fin P.n} {p : ProcessVariables}
    {m : Message} {k : Fin P.n} (hk : k ≠ j) :
    ((s.setProcessVariables j p).multicast j m).processVariables k = s.processVariables k := by
  rw [RoundState.multicast_processVariables, RoundState.setProcessVariables_processVariables_ne _ _
    _ hk]

/-- **Invariant preservation, correct-send schema.** Process `j` updates its
local state to `p` and multicasts `m`. The hypotheses collect, clause by
clause, what the new message and the touched field must satisfy; every condition on a field the
send leaves alone is discharged here once for all nine send transitions (`call`, `relay`,
`echo`, `voteBit`, `voteBot`, `bindBit`, `bindBot`, `echo5Bit`, `echo5Bot`). -/
private theorem Invariant.send {s : RoundState P.n} (hI : Invariant P s) {j : Fin P.n}
    {p : ProcessVariables} {m : Message}
    (hpne : p.input ≠ none)
    (hpmono : ∀ b, (s.processVariables j).input = some b → p.input = some b)
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
    (hEchoO : ((∀ b, m ≠ .echo b) ∧ p.sentEcho = (s.processVariables j).sentEcho) ∨
      (∃ b, m = .echo b ∧ p.sentEcho = some b ∧ (s.processVariables j).sentEcho = none))
    (hVoteO : ((∀ w, m ≠ .vote w) ∧ p.sentVote = (s.processVariables j).sentVote) ∨
      (∃ w, m = .vote w ∧ p.sentVote = some w ∧ (s.processVariables j).sentVote = none))
    (hBindO : ((∀ w, m ≠ .bind w) ∧ p.sentBind = (s.processVariables j).sentBind) ∨
      (∃ w, m = .bind w ∧ p.sentBind = some w ∧ (s.processVariables j).sentBind = none))
    (hEcho5O : ((∀ w, m ≠ .echo5 w) ∧ p.sentEcho5 = (s.processVariables j).sentEcho5) ∨
      (∃ w, m = .echo5 w ∧ p.sentEcho5 = some w ∧ (s.processVariables j).sentEcho5 = none)) :
    Invariant P ((s.setProcessVariables j p).multicast j m) := by
  have htrans : ∀ (b : Bool) (k : Fin P.n), (s.processVariables k).input = some b →
      (((s.setProcessVariables j p).multicast j m).processVariables k).input = some b := by
    intro b k hk
    by_cases hkj : k = j
    · subst hkj
      rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      exact hpmono b hk
    · rw [processVariables_send_ne hkj]
      exact hk
  refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- received_subset_sent
    intro i' j' m' hm'
    rw [RoundState.multicast_received, RoundState.setProcessVariables_received] at hm'
    exact RoundState.sent_subset_multicast _ _ _ _ (hI.received_subset_sent i' j' m' hm')
  · -- echo_conf
    intro j' b hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEchoC b heq.symm
    · simpa using hI.echo_confirmed j' b hF hold
  · -- echo_once
    intro j' b hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      rcases hEchoO with ⟨hne, _⟩ | ⟨b₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne b)
      · rw [hm0] at heq
        injection heq with hb
        rw [hpe, hb]
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        have hbase := hI.echo_once j' b hF hold
        rcases hEchoO with ⟨_, hpe⟩ | ⟨b₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [processVariables_send_ne hkj]
        exact hI.echo_once j' b hF hold
  · -- vote_input
    intro j' w hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        exact hpne
      · rw [processVariables_send_ne hkj]
        exact hI.vote_input j' w hF hold
  · -- vote_conf
    intro j' b hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hVoteC b heq.symm
    · simpa using hI.vote_confirmed j' b hF hold
  · -- vote_once
    intro j' w hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      rcases hVoteO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        have hbase := hI.vote_once j' w hF hold
        rcases hVoteO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [processVariables_send_ne hkj]
        exact hI.vote_once j' w hF hold
  · -- bind_once
    intro j' w hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      rcases hBindO with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        have hbase := hI.bind_once j' w hF hold
        rcases hBindO with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [processVariables_send_ne hkj]
        exact hI.bind_once j' w hF hold
  · -- bind_conf
    intro j' b hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hBindC b heq.symm
    · simpa using hI.bind_confirmed j' b hF hold
  · -- bindBot_conf
    intro j' hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hBindBotC heq.symm
    · simpa using hI.bindBot_confirmed j' hF hold
  · -- echo5_input
    intro j' w hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        exact hpne
      · rw [processVariables_send_ne hkj]
        exact hI.echo5_input j' w hF hold
  · -- echo5_once
    intro j' w hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      rcases hEcho5O with ⟨hne, _⟩ | ⟨w₀, hm0, hpe, _⟩
      · exact absurd heq.symm (hne w)
      · rw [hm0] at heq
        injection heq with hw
        rw [hpe, hw]
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        have hbase := hI.echo5_once j' w hF hold
        rcases hEcho5O with ⟨_, hpe⟩ | ⟨w₀, _, _, hnone⟩
        · rw [hpe]; exact hbase
        · rw [hnone] at hbase; exact absurd hbase (by simp)
      · rw [processVariables_send_ne hkj]
        exact hI.echo5_once j' w hF hold
  · -- echo5_conf
    intro j' b hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEcho5C b heq.symm
    · simpa using hI.echo5_confirmed j' b hF hold
  · -- echo5Bot_conf
    intro j' hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · simpa using hEcho5BotC heq.symm
    · simpa using hI.echo5Bot_confirmed j' hF hold
  · -- input_origin
    intro b G hFG hGc j' hjG hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · refine ⟨j', hjG, ?_⟩
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        exact hp
      · have hcnt' : G.card < s.receivedCount j' (Message.input b) := by omega
        obtain ⟨k, hkG, hkr⟩ := RoundState.exists_sender_notMem G hcnt'
        obtain ⟨m0, hmG, hmi⟩ :=
          hI.input_origin b G hFG hGc k hkG (hI.received_subset_sent j' k _ hkr)
        exact ⟨m0, hmG, htrans b m0 hmi⟩
    · obtain ⟨m0, hmG, hmi⟩ := hI.input_origin b G hFG hGc j' hjG hold
      exact ⟨m0, hmG, htrans b m0 hmi⟩
  · -- input_supp
    intro b j' hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, heq⟩ | hold
    · rcases hInp b heq.symm with hp | hcnt
      · left
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        exact hp
      · right
        exact InputSupport.mono (fun k hk => htrans b k hk) (fun _ hh => hh)
          (hI.support_of_received_inputs hcnt)
    · rcases hI.input_support b j' hF hold with hin | hsupp
      · left
        by_cases hkj : j' = j
        · subst hkj
          rw [RoundState.multicast_processVariables,
            RoundState.setProcessVariables_processVariables_self]
          exact hpmono b hin
        · rw [processVariables_send_ne hkj]
          exact hin
      · right
        exact InputSupport.mono (fun k hk => htrans b k hk) (fun _ hh => hh) hsupp
  · -- input_called
    intro j' b hF hm'
    rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
    · rw [RoundState.multicast_processVariables,
        RoundState.setProcessVariables_processVariables_self]
      exact hpne
    · by_cases hkj : j' = j
      · subst hkj
        rw [RoundState.multicast_processVariables,
          RoundState.setProcessVariables_processVariables_self]
        exact hpne
      · rw [processVariables_send_ne hkj]
        exact hI.input_called j' b hF hold

/-- **Invariant preservation, one process's own variables.** A `setProcessVariables` that keeps
the input and all four write-once fields (the return transitions, which flip only
`returned`) preserves every clause. -/
private theorem Invariant.setProcessVariables_unchanged {s : RoundState P.n} (hI : Invariant P s)
    {id : Fin P.n} {p : ProcessVariables}
    (h1 : p.input = (s.processVariables id).input)
    (h2 : p.sentEcho = (s.processVariables id).sentEcho)
    (h3 : p.sentVote = (s.processVariables id).sentVote)
    (h4 : p.sentBind = (s.processVariables id).sentBind)
    (h5 : p.sentEcho5 = (s.processVariables id).sentEcho5) :
    Invariant P (s.setProcessVariables id p) := by
  have hin : ∀ k, ((s.setProcessVariables id p).processVariables k).input = (s.processVariables
    k).input := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [RoundState.setProcessVariables_processVariables_self, h1]
    · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
  have hech : ∀ k, ((s.setProcessVariables id p).processVariables k).sentEcho = (s.processVariables
    k).sentEcho := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [RoundState.setProcessVariables_processVariables_self, h2]
    · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
  have hvot : ∀ k, ((s.setProcessVariables id p).processVariables k).sentVote = (s.processVariables
    k).sentVote := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [RoundState.setProcessVariables_processVariables_self, h3]
    · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
  have hbin : ∀ k, ((s.setProcessVariables id p).processVariables k).sentBind = (s.processVariables
    k).sentBind := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [RoundState.setProcessVariables_processVariables_self, h4]
    · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
  have hsea : ∀ k, ((s.setProcessVariables id p).processVariables k).sentEcho5 = (s.processVariables
    k).sentEcho5 := by
    intro k
    by_cases hk : k = id
    · subst hk; rw [RoundState.setProcessVariables_processVariables_self, h5]
    · rw [RoundState.setProcessVariables_processVariables_ne _ _ _ hk]
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

/-- **The invariant is preserved by the bound bit's write.** The ghost write touches the network
state's own field alone, and no clause of `Invariant` reads it. -/
private theorem Invariant.setBound {s : RoundState P.n} (hI : Invariant P s) (β : Bool) :
    Invariant P (s.setBound β) := { hI with }

/-- **Invariant preservation.** `Invariant` is preserved by every transition of the
algorithm. -/
theorem Invariant.step {r : ℕ} {s : RoundState P.n} {l : Label P.n}
    {μ : PMF (RoundState P.n)} {s' : RoundState P.n} (hI : Invariant P s)
    (hstep : Algorithm P r s l μ) (hs' : s' ∈ μ.support) : Invariant P s' := by
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
      rcases RoundState.mem_receiveMessage_received.mp hm' with ⟨rfl, rfl, rfl⟩ | hold
      · exact hsent
      · exact hI.received_subset_sent i' j' m' hold
    · intro j' b hF hm'
      exact le_trans (hI.echo_confirmed j' b hF hm')
        (RoundState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.vote_confirmed j' b hF hm')
        (RoundState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' b hF hm'
      exact le_trans (hI.bind_confirmed j' b hF hm')
        (RoundState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.bindBot_confirmed j' hF hm')
        (RoundState.voteCount_le_receiveMessage s i j m j')
    · intro j' b hF hm'
      exact le_trans (hI.echo5_confirmed j' b hF hm')
        (RoundState.receivedCount_le_receiveMessage s i j m j' _)
    · intro j' hF hm'
      exact le_trans (hI.echo5Bot_confirmed j' hF hm')
        (RoundState.bindCount_le_receiveMessage s i j m j')
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
      rcases RoundState.mem_multicast_sent.mp hm' with ⟨rfl, _⟩ | hold
      · exact absurd (hFG hjF) hjG
      · exact hold
    have hs := fun j' m' (hF : j' ∉ s.F) =>
      hsentG s.F (Finset.Subset.refl _) j' m' hF
    refine ⟨hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      exact RoundState.sent_subset_multicast _ _ _ _ (hI.received_subset_sent i' j' m' hm')
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
    exact hI.setProcessVariables_unchanged rfl rfl rfl rfl rfl
  | retGrade1 id v bnd _hin _hlv _hnotGrade2 hcnt honce hbind hval hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Invariant.setBound ?_ bnd
    exact hI.setProcessVariables_unchanged rfl rfl rfl rfl rfl
  | retGrade0 id bnd _hin _hlv _hnotGrade2 _hnotGrade1 hcnt hval hr _hbnd =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine Invariant.setBound ?_ bnd
    exact hI.setProcessVariables_unchanged rfl rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hsub := RoundState.corrupt_F_subset s id
    have hFtr : ∀ j' : Fin P.n, j' ∉ (s.corrupt P id).F → j' ∉ s.F :=
      fun j' hF hj => hF (hsub hj)
    refine ⟨RoundState.corrupt_card_le s id hI.F_card, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' j' m' hm'
      rw [RoundState.corrupt_received] at hm'
      rw [RoundState.corrupt_sent]
      exact hI.received_subset_sent i' j' m' hm'
    · intro j' b hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_receivedCount]
      exact hI.echo_confirmed j' b (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.echo_once j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.vote_input j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_receivedCount]
      exact hI.vote_confirmed j' b (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.vote_once j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.bind_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_receivedCount]
      exact hI.bind_confirmed j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_voteCount]
      exact hI.bindBot_confirmed j' (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.echo5_input j' w (hFtr j' hF) hm'
    · intro j' w hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.echo5_once j' w (hFtr j' hF) hm'
    · intro j' b hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_receivedCount]
      exact hI.echo5_confirmed j' b (hFtr j' hF) hm'
    · intro j' hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_bindCount]
      exact hI.echo5Bot_confirmed j' (hFtr j' hF) hm'
    · intro b G hFG hGc j' hjG hm'
      rw [RoundState.corrupt_sent] at hm'
      obtain ⟨m0, hmG, hmi⟩ :=
        hI.input_origin b G (Finset.Subset.trans hsub hFG) hGc j' hjG hm'
      exact ⟨m0, hmG, by rw [RoundState.corrupt_processVariables]; exact hmi⟩
    · intro b j' hF' hm'
      rw [RoundState.corrupt_sent] at hm'
      rcases hI.input_support b j' (hFtr j' hF') hm' with hin | hsupp
      · left
        rw [RoundState.corrupt_processVariables]
        exact hin
      · right
        refine InputSupport.mono (s := s) (fun k hk => ?_) hsub hsupp
        rw [RoundState.corrupt_processVariables]
        exact hk
    · intro j' b hF hm'
      rw [RoundState.corrupt_sent] at hm'
      rw [RoundState.corrupt_processVariables]
      exact hI.input_called j' b (hFtr j' hF) hm'

end GBCA.ByABDY
end ABA
end PLTS
