/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.Specification

/-!
# The GBCA implementation instance (ABDY22 Algorithm 6)

The round-`r` instance of the Graded Binding Crusader Agreement protocol, as an
LTS over the shared alphabet `ABA.Label n`.

*Attribution.* The file transcribes ABDY22's Algorithm 6 — the 6-round Graded
Binding Crusader Agreement for Byzantine faults — directly. The level mapping is

```
INPUT = echo,  ECHO = echo2,  VOTE = echo3,  BIND = echo4,  ECHO5 = echo5
```

and the three returns are the decide conditions of lines 23–29.

Each process runs the message pattern

* `INPUT b` — multicast on being called; relayed after `f + 1` receipts; * `ECHO b` — multicast once
`INPUT b` was received from `n − f` senders
  (which also puts `b` into the derived set `Valid`);
* `VOTE v` (`v ∈ {0,1,⊥}`) — a real bit after an `n − f` `ECHO b` quorum, `⊥`
  after `n − f` `ECHO`s of any payload with `|Valid| > 1`;
* `BIND v` — the same pattern one level up, over `VOTE`s; * `ECHO5 v` — the same pattern one level
up again, over `BIND`s;
* return — grade `2` at `b` after an `n − f` `ECHO5 b` quorum, grade `1` at `b` after an
  `n − f` any-`ECHO5` quorum containing `b` with `f + 1` `BIND b`s and
  `|Valid| > 1`, and grade `0` after an `n − f` `ECHO5 ⊥` quorum with `|Valid| > 1`.

Every transition is Dirac; asynchrony and Byzantine behaviour are modelled
by nondeterministic `τ`-transitions.

## Why the cited algorithm and not the blueprint's `alg:GBCA` (D18)

* **D18 (the five message levels).** This is a deviation from the source
  blueprint's `alg:GBCA`, which presents a **4-round compression** of
  Algorithm 6: the `echo5` round is elided, the decide conditions read one level
  down, and the grade-1 evidence is `f + 1` `VOTE v` where Algorithm 6 has
  `t + 1` `echo4 v`. The compression violates the paper's Graded Binding. One
  process held before its `ECHO` through a grade-0 decision can afterwards
  direct its write-once echo at either bit, and one corruption completes
  `f + 1` `VOTE v` for the bit of the adversary's choice — so two extensions of
  a single grade-0 return hand out two different bits. The encoding therefore
  follows the cited algorithm rather than the blueprint's compression; the
  upstream blueprint carries a matching red annotation.

The grade-1 evidence is what the depth buys. `f + 1` `BIND v` receipts exceed
the corruption budget, so they guarantee a correct `BIND v` sender, whose own
wait-condition is an `n − f` `VOTE v` receipt quorum over the write-once `VOTE`
level — and that quorum is the object the paper's binding argument counts
(Lemmas 4.8/4.9 through E.9).

*Transcription note.* The prose preceding Algorithm 6 says "upon receiving
`echo4` messages from `2t + 1` parties" where the pseudocode's lines 19–20 say
`n − t`; the two coincide only at `n = 3t + 1`. The encoding follows the
pseudocode (`n − f`).

## Model and deviations (continuing the project's D1–D4)

* **D1 (determinised `fail`).** As in the spec instance, corruption is the total Dirac function
  `ImplementationState.corrupt` — `F` stays equal to every other component under the `fail`
  broadcast.
* **D5 (set-based network).** Multicasts are idempotent: each sender owns a
  *set* `sent j` of messages it has multicast, and `received i j` is the set of
  messages from `j` that the adversary has delivered to `i` (`deliver` is a
  `τ`-transition requiring `m ∈ sent j`). Thresholds count *distinct senders*
  in the receiver's delivered sets, so message duplication and point-to-point
  scheduling are absorbed into the set model. A corrupted sender may inject
  any message into its `sent` set (`byzantine`).
* **D8 (participation guard).** Protocol sends (`relay`, `echo`, `vote*`,
  `bind*`, `echo5*`) and the three returns require the process to have received
  its input (`input ≠ none`): the algorithm's handlers only run inside a called
  instance. The send rows are taken in the wait-until order of Algorithm 6
  from the `BIND` level down: each of those rules requires the process's own
  send at the level below. The `VOTE` rules ask for no own send, the `ECHO`
  they read being sent by an `upon` handler that may still be pending. The
  return rules carry the negations that the algorithm's if/else chain implies.

The state is exactly the protocol's own data, held in two halves: each process keeps its own local
state beside the messages delivered to it, and the round's network state keeps the per-sender sent
sets and the corrupted set. `ImplementationState` is their pair, so the network is a component of
the state and not a field of it — a weaker network is a different second component and leaves the
rest of the round alone. The three return transitions are cases (1), (2), (3) of Algorithm 6's lines
23–29: case (1) an `n − f` `ECHO5 v` quorum, case (2) an `n − f` any-`ECHO5` quorum containing
`ECHO5 v` together with `f + 1` `BIND v`s and `|Valid| > 1`, case (3) an `n − f` `ECHO5 ⊥` quorum
with `|Valid| > 1`. Beside the receipts of its own case, each return reads the receipts named by the
cases above it in the chain, the process's own `ECHO5` field, and the call record. The binding and
grade information that the specification tracks is an abstraction of these receipt patterns and
lives only on the specification; the refinement (`GBCA/ABDY/RefinesSpecification.lean`) supplies it
from the receipts.

## The round's bound bit

The specification announces a bound bit on every return label (`ABA/GBCA/Specification.lean`).
The implementation announces one too, and holds it in the write-once field
`GBCA.ByABDY.NetworkState.bound` of the round's network state. The field is a ghost: it is
auxiliary state, no program reads it, and the three return rows are the only
rows that touch it.

`boundOf` computes the bit from the round's sent sets, the corrupted set and the
outcome. A return of outcome `out` announces `bound.getD (boundOf sent F out)` —
the bit already on record if the round has returned before, and `boundOf`'s
otherwise — and writes it back, so the round announces one bit on all of its
returns. The three return rows are otherwise the rows of Algorithm 6 unchanged:
the announced bit enters no guard of the algorithm and no field a program holds.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

/-- The five message levels of Algorithm 6. `VOTE`, `BIND` and `ECHO5` may
carry the non-bit payload `⊥` (`none`). -/
inductive Message : Type
  /-- `⟨INPUT, b⟩`. -/
  | input (b : Bool)
  /-- `⟨ECHO, b⟩`. -/
  | echo (b : Bool)
  /-- `⟨VOTE, v⟩` with `v ∈ {0, 1, ⊥}`. -/
  | vote (v : Option Bool)
  /-- `⟨BIND, v⟩` with `v ∈ {0, 1, ⊥}`. -/
  | bind (v : Option Bool)
  /-- `⟨echo5, v⟩` with `v ∈ {0, 1, ⊥}` (Algorithm 6 lines 21–22). -/
  | echo5 (v : Option Bool)
  deriving DecidableEq

/-- **The round's bound bit**, as a function of the round's messages. It is the
bit a return of outcome `out` announces on its label.

A value-bearing outcome announces the value it hands out. An outcome carrying no
value announces the payload of a correct `⟨VOTE, b⟩` sender, and `true` where
there is none. A correct `⟨VOTE, b⟩` sender holds an `n − f` `⟨ECHO, b⟩`
receipt quorum and at most one bit carries such a quorum, so on a reachable
state the two bit branches are exclusive and the order in which they are read
is immaterial. Where neither branch applies no bit is ever handed out, and the
announced bit is the surviving one of a round that hands out nothing.

The bit is a ghost output: no program reads it, and the three return rows are
the only rows that read it. -/
def boundOf {n : ℕ} (sent : Fin n → Finset Message) (F : Finset (Fin n)) :
    GBCAOutput → Bool
  | .grade2 v => v
  | .grade1 v => v
  | .grade0 =>
      if ∃ k, k ∉ F ∧ Message.vote (some true) ∈ sent k then true
      else if ∃ k, k ∉ F ∧ Message.vote (some false) ∈ sent k then false
      else true

@[simp] theorem boundOf_grade2 {n : ℕ} (sent : Fin n → Finset Message) (F : Finset (Fin n))
    (v : Bool) : boundOf sent F (.grade2 v) = v := rfl

@[simp] theorem boundOf_grade1 {n : ℕ} (sent : Fin n → Finset Message) (F : Finset (Fin n))
    (v : Bool) : boundOf sent F (.grade1 v) = v := rfl

theorem boundOf_grade0 {n : ℕ} (sent : Fin n → Finset Message) (F : Finset (Fin n)) :
    boundOf sent F .grade0 =
      if ∃ k, k ∉ F ∧ Message.vote (some true) ∈ sent k then true
      else if ∃ k, k ∉ F ∧ Message.vote (some false) ∈ sent k then false
      else true := rfl

/-- The local state of one process in one GBCA instance. -/
structure ProcessRecord : Type where
  /-- The input bit received via `callG` (`none` before the call). -/
  input : Option Bool
  /-- Which `INPUT` payloads this process has multicast (own input or relay). -/
  sentInput : Bool → Bool
  /-- The `ECHO` payload multicast, if any (write-once). -/
  sentEcho : Option Bool
  /-- The `VOTE` payload multicast, if any (write-once; payload may be `⊥`). -/
  sentVote : Option (Option Bool)
  /-- The `BIND` payload multicast, if any (write-once; payload may be `⊥`). -/
  sentBind : Option (Option Bool)
  /-- The `ECHO5` (`echo5`) payload multicast, if any (write-once; payload may
  be `⊥`). -/
  sentEcho5 : Option (Option Bool)
  /-- Whether this process has returned. -/
  returned : Bool
  deriving DecidableEq

/-- The initial local state: nothing received, nothing sent. -/
def ProcessRecord.initial : ProcessRecord where
  input := none
  sentInput := fun _ => false
  sentEcho := none
  sentVote := none
  sentBind := none
  sentEcho5 := none
  returned := false

/-! ### The two halves of a round's state

The data of one round sits in two records. Each process holds its own protocol
state together with the messages delivered to it, and nothing else — there is
no record there of what it has multicast. The round's network state holds the
per-sender sent sets and the corrupted set. The instance's state below is their
pair, so every field of the algorithm is a field of one local state or the other.

The network state carries the name of the instance that composes it beside the
programs (`ABA/Composition/GBCAInstanceByABDY/Instance.lean`). -/

/-- The round record of one process: its own local state and the messages delivered to it, indexed
by sender. There is no record of what it has sent — the sender's sent lives in the network. -/
structure RoundRecord (n : ℕ) : Type where
  /-- The process's own protocol state. -/
  process : ProcessRecord
  /-- `received k` — the messages from sender `k` delivered here. -/
  received : Fin n → Finset Message
  deriving DecidableEq

namespace RoundRecord

variable {n : ℕ}

/-- The initial round record: nothing received, nothing done. -/
def initial (n : ℕ) : RoundRecord n where
  process := ProcessRecord.initial
  received := fun _ => ∅

/-- The number of distinct senders from which this process has received `m`. -/
def receivedCount (p : RoundRecord n) (m : Message) : ℕ :=
  (Finset.univ.filter (fun k => m ∈ p.received k)).card

/-- The number of distinct senders of some received `ECHO`. -/
def echoCount (p : RoundRecord n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ b, Message.echo b ∈ p.received k)).card

/-- The number of distinct senders of some received `VOTE`. -/
def voteCount (p : RoundRecord n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Message.vote v ∈ p.received k)).card

/-- The number of distinct senders of some received `BIND`. -/
def bindCount (p : RoundRecord n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Message.bind v ∈ p.received k)).card

/-- The number of distinct senders of some received `ECHO5`. -/
def echo5Count (p : RoundRecord n) : ℕ :=
  (Finset.univ.filter (fun k => ∃ v, Message.echo5 v ∈ p.received k)).card

/-- Both bits are backed by an `n − f` `INPUT` quorum among the delivered
messages. -/
def bothValid (P : Parameters) (p : RoundRecord P.n) : Prop :=
  P.n - P.f ≤ p.receivedCount (.input true) ∧ P.n - P.f ≤ p.receivedCount (.input false)

/-- Overwrite the local record. -/
def setProcess (p : RoundRecord n) (pr : ProcessRecord) : RoundRecord n := { p with process := pr }

/-- File `m` under the recv row of sender `k`. -/
def deliverTo (p : RoundRecord n) (k : Fin n) (m : Message) : RoundRecord n :=
  { p with received := Function.update p.received k (insert m (p.received k)) }

end RoundRecord


/-- The state of the round's network: the per-sender sent sets and the
corrupted set. -/
structure NetworkState (n : ℕ) : Type where
  /-- `sent j` — the messages process `j` has multicast in this round (D5). -/
  sent : Fin n → Finset GBCA.ByABDY.Message
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- The round's bound bit, `none` before the round's first return. A ghost:
  no program reads it, it is written at the first return of the round and
  announced on every return of the round. -/
  bound : Option Bool
  deriving DecidableEq

namespace NetworkState

variable {n : ℕ}

/-- The initial network state: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) : NetworkState n where
  sent := fun _ => ∅
  F := ∅
  bound := none

/-- Sent `m` under sender `j` (D5). -/
def recordGBCASend (w : NetworkState n) (j : Fin n) (m : GBCA.ByABDY.Message) : NetworkState n :=
  { w with sent := Function.update w.sent j (insert m (w.sent j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. It is not a row
of any rule table — the family applies it to every round's network at once. -/
def corrupt (P : Parameters) (id : Fin P.n) (w : NetworkState P.n) : NetworkState P.n :=
  if id ∉ w.F ∧ w.F.card < P.f then { w with F := insert id w.F } else w

/-- The round's bound bit is written: the network state records `β`. -/
def setBound (w : NetworkState n) (β : Bool) : NetworkState n := { w with bound := some β }

@[simp] theorem recordGBCASend_F (w : NetworkState n) (j : Fin n) (m : GBCA.ByABDY.Message) :
    (w.recordGBCASend j m).F = w.F := rfl

@[simp] theorem recordGBCASend_bound (w : NetworkState n) (j : Fin n) (m : GBCA.ByABDY.Message) :
    (w.recordGBCASend j m).bound = w.bound := rfl

@[simp] theorem setBound_sent (w : NetworkState n) (β : Bool) :
    (w.setBound β).sent = w.sent := rfl

@[simp] theorem setBound_F (w : NetworkState n) (β : Bool) :
    (w.setBound β).F = w.F := rfl

@[simp] theorem setBound_bound (w : NetworkState n) (β : Bool) :
    (w.setBound β).bound = some β := rfl

@[simp] theorem corrupt_bound {P : Parameters} (w : NetworkState P.n) (id : Fin P.n) :
    (w.corrupt P id).bound = w.bound := by
  unfold corrupt; split <;> rfl

@[simp] theorem corrupt_sent {P : Parameters} (w : NetworkState P.n) (id : Fin P.n) :
    (w.corrupt P id).sent = w.sent := by
  unfold corrupt; split <;> rfl

/-- Membership in a sent after a multicast. -/
theorem mem_recordGBCASend {w : NetworkState n} {j : Fin n} {m : GBCA.ByABDY.Message} {k : Fin n}
    {m' : GBCA.ByABDY.Message} :
    m' ∈ (w.recordGBCASend j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ w.sent k := by
  change m' ∈ Function.update w.sent j (insert m (w.sent j)) k ↔ _
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Finset.mem_insert]
    simp
  · rw [Function.update_of_ne hk]
    simp [hk]

end NetworkState


/-- **The state of one GBCA implementation instance**: the `n` round records beside the round's
network state. -/
abbrev ImplementationState (n : ℕ) : Type := (∀ _ : Fin n,
  RoundRecord n) × GBCA.ByABDY.NetworkState n

namespace ImplementationState

variable {n : ℕ}

/-- Per-process local states. -/
def process (s : ImplementationState n) : Fin n → ProcessRecord := fun j => (s.1 j).process

/-- `sent j` — the messages process `j` has multicast (D5). -/
def sent (s : ImplementationState n) : Fin n → Finset Message := s.2.sent

/-- `received i j` — the messages from sender `j` delivered to receiver `i`. -/
def received (s : ImplementationState n) : Fin n → Fin n → Finset Message := fun i => (s.1
  i).received

/-- The corrupted set (the network state's, kept equal by `fail` broadcast). -/
def F (s : ImplementationState n) : Finset (Fin n) := s.2.F

/-- The round's bound bit (the network state's). A ghost: no rule but the three
returns reads it, and no program holds it. -/
def bound (s : ImplementationState n) : Option Bool := s.2.bound

/-- The round's bound bit is written: the network state records `β`. -/
def setBound (s : ImplementationState n) (β : Bool) : ImplementationState n := (s.1, s.2.setBound β)

@[simp] theorem process_apply (u : ∀ _ : Fin n, RoundRecord n) (w : GBCA.ByABDY.NetworkState n)
    (j : Fin n) : process (u, w) j = (u j).process := rfl
@[simp] theorem sent_apply (u : ∀ _ : Fin n, RoundRecord n) (w : GBCA.ByABDY.NetworkState n) :
    sent (u, w) = w.sent := rfl
@[simp] theorem received_apply (u : ∀ _ : Fin n, RoundRecord n) (w : GBCA.ByABDY.NetworkState n)
    (i : Fin n) : received (u, w) i = (u i).received := rfl
@[simp] theorem F_apply (u : ∀ _ : Fin n, RoundRecord n) (w : GBCA.ByABDY.NetworkState n) :
    F (u, w) = w.F := rfl
@[simp] theorem bound_apply (u : ∀ _ : Fin n, RoundRecord n) (w : GBCA.ByABDY.NetworkState n) :
    bound (u, w) = w.bound := rfl
@[simp] theorem setBound_apply (u : ∀ _ : Fin n, RoundRecord n) (w : GBCA.ByABDY.NetworkState n)
    (β : Bool) : setBound (u, w) β = (u, w.setBound β) := rfl

/-! The bound-bit write touches the network state's own field alone, so every
other projection of the round passes through it. -/

@[simp] theorem setBound_process (s : ImplementationState n) (β : Bool) :
    (s.setBound β).process = s.process := rfl
@[simp] theorem setBound_received (s : ImplementationState n) (β : Bool) :
    (s.setBound β).received = s.received := rfl
@[simp] theorem setBound_sent (s : ImplementationState n) (β : Bool) :
    (s.setBound β).sent = s.sent := rfl
@[simp] theorem setBound_F (s : ImplementationState n) (β : Bool) :
    (s.setBound β).F = s.F := rfl
@[simp] theorem setBound_bound (s : ImplementationState n) (β : Bool) :
    (s.setBound β).bound = some β := rfl

/-- Dot notation resolves against `ImplementationState`, so the rule table and the
refinement read the pair in the four names the algorithm uses. -/
example (s : ImplementationState n) (i j : Fin n) : s.received i j = (s.1 i).received j := rfl

/-- The initial implementation state. -/
def initial (n : ℕ) : ImplementationState n :=
  (fun _ => RoundRecord.initial n, GBCA.ByABDY.NetworkState.initial n)

/-! The two components' own initial states project componentwise, so unfolding
`initial` leaves no residue. -/

@[simp] theorem _root_.PLTS.ABA.GBCA.ByABDY.RoundRecord.initial_process (n : ℕ) :
    (RoundRecord.initial n).process = ProcessRecord.initial := rfl
@[simp] theorem _root_.PLTS.ABA.GBCA.ByABDY.RoundRecord.initial_received (n : ℕ) (k : Fin n) :
    (RoundRecord.initial n).received k = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.GBCA.ByABDY.NetworkState.initial_sent (n : ℕ) (j : Fin n) :
    (GBCA.ByABDY.NetworkState.initial n).sent j = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.GBCA.ByABDY.NetworkState.initial_F (n : ℕ) :
    (GBCA.ByABDY.NetworkState.initial n).F = ∅ := rfl

@[simp] theorem initial_process (j : Fin n) : (initial n).process j = ProcessRecord.initial := rfl
@[simp] theorem initial_sent (j : Fin n) : (initial n).sent j = ∅ := rfl
@[simp] theorem initial_received (i j : Fin n) : (initial n).received i j = ∅ := rfl
@[simp] theorem initial_F : (initial n).F = ∅ := rfl
@[simp] theorem initial_bound : (initial n).bound = none := rfl

/-- The number of distinct senders from which `i` has received `m`. -/
def receivedCount (s : ImplementationState n) (i : Fin n) (m : Message) : ℕ :=
  (Finset.univ.filter (fun j => m ∈ s.received i j)).card

/-- The number of distinct senders from which `i` has received some `ECHO`. -/
def echoCount (s : ImplementationState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ b, Message.echo b ∈ s.received i j)).card

/-- The number of distinct senders from which `i` has received some `VOTE`. -/
def voteCount (s : ImplementationState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ v, Message.vote v ∈ s.received i j)).card

/-- The number of distinct senders from which `i` has received some `BIND`. -/
def bindCount (s : ImplementationState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ v, Message.bind v ∈ s.received i j)).card

/-- The number of distinct senders from which `i` has received some `ECHO5`. -/
def echo5Count (s : ImplementationState n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => ∃ v, Message.echo5 v ∈ s.received i j)).card

/-- `Valid = {0, 1}` at process `i`: both bits are backed by an `n − f`
`INPUT` quorum among `i`'s delivered messages. -/
def bothValid (P : Parameters) (s : ImplementationState P.n) (i : Fin P.n) : Prop :=
  P.n - P.f ≤ s.receivedCount i (.input true) ∧ P.n - P.f ≤ s.receivedCount i (.input false)

/-- Both bits of a `bothValid` evidence, indexed by the bit. -/
theorem bothValid_le {P : Parameters} {s : ImplementationState P.n} {i : Fin P.n}
    (h : s.bothValid P i) (b : Bool) : P.n - P.f ≤ s.receivedCount i (.input b) := by
  cases b
  · exact h.2
  · exact h.1

/-! ### State update helpers -/

/-- Update the local state of process `j`. -/
def setProcess (s : ImplementationState n) (j : Fin n) (p : ProcessRecord) : ImplementationState n
  :=
  (Function.update s.1 j ((s.1 j).setProcess p), s.2)

@[simp] theorem setProcess_sent (s : ImplementationState n) (j : Fin n) (p : ProcessRecord) :
    (s.setProcess j p).sent = s.sent := rfl
@[simp] theorem setProcess_F (s : ImplementationState n) (j : Fin n) (p : ProcessRecord) :
    (s.setProcess j p).F = s.F := rfl

@[simp] theorem setProcess_received (s : ImplementationState n) (j : Fin n) (p : ProcessRecord) :
    (s.setProcess j p).received = s.received := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [setProcess, received, RoundRecord.setProcess]
  · simp [setProcess, received, Function.update_of_ne hi]

@[simp] theorem setProcess_process_self (s : ImplementationState n) (j : Fin n)
  (p : ProcessRecord) :
    (s.setProcess j p).process j = p := by
  simp [setProcess, process, RoundRecord.setProcess]

theorem setProcess_process_ne (s : ImplementationState n) (j : Fin n) (p : ProcessRecord)
    {k : Fin n} (h : k ≠ j) : (s.setProcess j p).process k = s.process k := by
  simp [setProcess, process, Function.update_of_ne h]

/-! A record write leaves every projection of the delivered sets alone. -/

@[simp] theorem setProcess_receivedCount (s : ImplementationState n) (j : Fin n) (p : ProcessRecord)
    (i : Fin n) (m : Message) : (s.setProcess j p).receivedCount i m = s.receivedCount i m := by
  simp [receivedCount, setProcess_received]
@[simp] theorem setProcess_echoCount (s : ImplementationState n) (j : Fin n) (p : ProcessRecord)
    (i : Fin n) : (s.setProcess j p).echoCount i = s.echoCount i := by
  simp [echoCount, setProcess_received]
@[simp] theorem setProcess_voteCount (s : ImplementationState n) (j : Fin n) (p : ProcessRecord)
    (i : Fin n) : (s.setProcess j p).voteCount i = s.voteCount i := by
  simp [voteCount, setProcess_received]
@[simp] theorem setProcess_bindCount (s : ImplementationState n) (j : Fin n) (p : ProcessRecord)
    (i : Fin n) : (s.setProcess j p).bindCount i = s.bindCount i := by
  simp [bindCount, setProcess_received]
@[simp] theorem setProcess_echo5Count (s : ImplementationState n) (j : Fin n) (p : ProcessRecord)
    (i : Fin n) : (s.setProcess j p).echo5Count i = s.echo5Count i := by
  simp [echo5Count, setProcess_received]
@[simp] theorem setProcess_bothValid {P : Parameters} (s : ImplementationState P.n) (j : Fin P.n)
    (p : ProcessRecord) (i : Fin P.n) :
    (s.setProcess j p).bothValid P i ↔ s.bothValid P i := by
  simp [bothValid]

/-- Process `j` multicasts `m`: the network state records it under `j`. -/
def multicast (s : ImplementationState n) (j : Fin n) (m : Message) : ImplementationState n :=
  (s.1, s.2.recordGBCASend j m)

@[simp] theorem multicast_process (s : ImplementationState n) (j : Fin n) (m : Message) :
    (s.multicast j m).process = s.process := rfl
@[simp] theorem multicast_received (s : ImplementationState n) (j : Fin n) (m : Message) :
    (s.multicast j m).received = s.received := rfl
@[simp] theorem multicast_F (s : ImplementationState n) (j : Fin n) (m : Message) :
    (s.multicast j m).F = s.F := rfl

/-! A multicast is the network state's write alone, so no projection of the delivered
sets moves. -/

@[simp] theorem multicast_receivedCount (s : ImplementationState n) (j : Fin n) (m : Message)
    (i : Fin n) (m' : Message) : (s.multicast j m).receivedCount i m' = s.receivedCount i m' := rfl
@[simp] theorem multicast_echoCount (s : ImplementationState n) (j : Fin n) (m : Message) (i : Fin
  n) :
    (s.multicast j m).echoCount i = s.echoCount i := rfl
@[simp] theorem multicast_voteCount (s : ImplementationState n) (j : Fin n) (m : Message) (i : Fin
  n) :
    (s.multicast j m).voteCount i = s.voteCount i := rfl
@[simp] theorem multicast_bindCount (s : ImplementationState n) (j : Fin n) (m : Message) (i : Fin
  n) :
    (s.multicast j m).bindCount i = s.bindCount i := rfl
@[simp] theorem multicast_echo5Count (s : ImplementationState n) (j : Fin n) (m : Message) (i : Fin
  n) :
    (s.multicast j m).echo5Count i = s.echo5Count i := rfl
@[simp] theorem multicast_bothValid {P : Parameters} (s : ImplementationState P.n) (j : Fin P.n)
    (m : Message) (i : Fin P.n) : (s.multicast j m).bothValid P i ↔ s.bothValid P i := Iff.rfl

/-- Membership in a sent set after a multicast. -/
theorem mem_multicast_sent {s : ImplementationState n} {j : Fin n} {m : Message} {k : Fin n}
    {m' : Message} : m' ∈ (s.multicast j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.sent k := by
  change m' ∈ (s.2.recordGBCASend j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.2.sent k
  exact GBCA.ByABDY.NetworkState.mem_recordGBCASend

theorem sent_subset_multicast (s : ImplementationState n) (j : Fin n) (m : Message) (k : Fin n) :
    s.sent k ⊆ (s.multicast j m).sent k :=
  fun _ h => mem_multicast_sent.mpr (Or.inr h)

/-- The adversary delivers `m` from sender `j` to receiver `i`: the receiver's round record files it
under `j`'s row. -/
def receiveMessage (s : ImplementationState n) (i j : Fin n) (m : Message) : ImplementationState n
  :=
  (Function.update s.1 i ((s.1 i).deliverTo j m), s.2)

@[simp] theorem receiveMessage_sent (s : ImplementationState n) (i j : Fin n) (m : Message) :
    (s.receiveMessage i j m).sent = s.sent := rfl
@[simp] theorem receiveMessage_F (s : ImplementationState n) (i j : Fin n) (m : Message) :
    (s.receiveMessage i j m).F = s.F := rfl

@[simp] theorem receiveMessage_process (s : ImplementationState n) (i j : Fin n) (m : Message) :
    (s.receiveMessage i j m).process = s.process := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [receiveMessage, process, RoundRecord.deliverTo]
  · simp [receiveMessage, process, Function.update_of_ne hk]

/-- Membership in a delivered set after a delivery. -/
theorem mem_receiveMessage_received {s : ImplementationState n} {i j : Fin n} {m : Message}
    {i' j' : Fin n} {m' : Message} :
    m' ∈ (s.receiveMessage i j m).received i' j' ↔
      (i' = i ∧ j' = j ∧ m' = m) ∨ m' ∈ s.received i' j' := by
  by_cases hi : i' = i
  · subst hi
    change m' ∈ (Function.update s.1 i' ((s.1 i').deliverTo j m) i').received j' ↔ _
    rw [Function.update_self]
    change m' ∈ Function.update ((s.1 i').received) j (insert m ((s.1 i').received j)) j' ↔ _
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self, Finset.mem_insert]
      simp [received]
    · rw [Function.update_of_ne hj]
      simp [hj, received]
  · change m' ∈ (Function.update s.1 i ((s.1 i).deliverTo j m) i').received j' ↔ _
    rw [Function.update_of_ne hi]
    simp [hi, received]

/-- Deliveries only grow the receiver counts. -/
theorem receivedCount_le_receiveMessage (s : ImplementationState n) (i j : Fin n) (m : Message)
    (i' : Fin n) (m' : Message) :
    s.receivedCount i' m' ≤ (s.receiveMessage i j m).receivedCount i' m' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, mem_receiveMessage_received.mpr (Or.inr hk.2)⟩

/-- Corruption (deviation D1): total, Dirac, equal to the spec's, and the network state's own row —
the round records are corruption-blind. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : ImplementationState P.n) : ImplementationState P.n
  :=
  (s.1, GBCA.ByABDY.NetworkState.corrupt P id s.2)

@[simp] theorem corrupt_process {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n) :
    (s.corrupt P id).process = s.process := rfl
@[simp] theorem corrupt_received {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n) :
    (s.corrupt P id).received = s.received := rfl
@[simp] theorem corrupt_receivedCount {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n)
    (i : Fin P.n) (m : Message) :
    (s.corrupt P id).receivedCount i m = s.receivedCount i m := rfl
@[simp] theorem corrupt_sent {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n) :
    (s.corrupt P id).sent = s.sent := by
  unfold corrupt sent GBCA.ByABDY.NetworkState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. `F` is the one field corruption
writes, and the budget guard sits in the network state, so the statement is made here
rather than reached by unfolding. Not a simp lemma: it introduces an `ite`. -/
theorem corrupt_F {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold corrupt F GBCA.ByABDY.NetworkState.corrupt
  split_ifs <;> rfl

/-! The bound-bit write moves no projection of the round. -/

@[simp] theorem setBound_receivedCount (s : ImplementationState n) (β : Bool) (i : Fin n)
    (m : Message) :
    (s.setBound β).receivedCount i m = s.receivedCount i m := rfl
@[simp] theorem setBound_echoCount (s : ImplementationState n) (β : Bool) (i : Fin n) :
    (s.setBound β).echoCount i = s.echoCount i := rfl
@[simp] theorem setBound_voteCount (s : ImplementationState n) (β : Bool) (i : Fin n) :
    (s.setBound β).voteCount i = s.voteCount i := rfl
@[simp] theorem setBound_bindCount (s : ImplementationState n) (β : Bool) (i : Fin n) :
    (s.setBound β).bindCount i = s.bindCount i := rfl
@[simp] theorem setBound_echo5Count (s : ImplementationState n) (β : Bool) (i : Fin n) :
    (s.setBound β).echo5Count i = s.echo5Count i := rfl
@[simp] theorem setBound_bothValid {P : Parameters} (s : ImplementationState P.n) (β : Bool)
    (i : Fin P.n) : (s.setBound β).bothValid P i ↔ s.bothValid P i := Iff.rfl

/-! The bound bit is written by no rule but the three returns. -/

@[simp] theorem setProcess_bound (s : ImplementationState n) (j : Fin n) (p : ProcessRecord) :
    (s.setProcess j p).bound = s.bound := rfl
@[simp] theorem multicast_bound (s : ImplementationState n) (j : Fin n) (m : Message) :
    (s.multicast j m).bound = s.bound := rfl
@[simp] theorem receiveMessage_bound (s : ImplementationState n) (i j : Fin n) (m : Message) :
    (s.receiveMessage i j m).bound = s.bound := rfl
@[simp] theorem corrupt_bound {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n) :
    (s.corrupt P id).bound = s.bound := GBCA.ByABDY.NetworkState.corrupt_bound s.2 id

theorem corrupt_F_subset {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n) :
    s.F ⊆ (s.corrupt P id).F := by
  rw [corrupt_F]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le {P : Parameters} (s : ImplementationState P.n) (id : Fin P.n)
    (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  rw [corrupt_F]
  split
  · next hc =>
    have h2 := hc.2
    have h3 := Finset.card_insert_le id s.F
    omega
  · exact hF

/-! ### Quorum counting -/

/-- A set strictly larger than `F` has a member outside `F`. -/
theorem exists_correct_of_card_lt {Q F : Finset (Fin n)} (h : F.card < Q.card) :
    ∃ j ∈ Q, j ∉ F := by
  by_contra hc
  refine absurd (Finset.card_le_card fun j hj => ?_) (not_le.mpr h)
  by_contra hjF
  exact hc ⟨j, hj, hjF⟩

/-- A receipt count exceeding `|G|` yields a sender outside `G`. -/
theorem exists_sender_notMem {P : Parameters} {s : ImplementationState P.n} (G : Finset (Fin P.n))
    {i : Fin P.n} {m : Message} (h : G.card < s.receivedCount i m) :
    ∃ j, j ∉ G ∧ m ∈ s.received i j := by
  unfold receivedCount at h
  obtain ⟨j, hjQ, hjF⟩ := exists_correct_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  exact ⟨j, hjF, hjQ.2⟩

/-- Two `n − f` receipt quorums (at possibly different receivers) share an
correct sender: `(n−f) + (n−f) − n = n − 2f > f ≥ |F|`. -/
theorem exists_correct_received_of_two_quorums {P : Parameters} {s : ImplementationState P.n}
    (hF : s.F.card ≤ P.f) {i i' : Fin P.n} {m m' : Message} (h : P.n - P.f ≤ s.receivedCount i m)
    (h' : P.n - P.f ≤ s.receivedCount i' m') :
    ∃ j, j ∉ s.F ∧ m ∈ s.received i j ∧ m' ∈ s.received i' j := by
  unfold receivedCount at h h'
  have hcard := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun j => m ∈ s.received i j))
    (Finset.univ.filter (fun j => m' ∈ s.received i' j))
  have hun : ((Finset.univ.filter (fun j => m ∈ s.received i j)) ∪
      (Finset.univ.filter (fun j => m' ∈ s.received i' j))).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hResilience
  have hlt : s.F.card < ((Finset.univ.filter (fun j => m ∈ s.received i j)) ∩
      (Finset.univ.filter (fun j => m' ∈ s.received i' j))).card := by
        omega
  obtain ⟨j, hj, hjF⟩ := exists_correct_of_card_lt hlt
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hjF, hj.1.2, hj.2.2⟩

end ImplementationState

/-- The step relation of the round-`r` GBCA implementation instance
(ABDY22 Algorithm 6, all five message levels). All transitions are Dirac. -/
inductive ImplementationStep (P : Parameters) (r : ℕ) :
    ImplementationState P.n → Label P.n → PMF (ImplementationState P.n) → Prop
  /-- The environment call arrives: record the input and multicast
  `⟨INPUT, b⟩`. -/
  | call (s : ImplementationState P.n) (id : Fin P.n) (b : Bool)
      (h : (s.process id).input = none) :
      ImplementationStep P r s (.callG r id b)
        (PMF.pure ((s.setProcess id { s.process id with
            input := some b,
            sentInput := Function.update (s.process id).sentInput b true }).multicast
          id (.input b)))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : ImplementationState P.n) (id : Fin P.n) (b : Bool) :
      ImplementationStep P r s (.callG r id b) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : ImplementationState P.n) (i j : Fin P.n) (m : Message) (h : m ∈ s.sent j) :
      ImplementationStep P r s .tau (PMF.pure (s.receiveMessage i j m))
  /-- `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩`, not yet multicast. -/
  | relay (s : ImplementationState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.process j).input ≠ none)
      (hcnt : P.f + 1 ≤ s.receivedCount j (.input b))
      (hsend : (s.process j).sentInput b = false) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with
            sentInput := Function.update (s.process j).sentInput b true }).multicast
          j (.input b)))
  /-- `ECHO`: an `n − f` `INPUT b` quorum puts `b` into `Valid` and, if no
  `ECHO` was sent yet, multicasts `⟨ECHO, b⟩`. -/
  | echo (s : ImplementationState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.process j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.input b))
      (hsend : (s.process j).sentEcho = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentEcho := some b }).multicast
          j (.echo b)))
  /-- `VOTE b` (wait case (a)): an `n − f` `ECHO b` quorum. The vote reads the
  `ECHO` quorum received. The process's own `ECHO` is sent by one of the
  algorithm's `upon` handlers and may still be pending, so no own-send
  condition applies here. The wait-until order is carried from the `BIND` level
  down. -/
  | voteBit (s : ImplementationState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.process j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.echo b))
      (hsend : (s.process j).sentVote = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentVote := some (some b) }).multicast
          j (.vote (some b))))
  /-- `VOTE ⊥` (wait case (b)): `n − f` `ECHO`s of any payload and
  `|Valid| > 1`, and no single-bit `ECHO` quorum is on record. The vote reads
  the `ECHO` quorum received. The process's own `ECHO` is sent by one of the
  algorithm's `upon` handlers and may still be pending, so no own-send
  condition applies here. The wait-until order is carried from the `BIND` level
  down. -/
  | voteBot (s : ImplementationState P.n) (j : Fin P.n)
      (hin : (s.process j).input ≠ none)
      (hnot : ∀ b, s.receivedCount j (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.echoCount j)
      (hval : s.bothValid P j)
      (hsend : (s.process j).sentVote = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentVote := some none }).multicast
          j (.vote none)))
  /-- `BIND b` (wait case (a)): an `n − f` `VOTE b` quorum, the process's own
  `VOTE` already out. -/
  | bindBit (s : ImplementationState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.process j).input ≠ none)
      (hlv : (s.process j).sentVote ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.vote (some b)))
      (hsend : (s.process j).sentBind = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentBind := some (some b) }).multicast
          j (.bind (some b))))
  /-- `BIND ⊥` (wait case (b)): `n − f` `VOTE`s of any payload and
  `|Valid| > 1`, the process's own `VOTE` already out, and no single-bit
  `VOTE` quorum is on record. -/
  | bindBot (s : ImplementationState P.n) (j : Fin P.n)
      (hin : (s.process j).input ≠ none)
      (hlv : (s.process j).sentVote ≠ none)
      (hnot : ∀ b, s.receivedCount j (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.voteCount j)
      (hval : s.bothValid P j)
      (hsend : (s.process j).sentBind = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentBind := some none }).multicast
          j (.bind none)))
  /-- `ECHO5 b` (wait case (a)): an `n − f` `BIND b` quorum, the process's own
  `BIND` already out. -/
  | echo5Bit (s : ImplementationState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.process j).input ≠ none)
      (hlv : (s.process j).sentBind ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.bind (some b)))
      (hsend : (s.process j).sentEcho5 = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentEcho5 := some (some b) }).multicast
          j (.echo5 (some b))))
  /-- `ECHO5 ⊥` (wait case (b)): `n − f` `BIND`s of any payload and
  `|Valid| > 1`, the process's own `BIND` already out, and no single-bit
  `BIND` quorum is on record. -/
  | echo5Bot (s : ImplementationState P.n) (j : Fin P.n)
      (hin : (s.process j).input ≠ none)
      (hlv : (s.process j).sentBind ≠ none)
      (hnot : ∀ b, s.receivedCount j (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.bindCount j)
      (hval : s.bothValid P j)
      (hsend : (s.process j).sentEcho5 = none) :
      ImplementationStep P r s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentEcho5 := some none }).multicast
          j (.echo5 none)))
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byzantine (s : ImplementationState P.n) (j : Fin P.n) (m : Message) (h : j ∈ s.F) :
      ImplementationStep P r s .tau (PMF.pure (s.multicast j m))
  /-- Grade-2 return (decide case (1)): an `n − f` `ECHO5 v` quorum. The process
  has called and its own `ECHO5` is out. Case (1) heads the chain, so there is
  no higher case to deny. -/
  | retGrade2 (s : ImplementationState P.n) (id : Fin P.n) (v : Bool) (bnd : Bool)
      (hin : (s.process id).input ≠ none)
      (hlv : (s.process id).sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 (some v)))
      (hr : (s.process id).returned = false)
      (hbnd : bnd = s.bound.getD (boundOf s.sent s.F (.grade2 v))) :
      ImplementationStep P r s (.retG r id (.grade2 v) bnd)
        (PMF.pure ((s.setProcess id { s.process id with returned := true }).setBound bnd))
  /-- Grade-1 return (decide case (2)): an `n − f` any-`ECHO5` quorum containing
  `ECHO5 v`, `f + 1` `BIND v`s and `|Valid| > 1`. The `f + 1` `BIND v` receipts
  put a correct `BIND v` sender — hence an `n − f` `VOTE v` receipt quorum —
  behind every grade-1 output. The process has called, its own `ECHO5` is out,
  and no higher case holds: `hnotGrade2` denies case (1) at either bit. -/
  | retGrade1 (s : ImplementationState P.n) (id : Fin P.n) (v : Bool) (bnd : Bool)
      (hin : (s.process id).input ≠ none)
      (hlv : (s.process id).sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, s.receivedCount id (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.echo5Count id)
      (honce : ∃ k, Message.echo5 (some v) ∈ s.received id k)
      (hbind : P.f + 1 ≤ s.receivedCount id (.bind (some v)))
      (hval : s.bothValid P id)
      (hr : (s.process id).returned = false)
      (hbnd : bnd = s.bound.getD (boundOf s.sent s.F (.grade1 v))) :
      ImplementationStep P r s (.retG r id (.grade1 v) bnd)
        (PMF.pure ((s.setProcess id { s.process id with returned := true }).setBound bnd))
  /-- Grade-0 return (decide case (3)): an `n − f` `ECHO5 ⊥` quorum and
  `|Valid| > 1`. The process has called, its own `ECHO5` is out, and no higher
  case holds: `hnotGrade2` denies case (1) at either bit, and `hnotGrade1` denies
  case (2). The denial of case (2) is carried in reduced form. Case (2) asks
  for four things at a bit `v`: an `n − f` any-`ECHO5` quorum, a received
  `ECHO5 v`, `f + 1` `BIND v` receipts, and `|Valid| > 1`. This row's own
  `hcnt` and `hval` already supply the first and the last, an `n − f`
  `ECHO5 ⊥` quorum being in particular an `n − f` any-`ECHO5` quorum. What is
  left to deny is the pair of the received `ECHO5 v` and the `f + 1` `BIND v`
  receipts, which is what `hnotGrade1` states. -/
  | retGrade0 (s : ImplementationState P.n) (id : Fin P.n) (bnd : Bool)
      (hin : (s.process id).input ≠ none)
      (hlv : (s.process id).sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, s.receivedCount id (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, Message.echo5 (some v) ∈ s.received id k) →
        s.receivedCount id (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 none))
      (hval : s.bothValid P id)
      (hr : (s.process id).returned = false)
      (hbnd : bnd = s.bound.getD (boundOf s.sent s.F .grade0)) :
      ImplementationStep P r s (.retG r id .grade0 bnd)
        (PMF.pure ((s.setProcess id { s.process id with returned := true }).setBound bnd))
  /-- Corruption (deviation D1). -/
  | fail (s : ImplementationState P.n) (id : Fin P.n) :
      ImplementationStep P r s (.fail id) (PMF.pure (s.corrupt P id))

/-- The round-`r` GBCA implementation instance. -/
noncomputable def implementation (P : Parameters) (r : ℕ) :
    System (ImplementationState P.n) (Label P.n) where
  init := ImplementationState.initial P.n
  step := ImplementationStep P r

@[simp] theorem implementation_init (P : Parameters) (r : ℕ) :
    (implementation P r).init = ImplementationState.initial P.n := rfl

@[simp] theorem implementation_step (P : Parameters) (r : ℕ) (s : ImplementationState P.n)
    (l : Label P.n) (μ : PMF (ImplementationState P.n)) :
    (implementation P r).step s l μ ↔ ImplementationStep P r s l μ := Iff.rfl

/-- Every transition of the implementation instance is Dirac: the instance is
an LTS. -/
theorem implementation_isLTS (P : Parameters) (r : ℕ) : (implementation P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end GBCA.ByABDY
end ABA
end PLTS
