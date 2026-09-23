/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.MessagesAndRecords

/-!
# The GBCA implementation instance (ABDY22 Algorithm 6)

The round-`r` instance of the Graded Binding Crusader Agreement protocol, as an LTS over the
shared alphabet `ABA.Label n`: the algorithm `ImplementationStep`, one transition per line of
ABDY22's Algorithm 6, and the system `implementation` it is the step relation of. The messages it
exchanges and the state it runs on are in `GBCA/ABDY/MessagesAndRecords.lean`.

*Attribution.* The file transcribes ABDY22's Algorithm 6 — the 6-round Graded Binding Crusader
Agreement for Byzantine faults — directly, under the level mapping

```
INPUT = echo,  ECHO = echo2,  VOTE = echo3,  BIND = echo4,  ECHO5 = echo5
```

and the three returns are the decide conditions of lines 23–29.

Each process runs the message pattern

* `INPUT b` — multicast on being called; relayed after `f + 1` receipts;
* `ECHO b` — multicast once `INPUT b` was received from `n − f` senders
  (which also puts `b` into the derived set `Valid`);
* `VOTE v` (`v ∈ {0,1,⊥}`) — a real bit after an `n − f` `ECHO b` quorum, `⊥`
  after `n − f` `ECHO`s of any payload with `|Valid| > 1`;
* `BIND v` — the same pattern one level up, over `VOTE`s;
* `ECHO5 v` — the same pattern one level up again, over `BIND`s;
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

## The algorithm

* **D8 (participation guard).** The protocol sends (`relay`, `echo`, `vote*`,
  `bind*`, `echo5*`) and the three returns require the process to have received
  its input (`input ≠ none`): the algorithm's handlers only run inside a called
  instance. The send transitions are taken in the wait-until order of Algorithm 6
  from the `BIND` level down: each of those transitions requires the process's own
  send at the level below. The `VOTE` transitions ask for no own send, the `ECHO`
  they read being sent by an `upon` handler that may still be pending. The
  return transitions carry the negations that the algorithm's if/else chain implies.
* **D1 (determinised `fail`).** The `fail` transition is `ImplementationState.corrupt`, the total
  Dirac function of `GBCA/ABDY/MessagesAndRecords.lean`.
* **D5 (set-based network).** `deliver` moves a message from a sender's sent set into a
  receiver's delivered set and does not consume it, and `byzantine` lets a corrupted sender
  multicast anything at any time.

The three return transitions are cases (1), (2), (3) of Algorithm 6's lines 23–29: case (1) an
`n − f` `ECHO5 v` quorum, case (2) an `n − f` any-`ECHO5` quorum containing `ECHO5 v` together
with `f + 1` `BIND v`s and `|Valid| > 1`, case (3) an `n − f` `ECHO5 ⊥` quorum with
`|Valid| > 1`. Beside the receipts of its own case, each return reads the receipts named by the
cases above it in the chain, the process's own `ECHO5` field, and the call record. The binding and
grade information that the specification tracks is an abstraction of these receipt patterns and
lives only on the specification; the simulation relation
(`GBCA/ABDY/SpecificationRelation.lean`) supplies it from the receipts.

Each return also announces the round's bound bit (D29): the label carries
`bound.getD (boundOf sent F out)`, the bit on record if the round has returned before and
`boundOf`'s otherwise, and the transition writes it back to `NetworkState.bound`. The three
returns are otherwise the returns of Algorithm 6 unchanged: the announced bit enters no guard of
the algorithm and no field a program holds.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

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
