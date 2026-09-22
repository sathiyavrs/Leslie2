/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.GBCA.ABDY.RefinesSpecification
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The round's graded-agreement instance

One round of the protocol, taken apart into the pieces that run it:
`n` corruption-blind local programs, one per process, beside the round's own
network. The instance is the unit the analysis replaces by the graded
agreement specification, so it is drawn to be exactly what that replacement
may see — the round's handshake ports and nothing else.

A local program holds one round record: the process's own protocol data and the messages delivered
to it, indexed by sender (`GBCA.ByABDY.RoundRecord`). It holds no corrupted set, no corruption flag
and no record of what it has multicast; its guards read the record and the recv, never the identity
of the caller. The round loop that moves the ports is not here either — a call writes the round
record alone, a return sets the record's `returned` flag alone.

The round's network holds the per-sender sent sets and the corrupted set.
A multicast is a joint step of the sender, which writes its record, and the
network, which records the message; a delivery is a joint step of the network,
which checks that the message is sent under the named sender, and the
receiver, which files it under that sender's recv row.

The two rendezvous — the multicast and the delivery — are labels of the instance-internal alphabet
`GBCALabel n = ExtendedLabel n ⊕ GBCAEvent n`, and they are hidden before anything outside sees the
instance: `composition` speaks the shared extended alphabet `ExtendedLabel n`, in which the round's
interface is `callG r`, `retG r`, `gbcaCallLoop r` and the three Byzantine graded-agreement rows of
round `r`. The round-multicast and round-delivery constructors of `NetworkEvent` are therefore not
part of that interface — no component offers them, so they carry no transition of the instance.

`gbcaInstanceFamily` is the ℕ-indexed family of these instances: `System.family`
routes a round-tagged label to its round, takes `τ` at any round, and
broadcasts `fail` to every round at once.

## Model and deviations

* **D1 (determinised `fail`).** `NetworkState.corrupt` is the total Dirac function guarded by `k ∉ F
  ∧ |F| < f`. `fail` is not a row of any rule table here: it is the family's broadcast act, applied
  to every round's network simultaneously, which is what keeps the per-round copies of the corrupted
  set together.
* **D5 (set-based network).** Multicasts are idempotent: `sent j` is the set
  of messages `j` has multicast in this round, and `received k` at a program is
  the set of messages from `k` delivered there. Thresholds count distinct
  senders. A corrupted sender's injections enter its sent through the
  network's own `byzantineGBCA` transition.
* **D8 (participation guard).** The protocol sends and the three returns
  require the record to have received its input: the algorithm's handlers only
  run inside a called instance.
* **D11 (Byzantine handshake rows), split.** A handshake row is authorised by a `k ∈ F` guard and
  has an effect on the round's data. The instance carries the effect and not the authorisation:
  `byzantineCallG` opens the round record and records its `⟨INPUT, b⟩` without any `k ∈ F` guard,
  and `byzantineRetG` sets the `returned` flag and writes the round's bound bit on the same
  evidence, denials and guard a correct return needs. The guard belongs to the network that
  surrounds the instance, where it applies to the handshake-row label that stays visible at this
  boundary.
* **The round's bound bit.** The ghost field `NetworkState.bound` belongs to the
  network, so the two return rows that write it are the network's
  (`GBCANetworkStep.retGIdle`, `GBCANetworkStep.byzantineRetG`), and a program's return row takes
  the announced bit free. The write is the one in
  `ImplementationStep.retGrade2`/`retGrade1`/`retGrade0`, which is what keeps `composition_projects`
  an equality.
* **D18 (the five message levels).** The send rows are the five levels
  `INPUT / ECHO / VOTE / BIND / ECHO5` and the three graded returns of the
  cited algorithm, not the four-round compression. The rows are taken in the
  wait-until order of Algorithm 6 from the `BIND` level down: each of those
  rows requires the record's own send at the level below. The `VOTE` rows ask
  for no own send, the `ECHO` they read being sent by an `upon` handler that
  may still be pending. The `⊥` rows and the returns carry the negations
  that the algorithm's if/else chain implies, the return rows in the reduced
  form `GBCA.ByABDY.ImplementationStep.retGrade0` states.

## The interface

Every row mirrors the round-visible half of one rule of the implementation instance
(`GBCA/ABDY/Implementation.lean`), split between the program that owns the record and the network
that owns the sent. What the implementation's rule writes on the core messagesOf — the round loop's
phase, estimate and grade — appears nowhere here: that messagesOf is a different component of the
protocol system. -/

namespace PLTS
namespace ABA

/-! `GBCA.ByABDY` names the graded sub-protocol: the round's graded-agreement
instance, read as a sub-protocol of ABA. -/

namespace GBCA.ByABDY

open Implementation Composition

/-! ### The instance-internal alphabet

The two rendezvous the shared alphabet cannot name. They are untagged: the
round is the identity of the instance they belong to, and they are hidden
before the family sees the instance at all. -/

/-- The internal rendezvous of one round: the multicast and the delivery. -/
inductive GBCAEvent (n : ℕ) : Type
  /-- Process `j` hands `m` to the round's network. -/
  | send (j : Fin n) (m : GBCA.ByABDY.Message)
  /-- The network delivers `j`'s `m` to `i`. -/
  | deliver (i j : Fin n) (m : GBCA.ByABDY.Message)
  deriving DecidableEq

/-- The instance-internal alphabet: the shared extended alphabet plus the two
rendezvous. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev GBCALabel (n : ℕ) : Type := ExtendedLabel n ⊕ GBCAEvent n

/-- The rendezvous labels, hidden by the instance. -/
def gbcaEvents (n : ℕ) : Set (GBCALabel n) := {l | ∃ e : GBCAEvent n, l = Sum.inr e}

@[simp] theorem inl_notMem_gbcaEvents {n : ℕ} (l : ExtendedLabel n) :
    Sum.inl l ∉ gbcaEvents n := by
  simp [gbcaEvents]

@[simp] theorem inr_mem_gbcaEvents {n : ℕ} (e : GBCAEvent n) :
    Sum.inr e ∈ gbcaEvents n := ⟨e, rfl⟩

@[simp] theorem gbcaLabel_tau (n : ℕ) :
    (Silent.τ : GBCALabel n) = Sum.inl (Sum.inl Label.tau) := rfl

/-! ### The local graded-agreement program

Process `j`'s program in this round. Every guard reads the round record and the recv and nothing
else. A rendezvous row carries the program's half of a joint step with the network — on a send the
record write, on a delivery the recv write. The rows are exactly the labels that reach the round's
instance: the round's own handshake ports and the two rendezvous. -/

/-- The step relation of the local graded-agreement program of process `j` in
round `r`. -/
inductive GBCAProgramStep (P : Parameters) (r : ℕ) (j : Fin P.n) :
    GBCA.ByABDY.RoundRecord P.n → GBCALabel P.n → PMF (GBCA.ByABDY.RoundRecord P.n) → Prop
  /-- The call arrives: record the input and mark `⟨INPUT, b⟩` as multicast.
  The recording of that message is the network's half (`ImplementationStep.call`). -/
  | call (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool) (h : p.process.input = none) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r j b)))
        (PMF.pure (p.setProcess { p.process with
          input := some b,
          sentInput := Function.update p.process.sentInput b true }))
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callIdle (p : GBCA.ByABDY.RoundRecord P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r id b))) (PMF.pure p)
  /-- A call against an already-called round record: the record does not move
  (`ImplementationStep.callLoop`). -/
  | callLoop (p : GBCA.ByABDY.RoundRecord P.n) (id : Fin P.n) (b : Bool) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) (PMF.pure p)
  /-- Return with outcome `grade2 v`: an `n − f` `ECHO5 v` quorum, the record called
  and its own `ECHO5` out (`ImplementationStep.retGrade2`). -/
  | retGrade2 (p : GBCA.ByABDY.RoundRecord P.n) (v : Bool) (bnd : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 (some v)))
      (hret : p.process.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade2 v) bnd)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- Return with outcome `grade1 v`: an `n − f` any-`ECHO5` quorum containing
  `ECHO5 v`, `f + 1` `BIND v`s and `|Valid| > 1`, the record called, its own
  `ECHO5` out and case (1) denied at either bit (`ImplementationStep.retGrade1`). -/
  | retGrade1 (p : GBCA.ByABDY.RoundRecord P.n) (v : Bool) (bnd : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.echo5Count)
      (honce : ∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k)
      (hbind : P.f + 1 ≤ p.receivedCount (.bind (some v)))
      (hval : p.bothValid P)
      (hret : p.process.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade1 v) bnd)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- Return with outcome `grade0`: an `n − f` `ECHO5 ⊥` quorum and `|Valid| > 1`, the
  record called, its own `ECHO5` out, case (1) denied at either bit and case (2)
  denied in the reduced form `ImplementationStep.retGrade0` states. -/
  | retGrade0 (p : GBCA.ByABDY.RoundRecord P.n) (bnd : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 none))
      (hval : p.bothValid P)
      (hret : p.process.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j .grade0 bnd)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- A return to another process: not `j`'s business. -/
  | retIdle (p : GBCA.ByABDY.RoundRecord P.n) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hid : id ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r id out bnd))) (PMF.pure p)
  /-- A Byzantine call (D11): the round record opens on the named bit, exactly as a correct call
  opens it (`ImplementationStep.call`). -/
  | byzantineCall (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool) (h : p.process.input = none) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r j b)))
        (PMF.pure (p.setProcess { p.process with
          input := some b,
          sentInput := Function.update p.process.sentInput b true }))
  /-- A Byzantine call at another process: not `j`'s business. -/
  | byzantineCallIdle (p : GBCA.ByABDY.RoundRecord P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r k b))) (PMF.pure p)
  /-- A Byzantine call against an already-called round record (D11): the record does not move
  (`ImplementationStep.callLoop`). -/
  | byzantineCallLoop (p : GBCA.ByABDY.RoundRecord P.n) (k : Fin P.n) (b : Bool) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) (PMF.pure p)
  /-- A Byzantine grade-2 return (D11): the correct row's evidence and guard, and
  the same record write (`ImplementationStep.retGrade2`). -/
  | byzantineRetGrade2 (p : GBCA.ByABDY.RoundRecord P.n) (v : Bool) (bnd : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 (some v)))
      (hret : p.process.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade2 v) bnd)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- A Byzantine grade-1 return (D11): the correct row's evidence, denial and
  guard, and the same record write (`ImplementationStep.retGrade1`). -/
  | byzantineRetGrade1 (p : GBCA.ByABDY.RoundRecord P.n) (v : Bool) (bnd : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.echo5Count)
      (honce : ∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k)
      (hbind : P.f + 1 ≤ p.receivedCount (.bind (some v)))
      (hval : p.bothValid P)
      (hret : p.process.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade1 v) bnd)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- A Byzantine grade-0 return (D11): the correct row's evidence, denials and
  guard, and the same record write (`ImplementationStep.retGrade0`). -/
  | byzantineRetGrade0 (p : GBCA.ByABDY.RoundRecord P.n) (bnd : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 none))
      (hval : p.bothValid P)
      (hret : p.process.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j .grade0 bnd)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- A Byzantine return at another process: not `j`'s business. -/
  | byzantineRetIdle (p : GBCA.ByABDY.RoundRecord P.n) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hk : k ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) (PMF.pure p)
  /-- `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩`, not yet multicast
  (`ImplementationStep.relay`; D8, D18). -/
  | sendRelay (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool)
      (hin : p.process.input ≠ none)
      (hcnt : P.f + 1 ≤ p.receivedCount (.input b))
      (hsend : p.process.sentInput b = false) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.input b)))
        (PMF.pure (p.setProcess { p.process with
          sentInput := Function.update p.process.sentInput b true }))
  /-- `ECHO b`: an `n − f` `INPUT b` quorum (`ImplementationStep.echo`; D18). -/
  | sendEcho (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool)
      (hin : p.process.input ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.input b))
      (hsend : p.process.sentEcho = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.echo b)))
        (PMF.pure (p.setProcess { p.process with sentEcho := some b }))
  /-- `VOTE b`: an `n − f` `ECHO b` quorum. The record's own `ECHO` is sent by
  one of the algorithm's `upon` handlers and may still be pending, so no
  own-send condition applies here (`ImplementationStep.voteBit`; D18). -/
  | sendVoteBit (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool)
      (hin : p.process.input ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo b))
      (hsend : p.process.sentVote = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.vote (some b))))
        (PMF.pure (p.setProcess { p.process with sentVote := some (some b) }))
  /-- `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`, and no
  single-bit `ECHO` quorum on record. The record's own `ECHO` is sent by one of
  the algorithm's `upon` handlers and may still be pending, so no own-send
  condition applies here (`ImplementationStep.voteBot`; D18). -/
  | sendVoteBot (p : GBCA.ByABDY.RoundRecord P.n)
      (hin : p.process.input ≠ none)
      (hnot : ∀ b, p.receivedCount (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.echoCount)
      (hval : p.bothValid P)
      (hsend : p.process.sentVote = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.vote none)))
        (PMF.pure (p.setProcess { p.process with sentVote := some none }))
  /-- `BIND b`: an `n − f` `VOTE b` quorum, the record's own `VOTE` already
  out (`ImplementationStep.bindBit`; D18). -/
  | sendBindBit (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentVote ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.vote (some b)))
      (hsend : p.process.sentBind = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.bind (some b))))
        (PMF.pure (p.setProcess { p.process with sentBind := some (some b) }))
  /-- `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`, the record's
  own `VOTE` already out, and no single-bit `VOTE` quorum on record
  (`ImplementationStep.bindBot`; D18). -/
  | sendBindBot (p : GBCA.ByABDY.RoundRecord P.n)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentVote ≠ none)
      (hnot : ∀ b, p.receivedCount (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.voteCount)
      (hval : p.bothValid P)
      (hsend : p.process.sentBind = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.bind none)))
        (PMF.pure (p.setProcess { p.process with sentBind := some none }))
  /-- `ECHO5 b`: an `n − f` `BIND b` quorum, the record's own `BIND` already
  out (`ImplementationStep.echo5Bit`; D18). -/
  | sendEcho5Bit (p : GBCA.ByABDY.RoundRecord P.n) (b : Bool)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentBind ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.bind (some b)))
      (hsend : p.process.sentEcho5 = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 (some b))))
        (PMF.pure (p.setProcess { p.process with sentEcho5 := some (some b) }))
  /-- `ECHO5 ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`, the record's
  own `BIND` already out, and no single-bit `BIND` quorum on record
  (`ImplementationStep.echo5Bot`; D18). -/
  | sendEcho5Bot (p : GBCA.ByABDY.RoundRecord P.n)
      (hin : p.process.input ≠ none)
      (hlv : p.process.sentBind ≠ none)
      (hnot : ∀ b, p.receivedCount (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.bindCount)
      (hval : p.bothValid P)
      (hsend : p.process.sentEcho5 = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 none)))
        (PMF.pure (p.setProcess { p.process with sentEcho5 := some none }))
  /-- A multicast by another process: not `j`'s business. -/
  | sendIdle (p : GBCA.ByABDY.RoundRecord P.n) (k : Fin P.n) (m : GBCA.ByABDY.Message)
    (hk : k ≠ j) :
      GBCAProgramStep P r j p (Sum.inr (.send k m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's recv row.
  Authenticity is the network's conjunct (`ImplementationStep.deliver`; D5). -/
  | deliverReceive (p : GBCA.ByABDY.RoundRecord P.n) (k : Fin P.n) (m : GBCA.ByABDY.Message) :
      GBCAProgramStep P r j p (Sum.inr (.deliver j k m)) (PMF.pure (p.deliverTo k m))
  /-- A delivery to another process: not `j`'s business. -/
  | deliverIdle (p : GBCA.ByABDY.RoundRecord P.n) (i k : Fin P.n) (m : GBCA.ByABDY.Message) (hi : i
    ≠ j) :
      GBCAProgramStep P r j p (Sum.inr (.deliver i k m)) (PMF.pure p)

/-! ### The round's network

The one local state of the instance that holds what no program may see: the per-sender sent sets and
the corrupted set. It participates in every send by recording the message and in every delivery by
checking that the message is sent, and it is where a corrupted sender's injections enter (D5). Its
state record `NetworkState` stands beside the round record in `GBCA/ABDY/Implementation.lean`, the
two of them being the components of a round's state; what follows is its rule table. -/

/-- The step relation of the round's network. All transitions are
Dirac. -/
inductive GBCANetworkStep (P : Parameters) (r : ℕ) :
    NetworkState P.n → GBCALabel P.n → PMF (NetworkState P.n) → Prop
  /-- The network's half of a multicast: sent the message under its sender.
  Authenticity is the sender's joint participation (D5). -/
  | send (w : NetworkState P.n) (j : Fin P.n) (m : GBCA.ByABDY.Message) :
      GBCANetworkStep P r w (Sum.inr (.send j m)) (PMF.pure (w.recordGBCASend j m))
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (`ImplementationStep.deliver`; D5). -/
  | deliver (w : NetworkState P.n) (i j : Fin P.n) (m : GBCA.ByABDY.Message) (h : m ∈ w.sent j) :
      GBCANetworkStep P r w (Sum.inr (.deliver i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (`ImplementationStep.byzantine`; D5, D11). -/
  | byzantineGBCA (w : NetworkState P.n) (k : Fin P.n) (m : GBCA.ByABDY.Message) (hF : k ∈ w.F) :
      GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure (w.recordGBCASend k m))
  /-- The network's half of the call: sent the caller's `⟨INPUT, b⟩`
  (`ImplementationStep.call`). -/
  | callG (w : NetworkState P.n) (id : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inl (.callG r id b)))
        (PMF.pure (w.recordGBCASend id (.input b)))
  /-- A return sends nothing, and writes the round's bound bit: the label's
  `bnd` is the bit on record if there is one and `boundOf`'s otherwise, and it
  goes on record (`ImplementationStep.retGrade2`/`retGrade1`/`retGrade0`). -/
  | retGIdle (w : NetworkState P.n) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hbnd : bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out)) :
      GBCANetworkStep P r w (Sum.inl (Sum.inl (.retG r id out bnd)))
        (PMF.pure (w.setBound bnd))
  /-- A call against an already-called round record sends nothing
  (`ImplementationStep.callLoop`). -/
  | gbcaCallLoop (w : NetworkState P.n) (id : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) (PMF.pure w)
  /-- A Byzantine call (D11): its `⟨INPUT, b⟩` is sent here, and there is no
  `k ∈ F` guard on this row — the authorisation of that row belongs to the
  network outside the instance, where the handshake-row label stays visible. -/
  | byzantineCallG (w : NetworkState P.n) (k : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallG r k b)))
        (PMF.pure (w.recordGBCASend k (.input b)))
  /-- A Byzantine call against an already-called round record sends nothing (D11). -/
  | byzantineCallGLoop (w : NetworkState P.n) (k : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) (PMF.pure w)
  /-- A Byzantine return sends nothing, and writes the round's bound bit
  exactly as the correct return does (D11). -/
  | byzantineRetG (w : NetworkState P.n) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hbnd : bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out)) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineRetG r k out bnd)))
        (PMF.pure (w.setBound bnd))

/-! ### The instance and its family -/

/-- The local graded-agreement program of process `j` in round `r`. -/
noncomputable def gbcaProgram (P : Parameters) (r : ℕ) (j : Fin P.n) :
    System (GBCA.ByABDY.RoundRecord P.n) (GBCALabel P.n) where
  init := GBCA.ByABDY.RoundRecord.initial P.n
  step := GBCAProgramStep P r j

@[simp] theorem gbcaProgram_init (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).init = GBCA.ByABDY.RoundRecord.initial P.n := rfl

@[simp] theorem gbcaProgram_step (P : Parameters) (r : ℕ) (j : Fin P.n)
    (p : GBCA.ByABDY.RoundRecord P.n) (l : GBCALabel P.n) (ν : PMF (GBCA.ByABDY.RoundRecord P.n)) :
    (gbcaProgram P r j).step p l ν ↔ GBCAProgramStep P r j p l ν := Iff.rfl

/-- The round's network. -/
noncomputable def GBCANetwork (P : Parameters) (r : ℕ) :
    System (NetworkState P.n) (GBCALabel P.n) where
  init := NetworkState.initial P.n
  step := GBCANetworkStep P r

@[simp] theorem GBCANetwork_init (P : Parameters) (r : ℕ) :
    (GBCANetwork P r).init = NetworkState.initial P.n := rfl

@[simp] theorem GBCANetwork_step (P : Parameters) (r : ℕ) (w : NetworkState P.n)
    (l : GBCALabel P.n) (μ : PMF (NetworkState P.n)) :
    (GBCANetwork P r).step w l μ ↔ GBCANetworkStep P r w l μ := Iff.rfl

/-- The programs beside the network, over the instance-internal alphabet. -/
noncomputable def compositionExtended (P : Parameters) (r : ℕ) :
    System (GBCA.ByABDY.ImplementationState P.n) (GBCALabel P.n) :=
  (System.synchronisedProduct (gbcaProgram P r)).parallel (GBCANetwork P r)

/-- **The round-`r` instance**: the programs beside the network, the two
rendezvous hidden, the result read back over the shared extended alphabet. Its
interface is the round's ports — `callG r`, `retG r`, `gbcaCallLoop r` and the
three graded-agreement rows of round `r`. -/
noncomputable def composition (P : Parameters) (r : ℕ) :
    System (GBCA.ByABDY.ImplementationState P.n) (ExtendedLabel P.n) :=
  ((compositionExtended P r).abstract (gbcaEvents P.n)).relabel

/-- The round a label of the instance interface belongs to. Every other label of the shared extended
alphabet — the ABA API, the coin ports, `fail`, the DECIDED sets, and the round rendezvous of the
protocol network — is owned by no round. -/
def roundOwnsLabel {n : ℕ} : ExtendedLabel n → Option ℕ
  | Sum.inl (.callG r _ _) => some r
  | Sum.inl (.retG r _ _ _) => some r
  | Sum.inr (.gbcaCallLoop r _ _) => some r
  | Sum.inr (.byzantineCallG r _ _) => some r
  | Sum.inr (.byzantineCallGLoop r _ _) => some r
  | Sum.inr (.byzantineRetG r _ _ _) => some r
  | _ => none

/-- Corruption is the one label every round takes at once. -/
def isFailLabel {n : ℕ} : ExtendedLabel n → Prop
  | Sum.inl (.fail _) => True
  | _ => False

instance {n : ℕ} : DecidablePred (isFailLabel (n := n)) := fun l => by
  cases l with
  | inl l => cases l <;> simp only [isFailLabel] <;> infer_instance
  | inr e => cases e <;> simp only [isFailLabel] <;> infer_instance

/-- The broadcast corruption act on an instance state: the round's network state records it, the
round records do not (D1). -/
def corruptionAct (P : Parameters) : ExtendedLabel P.n → GBCA.ByABDY.ImplementationState P.n →
  GBCA.ByABDY.ImplementationState P.n
  | Sum.inl (.fail k), (u, w) => (u, w.corrupt P k)
  | _, s => s

/-- **The graded-agreement family of the protocol**: the ℕ-indexed family of round instances. A
round-tagged label moves its round alone, `τ` moves one round, and `fail` is the broadcast that
keeps every round's copy of the corrupted set together. -/
noncomputable def gbcaInstanceFamily (P : Parameters) :
    System (ℕ → GBCA.ByABDY.ImplementationState P.n) (ExtendedLabel P.n) :=
  System.family (composition P) roundOwnsLabel isFailLabel (corruptionAct P)

/-! ### Determinacy

Both rule tables written here are Dirac, so the instance and its family are
LTS: the probabilistic transition of the protocol is the coin
resolution, which is not part of a graded-agreement round. -/

/-- Every program transition is Dirac. -/
theorem gbcaProgramStep_dirac {P : Parameters} {r : ℕ} {j : Fin P.n}
    {p : GBCA.ByABDY.RoundRecord P.n} {l : GBCALabel P.n} {ν : PMF (GBCA.ByABDY.RoundRecord P.n)}
    (h : GBCAProgramStep P r j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem gbcaNetworkStep_dirac {P : Parameters} {r : ℕ} {w : NetworkState P.n} {l : GBCALabel P.n}
    {μ : PMF (NetworkState P.n)} (h : GBCANetworkStep P r w l μ) :
    ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A local program is an LTS. -/
theorem gbcaProgram_isLTS (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).IsLTS :=
  fun _ _ _ h => gbcaProgramStep_dirac h

/-- The network is an LTS. -/
theorem GBCANetwork_isLTS (P : Parameters) (r : ℕ) : (GBCANetwork P r).IsLTS :=
  fun _ _ _ h => gbcaNetworkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem gbcaProgramProduct_isLTS (P : Parameters) (r : ℕ) :
    (System.synchronisedProduct (gbcaProgram P r)).IsLTS :=
  System.synchronisedProduct_isLTS (gbcaProgram_isLTS P r)

/-- The programs beside the network form an LTS. -/
theorem compositionExtended_isLTS (P : Parameters) (r : ℕ) : (compositionExtended P r).IsLTS :=
  System.parallel_isLTS (gbcaProgramProduct_isLTS P r) (GBCANetwork_isLTS P r)

/-- The instance is an LTS. -/
theorem composition_isLTS (P : Parameters) (r : ℕ) : (composition P r).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (compositionExtended_isLTS P r) _)

/-- The family of instances is an LTS. -/
theorem gbcaInstanceFamily_isLTS (P : Parameters) : (gbcaInstanceFamily P).IsLTS :=
  System.family_isLTS (composition_isLTS P) roundOwnsLabel isFailLabel (corruptionAct P)

/-- No program rule fires on `τ`: a program only ever moves in a rendezvous or
on one of the round's ports. The instance's silent transitions are therefore
exactly the network's injections and the hidden rendezvous. -/
theorem gbcaProgramStep_no_tau {P : Parameters} {r : ℕ} {j : Fin P.n}
    {p : GBCA.ByABDY.RoundRecord P.n} {ν : PMF (GBCA.ByABDY.RoundRecord P.n)}
    (h : GBCAProgramStep P r j p (Silent.τ : GBCALabel P.n) ν) : False := by
  rw [gbcaLabel_tau] at h; cases h

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ synchronisedProduct`; the lemmas
below unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem gbcaProgramProduct_inversion {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {l : GBCALabel P.n}
    {μ : PMF (∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n)}
    (h : (System.synchronisedProduct (gbcaProgram P r)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n, μ = PMF.pure x ∧ ∀ i, GBCAProgramStep P r i
    (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => gbcaProgramStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep gbcaProgramStep_no_tau

/-- Build a synchronised transition of the program group from per-process
Dirac steps. -/
theorem gbcaProgramProduct_pure {P : Parameters} {r : ℕ}
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {l : GBCALabel P.n}
    (hl : l ≠ Silent.τ)
    (h : ∀ i, GBCAProgramStep P r i (u i) l (PMF.pure (x i))) :
    (System.synchronisedProduct (gbcaProgram P r)).step u l (PMF.pure x) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program has a `τ` row. -/
theorem gbcaProgramProduct_no_tau {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n}
    {μ : PMF (∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n)}
    (h : (System.synchronisedProduct (gbcaProgram P r)).step u (Silent.τ : GBCALabel P.n) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact gbcaProgramStep_no_tau hstep

/-- The instance's step relation, unfolded to the hidden-rendezvous case and
the shared-label case. -/
theorem composition_step_iff (P : Parameters) (r : ℕ) (q : GBCA.ByABDY.ImplementationState P.n)
    (l : ExtendedLabel P.n) (μ : PMF (GBCA.ByABDY.ImplementationState P.n)) :
    (composition P r).step q l μ ↔
    (l = Sum.inl Label.tau ∧ ∃ e : GBCAEvent P.n, (compositionExtended P r).step q (Sum.inr e) μ) ∨
    (compositionExtended P r).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_gbcaEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_gbcaEvents l, hstep⟩

/-- Build a joint transition of the programs and the network on a rendezvous
label. -/
theorem compositionExtended_event_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (e : GBCAEvent P.n)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inr e) (PMF.pure w')) :
    (compositionExtended P r).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [compositionExtended, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', gbcaProgramProduct_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the programs and the network on a visible
shared label. -/
theorem compositionExtended_label_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    {l : ExtendedLabel P.n} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inl l) (PMF.pure w')) :
    (compositionExtended P r).step (u, w) (Sum.inl l) (PMF.pure (x, w')) := by
  have hne : (Sum.inl l : GBCALabel P.n) ≠ Silent.τ := by
    rw [gbcaLabel_tau]; simpa using hl
  rw [compositionExtended, System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure x, PMF.pure w', gbcaProgramProduct_pure hne hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the network from a
network-local one. -/
theorem compositionExtended_tau_network (P : Parameters) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (hn : GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (compositionExtended P r).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [compositionExtended, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden rendezvous is a silent transition of the instance. -/
theorem composition_event_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (e : GBCAEvent P.n)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inr e) (PMF.pure w')) :
    (composition P r).step (u, w) (Sum.inl Label.tau) (PMF.pure (x, w')) :=
  (composition_step_iff P r _ _ _).mpr
    (Or.inl ⟨rfl, e, compositionExtended_event_step P r e hall hn⟩)

/-- A visible shared label is a transition of the instance. -/
theorem composition_label_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    {l : ExtendedLabel P.n} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inl l) (PMF.pure w')) :
    (composition P r).step (u, w) l (PMF.pure (x, w')) :=
  (composition_step_iff P r _ _ _).mpr (Or.inr (compositionExtended_label_step P r hl hall hn))

/-- A network-local injection is a silent transition of the instance. -/
theorem composition_tau_network (P : Parameters) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (hn : GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (composition P r).step (u, w) (Sum.inl Label.tau) (PMF.pure (u, w')) :=
  (composition_step_iff P r _ _ _).mpr (Or.inr (compositionExtended_tau_network P r hn))

end GBCA.ByABDY
end ABA
end PLTS
