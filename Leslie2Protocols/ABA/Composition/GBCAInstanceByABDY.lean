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
protocol system.

## The replacement

`instanceSubstitution` is what licenses replacing the round instance by the graded agreement
specification. It runs through the implementation instance of `GBCA/ABDY/Implementation.lean` in two
steps.

The first step is strong and functional. The round instance and the implementation run on the same
state: `GBCA.ByABDY.ImplementationState` is the pair of the round records and the network state,
which are exactly the local states composed here. `composition_projects` says that every transition
of the round instance is a transition of the implementation at that same state, one step for one
step, with no stuttering: a joint call is the implementation's call, a hidden multicast or delivery
is the protocol rule or the delivery it carries, a network injection is the implementation's
Byzantine row. The two are one round under two presentations: a single rule table, and `n` programs
beside a network.

The second step is the per-instance refinement `GBCA.ByABDY.refinesSpecification`
(`GBCA/ABDY/RefinesSpecification.lean`), used as it stands. Its answer is a weak run of the
specification over the shared alphabet `Label n`, which is lifted to the instance's interface along
`gbcaLabelMap`: the projection that reads a Byzantine call row as a call, a Byzantine return row as
a return, and the two call loops as calls, which the specification takes on its input-enabledness
row (D11). The lifted specification `specificationOverRoundAlphabet` — the specification read back
along `gbcaLabelMap` — is the system that replaces the instance, and `specificationCorruptionAct` is
the broadcast corruption act it carries at that alphabet. -/

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

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its guards together with
the Dirac it produces, and the idle row of a non-participant as the identity. The record and the
distribution are variables, so `cases` unifies against any round record. -/

section ProcInversion

variable {P : Parameters} {r : ℕ} {j : Fin P.n} {p : GBCA.ByABDY.RoundRecord P.n}
  {ν : PMF (GBCA.ByABDY.RoundRecord P.n)}

theorem gbcaProgramStep_callG_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r j b))) ν) :
    p.process.input = none ∧
      ν = PMF.pure (p.setProcess { p.process with
        input := some b,
        sentInput := Function.update p.process.sentInput b true }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_callG_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r id b))) ν) :
    ν = PMF.pure p := by
  cases h
  case call => exact absurd rfl hid
  case callIdle => rfl

theorem gbcaProgramStep_gbcaCallLoop {id : Fin P.n} {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) ν) :
    ν = PMF.pure p := by
  cases h
  case callLoop => rfl

theorem gbcaProgramStep_retGGrade2_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade2 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.echo5 (some v)) ∧ p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case retGrade2 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_retGGrade1_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade1 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ p.echo5Count ∧ (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) ∧
      P.f + 1 ≤ p.receivedCount (.bind (some v)) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case retGrade1 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_retGGrade0_own {bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j .grade0 bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ p.receivedCount (.echo5 none) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case retGrade0 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_retG_foreign {id : Fin P.n} {out : GBCAOutput} {bnd : Bool} (hid : id ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r id out bnd))) ν) :
    ν = PMF.pure p := by
  cases h
  case retIdle => rfl
  all_goals exact absurd rfl hid

theorem gbcaProgramStep_byzantineCallG_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r j b))) ν) :
    p.process.input = none ∧
      ν = PMF.pure (p.setProcess { p.process with
        input := some b,
        sentInput := Function.update p.process.sentInput b true }) := by
  cases h
  case byzantineCall => exact ⟨by assumption, rfl⟩
  case byzantineCallIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineCallG_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r k b))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzantineCall => exact absurd rfl hk
  case byzantineCallIdle => rfl

theorem gbcaProgramStep_byzantineCallGLoop {k : Fin P.n} {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzantineCallLoop => rfl

theorem gbcaProgramStep_byzantineRetGGrade2_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade2 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.echo5 (some v)) ∧ p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case byzantineRetGrade2 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case byzantineRetIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineRetGGrade1_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade1 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ p.echo5Count ∧ (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) ∧
      P.f + 1 ≤ p.receivedCount (.bind (some v)) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case byzantineRetGrade1 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case byzantineRetIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineRetGGrade0_own {bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j .grade0 bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ p.receivedCount (.echo5 none) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case byzantineRetGrade0 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case byzantineRetIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineRetG_foreign {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (hk : k ≠ j) (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzantineRetIdle => rfl
  all_goals exact absurd rfl hk

theorem gbcaProgramStep_send_input_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.input b))) ν) :
    p.process.input ≠ none ∧ P.f + 1 ≤ p.receivedCount (.input b) ∧ p.process.sentInput b = false ∧
    ν = PMF.pure
    (p.setProcess { p.process with sentInput := Function.update p.process.sentInput b true }) := by
  cases h
  case sendRelay =>
    exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_echo_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.echo b))) ν) :
    p.process.input ≠ none ∧ P.n - P.f ≤ p.receivedCount (.input b) ∧
      p.process.sentEcho = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho := some b }) := by
  cases h
  case sendEcho => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_voteBit_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.vote (some b)))) ν) :
    p.process.input ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.echo b) ∧ p.process.sentVote = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentVote := some (some b) }) := by
  cases h
  case sendVoteBit =>
    exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_voteBot_own
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.vote none))) ν) :
    p.process.input ≠ none ∧
      (∀ b, p.receivedCount (.echo b) < P.n - P.f) ∧
      P.n - P.f ≤ p.echoCount ∧ p.bothValid P ∧
      p.process.sentVote = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentVote := some none }) := by
  cases h
  case sendVoteBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_bindBit_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.bind (some b)))) ν) :
    p.process.input ≠ none ∧ p.process.sentVote ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.vote (some b)) ∧ p.process.sentBind = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentBind := some (some b) }) := by
  cases h
  case sendBindBit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_bindBot_own
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.bind none))) ν) :
    p.process.input ≠ none ∧ p.process.sentVote ≠ none ∧
      (∀ b, p.receivedCount (.vote (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ p.voteCount ∧ p.bothValid P ∧
      p.process.sentBind = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentBind := some none }) := by
  cases h
  case sendBindBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_echo5Bit_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 (some b)))) ν) :
    p.process.input ≠ none ∧ p.process.sentBind ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.bind (some b)) ∧ p.process.sentEcho5 = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho5 := some (some b) }) := by
  cases h
  case sendEcho5Bit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_echo5Bot_own
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 none))) ν) :
    p.process.input ≠ none ∧ p.process.sentBind ≠ none ∧
      (∀ b, p.receivedCount (.bind (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ p.bindCount ∧ p.bothValid P ∧
      p.process.sentEcho5 = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho5 := some none }) := by
  cases h
  case sendEcho5Bot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_foreign {k : Fin P.n} {m : GBCA.ByABDY.Message} (hk : k ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inr (.send k m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hk

theorem gbcaProgramStep_deliver_own {k : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCAProgramStep P r j p (Sum.inr (.deliver j k m)) ν) :
    ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_deliver_foreign {i k : Fin P.n} {m : GBCA.ByABDY.Message} (hi : i ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

end ProcInversion

/-! ### The network's rules, by label class -/

section NetInversion

variable {P : Parameters} {r : ℕ} {w : NetworkState P.n} {μ : PMF (NetworkState P.n)}

theorem gbcaNetworkStep_send {j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inr (.send j m)) μ) :
    μ = PMF.pure (w.recordGBCASend j m) := by
  cases h; rfl

theorem gbcaNetworkStep_deliver {i j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inr (.deliver i j m)) μ) :
    m ∈ w.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem gbcaNetworkStep_tau (h : GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (k : Fin P.n) (m : GBCA.ByABDY.Message), k ∈ w.F ∧ μ = PMF.pure (w.recordGBCASend k m) := by
  cases h
  case byzantineGBCA k m hF => exact ⟨k, m, hF, rfl⟩

end NetInversion

/-! ### The specification read over the instance's interface

The graded agreement specification speaks the shared alphabet `Label n`; the
instance speaks the extended alphabet `ExtendedLabel n`, in which the three Byzantine
handshake rows and the call loop of round `r` are separate labels. `gbcaLabelMap` is the
projection that identifies them with the specification labels they stand for:
a Byzantine call is a call, a Byzantine return is a return, and the two
call loops are calls, which the specification takes on its input-enabledness
row. Every other extended label — the protocol network's rendezvous, the coin
handshake rows — are off the specification's interface and idles.

The lifted specification `specificationOverRoundAlphabet` is the specification read back along
`gbcaLabelMap`. It is what the instance is replaced by: the handshake-row labels stay visible
at this boundary, and their authorisation is the surrounding network's business
(D11). -/

/-- The projection of the extended alphabet onto the specification's alphabet.
-/
def gbcaLabelMap (n : ℕ) : ExtendedLabel n → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.gbcaCallLoop r id b) => some (.callG r id b)
  | Sum.inr (.byzantineCallG r k b) => some (.callG r k b)
  | Sum.inr (.byzantineCallGLoop r k b) => some (.callG r k b)
  | Sum.inr (.byzantineRetG r k out bnd) => some (.retG r k out bnd)
  | Sum.inr _ => none

@[simp] theorem gbcaLabelMap_inl {n : ℕ} (l : Label n) : gbcaLabelMap n (Sum.inl l) = some l := rfl

@[simp] theorem gbcaLabelMap_gbcaCallLoop {n : ℕ} (r : ℕ) (id : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.gbcaCallLoop r id b)) = some (.callG r id b) := rfl

@[simp] theorem gbcaLabelMap_byzantineCallG {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineCallG r k b)) = some (.callG r k b) := rfl

@[simp] theorem gbcaLabelMap_byzantineCallGLoop {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineCallGLoop r k b)) = some (.callG r k b) := rfl

@[simp] theorem gbcaLabelMap_byzantineRetG {n : ℕ} (r : ℕ) (k : Fin n) (out : GBCAOutput)
    (bnd : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineRetG r k out bnd)) = some (.retG r k out bnd) := rfl

@[simp] theorem gbcaLabelMap_gbcaSend {n : ℕ} (r : ℕ) (j : Fin n) (m : GBCA.ByABDY.Message) :
    gbcaLabelMap n (Sum.inr (.gbcaSend r j m)) = none := rfl

@[simp] theorem gbcaLabelMap_gbcaDeliver {n : ℕ} (r : ℕ) (i j : Fin n) (m : GBCA.ByABDY.Message) :
    gbcaLabelMap n (Sum.inr (.gbcaDeliver r i j m)) = none := rfl

@[simp] theorem gbcaLabelMap_decidedSend {n : ℕ} (j : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.decidedSend j b)) = none := rfl

@[simp] theorem gbcaLabelMap_decidedDeliver {n : ℕ} (i j : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.decidedDeliver i j b)) = none := rfl

@[simp] theorem gbcaLabelMap_retWPublish {n : ℕ} (r : ℕ) (id : Fin n) (c b : Bool) :
    gbcaLabelMap n (Sum.inr (.retWPublish r id c b)) = none := rfl

@[simp] theorem gbcaLabelMap_byzantineCallW {n : ℕ} (r : ℕ) (k : Fin n) :
    gbcaLabelMap n (Sum.inr (.byzantineCallW r k)) = none := rfl

@[simp] theorem gbcaLabelMap_byzantineRetW {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineRetW r k b)) = none := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem gbcaLabelMap_tau (n : ℕ) :
    gbcaLabelMap n (Silent.τ : ExtendedLabel n) = some (Silent.τ : Label n) := rfl

/-- Only the silent label projects to the silent label: a handshake row projects to a
handshake port, and every other extended label idles. -/
theorem gbcaLabelMap_eq_tau {n : ℕ} {l : ExtendedLabel n} (h : gbcaLabelMap n l = some Label.tau) :
    l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e <;> simp at h

/-- **The lifted specification**: the round-`r` graded agreement specification
read over the instance's interface. -/
noncomputable def specificationOverRoundAlphabet (P : Parameters) (r : ℕ) :
    System (GBCA.SpecState P.n) (ExtendedLabel P.n) :=
  (GBCA.specInst P r).mapIdle (gbcaLabelMap P.n)

@[simp] theorem specificationOverRoundAlphabet_init (P : Parameters) (r : ℕ) :
    (specificationOverRoundAlphabet P r).init = GBCA.SpecState.initial P.n := rfl

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverRoundAlphabet_isLTS (P : Parameters) (r : ℕ) :
    (specificationOverRoundAlphabet P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.specInst_isLTS P r)

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `gbcaLabelMap`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the
instance actually took — this is what turns a specification `callG` run into
the answer to a Byzantine call row. -/

/-- The section of `gbcaLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
def labelSection {n : ℕ} (l₀ : Label n) (l : ExtendedLabel n) : Label n → ExtendedLabel n :=
  fun x => if x = l₀ then l else Sum.inl x

theorem gbcaLabelMap_labelSection {n : ℕ} {l₀ : Label n} {l : ExtendedLabel n}
    (hl : gbcaLabelMap n l = some l₀) (x : Label n) :
    gbcaLabelMap n (labelSection l₀ l x) = some x := by
  unfold labelSection
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, gbcaLabelMap_inl]

theorem labelSection_tau {n : ℕ} {l₀ : Label n} {l : ExtendedLabel n}
    (hl : gbcaLabelMap n l = some l₀) (hl₀ : l₀ ≠ (Silent.τ : Label n)) (x : Label n) :
    labelSection l₀ l x = (Silent.τ : ExtendedLabel n) ↔ x = (Silent.τ : Label n) := by
  unfold labelSection
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Label n) := by
        rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    simp [Label.silent_eq]

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_specificationOverRoundAlphabet (P : Parameters) (r : ℕ)
    {s s' : GBCA.SpecState P.n} (h : (GBCA.specInst P r).weakLSilent s s') :
    (specificationOverRoundAlphabet P r).weakLSilent s s' :=
  System.weakLSilent_mapIdle Sum.inl (fun _ => rfl) (fun _ => by simp) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_specificationOverRoundAlphabet (P : Parameters) (r : ℕ)
    {s s' : GBCA.SpecState P.n} {l₀ : Label P.n} {l : ExtendedLabel P.n}
    (hl₀ : l₀ ≠ (Silent.τ : Label P.n)) (hl : gbcaLabelMap P.n l = some l₀)
    (h : (GBCA.specInst P r).weakLStep s l₀ s') :
    (specificationOverRoundAlphabet P r).weakLStep s l s' :=
  System.weakLStep_mapIdle (labelSection l₀ l) (gbcaLabelMap_labelSection hl) (labelSection_tau hl
    hl₀)
    (by simp [labelSection]) h

/-! ### One state, two presentations

The round records and the network state are the two components of `GBCA.ByABDY.ImplementationState`
(`GBCA/ABDY/Implementation.lean`), so the round instance and the implementation instance run on the
same state and every rule of the one is a rule of the other read in the implementation's accessors.
What the joint steps deliver, though, is a program function given pointwise — its value at the
acting process, and its agreement with the old one elsewhere — where the implementation's rules
write with `Function.update`. The lemmas here close that gap. -/

section Frame

variable {P : Parameters} {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w : NetworkState P.n}

/-- A program function fixed at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem programFunction_update {j : Fin P.n} {q : GBCA.ByABDY.RoundRecord P.n}
    (hj : x j = q) (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j q := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

/-- A record write at one program, with the network state untouched. -/
theorem composition_setProcess {j : Fin P.n} {pr : GBCA.ByABDY.ProcessRecord}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : GBCA.ByABDY.ImplementationState P.n) = GBCA.ByABDY.ImplementationState.setProcess
    (u, w) j pr := by
  rw [programFunction_update hj hne]
  rfl

/-- A record write at one program together with the network state recording the message
that write multicasts. -/
theorem composition_setProcess_recordGBCASend {j : Fin P.n} {pr : GBCA.ByABDY.ProcessRecord}
    {m : GBCA.ByABDY.Message} (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.recordGBCASend j m) : GBCA.ByABDY.ImplementationState P.n) =
    (GBCA.ByABDY.ImplementationState.setProcess (u, w) j pr).multicast j m := by
  rw [programFunction_update hj hne]
  rfl

/-- A record write at one program together with the network state's write of
the round's bound bit. -/
theorem composition_setProcess_setBound {j : Fin P.n} {pr : GBCA.ByABDY.ProcessRecord} {β : Bool}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.setBound β) : GBCA.ByABDY.ImplementationState P.n)
      = (GBCA.ByABDY.ImplementationState.setProcess (u, w) j pr).setBound β := by
  rw [programFunction_update hj hne]
  rfl

/-- The programs remain unchanged. -/
theorem composition_idle (hall : ∀ i, x i = u i) :
    ((x, w) : GBCA.ByABDY.ImplementationState P.n) = (u, w) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem composition_deliver {i k : Fin P.n} {m : GBCA.ByABDY.Message}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : GBCA.ByABDY.ImplementationState P.n) = GBCA.ByABDY.ImplementationState.receiveMessage
    (u, w) i k m := by
  rw [programFunction_update hi hne]
  rfl

/-- A Byzantine injection: the network state records a message under a corrupted
sender. -/
theorem composition_recordGBCASend {k : Fin P.n} {m : GBCA.ByABDY.Message} :
    ((u, w.recordGBCASend k m) : GBCA.ByABDY.ImplementationState P.n)
      = GBCA.ByABDY.ImplementationState.multicast (u, w) k m := rfl

/-- Corruption is the network state's own write, which is the implementation's (D1). -/
theorem composition_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : GBCA.ByABDY.ImplementationState P.n)
      = GBCA.ByABDY.ImplementationState.corrupt P k (u, w) := rfl

end Frame

/-! ### Reading an instance transition backwards

Two inversions of the composition, the counterparts of `compositionExtended_event_step` /
`compositionExtended_label_step` / `compositionExtended_tau_network`: on a visible label of the
internal alphabet every program and the network step together, and on the silent label
only the network moves. -/

/-- A visible transition of the programs beside the network: every program and
the network step on the label, and the joint distribution is their Dirac
product. -/
theorem compositionExtended_joint_inversion {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w : NetworkState P.n} {L : GBCALabel P.n}
    {μ : PMF (GBCA.ByABDY.ImplementationState P.n)} (hL : L ≠ (Silent.τ : GBCALabel P.n))
    (h : (compositionExtended P r).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n) (w' : NetworkState P.n),
      μ = PMF.pure (x, w') ∧ (∀ i, GBCAProgramStep P r i (u i) L (PMF.pure (x i))) ∧
        GBCANetworkStep P r w L (PMF.pure w') := by
  rw [compositionExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := gbcaProgramProduct_inversion hs
    obtain ⟨w', rfl⟩ := gbcaNetworkStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the network is a network-local
injection: no program has a `τ` row. -/
theorem compositionExtended_tau_inversion {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w : NetworkState P.n}
    {μ : PMF (GBCA.ByABDY.ImplementationState P.n)}
    (h : (compositionExtended P r).step (u, w) (Sum.inl (Sum.inl Label.tau)) μ) :
    ∃ w' : NetworkState P.n, μ = PMF.pure (u, w') ∧
      GBCANetworkStep P r w (Sum.inl (Sum.inl Label.tau)) (PMF.pure w') := by
  rw [compositionExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, rfl⟩ | ⟨-, μ₂, hn, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hs gbcaProgramProduct_no_tau
  · obtain ⟨w', rfl⟩ := gbcaNetworkStep_dirac hn
    exact ⟨w', prodPMF_pure_pure _ _, hn⟩

/-! ### The network's rules read off a round-tagged label

The network has a row only for its own round: a handshake label of another round
carries no transition of the instance at all. These readers therefore return
the round equation together with the network's move. -/

section NetRound

variable {P : Parameters} {r : ℕ} {w : NetworkState P.n} {μ : PMF (NetworkState P.n)}

theorem gbcaNetworkStep_callG_round {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.callG r' id b))) μ) :
    r' = r ∧ μ = PMF.pure (w.recordGBCASend id (.input b)) := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_retG_round {r' : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.retG r' id out bnd))) μ) :
    r' = r ∧ bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out) ∧
      μ = PMF.pure (w.setBound bnd) := by
  cases h with
  | retGIdle _ _ _ hbnd => exact ⟨rfl, hbnd, rfl⟩

theorem gbcaNetworkStep_gbcaCallLoop_round {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaCallLoop r' id b))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_byzantineCallG_round {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallG r' k b))) μ) :
    r' = r ∧ μ = PMF.pure (w.recordGBCASend k (.input b)) := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_byzantineCallGLoop_round {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallGLoop r' k b))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_byzantineRetG_round {r' : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineRetG r' k out bnd))) μ) :
    r' = r ∧ bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out) ∧
      μ = PMF.pure (w.setBound bnd) := by
  cases h with
  | byzantineRetG _ _ _ hbnd => exact ⟨rfl, hbnd, rfl⟩

/-! The labels the network does not offer at all: the ABA API, the coin ports,
corruption, and the protocol network's own rendezvous. -/

theorem gbcaNetworkStep_callABA_noStep {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.callABA id b))) μ) : False := by cases h

theorem gbcaNetworkStep_retABA_noStep {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.retABA id b))) μ) : False := by cases h

theorem gbcaNetworkStep_callW_noStep {r' : ℕ} {id : Fin P.n}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.callW r' id))) μ) : False := by cases h

theorem gbcaNetworkStep_retW_noStep {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.retW r' id b))) μ) : False := by cases h

theorem gbcaNetworkStep_fail_noStep {k : Fin P.n}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.fail k))) μ) : False := by cases h

theorem gbcaNetworkStep_gbcaSend_noStep {r' : ℕ} {j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaSend r' j m))) μ) : False := by cases h

theorem gbcaNetworkStep_gbcaDeliver_noStep {r' : ℕ} {i j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaDeliver r' i j m))) μ) : False := by cases h

theorem gbcaNetworkStep_decidedSend_noStep {j : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.decidedSend j b))) μ) : False := by cases h

theorem gbcaNetworkStep_decidedDeliver_noStep {i j : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.decidedDeliver i j b))) μ) : False := by cases h

theorem gbcaNetworkStep_retWPublish_noStep {r' : ℕ} {id : Fin P.n} {c b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.retWPublish r' id c b))) μ) : False := by cases h

theorem gbcaNetworkStep_byzantineCallW_noStep {r' : ℕ} {k : Fin P.n}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallW r' k))) μ) : False := by cases h

theorem gbcaNetworkStep_byzantineRetW_noStep {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineRetW r' k b))) μ) : False := by cases h

end NetRound

/-! ### The round instance projects onto the implementation

Every rule of the round instance is one rule of the round-`r` implementation at
the same state, and the correspondence is strong — one step answers one step,
at the specification label the interface label projects to, with no stuttering
anywhere:

| round instance | implementation |
| --- | --- |
| `callG` (caller writes, network records) | `ImplementationStep.call` |
| `gbcaCallLoop`, `byzantineCallGLoop` | `ImplementationStep.callLoop` |
| `byzantineCallG` (D11) | `ImplementationStep.call` |
| `retG` / `byzantineRetG`, by grade | `ImplementationStep.retGrade2` / `retGrade1` / `retGrade0` |
| hidden `send` rendezvous, by level | the eight protocol `τ` rules |
| hidden `deliver` rendezvous | `ImplementationStep.deliver` |
| network-local injection | `ImplementationStep.byzantine` |

The two hidden rendezvous and the network's injection are silent in both systems, and `gbcaLabelMap`
takes `τ` to `τ`. -/

/-- **The strong projection lemma.** -/
theorem composition_projects (P : Parameters) (r : ℕ) :
    ∀ (σ : GBCA.ByABDY.ImplementationState P.n) (l : ExtendedLabel P.n)
    (μ : PMF (GBCA.ByABDY.ImplementationState P.n)), (composition P r).step σ l μ → ∃ l₀,
    gbcaLabelMap P.n l = some l₀ ∧ (GBCA.ByABDY.implementation P r).step σ l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (composition_step_iff P r (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden rendezvous: an internal step of the implementation
    obtain ⟨x, w', rfl, hall, hn⟩ := compositionExtended_joint_inversion (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (gbcaProgramStep_send_foreign (Ne.symm hi) (hall i))
      have hw : w' = w.recordGBCASend j m := PMF.pure_injective (gbcaNetworkStep_send hn)
      subst hw
      cases m with
      | input b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_input_own (hall j)
        rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
        exact GBCA.ByABDY.ImplementationStep.relay _ j b hin hcnt hsend
      | echo b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_echo_own (hall j)
        rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
        exact GBCA.ByABDY.ImplementationStep.echo _ j b hin hcnt hsend
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_voteBit_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.voteBit _ j b hin hcnt hsend
        | none =>
          obtain ⟨hin, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_voteBot_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.voteBot _ j hin hnot hcnt hval hsend
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨hin, hlv, hcnt, hsend, hx⟩ := gbcaProgramStep_send_bindBit_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.bindBit _ j b hin hlv hcnt hsend
        | none =>
          obtain ⟨hin, hlv, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_bindBot_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.bindBot _ j hin hlv hnot hcnt hval hsend
      | «echo5» v =>
        cases v with
        | some b =>
          obtain ⟨hin, hlv, hcnt, hsend, hx⟩ := gbcaProgramStep_send_echo5Bit_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.echo5Bit _ j b hin hlv hcnt hsend
        | none =>
          obtain ⟨hin, hlv, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_echo5Bot_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.echo5Bot _ j hin hlv hnot hcnt hval hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := gbcaNetworkStep_deliver hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (gbcaProgramStep_deliver_foreign (Ne.symm hi') (hall i'))
      rw [composition_deliver (PMF.pure_injective (gbcaProgramStep_deliver_own (hall i))) hfor]
      exact GBCA.ByABDY.ImplementationStep.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Label.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := compositionExtended_tau_inversion hlab
      obtain ⟨k, m, hF, hw⟩ := gbcaNetworkStep_tau hn
      have hw' : w' = w.recordGBCASend k m := PMF.pure_injective hw
      subst hw'
      refine ⟨Label.tau, rfl, ?_⟩
      rw [composition_recordGBCASend]
      exact GBCA.ByABDY.ImplementationStep.byzantine _ k m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ := compositionExtended_joint_inversion (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (gbcaNetworkStep_callABA_noStep hn).elim
        | retABA id b => exact (gbcaNetworkStep_retABA_noStep hn).elim
        | callW r' id => exact (gbcaNetworkStep_callW_noStep hn).elim
        | retW r' id b => exact (gbcaNetworkStep_retW_noStep hn).elim
        | fail k => exact (gbcaNetworkStep_fail_noStep hn).elim
        | callG r' id b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_callG_round hn
          have hw' : w' = w.recordGBCASend id (.input b) := PMF.pure_injective hw
          subst hw'
          obtain ⟨hin, hx⟩ := gbcaProgramStep_callG_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_callG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.call _ id b hin
        | retG r' id out bnd =>
          obtain ⟨rfl, hbnd, hw⟩ := gbcaNetworkStep_retG_round hn
          have hw' : w' = w.setBound bnd := PMF.pure_injective hw
          subst hw'
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_retG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | grade2 v =>
            obtain ⟨hin, hlv, hcnt, hret, hx⟩ := gbcaProgramStep_retGGrade2_own (hall id)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade2 _ id v bnd hin hlv hcnt hret hbnd
          | grade1 v =>
            obtain ⟨hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hx⟩ :=
              gbcaProgramStep_retGGrade1_own (hall id)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade1 _ id v bnd hin hlv hnotGrade2 hcnt honce
              hbind hval
              hret hbnd
          | grade0 =>
            obtain ⟨hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hx⟩ :=
              gbcaProgramStep_retGGrade0_own (hall id)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade0 _ id bnd hin hlv hnotGrade2 hnotGrade1
              hcnt hval hret
              hbnd
      | inr ev =>
        cases ev with
        | gbcaSend r' j m => exact (gbcaNetworkStep_gbcaSend_noStep hn).elim
        | gbcaDeliver r' i j m => exact (gbcaNetworkStep_gbcaDeliver_noStep hn).elim
        | decidedSend j b => exact (gbcaNetworkStep_decidedSend_noStep hn).elim
        | decidedDeliver i j b => exact (gbcaNetworkStep_decidedDeliver_noStep hn).elim
        | retWPublish r' id c b => exact (gbcaNetworkStep_retWPublish_noStep hn).elim
        | byzantineCallW r' k => exact (gbcaNetworkStep_byzantineCallW_noStep hn).elim
        | byzantineRetW r' k b => exact (gbcaNetworkStep_byzantineRetW_noStep hn).elim
        | gbcaCallLoop r' id b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_gbcaCallLoop_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          have hidle : ∀ i,
            x i = u i := fun i => PMF.pure_injective (gbcaProgramStep_gbcaCallLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_idle hidle]
          exact GBCA.ByABDY.ImplementationStep.callLoop _ id b
        | byzantineCallG r' k b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_byzantineCallG_round hn
          have hw' : w' = w.recordGBCASend k (.input b) := PMF.pure_injective hw
          subst hw'
          obtain ⟨hin, hx⟩ := gbcaProgramStep_byzantineCallG_own (hall k)
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_byzantineCallG_foreign (Ne.symm hi)
              (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.call _ k b hin
        | byzantineCallGLoop r' k b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_byzantineCallGLoop_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          have hidle : ∀ i, x i = u i :=
            fun i => PMF.pure_injective (gbcaProgramStep_byzantineCallGLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_idle hidle]
          exact GBCA.ByABDY.ImplementationStep.callLoop _ k b
        | byzantineRetG r' k out bnd =>
          obtain ⟨rfl, hbnd, hw⟩ := gbcaNetworkStep_byzantineRetG_round hn
          have hw' : w' = w.setBound bnd := PMF.pure_injective hw
          subst hw'
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_byzantineRetG_foreign (Ne.symm hi) (hall
              i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | grade2 v =>
            obtain ⟨hin, hlv, hcnt, hret, hx⟩ := gbcaProgramStep_byzantineRetGGrade2_own (hall k)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade2 _ k v bnd hin hlv hcnt hret hbnd
          | grade1 v =>
            obtain ⟨hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hx⟩ :=
              gbcaProgramStep_byzantineRetGGrade1_own (hall k)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade1 _ k v bnd hin hlv hnotGrade2 hcnt honce
              hbind hval
              hret hbnd
          | grade0 =>
            obtain ⟨hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hx⟩ :=
              gbcaProgramStep_byzantineRetGGrade0_own (hall k)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade0 _ k bnd hin hlv hnotGrade2 hnotGrade1
              hcnt hval hret
              hbnd

/-! ### The round instance is refined by the graded agreement specification

The round instance's answer to a step is the implementation's answer, read through the per-instance
refinement (`GBCA.ByABDY.refinesSpecification`, `GBCA/ABDY/RefinesSpecification.lean`): the first
step is strong and functional, so nothing of that refinement is reproved here. The specification's
weak answer is finally lifted to the round instance's interface along a section of `gbcaLabelMap` —
which is where a Byzantine handshake row is answered by the specification's own call or return row
(D11). -/

/-- **The simulation relation of the round instance**: the relation
`GBCA.ByABDY.specificationRelation` of the implementation, which the shared state lets it be
verbatim. -/
def substitutionRelation (P : Parameters) (r : ℕ) (σ : GBCA.ByABDY.ImplementationState P.n)
    (s : GBCA.SpecState P.n) : Prop :=
  GBCA.ByABDY.specificationRelation P r σ s

/-- **The per-round instance simulation**: the round-`r` instance is forward
simulated by the round-`r` graded agreement specification, read over the
instance's interface. -/
theorem instanceSubstitution (P : Parameters) (r : ℕ) :
    ForwardSimulation (composition P r) (specificationOverRoundAlphabet P r)
    (substitutionRelation P r) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, himpl⟩ := composition_projects P r q₁ l μ hstep
  obtain ⟨s', hdis,
    hrel⟩ := (GBCA.ByABDY.refinesSpecification P r).step q₁ q₂ hR l₀ μ himpl q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨gbcaLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_specificationOverRoundAlphabet P r hweak⟩
  · refine Or.inr ⟨?_, weakLStep_specificationOverRoundAlphabet P r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : gbcaLabelMap P.n (Silent.τ : ExtendedLabel P.n) = some l₀ := by
      rw [← hl]; exact hpull
    rw [gbcaLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### What the family lift will need

The two premises of `ForwardSimulation.family` for the round-indexed family: the relation holds at
the initial states, and it survives the broadcast corruption. Both are the implementation instance's
own facts, which the shared state lets stand verbatim. -/

/-- The broadcast corruption act on a specification state, over the extended
alphabet: `GBCA.failAct` taken on the extended `fail` label. -/
def specificationCorruptionAct (P : Parameters) : ExtendedLabel P.n → GBCA.SpecState P.n →
  GBCA.SpecState P.n
  | Sum.inl (.fail k), s => s.corrupt P k
  | _, s => s

/-- The initial states of the instance and of its specification are
related. -/
theorem instanceSubstitution_init (P : Parameters) (r : ℕ) :
    substitutionRelation P r (composition P r).init (GBCA.specInst P r).init :=
  GBCA.ByABDY.specificationRelation_init P r

/-- **Broadcast compatibility**: corruption preserves the instance relation.
The network state's corrupted set is the implementation's, so the two guards
`k ∉ F ∧ |F| < f` agree and the implementation-level statement
(`GBCA.ByABDY.specificationRelation_corrupt`) applies verbatim (D1). -/
theorem instanceSubstitution_failAct (P : Parameters) :
    ∀ l : ExtendedLabel P.n, isFailLabel l → ∀ (r : ℕ) (σ : GBCA.ByABDY.ImplementationState P.n)
      (s : GBCA.SpecState P.n), substitutionRelation P r σ s →
      substitutionRelation P r (corruptionAct P l σ) (specificationCorruptionAct P l s) := by
  rintro l hl r ⟨u, w⟩ s hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k =>
      have hs : corruptionAct P (Sum.inl (Label.fail k)) (u, w)
          = GBCA.ByABDY.ImplementationState.corrupt P k (u, w) := composition_corrupt k
      have hc := GBCA.ByABDY.specificationRelation_corrupt P r k hR
      rw [← hs] at hc
      exact hc
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.instanceSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceSubstitution

/-- info: 'PLTS.ABA.GBCA.ByABDY.composition_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composition_projects

end GBCA.ByABDY

/-! ## The routing table, evaluated

`roundOwnsLabel` and `isFailLabel` are decided by a `rfl` at every label of the extended alphabet.
The composed system composes `gbcaInstanceFamily` with local states that speak that alphabet, so it
discharges the routing premises by `simp`; the table below is what `simp` uses, and it lives under
`PLTS.ABA.Composition` with the rest of the components' vocabulary. -/

namespace Composition

open Implementation

/-! ### Which labels the round-indexed family owns -/

section GOwns

variable {n : ℕ}

@[simp] theorem roundOwnsLabel_callG (r : ℕ) (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.callG r id b) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_retG (r : ℕ) (id : Fin n) (out : GBCAOutput) (bnd : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.retG r id out bnd) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_gbcaCallLoop (r : ℕ) (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.gbcaCallLoop r id b) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_byzantineCallG (r : ℕ) (k : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineCallG r k b) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_byzantineCallGLoop (r : ℕ) (k : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineCallGLoop r k b) : ExtendedLabel n) = some r :=
      rfl
@[simp] theorem roundOwnsLabel_byzantineRetG (r : ℕ) (k : Fin n) (out : GBCAOutput) (bnd : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineRetG r k out bnd) : ExtendedLabel n) = some r :=
      rfl

@[simp] theorem roundOwnsLabel_tau : GBCA.ByABDY.roundOwnsLabel (Sum.inl Label.tau : ExtendedLabel
  n) = none := rfl
@[simp] theorem roundOwnsLabel_callABA (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.callABA id b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_retABA (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.retABA id b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_callW (r : ℕ) (id : Fin n) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.callW r id) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_retW (r : ℕ) (id : Fin n) (c : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.retW r id c) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_fail (k : Fin n) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.fail k) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_gbcaSend (r : ℕ) (j : Fin n) (m : GBCA.ByABDY.Message) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.gbcaSend r j m) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_gbcaDeliver (r : ℕ) (i j : Fin n) (m : GBCA.ByABDY.Message) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.gbcaDeliver r i j m) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_decidedSend (j : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.decidedSend j b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_decidedDeliver (i j : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.decidedDeliver i j b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_retWPublish (r : ℕ) (id : Fin n) (c b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.retWPublish r id c b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_byzantineCallW (r : ℕ) (k : Fin n) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineCallW r k) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_byzantineRetW (r : ℕ) (k : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineRetW r k b) : ExtendedLabel n) = none := rfl

@[simp] theorem isFailLabel_fail (k : Fin n) :
    GBCA.ByABDY.isFailLabel (Sum.inl (Label.fail k) : ExtendedLabel n) := trivial

theorem corruptionAct_fail {P : Parameters} (k : Fin P.n)
  (s : GBCA.ByABDY.ImplementationState P.n) :
    GBCA.ByABDY.corruptionAct P (Sum.inl (Label.fail k)) s = (s.1, s.2.corrupt P k) := rfl

end GOwns

end Composition

end ABA
end PLTS
