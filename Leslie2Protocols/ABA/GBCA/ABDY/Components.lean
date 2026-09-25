/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.GBCA.ABDY.MessagesAndVariables
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The components of the round's graded-agreement instance

The pieces that run one round of the protocol: `n` corruption-blind local programs, one per
process, beside the round's own network. `GBCAProgramStep` is the step relation of process `j`'s
program and `GBCANetworkStep` that of the round's network; `gbcaProgram` and `GBCANetwork` are the
two systems they carry, and `ABA/GBCA/ABDY/Composition.lean` assembles them into the instance.

A local program holds the variables of one round: the process's own protocol data and the messages
delivered to it, indexed by sender (`GBCA.ByABDY.RoundVariables`). It holds no corrupted set and no
corruption flag, and it does not record the messages it has multicast; its guards read its variables
and the delivered sets, never the identity of the caller. The round loop that moves the ports is not
here either — a call writes the round's variables alone, a return sets their `returned` flag alone.

The round's network holds the per-sender sent sets and the corrupted set. A multicast is a
synchronised step of the sender, which writes its variables, and the network, which records the
message; a delivery is a synchronised step of the network, which checks that the message is sent
under the named sender, and the receiver, which files it under that sender's delivered set.

## The instance-internal alphabet

The two synchronisations — the multicast and the delivery — are the constructors of `GBCAEvent`, and
they are labels of the instance-internal alphabet
`GBCALabel n = ExtendedLabel n Message ⊕ GBCAEvent n`.
They are untagged: the round is the identity of the instance they belong to, and they are hidden
before the family sees the instance at all (`gbcaEvents` is the set hidden there). What stays
visible is the round's interface in the shared extended alphabet `ExtendedLabel n Message`:
`callG r`,
`retG r`, `gbcaCallLoop r` and the three Byzantine graded-agreement labels of round `r`. The
round-multicast and round-delivery constructors of `NetworkEvent` are therefore not part of that
interface — no component offers them, so they carry no transition of the instance.

## Model and deviations

* **D1 (determinised `fail`).** `NetworkState.corrupt` is the total Dirac function guarded by
  `k ∉ F ∧ |F| < f`. `fail` is a transition of neither component here: it is the family's broadcast
  act, applied to every round's network simultaneously, which is what keeps the per-round copies of
  the corrupted set together.
* **D5 (set-based network).** Multicasts are idempotent: `sent j` is the set of messages `j` has
  multicast in this round, and `received k` at a program is the set of messages from `k` delivered
  there. Thresholds count distinct senders. A corrupted sender's injections enter its sent set
  through the network's own `byzantineGBCA` transition.
* **D8 (participation guard).** The protocol sends and the three returns require the variables to
  hold the process's input: the algorithm's handlers only run inside a called instance.
* **D11 (Byzantine call and return transitions), split.** A Byzantine call or return transition is
  authorised by a `k ∈ F` guard and has an effect on the round's data. The components carry the
  effect and not the authorisation: `byzantineCallG` opens the round's variables and records its
  `⟨INPUT, b⟩` without any `k ∈ F` guard, and `byzantineRetG` sets the `returned` flag and writes
  the round's bound bit on the same witness, denials and guard a correct return needs. The guard
  belongs to the network that surrounds the instance, where it applies to the call or return label
  that stays visible at this boundary.
* **The round's bound bit (D29).** The ghost field `NetworkState.bound` belongs to the network, so
  the two return transitions that write it are the network's (`GBCANetworkStep.retGIdle`,
  `GBCANetworkStep.byzantineRetG`), and a program's return takes the announced bit free. The write
  is the one in `Algorithm.retGrade2`/`retGrade1`/`retGrade0`, which is what keeps
  `composition_projects` an equality.
* **D18 (the five message levels).** The send transitions are the five levels
  `INPUT / ECHO / VOTE / BIND / ECHO5` and the three graded returns of the cited algorithm, not the
  four-round compression. They are taken in the wait-until order of Algorithm 6 from the `BIND`
  level down: each of them requires the process's own send at the level below. The `VOTE`
  transitions ask for no own send, the `ECHO` they read being sent by an `upon` handler that may
  still be pending. The `⊥` transitions and the returns carry the negations that the algorithm's
  if/else chain implies, the returns in the reduced form
  `GBCA.ByABDY.Algorithm.retGrade0` states.

## The interface

Every transition mirrors the round-visible half of one transition of the algorithm
(`GBCA/ABDY/Algorithm.lean`), split between the program that owns the variables and the network
that owns the sent sets. The round loop's phase, estimate and grade appear nowhere here: they are
held by another component of the protocol system. -/

namespace PLTS
namespace ABA

/-! `GBCA.ByABDY` names the graded sub-protocol: the round's graded-agreement
instance, read as a sub-protocol of ABA. -/

namespace GBCA.ByABDY

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The instance-internal alphabet

The two synchronisations the shared alphabet cannot name. They are untagged: the
round is the identity of the instance they belong to, and they are hidden
before the family sees the instance at all. -/

/-- The internal synchronisations of one round: the multicast and the delivery. -/
inductive GBCAEvent (n : ℕ) : Type
  /-- Process `j` hands `m` to the round's network. -/
  | send (j : Fin n) (m : GBCA.ByABDY.Message)
  /-- The network delivers `j`'s `m` to `i`. -/
  | deliver (i j : Fin n) (m : GBCA.ByABDY.Message)
  deriving DecidableEq

/-- The instance-internal alphabet: the shared extended alphabet plus the two
synchronisations. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev GBCALabel (n : ℕ) : Type := ExtendedLabel n Message ⊕ GBCAEvent n

/-- The synchronisation labels, hidden by the instance. -/
def gbcaEvents (n : ℕ) : Set (GBCALabel n) := {l | ∃ e : GBCAEvent n, l = Sum.inr e}

@[simp] theorem inl_notMem_gbcaEvents {n : ℕ} (l : ExtendedLabel n Message) :
    Sum.inl l ∉ gbcaEvents n := by
  simp [gbcaEvents]

@[simp] theorem inr_mem_gbcaEvents {n : ℕ} (e : GBCAEvent n) :
    Sum.inr e ∈ gbcaEvents n := ⟨e, rfl⟩

@[simp] theorem gbcaLabel_tau (n : ℕ) :
    (Silent.τ : GBCALabel n) = Sum.inl (Sum.inl Label.tau) := rfl

/-! ### The local graded-agreement program

Process `j`'s program in this round. Every guard reads the round's variables and the received sets
and nothing else. A synchronised transition carries the program's half of a synchronised step with
the network — on a send the write to its variables, on a delivery the write to its received sets.
The transitions are exactly the labels that reach the round's instance: the round's own call and
return ports and the two synchronisations. -/

/-- The step relation of the local graded-agreement program of process `j` in
round `r`. -/
inductive GBCAProgramStep (P : Parameters) (r : ℕ) (j : Fin P.n) :
    GBCA.ByABDY.RoundVariables P.n → GBCALabel P.n → PMF (GBCA.ByABDY.RoundVariables P.n) → Prop
  /-- The call arrives: record the input and mark `⟨INPUT, b⟩` as multicast.
  The recording of that message is the network's half (`Algorithm.call`). -/
  | call (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool) (h : p.processVariables.input = none) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r j b)))
        (PMF.pure (p.setProcessVariables { p.processVariables with
          input := some b,
          sentInput := Function.update p.processVariables.sentInput b true }))
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callIdle (p : GBCA.ByABDY.RoundVariables P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r id b))) (PMF.pure p)
  /-- A call against variables already called: the variables do not move
  (`Algorithm.callLoop`). -/
  | callLoop (p : GBCA.ByABDY.RoundVariables P.n) (id : Fin P.n) (b : Bool) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) (PMF.pure p)
  /-- Return with outcome `grade2 v`: an `n − f` `ECHO5 v` quorum, the variables called
  and its own `ECHO5` out (`Algorithm.retGrade2`). -/
  | retGrade2 (p : GBCA.ByABDY.RoundVariables P.n) (v : Bool) (bnd : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 (some v)))
      (hret : p.processVariables.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade2 v) bnd)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- Return with outcome `grade1 v`: an `n − f` any-`ECHO5` quorum containing
  `ECHO5 v`, `f + 1` `BIND v`s and `|Valid| > 1`, the variables called, its own
  `ECHO5` out and case (1) denied at either bit (`Algorithm.retGrade1`). -/
  | retGrade1 (p : GBCA.ByABDY.RoundVariables P.n) (v : Bool) (bnd : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.echo5Count)
      (honce : ∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k)
      (hbind : P.f + 1 ≤ p.receivedCount (.bind (some v)))
      (hval : p.bothValid P)
      (hret : p.processVariables.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade1 v) bnd)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- Return with outcome `grade0`: an `n − f` `ECHO5 ⊥` quorum and `|Valid| > 1`, the
  variables called, its own `ECHO5` out, case (1) denied at either bit and case (2)
  denied in the reduced form `Algorithm.retGrade0` states. -/
  | retGrade0 (p : GBCA.ByABDY.RoundVariables P.n) (bnd : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 none))
      (hval : p.bothValid P)
      (hret : p.processVariables.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j .grade0 bnd)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- A return to another process: not `j`'s business. -/
  | retIdle (p : GBCA.ByABDY.RoundVariables P.n) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hid : id ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r id out bnd))) (PMF.pure p)
  /-- A Byzantine call (D11): the round's variables open on the named bit, exactly as a correct call
  opens them (`Algorithm.call`). -/
  | byzantineCall (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool) (h : p.processVariables.input =
      none) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r j b)))
        (PMF.pure (p.setProcessVariables { p.processVariables with
          input := some b,
          sentInput := Function.update p.processVariables.sentInput b true }))
  /-- A Byzantine call at another process: not `j`'s business. -/
  | byzantineCallIdle (p : GBCA.ByABDY.RoundVariables P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r k b))) (PMF.pure p)
  /-- A Byzantine call against variables already called (D11): the variables do not move
  (`Algorithm.callLoop`). -/
  | byzantineCallLoop (p : GBCA.ByABDY.RoundVariables P.n) (k : Fin P.n) (b : Bool) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) (PMF.pure p)
  /-- A Byzantine grade-2 return (D11): the correct transition's witness and guard, and
  the same write to the variables (`Algorithm.retGrade2`). -/
  | byzantineRetGrade2 (p : GBCA.ByABDY.RoundVariables P.n) (v : Bool) (bnd : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 (some v)))
      (hret : p.processVariables.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade2 v) bnd)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- A Byzantine grade-1 return (D11): the correct transition's witness, denial and
  guard, and the same write to the variables (`Algorithm.retGrade1`). -/
  | byzantineRetGrade1 (p : GBCA.ByABDY.RoundVariables P.n) (v : Bool) (bnd : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.echo5Count)
      (honce : ∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k)
      (hbind : P.f + 1 ≤ p.receivedCount (.bind (some v)))
      (hval : p.bothValid P)
      (hret : p.processVariables.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade1 v) bnd)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- A Byzantine grade-0 return (D11): the correct transition's witness, denials and
  guard, and the same write to the variables (`Algorithm.retGrade0`). -/
  | byzantineRetGrade0 (p : GBCA.ByABDY.RoundVariables P.n) (bnd : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo5 none))
      (hval : p.bothValid P)
      (hret : p.processVariables.returned = false) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j .grade0 bnd)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- A Byzantine return at another process: not `j`'s business. -/
  | byzantineRetIdle (p : GBCA.ByABDY.RoundVariables P.n) (k : Fin P.n) (out : GBCAOutput) (bnd :
      Bool)
      (hk : k ≠ j) :
      GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) (PMF.pure p)
  /-- `INPUT` relay: `f + 1` received `⟨INPUT, b⟩` messages, not yet multicast
  (`Algorithm.relay`; D8, D18). -/
  | sendRelay (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool)
      (hin : p.processVariables.input ≠ none)
      (hcnt : P.f + 1 ≤ p.receivedCount (.input b))
      (hsend : p.processVariables.sentInput b = false) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.input b)))
        (PMF.pure (p.setProcessVariables { p.processVariables with
          sentInput := Function.update p.processVariables.sentInput b true }))
  /-- `ECHO b`: an `n − f` `INPUT b` quorum (`Algorithm.echo`; D18). -/
  | sendEcho (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool)
      (hin : p.processVariables.input ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.input b))
      (hsend : p.processVariables.sentEcho = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.echo b)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentEcho := some b }))
  /-- `VOTE b`: an `n − f` `ECHO b` quorum. The process's own `ECHO` is sent by
  one of the algorithm's `upon` handlers and may still be pending, so no
  own-send condition applies here (`Algorithm.voteBit`; D18). -/
  | sendVoteBit (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool)
      (hin : p.processVariables.input ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.echo b))
      (hsend : p.processVariables.sentVote = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.vote (some b))))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentVote := some (some b) }))
  /-- `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`, and no
  single-bit `ECHO` quorum among the received messages. The process's own `ECHO`
  is sent by one of the algorithm's `upon` handlers and may still be pending, so
  no own-send condition applies here (`Algorithm.voteBot`; D18). -/
  | sendVoteBot (p : GBCA.ByABDY.RoundVariables P.n)
      (hin : p.processVariables.input ≠ none)
      (hnot : ∀ b, p.receivedCount (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.echoCount)
      (hval : p.bothValid P)
      (hsend : p.processVariables.sentVote = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.vote none)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentVote := some none }))
  /-- `BIND b`: an `n − f` `VOTE b` quorum, the process's own `VOTE` already
  out (`Algorithm.bindBit`; D18). -/
  | sendBindBit (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentVote ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.vote (some b)))
      (hsend : p.processVariables.sentBind = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.bind (some b))))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentBind := some (some b) }))
  /-- `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`, the process's
  own `VOTE` already out, and no single-bit `VOTE` quorum among the received
  messages (`Algorithm.bindBot`; D18). -/
  | sendBindBot (p : GBCA.ByABDY.RoundVariables P.n)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentVote ≠ none)
      (hnot : ∀ b, p.receivedCount (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.voteCount)
      (hval : p.bothValid P)
      (hsend : p.processVariables.sentBind = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.bind none)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentBind := some none }))
  /-- `ECHO5 b`: an `n − f` `BIND b` quorum, the process's own `BIND` already
  out (`Algorithm.echo5Bit`; D18). -/
  | sendEcho5Bit (p : GBCA.ByABDY.RoundVariables P.n) (b : Bool)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentBind ≠ none)
      (hcnt : P.n - P.f ≤ p.receivedCount (.bind (some b)))
      (hsend : p.processVariables.sentEcho5 = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 (some b))))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentEcho5 := some (some b) }))
  /-- `ECHO5 ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`, the process's
  own `BIND` already out, and no single-bit `BIND` quorum among the received
  messages (`Algorithm.echo5Bot`; D18). -/
  | sendEcho5Bot (p : GBCA.ByABDY.RoundVariables P.n)
      (hin : p.processVariables.input ≠ none)
      (hlv : p.processVariables.sentBind ≠ none)
      (hnot : ∀ b, p.receivedCount (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ p.bindCount)
      (hval : p.bothValid P)
      (hsend : p.processVariables.sentEcho5 = none) :
      GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 none)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentEcho5 := some none }))
  /-- A multicast by another process: not `j`'s business. -/
  | sendIdle (p : GBCA.ByABDY.RoundVariables P.n) (k : Fin P.n) (m : GBCA.ByABDY.Message)
    (hk : k ≠ j) :
      GBCAProgramStep P r j p (Sum.inr (.send k m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's received set.
  Authenticity is the network's conjunct (`Algorithm.deliver`; D5). -/
  | deliverReceive (p : GBCA.ByABDY.RoundVariables P.n) (k : Fin P.n) (m : GBCA.ByABDY.Message) :
      GBCAProgramStep P r j p (Sum.inr (.deliver j k m)) (PMF.pure (p.deliverTo k m))
  /-- A delivery to another process: not `j`'s business. -/
  | deliverIdle (p : GBCA.ByABDY.RoundVariables P.n) (i k : Fin P.n) (m : GBCA.ByABDY.Message) (hi :
      i
    ≠ j) :
      GBCAProgramStep P r j p (Sum.inr (.deliver i k m)) (PMF.pure p)

/-! ### The round's network

The one local state of the instance that holds what no program may see: the per-sender sent sets and
the corrupted set. It participates in every send by recording the message and in every delivery by
checking that the message is sent, and it is where a corrupted sender's injections enter (D5). Its
state `NetworkState` stands beside the round's variables in
`GBCA/ABDY/MessagesAndVariables.lean`, the two of them being the components of a round's state; what
follows is its step relation. -/

/-- The step relation of the round's network. All transitions are
Dirac. -/
inductive GBCANetworkStep (P : Parameters) (r : ℕ) :
    NetworkState P.n → GBCALabel P.n → PMF (NetworkState P.n) → Prop
  /-- The network's half of a multicast: sent the message under its sender.
  Authenticity is the sender's half of the synchronised step (D5). -/
  | send (w : NetworkState P.n) (j : Fin P.n) (m : GBCA.ByABDY.Message) :
      GBCANetworkStep P r w (Sum.inr (.send j m)) (PMF.pure (w.recordGBCASend j m))
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (`Algorithm.deliver`; D5). -/
  | deliver (w : NetworkState P.n) (i j : Fin P.n) (m : GBCA.ByABDY.Message) (h : m ∈ w.sent j) :
      GBCANetworkStep P r w (Sum.inr (.deliver i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (`Algorithm.byzantine`; D5, D11). -/
  | byzantineGBCA (w : NetworkState P.n) (k : Fin P.n) (m : GBCA.ByABDY.Message) (hF : k ∈ w.F) :
      GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure (w.recordGBCASend k m))
  /-- The network's half of the call: sent the caller's `⟨INPUT, b⟩`
  (`Algorithm.call`). -/
  | callG (w : NetworkState P.n) (id : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inl (.callG r id b)))
        (PMF.pure (w.recordGBCASend id (.input b)))
  /-- A return sends nothing, and writes the round's bound bit: the label's
  `bnd` is the bit `bound` holds if there is one and `boundOf`'s otherwise, and
  it is written there (`Algorithm.retGrade2`/`retGrade1`/`retGrade0`). -/
  | retGIdle (w : NetworkState P.n) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hbnd : bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out)) :
      GBCANetworkStep P r w (Sum.inl (Sum.inl (.retG r id out bnd)))
        (PMF.pure (w.setBound bnd))
  /-- A call against variables already called sends nothing
  (`Algorithm.callLoop`). -/
  | gbcaCallLoop (w : NetworkState P.n) (id : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) (PMF.pure w)
  /-- A Byzantine call (D11): its `⟨INPUT, b⟩` is sent here, and there is no
  `k ∈ F` guard on this transition — the authorisation belongs to the network
  outside the instance, where the call label stays visible. -/
  | byzantineCallG (w : NetworkState P.n) (k : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallG r k b)))
        (PMF.pure (w.recordGBCASend k (.input b)))
  /-- A Byzantine call against variables already called sends nothing (D11). -/
  | byzantineCallGLoop (w : NetworkState P.n) (k : Fin P.n) (b : Bool) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) (PMF.pure w)
  /-- A Byzantine return sends nothing, and writes the round's bound bit
  exactly as the correct return does (D11). -/
  | byzantineRetG (w : NetworkState P.n) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hbnd : bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out)) :
      GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineRetG r k out bnd)))
        (PMF.pure (w.setBound bnd))

/-! ### The program and the round's network as systems -/

/-- The local graded-agreement program of process `j` in round `r`. -/
noncomputable def gbcaProgram (P : Parameters) (r : ℕ) (j : Fin P.n) :
    System (GBCA.ByABDY.RoundVariables P.n) (GBCALabel P.n) where
  init := GBCA.ByABDY.RoundVariables.initial P.n
  step := GBCAProgramStep P r j

@[simp] theorem gbcaProgram_init (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).init = GBCA.ByABDY.RoundVariables.initial P.n := rfl

@[simp] theorem gbcaProgram_step (P : Parameters) (r : ℕ) (j : Fin P.n)
    (p : GBCA.ByABDY.RoundVariables P.n) (l : GBCALabel P.n) (ν : PMF (GBCA.ByABDY.RoundVariables
      P.n)) :
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

end GBCA.ByABDY
end ABA
end PLTS
