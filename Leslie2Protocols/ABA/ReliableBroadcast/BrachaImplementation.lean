/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Specification

/-!
# The vocabulary of one reliable-broadcast instance

The state of one Byzantine Reliable Broadcast instance with designated leader
`ldr` over an arbitrary payload type `M`, and its rows. The rows transcribe
Bracha's algorithm (Bracha 1987) in the form of AFW25's Algorithm 1. The
message pattern, per process:

* the leader, on being called with `m`, multicasts `⟨INIT, m⟩`; * `⟨ECHO, m⟩` — multicast on receipt
of `⟨INIT, m⟩` from the leader, on an
  `ECHO m` receipt quorum, or on `f + 1` `VOTE m` receipts, once;
* `⟨VOTE, m⟩` — multicast on an `ECHO m` receipt quorum, or amplified from
  `f + 1` `VOTE m` receipts, once;
* return `m` — on `2f + 1` `VOTE m` receipts.

The `ECHO` quorum is `ABA.Parameters.echoReceiptQuorum`, more than `(n + f) / 2` senders.

The state is the generic two-part shape (`ABA.InstanceState`,
`ABA/Vocabulary/ProcessAndNetworkState.lean`): each process's local record and delivered
sets beside the instance's network state, under the development's D1
(determinised corruption) and D5 (set-based network) conventions.

`BrachaStep` is the rows of the instance `BRB.brachaInstance`
(`ABA/ReliableBroadcast/BrachaComposition.lean`) — the `n` per-process programs beside the
instance's network — stated over that product state, one constructor per case of
`BRB.brachaInstance_step_iff_row`. It is a relation on the product state; the system is the
composition.

There is no participation guard here: only the leader is called, and every
other process runs its handlers unconditionally — Bracha's protocol has no
per-process input. The write-once `sentEcho` / `sentVote` fields carry the
"having not sent" guards of the source's `upon` clauses; the amplification
rule (`voteAmplification`) and the quorum rule (`voteQuorum`) write the same field, so a
process votes at most once whichever rule fires first.
-/

namespace PLTS
namespace ABA
namespace BRB

/-- The message levels of Bracha's protocol. -/
inductive Message (M : Type) : Type
  /-- `⟨INIT, m⟩` — the leader's broadcast of its payload. -/
  | init (m : M)
  /-- `⟨ECHO, m⟩`. -/
  | echo (m : M)
  /-- `⟨VOTE, m⟩`. -/
  | vote (m : M)
  deriving DecidableEq

/-- The local record of one process in one BRB instance. -/
structure ProcessRecord (M : Type) : Type where
  /-- The leader's call record (`none` before the call; only the leader's is
  ever written). -/
  input : Option M
  /-- The `ECHO` payload multicast, if any (write-once). -/
  sentEcho : Option M
  /-- The `VOTE` payload multicast, if any (write-once). -/
  sentVote : Option M
  /-- Whether this process has returned. -/
  returned : Bool
  deriving DecidableEq

/-- The initial local record. -/
def ProcessRecord.initial (M : Type) : ProcessRecord M where
  input := none
  sentEcho := none
  sentVote := none
  returned := false

/-- The state of one BRB implementation instance: the `n` local states beside the
instance's network state. -/
abbrev BrachaState (n : ℕ) (M : Type) : Type := InstanceState n (ProcessRecord M) (Message M)

/-- The initial BRB implementation state. -/
def BrachaState.initial (n : ℕ) (M : Type) : BrachaState n M :=
  InstanceState.initial n (Message M) (ProcessRecord.initial M)

variable {M : Type} [DecidableEq M]

/-- The rows of the reliable-broadcast instance with leader `ldr`
(`BRB.brachaInstance`, `ABA/ReliableBroadcast/BrachaComposition.lean`), stated over the product
state: one constructor per case of `BRB.brachaInstance_step_iff_row`. The call and the call loop are
the two rows of `call m`, which the instance takes at two labels. All
transitions are Dirac. -/
inductive BrachaStep (P : Parameters) (ldr : Fin P.n) :
    BrachaState P.n M → Label P.n M → PMF (BrachaState P.n M) → Prop
  /-- The environment call arrives at the leader: record the payload and
  multicast `⟨INIT, m⟩`. -/
  | call (s : BrachaState P.n M) (m : M)
      (h : (s.process ldr).input = none) :
      BrachaStep P ldr s (.call m)
        (PMF.pure ((s.setProcess ldr { s.process ldr with input := some m }).multicast
          ldr (.init m)))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : BrachaState P.n M) (m : M) :
      BrachaStep P ldr s (.call m) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : BrachaState P.n M) (i j : Fin P.n) (m : Message M)
      (h : m ∈ s.sent j) :
      BrachaStep P ldr s .tau (PMF.pure (s.receiveMessage i j m))
  /-- `ECHO`: `⟨INIT, m⟩` received from the leader, an `ECHO m` receipt quorum,
  or `f + 1` `VOTE m` receipts; no `ECHO` sent yet. -/
  | echo (s : BrachaState P.n M) (j : Fin P.n) (m : M)
      (hrecv : Message.init m ∈ s.received j ldr ∨ P.echoReceiptQuorum ≤ s.receivedCount j (.echo m)
        ∨
        P.f + 1 ≤ s.receivedCount j (.vote m))
      (hsend : (s.process j).sentEcho = none) :
      BrachaStep P ldr s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentEcho := some m }).multicast
          j (.echo m)))
  /-- `VOTE` (quorum case): an `ECHO m` receipt quorum, no `VOTE` sent yet. -/
  | voteQuorum (s : BrachaState P.n M) (j : Fin P.n) (m : M)
      (hcnt : P.echoReceiptQuorum ≤ s.receivedCount j (.echo m))
      (hsend : (s.process j).sentVote = none) :
      BrachaStep P ldr s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentVote := some m }).multicast
          j (.vote m)))
  /-- `VOTE` (amplification case): `f + 1` `VOTE m` receipts, no `VOTE` sent
  yet. -/
  | voteAmplification (s : BrachaState P.n M) (j : Fin P.n) (m : M)
      (hcnt : P.f + 1 ≤ s.receivedCount j (.vote m))
      (hsend : (s.process j).sentVote = none) :
      BrachaStep P ldr s .tau
        (PMF.pure ((s.setProcess j { s.process j with sentVote := some m }).multicast
          j (.vote m)))
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byzantine (s : BrachaState P.n M) (j : Fin P.n) (m : Message M) (h : j ∈ s.F) :
      BrachaStep P ldr s .tau (PMF.pure (s.multicast j m))
  /-- Return: `2f + 1` `VOTE m` receipts. -/
  | ret (s : BrachaState P.n M) (id : Fin P.n) (m : M)
      (hcnt : 2 * P.f + 1 ≤ s.receivedCount id (.vote m))
      (hr : (s.process id).returned = false) :
      BrachaStep P ldr s (.ret id m)
        (PMF.pure (s.setProcess id { s.process id with returned := true }))
  /-- Corruption (deviation D1). -/
  | fail (s : BrachaState P.n M) (id : Fin P.n) :
      BrachaStep P ldr s (.fail id) (PMF.pure (s.corrupt P id))

end BRB
end ABA
end PLTS
