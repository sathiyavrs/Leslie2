/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Broadcast.Spec

/-!
# The vocabulary of one reliable-broadcast instance

The state of one Byzantine Reliable Broadcast instance with designated leader
`ldr` over an arbitrary payload type `M`, and its rows. The rows transcribe
Bracha's algorithm (Bracha 1987; blueprint Algorithm 6). The message pattern,
per process:

* the leader, on being called with `m`, multicasts `⟨INIT, m⟩`;
* `⟨ECHO, m⟩` — multicast on receipt of `⟨INIT, m⟩` from the leader, once;
* `⟨VOTE, m⟩` — multicast on an `n − f` `ECHO m` receipt quorum, or amplified
  from `f + 1` `VOTE m` receipts, once;
* return `m` — on an `n − f` `VOTE m` receipt quorum.

The state is the generic two-part shape (`ABA.SubState`,
`ABA/Vocabulary/NetworkState.lean`): each process's local record and delivered
sets beside the instance's network state, under the development's D1
(determinised corruption) and D5 (set-based network) conventions.

`ImplStep` is the rows of the instance `BRB.sub` (`ABA/Broadcast/Sub.lean`) —
the `n` per-process programs beside the instance's network — stated over that
product state, one constructor per case of `BRB.sub_step_iff_row`. It is a
relation on the product state; the system is the composition.

There is no participation guard here: only the leader is called, and every
other process runs its handlers unconditionally — Bracha's protocol has no
per-process input. The write-once `sentEcho` / `sentVote` fields carry the
"having not sent" guards of the source's `upon` clauses; the amplification
rule (`voteAmp`) and the quorum rule (`voteQuorum`) write the same field, so a
process votes at most once whichever rule fires first.
-/

namespace PLTS
namespace ABA
namespace BRB

/-- The message levels of Bracha's protocol. -/
inductive BMsg (M : Type) : Type
  /-- `⟨INIT, m⟩` — the leader's broadcast of its payload. -/
  | init (m : M)
  /-- `⟨ECHO, m⟩`. -/
  | echo (m : M)
  /-- `⟨VOTE, m⟩`. -/
  | vote (m : M)
  deriving DecidableEq

/-- The local record of one process in one BRB instance. -/
structure PState (M : Type) : Type where
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
def PState.initial (M : Type) : PState M where
  input := none
  sentEcho := none
  sentVote := none
  returned := false

/-- The state of one BRB implementation instance: the `n` local states beside the
instance's network state. -/
abbrev ImplState (n : ℕ) (M : Type) : Type := SubState n (PState M) (BMsg M)

/-- The initial BRB implementation state. -/
def ImplState.initial (n : ℕ) (M : Type) : ImplState n M :=
  SubState.initial n (BMsg M) (PState.initial M)

variable {M : Type} [DecidableEq M]

/-- The rows of the reliable-broadcast instance with leader `ldr`
(`BRB.sub`, `ABA/Broadcast/Sub.lean`), stated over the product state: one
constructor per case of `BRB.sub_step_iff_row`. The call and the call loop are
the two rows of `call m`, which the instance takes at two labels. All
transitions are Dirac. -/
inductive ImplStep (P : Params) (ldr : Fin P.n) :
    ImplState P.n M → Lab P.n M → PMF (ImplState P.n M) → Prop
  /-- The environment call arrives at the leader: record the payload and
  multicast `⟨INIT, m⟩`. -/
  | call (s : ImplState P.n M) (m : M)
      (h : (s.proc ldr).input = none) :
      ImplStep P ldr s (.call m)
        (PMF.pure ((s.setProc ldr { s.proc ldr with input := some m }).mcast
          ldr (.init m)))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : ImplState P.n M) (m : M) :
      ImplStep P ldr s (.call m) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : ImplState P.n M) (i j : Fin P.n) (m : BMsg M)
      (h : m ∈ s.sent j) :
      ImplStep P ldr s .tau (PMF.pure (s.recvMsg i j m))
  /-- `ECHO`: `⟨INIT, m⟩` received from the leader, no `ECHO` sent yet. -/
  | echo (s : ImplState P.n M) (j : Fin P.n) (m : M)
      (hrecv : BMsg.init m ∈ s.recv j ldr)
      (hsend : (s.proc j).sentEcho = none) :
      ImplStep P ldr s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentEcho := some m }).mcast
          j (.echo m)))
  /-- `VOTE` (quorum case): an `n − f` `ECHO m` receipt quorum, no `VOTE`
  sent yet. -/
  | voteQuorum (s : ImplState P.n M) (j : Fin P.n) (m : M)
      (hcnt : P.n - P.f ≤ s.recvCount j (.echo m))
      (hsend : (s.proc j).sentVote = none) :
      ImplStep P ldr s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentVote := some m }).mcast
          j (.vote m)))
  /-- `VOTE` (amplification case): `f + 1` `VOTE m` receipts, no `VOTE` sent
  yet. -/
  | voteAmp (s : ImplState P.n M) (j : Fin P.n) (m : M)
      (hcnt : P.f + 1 ≤ s.recvCount j (.vote m))
      (hsend : (s.proc j).sentVote = none) :
      ImplStep P ldr s .tau
        (PMF.pure ((s.setProc j { s.proc j with sentVote := some m }).mcast
          j (.vote m)))
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byz (s : ImplState P.n M) (j : Fin P.n) (m : BMsg M) (h : j ∈ s.F) :
      ImplStep P ldr s .tau (PMF.pure (s.mcast j m))
  /-- Return: an `n − f` `VOTE m` receipt quorum. -/
  | ret (s : ImplState P.n M) (id : Fin P.n) (m : M)
      (hcnt : P.n - P.f ≤ s.recvCount id (.vote m))
      (hr : (s.proc id).returned = false) :
      ImplStep P ldr s (.ret id m)
        (PMF.pure (s.setProc id { s.proc id with returned := true }))
  /-- Corruption (deviation D1). -/
  | fail (s : ImplState P.n M) (id : Fin P.n) :
      ImplStep P ldr s (.fail id) (PMF.pure (s.corrupt P id))

end BRB
end ABA
end PLTS
