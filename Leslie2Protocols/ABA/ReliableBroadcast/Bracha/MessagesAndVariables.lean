/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Specification

/-!
# The messages and the records of one reliable-broadcast instance

The three message levels of Bracha's protocol over an arbitrary payload type `M`, the local
record one process keeps in one Byzantine Reliable Broadcast instance, and the composed state
they make with the instance's network.

`Message` carries `⟨INIT, m⟩`, `⟨ECHO, m⟩` and `⟨VOTE, m⟩`. `ProcessVariables` holds the leader's
call in `input`, the `ECHO` and `VOTE` payloads the process has multicast in the write-once
fields `sentEcho` and `sentVote`, which carry the "having not sent" guards of the source's `upon`
clauses, and the return in `returned`.

`BrachaState` is the generic two-part shape `ABA.InstanceState`
(`ABA/Vocabulary/ProcessAndNetworkState.lean`): each process's record and delivered sets beside
the instance's network state, under the development's D1 (determinised corruption) and D5
(set-based network) conventions.
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
structure ProcessVariables (M : Type) : Type where
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
def ProcessVariables.initial (M : Type) : ProcessVariables M where
  input := none
  sentEcho := none
  sentVote := none
  returned := false

/-- The state of one BRB implementation instance: the `n` local states beside the
instance's network state. -/
abbrev BrachaState (n : ℕ) (M : Type) : Type := InstanceState n (ProcessVariables M) (Message M)

/-- The initial BRB implementation state. -/
def BrachaState.initial (n : ℕ) (M : Type) : BrachaState n M :=
  InstanceState.initial n (Message M) (ProcessVariables.initial M)

end BRB
end ABA
end PLTS
