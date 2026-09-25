/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.MessagesAndVariables

/-!
# The echo certificate

`BRB.EchoWitness P s m` holds when some process in the state `s` has received `⟨ECHO, m⟩` from
an echo quorum, more than `(n + f) / 2` senders. It counts receipts and not correctness, so it is
blind to the corrupted set, and receipts only accumulate, so it survives every transition of the
instance: the simp lemmas here carry it across a record write, a multicast and a corruption, and
`EchoWitness.receiveMessage` carries it across a delivery.

The refinement of the instance into the broadcast specification
(`ABA/ReliableBroadcast/Bracha/RefinesSpecification.lean`) uses the certificate for the
specification's committed value `val`, the one piece of abstract information the specification
tracks and the implementation does not.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-! ### The certificate -/

/-- `m` is echo-certified: some receiver holds an `ECHO m` receipt quorum.
F-blind and monotone — receipts only accumulate. -/
def EchoWitness (P : Parameters) (s : BrachaState P.n M) (m : M) : Prop :=
  ∃ i, P.receivedEchoQuorum ≤ s.receivedCount i (.echo m)

@[simp] theorem echoWitness_setProcessVariables (s : BrachaState P.n M) (j : Fin P.n)
    (p : ProcessVariables M) (m : M) :
    EchoWitness P (s.setProcessVariables j p) m ↔ EchoWitness P s m := by
  simp [EchoWitness]

@[simp] theorem echoWitness_multicast (s : BrachaState P.n M) (j : Fin P.n)
    (x : Message M) (m : M) :
    EchoWitness P (s.multicast j x) m ↔ EchoWitness P s m := by
  simp [EchoWitness]

@[simp] theorem echoWitness_corrupt (s : BrachaState P.n M) (id : Fin P.n) (m : M) :
    EchoWitness P (s.corrupt P id) m ↔ EchoWitness P s m := by
  simp [EchoWitness]

/-- Deliveries preserve the certificate: counts only grow. -/
theorem EchoWitness.receiveMessage {s : BrachaState P.n M} {m : M} (h : EchoWitness P s m)
    (i j : Fin P.n) (x : Message M) : EchoWitness P (s.receiveMessage i j x) m := by
  obtain ⟨i', hi'⟩ := h
  exact ⟨i', le_trans hi' (InstanceState.receivedCount_le_receiveMessage s i j x i' _)⟩

end BRB
end ABA
end PLTS
