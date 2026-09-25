/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.MessagesAndVariables
import Leslie2Protocols.Framework.Relabel

/-!
# The components of one reliable-broadcast instance

One Byzantine Reliable Broadcast instance with designated leader `ldr` over an arbitrary payload
type `M`, taken apart into the pieces that run it: `n` per-process programs beside the instance's
network.

A program holds one process's variables and the messages delivered to it, indexed by sender
(`ABA.LocalState`). It holds no sent set and no corrupted set; its guards read its own variables and
its own delivered sets, never the identity of the caller. The network holds the per-sender sent
sets and the corrupted set (`ABA.NetworkState`), and reads no program's variables. A multicast is a
synchronised step of the sender, which writes its variables, and the network, which records the
message. A delivery is a synchronised step of the network, which checks that the message is sent
under the named sender, and the receiver, which files it under that sender.

`ProgramStep` is the step relation of process `j`'s program and `NetworkStep` that of the
instance's network. `broadcastProgram` and `broadcastNetwork` are the two automata they carry.

## The alphabets

The specification's `call m` carries two transitions, the call and the input-enabledness loop.
The composition splits them across two labels. The leader's variables and the network's sent sets
are different components, so a single label carrying both transitions would also carry the two
mixed pairs: the leader looping while the network posts `⟨INIT, m⟩`, and the leader recording its
payload while the network posts nothing. The loop therefore has a label of its own,
`LoopLabel.callLoop m`, and the interface alphabet is
`InstanceLabel n M = Label n M ⊕ LoopLabel M`.

The instance-internal alphabet `BroadcastLabel n M = InstanceLabel n M ⊕ BroadcastEvent n M` puts
the two synchronisation labels, the multicast and the delivery, beside the interface. Its silent
label is
`Sum.inl τ`, so every `Sum.inr` label is observable and hence hideable, and `broadcastEvents`
collects the labels the instance hides.

## Model and deviations

* **D1 (determinised `fail`).** `NetworkState.corrupt` is the total Dirac function guarded by
  `id ∉ F ∧ |F| < f`. It is the network's own transition, and the programs are unchanged on
  `fail`: their variables are corruption-blind.
* **D5 (set-based network).** Multicasts are idempotent: `sent j` is the set of messages `j` has
  multicast, and `received k` at a program is the set of messages from `k` delivered there.
  Thresholds count distinct senders. A corrupted sender's injections enter its sent set through
  the network's own silent transition.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M]

/-! ### The interface alphabet and the instance-internal alphabet -/

/-- The interface label of the call loop. The specification's `call m` carries
the call and the input-enabledness loop; the composition takes the loop on a
label of its own. -/
inductive LoopLabel (M : Type) : Type
  /-- The input-enabledness loop of `call m`. -/
  | callLoop (m : M)
  deriving DecidableEq

/-- The instance's interface alphabet: the specification's alphabet with the
call loop beside it. -/
abbrev InstanceLabel (n : ℕ) (M : Type) : Type := Label n M ⊕ LoopLabel M

/-- The labels a program and the instance's network synchronise on: the multicast and the
delivery. -/
inductive BroadcastEvent (n : ℕ) (M : Type) : Type
  /-- Process `j` hands `m` to the instance's network. -/
  | send (j : Fin n) (m : Message M)
  /-- The network delivers `j`'s `m` to `i`. -/
  | deliver (i j : Fin n) (m : Message M)
  deriving DecidableEq

/-- The instance-internal alphabet: the interface alphabet plus the two
synchronisation labels. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev BroadcastLabel (n : ℕ) (M : Type) : Type := InstanceLabel n M ⊕ BroadcastEvent n M

/-- The synchronisation labels, hidden by the instance. -/
def broadcastEvents (n : ℕ) (M : Type) : Set (BroadcastLabel n M) := {l | ∃ e : BroadcastEvent n M,
  l = Sum.inr e}

@[simp] theorem inl_notMem_broadcastEvents {n : ℕ} {M : Type} (l : InstanceLabel n M) :
    Sum.inl l ∉ broadcastEvents n M := by
  simp [broadcastEvents]

@[simp] theorem inr_mem_broadcastEvents {n : ℕ} {M : Type} (e : BroadcastEvent n M) :
    Sum.inr e ∈ broadcastEvents n M := ⟨e, rfl⟩

@[simp] theorem broadcastLabel_tau (n : ℕ) (M : Type) :
    (Silent.τ : BroadcastLabel n M) = Sum.inl (Sum.inl Label.tau) := rfl

/-! ### The local program

Process `j`'s program in one instance. Every guard reads its own variables and
the delivered sets and nothing else. A synchronised transition carries the program's
half of a step with the network — on a send the write to its variables, on a
delivery the write of the delivered set. -/

/-- The step relation of the program of process `j` in the instance with leader
`ldr`. All transitions are Dirac. -/
inductive ProgramStep (P : Parameters) (ldr j : Fin P.n) :
    LocalState P.n (ProcessVariables M) (Message M) → BroadcastLabel P.n M →
      PMF (LocalState P.n (ProcessVariables M) (Message M)) → Prop
  /-- The call arrives at the leader: record the payload. The multicast of
  `⟨INIT, m⟩` is the network's half (`BrachaAlgorithm.call`). -/
  | call (p) (m : M) (hj : j = ldr) (h : p.processVariables.input = none) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.call m)))
        (PMF.pure (p.setProcessVariables { p.processVariables with input := some m }))
  /-- A call at the leader is not a non-leader's business. -/
  | callIdle (p) (m : M) (hj : j ≠ ldr) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.call m))) (PMF.pure p)
  /-- The call loop: the variables do not move (`BrachaAlgorithm.callLoop`). -/
  | callLoop (p) (m : M) :
      ProgramStep P ldr j p (Sum.inl (Sum.inr (.callLoop m))) (PMF.pure p)
  /-- `ECHO m`: `⟨INIT, m⟩` delivered from the leader, a quorum of received
  `ECHO m` messages, or `f + 1` received `VOTE m` messages; no `ECHO` sent yet
  (`BrachaAlgorithm.echo`). -/
  | sendEcho (p) (m : M)
      (hrecv : Message.init m ∈ p.received ldr ∨ P.receivedEchoQuorum ≤ p.receivedCount (.echo m) ∨
        P.f + 1 ≤ p.receivedCount (.vote m))
      (hsend : p.processVariables.sentEcho = none) :
      ProgramStep P ldr j p (Sum.inr (.send j (.echo m)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentEcho := some m }))
  /-- `VOTE m` (quorum case): a quorum of received `ECHO m` messages, no `VOTE` sent yet
  (`BrachaAlgorithm.voteQuorum`). -/
  | sendVoteQuorum (p) (m : M) (hcnt : P.receivedEchoQuorum ≤ p.receivedCount (.echo m))
      (hsend : p.processVariables.sentVote = none) :
      ProgramStep P ldr j p (Sum.inr (.send j (.vote m)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentVote := some m }))
  /-- `VOTE m` (amplification case): `f + 1` received `VOTE m` messages, no `VOTE` sent
  yet (`BrachaAlgorithm.voteAmplification`). -/
  | sendVoteAmplification (p) (m : M) (hcnt : P.f + 1 ≤ p.receivedCount (.vote m))
      (hsend : p.processVariables.sentVote = none) :
      ProgramStep P ldr j p (Sum.inr (.send j (.vote m)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentVote := some m }))
  /-- A multicast by another process: not `j`'s business. -/
  | sendIdle (p) (i : Fin P.n) (m : Message M) (hi : i ≠ j) :
      ProgramStep P ldr j p (Sum.inr (.send i m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under its sender.
  Authenticity is the network's conjunct (`BrachaAlgorithm.deliver`; D5). -/
  | deliverReceive (p) (i : Fin P.n) (m : Message M) :
      ProgramStep P ldr j p (Sum.inr (.deliver j i m)) (PMF.pure (p.deliverTo i m))
  /-- A delivery to another process: not `j`'s business. -/
  | deliverIdle (p) (i k : Fin P.n) (m : Message M) (hi : i ≠ j) :
      ProgramStep P ldr j p (Sum.inr (.deliver i k m)) (PMF.pure p)
  /-- Return: `2f + 1` received `VOTE m` messages on its own delivered sets,
  and it has not returned (`BrachaAlgorithm.ret`). -/
  | ret (p) (m : M) (hcnt : 2 * P.f + 1 ≤ p.receivedCount (.vote m)) (hr :
      p.processVariables.returned =
    false) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret j m)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- A return at another process: not `j`'s business. -/
  | retIdle (p) (i : Fin P.n) (m : M) (hi : i ≠ j) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret i m))) (PMF.pure p)
  /-- Corruption is the network's own write, and the programs' variables are
  corruption-blind (D1). -/
  | failIdle (p) (i : Fin P.n) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.fail i))) (PMF.pure p)

/-! ### The instance's network

The one local state of the instance that holds what no program may see: the
per-sender sent sets and the corrupted set. It participates in every send by
recording the message and in every delivery by checking that the message is
sent, and it is where a corrupted sender's injections enter (D5). -/

/-- The step relation of the instance's network. All transitions are Dirac. -/
inductive NetworkStep (P : Parameters) (ldr : Fin P.n) :
    NetworkState P.n (Message M) → BroadcastLabel P.n M → PMF (NetworkState P.n (Message M)) → Prop
  /-- The network's half of the call: the leader's `⟨INIT, m⟩` is sent
  (`BrachaAlgorithm.call`). -/
  | call (w) (m : M) :
      NetworkStep P ldr w (Sum.inl (Sum.inl (.call m))) (PMF.pure (w.recordSent ldr (.init m)))
  /-- The call loop sends nothing (`BrachaAlgorithm.callLoop`). -/
  | callLoop (w) (m : M) :
      NetworkStep P ldr w (Sum.inl (Sum.inr (.callLoop m))) (PMF.pure w)
  /-- The network's half of a multicast: sent the message under its sender.
  Authenticity is the sender's participation in the synchronised step (D5). -/
  | send (w) (j : Fin P.n) (m : Message M) :
      NetworkStep P ldr w (Sum.inr (.send j m)) (PMF.pure (w.recordSent j m))
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (`BrachaAlgorithm.deliver`; D5). -/
  | deliver (w) (i j : Fin P.n) (m : Message M) (h : m ∈ w.sent j) :
      NetworkStep P ldr w (Sum.inr (.deliver i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (`BrachaAlgorithm.byzantine`; D5). -/
  | byzantine (w) (j : Fin P.n) (m : Message M) (h : j ∈ w.F) :
      NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure (w.recordSent j m))
  /-- A return sends nothing (`BrachaAlgorithm.ret`). -/
  | retIdle (w) (i : Fin P.n) (m : M) :
      NetworkStep P ldr w (Sum.inl (Sum.inl (.ret i m))) (PMF.pure w)
  /-- Corruption (deviation D1). -/
  | fail (w) (i : Fin P.n) :
      NetworkStep P ldr w (Sum.inl (Sum.inl (.fail i))) (PMF.pure (w.corrupt P i))

/-! ### The instance -/

/-- The program of process `j` in the instance with leader `ldr`. -/
noncomputable def broadcastProgram (P : Parameters) (ldr j : Fin P.n) :
    System (LocalState P.n (ProcessVariables M) (Message M)) (BroadcastLabel P.n M) where
  init := LocalState.initial P.n (Message M) (ProcessVariables.initial M)
  step := ProgramStep P ldr j

@[simp] theorem broadcastProgram_init (P : Parameters) (ldr j : Fin P.n) :
    (broadcastProgram P ldr j (M := M)).init = LocalState.initial P.n (Message M)
      (ProcessVariables.initial M) :=
      rfl

@[simp] theorem broadcastProgram_step (P : Parameters) (ldr j : Fin P.n)
    (p : LocalState P.n (ProcessVariables M) (Message M)) (l : BroadcastLabel P.n M)
    (ν : PMF (LocalState P.n (ProcessVariables M) (Message M))) :
    (broadcastProgram P ldr j).step p l ν ↔ ProgramStep P ldr j p l ν := Iff.rfl

/-- The instance's network. -/
noncomputable def broadcastNetwork (P : Parameters) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (NetworkState P.n (Message M)) (BroadcastLabel P.n M) where
  init := NetworkState.initial P.n (Message M)
  step := NetworkStep P ldr

@[simp] theorem broadcastNetwork_init (P : Parameters) (ldr : Fin P.n) :
    (broadcastNetwork P ldr M).init = NetworkState.initial P.n (Message M) := rfl

@[simp] theorem broadcastNetwork_step (P : Parameters) (ldr : Fin P.n) (w : NetworkState P.n
  (Message M))
    (l : BroadcastLabel P.n M) (μ : PMF (NetworkState P.n (Message M))) :
    (broadcastNetwork P ldr M).step w l μ ↔ NetworkStep P ldr w l μ := Iff.rfl

end BRB
end ABA
end PLTS
