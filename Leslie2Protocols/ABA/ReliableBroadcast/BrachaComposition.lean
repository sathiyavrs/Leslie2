/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.BrachaImplementation
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The reliable-broadcast instance, composed

One Byzantine Reliable Broadcast instance with designated leader `ldr` over an
arbitrary payload type `M`, taken apart into the pieces that run it: `n`
per-process programs beside the instance's network.

A program holds one process's local record and the messages delivered to it,
indexed by sender (`ABA.LocalState`). It holds no sent set and no corrupted
set; its guards read its own record and its own delivered sets, never the
identity of the caller. The network holds the per-sender sent sets and the
corrupted set (`ABA.NetworkState`), and reads no program's record. A multicast
is a joint step of the sender, which writes its record, and the network, which
records the message; a delivery is a joint step of the network, which checks
that the message is sent under the named sender, and the receiver, which files
it under that sender's row.

The two rendezvous are labels of the instance-internal alphabet
`BroadcastLabel n M = InstanceLabel n M ⊕ BroadcastEvent n M`, and they are hidden before anything
outside sees the instance: `brachaInstance` speaks `InstanceLabel n M`, in which the instance's
interface is the leader's call, the per-process returns, corruption and the call loop.

## The alphabet

The specification's `call m` carries two rows, the call and the
input-enabledness loop. The composition splits them across two labels. The
leader's record and the network's sent sets are different components, so a
single label carrying both rows would also carry the two mixed pairs — the
leader looping while the network posts `⟨INIT, m⟩`, and the leader recording
its payload while the network posts nothing. The loop therefore has a label of
its own, `LoopLabel.callLoop m`, and the specification is read along `specificationLabelMap`,
which sends that label to `call m`: the specification answers it on its own
loop row. The interface alphabet is `InstanceLabel n M = Label n M ⊕ LoopLabel M`.

## The rows

`brachaInstance_step_iff_row` is the row characterisation: at a specification label `l₀`,
the transitions of the composition over the labels `specificationLabelMap` sends to `l₀` are
exactly the `l₀`-rows of `BRB.BrachaStep` (`ABA/ReliableBroadcast/BrachaImplementation.lean`), one
constructor per case, on the same product state and with the same distribution.
The call and the call loop are the two rows of `call m`, taken at the two
labels; every other specification label has a single label over it.

## Model and deviations

* **D1 (determinised `fail`).** `NetworkState.corrupt` is the total Dirac
  function guarded by `id ∉ F ∧ |F| < f`. It is the network's own row, and the
  programs answer `fail` by standing still: the local records are
  corruption-blind.
* **D5 (set-based network).** Multicasts are idempotent: `sent j` is the set of
  messages `j` has multicast, and `received k` at a program is the set of messages
  from `k` delivered there. Thresholds count distinct senders. A corrupted
  sender's injections enter its sent set through the network's own silent row.
* **D27 (safety only).** The specification the instance is replaced by carries
  Validity and Agreement; Totality is out of scope.
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

/-- The internal rendezvous of one instance: the multicast and the delivery. -/
inductive BroadcastEvent (n : ℕ) (M : Type) : Type
  /-- Process `j` hands `m` to the instance's network. -/
  | send (j : Fin n) (m : Message M)
  /-- The network delivers `j`'s `m` to `i`. -/
  | deliver (i j : Fin n) (m : Message M)
  deriving DecidableEq

/-- The instance-internal alphabet: the interface alphabet plus the two
rendezvous. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev BroadcastLabel (n : ℕ) (M : Type) : Type := InstanceLabel n M ⊕ BroadcastEvent n M

/-- The rendezvous labels, hidden by the instance. -/
def broadcastEvents (n : ℕ) (M : Type) : Set (BroadcastLabel n M) := {l | ∃ e : BroadcastEvent n M,
  l = Sum.inr e}

@[simp] theorem inl_notMem_broadcastEvents {n : ℕ} {M : Type} (l : InstanceLabel n M) :
    Sum.inl l ∉ broadcastEvents n M := by
  simp [broadcastEvents]

@[simp] theorem inr_mem_broadcastEvents {n : ℕ} {M : Type} (e : BroadcastEvent n M) :
    Sum.inr e ∈ broadcastEvents n M := ⟨e, rfl⟩

@[simp] theorem blab_tau (n : ℕ) (M : Type) :
    (Silent.τ : BroadcastLabel n M) = Sum.inl (Sum.inl Label.tau) := rfl

/-! ### The local program

Process `j`'s program in one instance. Every guard reads the local record and
the delivered sets and nothing else. A rendezvous row carries the program's
half of a joint step with the network — on a send the record write, on a
delivery the write of the delivered set. -/

/-- The step relation of the program of process `j` in the instance with leader
`ldr`. All transitions are Dirac. -/
inductive ProgramStep (P : Parameters) (ldr j : Fin P.n) :
    LocalState P.n (ProcessRecord M) (Message M) → BroadcastLabel P.n M →
      PMF (LocalState P.n (ProcessRecord M) (Message M)) → Prop
  /-- The call arrives at the leader: record the payload. The multicast of
  `⟨INIT, m⟩` is the network's half (`BrachaStep.call`). -/
  | call (p) (m : M) (hj : j = ldr) (h : p.process.input = none) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.call m)))
        (PMF.pure (p.setProcess { p.process with input := some m }))
  /-- A call at the leader is not a non-leader's business. -/
  | callIdle (p) (m : M) (hj : j ≠ ldr) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.call m))) (PMF.pure p)
  /-- The call loop: the record does not move (`BrachaStep.callLoop`). -/
  | callLoop (p) (m : M) :
      ProgramStep P ldr j p (Sum.inl (Sum.inr (.callLoop m))) (PMF.pure p)
  /-- `ECHO m`: `⟨INIT, m⟩` delivered from the leader, an `ECHO m` receipt
  quorum, or `f + 1` `VOTE m` receipts; no `ECHO` sent yet
  (`BrachaStep.echo`). -/
  | sendEcho (p) (m : M)
      (hrecv : Message.init m ∈ p.received ldr ∨ P.echoQuorum ≤ p.receivedCount (.echo m) ∨
        P.f + 1 ≤ p.receivedCount (.vote m))
      (hsend : p.process.sentEcho = none) :
      ProgramStep P ldr j p (Sum.inr (.send j (.echo m)))
        (PMF.pure (p.setProcess { p.process with sentEcho := some m }))
  /-- `VOTE m` (quorum case): an `ECHO m` receipt quorum, no `VOTE` sent yet
  (`BrachaStep.voteQuorum`). -/
  | sendVoteQuorum (p) (m : M) (hcnt : P.echoQuorum ≤ p.receivedCount (.echo m))
      (hsend : p.process.sentVote = none) :
      ProgramStep P ldr j p (Sum.inr (.send j (.vote m)))
        (PMF.pure (p.setProcess { p.process with sentVote := some m }))
  /-- `VOTE m` (amplification case): `f + 1` `VOTE m` receipts, no `VOTE` sent
  yet (`BrachaStep.voteAmplification`). -/
  | sendVoteAmplification (p) (m : M) (hcnt : P.f + 1 ≤ p.receivedCount (.vote m))
      (hsend : p.process.sentVote = none) :
      ProgramStep P ldr j p (Sum.inr (.send j (.vote m)))
        (PMF.pure (p.setProcess { p.process with sentVote := some m }))
  /-- A multicast by another process: not `j`'s business. -/
  | sendIdle (p) (i : Fin P.n) (m : Message M) (hi : i ≠ j) :
      ProgramStep P ldr j p (Sum.inr (.send i m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's row.
  Authenticity is the network's conjunct (`BrachaStep.deliver`; D5). -/
  | deliverReceive (p) (i : Fin P.n) (m : Message M) :
      ProgramStep P ldr j p (Sum.inr (.deliver j i m)) (PMF.pure (p.deliverTo i m))
  /-- A delivery to another process: not `j`'s business. -/
  | deliverIdle (p) (i k : Fin P.n) (m : Message M) (hi : i ≠ j) :
      ProgramStep P ldr j p (Sum.inr (.deliver i k m)) (PMF.pure p)
  /-- Return: `2f + 1` `VOTE m` receipts on the record's own delivered sets,
  and the record has not returned (`BrachaStep.ret`). -/
  | ret (p) (m : M) (hcnt : 2 * P.f + 1 ≤ p.receivedCount (.vote m)) (hr : p.process.returned =
    false) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret j m)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- A return at another process: not `j`'s business. -/
  | retIdle (p) (i : Fin P.n) (m : M) (hi : i ≠ j) :
      ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret i m))) (PMF.pure p)
  /-- Corruption is the network's own write, and the local records are
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
  (`BrachaStep.call`). -/
  | call (w) (m : M) :
      NetworkStep P ldr w (Sum.inl (Sum.inl (.call m))) (PMF.pure (w.recordSent ldr (.init m)))
  /-- The call loop sends nothing (`BrachaStep.callLoop`). -/
  | callLoop (w) (m : M) :
      NetworkStep P ldr w (Sum.inl (Sum.inr (.callLoop m))) (PMF.pure w)
  /-- The network's half of a multicast: sent the message under its sender.
  Authenticity is the sender's joint participation (D5). -/
  | send (w) (j : Fin P.n) (m : Message M) :
      NetworkStep P ldr w (Sum.inr (.send j m)) (PMF.pure (w.recordSent j m))
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (`BrachaStep.deliver`; D5). -/
  | deliver (w) (i j : Fin P.n) (m : Message M) (h : m ∈ w.sent j) :
      NetworkStep P ldr w (Sum.inr (.deliver i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (`BrachaStep.byzantine`; D5). -/
  | byzantine (w) (j : Fin P.n) (m : Message M) (h : j ∈ w.F) :
      NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure (w.recordSent j m))
  /-- A return sends nothing (`BrachaStep.ret`). -/
  | retIdle (w) (i : Fin P.n) (m : M) :
      NetworkStep P ldr w (Sum.inl (Sum.inl (.ret i m))) (PMF.pure w)
  /-- Corruption (deviation D1). -/
  | fail (w) (i : Fin P.n) :
      NetworkStep P ldr w (Sum.inl (Sum.inl (.fail i))) (PMF.pure (w.corrupt P i))

/-! ### The instance -/

/-- The program of process `j` in the instance with leader `ldr`. -/
noncomputable def broadcastProgram (P : Parameters) (ldr j : Fin P.n) :
    System (LocalState P.n (ProcessRecord M) (Message M)) (BroadcastLabel P.n M) where
  init := LocalState.initial P.n (Message M) (ProcessRecord.initial M)
  step := ProgramStep P ldr j

@[simp] theorem broadcastProgram_init (P : Parameters) (ldr j : Fin P.n) :
    (broadcastProgram P ldr j (M := M)).init = LocalState.initial P.n (Message M)
      (ProcessRecord.initial M) :=
      rfl

@[simp] theorem broadcastProgram_step (P : Parameters) (ldr j : Fin P.n)
    (p : LocalState P.n (ProcessRecord M) (Message M)) (l : BroadcastLabel P.n M)
    (ν : PMF (LocalState P.n (ProcessRecord M) (Message M))) :
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

/-- The programs beside the network, over the instance-internal alphabet. -/
noncomputable def brachaInstanceExtended (P : Parameters) (ldr : Fin P.n) (M : Type) [DecidableEq M]
  :
    System (BrachaState P.n M) (BroadcastLabel P.n M) :=
  (System.syncProduct (broadcastProgram P ldr (M := M))).parallel (broadcastNetwork P ldr M)

/-- **The reliable-broadcast instance**: the programs beside the network, the
two rendezvous hidden, the result read back over the interface alphabet. -/
noncomputable def brachaInstance (P : Parameters) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (BrachaState P.n M) (InstanceLabel P.n M) :=
  ((brachaInstanceExtended P ldr M).abstract (broadcastEvents P.n M)).relabel

@[simp] theorem brachaInstance_init (P : Parameters) (ldr : Fin P.n) :
    (brachaInstance P ldr M).init = BrachaState.initial P.n M := rfl

/-! ### The specification read over the instance's interface

The specification speaks `Label n M`; the instance speaks `InstanceLabel n M`, in which
the call loop is a label of its own. `specificationLabelMap` is the projection that
identifies the loop with the specification label it stands for, so that the
specification's own loop row answers it. -/

/-- The projection of the interface alphabet onto the specification's
alphabet. -/
def specificationLabelMap (n : ℕ) (M : Type) : InstanceLabel n M → Option (Label n M)
  | Sum.inl l => some l
  | Sum.inr (.callLoop m) => some (.call m)

@[simp] theorem specificationLabelMap_inl {n : ℕ} {M : Type} (l : Label n M) :
    specificationLabelMap n M (Sum.inl l) = some l := rfl

@[simp] theorem specificationLabelMap_callLoop {n : ℕ} {M : Type} (m : M) :
    specificationLabelMap n M (Sum.inr (.callLoop m)) = some (.call m) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specificationLabelMap_tau (n : ℕ) (M : Type) :
    specificationLabelMap n M (Silent.τ : InstanceLabel n M) = some (Silent.τ : Label n M) := rfl

/-- Only the silent label projects to the silent label: the call loop projects
to the call. -/
theorem specificationLabelMap_eq_tau {n : ℕ} {M : Type} {l : InstanceLabel n M} (h :
  specificationLabelMap n M l = some Label.tau) :
    l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e; simp at h

/-- Every interface label carries a specification label. -/
theorem specificationLabelMap_isSome {n : ℕ} {M : Type} (l : InstanceLabel n M) : ∃ l₀,
  specificationLabelMap n M l = some l₀ := by
    cases l with
  | inl l₀ => exact ⟨l₀, rfl⟩
  | inr e => cases e; exact ⟨_, rfl⟩

/-- **The lifted specification**: the specification instance with leader `ldr`,
read over the instance's interface. -/
noncomputable def specificationOverInstanceAlphabet (P : Parameters) (ldr : Fin P.n) (M : Type) :
    System (SpecState P.n M) (InstanceLabel P.n M) :=
  (specInst P ldr M).mapIdle (specificationLabelMap P.n M)

@[simp] theorem specificationOverInstanceAlphabet_init {M : Type} (P : Parameters) (ldr : Fin P.n) :
    (specificationOverInstanceAlphabet P ldr M).init = SpecState.initial P.n M := rfl

/-! ### Determinacy

Both rule tables written here are Dirac, so the instance is an LTS. -/

/-- Every program transition is Dirac. -/
theorem programStep_dirac {P : Parameters} {ldr j : Fin P.n} {p : LocalState P.n (ProcessRecord M)
  (Message M)}
    {l : BroadcastLabel P.n M} {ν : PMF (LocalState P.n (ProcessRecord M) (Message M))}
    (h : ProgramStep P ldr j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem networkStep_dirac {P : Parameters} {ldr : Fin P.n} {w : NetworkState P.n (Message M)}
    {l : BroadcastLabel P.n M} {μ : PMF (NetworkState P.n (Message M))} (h : NetworkStep P ldr w l
      μ) :
    ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem broadcastProgram_isLTS (P : Parameters) (ldr j : Fin P.n) : (broadcastProgram P ldr j (M :=
  M)).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The network is an LTS. -/
theorem broadcastNetwork_isLTS (P : Parameters) (ldr : Fin P.n) : (broadcastNetwork P ldr M).IsLTS
  :=
  fun _ _ _ h => networkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem broadcastProgramProduct_isLTS (P : Parameters) (ldr : Fin P.n) :
    (System.syncProduct (broadcastProgram P ldr (M := M))).IsLTS :=
  System.syncProduct_isLTS (broadcastProgram_isLTS P ldr)

/-- The programs beside the network form an LTS. -/
theorem brachaInstanceExtended_isLTS (P : Parameters) (ldr : Fin P.n) : (brachaInstanceExtended P
  ldr
  M).IsLTS :=
  System.parallel_isLTS (broadcastProgramProduct_isLTS P ldr) (broadcastNetwork_isLTS P ldr)

/-- The instance is an LTS. -/
theorem brachaInstance_isLTS (P : Parameters) (ldr : Fin P.n) : (brachaInstance P ldr M).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (brachaInstanceExtended_isLTS P ldr) _)

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverInstanceAlphabet_isLTS {M : Type} (P : Parameters) (ldr : Fin P.n) :
  (specificationOverInstanceAlphabet P ldr M).IsLTS :=
  System.mapIdle_isLTS _ (specInst_isLTS P ldr)

/-- No program rule fires on `τ`: a program only ever moves in a rendezvous or
on one of the instance's interface labels. The instance's silent transitions
are therefore exactly the network's injections and the hidden rendezvous. -/
theorem programStep_no_tau {P : Parameters} {ldr j : Fin P.n} {p : LocalState P.n (ProcessRecord M)
  (Message M)}
    {ν : PMF (LocalState P.n (ProcessRecord M) (Message M))}
    (h : ProgramStep P ldr j p (Silent.τ : BroadcastLabel P.n M) ν) : False := by
  rw [blab_tau] at h; cases h

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `specificationLabelMap`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the
instance actually took — this is what turns a specification `call` run into the
answer to the call loop. -/

/-- The left injection: the interface label a specification label sits at. -/
def labelSection {n : ℕ} {M : Type} : Label n M → InstanceLabel n M := Sum.inl

open scoped Classical in
/-- The section of `specificationLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
noncomputable def sectionAt {n : ℕ} {M : Type} (l₀ : Label n M) (l : InstanceLabel n M) :
    Label n M → InstanceLabel n M :=
  fun x => if x = l₀ then l else labelSection x

@[simp] theorem specificationLabelMap_labelSection {n : ℕ} {M : Type} (x : Label n M) :
    specificationLabelMap n M (labelSection x) = some x := rfl

/-- The left injection reflects the silent label. -/
theorem labelSection_eq_tau {n : ℕ} {M : Type} (x : Label n M) :
    (labelSection x : InstanceLabel n M) = (Silent.τ : InstanceLabel n M) ↔ x = (Silent.τ : Label n
      M) :=
  inl_eq_tau_iff x

theorem specificationLabelMap_sectionAt {n : ℕ} {M : Type} {l₀ : Label n M} {l : InstanceLabel n M}
    (hl : specificationLabelMap n M l = some l₀) (x : Label n M) : specificationLabelMap n M
      (sectionAt l₀ l x) = some x := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specificationLabelMap_labelSection]

theorem sectionAt_tau {n : ℕ} {M : Type} {l₀ : Label n M} {l : InstanceLabel n M}
    (hl : specificationLabelMap n M l = some l₀)
    (hl₀ : l₀ ≠ (Silent.τ : Label n M)) (x : Label n M) :
    sectionAt l₀ l x = (Silent.τ : InstanceLabel n M) ↔ x = (Silent.τ : Label n M) := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Label n M) := by
        rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    exact labelSection_eq_tau x

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_specificationOverInstanceAlphabet {M : Type} (P : Parameters) (ldr : Fin P.n) {s
  s'
  : SpecState P.n M}
    (h : (specInst P ldr M).weakLSilent s s') : (specificationOverInstanceAlphabet P ldr
      M).weakLSilent s s' :=
  System.weakLSilent_mapIdle labelSection (fun _ => rfl) (fun x => labelSection_eq_tau x) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_specificationOverInstanceAlphabet {M : Type} (P : Parameters) (ldr : Fin P.n) {s
  s' :
  SpecState P.n M}
    {l₀ : Label P.n M} {l : InstanceLabel P.n M} (hl₀ : l₀ ≠ (Silent.τ : Label P.n M))
    (hl : specificationLabelMap P.n M l = some l₀)
    (h : (specInst P ldr M).weakLStep s l₀ s') : (specificationOverInstanceAlphabet P ldr
      M).weakLStep s l s' :=
  System.weakLStep_mapIdle (sectionAt l₀ l) (specificationLabelMap_sectionAt hl) (sectionAt_tau hl
    hl₀)
    (by simp [sectionAt]) h

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ syncProduct`; the lemmas below
unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem broadcastProgramProduct_inv {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)} {l : BroadcastLabel P.n M}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M))}
    (h : (System.syncProduct (broadcastProgram P ldr (M := M))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M),
      μ = PMF.pure x ∧ ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => programStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep programStep_no_tau

/-- Build a synchronised transition of the program group from per-process Dirac
steps. -/
theorem broadcastProgramProduct_pure {P : Parameters} {ldr : Fin P.n}
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)} {l : BroadcastLabel P.n M}
    (hl : l ≠ Silent.τ) (h : ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (x i))) :
    (System.syncProduct (broadcastProgram P ldr (M := M))).step u l (PMF.pure x) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program has a `τ` row. -/
theorem broadcastProgramProduct_no_tau {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M))}
    (h : (System.syncProduct (broadcastProgram P ldr (M := M))).step u (Silent.τ : BroadcastLabel
      P.n M) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau hstep

/-- The instance's step relation, unfolded to the hidden-rendezvous case and
the interface-label case. -/
theorem brachaInstance_step_iff (P : Parameters) (ldr : Fin P.n) (q : BrachaState P.n M) (l :
  InstanceLabel P.n M)
    (μ : PMF (BrachaState P.n M)) :
    (brachaInstance P ldr M).step q l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : BroadcastEvent P.n M,
        (brachaInstanceExtended P ldr M).step q (Sum.inr e) μ) ∨
      (brachaInstanceExtended P ldr M).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_broadcastEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_broadcastEvents l, hstep⟩

/-- Build a joint transition of the programs and the network on a rendezvous
label. -/
theorem brachaInstanceExtended_event_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} (e : BroadcastEvent P.n M)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', broadcastProgramProduct_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the programs and the network on a visible
interface label. -/
theorem brachaInstanceExtended_label_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} {l : InstanceLabel P.n M} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl l) (PMF.pure (x, w')) := by
  have hne : (Sum.inl l : BroadcastLabel P.n M) ≠ Silent.τ := by
    rw [blab_tau]; simpa using hl
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure x, PMF.pure w', broadcastProgramProduct_pure hne hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the network from a
network-local one. -/
theorem brachaInstanceExtended_tau_network (P : Parameters) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)}
    (hn : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden rendezvous is a silent transition of the instance. -/
theorem brachaInstance_event_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} (e : BroadcastEvent P.n M)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) (Sum.inl Label.tau) (PMF.pure (x, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inl ⟨rfl, e,
    brachaInstanceExtended_event_step P ldr e hall hn⟩)

/-- A visible interface label is a transition of the instance. -/
theorem brachaInstance_label_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} {l : InstanceLabel P.n M} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) l (PMF.pure (x, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inr (brachaInstanceExtended_label_step P ldr hl hall
    hn))

/-- A network-local injection is a silent transition of the instance. -/
theorem brachaInstance_tau_network (P : Parameters) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)}
    (hn : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) (Sum.inl Label.tau) (PMF.pure (u, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inr (brachaInstanceExtended_tau_network P ldr hn))

/-- A visible transition of the programs beside the network: every program and
the network step on the label, and the joint distribution is their Dirac
product. -/
theorem brachaInstanceExtended_joint_inv {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n,
      LocalState P.n (ProcessRecord M) (Message M)} {w : NetworkState P.n (Message M)}
    {L : BroadcastLabel P.n M} {μ : PMF (BrachaState P.n M)} (hL : L ≠ (Silent.τ : BroadcastLabel
      P.n M))
    (h : (brachaInstanceExtended P ldr M).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n,
      LocalState P.n (ProcessRecord M) (Message M)) (w' : NetworkState P.n (Message M)),
        μ = PMF.pure (x, w') ∧ (∀ i,
          ProgramStep P ldr i (u i) L (PMF.pure (x i))) ∧ NetworkStep P ldr w L (PMF.pure w') := by
  rw [brachaInstanceExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := broadcastProgramProduct_inv hs
    obtain ⟨w', rfl⟩ := networkStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the network is a network-local
injection: no program has a `τ` row. -/
theorem brachaInstanceExtended_tau_inv {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n,
      LocalState P.n (ProcessRecord M) (Message M)} {w : NetworkState P.n (Message M)}
    {μ : PMF (BrachaState P.n M)}
    (h : (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl (Sum.inl Label.tau)) μ) :
    ∃ w' : NetworkState P.n (Message M), μ = PMF.pure (u, w') ∧
      NetworkStep P ldr w (Sum.inl (Sum.inl Label.tau)) (PMF.pure w') := by
  rw [brachaInstanceExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, rfl⟩ | ⟨-, μ₂, hn, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hs broadcastProgramProduct_no_tau
  · obtain ⟨w', rfl⟩ := networkStep_dirac hn
    exact ⟨w', prodPMF_pure_pure _ _, hn⟩

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The record and the distribution are variables,
so `cases` unifies against any local state. -/

section ProcInversion

variable {P : Parameters} {ldr j : Fin P.n} {p : LocalState P.n (ProcessRecord M) (Message M)}
  {ν : PMF (LocalState P.n (ProcessRecord M) (Message M))}

theorem programStep_call_leader {m : M}
    (h : ProgramStep P ldr ldr p (Sum.inl (Sum.inl (.call m))) ν) :
    p.process.input = none ∧ ν = PMF.pure (p.setProcess { p.process with input := some m }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ ldr›

theorem programStep_call_foreign {m : M} (hj : j ≠ ldr)
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.call m))) ν) : ν = PMF.pure p := by
  cases h
  case call => exact absurd ‹j = ldr› hj
  case callIdle => rfl

theorem programStep_callLoop {m : M}
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inr (.callLoop m))) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl

theorem programStep_ret_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret j m))) ν) :
    2 * P.f + 1 ≤ p.receivedCount (.vote m) ∧ p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_ret_foreign {i : Fin P.n} {m : M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret i m))) ν) : ν = PMF.pure p := by
  cases h
  case ret => exact absurd rfl hi
  case retIdle => rfl

theorem programStep_fail {i : Fin P.n}
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.fail i))) ν) : ν = PMF.pure p := by
  cases h
  case failIdle => rfl

theorem programStep_send_init_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.init m))) ν) : False := by
  cases h
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_echo_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.echo m))) ν) :
    (Message.init m ∈ p.received ldr ∨ P.echoQuorum ≤ p.receivedCount (.echo m) ∨
        P.f + 1 ≤ p.receivedCount (.vote m)) ∧ p.process.sentEcho = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho := some m }) := by
  cases h
  case sendEcho => exact ⟨by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_vote_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.vote m))) ν) :
    (P.echoQuorum ≤ p.receivedCount (.echo m) ∨ P.f + 1 ≤ p.receivedCount (.vote m)) ∧
      p.process.sentVote = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentVote := some m }) := by
  cases h
  case sendVoteQuorum => exact ⟨Or.inl (by assumption), by assumption, rfl⟩
  case sendVoteAmplification => exact ⟨Or.inr (by assumption), by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_foreign {i : Fin P.n} {m : Message M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inr (.send i m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hi

theorem programStep_deliver_own {k : Fin P.n} {m : Message M}
    (h : ProgramStep P ldr j p (Sum.inr (.deliver j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_deliver_foreign {i k : Fin P.n} {m : Message M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

end ProcInversion

/-! ### The network's rules, by label class -/

section NetInversion

variable {P : Parameters} {ldr : Fin P.n} {w : NetworkState P.n (Message M)}
  {μ : PMF (NetworkState P.n (Message M))}

theorem networkStep_call {m : M} (h : NetworkStep P ldr w (Sum.inl (Sum.inl (.call m))) μ) :
    μ = PMF.pure (w.recordSent ldr (.init m)) := by
  cases h; rfl

theorem networkStep_callLoop {m : M} (h : NetworkStep P ldr w (Sum.inl (Sum.inr (.callLoop m))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_ret {i : Fin P.n} {m : M}
    (h : NetworkStep P ldr w (Sum.inl (Sum.inl (.ret i m))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_fail {i : Fin P.n} (h : NetworkStep P ldr w (Sum.inl (Sum.inl (.fail i))) μ) :
    μ = PMF.pure (w.corrupt P i) := by
  cases h; rfl

theorem networkStep_send {j : Fin P.n} {m : Message M}
    (h : NetworkStep P ldr w (Sum.inr (.send j m)) μ) : μ = PMF.pure (w.recordSent j m) := by
  cases h; rfl

theorem networkStep_deliver {i j : Fin P.n} {m : Message M}
    (h : NetworkStep P ldr w (Sum.inr (.deliver i j m)) μ) : m ∈ w.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_tau (h : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : Message M), j ∈ w.F ∧ μ = PMF.pure (w.recordSent j m) := by
  cases h
  case byzantine j m hF => exact ⟨j, m, hF, rfl⟩

end NetInversion

/-! ### One state, two presentations

The local states and the network state are the two components of `BrachaState`
(`ABA/ReliableBroadcast/BrachaImplementation.lean`), so the instance and the rule table `BrachaStep`
run on the same state and every rule of the one is a rule of the other read in the
instance state's accessors. What the joint steps deliver, though, is a program
function pinned pointwise — its value at the acting process, and its agreement
with the old one elsewhere — where `BrachaStep` writes with `InstanceState.setProcess`.
The lemmas here close that gap. -/

section Frame

variable {P : Parameters} {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
  {w : NetworkState P.n (Message M)}

omit [DecidableEq M] in
/-- A program function pinned at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem programFunction_update {j : Fin P.n} {q : LocalState P.n (ProcessRecord M) (Message M)}
    (hj : x j = q) (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j q := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

omit [DecidableEq M] in
/-- A record write at one program, with the network state untouched. -/
theorem brachaInstance_setProcess {j : Fin P.n} {pr : ProcessRecord M}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : BrachaState P.n M) = InstanceState.setProcess (u, w) j pr := by
  rw [programFunction_update hj hne]
  rfl

/-- A record write at one program together with the network state recording the
message that write multicasts. -/
theorem brachaInstance_setProcess_recordSent {j : Fin P.n} {pr : ProcessRecord M} {m : Message M}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.recordSent j m) : BrachaState P.n M) = (InstanceState.setProcess (u,
      w) j pr).multicast j m := by
  rw [programFunction_update hj hne]
  rfl

omit [DecidableEq M] in
/-- The programs stand still. -/
theorem brachaInstance_idle (hall : ∀ i, x i = u i) : ((x, w) : BrachaState P.n M) = (u, w) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem brachaInstance_deliver {i k : Fin P.n} {m : Message M}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : BrachaState P.n M) = InstanceState.receiveMessage (u, w) i k m := by
  rw [programFunction_update hi hne]
  rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem brachaInstance_recordSent {k : Fin P.n} {m : Message M} :
    ((u, w.recordSent k m) : BrachaState P.n M) = InstanceState.multicast (u, w) k m := rfl

omit [DecidableEq M] in
/-- Corruption is the network state's own write (D1). -/
theorem brachaInstance_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : BrachaState P.n M) = InstanceState.corrupt P k (u, w) := rfl

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem programStep_update {ldr j : Fin P.n} {q : LocalState P.n (ProcessRecord M) (Message M)}
    {l : BroadcastLabel P.n M} (hj : ProgramStep P ldr j (u j) l (PMF.pure q))
    (hne : ∀ i, i ≠ j → ProgramStep P ldr i (u i) l (PMF.pure (u i))) :
    ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (Function.update u j q i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

end Frame

/-! ### The rows of the instance

Every transition of the instance is one row of `BrachaStep` at the same state,
and the correspondence is strong — one step answers one step, at the
specification label the interface label projects to, with no stuttering
anywhere:

| instance | row |
| --- | --- |
| `call` (leader writes, network records) | `BrachaStep.call` |
| `callLoop` | `BrachaStep.callLoop` |
| hidden `send` rendezvous, by level | `BrachaStep.echo` / `voteQuorum` / `voteAmplification` |
| hidden `deliver` rendezvous | `BrachaStep.deliver` |
| network-local injection | `BrachaStep.byzantine` |
| `ret` | `BrachaStep.ret` |
| `fail` | `BrachaStep.fail` |

The two hidden rendezvous and the network's injection are silent on both sides,
and `specificationLabelMap` takes `τ` to `τ`. -/

/-- **The projection.** -/
theorem brachaInstance_step_row (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l : InstanceLabel P.n M) (μ : PMF (BrachaState P.n M)),
      (brachaInstance P ldr M).step s l μ →
      ∃ l₀, specificationLabelMap P.n M l = some l₀ ∧ BrachaStep P ldr s l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (brachaInstance_step_iff P ldr (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden rendezvous: an internal row
    obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_joint_inv (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_foreign (Ne.symm hi) (hall i))
      have hw : w' = w.recordSent j m := PMF.pure_injective (networkStep_send hn)
      subst hw
      cases m with
      | init m => exact (programStep_send_init_own (hall j)).elim
      | echo m =>
        obtain ⟨hrecv, hsend, hx⟩ := programStep_send_echo_own (hall j)
        rw [brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
        exact BrachaStep.echo _ j m hrecv hsend
      | vote m =>
        obtain ⟨hcnt, hsend, hx⟩ := programStep_send_vote_own (hall j)
        rw [brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
        rcases hcnt with hq | ha
        · exact BrachaStep.voteQuorum _ j m hq hsend
        · exact BrachaStep.voteAmplification _ j m ha hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_foreign (Ne.symm hi') (hall i'))
      rw [brachaInstance_deliver (PMF.pure_injective (programStep_deliver_own (hall i))) hfor]
      exact BrachaStep.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Label.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := brachaInstanceExtended_tau_inv hlab
      obtain ⟨j, m, hF, hw⟩ := networkStep_tau hn
      have hw' : w' = w.recordSent j m := PMF.pure_injective hw
      subst hw'
      refine ⟨Label.tau, rfl, ?_⟩
      rw [brachaInstance_recordSent]
      exact BrachaStep.byzantine _ j m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_joint_inv (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call m =>
          have hw : w' = w.recordSent ldr (.init m) := PMF.pure_injective (networkStep_call hn)
          subst hw
          obtain ⟨hin, hx⟩ := programStep_call_leader (hall ldr)
          have hfor : ∀ i, i ≠ ldr → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_call_foreign hi (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
          exact BrachaStep.call _ m hin
        | ret id m =>
          have hw : w' = w := PMF.pure_injective (networkStep_ret hn)
          subst hw
          obtain ⟨hcnt, hr, hx⟩ := programStep_ret_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_ret_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_setProcess (PMF.pure_injective hx) hfor]
          exact BrachaStep.ret _ id m hcnt hr
        | fail id =>
          have hw : w' = w.corrupt P id := PMF.pure_injective (networkStep_fail hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_idle hidle, brachaInstance_corrupt]
          exact BrachaStep.fail _ id
      | inr e =>
        cases e with
        | callLoop m =>
          have hw : w' = w := PMF.pure_injective (networkStep_callLoop hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_callLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_idle hidle]
          exact BrachaStep.callLoop _ m

/-- **The embedding.** -/
theorem row_brachaInstance_step (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l₀ : Label P.n M) (μ : PMF (BrachaState P.n M)),
      BrachaStep P ldr s l₀ μ →
      ∃ l, specificationLabelMap P.n M l = some l₀ ∧ (brachaInstance P ldr M).step s l μ := by
  rintro ⟨u, w⟩ l₀ μ hrow
  cases hrow with
  | call m h =>
    exact ⟨Sum.inl (.call m), rfl, brachaInstance_label_step P ldr (by simp)
      (programStep_update (ProgramStep.call (u ldr) m rfl h)
        (fun i hi => ProgramStep.callIdle (u i) m hi))
      (NetworkStep.call w m)⟩
  | callLoop m =>
    exact ⟨Sum.inr (.callLoop m), rfl, brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.callLoop (u i) m) (NetworkStep.callLoop w m)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.deliver i j m)
      (programStep_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h)⟩
  | echo j m hrecv hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.echo m))
      (programStep_update (ProgramStep.sendEcho (u j) m hrecv hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo m) (Ne.symm hi)))
      (NetworkStep.send w j (.echo m))⟩
  | voteQuorum j m hcnt hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (programStep_update (ProgramStep.sendVoteQuorum (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))⟩
  | voteAmplification j m hcnt hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (programStep_update (ProgramStep.sendVoteAmplification (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))⟩
  | byzantine j m h =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_tau_network P ldr (NetworkStep.byzantine w j m h)⟩
  | ret id m hcnt hr =>
    exact ⟨Sum.inl (.ret id m), rfl, brachaInstance_label_step P ldr (by simp)
      (programStep_update (ProgramStep.ret (u id) m hcnt hr)
        (fun i hi => ProgramStep.retIdle (u i) id m (Ne.symm hi)))
      (NetworkStep.retIdle w id m)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)⟩

/-- **The row characterisation.** At a specification label `l₀`, the
transitions of the instance over the labels `specificationLabelMap` sends to `l₀` are
exactly the `l₀`-rows of `BrachaStep`, on the same state and with the same
distribution. The call and the call loop are the two rows of `call m`, taken at
the two labels `specificationLabelMap` sends to it; every other specification label has a
single interface label over it. -/
theorem brachaInstance_step_iff_row (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (l₀ : Label P.n M) (μ : PMF (BrachaState P.n M)) :
    (∃ l,
      specificationLabelMap P.n M l = some l₀ ∧ (brachaInstance P ldr M).step s l μ) ↔ BrachaStep P
        ldr s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := brachaInstance_step_row P ldr s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n M)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_brachaInstance_step P ldr s l₀ μ

/-- info: 'PLTS.ABA.BRB.brachaInstance_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaInstance_step_iff_row

end BRB
end ABA
end PLTS
