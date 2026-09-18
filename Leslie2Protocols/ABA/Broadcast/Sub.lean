/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Broadcast.Impl
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct
import Leslie2Protocols.Framework.IdleFamily

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
`BLab n M = SubLab n M ⊕ BEvt n M`, and they are hidden before anything outside
sees the instance: `sub` speaks `SubLab n M`, in which the instance's interface
is the leader's call, the per-process returns, corruption and the call loop.

## The alphabet

The specification's `call m` carries two rows, the call and the
input-enabledness loop. The composition splits them across two labels. The
leader's record and the network's sent sets are different components, so a
single label carrying both rows would also carry the two mixed pairs — the
leader looping while the network posts `⟨INIT, m⟩`, and the leader recording
its payload while the network posts nothing. The loop therefore has a label of
its own, `Extra.callLoop m`, and the specification is read along `specPull`,
which sends that label to `call m`: the specification answers it on its own
loop row. The interface alphabet is `SubLab n M = Lab n M ⊕ Extra M`.

## The rows

`sub_step_iff_row` is the row characterisation: at a specification label `l₀`,
the transitions of the composition over the labels `specPull` sends to `l₀` are
exactly the `l₀`-rows of `BRB.ImplStep` (`ABA/Broadcast/Impl.lean`), one
constructor per case, on the same product state and with the same distribution.
The call and the call loop are the two rows of `call m`, taken at the two
labels; every other specification label has a single label over it.

## Model and deviations

* **D1 (determinised `fail`).** `NetworkState.corrupt` is the total Dirac
  function guarded by `id ∉ F ∧ |F| < f`. It is the network's own row, and the
  programs answer `fail` by standing still: the local records are
  corruption-blind.
* **D5 (set-based network).** Multicasts are idempotent: `sent j` is the set of
  messages `j` has multicast, and `recv k` at a program is the set of messages
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
inductive Extra (M : Type) : Type
  /-- The input-enabledness loop of `call m`. -/
  | callLoop (m : M)
  deriving DecidableEq

/-- The instance's interface alphabet: the specification's alphabet with the
call loop beside it. -/
abbrev SubLab (n : ℕ) (M : Type) : Type := Lab n M ⊕ Extra M

/-- The internal rendezvous of one instance: the multicast and the delivery. -/
inductive BEvt (n : ℕ) (M : Type) : Type
  /-- Process `j` hands `m` to the instance's network. -/
  | snd (j : Fin n) (m : BMsg M)
  /-- The network delivers `j`'s `m` to `i`. -/
  | dlv (i j : Fin n) (m : BMsg M)
  deriving DecidableEq

/-- The instance-internal alphabet: the interface alphabet plus the two
rendezvous. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev BLab (n : ℕ) (M : Type) : Type := SubLab n M ⊕ BEvt n M

/-- The rendezvous labels, hidden by the instance. -/
def bEvents (n : ℕ) (M : Type) : Set (BLab n M) := {l | ∃ e : BEvt n M, l = Sum.inr e}

@[simp] theorem inl_notMem_bEvents {n : ℕ} {M : Type} (l : SubLab n M) :
    Sum.inl l ∉ bEvents n M := by
  simp [bEvents]

@[simp] theorem inr_mem_bEvents {n : ℕ} {M : Type} (e : BEvt n M) :
    Sum.inr e ∈ bEvents n M := ⟨e, rfl⟩

@[simp] theorem blab_tau (n : ℕ) (M : Type) :
    (Silent.τ : BLab n M) = Sum.inl (Sum.inl Lab.tau) := rfl

/-! ### The local program

Process `j`'s program in one instance. Every guard reads the local record and
the delivered sets and nothing else. A rendezvous row carries the program's
half of a joint step with the network — on a send the record write, on a
delivery the write of the delivered set. -/

/-- The step relation of the program of process `j` in the instance with leader
`ldr`. All transitions are Dirac. -/
inductive ProcStep (P : Params) (ldr j : Fin P.n) :
    LocalState P.n (PState M) (BMsg M) → BLab P.n M →
      PMF (LocalState P.n (PState M) (BMsg M)) → Prop
  /-- The call arrives at the leader: record the payload. The multicast of
  `⟨INIT, m⟩` is the network's half (`ImplStep.call`). -/
  | call (p) (m : M) (hj : j = ldr) (h : p.proc.input = none) :
      ProcStep P ldr j p (Sum.inl (Sum.inl (.call m)))
        (PMF.pure (p.setP { p.proc with input := some m }))
  /-- A call at the leader is not a non-leader's business. -/
  | callIdle (p) (m : M) (hj : j ≠ ldr) :
      ProcStep P ldr j p (Sum.inl (Sum.inl (.call m))) (PMF.pure p)
  /-- The call loop: the record does not move (`ImplStep.callLoop`). -/
  | callLoop (p) (m : M) :
      ProcStep P ldr j p (Sum.inl (Sum.inr (.callLoop m))) (PMF.pure p)
  /-- `ECHO m`: `⟨INIT, m⟩` delivered from the leader, no `ECHO` sent yet
  (`ImplStep.echo`). -/
  | sndEcho (p) (m : M) (hrecv : BMsg.init m ∈ p.recv ldr) (hsend : p.proc.sentEcho = none) :
      ProcStep P ldr j p (Sum.inr (.snd j (.echo m)))
        (PMF.pure (p.setP { p.proc with sentEcho := some m }))
  /-- `VOTE m` (quorum case): an `n − f` `ECHO m` receipt quorum, no `VOTE`
  sent yet (`ImplStep.voteQuorum`). -/
  | sndVoteQuorum (p) (m : M) (hcnt : P.n - P.f ≤ p.recvCount (.echo m))
      (hsend : p.proc.sentVote = none) :
      ProcStep P ldr j p (Sum.inr (.snd j (.vote m)))
        (PMF.pure (p.setP { p.proc with sentVote := some m }))
  /-- `VOTE m` (amplification case): `f + 1` `VOTE m` receipts, no `VOTE` sent
  yet (`ImplStep.voteAmp`). -/
  | sndVoteAmp (p) (m : M) (hcnt : P.f + 1 ≤ p.recvCount (.vote m))
      (hsend : p.proc.sentVote = none) :
      ProcStep P ldr j p (Sum.inr (.snd j (.vote m)))
        (PMF.pure (p.setP { p.proc with sentVote := some m }))
  /-- A multicast by another process: not `j`'s business. -/
  | sndIdle (p) (i : Fin P.n) (m : BMsg M) (hi : i ≠ j) :
      ProcStep P ldr j p (Sum.inr (.snd i m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's row.
  Authenticity is the network's conjunct (`ImplStep.deliver`; D5). -/
  | dlvRecv (p) (i : Fin P.n) (m : BMsg M) :
      ProcStep P ldr j p (Sum.inr (.dlv j i m)) (PMF.pure (p.deliverTo i m))
  /-- A delivery to another process: not `j`'s business. -/
  | dlvIdle (p) (i k : Fin P.n) (m : BMsg M) (hi : i ≠ j) :
      ProcStep P ldr j p (Sum.inr (.dlv i k m)) (PMF.pure p)
  /-- Return: an `n − f` `VOTE m` receipt quorum on the record's own delivered
  sets, and the record has not returned (`ImplStep.ret`). -/
  | ret (p) (m : M) (hcnt : P.n - P.f ≤ p.recvCount (.vote m)) (hr : p.proc.returned = false) :
      ProcStep P ldr j p (Sum.inl (Sum.inl (.ret j m)))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A return at another process: not `j`'s business. -/
  | retIdle (p) (i : Fin P.n) (m : M) (hi : i ≠ j) :
      ProcStep P ldr j p (Sum.inl (Sum.inl (.ret i m))) (PMF.pure p)
  /-- Corruption is the network's own write, and the local records are
  corruption-blind (D1). -/
  | failIdle (p) (i : Fin P.n) :
      ProcStep P ldr j p (Sum.inl (Sum.inl (.fail i))) (PMF.pure p)

/-! ### The instance's network

The one local state of the instance that holds what no program may see: the
per-sender sent sets and the corrupted set. It participates in every send by
recording the message and in every delivery by checking that the message is
sent, and it is where a corrupted sender's injections enter (D5). -/

/-- The step relation of the instance's network. All transitions are Dirac. -/
inductive NetStep (P : Params) (ldr : Fin P.n) :
    NetworkState P.n (BMsg M) → BLab P.n M → PMF (NetworkState P.n (BMsg M)) → Prop
  /-- The network's half of the call: the leader's `⟨INIT, m⟩` is sent
  (`ImplStep.call`). -/
  | call (w) (m : M) :
      NetStep P ldr w (Sum.inl (Sum.inl (.call m))) (PMF.pure (w.post ldr (.init m)))
  /-- The call loop sends nothing (`ImplStep.callLoop`). -/
  | callLoop (w) (m : M) :
      NetStep P ldr w (Sum.inl (Sum.inr (.callLoop m))) (PMF.pure w)
  /-- The network's half of a multicast: sent the message under its sender.
  Authenticity is the sender's joint participation (D5). -/
  | snd (w) (j : Fin P.n) (m : BMsg M) :
      NetStep P ldr w (Sum.inr (.snd j m)) (PMF.pure (w.post j m))
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (`ImplStep.deliver`; D5). -/
  | dlv (w) (i j : Fin P.n) (m : BMsg M) (h : m ∈ w.sent j) :
      NetStep P ldr w (Sum.inr (.dlv i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (`ImplStep.byz`; D5). -/
  | byz (w) (j : Fin P.n) (m : BMsg M) (h : j ∈ w.F) :
      NetStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure (w.post j m))
  /-- A return sends nothing (`ImplStep.ret`). -/
  | retIdle (w) (i : Fin P.n) (m : M) :
      NetStep P ldr w (Sum.inl (Sum.inl (.ret i m))) (PMF.pure w)
  /-- Corruption (deviation D1). -/
  | fail (w) (i : Fin P.n) :
      NetStep P ldr w (Sum.inl (Sum.inl (.fail i))) (PMF.pure (w.corrupt P i))

/-! ### The instance -/

/-- The program of process `j` in the instance with leader `ldr`. -/
noncomputable def brbProc (P : Params) (ldr j : Fin P.n) :
    System (LocalState P.n (PState M) (BMsg M)) (BLab P.n M) where
  init := LocalState.initial P.n (BMsg M) (PState.initial M)
  step := ProcStep P ldr j

@[simp] theorem brbProc_init (P : Params) (ldr j : Fin P.n) :
    (brbProc P ldr j (M := M)).init = LocalState.initial P.n (BMsg M) (PState.initial M) := rfl

@[simp] theorem brbProc_step (P : Params) (ldr j : Fin P.n)
    (p : LocalState P.n (PState M) (BMsg M)) (l : BLab P.n M)
    (ν : PMF (LocalState P.n (PState M) (BMsg M))) :
    (brbProc P ldr j).step p l ν ↔ ProcStep P ldr j p l ν := Iff.rfl

/-- The instance's network. -/
noncomputable def brbNet (P : Params) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (NetworkState P.n (BMsg M)) (BLab P.n M) where
  init := NetworkState.initial P.n (BMsg M)
  step := NetStep P ldr

@[simp] theorem brbNet_init (P : Params) (ldr : Fin P.n) :
    (brbNet P ldr M).init = NetworkState.initial P.n (BMsg M) := rfl

@[simp] theorem brbNet_step (P : Params) (ldr : Fin P.n) (w : NetworkState P.n (BMsg M))
    (l : BLab P.n M) (μ : PMF (NetworkState P.n (BMsg M))) :
    (brbNet P ldr M).step w l μ ↔ NetStep P ldr w l μ := Iff.rfl

/-- The programs beside the network, over the instance-internal alphabet. -/
noncomputable def subPre (P : Params) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (ImplState P.n M) (BLab P.n M) :=
  (System.syncProduct (brbProc P ldr (M := M))).parallel (brbNet P ldr M)

/-- **The reliable-broadcast instance**: the programs beside the network, the
two rendezvous hidden, the result read back over the interface alphabet. -/
noncomputable def sub (P : Params) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (ImplState P.n M) (SubLab P.n M) :=
  ((subPre P ldr M).abstract (bEvents P.n M)).relabel

@[simp] theorem sub_init (P : Params) (ldr : Fin P.n) :
    (sub P ldr M).init = ImplState.initial P.n M := rfl

/-! ### The specification read over the instance's interface

The specification speaks `Lab n M`; the instance speaks `SubLab n M`, in which
the call loop is a label of its own. `specPull` is the projection that
identifies the loop with the specification label it stands for, so that the
specification's own loop row answers it. -/

/-- The projection of the interface alphabet onto the specification's
alphabet. -/
def specPull (n : ℕ) (M : Type) : SubLab n M → Option (Lab n M)
  | Sum.inl l => some l
  | Sum.inr (.callLoop m) => some (.call m)

@[simp] theorem specPull_inl {n : ℕ} {M : Type} (l : Lab n M) :
    specPull n M (Sum.inl l) = some l := rfl

@[simp] theorem specPull_callLoop {n : ℕ} {M : Type} (m : M) :
    specPull n M (Sum.inr (.callLoop m)) = some (.call m) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specPull_tau (n : ℕ) (M : Type) :
    specPull n M (Silent.τ : SubLab n M) = some (Silent.τ : Lab n M) := rfl

/-- Only the silent label projects to the silent label: the call loop projects
to the call. -/
theorem specPull_eq_tau {n : ℕ} {M : Type} {l : SubLab n M} (h : specPull n M l = some Lab.tau) :
    l = Sum.inl Lab.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e; simp at h

/-- Every interface label carries a specification label. -/
theorem specPull_isSome {n : ℕ} {M : Type} (l : SubLab n M) : ∃ l₀, specPull n M l = some l₀ := by
  cases l with
  | inl l₀ => exact ⟨l₀, rfl⟩
  | inr e => cases e; exact ⟨_, rfl⟩

/-- **The lifted specification**: the specification instance with leader `ldr`,
read over the instance's interface. -/
noncomputable def liftedSpec (P : Params) (ldr : Fin P.n) (M : Type) :
    System (SpecState P.n M) (SubLab P.n M) :=
  (specInst P ldr M).mapIdle (specPull P.n M)

@[simp] theorem liftedSpec_init {M : Type} (P : Params) (ldr : Fin P.n) :
    (liftedSpec P ldr M).init = SpecState.initial P.n M := rfl

/-! ### Determinacy

Both rule tables written here are Dirac, so the instance is an LTS. -/

/-- Every program transition is Dirac. -/
theorem procStep_dirac {P : Params} {ldr j : Fin P.n} {p : LocalState P.n (PState M) (BMsg M)}
    {l : BLab P.n M} {ν : PMF (LocalState P.n (PState M) (BMsg M))}
    (h : ProcStep P ldr j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem netStep_dirac {P : Params} {ldr : Fin P.n} {w : NetworkState P.n (BMsg M)}
    {l : BLab P.n M} {μ : PMF (NetworkState P.n (BMsg M))} (h : NetStep P ldr w l μ) :
    ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem brbProc_isLTS (P : Params) (ldr j : Fin P.n) : (brbProc P ldr j (M := M)).IsLTS :=
  fun _ _ _ h => procStep_dirac h

/-- The network is an LTS. -/
theorem brbNet_isLTS (P : Params) (ldr : Fin P.n) : (brbNet P ldr M).IsLTS :=
  fun _ _ _ h => netStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem syncB_isLTS (P : Params) (ldr : Fin P.n) :
    (System.syncProduct (brbProc P ldr (M := M))).IsLTS :=
  System.syncProduct_isLTS (brbProc_isLTS P ldr)

/-- The programs beside the network form an LTS. -/
theorem subPre_isLTS (P : Params) (ldr : Fin P.n) : (subPre P ldr M).IsLTS :=
  System.parallel_isLTS (syncB_isLTS P ldr) (brbNet_isLTS P ldr)

/-- The instance is an LTS. -/
theorem sub_isLTS (P : Params) (ldr : Fin P.n) : (sub P ldr M).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (subPre_isLTS P ldr) _)

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem liftedSpec_isLTS {M : Type} (P : Params) (ldr : Fin P.n) : (liftedSpec P ldr M).IsLTS :=
  System.mapIdle_isLTS _ (specInst_isLTS P ldr)

/-- No program rule fires on `τ`: a program only ever moves in a rendezvous or
on one of the instance's interface labels. The instance's silent transitions
are therefore exactly the network's injections and the hidden rendezvous. -/
theorem procStep_no_tau {P : Params} {ldr j : Fin P.n} {p : LocalState P.n (PState M) (BMsg M)}
    {ν : PMF (LocalState P.n (PState M) (BMsg M))}
    (h : ProcStep P ldr j p (Silent.τ : BLab P.n M) ν) : False := by
  rw [blab_tau] at h; cases h

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `specPull`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the
instance actually took — this is what turns a specification `call` run into the
answer to the call loop. -/

/-- The left injection: the interface label a specification label sits at. -/
def sect {n : ℕ} {M : Type} : Lab n M → SubLab n M := Sum.inl

open scoped Classical in
/-- The section of `specPull` that answers the interface label `l` over the
specification label `l₀`. -/
noncomputable def sectAt {n : ℕ} {M : Type} (l₀ : Lab n M) (l : SubLab n M) :
    Lab n M → SubLab n M :=
  fun x => if x = l₀ then l else sect x

@[simp] theorem specPull_sect {n : ℕ} {M : Type} (x : Lab n M) :
    specPull n M (sect x) = some x := rfl

/-- The left injection reflects the silent label. -/
theorem sect_eq_tau {n : ℕ} {M : Type} (x : Lab n M) :
    (sect x : SubLab n M) = (Silent.τ : SubLab n M) ↔ x = (Silent.τ : Lab n M) :=
  inl_eq_tau_iff x

theorem specPull_sectAt {n : ℕ} {M : Type} {l₀ : Lab n M} {l : SubLab n M}
    (hl : specPull n M l = some l₀) (x : Lab n M) : specPull n M (sectAt l₀ l x) = some x := by
  unfold sectAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specPull_sect]

theorem sectAt_tau {n : ℕ} {M : Type} {l₀ : Lab n M} {l : SubLab n M}
    (hl : specPull n M l = some l₀)
    (hl₀ : l₀ ≠ (Silent.τ : Lab n M)) (x : Lab n M) :
    sectAt l₀ l x = (Silent.τ : SubLab n M) ↔ x = (Silent.τ : Lab n M) := by
  unfold sectAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Lab n M) := by rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    exact sect_eq_tau x

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_liftedSpec {M : Type} (P : Params) (ldr : Fin P.n) {s s' : SpecState P.n M}
    (h : (specInst P ldr M).weakLSilent s s') : (liftedSpec P ldr M).weakLSilent s s' :=
  System.weakLSilent_mapIdle sect (fun _ => rfl) (fun x => sect_eq_tau x) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_liftedSpec {M : Type} (P : Params) (ldr : Fin P.n) {s s' : SpecState P.n M}
    {l₀ : Lab P.n M} {l : SubLab P.n M} (hl₀ : l₀ ≠ (Silent.τ : Lab P.n M))
    (hl : specPull P.n M l = some l₀)
    (h : (specInst P ldr M).weakLStep s l₀ s') : (liftedSpec P ldr M).weakLStep s l s' :=
  System.weakLStep_mapIdle (sectAt l₀ l) (specPull_sectAt hl) (sectAt_tau hl hl₀)
    (by simp [sectAt]) h

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ syncProduct`; the lemmas below
unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem syncB_inv {P : Params} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)} {l : BLab P.n M}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M))}
    (h : (System.syncProduct (brbProc P ldr (M := M))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M),
      μ = PMF.pure x ∧ ∀ i, ProcStep P ldr i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => procStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep procStep_no_tau

/-- Build a synchronised transition of the program group from per-process Dirac
steps. -/
theorem syncB_pure {P : Params} {ldr : Fin P.n}
    {u x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)} {l : BLab P.n M}
    (hl : l ≠ Silent.τ) (h : ∀ i, ProcStep P ldr i (u i) l (PMF.pure (x i))) :
    (System.syncProduct (brbProc P ldr (M := M))).step u l (PMF.pure x) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program has a `τ` row. -/
theorem syncB_no_tau {P : Params} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M))}
    (h : (System.syncProduct (brbProc P ldr (M := M))).step u (Silent.τ : BLab P.n M) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact procStep_no_tau hstep

/-- The instance's step relation, unfolded to the hidden-rendezvous case and
the interface-label case. -/
theorem sub_step_iff (P : Params) (ldr : Fin P.n) (q : ImplState P.n M) (l : SubLab P.n M)
    (μ : PMF (ImplState P.n M)) :
    (sub P ldr M).step q l μ ↔
      (l = Sum.inl Lab.tau ∧ ∃ e : BEvt P.n M, (subPre P ldr M).step q (Sum.inr e) μ) ∨
      (subPre P ldr M).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_bEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_bEvents l, hstep⟩

/-- Build a joint transition of the programs and the network on a rendezvous
label. -/
theorem subPre_event_step (P : Params) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {w w' : NetworkState P.n (BMsg M)} (e : BEvt P.n M)
    (hall : ∀ i, ProcStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (subPre P ldr M).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [subPre, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', syncB_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the programs and the network on a visible
interface label. -/
theorem subPre_lab_step (P : Params) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {w w' : NetworkState P.n (BMsg M)} {l : SubLab P.n M} (hl : l ≠ Sum.inl Lab.tau)
    (hall : ∀ i, ProcStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (subPre P ldr M).step (u, w) (Sum.inl l) (PMF.pure (x, w')) := by
  have hne : (Sum.inl l : BLab P.n M) ≠ Silent.τ := by
    rw [blab_tau]; simpa using hl
  rw [subPre, System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure x, PMF.pure w', syncB_pure hne hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the network from a
network-local one. -/
theorem subPre_tau_net (P : Params) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {w w' : NetworkState P.n (BMsg M)}
    (hn : NetStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (subPre P ldr M).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [subPre, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden rendezvous is a silent transition of the instance. -/
theorem sub_event_step (P : Params) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {w w' : NetworkState P.n (BMsg M)} (e : BEvt P.n M)
    (hall : ∀ i, ProcStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (sub P ldr M).step (u, w) (Sum.inl Lab.tau) (PMF.pure (x, w')) :=
  (sub_step_iff P ldr _ _ _).mpr (Or.inl ⟨rfl, e, subPre_event_step P ldr e hall hn⟩)

/-- A visible interface label is a transition of the instance. -/
theorem sub_lab_step (P : Params) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {w w' : NetworkState P.n (BMsg M)} {l : SubLab P.n M} (hl : l ≠ Sum.inl Lab.tau)
    (hall : ∀ i, ProcStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (sub P ldr M).step (u, w) l (PMF.pure (x, w')) :=
  (sub_step_iff P ldr _ _ _).mpr (Or.inr (subPre_lab_step P ldr hl hall hn))

/-- A network-local injection is a silent transition of the instance. -/
theorem sub_tau_net (P : Params) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
    {w w' : NetworkState P.n (BMsg M)}
    (hn : NetStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (sub P ldr M).step (u, w) (Sum.inl Lab.tau) (PMF.pure (u, w')) :=
  (sub_step_iff P ldr _ _ _).mpr (Or.inr (subPre_tau_net P ldr hn))

/-- A visible transition of the programs beside the network: every program and
the network step on the label, and the joint distribution is their Dirac
product. -/
theorem subPre_joint_inv {P : Params} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)} {w : NetworkState P.n (BMsg M)}
    {L : BLab P.n M} {μ : PMF (ImplState P.n M)} (hL : L ≠ (Silent.τ : BLab P.n M))
    (h : (subPre P ldr M).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)) (w' : NetworkState P.n (BMsg M)),
      μ = PMF.pure (x, w') ∧ (∀ i, ProcStep P ldr i (u i) L (PMF.pure (x i))) ∧
        NetStep P ldr w L (PMF.pure w') := by
  rw [subPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := syncB_inv hs
    obtain ⟨w', rfl⟩ := netStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the network is a network-local
injection: no program has a `τ` row. -/
theorem subPre_tau_inv {P : Params} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)} {w : NetworkState P.n (BMsg M)}
    {μ : PMF (ImplState P.n M)}
    (h : (subPre P ldr M).step (u, w) (Sum.inl (Sum.inl Lab.tau)) μ) :
    ∃ w' : NetworkState P.n (BMsg M), μ = PMF.pure (u, w') ∧
      NetStep P ldr w (Sum.inl (Sum.inl Lab.tau)) (PMF.pure w') := by
  rw [subPre, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, rfl⟩ | ⟨-, μ₂, hn, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hs syncB_no_tau
  · obtain ⟨w', rfl⟩ := netStep_dirac hn
    exact ⟨w', prodPMF_pure_pure _ _, hn⟩

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The record and the distribution are variables,
so `cases` unifies against any local state. -/

section ProcInversion

variable {P : Params} {ldr j : Fin P.n} {p : LocalState P.n (PState M) (BMsg M)}
  {ν : PMF (LocalState P.n (PState M) (BMsg M))}

theorem stepB_call_leader {m : M}
    (h : ProcStep P ldr ldr p (Sum.inl (Sum.inl (.call m))) ν) :
    p.proc.input = none ∧ ν = PMF.pure (p.setP { p.proc with input := some m }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ ldr›

theorem stepB_call_foreign {m : M} (hj : j ≠ ldr)
    (h : ProcStep P ldr j p (Sum.inl (Sum.inl (.call m))) ν) : ν = PMF.pure p := by
  cases h
  case call => exact absurd ‹j = ldr› hj
  case callIdle => rfl

theorem stepB_callLoop {m : M}
    (h : ProcStep P ldr j p (Sum.inl (Sum.inr (.callLoop m))) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl

theorem stepB_ret_own {m : M}
    (h : ProcStep P ldr j p (Sum.inl (Sum.inl (.ret j m))) ν) :
    P.n - P.f ≤ p.recvCount (.vote m) ∧ p.proc.returned = false ∧
      ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem stepB_ret_foreign {i : Fin P.n} {m : M} (hi : i ≠ j)
    (h : ProcStep P ldr j p (Sum.inl (Sum.inl (.ret i m))) ν) : ν = PMF.pure p := by
  cases h
  case ret => exact absurd rfl hi
  case retIdle => rfl

theorem stepB_fail {i : Fin P.n}
    (h : ProcStep P ldr j p (Sum.inl (Sum.inl (.fail i))) ν) : ν = PMF.pure p := by
  cases h
  case failIdle => rfl

theorem stepB_snd_init_own {m : M}
    (h : ProcStep P ldr j p (Sum.inr (.snd j (.init m))) ν) : False := by
  cases h
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepB_snd_echo_own {m : M}
    (h : ProcStep P ldr j p (Sum.inr (.snd j (.echo m))) ν) :
    BMsg.init m ∈ p.recv ldr ∧ p.proc.sentEcho = none ∧
      ν = PMF.pure (p.setP { p.proc with sentEcho := some m }) := by
  cases h
  case sndEcho => exact ⟨by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepB_snd_vote_own {m : M}
    (h : ProcStep P ldr j p (Sum.inr (.snd j (.vote m))) ν) :
    (P.n - P.f ≤ p.recvCount (.echo m) ∨ P.f + 1 ≤ p.recvCount (.vote m)) ∧
      p.proc.sentVote = none ∧
      ν = PMF.pure (p.setP { p.proc with sentVote := some m }) := by
  cases h
  case sndVoteQuorum => exact ⟨Or.inl (by assumption), by assumption, rfl⟩
  case sndVoteAmp => exact ⟨Or.inr (by assumption), by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepB_snd_foreign {i : Fin P.n} {m : BMsg M} (hi : i ≠ j)
    (h : ProcStep P ldr j p (Sum.inr (.snd i m)) ν) : ν = PMF.pure p := by
  cases h
  case sndIdle => rfl
  all_goals exact absurd rfl hi

theorem stepB_dlv_own {k : Fin P.n} {m : BMsg M}
    (h : ProcStep P ldr j p (Sum.inr (.dlv j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case dlvRecv => rfl
  case dlvIdle => exact absurd rfl ‹_ ≠ j›

theorem stepB_dlv_foreign {i k : Fin P.n} {m : BMsg M} (hi : i ≠ j)
    (h : ProcStep P ldr j p (Sum.inr (.dlv i k m)) ν) : ν = PMF.pure p := by
  cases h
  case dlvRecv => exact absurd rfl hi
  case dlvIdle => rfl

end ProcInversion

/-! ### The network's rules, by label class -/

section NetInversion

variable {P : Params} {ldr : Fin P.n} {w : NetworkState P.n (BMsg M)}
  {μ : PMF (NetworkState P.n (BMsg M))}

theorem netStep_call {m : M} (h : NetStep P ldr w (Sum.inl (Sum.inl (.call m))) μ) :
    μ = PMF.pure (w.post ldr (.init m)) := by
  cases h; rfl

theorem netStep_callLoop {m : M} (h : NetStep P ldr w (Sum.inl (Sum.inr (.callLoop m))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

theorem netStep_ret {i : Fin P.n} {m : M}
    (h : NetStep P ldr w (Sum.inl (Sum.inl (.ret i m))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem netStep_fail {i : Fin P.n} (h : NetStep P ldr w (Sum.inl (Sum.inl (.fail i))) μ) :
    μ = PMF.pure (w.corrupt P i) := by
  cases h; rfl

theorem netStep_snd {j : Fin P.n} {m : BMsg M}
    (h : NetStep P ldr w (Sum.inr (.snd j m)) μ) : μ = PMF.pure (w.post j m) := by
  cases h; rfl

theorem netStep_dlv {i j : Fin P.n} {m : BMsg M}
    (h : NetStep P ldr w (Sum.inr (.dlv i j m)) μ) : m ∈ w.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_tau (h : NetStep P ldr w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : BMsg M), j ∈ w.F ∧ μ = PMF.pure (w.post j m) := by
  cases h
  case byz j m hF => exact ⟨j, m, hF, rfl⟩

end NetInversion

/-! ### One state, two presentations

The local states and the network state are the two components of `ImplState`
(`ABA/Broadcast/Impl.lean`), so the instance and the rule table `ImplStep` run
on the same state and every rule of the one is a rule of the other read in the
instance state's accessors. What the joint steps deliver, though, is a program
function pinned pointwise — its value at the acting process, and its agreement
with the old one elsewhere — where `ImplStep` writes with `SubState.setProc`.
The lemmas here close that gap. -/

section Frame

variable {P : Params} {u x : ∀ _ : Fin P.n, LocalState P.n (PState M) (BMsg M)}
  {w : NetworkState P.n (BMsg M)}

omit [DecidableEq M] in
/-- A program function pinned at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem procFun_update {j : Fin P.n} {q : LocalState P.n (PState M) (BMsg M)}
    (hj : x j = q) (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j q := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

omit [DecidableEq M] in
/-- A record write at one program, with the network state untouched. -/
theorem sub_setProc {j : Fin P.n} {pr : PState M}
    (hj : x j = (u j).setP pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : ImplState P.n M) = SubState.setProc (u, w) j pr := by
  rw [procFun_update hj hne]
  rfl

/-- A record write at one program together with the network state recording the
message that write multicasts. -/
theorem sub_setProc_post {j : Fin P.n} {pr : PState M} {m : BMsg M}
    (hj : x j = (u j).setP pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.post j m) : ImplState P.n M) = (SubState.setProc (u, w) j pr).mcast j m := by
  rw [procFun_update hj hne]
  rfl

omit [DecidableEq M] in
/-- The programs stand still. -/
theorem sub_idle (hall : ∀ i, x i = u i) : ((x, w) : ImplState P.n M) = (u, w) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem sub_deliver {i k : Fin P.n} {m : BMsg M}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : ImplState P.n M) = SubState.recvMsg (u, w) i k m := by
  rw [procFun_update hi hne]
  rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem sub_post {k : Fin P.n} {m : BMsg M} :
    ((u, w.post k m) : ImplState P.n M) = SubState.mcast (u, w) k m := rfl

omit [DecidableEq M] in
/-- Corruption is the network state's own write (D1). -/
theorem sub_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : ImplState P.n M) = SubState.corrupt P k (u, w) := rfl

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem procStep_update {ldr j : Fin P.n} {q : LocalState P.n (PState M) (BMsg M)}
    {l : BLab P.n M} (hj : ProcStep P ldr j (u j) l (PMF.pure q))
    (hne : ∀ i, i ≠ j → ProcStep P ldr i (u i) l (PMF.pure (u i))) :
    ∀ i, ProcStep P ldr i (u i) l (PMF.pure (Function.update u j q i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

end Frame

/-! ### The rows of the instance

Every transition of the instance is one row of `ImplStep` at the same state,
and the correspondence is strong — one step answers one step, at the
specification label the interface label projects to, with no stuttering
anywhere:

| instance | row |
| --- | --- |
| `call` (leader writes, network records) | `ImplStep.call` |
| `callLoop` | `ImplStep.callLoop` |
| hidden `snd` rendezvous, by level | `ImplStep.echo` / `voteQuorum` / `voteAmp` |
| hidden `dlv` rendezvous | `ImplStep.deliver` |
| network-local injection | `ImplStep.byz` |
| `ret` | `ImplStep.ret` |
| `fail` | `ImplStep.fail` |

The two hidden rendezvous and the network's injection are silent on both sides,
and `specPull` takes `τ` to `τ`. -/

/-- **The projection.** -/
theorem sub_step_row (P : Params) (ldr : Fin P.n) :
    ∀ (s : ImplState P.n M) (l : SubLab P.n M) (μ : PMF (ImplState P.n M)),
      (sub P ldr M).step s l μ →
      ∃ l₀, specPull P.n M l = some l₀ ∧ ImplStep P ldr s l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (sub_step_iff P ldr (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden rendezvous: an internal row
    obtain ⟨x, w', rfl, hall, hn⟩ := subPre_joint_inv (by simp) hev
    refine ⟨Lab.tau, rfl, ?_⟩
    cases e with
    | snd j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepB_snd_foreign (Ne.symm hi) (hall i))
      have hw : w' = w.post j m := PMF.pure_injective (netStep_snd hn)
      subst hw
      cases m with
      | init m => exact (stepB_snd_init_own (hall j)).elim
      | echo m =>
        obtain ⟨hrecv, hsend, hx⟩ := stepB_snd_echo_own (hall j)
        rw [sub_setProc_post (PMF.pure_injective hx) hfor]
        exact ImplStep.echo _ j m hrecv hsend
      | vote m =>
        obtain ⟨hcnt, hsend, hx⟩ := stepB_snd_vote_own (hall j)
        rw [sub_setProc_post (PMF.pure_injective hx) hfor]
        rcases hcnt with hq | ha
        · exact ImplStep.voteQuorum _ j m hq hsend
        · exact ImplStep.voteAmp _ j m ha hsend
    | dlv i j m =>
      obtain ⟨hmem, hw⟩ := netStep_dlv hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (stepB_dlv_foreign (Ne.symm hi') (hall i'))
      rw [sub_deliver (PMF.pure_injective (stepB_dlv_own (hall i))) hfor]
      exact ImplStep.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Lab.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := subPre_tau_inv hlab
      obtain ⟨j, m, hF, hw⟩ := netStep_tau hn
      have hw' : w' = w.post j m := PMF.pure_injective hw
      subst hw'
      refine ⟨Lab.tau, rfl, ?_⟩
      rw [sub_post]
      exact ImplStep.byz _ j m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ := subPre_joint_inv (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call m =>
          have hw : w' = w.post ldr (.init m) := PMF.pure_injective (netStep_call hn)
          subst hw
          obtain ⟨hin, hx⟩ := stepB_call_leader (hall ldr)
          have hfor : ∀ i, i ≠ ldr → x i = u i :=
            fun i hi => PMF.pure_injective (stepB_call_foreign hi (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_setProc_post (PMF.pure_injective hx) hfor]
          exact ImplStep.call _ m hin
        | ret id m =>
          have hw : w' = w := PMF.pure_injective (netStep_ret hn)
          subst hw
          obtain ⟨hcnt, hr, hx⟩ := stepB_ret_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (stepB_ret_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_setProc (PMF.pure_injective hx) hfor]
          exact ImplStep.ret _ id m hcnt hr
        | fail id =>
          have hw : w' = w.corrupt P id := PMF.pure_injective (netStep_fail hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (stepB_fail (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_idle hidle, sub_corrupt]
          exact ImplStep.fail _ id
      | inr e =>
        cases e with
        | callLoop m =>
          have hw : w' = w := PMF.pure_injective (netStep_callLoop hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (stepB_callLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_idle hidle]
          exact ImplStep.callLoop _ m

/-- **The embedding.** -/
theorem row_sub_step (P : Params) (ldr : Fin P.n) :
    ∀ (s : ImplState P.n M) (l₀ : Lab P.n M) (μ : PMF (ImplState P.n M)),
      ImplStep P ldr s l₀ μ →
      ∃ l, specPull P.n M l = some l₀ ∧ (sub P ldr M).step s l μ := by
  rintro ⟨u, w⟩ l₀ μ hrow
  cases hrow with
  | call m h =>
    exact ⟨Sum.inl (.call m), rfl, sub_lab_step P ldr (by simp)
      (procStep_update (ProcStep.call (u ldr) m rfl h)
        (fun i hi => ProcStep.callIdle (u i) m hi))
      (NetStep.call w m)⟩
  | callLoop m =>
    exact ⟨Sum.inr (.callLoop m), rfl, sub_lab_step P ldr (by simp)
      (fun i => ProcStep.callLoop (u i) m) (NetStep.callLoop w m)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Lab.tau, rfl, sub_event_step P ldr (BEvt.dlv i j m)
      (procStep_update (ProcStep.dlvRecv (u i) j m)
        (fun i' hi' => ProcStep.dlvIdle (u i') i j m (Ne.symm hi')))
      (NetStep.dlv w i j m h)⟩
  | echo j m hrecv hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, sub_event_step P ldr (BEvt.snd j (.echo m))
      (procStep_update (ProcStep.sndEcho (u j) m hrecv hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.echo m) (Ne.symm hi)))
      (NetStep.snd w j (.echo m))⟩
  | voteQuorum j m hcnt hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, sub_event_step P ldr (BEvt.snd j (.vote m))
      (procStep_update (ProcStep.sndVoteQuorum (u j) m hcnt hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetStep.snd w j (.vote m))⟩
  | voteAmp j m hcnt hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, sub_event_step P ldr (BEvt.snd j (.vote m))
      (procStep_update (ProcStep.sndVoteAmp (u j) m hcnt hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetStep.snd w j (.vote m))⟩
  | byz j m h =>
    exact ⟨Sum.inl Lab.tau, rfl, sub_tau_net P ldr (NetStep.byz w j m h)⟩
  | ret id m hcnt hr =>
    exact ⟨Sum.inl (.ret id m), rfl, sub_lab_step P ldr (by simp)
      (procStep_update (ProcStep.ret (u id) m hcnt hr)
        (fun i hi => ProcStep.retIdle (u i) id m (Ne.symm hi)))
      (NetStep.retIdle w id m)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, sub_lab_step P ldr (by simp)
      (fun i => ProcStep.failIdle (u i) id) (NetStep.fail w id)⟩

/-- **The row characterisation.** At a specification label `l₀`, the
transitions of the instance over the labels `specPull` sends to `l₀` are
exactly the `l₀`-rows of `ImplStep`, on the same state and with the same
distribution. The call and the call loop are the two rows of `call m`, taken at
the two labels `specPull` sends to it; every other specification label has a
single interface label over it. -/
theorem sub_step_iff_row (P : Params) (ldr : Fin P.n) (s : ImplState P.n M)
    (l₀ : Lab P.n M) (μ : PMF (ImplState P.n M)) :
    (∃ l, specPull P.n M l = some l₀ ∧ (sub P ldr M).step s l μ) ↔ ImplStep P ldr s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := sub_step_row P ldr s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Lab P.n M)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_sub_step P ldr s l₀ μ

/-- info: 'PLTS.ABA.BRB.sub_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_step_iff_row

end BRB
end ABA
end PLTS
