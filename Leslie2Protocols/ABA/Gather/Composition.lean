/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.BrachaComposition
import Leslie2Protocols.ABA.Gather.MessagesAndCommonCore
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The gather instance, composed

One gather instance over an arbitrary payload type `X`, taken apart into the
pieces that run it. The gather tier is `n` per-process programs beside the
gather network. The broadcast tier is `2n` reliable-broadcast instances, one
per process for the inputs and one per process for the `BIND` payloads, each
lifted along a pullback that names it. The two tiers run in parallel, the
instance's own events are hidden, and the result is read back over the gather
alphabet extended by the call loop.

A gather program holds one process's local record and the messages delivered to
it, indexed by sender (`ABA.LocalState`). Its guards read its own record and
its own delivered sets. The gather network holds the per-sender sent sets, the
corrupted set (`ABA.NetworkState`) and the instance's core; it reads no
program's record.

The composition is generic in the broadcast tier: `instanceOverBroadcasts` takes the `2n`
instances as arguments, `instanceOverBracha` supplies Bracha instances (`BRB.brachaInstance`) and
`instanceOverBroadcastSpecification` supplies lifted broadcast specifications
(`BRB.specificationOverInstanceAlphabet`).

## The alphabet

The specification's `call id x` carries two rows, the call and the
input-enabledness loop. The composition splits them across two labels, as the
reliable-broadcast composition does one level down (`ABA/ReliableBroadcast/BrachaComposition.lean`).
The gather record and the broadcast instance are different components, so a
single label carrying both rows would also carry the mixed pairs. The loop
therefore has a label of its own, `LoopLabel.callLoop id x`, and the specification
is read along `specificationLabelMap`, which sends that label to `call id x`. The interface
alphabet is `InstanceLabel n X = Label n X ⊕ LoopLabel n X`.

The instance-internal alphabet is `GatherLabel n X = InstanceLabel n X ⊕ GatherEvent n X`. Its
five events are the gather multicast and delivery, the return of an input
instance, the call of a bind instance and the return of a bind instance. They
are hidden before anything outside sees the instance: `instanceOverBroadcasts` speaks
`InstanceLabel n X`.

A broadcast instance joins the composition along a pullback — `inputBroadcastLabelMap k` for
the instance broadcasting `k`'s input, `bindBroadcastLabelMap q` for the instance
broadcasting `q`'s `BIND` payload. The pullback names the instance: a label
carrying another instance's index has no image, and that instance stands still.
Corruption and the silent label have an image at every instance, so `fail` is a
broadcast across the whole composition.

## What the broadcast instances returned

A gather program reads no neighbouring coordinate. What a broadcast instance has returned to it is
written on the return event into its own record: `inputBroadcastReturned k` is the value instance
`k` returned here, `bindBroadcastReturned q` is the payload bind instance `q` returned here. The
four rows that read what has been returned — `sendEcho`, `sendVote`, `bindCall` and `ret` — read the
returned values through `ProcessRecord.accepted`, `holdsInputBroadcastReturn`,
`holdsBindBroadcastReturn` and `approvedBy`.

## The core

The core is a function of the gather network state alone
(`coreOf_networkState_only`), so the gather network holds it. `coreOfNetwork` reads
it off the network state, `coreOf_eq_coreOfNetwork` identifies the two systems, and
the network's `ret` row writes the core and carries it on the label.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type}

/-! ### The interface alphabet and the instance-internal alphabet -/

/-- The interface label of the call loop. The specification's `call id x`
carries the call and the input-enabledness loop; the composition takes the loop
on a label of its own. -/
inductive LoopLabel (n : ℕ) (X : Type) : Type
  /-- The input-enabledness loop of `call id x`. -/
  | callLoop (id : Fin n) (x : X)

/-- The instance's interface alphabet: the specification's alphabet with the
call loop beside it. -/
abbrev InstanceLabel (n : ℕ) (X : Type) : Type := Label n X ⊕ LoopLabel n X

/-- The instance's own events: the gather multicast and delivery, the return of
an input instance, and the call and return of a bind instance. -/
inductive GatherEvent (n : ℕ) (X : Type) : Type
  /-- Process `j` hands `m` to the gather network. -/
  | send (j : Fin n) (m : Message n X)
  /-- The gather network delivers `j`'s `m` to `i`. -/
  | deliver (i j : Fin n) (m : Message n X)
  /-- The instance broadcasting `k`'s input returns `v` to `j`. -/
  | inputBroadcastRet (k j : Fin n) (v : X)
  /-- Process `j` calls the instance broadcasting its `BIND` payload `U`. -/
  | bindCall (j : Fin n) (U : AcceptedPairs n X)
  /-- The instance broadcasting `q`'s `BIND` payload returns `U` to `j`. -/
  | bindRet (q j : Fin n) (U : AcceptedPairs n X)

/-- The instance-internal alphabet: the interface alphabet plus the five
events. Its silent label is `Sum.inl (Sum.inl tau)`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev GatherLabel (n : ℕ) (X : Type) : Type := InstanceLabel n X ⊕ GatherEvent n X

/-- The event labels, hidden by the instance. -/
def gatherEvents (n : ℕ) (X : Type) : Set (GatherLabel n X) := {l | ∃ e : GatherEvent n X,
  l = Sum.inr e}

@[simp] theorem inl_notMem_gatherEvents {n : ℕ} {X : Type} (l : InstanceLabel n X) :
    Sum.inl l ∉ gatherEvents n X := by
  simp [gatherEvents]

@[simp] theorem inr_mem_gatherEvents {n : ℕ} {X : Type} (e : GatherEvent n X) :
    Sum.inr e ∈ gatherEvents n X := ⟨e, rfl⟩

@[simp] theorem gatherLabel_tau (n : ℕ) (X : Type) :
    (Silent.τ : GatherLabel n X) = Sum.inl (Sum.inl Label.tau) := rfl

@[simp] theorem instanceLabel_tau (n : ℕ) (X : Type) :
    (Silent.τ : InstanceLabel n X) = Sum.inl Label.tau := rfl

/-- The silent label of a broadcast instance's interface alphabet. -/
@[simp] theorem broadcastInstanceLabel_tau (n : ℕ) (M : Type) :
    (Silent.τ : BRB.InstanceLabel n M) = Sum.inl BRB.Label.tau := rfl

/-! ### The records -/

/-- The local record of one gather program: the gather record beside the returned values of what the
broadcast instances have returned here. -/
structure ProcessRecord (n : ℕ) (X : Type) extends BaseProcessRecord n X where
  /-- `inputBroadcastReturned k` — the value the instance broadcasting `k`'s input returned
  here. -/
  inputBroadcastReturned : Fin n → Option X
  /-- `bindBroadcastReturned q` — the payload the instance broadcasting `q`'s `BIND`
  payload returned here. -/
  bindBroadcastReturned : Fin n → Option (AcceptedPairs n X)

/-- The initial local record: nothing called, nothing sent, nothing returned
here. -/
def ProcessRecord.initial (n : ℕ) (X : Type) : ProcessRecord n X :=
  { BaseProcessRecord.initial n X with
    inputBroadcastReturned := fun _ => none,
    bindBroadcastReturned := fun _ => none }

/-- `p` holds the value `v` of the instance broadcasting `k`'s input. -/
def holdsInputBroadcastReturn {n : ℕ} {X : Type} (p : ProcessRecord n X) (k : Fin n) (v : X) : Prop
  :=
  p.inputBroadcastReturned k = some v

/-- `p` holds the payload `U` of the instance broadcasting `q`'s `BIND`
payload. -/
def holdsBindBroadcastReturn {n : ℕ} {X : Type} (p : ProcessRecord n X) (q : Fin n)
    (U : AcceptedPairs n X) : Prop :=
  p.bindBroadcastReturned q = some U

/-- A payload set is approved by `p` when `p` holds every one of its pairs. -/
def approvedBy {n : ℕ} {X : Type} (p : ProcessRecord n X) (A : AcceptedPairs n X) : Prop :=
  A.subMap p.inputBroadcastReturned

/-- The accepted pairs of `p`: the entries of what its input instances returned. AFW25's
Algorithm 5 writes this set `AP_i` and multicasts it as the `ECHO` payload. -/
def ProcessRecord.accepted {n : ℕ} {X : Type} [DecidableEq X] (p : ProcessRecord n X) :
  AcceptedPairs n X :=
  Finset.univ.biUnion fun k =>
    match p.inputBroadcastReturned k with
    | some v => {(k, v)}
    | none => ∅

/-- A pair is accepted exactly when the input instance's returned value holds it. -/
theorem ProcessRecord.mem_accepted {n : ℕ} {X : Type} [DecidableEq X] {p : ProcessRecord n X}
    {k : Fin n} {v : X} : (k, v) ∈ p.accepted ↔ p.inputBroadcastReturned k = some v := by
  constructor
  · intro h
    obtain ⟨k', -, hk'⟩ := Finset.mem_biUnion.mp h
    split at hk'
    · rename_i v' hd
      rw [Finset.mem_singleton, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      exact hd
    · exact absurd hk' (by simp)
  · intro h
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩
    rw [h]
    simp

/-- The accepted pairs are entries of the input instance's returned value. -/
theorem ProcessRecord.accepted_subMap {n : ℕ} {X : Type} [DecidableEq X] (p : ProcessRecord n X) :
    p.accepted.subMap p.inputBroadcastReturned :=
  fun _ ha => ProcessRecord.mem_accepted.mp ha

/-- The state of the gather network: the per-sender sent sets and the corrupted
set beside the instance's core. -/
structure NetworkState (n : ℕ) (X : Type) : Type where
  /-- The gather network state. -/
  network : ABA.NetworkState n (Message n X)
  /-- The instance's core, written at the first return and carried on every
  return label. -/
  core : Option (AcceptedPairs n X)

/-- The initial gather network state: nothing multicast, nobody corrupted, the
core unwritten. -/
def NetworkState.initial (n : ℕ) (X : Type) : NetworkState n X :=
  ⟨ABA.NetworkState.initial n (Message n X), none⟩

/-- The core read off a network state. The local records are not consulted
(`coreOf_networkState_only`), so any record vector gives the same set. -/
noncomputable def coreOfNetwork {X : Type} (P : Parameters)
    (w : ABA.NetworkState P.n (Message P.n X)) : AcceptedPairs P.n X :=
  coreOf P ((fun _ => LocalState.initial P.n (Message P.n X) (BaseProcessRecord.initial P.n X)), w)

/-- The core of an instance state is the core of its network state. -/
theorem coreOf_eq_coreOfNetwork {X : Type} (P : Parameters)
    (w : InstanceState P.n (BaseProcessRecord P.n X) (Message P.n X)) :
    coreOf P w = coreOfNetwork P w.2 :=
  coreOf_networkState_only w _ rfl

/-! ### The pullbacks

A broadcast instance speaks its own interface alphabet `BRB.InstanceLabel`. It joins
the composition along a pullback that names it: a label carrying another
instance's index has no image and leaves that instance idle. -/

/-- The pullback along which the instance broadcasting `k`'s input is read. -/
def inputBroadcastLabelMap (n : ℕ) (X : Type) (k : Fin n) : GatherLabel n X → Option
  (BRB.InstanceLabel n X)
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.call id x)) => if k = id then some (Sum.inl (.call x)) else none
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inl (Sum.inr (.callLoop id x)) => if k = id then some (Sum.inr (.callLoop x)) else none
  | Sum.inr (.inputBroadcastRet k' j v) => if k = k' then some (Sum.inl (.ret j v)) else none
  | _ => none

/-- The pullback along which the instance broadcasting `q`'s `BIND` payload is
read. -/
def bindBroadcastLabelMap (n : ℕ) (X : Type) (q : Fin n) : GatherLabel n X → Option
  (BRB.InstanceLabel n (AcceptedPairs n X))
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inr (.bindCall j U) => if q = j then some (Sum.inl (.call U)) else none
  | Sum.inr (.bindRet q' j U) => if q = q' then some (Sum.inl (.ret j U)) else none
  | _ => none

@[simp] theorem inputBroadcastLabelMap_tau (n : ℕ) (X : Type) (k : Fin n) :
    inputBroadcastLabelMap n X k (Silent.τ : GatherLabel n X) = some (Silent.τ : BRB.InstanceLabel n
      X) := rfl

@[simp] theorem bindBroadcastLabelMap_tau (n : ℕ) (X : Type) (q : Fin n) :
    bindBroadcastLabelMap n X q (Silent.τ : GatherLabel n X) = some (Silent.τ : BRB.InstanceLabel n
      (AcceptedPairs n X)) := rfl

/-- Only the silent label of the composition reaches the silent label of an
input instance. -/
theorem inputBroadcastLabelMap_eq_tau {n : ℕ} {X : Type} {k : Fin n} {l : GatherLabel n X}
    (h : inputBroadcastLabelMap n X k l = some (Silent.τ : BRB.InstanceLabel n X)) : l = Silent.τ :=
      by
  rcases l with (l | e) | e
  · cases l <;> simp_all [inputBroadcastLabelMap]
  · cases e; simp_all [inputBroadcastLabelMap]
  · cases e <;> simp_all [inputBroadcastLabelMap]

/-- Only the silent label of the composition reaches the silent label of a bind
instance. -/
theorem bindBroadcastLabelMap_eq_tau {n : ℕ} {X : Type} {q : Fin n} {l : GatherLabel n X}
    (h : bindBroadcastLabelMap n X q l = some (Silent.τ : BRB.InstanceLabel n (AcceptedPairs n X)))
      : l =
      Silent.τ := by
  rcases l with (l | e) | e
  · cases l <;> simp_all [bindBroadcastLabelMap]
  · cases e; simp_all [bindBroadcastLabelMap]
  · cases e <;> simp_all [bindBroadcastLabelMap]

section Rules

variable [DecidableEq X]

/-! ### The gather program

Process `j`'s program. Every guard reads its own record and its own delivered sets. An event row
carries the program's half of a joint step: on a multicast the record write, on a delivery the write
of the delivered set, on a broadcast instance's return the recording of the returned value. -/

/-- The step relation of the gather program of process `j`. All transitions are
Dirac. -/
inductive ProgramStep (P : Parameters) (j : Fin P.n) :
    LocalState P.n (ProcessRecord P.n X) (Message P.n X) → GatherLabel P.n X →
      PMF (LocalState P.n (ProcessRecord P.n X) (Message P.n X)) → Prop
  /-- The call arrives: record the payload. -/
  | call (p) (x : X) (h : p.process.input = none) :
      ProgramStep P j p (Sum.inl (Sum.inl (.call j x)))
        (PMF.pure (p.setProcess { p.process with input := some x }))
  /-- A call at another process is not `j`'s business. -/
  | callIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inl (Sum.inl (.call i x))) (PMF.pure p)
  /-- The call loop: the record does not move. -/
  | callLoop (p) (x : X) :
      ProgramStep P j p (Sum.inl (Sum.inr (.callLoop j x))) (PMF.pure p)
  /-- A call loop at another process is not `j`'s business. -/
  | callLoopIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inl (Sum.inr (.callLoop i x))) (PMF.pure p)
  /-- `ECHO`: `j` is called and its accepted pairs number at least `n − f`, the
  source blueprint's `|AP| ≥ n − f`. The payload is those pairs, `T_i ← AP_i` of
  AFW25's Algorithm 5, line 9. -/
  | sendEcho (p) (hin : p.process.input ≠ none)
      (hcard : P.n - P.f ≤ p.process.accepted.card)
      (hsend : p.process.sentEcho = none) :
      ProgramStep P j p (Sum.inr (.send j (.echo p.process.accepted)))
        (PMF.pure (p.setProcess { p.process with sentEcho := some p.process.accepted }))
  /-- `VOTE U`: `n − f` senders' approved `ECHO` payloads, each contained in
  `U`, are delivered here, and `j` has multicast its own `ECHO`. The main thread
  of AFW25's Algorithm 5 sends `ECHO` before `VOTE`. -/
  | sendVote (p) (U : AcceptedPairs P.n X) (hin : p.process.input ≠ none)
      (hech : p.process.sentEcho ≠ none)
      (happ : approvedBy p.process U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Message.echo A ∈ p.received q ∧ approvedBy p.process A ∧ A ⊆ U)
      (hsend : p.process.sentVote = none) :
      ProgramStep P j p (Sum.inr (.send j (.vote U)))
        (PMF.pure (p.setProcess { p.process with sentVote := some U }))
  /-- A multicast by another process is not `j`'s business. -/
  | sendIdle (p) (i : Fin P.n) (m : Message P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.send i m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's row. -/
  | deliverReceive (p) (i : Fin P.n) (m : Message P.n X) :
      ProgramStep P j p (Sum.inr (.deliver j i m)) (PMF.pure (p.deliverTo i m))
  /-- A delivery to another process is not `j`'s business. -/
  | deliverIdle (p) (i k : Fin P.n) (m : Message P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.deliver i k m)) (PMF.pure p)
  /-- An input instance returns here: record the returned value. -/
  | inputBroadcastRetReceive (p) (k : Fin P.n) (v : X) :
      ProgramStep P j p (Sum.inr (.inputBroadcastRet k j v))
        (PMF.pure (p.setProcess { p.process with
          inputBroadcastReturned :=
            Function.update p.process.inputBroadcastReturned k (some v) }))
  /-- An input instance's return to another process is not `j`'s business. -/
  | inputBroadcastRetIdle (p) (k i : Fin P.n) (v : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.inputBroadcastRet k i v)) (PMF.pure p)
  /-- `BIND U`: `n − f` senders' approved `VOTE` payloads, each contained in
  `U`, are delivered here, `j` has multicast its own `VOTE`, and `j` has not
  called its own bind broadcast. The main thread of AFW25's Algorithm 5 sends
  `VOTE` before `BIND`, and sends `BIND` once, at line 17. The payload handed
  to the broadcast is written to the record; the bind instance's own guard decides
  whether the call lands. -/
  | bindCall (p) (U : AcceptedPairs P.n X) (hin : p.process.input ≠ none)
      (hvot : p.process.sentVote ≠ none)
      (hsnd : p.process.sentBind = none)
      (happ : approvedBy p.process U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Message.vote W ∈ p.received q ∧ approvedBy p.process W ∧ W ⊆ U) :
      ProgramStep P j p (Sum.inr (.bindCall j U))
        (PMF.pure (p.setProcess { p.process with sentBind := some U }))
  /-- Another process's bind call is not `j`'s business. -/
  | bindCallIdle (p) (i : Fin P.n) (U : AcceptedPairs P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.bindCall i U)) (PMF.pure p)
  /-- A bind instance returns here: record the returned value. -/
  | bindRetReceive (p) (q : Fin P.n) (U : AcceptedPairs P.n X) :
      ProgramStep P j p (Sum.inr (.bindRet q j U))
        (PMF.pure (p.setProcess { p.process with
          bindBroadcastReturned :=
            Function.update p.process.bindBroadcastReturned q (some U) }))
  /-- A bind instance's return to another process is not `j`'s business. -/
  | bindRetIdle (p) (q i : Fin P.n) (U : AcceptedPairs P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.bindRet q i U)) (PMF.pure p)
  /-- Return: the output's entries are held here, `n − f` bind payloads held
  here are sub-maps of it, and `j` has called its own bind broadcast. The `BIND`
  broadcast of AFW25's Algorithm 5, line 17, precedes the wait of line 18. The
  core on the label is the network's. -/
  | ret (p) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X) (hin : p.process.input ≠ none)
      (hbind : p.process.sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn p.process k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBindBroadcastReturn p.process q U ∧ AcceptedPairs.subMap U g)
      (hr : p.process.returned = false) :
      ProgramStep P j p (Sum.inl (Sum.inl (.ret j g C)))
        (PMF.pure (p.setProcess { p.process with returned := true }))
  /-- A return at another process is not `j`'s business. -/
  | retIdle (p) (i : Fin P.n) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inl (Sum.inl (.ret i g C))) (PMF.pure p)
  /-- Corruption is the network's own write, and the local records are
  corruption-blind (D1). -/
  | failIdle (p) (i : Fin P.n) :
      ProgramStep P j p (Sum.inl (Sum.inl (.fail i))) (PMF.pure p)

/-! ### The gather network

The one local state of the gather tier that holds what no program may see: the
per-sender sent sets, the corrupted set and the instance's core. It participates
in every gather multicast and delivery, it is where a corrupted sender's
injections enter (D5), and it writes the core at the first return. -/

/-- The step relation of the gather network. All transitions are Dirac. -/
inductive NetworkStep (P : Parameters) :
    NetworkState P.n X → GatherLabel P.n X → PMF (NetworkState P.n X) → Prop
  /-- A call sends nothing. -/
  | call (w) (id : Fin P.n) (x : X) :
      NetworkStep P w (Sum.inl (Sum.inl (.call id x))) (PMF.pure w)
  /-- A call loop sends nothing. -/
  | callLoop (w) (id : Fin P.n) (x : X) :
      NetworkStep P w (Sum.inl (Sum.inr (.callLoop id x))) (PMF.pure w)
  /-- The network's half of a multicast: record the message under its sender. -/
  | send (w) (j : Fin P.n) (m : Message P.n X) :
      NetworkStep P w (Sum.inr (.send j m)) (PMF.pure { w with network := w.network.recordSent j m
        })
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (D5). -/
  | deliver (w) (i j : Fin P.n) (m : Message P.n X) (h : m ∈ w.network.sent j) :
      NetworkStep P w (Sum.inr (.deliver i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (D5). -/
  | byzantine (w) (j : Fin P.n) (m : Message P.n X) (h : j ∈ w.network.F) :
      NetworkStep P w (Sum.inl (Sum.inl .tau)) (PMF.pure { w with
        network :=
          w.network.recordSent j m })
  /-- An input instance's return sends nothing. -/
  | inputBroadcastRetIdle (w) (k j : Fin P.n) (v : X) :
      NetworkStep P w (Sum.inr (.inputBroadcastRet k j v)) (PMF.pure w)
  /-- A bind call sends nothing. -/
  | bindCallIdle (w) (j : Fin P.n) (U : AcceptedPairs P.n X) :
      NetworkStep P w (Sum.inr (.bindCall j U)) (PMF.pure w)
  /-- A bind instance's return sends nothing. -/
  | bindRetIdle (w) (q j : Fin P.n) (U : AcceptedPairs P.n X) :
      NetworkStep P w (Sum.inr (.bindRet q j U)) (PMF.pure w)
  /-- Return: the label carries the core, which this row writes if it is
  unwritten. -/
  | ret (w) (id : Fin P.n) (g : Fin P.n → Option X) :
      NetworkStep P w (Sum.inl (Sum.inl (.ret id g (w.core.getD (coreOfNetwork P w.network)))))
        (PMF.pure { w with core := some (w.core.getD (coreOfNetwork P w.network)) })
  /-- Corruption (deviation D1). -/
  | fail (w) (i : Fin P.n) :
      NetworkStep P w (Sum.inl (Sum.inl (.fail i))) (PMF.pure { w with
        network :=
          w.network.corrupt P i })

/-! ### The two tiers -/

/-- The gather program of process `j`. -/
noncomputable def gatherProgram (P : Parameters) (j : Fin P.n) :
    System (LocalState P.n (ProcessRecord P.n X) (Message P.n X)) (GatherLabel P.n X) where
  init := LocalState.initial P.n (Message P.n X) (ProcessRecord.initial P.n X)
  step := ProgramStep P j

@[simp] theorem gatherProgram_init (P : Parameters) (j : Fin P.n) :
    (gatherProgram P j (X := X)).init = LocalState.initial P.n (Message P.n X)
      (ProcessRecord.initial P.n X)
      :=
  rfl

@[simp] theorem gatherProgram_step (P : Parameters) (j : Fin P.n)
    (p : LocalState P.n (ProcessRecord P.n X) (Message P.n X)) (l : GatherLabel P.n X)
    (ν : PMF (LocalState P.n (ProcessRecord P.n X) (Message P.n X))) :
    (gatherProgram P j).step p l ν ↔ ProgramStep P j p l ν := Iff.rfl

/-- The gather network. -/
noncomputable def gatherNetwork (P : Parameters) (X : Type) [DecidableEq X] :
    System (NetworkState P.n X) (GatherLabel P.n X) where
  init := NetworkState.initial P.n X
  step := NetworkStep P

@[simp] theorem gatherNetwork_init (P : Parameters) :
    (gatherNetwork P X).init = NetworkState.initial P.n X := rfl

@[simp] theorem gatherNetwork_step (P : Parameters) (w : NetworkState P.n X) (l : GatherLabel P.n X)
    (μ : PMF (NetworkState P.n X)) : (gatherNetwork P X).step w l μ ↔ NetworkStep P w l μ := Iff.rfl

/-- The gather tier: the programs beside the gather network. -/
noncomputable def gatherPrograms (P : Parameters) (X : Type) [DecidableEq X] :
    System
    ((∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X)) × NetworkState P.n X)
    (GatherLabel P.n X) :=
  (System.synchronisedProduct (gatherProgram P (X := X))).parallel (gatherNetwork P X)

/-- The state of the composition whose broadcast instances have state `B` for
the inputs and `B'` for the `BIND` payloads. -/
abbrev StateOverBroadcasts (n : ℕ) (X B B' : Type) : Type :=
  ((∀ _ : Fin n, LocalState n (ProcessRecord n X) (Message n X)) × NetworkState n X) ×
    ((∀ _ : Fin n, B) × (∀ _ : Fin n, B'))

/-- The gather tier beside the broadcast tier, over the instance-internal
alphabet. -/
noncomputable def instanceOverBroadcastsExtended (P : Parameters) (X : Type) [DecidableEq X]
    {B B' : Type} (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))) :
    System (StateOverBroadcasts P.n X B B') (GatherLabel P.n X) :=
  (gatherPrograms P X).parallel
    ((System.synchronisedProduct (fun k => (BIn k).mapIdle (inputBroadcastLabelMap P.n X
      k))).parallel
      (System.synchronisedProduct (fun q => (BBind q).mapIdle (bindBroadcastLabelMap P.n X q))))

/-- **The gather instance** over the broadcast tier `BIn`, `BBind`: the two
tiers in parallel, the instance's events hidden, the result read back over the
interface alphabet. -/
noncomputable def instanceOverBroadcasts (P : Parameters) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))) :
    System (StateOverBroadcasts P.n X B B') (InstanceLabel P.n X) :=
  ((instanceOverBroadcastsExtended P X BIn BBind).abstract (gatherEvents P.n X)).relabel

/-- The state of the gather instance over Bracha's broadcast. -/
abbrev StateOverBracha (n : ℕ) (X : Type) : Type :=
  StateOverBroadcasts n X (BRB.BrachaState n X) (BRB.BrachaState n (AcceptedPairs n X))

/-- The state of the gather instance over the broadcast specification. -/
abbrev StateOverBroadcastSpecification (n : ℕ) (X : Type) : Type :=
  StateOverBroadcasts n X (BRB.SpecState n X) (BRB.SpecState n (AcceptedPairs n X))

/-- **The gather instance over Bracha's broadcast.** -/
noncomputable def instanceOverBracha (P : Parameters) (X : Type) [DecidableEq X] :
    System (StateOverBracha P.n X) (InstanceLabel P.n X) :=
  instanceOverBroadcasts P X (fun k => BRB.brachaInstance P k X) (fun q => BRB.brachaInstance P q
    (AcceptedPairs P.n X))

/-- **The gather instance over the broadcast specification.** -/
noncomputable def instanceOverBroadcastSpecification (P : Parameters) (X : Type) [DecidableEq X] :
    System (StateOverBroadcastSpecification P.n X) (InstanceLabel P.n X) :=
  instanceOverBroadcasts P X (fun k => BRB.specificationOverInstanceAlphabet P k X) (fun q =>
    BRB.specificationOverInstanceAlphabet P q (AcceptedPairs P.n X))

@[simp] theorem instanceOverBroadcasts_init (P : Parameters) {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))) :
    (instanceOverBroadcasts P X BIn BBind).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessRecord.initial P.n X)),
        NetworkState.initial P.n X),
        ((fun k => (BIn k).init), (fun q => (BBind q).init))) := rfl

@[simp] theorem instanceOverBracha_init (P : Parameters) :
    (instanceOverBracha P X).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessRecord.initial P.n X)),
        NetworkState.initial P.n X),
        ((fun _ => BRB.BrachaState.initial P.n X),
          (fun _ => BRB.BrachaState.initial P.n (AcceptedPairs P.n X)))) := rfl

@[simp] theorem instanceOverBroadcastSpecification_init (P : Parameters) :
    (instanceOverBroadcastSpecification P X).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessRecord.initial P.n X)),
        NetworkState.initial P.n X),
        ((fun _ => BRB.SpecState.initial P.n X),
          (fun _ => BRB.SpecState.initial P.n (AcceptedPairs P.n X)))) := rfl

end Rules

/-! ### Views of the instance state

The four components of the instance state, and the four writes that reach one
of them. A row of either tier is stated through these, so that a guard reads
`gatherTier s` where the implementation reads the gather instance state. -/

section Views

variable {n : ℕ} {B B' : Type}

/-- The gather tier's instance state: the programs beside the gather network
state. -/
def gatherTier (s : StateOverBroadcasts n X B B') : InstanceState n (ProcessRecord n X) (Message n
  X) := (s.1.1, s.1.2.network)

/-- The input instances. -/
def inputBroadcasts (s : StateOverBroadcasts n X B B') : ∀ _ : Fin n, B := s.2.1

/-- The bind instances. -/
def bindBroadcasts (s : StateOverBroadcasts n X B B') : ∀ _ : Fin n, B' := s.2.2

/-- The instance's core. -/
def core (s : StateOverBroadcasts n X B B') : Option (AcceptedPairs n X) := s.1.2.core

/-- Overwrite the gather tier's instance state. -/
def setGatherTier (s : StateOverBroadcasts n X B B') (t : InstanceState n (ProcessRecord n X)
  (Message n X)) :
    StateOverBroadcasts n X B B' := ((t.1, { s.1.2 with network := t.2 }), s.2)

/-- Overwrite the input instances. -/
def setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n,
  B) : StateOverBroadcasts n X B B' := (s.1, (b, s.2.2))

/-- Overwrite the bind instances. -/
def setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n,
  B') : StateOverBroadcasts n X B B' := (s.1, (s.2.1, b))

/-- Overwrite the core. -/
def setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs n X)) :
  StateOverBroadcasts n X B B' :=
  ((s.1.1, { s.1.2 with core := c }), s.2)

@[simp] theorem gatherTier_setGatherTier (s : StateOverBroadcasts n X B B') (t : InstanceState n
  (ProcessRecord n X) (Message n X)) :
    gatherTier (setGatherTier s t) = t := rfl
@[simp] theorem inputBroadcasts_setGatherTier (s : StateOverBroadcasts n X B B') (t : InstanceState
  n (ProcessRecord n X) (Message n X)) :
    inputBroadcasts (setGatherTier s t) = inputBroadcasts s := rfl
@[simp] theorem bindBroadcasts_setGatherTier (s : StateOverBroadcasts n X B B')
    (t : InstanceState n (ProcessRecord n X) (Message n X)) : bindBroadcasts (setGatherTier s t) =
      bindBroadcasts s := rfl
@[simp] theorem core_setGatherTier (s : StateOverBroadcasts n X B B') (t : InstanceState n
  (ProcessRecord n X) (Message n X)) :
    core (setGatherTier s t) = core s := rfl

@[simp] theorem gatherTier_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n,
    B) : gatherTier (setInputBroadcasts s b) = gatherTier s := rfl
@[simp] theorem inputBroadcasts_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B) :
    inputBroadcasts (setInputBroadcasts s b) = b := rfl
@[simp] theorem bindBroadcasts_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B) :
    bindBroadcasts (setInputBroadcasts s b) = bindBroadcasts s := rfl
@[simp] theorem core_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n, B) :
    core (setInputBroadcasts s b) = core s := rfl

@[simp] theorem gatherTier_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n,
    B') : gatherTier (setBindBroadcasts s b) = gatherTier s := rfl
@[simp] theorem inputBroadcasts_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B') :
    inputBroadcasts (setBindBroadcasts s b) = inputBroadcasts s := rfl
@[simp] theorem bindBroadcasts_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B') :
    bindBroadcasts (setBindBroadcasts s b) = b := rfl
@[simp] theorem core_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n, B') :
    core (setBindBroadcasts s b) = core s := rfl

@[simp] theorem gatherTier_setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs n
  X)) :
    gatherTier (setCore s c) = gatherTier s := rfl
@[simp] theorem inputBroadcasts_setCore (s : StateOverBroadcasts n X B B') (c : Option
  (AcceptedPairs n X)) :
    inputBroadcasts (setCore s c) = inputBroadcasts s := rfl
@[simp] theorem bindBroadcasts_setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs
  n X)) :
    bindBroadcasts (setCore s c) = bindBroadcasts s := rfl
@[simp] theorem core_setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs n X)) :
    core (setCore s c) = c := rfl

/-- Corruption (deviation D1): the gather network state and every broadcast coordinate corrupted
together, the programs untouched. The two transforms are the corruption of the tier's broadcast
instances. -/
def corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : StateOverBroadcasts P.n X B B') : StateOverBroadcasts P.n X B B' :=
  ((s.1.1, { s.1.2 with network := s.1.2.network.corrupt P id }),
    (fun k => cIn (s.2.1 k), fun q => cBind (s.2.2 q)))

@[simp] theorem gatherTier_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B' →
  B')
    (s : StateOverBroadcasts P.n X B B') :
    gatherTier (corruptAll P id cIn cBind s) = InstanceState.corrupt P id (gatherTier s) := rfl
@[simp] theorem inputBroadcasts_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B'
  → B')
    (s : StateOverBroadcasts P.n X B B') (k : Fin P.n) :
    inputBroadcasts (corruptAll P id cIn cBind s) k = cIn (inputBroadcasts s k) := rfl
@[simp] theorem bindBroadcasts_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B'
  → B')
    (s : StateOverBroadcasts P.n X B B') (q : Fin P.n) :
    bindBroadcasts (corruptAll P id cIn cBind s) q = cBind (bindBroadcasts s q) := rfl
@[simp] theorem core_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : StateOverBroadcasts P.n X B B') : core (corruptAll P id cIn cBind s) = core s := rfl

end Views

/-- A payload set is approved at the tier over the broadcast specification when every pair is a
committed entry of the input instance that carries it. -/
def approved {n : ℕ} (s : StateOverBroadcastSpecification n X) (A : AcceptedPairs n X) : Prop :=
  A.subMap (fun k => (inputBroadcasts s k).val)

section Determinacy

variable [DecidableEq X]

/-! ### Determinacy

Both rule tables written here are Dirac, so the composition is an LTS whenever
the broadcast tier is. -/

/-- Every gather program transition is Dirac. -/
theorem programStep_dirac {P : Parameters} {j : Fin P.n}
    {p : LocalState P.n (ProcessRecord P.n X) (Message P.n X)} {l : GatherLabel P.n X}
    {ν : PMF (LocalState P.n (ProcessRecord P.n X) (Message P.n X))} (h : ProgramStep P j p l ν) :
    ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every gather network transition is Dirac. -/
theorem networkStep_dirac {P : Parameters} {w : NetworkState P.n X} {l : GatherLabel P.n X}
    {μ : PMF (NetworkState P.n X)} (h : NetworkStep P w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A gather program is an LTS. -/
theorem gatherProgram_isLTS (P : Parameters) (j : Fin P.n) : (gatherProgram P j (X := X)).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The gather network is an LTS. -/
theorem gatherNetwork_isLTS (P : Parameters) : (gatherNetwork P X).IsLTS := fun _ _ _ h =>
  networkStep_dirac
  h

/-- The synchronised group of gather programs is an LTS. -/
theorem gatherProgramProduct_isLTS (P : Parameters) :
    (System.synchronisedProduct (gatherProgram P (X := X))).IsLTS :=
  System.synchronisedProduct_isLTS (gatherProgram_isLTS P)

/-- The gather tier is an LTS. -/
theorem gatherPrograms_isLTS (P : Parameters) : (gatherPrograms P X).IsLTS :=
  System.parallel_isLTS (gatherProgramProduct_isLTS P) (gatherNetwork_isLTS P)

/-- The two tiers in parallel form an LTS. -/
theorem instanceOverBroadcastsExtended_isLTS (P : Parameters) {B B' : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
    {BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))}
    (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS) :
    (instanceOverBroadcastsExtended P X BIn BBind).IsLTS :=
  System.parallel_isLTS (gatherPrograms_isLTS P)
    (System.parallel_isLTS
      (System.synchronisedProduct_isLTS (fun k => System.mapIdle_isLTS _ (hIn k)))
      (System.synchronisedProduct_isLTS (fun q => System.mapIdle_isLTS _ (hBind q))))

/-- The gather instance is an LTS. -/
theorem instanceOverBroadcasts_isLTS (P : Parameters) {B B' : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
    {BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))}
    (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS) :
    (instanceOverBroadcasts P X BIn BBind).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (instanceOverBroadcastsExtended_isLTS P hIn hBind) _)

/-- The gather instance over Bracha's broadcast is an LTS. -/
theorem instanceOverBracha_isLTS (P : Parameters) : (instanceOverBracha P X).IsLTS :=
  instanceOverBroadcasts_isLTS P (fun k => BRB.brachaInstance_isLTS P k) (fun q =>
    BRB.brachaInstance_isLTS P q)

/-- The gather instance over the broadcast specification is an LTS. -/
theorem instanceOverBroadcastSpecification_isLTS (P : Parameters) :
    (instanceOverBroadcastSpecification P X).IsLTS :=
  instanceOverBroadcasts_isLTS P (fun k => BRB.specificationOverInstanceAlphabet_isLTS P k) (fun q
    =>
    BRB.specificationOverInstanceAlphabet_isLTS P q)

/-- No gather program rule fires on `τ`: a program only ever moves in an event
or on one of the interface labels. The composition's silent transitions are
therefore the gather network's injections, the hidden events and the broadcast
tier's own silent steps. -/
theorem programStep_no_tau {P : Parameters} {j : Fin P.n}
    {p : LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
    {ν : PMF (LocalState P.n (ProcessRecord P.n X) (Message P.n X))}
    (h : ProgramStep P j p (Silent.τ : GatherLabel P.n X) ν) : False := by
  rw [gatherLabel_tau] at h; cases h

end Determinacy

/-! ### The specification read over the instance's interface

The specification speaks `Label n X`; the instance speaks `InstanceLabel n X`, in which
the call loop is a label of its own. `specificationLabelMap` identifies the loop with the
specification label it stands for, so that the specification's own loop row
answers it. -/

/-- The projection of the interface alphabet onto the specification's
alphabet. -/
def specificationLabelMap (n : ℕ) (X : Type) : InstanceLabel n X → Option (Label n X)
  | Sum.inl l => some l
  | Sum.inr (.callLoop id x) => some (.call id x)

@[simp] theorem specificationLabelMap_inl {n : ℕ} (l : Label n X) : specificationLabelMap n X
  (Sum.inl l) = some l := rfl

@[simp] theorem specificationLabelMap_callLoop {n : ℕ} (id : Fin n) (x : X) :
    specificationLabelMap n X (Sum.inr (.callLoop id x)) = some (.call id x) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specificationLabelMap_tau (n : ℕ) (X : Type) :
    specificationLabelMap n X (Silent.τ : InstanceLabel n X) = some (Silent.τ : Label n X) := rfl

/-- Only the silent label projects to the silent label: the call loop projects
to the call. -/
theorem specificationLabelMap_eq_tau {n : ℕ} {l : InstanceLabel n X}
    (h : specificationLabelMap n X l = some Label.tau) : l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e; simp at h

/-- Every interface label carries a specification label. -/
theorem specificationLabelMap_isSome {n : ℕ} (l : InstanceLabel n X) : ∃ l₀,
  specificationLabelMap n X l = some l₀ := by
    cases l with
  | inl l₀ => exact ⟨l₀, rfl⟩
  | inr e => cases e; exact ⟨_, rfl⟩

/-- **The lifted specification**: the gather specification read over the
instance's interface. -/
noncomputable def specificationOverInstanceAlphabet (P : Parameters) (X : Type) [DecidableEq X] :
    System (SpecState P.n X) (InstanceLabel P.n X) :=
  (specInst P X).mapIdle (specificationLabelMap P.n X)

@[simp] theorem specificationOverInstanceAlphabet_init (P : Parameters) [DecidableEq X] :
    (specificationOverInstanceAlphabet P X).init = SpecState.initial P.n X := rfl

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverInstanceAlphabet_isLTS (P : Parameters) [DecidableEq X] :
  (specificationOverInstanceAlphabet P X).IsLTS :=
  System.mapIdle_isLTS _ (specInst_isLTS P)

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `specificationLabelMap`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the instance
actually took. -/

/-- The left injection: the interface label a specification label sits at. -/
def labelSection {n : ℕ} : Label n X → InstanceLabel n X := Sum.inl

open scoped Classical in
/-- The section of `specificationLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
noncomputable def sectionAt {n : ℕ} (l₀ : Label n X) (l : InstanceLabel n X) : Label n X →
  InstanceLabel n X :=
  fun x => if x = l₀ then l else labelSection x

@[simp] theorem specificationLabelMap_labelSection {n : ℕ} (x : Label n X) : specificationLabelMap n
  X (labelSection x) = some x := rfl

/-- The left injection reflects the silent label. -/
theorem labelSection_eq_tau {n : ℕ} (x : Label n X) :
    (labelSection x : InstanceLabel n X) = (Silent.τ : InstanceLabel n X) ↔ x =
    (Silent.τ : Label n X) :=
  inl_eq_tau_iff x

theorem specificationLabelMap_sectionAt {n : ℕ} {l₀ : Label n X} {l : InstanceLabel n X}
    (hl : specificationLabelMap n X l = some l₀) (x : Label n X) : specificationLabelMap n X
      (sectionAt l₀ l x) = some x := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specificationLabelMap_labelSection]

theorem sectionAt_tau {n : ℕ} {l₀ : Label n X} {l : InstanceLabel n X}
    (hl : specificationLabelMap n X l = some l₀) (hl₀ : l₀ ≠ (Silent.τ : Label n X)) (x : Label n X)
    : sectionAt l₀ l x = (Silent.τ : InstanceLabel n X) ↔ x = (Silent.τ : Label n X) := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Label n X) := by
        rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    exact labelSection_eq_tau x

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_specificationOverInstanceAlphabet [DecidableEq X] (P : Parameters)
    {s s' : SpecState P.n X} (h : (specInst P X).weakLSilent s s') :
    (specificationOverInstanceAlphabet P X).weakLSilent s s' :=
  System.weakLSilent_mapIdle labelSection (fun _ => rfl) (fun x => labelSection_eq_tau x) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_specificationOverInstanceAlphabet [DecidableEq X] (P : Parameters)
    {s s' : SpecState P.n X} {l₀ : Label P.n X} {l : InstanceLabel P.n X}
    (hl₀ : l₀ ≠ (Silent.τ : Label P.n X)) (hl : specificationLabelMap P.n X l = some l₀)
    (h : (specInst P X).weakLStep s l₀ s') :
    (specificationOverInstanceAlphabet P X).weakLStep s l s' :=
  System.weakLStep_mapIdle (sectionAt l₀ l) (specificationLabelMap_sectionAt hl) (sectionAt_tau hl
    hl₀)
    (by simp [sectionAt]) h

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (synchronisedProduct, synchronisedProduct,
synchronisedProduct)`; the lemmas below unfold it once and for all, in both
directions. -/

/-- The instance's step relation, unfolded to the hidden-event case and the
interface-label case. -/
theorem instanceOverBroadcasts_step_iff (P : Parameters) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X)))
    (s : StateOverBroadcasts P.n X B B') (l : InstanceLabel P.n X)
    (μ : PMF (StateOverBroadcasts P.n X B B')) :
    (instanceOverBroadcasts P X BIn BBind).step s l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : GatherEvent P.n X,
        (instanceOverBroadcastsExtended P X BIn BBind).step s (Sum.inr e) μ) ∨
      (instanceOverBroadcastsExtended P X BIn BBind).step s (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_gatherEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_gatherEvents l, hstep⟩

/-! ### The synchronised group of broadcast instances

The `n` instances of one level, each read along its own pullback, under full
synchronisation. An instance whose pullback has no image at the label stands
still, so a label naming one instance moves that instance alone. -/

section SyncLift

variable {n : ℕ} {B Lbl Λ : Type} [Silent Λ] {A : ∀ _ : Fin n, System B Lbl}
  {φ : Fin n → Λ → Option Lbl} {a a' : ∀ _ : Fin n, B} {L : Λ}
  {μ : PMF (∀ _ : Fin n, B)}

omit [Silent Λ] in
/-- An instance whose pullback has no image at the label stands still. -/
theorem lift_idle {A₀ : System B Lbl} {ψ : Λ → Option Lbl} {c : B} (hψ : ψ L = none) :
    (A₀.mapIdle ψ).step c L (PMF.pure c) :=
  (System.mapIdle_step_none hψ _).mpr rfl

/-- A synchronised transition of the lifted family on a visible label: every
instance steps, and the joint distribution is Dirac. -/
theorem synchronisedProductMapIdle_inversion (hA : ∀ k, (A k).IsLTS) (hL : L ≠ Silent.τ)
    (h : (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a L μ) :
    ∃ a' : ∀ _ : Fin n, B, μ = PMF.pure a' ∧
      ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨hτ, -⟩
  · have hx : ∀ k, ∃ c, μ_ k = PMF.pure c :=
      fun k => System.mapIdle_isLTS (φ k) (hA k) _ _ _ (hall k)
    choose y hy using hx
    refine ⟨y, ?_, fun k => ?_⟩
    · rw [show μ_ = fun k => PMF.pure (y k) from funext hy]
      exact piPMF_pure y
    · rw [← hy k]; exact hall k
  · exact absurd hτ hL

/-- Build a synchronised transition of the lifted family from per-instance
Dirac steps. -/
theorem synchronisedProductMapIdle_pure (hL : L ≠ Silent.τ)
    (h : ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k))) :
    (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a L (PMF.pure a') := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hL, fun k => PMF.pure (a' k), h, (piPMF_pure a').symm⟩

/-- On a label no pullback has an image at, the lifted family stands still. -/
theorem synchronisedProductMapIdle_none (hL : L ≠ Silent.τ) (hφ : ∀ k, φ k L = none) :
    (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a L (PMF.pure a) :=
  synchronisedProductMapIdle_pure hL fun k => lift_idle (hφ k)

/-- A silent transition of the lifted family is a silent transition of exactly
one instance. -/
theorem synchronisedProductMapIdle_tau_inversion [Silent Lbl] (hA : ∀ k, (A k).IsLTS)
    (hτ : ∀ k, φ k (Silent.τ : Λ) = some (Silent.τ : Lbl))
    (h : (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a (Silent.τ : Λ) μ) :
    ∃ (k : Fin n) (c : B), μ = PMF.pure (Function.update a k c) ∧
      (A k).step (a k) (Silent.τ : Lbl) (PMF.pure c) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨hne, -⟩ | ⟨-, k, μ_k, hstep, rfl⟩
  · exact absurd rfl hne
  · rw [System.mapIdle_step_some (hτ k)] at hstep
    obtain ⟨c, rfl⟩ := hA k _ _ _ hstep
    exact ⟨k, c, by rw [piPMF_update_pure, PMF.pure_map], hstep⟩

/-- A silent transition of one instance is a silent transition of the lifted
family. -/
theorem synchronisedProductMapIdle_tau_step [Silent Lbl] {k : Fin n} {c : B}
    (hτ : φ k (Silent.τ : Λ) = some (Silent.τ : Lbl))
    (h : (A k).step (a k) (Silent.τ : Lbl) (PMF.pure c)) :
    (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a (Silent.τ : Λ)
      (PMF.pure (Function.update a k c)) := by
  rw [System.synchronisedProduct_step]
  refine Or.inr ⟨rfl, k, PMF.pure c, ?_, ?_⟩
  · rw [System.mapIdle_step_some hτ]; exact h
  · rw [piPMF_update_pure, PMF.pure_map]

end SyncLift

/-! ### The synchronised group of gather programs -/

section SyncGa

variable [DecidableEq X] {P : Parameters}
  {u x : ∀ _ : Fin P.n,
    LocalState P.n (ProcessRecord P.n X) (Message P.n X)} {l : GatherLabel P.n X}

/-- A synchronised transition of the gather programs on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem gatherProgramProduct_inversion
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X))}
    (h : (System.synchronisedProduct (gatherProgram P (X := X))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X), μ = PMF.pure x ∧ ∀ i,
    ProgramStep P i (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => programStep_dirac (hall i)
    choose y hy using hx
    refine ⟨y, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (y i) from funext hy]
      exact piPMF_pure y
    · rw [← hy i]; exact hall i
  · exact absurd hstep programStep_no_tau

/-- Build a synchronised transition of the gather programs from per-process
Dirac steps. -/
theorem gatherProgramProduct_pure (hl : l ≠ Silent.τ)
    (h : ∀ i, ProgramStep P i (u i) l (PMF.pure (x i))) :
    (System.synchronisedProduct (gatherProgram P (X := X))).step u l (PMF.pure x) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The gather programs have no silent transition: no program has a `τ` row. -/
theorem gatherProgramProduct_no_tau
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X))}
    (h : (System.synchronisedProduct (gatherProgram P (X := X))).step u
      (Silent.τ : GatherLabel P.n X) μ)
    : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau hstep

end SyncGa

/-! ### The two tiers in parallel

A visible label moves all four factors — the programs, the gather network, the
input instances and the bind instances — and the joint distribution is their
Dirac product. A silent label moves exactly one of the gather network, one
input instance or one bind instance. -/

section PreAt

variable [DecidableEq X] {P : Parameters} {B B' : Type}
  {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
  {BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {w w' : NetworkState P.n X} {a a' : ∀ _ : Fin P.n, B} {b b' : ∀ _ : Fin P.n, B'}
  {L : GatherLabel P.n X}

/-- **The joint inversion.** A visible transition of the two tiers: every
factor steps on the label, and the joint distribution is their Dirac
product. -/
theorem instanceOverBroadcastsExtended_joint_inversion (hIn : ∀ k, (BIn k).IsLTS)
    (hBind : ∀ q, (BBind q).IsLTS) {μ : PMF (StateOverBroadcasts P.n X B B')}
    (hL : L ≠ (Silent.τ : GatherLabel P.n X))
    (h : (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b)) L μ) :
    ∃ (x : ∀ _ : Fin P.n,
      LocalState P.n (ProcessRecord P.n X) (Message P.n X)) (w' : NetworkState P.n X) (a' : ∀ _ :
        Fin P.n, B) (b' : ∀ _ : Fin P.n, B'),
      μ = PMF.pure ((x, w'), (a', b')) ∧
      (∀ i, ProgramStep P i (u i) L (PMF.pure (x i))) ∧ NetworkStep P w L (PMF.pure w') ∧
      (∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) L (PMF.pure (a' k))) ∧
      (∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) L (PMF.pure (b' q))) :=
    by
  rw [instanceOverBroadcastsExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hga, hbr, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · rw [gatherPrograms, System.parallel_step] at hga
    rcases hga with ⟨-, ν₁, ν₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨y, rfl, hall⟩ := gatherProgramProduct_inversion hs
      obtain ⟨v, rfl⟩ := networkStep_dirac hn
      rw [System.parallel_step] at hbr
      rcases hbr with ⟨-, ρ₁, ρ₂, hi, hb, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · obtain ⟨c, rfl, hic⟩ := synchronisedProductMapIdle_inversion hIn hL hi
        obtain ⟨d, rfl, hbd⟩ := synchronisedProductMapIdle_inversion hBind hL hb
        exact ⟨y, v, c, d, by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure],
          hall, hn, hic, hbd⟩
      · exact absurd hτ hL
      · exact absurd hτ hL
    · exact absurd hτ hL
    · exact absurd hτ hL
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The silent inversion.** A silent transition of the two tiers is an
injection of the gather network, a silent step of one input instance, or a
silent step of one bind instance: no gather program has a `τ` row. -/
theorem instanceOverBroadcastsExtended_tau_inversion (hIn : ∀ k, (BIn k).IsLTS)
    (hBind : ∀ q, (BBind q).IsLTS) {μ : PMF (StateOverBroadcasts P.n X B B')}
    (h : (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
      (Silent.τ : GatherLabel P.n X) μ) :
    (∃ v, μ = PMF.pure ((u, v), (a, b)) ∧
      NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure v)) ∨
    (∃ (k : Fin P.n) (c : B), μ = PMF.pure ((u, w), (Function.update a k c, b)) ∧
      (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) ∨
    (∃ (q : Fin P.n) (d : B'), μ = PMF.pure ((u, w), (a, Function.update b q d)) ∧
      (BBind q).step (b q) (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X)) (PMF.pure d)) :=
        by
  rw [instanceOverBroadcastsExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hga, rfl⟩ | ⟨-, μ₂, hbr, rfl⟩
  · exact absurd rfl hτ
  · rw [gatherPrograms, System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ν₁, hs, rfl⟩ | ⟨-, ν₂, hn, rfl⟩
    · exact absurd rfl hτ
    · exact absurd hs gatherProgramProduct_no_tau
    · obtain ⟨v, rfl⟩ := networkStep_dirac hn
      exact Or.inl ⟨v, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hn⟩
  · rw [System.parallel_step] at hbr
    rcases hbr with ⟨hτ, -⟩ | ⟨-, ρ₁, hi, rfl⟩ | ⟨-, ρ₂, hb, rfl⟩
    · exact absurd rfl hτ
    · obtain ⟨k, c, rfl, hstep⟩ :=
        synchronisedProductMapIdle_tau_inversion hIn
          (fun k => inputBroadcastLabelMap_tau P.n X k) hi
      exact Or.inr
        (Or.inl ⟨k, c, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩)
    · obtain ⟨q, d, rfl, hstep⟩ :=
        synchronisedProductMapIdle_tau_inversion hBind
          (fun q => bindBroadcastLabelMap_tau P.n X q) hb
      exact Or.inr
        (Or.inr ⟨q, d, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩)

/-- Build a visible transition of the two tiers from the four factors' Dirac
steps. -/
theorem instanceOverBroadcastsExtended_label_step (hL : L ≠ (Silent.τ : GatherLabel P.n X))
    (hproc : ∀ i, ProgramStep P i (u i) L (PMF.pure (x i))) (hnet : NetworkStep P w L (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) L (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) L
      (PMF.pure (b' q)))
    :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b)) L
    (PMF.pure ((x, w'), (a', b'))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, w'), PMF.pure (a', b'), ?_, ?_,
    (prodPMF_pure_pure _ _).symm⟩
  · rw [gatherPrograms, System.parallel_step]
    exact Or.inl ⟨hL, PMF.pure x, PMF.pure w', gatherProgramProduct_pure hL hproc, hnet,
      (prodPMF_pure_pure _ _).symm⟩
  · rw [System.parallel_step]
    exact Or.inl ⟨hL, PMF.pure a', PMF.pure b', synchronisedProductMapIdle_pure hL hin,
      synchronisedProductMapIdle_pure hL hbind, (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the two tiers from an injection of the gather
network. -/
theorem instanceOverBroadcastsExtended_tau_network
    (hn : NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure w')) :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w'), (a, b))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure (u, w'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [gatherPrograms, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the two tiers from a silent step of one input
instance. -/ theorem instanceOverBroadcastsExtended_tau_in {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w), (Function.update a k c, b))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update a k c, b), ?_,
    (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure (Function.update a k c),
    synchronisedProductMapIdle_tau_step (inputBroadcastLabelMap_tau P.n X k) h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the two tiers from a silent step of one bind
instance. -/ theorem instanceOverBroadcastsExtended_tau_bind {q : Fin P.n} {d : B'}
    (h : (BBind q).step (b q) (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X)) (PMF.pure d))
    :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w), (a, Function.update b q d))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (a, Function.update b q d), ?_,
    (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update b q d),
    synchronisedProductMapIdle_tau_step (bindBroadcastLabelMap_tau P.n X q) h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the instance. -/
theorem instanceOverBroadcasts_event_step (e : GatherEvent P.n X)
    (hproc : ∀ i, ProgramStep P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hnet : NetworkStep P w (Sum.inr e) (PMF.pure w'))
    (hin : ∀ k,
      ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) (Sum.inr e) (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) (Sum.inr e)
      (PMF.pure (b' q))) :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
      (PMF.pure ((x, w'), (a', b'))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr
    (Or.inl ⟨rfl, e, instanceOverBroadcastsExtended_label_step (by simp) hproc hnet hin hbind⟩)

/-- A visible interface label is a transition of the instance. -/
theorem instanceOverBroadcasts_label_step {l : InstanceLabel P.n X} (hl : l ≠ Sum.inl Label.tau)
    (hproc : ∀ i, ProgramStep P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hnet : NetworkStep P w (Sum.inl l) (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) (Sum.inl l)
      (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) (Sum.inl l)
      (PMF.pure (b' q)))
    :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) l (PMF.pure ((x, w'), (a', b'))) :=
    by
  refine (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_label_step ?_ hproc hnet hin hbind))
  rw [gatherLabel_tau]
  simpa using hl

/-- An injection of the gather network is a silent transition of the
instance. -/ theorem instanceOverBroadcasts_tau_network
    (hn : NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure w')) :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
    (PMF.pure ((u, w'), (a, b))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_network hn))

/-- A silent step of one input instance is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_in {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
      (PMF.pure ((u, w), (Function.update a k c, b))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_in h))

/-- A silent step of one bind instance is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_bind {q : Fin P.n} {d : B'}
    (h : (BBind q).step (b q) (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X)) (PMF.pure d))
      :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
      (PMF.pure ((u, w), (a, Function.update b q d))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_bind h))

end PreAt

/-! ### The pullbacks, label by label -/

section PullRows

variable {n : ℕ} (X : Type) (k q id j q' k' i : Fin n)

@[simp] theorem inputBroadcastLabelMap_call (x : X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (.call id x))) =
      if k = id then some (Sum.inl (.call x)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_fail :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (Label.fail (X := X) id))) = some (Sum.inl (.fail
      id)) := rfl
@[simp] theorem inputBroadcastLabelMap_ret (g : Fin n → Option X) (C : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem inputBroadcastLabelMap_callLoop (x : X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inr (.callLoop id x))) =
      if k = id then some (Sum.inr (.callLoop x)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_send (m : Message n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.send j m)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_deliver (m : Message n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.deliver i j m)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_inputBroadcastRet (v : X) :
    inputBroadcastLabelMap n X k (Sum.inr (.inputBroadcastRet k' j v)) =
      if k = k' then some (Sum.inl (.ret j v)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_bindCall (U : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.bindCall j U)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_bindRet (U : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.bindRet q' j U)) = none := rfl

@[simp] theorem bindBroadcastLabelMap_call (x : X) :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inl (.call id x))) = none := rfl
@[simp] theorem bindBroadcastLabelMap_fail :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inl (Label.fail (X := X) id))) = some (Sum.inl (.fail
      id)) := rfl
@[simp] theorem bindBroadcastLabelMap_ret (g : Fin n → Option X) (C : AcceptedPairs n X) :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem bindBroadcastLabelMap_callLoop (x : X) :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inr (.callLoop id x))) = none := rfl
@[simp] theorem bindBroadcastLabelMap_send (m : Message n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.send j m)) = none := rfl
@[simp] theorem bindBroadcastLabelMap_deliver (m : Message n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.deliver i j m)) = none := rfl
@[simp] theorem bindBroadcastLabelMap_inputBroadcastRet (v : X) :
    bindBroadcastLabelMap n X q (Sum.inr (.inputBroadcastRet k' j v)) = none := rfl
@[simp] theorem bindBroadcastLabelMap_bindCall (U : AcceptedPairs n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.bindCall j U)) =
      if q = j then some (Sum.inl (.call U)) else none := rfl
@[simp] theorem bindBroadcastLabelMap_bindRet (U : AcceptedPairs n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.bindRet q' j U)) =
      if q = q' then some (Sum.inl (.ret j U)) else none := rfl

end PullRows

/-! ### One lifted instance's step, by the pullback's value -/

section LiftRows

variable {S B Lbl Λ : Type} {A₀ : System S Lbl} {ψ : Λ → Option Lbl} {s s' : S} {L : Λ}

/-- An instance whose pullback has no image at the label has not moved. -/
theorem lift_step_none (hψ : ψ L = none) (h : (A₀.mapIdle ψ).step s L (PMF.pure s')) : s' = s :=
  PMF.pure_injective ((System.mapIdle_step_none hψ _).mp h)

/-- An instance whose pullback has an image at the label steps on that
image. -/
theorem lift_step_some {l₀ : Lbl} (hψ : ψ L = some l₀)
    (h : (A₀.mapIdle ψ).step s L (PMF.pure s')) : A₀.step s l₀ (PMF.pure s') :=
  (System.mapIdle_step_some hψ _).mp h

/-- A row of an instance is a transition read through the pullback. -/
theorem row_lift_step {l₀ : Lbl} (hψ : ψ L = some l₀) (h : A₀.step s l₀ (PMF.pure s')) :
    (A₀.mapIdle ψ).step s L (PMF.pure s') :=
  (System.mapIdle_step_some hψ _).mpr h

variable {n : ℕ} {A : ∀ _ : Fin n, System B Lbl} {φ : Fin n → Λ → Option Lbl}
  {a a' : ∀ _ : Fin n, B} {k : Fin n}

/-- A label naming one instance moves that instance alone. -/
theorem lift_update {l₀ : Lbl} {c : B} (hk : φ k L = some l₀)
    (hother : ∀ k', k' ≠ k → φ k' L = none) (h : (A k).step (a k) l₀ (PMF.pure c)) :
    ∀ k', ((A k').mapIdle (φ k')).step (a k') L (PMF.pure (Function.update a k c k')) := by
  intro k'
  by_cases hkk : k' = k
  · subst hkk; rw [Function.update_self, System.mapIdle_step_some hk]; exact h
  · rw [Function.update_of_ne hkk]; exact lift_idle (hother k' hkk)

/-- A label with an image at every instance moves them all. -/
theorem lift_all {l₀ : Fin n → Lbl} (hk : ∀ k, φ k L = some (l₀ k))
    (h : ∀ k, (A k).step (a k) (l₀ k) (PMF.pure (a' k))) :
    ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k)) :=
  fun k => (System.mapIdle_step_some (hk k) _).mpr (h k)

end LiftRows

/-! ### One gather program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. -/

section ProcInversion

variable [DecidableEq X] {P : Parameters} {j : Fin P.n}
  {p : LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {ν : PMF (LocalState P.n (ProcessRecord P.n X) (Message P.n X))}

theorem programStep_call_own {x : X} (h : ProgramStep P j p (Sum.inl (Sum.inl (.call j x))) ν) :
    p.process.input = none ∧ ν = PMF.pure (p.setProcess { p.process with input := some x }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_call_foreign {i : Fin P.n} {x : X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inl (Sum.inl (.call i x))) ν) : ν = PMF.pure p := by
  cases h
  case call => exact absurd rfl hi
  case callIdle => rfl

theorem programStep_callLoop {i : Fin P.n} {x : X}
    (h : ProgramStep P j p (Sum.inl (Sum.inr (.callLoop i x))) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl
  case callLoopIdle => rfl

theorem programStep_ret_own {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inl (Sum.inl (.ret j g C))) ν) :
    p.process.input ≠ none ∧ p.process.sentBind ≠ none ∧
      (∀ k x, g k = some x → holdsInputBroadcastReturn p.process k x) ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBindBroadcastReturn p.process q U ∧ AcceptedPairs.subMap U g) ∧
      p.process.returned = false ∧ ν = PMF.pure
        (p.setProcess { p.process with returned := true }) := by
  cases h
  case ret =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_ret_foreign {i : Fin P.n} {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
    (hi : i ≠ j) (h : ProgramStep P j p (Sum.inl (Sum.inl (.ret i g C))) ν) : ν = PMF.pure p := by
  cases h
  case ret => exact absurd rfl hi
  case retIdle => rfl

theorem programStep_fail {i : Fin P.n} (h : ProgramStep P j p (Sum.inl (Sum.inl (.fail i))) ν) :
    ν = PMF.pure p := by
  cases h
  case failIdle => rfl

theorem programStep_send_echo_own {A : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.send j (.echo A))) ν) :
    A = p.process.accepted ∧ p.process.input ≠ none ∧ P.n - P.f ≤ p.process.accepted.card ∧
      p.process.sentEcho = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho := some p.process.accepted }) := by
  cases h
  case sendEcho => exact ⟨rfl, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_vote_own {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.send j (.vote U))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho ≠ none ∧ approvedBy p.process U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Message.echo A ∈ p.received q ∧ approvedBy p.process A ∧ A ⊆ U) ∧
      p.process.sentVote = none ∧ ν = PMF.pure
        (p.setProcess { p.process with sentVote := some U }) := by
  cases h
  case sendVote =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_foreign {i : Fin P.n} {m : Message P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.send i m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hi

theorem programStep_deliver_own {k : Fin P.n} {m : Message P.n X}
    (h : ProgramStep P j p (Sum.inr (.deliver j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_deliver_foreign {i k : Fin P.n} {m : Message P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

theorem programStep_inputBroadcastRet_own {k : Fin P.n} {v : X}
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastRet k j v)) ν) :
    ν = PMF.pure (p.setProcess { p.process with
      inputBroadcastReturned :=
        Function.update p.process.inputBroadcastReturned k (some v) }) := by
  cases h
  case inputBroadcastRetReceive => rfl
  case inputBroadcastRetIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_inputBroadcastRet_foreign {k i : Fin P.n} {v : X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastRet k i v)) ν) : ν = PMF.pure p := by
  cases h
  case inputBroadcastRetReceive => exact absurd rfl hi
  case inputBroadcastRetIdle => rfl

theorem programStep_bindCall_own {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.bindCall j U)) ν) :
    p.process.input ≠ none ∧ p.process.sentVote ≠ none ∧ p.process.sentBind = none ∧
      approvedBy p.process U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Message.vote W ∈ p.received q ∧ approvedBy p.process W ∧ W ⊆ U) ∧
      ν = PMF.pure (p.setProcess { p.process with sentBind := some U }) := by
  cases h
  case bindCall =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case bindCallIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_bindCall_foreign {i : Fin P.n} {U : AcceptedPairs P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.bindCall i U)) ν) : ν = PMF.pure p := by
  cases h
  case bindCall => exact absurd rfl hi
  case bindCallIdle => rfl

theorem programStep_bindRet_own {q : Fin P.n} {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.bindRet q j U)) ν) :
    ν = PMF.pure
      (p.setProcess { p.process with
        bindBroadcastReturned :=
          Function.update p.process.bindBroadcastReturned q (some U) }) := by
  cases h
  case bindRetReceive => rfl
  case bindRetIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_bindRet_foreign {q i : Fin P.n} {U : AcceptedPairs P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.bindRet q i U)) ν) : ν = PMF.pure p := by
  cases h
  case bindRetReceive => exact absurd rfl hi
  case bindRetIdle => rfl

end ProcInversion

/-! ### The gather network's rules, by label class -/

section NetInversion

variable [DecidableEq X] {P : Parameters} {w : NetworkState P.n X} {μ : PMF (NetworkState P.n X)}

theorem networkStep_call {id : Fin P.n} {x : X}
    (h : NetworkStep P w (Sum.inl (Sum.inl (.call id x))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_callLoop {id : Fin P.n} {x : X}
    (h : NetworkStep P w (Sum.inl (Sum.inr (.callLoop id x))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_ret {id : Fin P.n} {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
    (h : NetworkStep P w (Sum.inl (Sum.inl (.ret id g C))) μ) :
    C = w.core.getD (coreOfNetwork P w.network) ∧ μ = PMF.pure { w with core := some C } := by
  cases h; exact ⟨rfl, rfl⟩

theorem networkStep_fail {i : Fin P.n} (h : NetworkStep P w (Sum.inl (Sum.inl (.fail i))) μ) :
    μ = PMF.pure { w with network := w.network.corrupt P i } := by
  cases h; rfl

theorem networkStep_send {j : Fin P.n} {m : Message P.n X}
    (h : NetworkStep P w (Sum.inr (.send j m)) μ) :
    μ = PMF.pure { w with network := w.network.recordSent j m } := by
  cases h; rfl

theorem networkStep_deliver {i j : Fin P.n} {m : Message P.n X}
    (h : NetworkStep P w (Sum.inr (.deliver i j m)) μ) : m ∈ w.network.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_inputBroadcastRet {k j : Fin P.n} {v : X}
    (h : NetworkStep P w (Sum.inr (.inputBroadcastRet k j v)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_bindCall {j : Fin P.n} {U : AcceptedPairs P.n X}
    (h : NetworkStep P w (Sum.inr (.bindCall j U)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_bindRet {q j : Fin P.n} {U : AcceptedPairs P.n X}
    (h : NetworkStep P w (Sum.inr (.bindRet q j U)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_tau (h : NetworkStep P w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : Message P.n X), j ∈ w.network.F ∧
      μ = PMF.pure { w with network := w.network.recordSent j m } := by
  cases h
  case byzantine j m hF => exact ⟨j, m, hF, rfl⟩

end NetInversion

/-- A function fixed at `i` and unchanged elsewhere is the old one updated at
`i`. -/
theorem funUpdate {ι β : Type} [DecidableEq ι] {f g : ι → β} {i : ι} {y : β}
    (hi : g i = y) (hne : ∀ i', i' ≠ i → g i' = f i') : g = Function.update f i y := by
  funext i'
  by_cases h : i' = i
  · subst h; rw [hi, Function.update_self]
  · rw [hne i' h, Function.update_of_ne h]

/-! ### One state, four views

What a joint step delivers is a program function given pointwise — its value
at the acting process, and its agreement with the old one elsewhere — where a
row writes with `setGatherTier` and `InstanceState.setProcess`. The lemmas here close that
gap. -/

section Frame

variable [DecidableEq X] {P : Parameters} {B B' : Type}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {w : NetworkState P.n X} {a : ∀ _ : Fin P.n, B} {b : ∀ _ : Fin P.n, B'}

omit [DecidableEq X] in
/-- A program function fixed at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem programFunction_update {j : Fin P.n}
    {r : LocalState P.n (ProcessRecord P.n X) (Message P.n X)} (hj : x j = r)
    (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j r := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem programStep_update {j : Fin P.n} {r : LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
    {l : GatherLabel P.n X} (hj : ProgramStep P j (u j) l (PMF.pure r))
    (hne : ∀ i, i ≠ j → ProgramStep P i (u i) l (PMF.pure (u i))) :
    ∀ i, ProgramStep P i (u i) l (PMF.pure (Function.update u j r i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

omit [DecidableEq X] in
/-- A record write at one program, with the network state untouched. -/
theorem stateOverBroadcasts_setProcess {j : Fin P.n} {pr : ProcessRecord P.n X}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, w), (a, b)) : StateOverBroadcasts P.n X B B') = setGatherTier ((u, w), (a, b))
    (InstanceState.setProcess (gatherTier ((u, w), (a, b))) j pr) := by
  rw [programFunction_update hj hne]; rfl

/-- A record write at one program together with the network state recording the
message that write multicasts. -/
theorem stateOverBroadcasts_setProcess_recordSent {j : Fin P.n} {pr : ProcessRecord P.n X}
    {m : Message P.n X} (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, { w with network := w.network.recordSent j m }), (a, b)) : StateOverBroadcasts P.n X B B')
    = setGatherTier ((u, w), (a, b))
    ((InstanceState.setProcess (gatherTier ((u, w), (a, b))) j pr).multicast j m) := by
  rw [programFunction_update hj hne]; rfl

omit [DecidableEq X] in
/-- The programs stand still and the network state is untouched. -/
theorem stateOverBroadcasts_idle (hall : ∀ i, x i = u i) :
    (((x, w), (a, b)) : StateOverBroadcasts P.n X B B') = ((u, w), (a, b)) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem stateOverBroadcasts_deliver {i k : Fin P.n} {m : Message P.n X}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    (((x, w), (a, b)) : StateOverBroadcasts P.n X B B') = setGatherTier ((u, w), (a, b))
    (InstanceState.receiveMessage (gatherTier ((u, w), (a, b))) i k m) := by
  rw [programFunction_update hi hne]; rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem stateOverBroadcasts_recordSent {k : Fin P.n} {m : Message P.n X} :
    (((u, { w with network := w.network.recordSent k m }), (a,
      b)) : StateOverBroadcasts P.n X B B') = setGatherTier ((u, w), (a,
        b)) (InstanceState.multicast (gatherTier ((u, w), (a, b))) k m) := rfl

omit [DecidableEq X] in
/-- A return: the returner's flag and the instance's core. -/
theorem stateOverBroadcasts_ret {id : Fin P.n} {pr : ProcessRecord P.n X} {C : AcceptedPairs P.n X}
    (hj : x id = (u id).setProcess pr) (hne : ∀ i, i ≠ id → x i = u i) :
    (((x, { w with core := some C }), (a, b)) : StateOverBroadcasts P.n X B B') = setCore
    (setGatherTier ((u, w), (a, b)) (InstanceState.setProcess (gatherTier ((u, w), (a, b))) id pr))
    (some C) := by
  rw [programFunction_update hj hne]; rfl

omit [DecidableEq X] in
/-- Corruption is the network state's own write beside the broadcast
coordinates' (D1). -/
theorem stateOverBroadcasts_corrupt {id : Fin P.n} {cIn : B → B} {cBind : B' → B'} (hall : ∀ i,
    x i = u i) : (((x, { w with network := w.network.corrupt P id }),
        ((fun k => cIn (a k)), fun q => cBind (b q))) : StateOverBroadcasts P.n X B B') =
      corruptAll P id cIn cBind ((u, w), (a, b)) := by
  rw [funext hall]; rfl

omit [DecidableEq X] in
/-- A write at one input instance. -/
theorem stateOverBroadcasts_setInputBroadcasts {k : Fin P.n} {c : B} :
    (((u, w), (Function.update a k c, b)) : StateOverBroadcasts P.n X B B') =
      setInputBroadcasts ((u, w), (a, b)) (Function.update (inputBroadcasts ((u, w), (a,
        b))) k c) := rfl

omit [DecidableEq X] in
/-- A write at one bind instance. -/
theorem stateOverBroadcasts_setBindBroadcasts {q : Fin P.n} {d : B'} :
    (((u, w), (a, Function.update b q d)) : StateOverBroadcasts P.n X B B') =
      setBindBroadcasts ((u, w), (a, b)) (Function.update (bindBroadcasts ((u, w), (a,
        b))) q d) := rfl

end Frame

end Gather
end ABA
end PLTS
