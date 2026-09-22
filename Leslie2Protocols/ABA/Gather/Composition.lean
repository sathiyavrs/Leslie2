/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.BrachaSpecificationOverInstanceAlphabet
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
therefore has a label of its own, `LoopLabel.callLoop id x`. The interface
alphabet is `InstanceLabel n X = Label n X ⊕ LoopLabel n X`.

The instance-internal alphabet is `GatherLabel n X = InstanceLabel n X ⊕ GatherEvent n X`. Its
five events are the gather multicast and delivery, the return of an input
instance, the call of a bind instance and the return of a bind instance. They
are hidden before anything outside sees the instance: `instanceOverBroadcasts` speaks
`InstanceLabel n X`.

A broadcast instance joins the composition along a pullback — `inputBroadcastLabelMap k` for
the instance broadcasting `k`'s input, `bindBroadcastLabelMap q` for the instance
broadcasting `q`'s `BIND` payload. The pullback names the instance: a label
carrying another instance's index has no image, and that instance is unchanged.
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

/-- The input instances. One per process, carrying that process's input; these and the `n` bind
instances are the `2n` reliable-broadcast instances of a gather instance. -/
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

end Gather
end ABA
end PLTS
