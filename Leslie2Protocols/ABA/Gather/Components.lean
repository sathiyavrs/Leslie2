/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Components
import Leslie2Protocols.ABA.Gather.MessagesAndCommonCore
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# The components of one gather instance

One gather instance over an arbitrary payload type `X`, taken apart into the pieces that run it:
`n` per-process gather programs beside the gather network.

A gather program holds one process's variables and the messages delivered to it, indexed by
sender (`ABA.LocalState`). Its guards read its own variables and its own delivered sets. The gather
network holds the per-sender sent sets, the corrupted set (`ABA.NetworkState`) and the instance's
core; it reads no program's variables. A multicast is a synchronised step of the sender, which
writes its variables, and the network, which records the message. A delivery is a synchronised step
of the network,
which checks that the message is sent under the named sender, and the receiver, which files it
under that sender.

`ProgramStep` is the step relation of process `j`'s program and `NetworkStep` that of the gather
network. `gatherProgram` and `gatherNetwork` are the two automata they carry, and `gatherPrograms`
is the programs beside the network.

## The alphabets

The specification's `call id x` carries two transitions, the call and the input-enabledness loop.
The composition splits them across two labels, as the reliable-broadcast composition does one level
down (`ABA/ReliableBroadcast/Bracha/Components.lean`). A gather program's variables and the
broadcast instance
are different components, so a single label carrying both transitions would also carry the mixed
pairs. The loop therefore has a label of its own, `LoopLabel.callLoop id x`. The interface alphabet
is `InstanceLabel n X = Label n X ⊕ LoopLabel n X`.

The instance-internal alphabet is `GatherLabel n X = InstanceLabel n X ⊕ GatherEvent n X`. Its
six events are the gather multicast and delivery, the call and the return of an input instance,
and the call and the return of a bind instance. They are hidden before anything outside sees the
instance, and `gatherEvents` collects the labels hidden there.

A broadcast instance has its own interface alphabet and joins the composition along a pullback
that names it -- `inputBroadcastLabelMap k` for the instance broadcasting `k`'s input,
`bindBroadcastLabelMap q` for the instance broadcasting `q`'s `BIND` payload (D32). A label
carrying another instance's index has no image, and that instance is unchanged. Corruption and the
silent label have an image at every instance, so `fail` is a broadcast across the whole
composition.

## What the broadcast instances returned

A gather program reads no neighbouring coordinate. What a broadcast instance has returned to it is
written on the return event into its own variables: `inputBroadcastReturned k` is the value instance
`k` returned here, `bindBroadcastReturned q` is the payload bind instance `q` returned here. The
four transitions that read what has been returned -- `sendEcho`, `sendVote`, `bindCall` and `ret`
-- read the returned values through `ProcessVariables.accepted`, `holdsInputBroadcastReturn`,
`holdsBindBroadcastReturn` and `approvedBy`.

## The core

The core is a function of the gather network state alone (`coreOf_networkState_only`), so the
gather network holds it. `coreOfNetwork` reads it off the network state,
`coreOf_eq_coreOfNetwork` identifies the two systems, and the network's `ret` transition writes the
core and carries it on the label.

## Model and deviations

* **D1 (determinised `fail`).** `NetworkState.corrupt` is the total Dirac function guarded by
  `id ∉ F ∧ |F| < f`. It is the gather network's own transition, and the programs are unchanged on
  `fail`: their variables are corruption-blind.
* **D5 (set-based network).** A multicast records the message in the sender's sent set and a
  delivery does not consume it; a corrupted sender's injections enter its sent set through the
  network's own silent transition.
* **D32 (two broadcast families).** The inputs and the `BIND` payloads are carried by two families
  of `n` instances each, read along the two pullbacks.
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

/-- The instance's own events: the gather multicast and delivery, the call and the return of an
input instance, and the call and return of a bind instance. -/
inductive GatherEvent (n : ℕ) (X : Type) : Type
  /-- Process `j` hands `m` to the gather network. -/
  | send (j : Fin n) (m : Message n X)
  /-- The gather network delivers `j`'s `m` to `i`. -/
  | deliver (i j : Fin n) (m : Message n X)
  /-- Process `j` calls the instance broadcasting its input `x`, the
  `r-broadcast(⟨1, x_i⟩, p_i)` of AFW25's Algorithm 5, line 6, and the `BRB_id.call(m)` of
  LeslieBP's Algorithm 4. -/
  | inputBroadcastCall (j : Fin n) (x : X)
  /-- The instance broadcasting `k`'s input returns `v` to `j`. -/
  | inputBroadcastRet (k j : Fin n) (v : X)
  /-- Process `j` calls the instance broadcasting its `BIND` payload `U`. -/
  | bindCall (j : Fin n) (U : AcceptedPairs n X)
  /-- The instance broadcasting `q`'s `BIND` payload returns `U` to `j`. -/
  | bindRet (q j : Fin n) (U : AcceptedPairs n X)

/-- The instance-internal alphabet: the interface alphabet plus the six
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

/-! ### The variables -/

/-- The variables of one gather program: the base variables beside what the
broadcast instances have returned here. -/
structure ProcessVariables (n : ℕ) (X : Type) extends BaseProcessVariables n X where
  /-- `inputBroadcastReturned k` — the value the instance broadcasting `k`'s input returned
  here. -/
  inputBroadcastReturned : Fin n → Option X
  /-- `bindBroadcastReturned q` — the payload the instance broadcasting `q`'s `BIND`
  payload returned here. -/
  bindBroadcastReturned : Fin n → Option (AcceptedPairs n X)

/-- The initial variables: nothing called, nothing sent, nothing returned
here. -/
def ProcessVariables.initial (n : ℕ) (X : Type) : ProcessVariables n X :=
  { BaseProcessVariables.initial n X with
    inputBroadcastReturned := fun _ => none,
    bindBroadcastReturned := fun _ => none }

/-- `p` holds the value `v` of the instance broadcasting `k`'s input. -/
def holdsInputBroadcastReturn {n : ℕ} {X : Type} (p : ProcessVariables n X) (k : Fin n) (v : X) :
  Prop
  :=
  p.inputBroadcastReturned k = some v

/-- `p` holds the payload `U` of the instance broadcasting `q`'s `BIND`
payload. -/
def holdsBindBroadcastReturn {n : ℕ} {X : Type} (p : ProcessVariables n X) (q : Fin n)
    (U : AcceptedPairs n X) : Prop :=
  p.bindBroadcastReturned q = some U

/-- A payload set is approved by `p` when `p` holds every one of its pairs. -/
def approvedBy {n : ℕ} {X : Type} (p : ProcessVariables n X) (A : AcceptedPairs n X) : Prop :=
  A.subMap p.inputBroadcastReturned

/-- The accepted pairs of `p`: the entries of what its input instances returned. AFW25's
Algorithm 5 writes this set `AP_i` and multicasts it as the `ECHO` payload. -/
def ProcessVariables.accepted {n : ℕ} {X : Type} [DecidableEq X] (p : ProcessVariables n X) :
  AcceptedPairs n X :=
  Finset.univ.biUnion fun k =>
    match p.inputBroadcastReturned k with
    | some v => {(k, v)}
    | none => ∅

/-- A pair is accepted exactly when the input instance's returned value holds it. -/
theorem ProcessVariables.mem_accepted {n : ℕ} {X : Type} [DecidableEq X] {p : ProcessVariables n X}
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
theorem ProcessVariables.accepted_subMap {n : ℕ} {X : Type} [DecidableEq X] (p : ProcessVariables n
  X) :
    p.accepted.subMap p.inputBroadcastReturned :=
  fun _ ha => ProcessVariables.mem_accepted.mp ha

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

/-- The core read off a network state. The programs' variables are not consulted
(`coreOf_networkState_only`), so any vector of variables gives the same set. -/
noncomputable def coreOfNetwork {X : Type} (P : Parameters)
    (w : ABA.NetworkState P.n (Message P.n X)) : AcceptedPairs P.n X :=
  coreOf P ((fun _ => LocalState.initial P.n (Message P.n X) (BaseProcessVariables.initial P.n X)),
    w)

/-- The core of an instance state is the core of its network state. -/
theorem coreOf_eq_coreOfNetwork {X : Type} (P : Parameters)
    (w : InstanceState P.n (BaseProcessVariables P.n X) (Message P.n X)) :
    coreOf P w = coreOfNetwork P w.2 :=
  coreOf_networkState_only w _ rfl

/-! ### The pullbacks

A broadcast instance has its own interface alphabet `BRB.InstanceLabel`. It joins
the composition along a pullback that names it: a label carrying another
instance's index has no image and leaves that instance idle. -/

/-- The pullback along which the instance broadcasting `k`'s input is read. The gather's own
`call` and its call loop have no image here: the call of the instance is the event
`inputBroadcastCall`. -/
def inputBroadcastLabelMap (n : ℕ) (X : Type) (k : Fin n) : GatherLabel n X → Option
  (BRB.InstanceLabel n X)
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inr (.inputBroadcastCall j x) => if k = j then some (Sum.inl (.call x)) else none
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

section Transitions

variable [DecidableEq X]

/-! ### The gather program

Process `j`'s program. Every guard reads its own variables and its own delivered sets. An event
transition carries the program's half of a synchronised step: on a multicast the write to its
variables, on a delivery the write of the delivered set, on a broadcast instance's return the
recording of the returned value. -/

/-- The step relation of the gather program of process `j`. All transitions are
Dirac. -/
inductive ProgramStep (P : Parameters) (j : Fin P.n) :
    LocalState P.n (ProcessVariables P.n X) (Message P.n X) → GatherLabel P.n X →
      PMF (LocalState P.n (ProcessVariables P.n X) (Message P.n X)) → Prop
  /-- The call arrives: record the payload. -/
  | call (p) (x : X) (h : p.processVariables.input = none) :
      ProgramStep P j p (Sum.inl (Sum.inl (.call j x)))
        (PMF.pure (p.setProcessVariables { p.processVariables with input := some x }))
  /-- A call at another process is not `j`'s business. -/
  | callIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inl (Sum.inl (.call i x))) (PMF.pure p)
  /-- The call loop: the variables do not move. -/
  | callLoop (p) (x : X) :
      ProgramStep P j p (Sum.inl (Sum.inr (.callLoop j x))) (PMF.pure p)
  /-- A call loop at another process is not `j`'s business. -/
  | callLoopIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inl (Sum.inr (.callLoop i x))) (PMF.pure p)
  /-- `ECHO`: `j` is called (D8) and its accepted pairs number at least `n − f`, the
  source blueprint's `|AP| ≥ n − f`. The payload is those pairs, `T_i ← AP_i` of
  AFW25's Algorithm 5, line 9. -/
  | sendEcho (p) (hin : p.processVariables.input ≠ none)
      (hcard : P.n - P.f ≤ p.processVariables.accepted.card)
      (hsend : p.processVariables.sentEcho = none) :
      ProgramStep P j p (Sum.inr (.send j (.echo p.processVariables.accepted)))
        (PMF.pure (p.setProcessVariables
          { p.processVariables with sentEcho := some p.processVariables.accepted }))
  /-- `VOTE U`: `j` is called (D8), `n − f` senders' approved `ECHO` payloads, each
  contained in `U`, are delivered here, and `j` has multicast its own `ECHO`. The main thread
  of AFW25's Algorithm 5 sends `ECHO` before `VOTE`. -/
  | sendVote (p) (U : AcceptedPairs P.n X) (hin : p.processVariables.input ≠ none)
      (hech : p.processVariables.sentEcho ≠ none)
      (happ : approvedBy p.processVariables U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Message.echo A ∈ p.received q ∧ approvedBy p.processVariables A ∧ A ⊆ U)
      (hsend : p.processVariables.sentVote = none) :
      ProgramStep P j p (Sum.inr (.send j (.vote U)))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentVote := some U }))
  /-- A multicast by another process is not `j`'s business. -/
  | sendIdle (p) (i : Fin P.n) (m : Message P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.send i m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender it came from. -/
  | deliverReceive (p) (i : Fin P.n) (m : Message P.n X) :
      ProgramStep P j p (Sum.inr (.deliver j i m)) (PMF.pure (p.deliverTo i m))
  /-- A delivery to another process is not `j`'s business. -/
  | deliverIdle (p) (i k : Fin P.n) (m : Message P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.deliver i k m)) (PMF.pure p)
  /-- An input instance returns here: record the returned value. -/
  | inputBroadcastRetReceive (p) (k : Fin P.n) (v : X) :
      ProgramStep P j p (Sum.inr (.inputBroadcastRet k j v))
        (PMF.pure (p.setProcessVariables { p.processVariables with
          inputBroadcastReturned :=
            Function.update p.processVariables.inputBroadcastReturned k (some v) }))
  /-- An input instance's return to another process is not `j`'s business. -/
  | inputBroadcastRetIdle (p) (k i : Fin P.n) (v : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.inputBroadcastRet k i v)) (PMF.pure p)
  /-- `j` calls the instance broadcasting its input: the payload is the one its own variables
  hold, and they do not move. The instance's own guard decides whether the call lands.
  AFW25's Algorithm 5, line 6. -/
  | inputBroadcastCall (p) (x : X) (hin : p.processVariables.input = some x) :
      ProgramStep P j p (Sum.inr (.inputBroadcastCall j x)) (PMF.pure p)
  /-- Another process's input-broadcast call is not `j`'s business. -/
  | inputBroadcastCallIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.inputBroadcastCall i x)) (PMF.pure p)
  /-- `BIND U`: `j` is called (D8), `n − f` senders' approved `VOTE` payloads, each
  contained in `U`, are delivered here, `j` has multicast its own `VOTE`, and `j` has not
  called its own bind broadcast. The main thread of AFW25's Algorithm 5 sends
  `VOTE` before `BIND`, and sends `BIND` once, at line 17. The payload handed
  to the broadcast is written to its variables; the bind instance's own guard decides
  whether the call lands. -/
  | bindCall (p) (U : AcceptedPairs P.n X) (hin : p.processVariables.input ≠ none)
      (hvot : p.processVariables.sentVote ≠ none)
      (hsnd : p.processVariables.sentBind = none)
      (happ : approvedBy p.processVariables U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Message.vote W ∈ p.received q ∧ approvedBy p.processVariables W ∧ W ⊆ U) :
      ProgramStep P j p (Sum.inr (.bindCall j U))
        (PMF.pure (p.setProcessVariables { p.processVariables with sentBind := some U }))
  /-- Another process's bind call is not `j`'s business. -/
  | bindCallIdle (p) (i : Fin P.n) (U : AcceptedPairs P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.bindCall i U)) (PMF.pure p)
  /-- A bind instance returns here: record the returned value. -/
  | bindRetReceive (p) (q : Fin P.n) (U : AcceptedPairs P.n X) :
      ProgramStep P j p (Sum.inr (.bindRet q j U))
        (PMF.pure (p.setProcessVariables { p.processVariables with
          bindBroadcastReturned :=
            Function.update p.processVariables.bindBroadcastReturned q (some U) }))
  /-- A bind instance's return to another process is not `j`'s business. -/
  | bindRetIdle (p) (q i : Fin P.n) (U : AcceptedPairs P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inr (.bindRet q i U)) (PMF.pure p)
  /-- Return: `j` is called (D8), the output's entries are held here, `n − f` bind
  payloads held here are sub-maps of it, and `j` has called its own bind broadcast. The `BIND`
  broadcast of AFW25's Algorithm 5, line 17, precedes the wait of line 18. The
  core on the label is the network's. -/
  | ret (p) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X) (hin : p.processVariables.input ≠
      none)
      (hbind : p.processVariables.sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn p.processVariables k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBindBroadcastReturn p.processVariables q U ∧ AcceptedPairs.subMap U g)
      (hr : p.processVariables.returned = false) :
      ProgramStep P j p (Sum.inl (Sum.inl (.ret j g C)))
        (PMF.pure (p.setProcessVariables { p.processVariables with returned := true }))
  /-- A return at another process is not `j`'s business. -/
  | retIdle (p) (i : Fin P.n) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X) (hi : i ≠ j) :
      ProgramStep P j p (Sum.inl (Sum.inl (.ret i g C))) (PMF.pure p)
  /-- Corruption is the network's own write, and the programs' variables are
  corruption-blind (D1). -/
  | failIdle (p) (i : Fin P.n) :
      ProgramStep P j p (Sum.inl (Sum.inl (.fail i))) (PMF.pure p)

/-! ### The gather network

The one state of the gather that holds what no program may see: the
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
      NetworkStep P w (Sum.inr (.send j m)) (PMF.pure
        { w with network := w.network.recordSent j m })
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
  /-- An input-broadcast call sends nothing. -/
  | inputBroadcastCallIdle (w) (j : Fin P.n) (x : X) :
      NetworkStep P w (Sum.inr (.inputBroadcastCall j x)) (PMF.pure w)
  /-- A bind call sends nothing. -/
  | bindCallIdle (w) (j : Fin P.n) (U : AcceptedPairs P.n X) :
      NetworkStep P w (Sum.inr (.bindCall j U)) (PMF.pure w)
  /-- A bind instance's return sends nothing. -/
  | bindRetIdle (w) (q j : Fin P.n) (U : AcceptedPairs P.n X) :
      NetworkStep P w (Sum.inr (.bindRet q j U)) (PMF.pure w)
  /-- Return: the label carries the core, which this transition writes if it is
  unwritten. -/
  | ret (w) (id : Fin P.n) (g : Fin P.n → Option X) :
      NetworkStep P w (Sum.inl (Sum.inl (.ret id g (w.core.getD (coreOfNetwork P w.network)))))
        (PMF.pure { w with core := some (w.core.getD (coreOfNetwork P w.network)) })
  /-- Corruption (deviation D1). -/
  | fail (w) (i : Fin P.n) :
      NetworkStep P w (Sum.inl (Sum.inl (.fail i))) (PMF.pure { w with
        network :=
          w.network.corrupt P i })

/-! ### The gather programs and the gather network -/

/-- The gather program of process `j`. -/
noncomputable def gatherProgram (P : Parameters) (j : Fin P.n) :
    System (LocalState P.n (ProcessVariables P.n X) (Message P.n X)) (GatherLabel P.n X) where
  init := LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)
  step := ProgramStep P j

@[simp] theorem gatherProgram_init (P : Parameters) (j : Fin P.n) :
    (gatherProgram P j (X := X)).init = LocalState.initial P.n (Message P.n X)
      (ProcessVariables.initial P.n X)
      :=
  rfl

@[simp] theorem gatherProgram_step (P : Parameters) (j : Fin P.n)
    (p : LocalState P.n (ProcessVariables P.n X) (Message P.n X)) (l : GatherLabel P.n X)
    (ν : PMF (LocalState P.n (ProcessVariables P.n X) (Message P.n X))) :
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

/-- The gather programs beside the gather network. -/
noncomputable def gatherPrograms (P : Parameters) (X : Type) [DecidableEq X] :
    System
    ((∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X)) × NetworkState P.n X)
    (GatherLabel P.n X) :=
  (System.synchronisedProduct (gatherProgram P (X := X))).parallel (gatherNetwork P X)

end Transitions

end Gather
end ABA
end PLTS
