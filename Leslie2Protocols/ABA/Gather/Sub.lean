/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Broadcast.Sub
import Leslie2Protocols.ABA.Gather.Vocabulary
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct
import Leslie2Protocols.Framework.IdleFamily

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

The composition is generic in the broadcast tier: `instAt` takes the `2n`
instances as arguments, `lowInst` supplies Bracha instances (`BRB.implInst`) and
`idealInst` supplies lifted broadcast specifications (`BRB.liftedSpec`).

## The alphabet

The specification's `call id x` carries two rows, the call and the
input-enabledness loop. The composition splits them across two labels, as the
reliable-broadcast composition does one level down (`ABA/Broadcast/Sub.lean`).
The gather record and the broadcast instance are different components, so a
single label carrying both rows would also carry the mixed pairs. The loop
therefore has a label of its own, `Extra.callLoop id x`, and the specification
is read along `specPull`, which sends that label to `call id x`. The interface
alphabet is `InstLab n X = Lab n X ⊕ Extra n X`.

The instance-internal alphabet is `GaLab n X = InstLab n X ⊕ GaEvt n X`. Its
five events are the gather multicast and delivery, the return of an input
instance, the call of a bind instance and the return of a bind instance. They
are hidden before anything outside sees the instance: `instAt` speaks
`InstLab n X`.

A broadcast instance joins the composition along a pullback — `inPull k` for
the instance broadcasting `k`'s input, `bindPull q` for the instance
broadcasting `q`'s `BIND` payload. The pullback names the instance: a label
carrying another instance's index has no image, and that instance stands still.
Corruption and the silent label have an image at every instance, so `fail` is a
broadcast across the whole composition.

## The stores

A gather program reads no neighbouring coordinate. What a broadcast instance has
returned to it is written on the return event into its own record: `delivIn k`
is the value instance `k` returned here, `delivBind q` is the payload bind
instance `q` returned here. The guards that today read `approved` or `apIn` read
these stores.

## The core

The core is a function of the gather network state alone
(`coreOf_networkState_only`), so the gather network holds it. `coreOfNet` reads
it off the network state, `coreOf_eq_coreOfNet` identifies the two readings, and
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
inductive Extra (n : ℕ) (X : Type) : Type
  /-- The input-enabledness loop of `call id x`. -/
  | callLoop (id : Fin n) (x : X)

/-- The instance's interface alphabet: the specification's alphabet with the
call loop beside it. -/
abbrev InstLab (n : ℕ) (X : Type) : Type := Lab n X ⊕ Extra n X

/-- The instance's own events: the gather multicast and delivery, the return of
an input instance, and the call and return of a bind instance. -/
inductive GaEvt (n : ℕ) (X : Type) : Type
  /-- Process `j` hands `m` to the gather network. -/
  | snd (j : Fin n) (m : GaMsg n X)
  /-- The gather network delivers `j`'s `m` to `i`. -/
  | dlv (i j : Fin n) (m : GaMsg n X)
  /-- The instance broadcasting `k`'s input returns `v` to `j`. -/
  | inRet (k j : Fin n) (v : X)
  /-- Process `j` calls the instance broadcasting its `BIND` payload `U`. -/
  | bindCall (j : Fin n) (U : APSet n X)
  /-- The instance broadcasting `q`'s `BIND` payload returns `U` to `j`. -/
  | bindRet (q j : Fin n) (U : APSet n X)

/-- The instance-internal alphabet: the interface alphabet plus the five
events. Its silent label is `Sum.inl (Sum.inl tau)`, so every `Sum.inr` label is
observable and hence hideable. -/
abbrev GaLab (n : ℕ) (X : Type) : Type := InstLab n X ⊕ GaEvt n X

/-- The event labels, hidden by the instance. -/
def gaEvents (n : ℕ) (X : Type) : Set (GaLab n X) := {l | ∃ e : GaEvt n X, l = Sum.inr e}

@[simp] theorem inl_notMem_gaEvents {n : ℕ} {X : Type} (l : InstLab n X) :
    Sum.inl l ∉ gaEvents n X := by
  simp [gaEvents]

@[simp] theorem inr_mem_gaEvents {n : ℕ} {X : Type} (e : GaEvt n X) :
    Sum.inr e ∈ gaEvents n X := ⟨e, rfl⟩

@[simp] theorem galab_tau (n : ℕ) (X : Type) :
    (Silent.τ : GaLab n X) = Sum.inl (Sum.inl Lab.tau) := rfl

@[simp] theorem instlab_tau (n : ℕ) (X : Type) :
    (Silent.τ : InstLab n X) = Sum.inl Lab.tau := rfl

/-- The silent label of a broadcast instance's interface alphabet. -/
@[simp] theorem brbInstLab_tau (n : ℕ) (M : Type) :
    (Silent.τ : BRB.InstLab n M) = Sum.inl BRB.Lab.tau := rfl

/-! ### The records -/

/-- The local record of one gather program: the gather record beside the stores
of what the broadcast instances have returned here. -/
structure ProcRec (n : ℕ) (X : Type) extends PRec n X where
  /-- `delivIn k` — the value the instance broadcasting `k`'s input returned
  here. -/
  delivIn : Fin n → Option X
  /-- `delivBind q` — the payload the instance broadcasting `q`'s `BIND`
  payload returned here. -/
  delivBind : Fin n → Option (APSet n X)

/-- The initial local record: nothing called, nothing sent, nothing returned
here. -/
def ProcRec.initial (n : ℕ) (X : Type) : ProcRec n X :=
  { PRec.initial n X with delivIn := fun _ => none, delivBind := fun _ => none }

/-- `p` holds the value `v` of the instance broadcasting `k`'s input. -/
def holdsIn {n : ℕ} {X : Type} (p : ProcRec n X) (k : Fin n) (v : X) : Prop :=
  p.delivIn k = some v

/-- `p` holds the payload `U` of the instance broadcasting `q`'s `BIND`
payload. -/
def holdsBind {n : ℕ} {X : Type} (p : ProcRec n X) (q : Fin n) (U : APSet n X) : Prop :=
  p.delivBind q = some U

/-- A payload set is approved by `p` when `p` holds every one of its pairs. -/
def approvedBy {n : ℕ} {X : Type} (p : ProcRec n X) (A : APSet n X) : Prop :=
  A.subMap p.delivIn

/-- The state of the gather network: the per-sender sent sets and the corrupted
set beside the instance's core. -/
structure GaNetState (n : ℕ) (X : Type) : Type where
  /-- The gather network state. -/
  net : NetworkState n (GaMsg n X)
  /-- The instance's core, written at the first return and carried on every
  return label. -/
  core : Option (APSet n X)

/-- The initial gather network state: nothing multicast, nobody corrupted, the
core unwritten. -/
def GaNetState.initial (n : ℕ) (X : Type) : GaNetState n X :=
  ⟨NetworkState.initial n (GaMsg n X), none⟩

/-- The core read off a network state. The local records are not consulted
(`coreOf_networkState_only`), so any record vector gives the same set. -/
noncomputable def coreOfNet {X : Type} (P : Params) (w : NetworkState P.n (GaMsg P.n X)) :
    APSet P.n X :=
  coreOf P ((fun _ => LocalState.initial P.n (GaMsg P.n X) (PRec.initial P.n X)), w)

/-- The core of an instance state is the core of its network state. -/
theorem coreOf_eq_coreOfNet {X : Type} (P : Params)
    (w : SubState P.n (PRec P.n X) (GaMsg P.n X)) :
    coreOf P w = coreOfNet P w.2 :=
  coreOf_networkState_only w _ rfl

/-! ### The pullbacks

A broadcast instance speaks its own interface alphabet `BRB.InstLab`. It joins
the composition along a pullback that names it: a label carrying another
instance's index has no image and leaves that instance idle. -/

/-- The pullback along which the instance broadcasting `k`'s input is read. -/
def inPull (n : ℕ) (X : Type) (k : Fin n) : GaLab n X → Option (BRB.InstLab n X)
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.call id x)) => if k = id then some (Sum.inl (.call x)) else none
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inl (Sum.inr (.callLoop id x)) => if k = id then some (Sum.inr (.callLoop x)) else none
  | Sum.inr (.inRet k' j v) => if k = k' then some (Sum.inl (.ret j v)) else none
  | _ => none

/-- The pullback along which the instance broadcasting `q`'s `BIND` payload is
read. -/
def bindPull (n : ℕ) (X : Type) (q : Fin n) : GaLab n X → Option (BRB.InstLab n (APSet n X))
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inr (.bindCall j U) => if q = j then some (Sum.inl (.call U)) else none
  | Sum.inr (.bindRet q' j U) => if q = q' then some (Sum.inl (.ret j U)) else none
  | _ => none

@[simp] theorem inPull_tau (n : ℕ) (X : Type) (k : Fin n) :
    inPull n X k (Silent.τ : GaLab n X) = some (Silent.τ : BRB.InstLab n X) := rfl

@[simp] theorem bindPull_tau (n : ℕ) (X : Type) (q : Fin n) :
    bindPull n X q (Silent.τ : GaLab n X) = some (Silent.τ : BRB.InstLab n (APSet n X)) := rfl

/-- Only the silent label of the composition reaches the silent label of an
input instance. -/
theorem inPull_eq_tau {n : ℕ} {X : Type} {k : Fin n} {l : GaLab n X}
    (h : inPull n X k l = some (Silent.τ : BRB.InstLab n X)) : l = Silent.τ := by
  rcases l with (l | e) | e
  · cases l <;> simp_all [inPull]
  · cases e; simp_all [inPull]
  · cases e <;> simp_all [inPull]

/-- Only the silent label of the composition reaches the silent label of a bind
instance. -/
theorem bindPull_eq_tau {n : ℕ} {X : Type} {q : Fin n} {l : GaLab n X}
    (h : bindPull n X q l = some (Silent.τ : BRB.InstLab n (APSet n X))) : l = Silent.τ := by
  rcases l with (l | e) | e
  · cases l <;> simp_all [bindPull]
  · cases e; simp_all [bindPull]
  · cases e <;> simp_all [bindPull]

section Rules

variable [DecidableEq X]

/-! ### The gather program

Process `j`'s program. Every guard reads its own record and its own delivered
sets. An event row carries the program's half of a joint step: on a multicast
the record write, on a delivery the write of the delivered set, on a broadcast
instance's return the write of the store. -/

/-- The step relation of the gather program of process `j`. All transitions are
Dirac. -/
inductive ProcStep (P : Params) (j : Fin P.n) :
    LocalState P.n (ProcRec P.n X) (GaMsg P.n X) → GaLab P.n X →
      PMF (LocalState P.n (ProcRec P.n X) (GaMsg P.n X)) → Prop
  /-- The call arrives: record the payload. -/
  | call (p) (x : X) (h : p.proc.input = none) :
      ProcStep P j p (Sum.inl (Sum.inl (.call j x)))
        (PMF.pure (p.setP { p.proc with input := some x }))
  /-- A call at another process is not `j`'s business. -/
  | callIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inl (Sum.inl (.call i x))) (PMF.pure p)
  /-- The call loop: the record does not move. -/
  | callLoop (p) (x : X) :
      ProcStep P j p (Sum.inl (Sum.inr (.callLoop j x))) (PMF.pure p)
  /-- A call loop at another process is not `j`'s business. -/
  | callLoopIdle (p) (i : Fin P.n) (x : X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inl (Sum.inr (.callLoop i x))) (PMF.pure p)
  /-- `ECHO A`: `j` is called, holds every pair of `A`, and `A` has at least
  `n − f` pairs. -/
  | sndEcho (p) (A : APSet P.n X) (hin : p.proc.input ≠ none)
      (happ : approvedBy p.proc A) (hcard : P.n - P.f ≤ A.card)
      (hsend : p.proc.sentEcho = none) :
      ProcStep P j p (Sum.inr (.snd j (.echo A)))
        (PMF.pure (p.setP { p.proc with sentEcho := some A }))
  /-- `VOTE U`: `n − f` senders' approved `ECHO` payloads, each contained in
  `U`, are delivered here. -/
  | sndVote (p) (U : APSet P.n X) (hin : p.proc.input ≠ none)
      (happ : approvedBy p.proc U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ p.recv q ∧ approvedBy p.proc A ∧ A ⊆ U)
      (hsend : p.proc.sentVote = none) :
      ProcStep P j p (Sum.inr (.snd j (.vote U)))
        (PMF.pure (p.setP { p.proc with sentVote := some U }))
  /-- A multicast by another process is not `j`'s business. -/
  | sndIdle (p) (i : Fin P.n) (m : GaMsg P.n X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inr (.snd i m)) (PMF.pure p)
  /-- Delivery, receiver's half: file the message under the sender's row. -/
  | dlvRecv (p) (i : Fin P.n) (m : GaMsg P.n X) :
      ProcStep P j p (Sum.inr (.dlv j i m)) (PMF.pure (p.deliverTo i m))
  /-- A delivery to another process is not `j`'s business. -/
  | dlvIdle (p) (i k : Fin P.n) (m : GaMsg P.n X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inr (.dlv i k m)) (PMF.pure p)
  /-- An input instance returns here: write the store. -/
  | inRetRecv (p) (k : Fin P.n) (v : X) :
      ProcStep P j p (Sum.inr (.inRet k j v))
        (PMF.pure (p.setP { p.proc with delivIn := Function.update p.proc.delivIn k (some v) }))
  /-- An input instance's return to another process is not `j`'s business. -/
  | inRetIdle (p) (k i : Fin P.n) (v : X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inr (.inRet k i v)) (PMF.pure p)
  /-- `BIND U`: `n − f` senders' approved `VOTE` payloads, each contained in
  `U`, are delivered here. The record does not move; the bind instance's own
  guard decides whether the call lands. -/
  | bindCall (p) (U : APSet P.n X) (hin : p.proc.input ≠ none)
      (happ : approvedBy p.proc U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ p.recv q ∧ approvedBy p.proc W ∧ W ⊆ U) :
      ProcStep P j p (Sum.inr (.bindCall j U)) (PMF.pure p)
  /-- Another process's bind call is not `j`'s business. -/
  | bindCallIdle (p) (i : Fin P.n) (U : APSet P.n X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inr (.bindCall i U)) (PMF.pure p)
  /-- A bind instance returns here: write the store. -/
  | bindRetRecv (p) (q : Fin P.n) (U : APSet P.n X) :
      ProcStep P j p (Sum.inr (.bindRet q j U))
        (PMF.pure (p.setP { p.proc with delivBind := Function.update p.proc.delivBind q (some U) }))
  /-- A bind instance's return to another process is not `j`'s business. -/
  | bindRetIdle (p) (q i : Fin P.n) (U : APSet P.n X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inr (.bindRet q i U)) (PMF.pure p)
  /-- Return: the output's entries are held here, and `n − f` bind payloads
  held here are sub-maps of it. The core on the label is the network's. -/
  | ret (p) (g : Fin P.n → Option X) (C : APSet P.n X) (hin : p.proc.input ≠ none)
      (hsub : ∀ k x, g k = some x → holdsIn p.proc k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBind p.proc q U ∧ APSet.subMap U g)
      (hr : p.proc.returned = false) :
      ProcStep P j p (Sum.inl (Sum.inl (.ret j g C)))
        (PMF.pure (p.setP { p.proc with returned := true }))
  /-- A return at another process is not `j`'s business. -/
  | retIdle (p) (i : Fin P.n) (g : Fin P.n → Option X) (C : APSet P.n X) (hi : i ≠ j) :
      ProcStep P j p (Sum.inl (Sum.inl (.ret i g C))) (PMF.pure p)
  /-- Corruption is the network's own write, and the local records are
  corruption-blind (D1). -/
  | failIdle (p) (i : Fin P.n) :
      ProcStep P j p (Sum.inl (Sum.inl (.fail i))) (PMF.pure p)

/-! ### The gather network

The one local state of the gather tier that holds what no program may see: the
per-sender sent sets, the corrupted set and the instance's core. It participates
in every gather multicast and delivery, it is where a corrupted sender's
injections enter (D5), and it writes the core at the first return. -/

/-- The step relation of the gather network. All transitions are Dirac. -/
inductive NetStep (P : Params) :
    GaNetState P.n X → GaLab P.n X → PMF (GaNetState P.n X) → Prop
  /-- A call sends nothing. -/
  | call (w) (id : Fin P.n) (x : X) :
      NetStep P w (Sum.inl (Sum.inl (.call id x))) (PMF.pure w)
  /-- A call loop sends nothing. -/
  | callLoop (w) (id : Fin P.n) (x : X) :
      NetStep P w (Sum.inl (Sum.inr (.callLoop id x))) (PMF.pure w)
  /-- The network's half of a multicast: record the message under its sender. -/
  | snd (w) (j : Fin P.n) (m : GaMsg P.n X) :
      NetStep P w (Sum.inr (.snd j m)) (PMF.pure { w with net := w.net.post j m })
  /-- The network's half of a delivery: the message must be sent under the
  named sender, and delivery does not consume it (D5). -/
  | dlv (w) (i j : Fin P.n) (m : GaMsg P.n X) (h : m ∈ w.net.sent j) :
      NetStep P w (Sum.inr (.dlv i j m)) (PMF.pure w)
  /-- Byzantine injection: a corrupted sender multicasts anything, at any time
  (D5). -/
  | byz (w) (j : Fin P.n) (m : GaMsg P.n X) (h : j ∈ w.net.F) :
      NetStep P w (Sum.inl (Sum.inl .tau)) (PMF.pure { w with net := w.net.post j m })
  /-- An input instance's return sends nothing. -/
  | inRetIdle (w) (k j : Fin P.n) (v : X) :
      NetStep P w (Sum.inr (.inRet k j v)) (PMF.pure w)
  /-- A bind call sends nothing. -/
  | bindCallIdle (w) (j : Fin P.n) (U : APSet P.n X) :
      NetStep P w (Sum.inr (.bindCall j U)) (PMF.pure w)
  /-- A bind instance's return sends nothing. -/
  | bindRetIdle (w) (q j : Fin P.n) (U : APSet P.n X) :
      NetStep P w (Sum.inr (.bindRet q j U)) (PMF.pure w)
  /-- Return: the label carries the core, which this row writes if it is
  unwritten. -/
  | ret (w) (id : Fin P.n) (g : Fin P.n → Option X) :
      NetStep P w (Sum.inl (Sum.inl (.ret id g (w.core.getD (coreOfNet P w.net)))))
        (PMF.pure { w with core := some (w.core.getD (coreOfNet P w.net)) })
  /-- Corruption (deviation D1). -/
  | fail (w) (i : Fin P.n) :
      NetStep P w (Sum.inl (Sum.inl (.fail i))) (PMF.pure { w with net := w.net.corrupt P i })

/-! ### The two tiers -/

/-- The gather program of process `j`. -/
noncomputable def gaProc (P : Params) (j : Fin P.n) :
    System (LocalState P.n (ProcRec P.n X) (GaMsg P.n X)) (GaLab P.n X) where
  init := LocalState.initial P.n (GaMsg P.n X) (ProcRec.initial P.n X)
  step := ProcStep P j

@[simp] theorem gaProc_init (P : Params) (j : Fin P.n) :
    (gaProc P j (X := X)).init = LocalState.initial P.n (GaMsg P.n X) (ProcRec.initial P.n X) :=
  rfl

@[simp] theorem gaProc_step (P : Params) (j : Fin P.n)
    (p : LocalState P.n (ProcRec P.n X) (GaMsg P.n X)) (l : GaLab P.n X)
    (ν : PMF (LocalState P.n (ProcRec P.n X) (GaMsg P.n X))) :
    (gaProc P j).step p l ν ↔ ProcStep P j p l ν := Iff.rfl

/-- The gather network. -/
noncomputable def gaNet (P : Params) (X : Type) [DecidableEq X] :
    System (GaNetState P.n X) (GaLab P.n X) where
  init := GaNetState.initial P.n X
  step := NetStep P

@[simp] theorem gaNet_init (P : Params) :
    (gaNet P X).init = GaNetState.initial P.n X := rfl

@[simp] theorem gaNet_step (P : Params) (w : GaNetState P.n X) (l : GaLab P.n X)
    (μ : PMF (GaNetState P.n X)) : (gaNet P X).step w l μ ↔ NetStep P w l μ := Iff.rfl

/-- The gather tier: the programs beside the gather network. -/
noncomputable def gaPart (P : Params) (X : Type) [DecidableEq X] :
    System ((∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X)) × GaNetState P.n X)
      (GaLab P.n X) :=
  (System.syncProduct (gaProc P (X := X))).parallel (gaNet P X)

/-- The state of the composition whose broadcast instances have state `B` for
the inputs and `B'` for the `BIND` payloads. -/
abbrev SubStateAt (n : ℕ) (X B B' : Type) : Type :=
  ((∀ _ : Fin n, LocalState n (ProcRec n X) (GaMsg n X)) × GaNetState n X) ×
    ((∀ _ : Fin n, B) × (∀ _ : Fin n, B'))

/-- The gather tier beside the broadcast tier, over the instance-internal
alphabet. -/
noncomputable def preAt (P : Params) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X))) :
    System (SubStateAt P.n X B B') (GaLab P.n X) :=
  (gaPart P X).parallel
    ((System.syncProduct (fun k => (BIn k).mapIdle (inPull P.n X k))).parallel
      (System.syncProduct (fun q => (BBind q).mapIdle (bindPull P.n X q))))

/-- **The gather instance** over the broadcast tier `BIn`, `BBind`: the two
tiers in parallel, the instance's events hidden, the result read back over the
interface alphabet. -/
noncomputable def instAt (P : Params) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X))) :
    System (SubStateAt P.n X B B') (InstLab P.n X) :=
  ((preAt P X BIn BBind).abstract (gaEvents P.n X)).relabel

/-- The state of the gather instance over Bracha's broadcast. -/
abbrev LowState (n : ℕ) (X : Type) : Type :=
  SubStateAt n X (BRB.ImplState n X) (BRB.ImplState n (APSet n X))

/-- The state of the gather instance over the broadcast specification. -/
abbrev IdealState (n : ℕ) (X : Type) : Type :=
  SubStateAt n X (BRB.SpecState n X) (BRB.SpecState n (APSet n X))

/-- **The gather instance over Bracha's broadcast.** -/
noncomputable def lowInst (P : Params) (X : Type) [DecidableEq X] :
    System (LowState P.n X) (InstLab P.n X) :=
  instAt P X (fun k => BRB.implInst P k X) (fun q => BRB.implInst P q (APSet P.n X))

/-- **The gather instance over the broadcast specification.** -/
noncomputable def idealInst (P : Params) (X : Type) [DecidableEq X] :
    System (IdealState P.n X) (InstLab P.n X) :=
  instAt P X (fun k => BRB.liftedSpec P k X) (fun q => BRB.liftedSpec P q (APSet P.n X))

@[simp] theorem instAt_init (P : Params) {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X))) :
    (instAt P X BIn BBind).init =
      (((fun _ => LocalState.initial P.n (GaMsg P.n X) (ProcRec.initial P.n X)),
        GaNetState.initial P.n X),
        ((fun k => (BIn k).init), (fun q => (BBind q).init))) := rfl

@[simp] theorem lowInst_init (P : Params) :
    (lowInst P X).init =
      (((fun _ => LocalState.initial P.n (GaMsg P.n X) (ProcRec.initial P.n X)),
        GaNetState.initial P.n X),
        ((fun _ => BRB.ImplState.initial P.n X),
          (fun _ => BRB.ImplState.initial P.n (APSet P.n X)))) := rfl

@[simp] theorem idealInst_init (P : Params) :
    (idealInst P X).init =
      (((fun _ => LocalState.initial P.n (GaMsg P.n X) (ProcRec.initial P.n X)),
        GaNetState.initial P.n X),
        ((fun _ => BRB.SpecState.initial P.n X),
          (fun _ => BRB.SpecState.initial P.n (APSet P.n X)))) := rfl

end Rules

/-! ### Views of the instance state

The four components of the instance state, and the four writes that reach one
of them. A row of either tier is stated through these, so that a guard reads
`ga s` where a flat reading reads the gather instance state. -/

section Views

variable {n : ℕ} {B B' : Type}

/-- The gather tier's instance state: the programs beside the gather network
state. -/
def ga (s : SubStateAt n X B B') : SubState n (ProcRec n X) (GaMsg n X) := (s.1.1, s.1.2.net)

/-- The input instances. -/
def brbIn (s : SubStateAt n X B B') : ∀ _ : Fin n, B := s.2.1

/-- The bind instances. -/
def brbBind (s : SubStateAt n X B B') : ∀ _ : Fin n, B' := s.2.2

/-- The instance's core. -/
def core (s : SubStateAt n X B B') : Option (APSet n X) := s.1.2.core

/-- Overwrite the gather tier's instance state. -/
def setGa (s : SubStateAt n X B B') (t : SubState n (ProcRec n X) (GaMsg n X)) :
    SubStateAt n X B B' := ((t.1, { s.1.2 with net := t.2 }), s.2)

/-- Overwrite the input instances. -/
def setBrbIn (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B) : SubStateAt n X B B' :=
  (s.1, (b, s.2.2))

/-- Overwrite the bind instances. -/
def setBrbBind (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B') : SubStateAt n X B B' :=
  (s.1, (s.2.1, b))

/-- Overwrite the core. -/
def setCore (s : SubStateAt n X B B') (c : Option (APSet n X)) : SubStateAt n X B B' :=
  ((s.1.1, { s.1.2 with core := c }), s.2)

@[simp] theorem ga_setGa (s : SubStateAt n X B B') (t : SubState n (ProcRec n X) (GaMsg n X)) :
    ga (setGa s t) = t := rfl
@[simp] theorem brbIn_setGa (s : SubStateAt n X B B') (t : SubState n (ProcRec n X) (GaMsg n X)) :
    brbIn (setGa s t) = brbIn s := rfl
@[simp] theorem brbBind_setGa (s : SubStateAt n X B B')
    (t : SubState n (ProcRec n X) (GaMsg n X)) : brbBind (setGa s t) = brbBind s := rfl
@[simp] theorem core_setGa (s : SubStateAt n X B B') (t : SubState n (ProcRec n X) (GaMsg n X)) :
    core (setGa s t) = core s := rfl

@[simp] theorem ga_setBrbIn (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B) :
    ga (setBrbIn s b) = ga s := rfl
@[simp] theorem brbIn_setBrbIn (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B) :
    brbIn (setBrbIn s b) = b := rfl
@[simp] theorem brbBind_setBrbIn (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B) :
    brbBind (setBrbIn s b) = brbBind s := rfl
@[simp] theorem core_setBrbIn (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B) :
    core (setBrbIn s b) = core s := rfl

@[simp] theorem ga_setBrbBind (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B') :
    ga (setBrbBind s b) = ga s := rfl
@[simp] theorem brbIn_setBrbBind (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B') :
    brbIn (setBrbBind s b) = brbIn s := rfl
@[simp] theorem brbBind_setBrbBind (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B') :
    brbBind (setBrbBind s b) = b := rfl
@[simp] theorem core_setBrbBind (s : SubStateAt n X B B') (b : ∀ _ : Fin n, B') :
    core (setBrbBind s b) = core s := rfl

@[simp] theorem ga_setCore (s : SubStateAt n X B B') (c : Option (APSet n X)) :
    ga (setCore s c) = ga s := rfl
@[simp] theorem brbIn_setCore (s : SubStateAt n X B B') (c : Option (APSet n X)) :
    brbIn (setCore s c) = brbIn s := rfl
@[simp] theorem brbBind_setCore (s : SubStateAt n X B B') (c : Option (APSet n X)) :
    brbBind (setCore s c) = brbBind s := rfl
@[simp] theorem core_setCore (s : SubStateAt n X B B') (c : Option (APSet n X)) :
    core (setCore s c) = c := rfl

/-- Corruption (deviation D1): the gather network state and every broadcast
coordinate corrupted in lockstep, the programs untouched. The two transforms
are the corruption of the tier's broadcast instances. -/
def corruptAll (P : Params) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : SubStateAt P.n X B B') : SubStateAt P.n X B B' :=
  ((s.1.1, { s.1.2 with net := s.1.2.net.corrupt P id }),
    (fun k => cIn (s.2.1 k), fun q => cBind (s.2.2 q)))

@[simp] theorem ga_corruptAll (P : Params) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : SubStateAt P.n X B B') :
    ga (corruptAll P id cIn cBind s) = SubState.corrupt P id (ga s) := rfl
@[simp] theorem brbIn_corruptAll (P : Params) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : SubStateAt P.n X B B') (k : Fin P.n) :
    brbIn (corruptAll P id cIn cBind s) k = cIn (brbIn s k) := rfl
@[simp] theorem brbBind_corruptAll (P : Params) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : SubStateAt P.n X B B') (q : Fin P.n) :
    brbBind (corruptAll P id cIn cBind s) q = cBind (brbBind s q) := rfl
@[simp] theorem core_corruptAll (P : Params) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : SubStateAt P.n X B B') : core (corruptAll P id cIn cBind s) = core s := rfl

end Views

/-- A payload set is approved at the ideal tier when every pair is a committed
entry of the input instance that carries it. -/
def approved {n : ℕ} (s : IdealState n X) (A : APSet n X) : Prop :=
  A.subMap (fun k => (brbIn s k).val)

section Determinacy

variable [DecidableEq X]

/-! ### Determinacy

Both rule tables written here are Dirac, so the composition is an LTS whenever
the broadcast tier is. -/

/-- Every gather program transition is Dirac. -/
theorem procStep_dirac {P : Params} {j : Fin P.n} {p : LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
    {l : GaLab P.n X} {ν : PMF (LocalState P.n (ProcRec P.n X) (GaMsg P.n X))}
    (h : ProcStep P j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every gather network transition is Dirac. -/
theorem netStep_dirac {P : Params} {w : GaNetState P.n X} {l : GaLab P.n X}
    {μ : PMF (GaNetState P.n X)} (h : NetStep P w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A gather program is an LTS. -/
theorem gaProc_isLTS (P : Params) (j : Fin P.n) : (gaProc P j (X := X)).IsLTS :=
  fun _ _ _ h => procStep_dirac h

/-- The gather network is an LTS. -/
theorem gaNet_isLTS (P : Params) : (gaNet P X).IsLTS := fun _ _ _ h => netStep_dirac h

/-- The synchronised group of gather programs is an LTS. -/
theorem syncGa_isLTS (P : Params) : (System.syncProduct (gaProc P (X := X))).IsLTS :=
  System.syncProduct_isLTS (gaProc_isLTS P)

/-- The gather tier is an LTS. -/
theorem gaPart_isLTS (P : Params) : (gaPart P X).IsLTS :=
  System.parallel_isLTS (syncGa_isLTS P) (gaNet_isLTS P)

/-- The two tiers in parallel form an LTS. -/
theorem preAt_isLTS (P : Params) {B B' : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X)}
    {BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X))}
    (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS) :
    (preAt P X BIn BBind).IsLTS :=
  System.parallel_isLTS (gaPart_isLTS P)
    (System.parallel_isLTS
      (System.syncProduct_isLTS (fun k => System.mapIdle_isLTS _ (hIn k)))
      (System.syncProduct_isLTS (fun q => System.mapIdle_isLTS _ (hBind q))))

/-- The gather instance is an LTS. -/
theorem instAt_isLTS (P : Params) {B B' : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X)}
    {BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X))}
    (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS) :
    (instAt P X BIn BBind).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (preAt_isLTS P hIn hBind) _)

/-- The gather instance over Bracha's broadcast is an LTS. -/
theorem lowInst_isLTS (P : Params) : (lowInst P X).IsLTS :=
  instAt_isLTS P (fun k => BRB.implInst_isLTS P k) (fun q => BRB.implInst_isLTS P q)

/-- The gather instance over the broadcast specification is an LTS. -/
theorem idealInst_isLTS (P : Params) : (idealInst P X).IsLTS :=
  instAt_isLTS P (fun k => BRB.liftedSpec_isLTS P k) (fun q => BRB.liftedSpec_isLTS P q)

/-- No gather program rule fires on `τ`: a program only ever moves in an event
or on one of the interface labels. The composition's silent transitions are
therefore the gather network's injections, the hidden events and the broadcast
tier's own silent steps. -/
theorem procStep_no_tau {P : Params} {j : Fin P.n}
    {p : LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
    {ν : PMF (LocalState P.n (ProcRec P.n X) (GaMsg P.n X))}
    (h : ProcStep P j p (Silent.τ : GaLab P.n X) ν) : False := by
  rw [galab_tau] at h; cases h

end Determinacy

/-! ### The specification read over the instance's interface

The specification speaks `Lab n X`; the instance speaks `InstLab n X`, in which
the call loop is a label of its own. `specPull` identifies the loop with the
specification label it stands for, so that the specification's own loop row
answers it. -/

/-- The projection of the interface alphabet onto the specification's
alphabet. -/
def specPull (n : ℕ) (X : Type) : InstLab n X → Option (Lab n X)
  | Sum.inl l => some l
  | Sum.inr (.callLoop id x) => some (.call id x)

@[simp] theorem specPull_inl {n : ℕ} (l : Lab n X) : specPull n X (Sum.inl l) = some l := rfl

@[simp] theorem specPull_callLoop {n : ℕ} (id : Fin n) (x : X) :
    specPull n X (Sum.inr (.callLoop id x)) = some (.call id x) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specPull_tau (n : ℕ) (X : Type) :
    specPull n X (Silent.τ : InstLab n X) = some (Silent.τ : Lab n X) := rfl

/-- Only the silent label projects to the silent label: the call loop projects
to the call. -/
theorem specPull_eq_tau {n : ℕ} {l : InstLab n X} (h : specPull n X l = some Lab.tau) :
    l = Sum.inl Lab.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e; simp at h

/-- Every interface label carries a specification label. -/
theorem specPull_isSome {n : ℕ} (l : InstLab n X) : ∃ l₀, specPull n X l = some l₀ := by
  cases l with
  | inl l₀ => exact ⟨l₀, rfl⟩
  | inr e => cases e; exact ⟨_, rfl⟩

/-- **The lifted specification**: the gather specification read over the
instance's interface. -/
noncomputable def liftedSpec (P : Params) (X : Type) [DecidableEq X] :
    System (SpecState P.n X) (InstLab P.n X) :=
  (specInst P X).mapIdle (specPull P.n X)

@[simp] theorem liftedSpec_init (P : Params) [DecidableEq X] :
    (liftedSpec P X).init = SpecState.initial P.n X := rfl

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem liftedSpec_isLTS (P : Params) [DecidableEq X] : (liftedSpec P X).IsLTS :=
  System.mapIdle_isLTS _ (specInst_isLTS P)

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `specPull`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the instance
actually took. -/

/-- The left injection: the interface label a specification label sits at. -/
def sect {n : ℕ} : Lab n X → InstLab n X := Sum.inl

open scoped Classical in
/-- The section of `specPull` that answers the interface label `l` over the
specification label `l₀`. -/
noncomputable def sectAt {n : ℕ} (l₀ : Lab n X) (l : InstLab n X) : Lab n X → InstLab n X :=
  fun x => if x = l₀ then l else sect x

@[simp] theorem specPull_sect {n : ℕ} (x : Lab n X) : specPull n X (sect x) = some x := rfl

/-- The left injection reflects the silent label. -/
theorem sect_eq_tau {n : ℕ} (x : Lab n X) :
    (sect x : InstLab n X) = (Silent.τ : InstLab n X) ↔ x = (Silent.τ : Lab n X) :=
  inl_eq_tau_iff x

theorem specPull_sectAt {n : ℕ} {l₀ : Lab n X} {l : InstLab n X}
    (hl : specPull n X l = some l₀) (x : Lab n X) : specPull n X (sectAt l₀ l x) = some x := by
  unfold sectAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specPull_sect]

theorem sectAt_tau {n : ℕ} {l₀ : Lab n X} {l : InstLab n X} (hl : specPull n X l = some l₀)
    (hl₀ : l₀ ≠ (Silent.τ : Lab n X)) (x : Lab n X) :
    sectAt l₀ l x = (Silent.τ : InstLab n X) ↔ x = (Silent.τ : Lab n X) := by
  unfold sectAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Lab n X) := by rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    exact sect_eq_tau x

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_liftedSpec [DecidableEq X] (P : Params) {s s' : SpecState P.n X}
    (h : (specInst P X).weakLSilent s s') : (liftedSpec P X).weakLSilent s s' :=
  System.weakLSilent_mapIdle sect (fun _ => rfl) (fun x => sect_eq_tau x) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_liftedSpec [DecidableEq X] (P : Params) {s s' : SpecState P.n X}
    {l₀ : Lab P.n X} {l : InstLab P.n X} (hl₀ : l₀ ≠ (Silent.τ : Lab P.n X))
    (hl : specPull P.n X l = some l₀) (h : (specInst P X).weakLStep s l₀ s') :
    (liftedSpec P X).weakLStep s l s' :=
  System.weakLStep_mapIdle (sectAt l₀ l) (specPull_sectAt hl) (sectAt_tau hl hl₀)
    (by simp [sectAt]) h

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (syncProduct, syncProduct,
syncProduct)`; the lemmas below unfold it once and for all, in both
directions. -/

/-- The instance's step relation, unfolded to the hidden-event case and the
interface-label case. -/
theorem instAt_step_iff (P : Params) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X)))
    (s : SubStateAt P.n X B B') (l : InstLab P.n X) (μ : PMF (SubStateAt P.n X B B')) :
    (instAt P X BIn BBind).step s l μ ↔
      (l = Sum.inl Lab.tau ∧ ∃ e : GaEvt P.n X, (preAt P X BIn BBind).step s (Sum.inr e) μ) ∨
      (preAt P X BIn BBind).step s (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_gaEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_gaEvents l, hstep⟩

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
theorem syncLift_inv (hA : ∀ k, (A k).IsLTS) (hL : L ≠ Silent.τ)
    (h : (System.syncProduct (fun k => (A k).mapIdle (φ k))).step a L μ) :
    ∃ a' : ∀ _ : Fin n, B, μ = PMF.pure a' ∧
      ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k)) := by
  rw [System.syncProduct_step] at h
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
theorem syncLift_pure (hL : L ≠ Silent.τ)
    (h : ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k))) :
    (System.syncProduct (fun k => (A k).mapIdle (φ k))).step a L (PMF.pure a') := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hL, fun k => PMF.pure (a' k), h, (piPMF_pure a').symm⟩

/-- On a label no pullback has an image at, the lifted family stands still. -/
theorem syncLift_none (hL : L ≠ Silent.τ) (hφ : ∀ k, φ k L = none) :
    (System.syncProduct (fun k => (A k).mapIdle (φ k))).step a L (PMF.pure a) :=
  syncLift_pure hL fun k => lift_idle (hφ k)

/-- A silent transition of the lifted family is a silent transition of exactly
one instance. -/
theorem syncLift_tau_inv [Silent Lbl] (hA : ∀ k, (A k).IsLTS)
    (hτ : ∀ k, φ k (Silent.τ : Λ) = some (Silent.τ : Lbl))
    (h : (System.syncProduct (fun k => (A k).mapIdle (φ k))).step a (Silent.τ : Λ) μ) :
    ∃ (k : Fin n) (c : B), μ = PMF.pure (Function.update a k c) ∧
      (A k).step (a k) (Silent.τ : Lbl) (PMF.pure c) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨hne, -⟩ | ⟨-, k, μ_k, hstep, rfl⟩
  · exact absurd rfl hne
  · rw [System.mapIdle_step_some (hτ k)] at hstep
    obtain ⟨c, rfl⟩ := hA k _ _ _ hstep
    exact ⟨k, c, by rw [piPMF_update_pure, PMF.pure_map], hstep⟩

/-- A silent transition of one instance is a silent transition of the lifted
family. -/
theorem syncLift_tau_step [Silent Lbl] {k : Fin n} {c : B}
    (hτ : φ k (Silent.τ : Λ) = some (Silent.τ : Lbl))
    (h : (A k).step (a k) (Silent.τ : Lbl) (PMF.pure c)) :
    (System.syncProduct (fun k => (A k).mapIdle (φ k))).step a (Silent.τ : Λ)
      (PMF.pure (Function.update a k c)) := by
  rw [System.syncProduct_step]
  refine Or.inr ⟨rfl, k, PMF.pure c, ?_, ?_⟩
  · rw [System.mapIdle_step_some hτ]; exact h
  · rw [piPMF_update_pure, PMF.pure_map]

end SyncLift

/-! ### The synchronised group of gather programs -/

section SyncGa

variable [DecidableEq X] {P : Params}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X)} {l : GaLab P.n X}

/-- A synchronised transition of the gather programs on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem syncGa_inv {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X))}
    (h : (System.syncProduct (gaProc P (X := X))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X),
      μ = PMF.pure x ∧ ∀ i, ProcStep P i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => procStep_dirac (hall i)
    choose y hy using hx
    refine ⟨y, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (y i) from funext hy]
      exact piPMF_pure y
    · rw [← hy i]; exact hall i
  · exact absurd hstep procStep_no_tau

/-- Build a synchronised transition of the gather programs from per-process
Dirac steps. -/
theorem syncGa_pure (hl : l ≠ Silent.τ) (h : ∀ i, ProcStep P i (u i) l (PMF.pure (x i))) :
    (System.syncProduct (gaProc P (X := X))).step u l (PMF.pure x) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The gather programs have no silent transition: no program has a `τ` row. -/
theorem syncGa_no_tau {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X))}
    (h : (System.syncProduct (gaProc P (X := X))).step u (Silent.τ : GaLab P.n X) μ) : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact procStep_no_tau hstep

end SyncGa

/-! ### The two tiers in parallel

A visible label moves all four factors — the programs, the gather network, the
input instances and the bind instances — and the joint distribution is their
Dirac product. A silent label moves exactly one of the gather network, one
input instance or one bind instance. -/

section PreAt

variable [DecidableEq X] {P : Params} {B B' : Type}
  {BIn : ∀ _ : Fin P.n, System B (BRB.InstLab P.n X)}
  {BBind : ∀ _ : Fin P.n, System B' (BRB.InstLab P.n (APSet P.n X))}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
  {w w' : GaNetState P.n X} {a a' : ∀ _ : Fin P.n, B} {b b' : ∀ _ : Fin P.n, B'}
  {L : GaLab P.n X}

/-- **The joint inversion.** A visible transition of the two tiers: every
factor steps on the label, and the joint distribution is their Dirac
product. -/
theorem preAt_joint_inv (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS)
    {μ : PMF (SubStateAt P.n X B B')} (hL : L ≠ (Silent.τ : GaLab P.n X))
    (h : (preAt P X BIn BBind).step ((u, w), (a, b)) L μ) :
    ∃ (x : ∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X)) (w' : GaNetState P.n X)
      (a' : ∀ _ : Fin P.n, B) (b' : ∀ _ : Fin P.n, B'),
      μ = PMF.pure ((x, w'), (a', b')) ∧
      (∀ i, ProcStep P i (u i) L (PMF.pure (x i))) ∧ NetStep P w L (PMF.pure w') ∧
      (∀ k, ((BIn k).mapIdle (inPull P.n X k)).step (a k) L (PMF.pure (a' k))) ∧
      (∀ q, ((BBind q).mapIdle (bindPull P.n X q)).step (b q) L (PMF.pure (b' q))) := by
  rw [preAt, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hga, hbr, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · rw [gaPart, System.parallel_step] at hga
    rcases hga with ⟨-, ν₁, ν₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨y, rfl, hall⟩ := syncGa_inv hs
      obtain ⟨v, rfl⟩ := netStep_dirac hn
      rw [System.parallel_step] at hbr
      rcases hbr with ⟨-, ρ₁, ρ₂, hi, hb, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · obtain ⟨c, rfl, hic⟩ := syncLift_inv hIn hL hi
        obtain ⟨d, rfl, hbd⟩ := syncLift_inv hBind hL hb
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
theorem preAt_tau_inv (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS)
    {μ : PMF (SubStateAt P.n X B B')}
    (h : (preAt P X BIn BBind).step ((u, w), (a, b)) (Silent.τ : GaLab P.n X) μ) :
    (∃ v, μ = PMF.pure ((u, v), (a, b)) ∧
      NetStep P w (Silent.τ : GaLab P.n X) (PMF.pure v)) ∨
    (∃ (k : Fin P.n) (c : B), μ = PMF.pure ((u, w), (Function.update a k c, b)) ∧
      (BIn k).step (a k) (Silent.τ : BRB.InstLab P.n X) (PMF.pure c)) ∨
    (∃ (q : Fin P.n) (d : B'), μ = PMF.pure ((u, w), (a, Function.update b q d)) ∧
      (BBind q).step (b q) (Silent.τ : BRB.InstLab P.n (APSet P.n X)) (PMF.pure d)) := by
  rw [preAt, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hga, rfl⟩ | ⟨-, μ₂, hbr, rfl⟩
  · exact absurd rfl hτ
  · rw [gaPart, System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ν₁, hs, rfl⟩ | ⟨-, ν₂, hn, rfl⟩
    · exact absurd rfl hτ
    · exact absurd hs syncGa_no_tau
    · obtain ⟨v, rfl⟩ := netStep_dirac hn
      exact Or.inl ⟨v, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hn⟩
  · rw [System.parallel_step] at hbr
    rcases hbr with ⟨hτ, -⟩ | ⟨-, ρ₁, hi, rfl⟩ | ⟨-, ρ₂, hb, rfl⟩
    · exact absurd rfl hτ
    · obtain ⟨k, c, rfl, hstep⟩ := syncLift_tau_inv hIn (fun k => inPull_tau P.n X k) hi
      exact Or.inr (Or.inl ⟨k, c, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩)
    · obtain ⟨q, d, rfl, hstep⟩ := syncLift_tau_inv hBind (fun q => bindPull_tau P.n X q) hb
      exact Or.inr (Or.inr ⟨q, d, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩)

/-- Build a visible transition of the two tiers from the four factors' Dirac
steps. -/
theorem preAt_lab_step (hL : L ≠ (Silent.τ : GaLab P.n X))
    (hproc : ∀ i, ProcStep P i (u i) L (PMF.pure (x i)))
    (hnet : NetStep P w L (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inPull P.n X k)).step (a k) L (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindPull P.n X q)).step (b q) L (PMF.pure (b' q))) :
    (preAt P X BIn BBind).step ((u, w), (a, b)) L (PMF.pure ((x, w'), (a', b'))) := by
  rw [preAt, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, w'), PMF.pure (a', b'), ?_, ?_,
    (prodPMF_pure_pure _ _).symm⟩
  · rw [gaPart, System.parallel_step]
    exact Or.inl ⟨hL, PMF.pure x, PMF.pure w', syncGa_pure hL hproc, hnet,
      (prodPMF_pure_pure _ _).symm⟩
  · rw [System.parallel_step]
    exact Or.inl ⟨hL, PMF.pure a', PMF.pure b', syncLift_pure hL hin, syncLift_pure hL hbind,
      (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the two tiers from an injection of the gather
network. -/
theorem preAt_tau_net (hn : NetStep P w (Silent.τ : GaLab P.n X) (PMF.pure w')) :
    (preAt P X BIn BBind).step ((u, w), (a, b)) (Silent.τ : GaLab P.n X)
      (PMF.pure ((u, w'), (a, b))) := by
  rw [preAt, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure (u, w'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [gaPart, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the two tiers from a silent step of one input
instance. -/
theorem preAt_tau_in {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstLab P.n X) (PMF.pure c)) :
    (preAt P X BIn BBind).step ((u, w), (a, b)) (Silent.τ : GaLab P.n X)
      (PMF.pure ((u, w), (Function.update a k c, b))) := by
  rw [preAt, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update a k c, b), ?_,
    (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure (Function.update a k c),
    syncLift_tau_step (inPull_tau P.n X k) h, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the two tiers from a silent step of one bind
instance. -/
theorem preAt_tau_bind {q : Fin P.n} {d : B'}
    (h : (BBind q).step (b q) (Silent.τ : BRB.InstLab P.n (APSet P.n X)) (PMF.pure d)) :
    (preAt P X BIn BBind).step ((u, w), (a, b)) (Silent.τ : GaLab P.n X)
      (PMF.pure ((u, w), (a, Function.update b q d))) := by
  rw [preAt, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (a, Function.update b q d), ?_,
    (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update b q d),
    syncLift_tau_step (bindPull_tau P.n X q) h, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the instance. -/
theorem instAt_event_step (e : GaEvt P.n X)
    (hproc : ∀ i, ProcStep P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hnet : NetStep P w (Sum.inr e) (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inPull P.n X k)).step (a k) (Sum.inr e) (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindPull P.n X q)).step (b q) (Sum.inr e)
      (PMF.pure (b' q))) :
    (instAt P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Lab.tau)
      (PMF.pure ((x, w'), (a', b'))) :=
  (instAt_step_iff P X BIn BBind _ _ _).mpr
    (Or.inl ⟨rfl, e, preAt_lab_step (by simp) hproc hnet hin hbind⟩)

/-- A visible interface label is a transition of the instance. -/
theorem instAt_lab_step {l : InstLab P.n X} (hl : l ≠ Sum.inl Lab.tau)
    (hproc : ∀ i, ProcStep P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hnet : NetStep P w (Sum.inl l) (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inPull P.n X k)).step (a k) (Sum.inl l) (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindPull P.n X q)).step (b q) (Sum.inl l)
      (PMF.pure (b' q))) :
    (instAt P X BIn BBind).step ((u, w), (a, b)) l (PMF.pure ((x, w'), (a', b'))) := by
  refine (instAt_step_iff P X BIn BBind _ _ _).mpr (Or.inr (preAt_lab_step ?_ hproc hnet hin hbind))
  rw [galab_tau]
  simpa using hl

/-- An injection of the gather network is a silent transition of the
instance. -/
theorem instAt_tau_net (hn : NetStep P w (Silent.τ : GaLab P.n X) (PMF.pure w')) :
    (instAt P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Lab.tau)
      (PMF.pure ((u, w'), (a, b))) :=
  (instAt_step_iff P X BIn BBind _ _ _).mpr (Or.inr (preAt_tau_net hn))

/-- A silent step of one input instance is a silent transition of the
instance. -/
theorem instAt_tau_in {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstLab P.n X) (PMF.pure c)) :
    (instAt P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Lab.tau)
      (PMF.pure ((u, w), (Function.update a k c, b))) :=
  (instAt_step_iff P X BIn BBind _ _ _).mpr (Or.inr (preAt_tau_in h))

/-- A silent step of one bind instance is a silent transition of the
instance. -/
theorem instAt_tau_bind {q : Fin P.n} {d : B'}
    (h : (BBind q).step (b q) (Silent.τ : BRB.InstLab P.n (APSet P.n X)) (PMF.pure d)) :
    (instAt P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Lab.tau)
      (PMF.pure ((u, w), (a, Function.update b q d))) :=
  (instAt_step_iff P X BIn BBind _ _ _).mpr (Or.inr (preAt_tau_bind h))

end PreAt

/-! ### The pullbacks, label by label -/

section PullRows

variable {n : ℕ} (X : Type) (k q id j q' k' i : Fin n)

@[simp] theorem inPull_call (x : X) :
    inPull n X k (Sum.inl (Sum.inl (.call id x))) =
      if k = id then some (Sum.inl (.call x)) else none := rfl
@[simp] theorem inPull_fail :
    inPull n X k (Sum.inl (Sum.inl (Lab.fail (X := X) id))) = some (Sum.inl (.fail id)) := rfl
@[simp] theorem inPull_ret (g : Fin n → Option X) (C : APSet n X) :
    inPull n X k (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem inPull_callLoop (x : X) :
    inPull n X k (Sum.inl (Sum.inr (.callLoop id x))) =
      if k = id then some (Sum.inr (.callLoop x)) else none := rfl
@[simp] theorem inPull_snd (m : GaMsg n X) :
    inPull n X k (Sum.inr (.snd j m)) = none := rfl
@[simp] theorem inPull_dlv (m : GaMsg n X) :
    inPull n X k (Sum.inr (.dlv i j m)) = none := rfl
@[simp] theorem inPull_inRet (v : X) :
    inPull n X k (Sum.inr (.inRet k' j v)) =
      if k = k' then some (Sum.inl (.ret j v)) else none := rfl
@[simp] theorem inPull_bindCall (U : APSet n X) :
    inPull n X k (Sum.inr (.bindCall j U)) = none := rfl
@[simp] theorem inPull_bindRet (U : APSet n X) :
    inPull n X k (Sum.inr (.bindRet q' j U)) = none := rfl

@[simp] theorem bindPull_call (x : X) :
    bindPull n X q (Sum.inl (Sum.inl (.call id x))) = none := rfl
@[simp] theorem bindPull_fail :
    bindPull n X q (Sum.inl (Sum.inl (Lab.fail (X := X) id))) = some (Sum.inl (.fail id)) := rfl
@[simp] theorem bindPull_ret (g : Fin n → Option X) (C : APSet n X) :
    bindPull n X q (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem bindPull_callLoop (x : X) :
    bindPull n X q (Sum.inl (Sum.inr (.callLoop id x))) = none := rfl
@[simp] theorem bindPull_snd (m : GaMsg n X) :
    bindPull n X q (Sum.inr (.snd j m)) = none := rfl
@[simp] theorem bindPull_dlv (m : GaMsg n X) :
    bindPull n X q (Sum.inr (.dlv i j m)) = none := rfl
@[simp] theorem bindPull_inRet (v : X) :
    bindPull n X q (Sum.inr (.inRet k' j v)) = none := rfl
@[simp] theorem bindPull_bindCall (U : APSet n X) :
    bindPull n X q (Sum.inr (.bindCall j U)) =
      if q = j then some (Sum.inl (.call U)) else none := rfl
@[simp] theorem bindPull_bindRet (U : APSet n X) :
    bindPull n X q (Sum.inr (.bindRet q' j U)) =
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

variable [DecidableEq X] {P : Params} {j : Fin P.n}
  {p : LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
  {ν : PMF (LocalState P.n (ProcRec P.n X) (GaMsg P.n X))}

theorem stepG_call_own {x : X} (h : ProcStep P j p (Sum.inl (Sum.inl (.call j x))) ν) :
    p.proc.input = none ∧ ν = PMF.pure (p.setP { p.proc with input := some x }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_call_foreign {i : Fin P.n} {x : X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inl (Sum.inl (.call i x))) ν) : ν = PMF.pure p := by
  cases h
  case call => exact absurd rfl hi
  case callIdle => rfl

theorem stepG_callLoop {i : Fin P.n} {x : X}
    (h : ProcStep P j p (Sum.inl (Sum.inr (.callLoop i x))) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl
  case callLoopIdle => rfl

theorem stepG_ret_own {g : Fin P.n → Option X} {C : APSet P.n X}
    (h : ProcStep P j p (Sum.inl (Sum.inl (.ret j g C))) ν) :
    p.proc.input ≠ none ∧ (∀ k x, g k = some x → holdsIn p.proc k x) ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBind p.proc q U ∧ APSet.subMap U g) ∧
      p.proc.returned = false ∧ ν = PMF.pure (p.setP { p.proc with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_ret_foreign {i : Fin P.n} {g : Fin P.n → Option X} {C : APSet P.n X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inl (Sum.inl (.ret i g C))) ν) : ν = PMF.pure p := by
  cases h
  case ret => exact absurd rfl hi
  case retIdle => rfl

theorem stepG_fail {i : Fin P.n} (h : ProcStep P j p (Sum.inl (Sum.inl (.fail i))) ν) :
    ν = PMF.pure p := by
  cases h
  case failIdle => rfl

theorem stepG_snd_echo_own {A : APSet P.n X}
    (h : ProcStep P j p (Sum.inr (.snd j (.echo A))) ν) :
    p.proc.input ≠ none ∧ approvedBy p.proc A ∧ P.n - P.f ≤ A.card ∧
      p.proc.sentEcho = none ∧ ν = PMF.pure (p.setP { p.proc with sentEcho := some A }) := by
  cases h
  case sndEcho => exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_vote_own {U : APSet P.n X}
    (h : ProcStep P j p (Sum.inr (.snd j (.vote U))) ν) :
    p.proc.input ≠ none ∧ approvedBy p.proc U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ p.recv q ∧ approvedBy p.proc A ∧ A ⊆ U) ∧
      p.proc.sentVote = none ∧ ν = PMF.pure (p.setP { p.proc with sentVote := some U }) := by
  cases h
  case sndVote => exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sndIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_snd_foreign {i : Fin P.n} {m : GaMsg P.n X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inr (.snd i m)) ν) : ν = PMF.pure p := by
  cases h
  case sndIdle => rfl
  all_goals exact absurd rfl hi

theorem stepG_dlv_own {k : Fin P.n} {m : GaMsg P.n X}
    (h : ProcStep P j p (Sum.inr (.dlv j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case dlvRecv => rfl
  case dlvIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_dlv_foreign {i k : Fin P.n} {m : GaMsg P.n X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inr (.dlv i k m)) ν) : ν = PMF.pure p := by
  cases h
  case dlvRecv => exact absurd rfl hi
  case dlvIdle => rfl

theorem stepG_inRet_own {k : Fin P.n} {v : X}
    (h : ProcStep P j p (Sum.inr (.inRet k j v)) ν) :
    ν = PMF.pure (p.setP { p.proc with delivIn := Function.update p.proc.delivIn k (some v) }) := by
  cases h
  case inRetRecv => rfl
  case inRetIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_inRet_foreign {k i : Fin P.n} {v : X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inr (.inRet k i v)) ν) : ν = PMF.pure p := by
  cases h
  case inRetRecv => exact absurd rfl hi
  case inRetIdle => rfl

theorem stepG_bindCall_own {U : APSet P.n X}
    (h : ProcStep P j p (Sum.inr (.bindCall j U)) ν) :
    p.proc.input ≠ none ∧ approvedBy p.proc U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ p.recv q ∧ approvedBy p.proc W ∧ W ⊆ U) ∧
      ν = PMF.pure p := by
  cases h
  case bindCall => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case bindCallIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_bindCall_foreign {i : Fin P.n} {U : APSet P.n X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inr (.bindCall i U)) ν) : ν = PMF.pure p := by
  cases h
  case bindCall => exact absurd rfl hi
  case bindCallIdle => rfl

theorem stepG_bindRet_own {q : Fin P.n} {U : APSet P.n X}
    (h : ProcStep P j p (Sum.inr (.bindRet q j U)) ν) :
    ν = PMF.pure
      (p.setP { p.proc with delivBind := Function.update p.proc.delivBind q (some U) }) := by
  cases h
  case bindRetRecv => rfl
  case bindRetIdle => exact absurd rfl ‹_ ≠ j›

theorem stepG_bindRet_foreign {q i : Fin P.n} {U : APSet P.n X} (hi : i ≠ j)
    (h : ProcStep P j p (Sum.inr (.bindRet q i U)) ν) : ν = PMF.pure p := by
  cases h
  case bindRetRecv => exact absurd rfl hi
  case bindRetIdle => rfl

end ProcInversion

/-! ### The gather network's rules, by label class -/

section NetInversion

variable [DecidableEq X] {P : Params} {w : GaNetState P.n X} {μ : PMF (GaNetState P.n X)}

theorem netStep_call {id : Fin P.n} {x : X}
    (h : NetStep P w (Sum.inl (Sum.inl (.call id x))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem netStep_callLoop {id : Fin P.n} {x : X}
    (h : NetStep P w (Sum.inl (Sum.inr (.callLoop id x))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem netStep_ret {id : Fin P.n} {g : Fin P.n → Option X} {C : APSet P.n X}
    (h : NetStep P w (Sum.inl (Sum.inl (.ret id g C))) μ) :
    C = w.core.getD (coreOfNet P w.net) ∧ μ = PMF.pure { w with core := some C } := by
  cases h; exact ⟨rfl, rfl⟩

theorem netStep_fail {i : Fin P.n} (h : NetStep P w (Sum.inl (Sum.inl (.fail i))) μ) :
    μ = PMF.pure { w with net := w.net.corrupt P i } := by
  cases h; rfl

theorem netStep_snd {j : Fin P.n} {m : GaMsg P.n X} (h : NetStep P w (Sum.inr (.snd j m)) μ) :
    μ = PMF.pure { w with net := w.net.post j m } := by
  cases h; rfl

theorem netStep_dlv {i j : Fin P.n} {m : GaMsg P.n X}
    (h : NetStep P w (Sum.inr (.dlv i j m)) μ) : m ∈ w.net.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_inRet {k j : Fin P.n} {v : X}
    (h : NetStep P w (Sum.inr (.inRet k j v)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem netStep_bindCall {j : Fin P.n} {U : APSet P.n X}
    (h : NetStep P w (Sum.inr (.bindCall j U)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem netStep_bindRet {q j : Fin P.n} {U : APSet P.n X}
    (h : NetStep P w (Sum.inr (.bindRet q j U)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem netStep_tau (h : NetStep P w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : GaMsg P.n X), j ∈ w.net.F ∧
      μ = PMF.pure { w with net := w.net.post j m } := by
  cases h
  case byz j m hF => exact ⟨j, m, hF, rfl⟩

end NetInversion

/-- A function pinned at `i` and unchanged elsewhere is the old one updated at
`i`. -/
theorem funPin {ι β : Type} [DecidableEq ι] {f g : ι → β} {i : ι} {y : β}
    (hi : g i = y) (hne : ∀ i', i' ≠ i → g i' = f i') : g = Function.update f i y := by
  funext i'
  by_cases h : i' = i
  · subst h; rw [hi, Function.update_self]
  · rw [hne i' h, Function.update_of_ne h]

/-! ### One state, four views

What a joint step delivers is a program function pinned pointwise — its value
at the acting process, and its agreement with the old one elsewhere — where a
row writes with `setGa` and `SubState.setProc`. The lemmas here close that
gap. -/

section Frame

variable [DecidableEq X] {P : Params} {B B' : Type}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
  {w : GaNetState P.n X} {a : ∀ _ : Fin P.n, B} {b : ∀ _ : Fin P.n, B'}

omit [DecidableEq X] in
/-- A program function pinned at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem procFun_update {j : Fin P.n} {r : LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
    (hj : x j = r) (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j r := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem procStep_update {j : Fin P.n} {r : LocalState P.n (ProcRec P.n X) (GaMsg P.n X)}
    {l : GaLab P.n X} (hj : ProcStep P j (u j) l (PMF.pure r))
    (hne : ∀ i, i ≠ j → ProcStep P i (u i) l (PMF.pure (u i))) :
    ∀ i, ProcStep P i (u i) l (PMF.pure (Function.update u j r i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

omit [DecidableEq X] in
/-- A record write at one program, with the network state untouched. -/
theorem sub_setProc {j : Fin P.n} {pr : ProcRec P.n X}
    (hj : x j = (u j).setP pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, w), (a, b)) : SubStateAt P.n X B B') =
      setGa ((u, w), (a, b)) (SubState.setProc (ga ((u, w), (a, b))) j pr) := by
  rw [procFun_update hj hne]; rfl

/-- A record write at one program together with the network state recording the
message that write multicasts. -/
theorem sub_setProc_post {j : Fin P.n} {pr : ProcRec P.n X} {m : GaMsg P.n X}
    (hj : x j = (u j).setP pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, { w with net := w.net.post j m }), (a, b)) : SubStateAt P.n X B B') =
      setGa ((u, w), (a, b)) ((SubState.setProc (ga ((u, w), (a, b))) j pr).mcast j m) := by
  rw [procFun_update hj hne]; rfl

omit [DecidableEq X] in
/-- The programs stand still and the network state is untouched. -/
theorem sub_idle (hall : ∀ i, x i = u i) :
    (((x, w), (a, b)) : SubStateAt P.n X B B') = ((u, w), (a, b)) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem sub_deliver {i k : Fin P.n} {m : GaMsg P.n X}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    (((x, w), (a, b)) : SubStateAt P.n X B B') =
      setGa ((u, w), (a, b)) (SubState.recvMsg (ga ((u, w), (a, b))) i k m) := by
  rw [procFun_update hi hne]; rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem sub_post {k : Fin P.n} {m : GaMsg P.n X} :
    (((u, { w with net := w.net.post k m }), (a, b)) : SubStateAt P.n X B B') =
      setGa ((u, w), (a, b)) (SubState.mcast (ga ((u, w), (a, b))) k m) := rfl

omit [DecidableEq X] in
/-- A return: the returner's flag and the instance's core. -/
theorem sub_ret {id : Fin P.n} {pr : ProcRec P.n X} {C : APSet P.n X}
    (hj : x id = (u id).setP pr) (hne : ∀ i, i ≠ id → x i = u i) :
    (((x, { w with core := some C }), (a, b)) : SubStateAt P.n X B B') =
      setCore (setGa ((u, w), (a, b)) (SubState.setProc (ga ((u, w), (a, b))) id pr))
        (some C) := by
  rw [procFun_update hj hne]; rfl

omit [DecidableEq X] in
/-- Corruption is the network state's own write beside the broadcast
coordinates' (D1). -/
theorem sub_corrupt {id : Fin P.n} {cIn : B → B} {cBind : B' → B'} (hall : ∀ i, x i = u i) :
    (((x, { w with net := w.net.corrupt P id }),
        ((fun k => cIn (a k)), fun q => cBind (b q))) : SubStateAt P.n X B B') =
      corruptAll P id cIn cBind ((u, w), (a, b)) := by
  rw [funext hall]; rfl

omit [DecidableEq X] in
/-- A write at one input instance. -/
theorem sub_setBrbIn {k : Fin P.n} {c : B} :
    (((u, w), (Function.update a k c, b)) : SubStateAt P.n X B B') =
      setBrbIn ((u, w), (a, b)) (Function.update (brbIn ((u, w), (a, b))) k c) := rfl

omit [DecidableEq X] in
/-- A write at one bind instance. -/
theorem sub_setBrbBind {q : Fin P.n} {d : B'} :
    (((u, w), (a, Function.update b q d)) : SubStateAt P.n X B B') =
      setBrbBind ((u, w), (a, b)) (Function.update (brbBind ((u, w), (a, b))) q d) := rfl

end Frame

end Gather
end ABA
end PLTS
