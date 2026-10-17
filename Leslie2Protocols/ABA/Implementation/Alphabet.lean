/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels
import Leslie2Protocols.ABA.Specifications.WCC
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.Relabel

/-!
# The extended alphabet

The shared alphabet `Label n` names what an observer of the protocol sees: the
ABA interface, the two sub-protocol interfaces with the announcement `boundG` of a round's bound
bit, and corruption. It cannot name a multicast, a delivery, a round-internal call or return, or a
corrupted process's sub-protocol call, because those are synchronised steps of components whose
boundary the observer does not see. The extended alphabet `ExtendedLabel n M E` adds them, and the
composition hides them again.

The alphabet is parametric in two types an implementation supplies: the graded-agreement message
type `M`, and the type `E` of the round's own calls and returns. Every constructor but the three
that carry one of them is independent of which graded-agreement implementation is being read, and so
is everything defined over the alphabet here: the hidden-label set, the labels a process acts on
(D23), the common coin's label pullback, and the lifted coin itself. An implementation fixes `M`
and `E` and inherits all of it.

Each label is output by one component. The program of process `j` outputs its
graded-agreement call and return, its round multicast and its round-internal calls and returns,
its coin call, its DECIDED send and relay, and its ABA return. The network outputs the deliveries,
`fail`, the announcement `boundG`, and a corrupted process's two sub-protocol calls
`byzantineCallG` and `byzantineCallW` (D11). The common coin outputs its return `retW`. A program
takes every other non-silent label as an input, and every program idles on `boundG`. A return to a
corrupted process is the output of the instance that computes it, on the instance's own return
label. A replaced program takes no transition on the labels of `actsAt j` and takes every other
non-silent label on a self-loop (D23).

The graded-agreement return `retG` carries `GBCAOutput`, the interface's grade,
which is the specification's own value type and is shared by every
implementation. It carries the returned value alone; the round's bound bit is announced by
`boundG` (D29).
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The synchronisation labels -/

/-- The labels the programs and the network synchronise on: the sends and the deliveries of the two
networks, the round-internal calls and returns, and a corrupted process's sub-protocol calls. The
round multicast and the round delivery carry a message of the graded-agreement implementation being
read. -/
inductive NetworkEvent (n : ℕ) (M E : Type) : Type
  /-- Round-`r` multicast: sender `j` writes its variables and the network sent sets
  `m` under `j`. -/
  | gbcaSend (r : ℕ) (j : Fin n) (m : M)
  /-- Round-`r` delivery: `m`, sent under sender `j`, reaches receiver `i`. -/
  | gbcaDeliver (r : ℕ) (i j : Fin n) (m : M)
  /-- DECIDED send: sender `j` sends `⟨DECIDED, b⟩` to all on the grade-2 outcome `grade2 b`
  of the round it has just closed. -/
  | decidedSend (j : Fin n) (b : Bool)
  /-- DECIDED relay: sender `j` sends `⟨DECIDED, b⟩` to all on an `f + 1` quorum. -/
  | decidedRelay (j : Fin n) (b : Bool)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | decidedDeliver (i j : Fin n) (b : Bool)
  /-- A round-internal call or return at process `j`: a step at the boundary between the round's
  program and one of its sub-protocol instances, which the shared alphabet does not name. The
  network takes part in it, writing the round's ghost, and it sends no message. -/
  | gbcaRoundEvent (r : ℕ) (j : Fin n) (e : E)
  /-- A corrupted process's graded-agreement call, output by the network under `k ∈ F` at a round
  a correct process has started; the round instance takes it on its call or its loop (D11,
  D37). -/
  | byzantineCallG (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process's coin call, output by the network under `k ∈ F` at a round a correct
  process has started; the common coin takes it on its call or its loop (D11, D37). -/
  | byzantineCallW (r : ℕ) (k : Fin n)
  deriving DecidableEq

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev ExtendedLabel (n : ℕ) (M E : Type) : Type := Label n ⊕ NetworkEvent n M E

/-- The synchronisation labels, hidden by the composition. -/
def networkEventLabels (n : ℕ) {M E : Type} : Set (ExtendedLabel n M E) :=
  {l | ∃ e : NetworkEvent n M E, l = Sum.inr e}

@[simp] theorem inl_notMem_networkEventLabels {n : ℕ} {M E : Type} (l : Label n) :
    Sum.inl l ∉ networkEventLabels (M := M) (E := E) n := by
  simp [networkEventLabels]

@[simp] theorem inr_mem_networkEventLabels {n : ℕ} {M E : Type} (e : NetworkEvent n M E) :
    Sum.inr e ∈ networkEventLabels (M := M) (E := E) n := ⟨e, rfl⟩

@[simp] theorem extendedLabel_tau (n : ℕ) (M E : Type) :
    (Silent.τ : ExtendedLabel n M E) = Sum.inl Label.tau := rfl

/-! ### The labels a process acts on

A corruption replaces the program of the process it names (D23). The replaced program takes no
transition on the outputs below and takes every other non-silent label on a self-loop: the
deliveries addressed to it, the coin's return, the Byzantine calls, the announcement `boundG` and
`fail`, which are its inputs, and its two other outputs, `decidedRelay j _` and `retABA j _`, at
either bit. -/

/-- The outputs of the program of process `j` on which a replaced program takes no transition: its
own graded-agreement call and return, its own round multicast, its own round-internal calls and
returns, its own coin call and its own DECIDED send. -/
def actsAt {n : ℕ} {M E : Type} (j : Fin n) : ExtendedLabel n M E → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _) => id = j
  | Sum.inl (.callW _ id) => id = j
  | Sum.inr (.gbcaSend _ k _) => k = j
  | Sum.inr (.gbcaRoundEvent _ k _) => k = j
  | Sum.inr (.decidedSend id _) => id = j
  | _ => False

instance {n : ℕ} {M E : Type} (j : Fin n) :
    DecidablePred (actsAt (M := M) (E := E) j) := fun l => by
  match l with
  | Sum.inl l => cases l <;> unfold actsAt <;> infer_instance
  | Sum.inr e => cases e <;> unfold actsAt <;> infer_instance

/-! ### The label pullback of the common coin -/

/-- The pullback along which the common coin is read over the extended
alphabet: a shared label is its own, a corrupted process's coin call is the coin's own call, and
every other network event leaves the coin idle. -/
def coinLabelMap (n : ℕ) {M E : Type} : ExtendedLabel n M E → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.byzantineCallW r k) => some (.callW r k)
  | Sum.inr _ => none

@[simp] theorem coinLabelMap_inl {n : ℕ} {M E : Type} (l : Label n) :
    coinLabelMap (M := M) (E := E) n (Sum.inl l) = some l := rfl

@[simp] theorem coinLabelMap_byzantineCallW {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineCallW r k)) = some (.callW r k) := rfl

@[simp] theorem coinLabelMap_gbcaSend {n : ℕ} {M E : Type} (r : ℕ) (j : Fin n) (m : M) :
    coinLabelMap (E := E) n (Sum.inr (.gbcaSend r j m)) = none := rfl

@[simp] theorem coinLabelMap_gbcaDeliver {n : ℕ} {M E : Type} (r : ℕ) (i j : Fin n) (m : M) :
    coinLabelMap (E := E) n (Sum.inr (.gbcaDeliver r i j m)) = none := rfl

@[simp] theorem coinLabelMap_decidedSend {n : ℕ} {M E : Type} (j : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.decidedSend j b)) = none := rfl

@[simp] theorem coinLabelMap_decidedRelay {n : ℕ} {M E : Type} (j : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.decidedRelay j b)) = none := rfl

@[simp] theorem coinLabelMap_decidedDeliver {n : ℕ} {M E : Type} (i j : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.decidedDeliver i j b)) = none := rfl

@[simp] theorem coinLabelMap_gbcaRoundEvent {n : ℕ} {M E : Type} (r : ℕ) (j : Fin n) (e : E) :
    coinLabelMap (M := M) n (Sum.inr (.gbcaRoundEvent r j e)) = none := rfl

@[simp] theorem coinLabelMap_byzantineCallG {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineCallG r k b)) = none := rfl

/-! ### The lifted common coin -/

/-- The common coin, read over the extended alphabet through the pullback. A
implementation fixes `M` and `E` and names the result `coinOverRoundAlphabet`. -/
noncomputable def coinOverExtendedAlphabet (P : Parameters) (M E : Type) :
    System (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
      (ExtendedLabel P.n M E) :=
  (WCC.specFamily P).mapIdle (coinLabelMap P.n)

@[simp] theorem coinOverExtendedAlphabet_init (P : Parameters) (M E : Type) :
    (coinOverExtendedAlphabet P M E).init = (WCC.specFamily P).init := rfl

/-! ### The common coin's idle transition over the shared alphabet -/

/-- The common coin idles on a shared label that is neither `τ`, nor a
call or return of one of its own rounds, nor `fail`. Read through the pullback
`coinLabelMap`, this is the coin's transition in every synchronised step — of a protocol
system, of its composed system, and of the protocol-shaped specification
(`ABA/Composition/Hybrid.lean`) — that leaves the coin unchanged. -/
theorem wccFamily_idle (P : Parameters)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {l : Label P.n}
    (hl : l ≠ Label.tau) (hr : Label.wccRound l = none) (hf : ¬ Label.isFail l) :
    (WCC.specFamily P).step o l (PMF.pure o) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

/-! ### The common coin's resolution -/

/-- An instance's resolution at a round `r` of the map is a silent transition of the common
coin's family, every other round unchanged. -/
theorem wccFamily_tau (P : Parameters)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {r : ℕ}
    (hr : r ∈ o.instanceMap.keys) {μw : PMF (WCC.SpecState P.n)}
    (h : WCC.Step P r (o r) Label.tau μw) :
    (WCC.specFamily P).step o Label.tau (μw.map (o.setInstanceState r)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inl ⟨rfl, r, hr, μw, h, rfl⟩

/-- An instance's resolution at a round `r` of the map is a silent transition of the common
coin read over the extended alphabet. -/
theorem coinOverExtendedAlphabet_tau (P : Parameters) (M E : Type)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {r : ℕ}
    (hr : r ∈ o.instanceMap.keys) {μw : PMF (WCC.SpecState P.n)}
    (h : WCC.Step P r (o r) Label.tau μw) :
    (coinOverExtendedAlphabet P M E).step o (Sum.inl Label.tau)
      (μw.map (o.setInstanceState r)) :=
  (System.mapIdle_step_some (coinLabelMap_inl Label.tau) _).mpr (wccFamily_tau P o hr h)

/-! ### Dirac successors

A Dirac distribution determines its point. -/

theorem pure_inj {α : Type} {a b : α}
    (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by
    rw [← h]; simp
  simpa using hm

end Implementation
end ABA
end PLTS
