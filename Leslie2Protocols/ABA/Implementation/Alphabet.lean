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
ABA interface, the two sub-protocol interfaces, and corruption. It cannot name
a multicast, a delivery, or a Byzantine handshake row, because those are joint steps of
components whose boundary the observer does not see. The extended alphabet
`ExtendedLabel n M` adds them, and the composition hides them again.

The alphabet is parametric in the graded-agreement message type `M`. Every
constructor but the two that carry a stage message is independent of which
graded-agreement implementation is being read, and so is everything defined
over the alphabet here: the hidden-label set, the labels a process acts on
(D23), the coin oracle's label pullback, and the lifted oracle itself. A
reading fixes `M` and inherits all of it.

The graded-agreement return `retG` carries `GBCAOutput`, the interface's grade,
which is the specification's own value type and is shared by every
implementation. It carries the round's bound bit beside it, and so does the
Byzantine return row `byzantineRetG`: both returns of a round announce the same
ghost output, whichever process they answer.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The rendezvous alphabet -/

/-- The rendezvous alphabet: the two networks, the Byzantine handshake rows, and the
handshake branches the shared alphabet does not distinguish. The stage
multicast and the stage delivery carry a message of the graded-agreement
implementation being read. -/
inductive NetworkEvent (n : ℕ) (M : Type) : Type
  /-- Stage-`r` multicast: sender `j` writes its record and the network sent sets
  `m` under `j`. -/
  | gbcaSend (r : ℕ) (j : Fin n) (m : M)
  /-- Stage-`r` delivery: `m`, sent under sender `j`, reaches receiver `i`. -/
  | gbcaDeliver (r : ℕ) (i j : Fin n) (m : M)
  /-- DECIDED relay: sender `j` publishes `⟨DECIDED, b⟩` on an `f + 1` quorum. -/
  | decidedSend (j : Fin n) (b : Bool)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | decidedDeliver (i j : Fin n) (b : Bool)
  /-- The coin return fused with a `⟨DECIDED, b⟩` publication (D10): the
  round-`r` coin `c` returns to `id`, whose grade was `A b`. -/
  | retWPublish (r : ℕ) (id : Fin n) (c : Bool) (b : Bool)
  /-- The graded-agreement call against an already-called stage record. -/
  | gbcaCallLoop (r : ℕ) (id : Fin n) (b : Bool)
  /-- A corrupted process takes the graded-agreement call, opening the stage
  record (D11). -/
  | byzantineCallG (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process takes the graded-agreement call against an
  already-called stage record (D11). -/
  | byzantineCallGLoop (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process takes a graded-agreement return (D11), the round's
  bound bit `bnd` announced beside the graded outcome. -/
  | byzantineRetG (r : ℕ) (k : Fin n) (out : GBCAOutput) (bnd : Bool)
  /-- A corrupted process takes the coin call (D11). -/
  | byzantineCallW (r : ℕ) (k : Fin n)
  /-- A corrupted process takes the coin return (D11). -/
  | byzantineRetW (r : ℕ) (k : Fin n) (b : Bool)
  deriving DecidableEq

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev ExtendedLabel (n : ℕ) (M : Type) : Type := Label n ⊕ NetworkEvent n M

/-- The rendezvous labels, hidden by the composition. -/
def networkEventLabels (n : ℕ) {M : Type} : Set (ExtendedLabel n M) :=
  {l | ∃ e : NetworkEvent n M, l = Sum.inr e}

@[simp] theorem inl_notMem_networkEventLabels {n : ℕ} {M : Type} (l : Label n) :
    Sum.inl l ∉ networkEventLabels (M := M) n := by
  simp [networkEventLabels]

@[simp] theorem inr_mem_networkEventLabels {n : ℕ} {M : Type} (e : NetworkEvent n M) :
    Sum.inr e ∈ networkEventLabels (M := M) n := ⟨e, rfl⟩

@[simp] theorem extendedLabel_tau (n : ℕ) (M : Type) :
    (Silent.τ : ExtendedLabel n M) = Sum.inl Label.tau := rfl

/-! ### The labels a process acts on

A corruption replaces the program of the process it names (D23). The replaced
program stands still on every label it can take at all, and it can take every
label except the ones below: those on which the process would act on its own
sub-protocol messages. Those messages are the business of the Byzantine handshake rows
(D11), which carry it with no row at the process they name. -/

/-- The labels on which process `j` acts on its own sub-protocol messages: its
own graded-agreement call and return, its own stage multicast, the stage and
DECIDED deliveries addressed to it, its own call against an already-called
stage record, its own fused coin return, and the graded-agreement rows that
name it. -/
def actsAt {n : ℕ} {M : Type} (j : Fin n) : ExtendedLabel n M → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _ _) => id = j
  | Sum.inr (.gbcaSend _ k _) => k = j
  | Sum.inr (.gbcaDeliver _ i _ _) => i = j
  | Sum.inr (.decidedDeliver i _ _) => i = j
  | Sum.inr (.gbcaCallLoop _ id _) => id = j
  | Sum.inr (.retWPublish _ id _ _) => id = j
  | Sum.inr (.byzantineCallG _ k _) => k = j
  | Sum.inr (.byzantineCallGLoop _ k _) => k = j
  | Sum.inr (.byzantineRetG _ k _ _) => k = j
  | _ => False

instance {n : ℕ} {M : Type} (j : Fin n) :
    DecidablePred (actsAt (M := M) j) := fun l => by
  match l with
  | Sum.inl l => cases l <;> unfold actsAt <;> infer_instance
  | Sum.inr e => cases e <;> unfold actsAt <;> infer_instance

/-! ### The label pullback of the coin oracle -/

/-- The pullback along which the coin oracle is read over the extended
alphabet: a shared label is its own, the Byzantine handshake rows and the
fused coin return are the oracle's own handshakes, and every other rendezvous
label leaves the oracle idle. -/
def coinLabelMap (n : ℕ) {M : Type} : ExtendedLabel n M → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.byzantineCallW r k) => some (.callW r k)
  | Sum.inr (.byzantineRetW r k b) => some (.retW r k b)
  | Sum.inr (.retWPublish r id c _) => some (.retW r id c)
  | Sum.inr _ => none

@[simp] theorem coinLabelMap_inl {n : ℕ} {M : Type} (l : Label n) :
    coinLabelMap (M := M) n (Sum.inl l) = some l := rfl

@[simp] theorem coinLabelMap_byzantineCallW {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) :
    coinLabelMap (M := M) n (Sum.inr (.byzantineCallW r k)) = some (.callW r k) := rfl

@[simp] theorem coinLabelMap_byzantineRetW {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.byzantineRetW r k b)) = some (.retW r k b) := rfl

@[simp] theorem coinLabelMap_retWPublish {n : ℕ} {M : Type} (r : ℕ) (id : Fin n) (c b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.retWPublish r id c b)) = some (.retW r id c) := rfl

@[simp] theorem coinLabelMap_gbcaSend {n : ℕ} {M : Type} (r : ℕ) (j : Fin n) (m : M) :
    coinLabelMap n (Sum.inr (.gbcaSend r j m)) = none := rfl

@[simp] theorem coinLabelMap_gbcaDeliver {n : ℕ} {M : Type} (r : ℕ) (i j : Fin n) (m : M) :
    coinLabelMap n (Sum.inr (.gbcaDeliver r i j m)) = none := rfl

@[simp] theorem coinLabelMap_decidedSend {n : ℕ} {M : Type} (j : Fin n) (b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.decidedSend j b)) = none := rfl

@[simp] theorem coinLabelMap_decidedDeliver {n : ℕ} {M : Type} (i j : Fin n) (b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.decidedDeliver i j b)) = none := rfl

@[simp] theorem coinLabelMap_gbcaCallLoop {n : ℕ} {M : Type} (r : ℕ) (id : Fin n) (b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.gbcaCallLoop r id b)) = none := rfl

@[simp] theorem coinLabelMap_byzantineCallG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.byzantineCallG r k b)) = none := rfl

@[simp] theorem coinLabelMap_byzantineCallGLoop {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    coinLabelMap (M := M) n (Sum.inr (.byzantineCallGLoop r k b)) = none := rfl

@[simp] theorem coinLabelMap_byzantineRetG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (out : GBCAOutput)
    (bnd : Bool) : coinLabelMap (M := M) n (Sum.inr (.byzantineRetG r k out bnd)) = none := rfl

/-! ### The lifted coin oracle -/

/-- The coin oracle, read over the extended alphabet through the pullback. A
reading fixes `M` and names the result `coinOverRoundAlphabet`. -/
noncomputable def coinOverExtendedAlphabet (P : Parameters) (M : Type) :
    System (ℕ → WCC.SpecState P.n) (ExtendedLabel P.n M) :=
  (WCC.specFamily P).mapIdle (coinLabelMap P.n)

@[simp] theorem coinOverExtendedAlphabet_init (P : Parameters) (M : Type) :
    (coinOverExtendedAlphabet P M).init = (WCC.specFamily P).init := rfl

/-! ### The coin oracle's idle row over the shared alphabet -/

/-- The coin oracle idles on a shared label that is neither `τ`, nor a
handshake of one of its own rounds, nor `fail`. Read through the pullback
`coinLabelMap`, this is the oracle's row in every joint transition — of a protocol
system, of its composed reading, and of the protocol-shaped specification
(`ABA/Composition/HybridAndSubstitution.lean`) — that leaves the coin standing still. -/
theorem wccFamily_idle (P : Parameters) (o : ℕ → WCC.SpecState P.n) {l : Label P.n}
    (hl : l ≠ Label.tau) (hr : Label.wccRound l = none) (hf : ¬ Label.isFail l) :
    (WCC.specFamily P).step o l (PMF.pure o) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

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
