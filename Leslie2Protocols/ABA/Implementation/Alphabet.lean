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
a multicast, a delivery, or a Byzantine call or return transition, because those are synchronised
steps of
components whose boundary the observer does not see. The extended alphabet
`ExtendedLabel n M E` adds them, and the composition hides them again.

The alphabet is parametric in two types an implementation supplies: the graded-agreement message
type `M`, and the type `E` of the round's own calls and returns. Every constructor but the three
that carry one of them is independent of which graded-agreement implementation is being read, and so
is everything defined over the alphabet here: the hidden-label set, the labels a process acts on
(D23), the common coin's label pullback, and the lifted coin itself. An implementation fixes `M`
and `E` and inherits all of it.

The graded-agreement return `retG` carries `GBCAOutput`, the interface's grade,
which is the specification's own value type and is shared by every
implementation. It carries the round's bound bit beside it, and so does the
Byzantine return transition `byzantineRetG`: both returns of a round announce the same
ghost output, whichever process they answer.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The synchronisation labels -/

/-- The labels the programs and the network synchronise on: the two networks, the Byzantine call and
return transitions, and the call and return branches the shared alphabet does not distinguish. The
round multicast and the round delivery carry a message of the graded-agreement implementation being
read. -/
inductive NetworkEvent (n : ℕ) (M E : Type) : Type
  /-- Round-`r` multicast: sender `j` writes its variables and the network sent sets
  `m` under `j`. -/
  | gbcaSend (r : ℕ) (j : Fin n) (m : M)
  /-- Round-`r` delivery: `m`, sent under sender `j`, reaches receiver `i`. -/
  | gbcaDeliver (r : ℕ) (i j : Fin n) (m : M)
  /-- DECIDED relay: sender `j` publishes `⟨DECIDED, b⟩` on an `f + 1` quorum. -/
  | decidedSend (j : Fin n) (b : Bool)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | decidedDeliver (i j : Fin n) (b : Bool)
  /-- The coin return fused with a `⟨DECIDED, b⟩` publication (D10): the
  round-`r` coin `c` returns to `id`, whose outcome was `grade2 b`. -/
  | retWPublish (r : ℕ) (id : Fin n) (c : Bool) (b : Bool)
  /-- The graded-agreement call against a round already called. -/
  | gbcaCallLoop (r : ℕ) (id : Fin n) (b : Bool)
  /-- A round-internal call or return at process `j`: a step at the boundary between the round's
  program and one of its sub-protocol instances, which the shared alphabet does not name. The
  network takes part in it, writing the round's ghost, and it sends no message. -/
  | gbcaRoundEvent (r : ℕ) (j : Fin n) (e : E)
  /-- A corrupted process takes the graded-agreement call, opening the round's variables (D11). -/
  | byzantineCallG (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process takes the graded-agreement call against a round already called
  (D11). -/
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

A corruption replaces the program of the process it names (D23). The replaced
program is unchanged on every label it can take at all, and it can take every
label except the ones below: those on which the process would act on its own
sub-protocol messages. Those messages are the business of the Byzantine call and return
transitions (D11), which carry it with no transition at the process they name. -/

/-- The labels on which process `j` acts on its own sub-protocol messages: its own graded-agreement
call and return, its own round multicast, the round and DECIDED deliveries addressed to it, its own
call against a round already called, its own round-internal call or return, its own fused
coin return, and the graded-agreement transitions that name it. -/
def actsAt {n : ℕ} {M E : Type} (j : Fin n) : ExtendedLabel n M E → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _ _) => id = j
  | Sum.inr (.gbcaSend _ k _) => k = j
  | Sum.inr (.gbcaDeliver _ i _ _) => i = j
  | Sum.inr (.decidedDeliver i _ _) => i = j
  | Sum.inr (.gbcaCallLoop _ id _) => id = j
  | Sum.inr (.gbcaRoundEvent _ k _) => k = j
  | Sum.inr (.retWPublish _ id _ _) => id = j
  | Sum.inr (.byzantineCallG _ k _) => k = j
  | Sum.inr (.byzantineCallGLoop _ k _) => k = j
  | Sum.inr (.byzantineRetG _ k _ _) => k = j
  | _ => False

instance {n : ℕ} {M E : Type} (j : Fin n) :
    DecidablePred (actsAt (M := M) (E := E) j) := fun l => by
  match l with
  | Sum.inl l => cases l <;> unfold actsAt <;> infer_instance
  | Sum.inr e => cases e <;> unfold actsAt <;> infer_instance

/-! ### The label pullback of the common coin -/

/-- The pullback along which the common coin is read over the extended
alphabet: a shared label is its own, the Byzantine call and return transitions and the
fused coin return are the coin's own calls and returns, and every other network
event leaves the coin idle. -/
def coinLabelMap (n : ℕ) {M E : Type} : ExtendedLabel n M E → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.byzantineCallW r k) => some (.callW r k)
  | Sum.inr (.byzantineRetW r k b) => some (.retW r k b)
  | Sum.inr (.retWPublish r id c _) => some (.retW r id c)
  | Sum.inr _ => none

@[simp] theorem coinLabelMap_inl {n : ℕ} {M E : Type} (l : Label n) :
    coinLabelMap (M := M) (E := E) n (Sum.inl l) = some l := rfl

@[simp] theorem coinLabelMap_byzantineCallW {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineCallW r k)) = some (.callW r k) := rfl

@[simp] theorem coinLabelMap_byzantineRetW {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineRetW r k b)) = some (.retW r k b) := rfl

@[simp] theorem coinLabelMap_retWPublish {n : ℕ} {M E : Type} (r : ℕ) (id : Fin n) (c b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.retWPublish r id c b)) = some (.retW r id c) := rfl

@[simp] theorem coinLabelMap_gbcaSend {n : ℕ} {M E : Type} (r : ℕ) (j : Fin n) (m : M) :
    coinLabelMap (E := E) n (Sum.inr (.gbcaSend r j m)) = none := rfl

@[simp] theorem coinLabelMap_gbcaDeliver {n : ℕ} {M E : Type} (r : ℕ) (i j : Fin n) (m : M) :
    coinLabelMap (E := E) n (Sum.inr (.gbcaDeliver r i j m)) = none := rfl

@[simp] theorem coinLabelMap_decidedSend {n : ℕ} {M E : Type} (j : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.decidedSend j b)) = none := rfl

@[simp] theorem coinLabelMap_decidedDeliver {n : ℕ} {M E : Type} (i j : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.decidedDeliver i j b)) = none := rfl

@[simp] theorem coinLabelMap_gbcaCallLoop {n : ℕ} {M E : Type} (r : ℕ) (id : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.gbcaCallLoop r id b)) = none := rfl

@[simp] theorem coinLabelMap_gbcaRoundEvent {n : ℕ} {M E : Type} (r : ℕ) (j : Fin n) (e : E) :
    coinLabelMap (M := M) n (Sum.inr (.gbcaRoundEvent r j e)) = none := rfl

@[simp] theorem coinLabelMap_byzantineCallG {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineCallG r k b)) = none := rfl

@[simp] theorem coinLabelMap_byzantineCallGLoop {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n)
    (b : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineCallGLoop r k b)) = none := rfl

@[simp] theorem coinLabelMap_byzantineRetG {n : ℕ} {M E : Type} (r : ℕ) (k : Fin n)
    (out : GBCAOutput) (bnd : Bool) :
    coinLabelMap (M := M) (E := E) n (Sum.inr (.byzantineRetG r k out bnd)) = none := rfl

/-! ### The lifted common coin -/

/-- The common coin, read over the extended alphabet through the pullback. A
implementation fixes `M` and `E` and names the result `coinOverRoundAlphabet`. -/
noncomputable def coinOverExtendedAlphabet (P : Parameters) (M E : Type) :
    System (ℕ → WCC.SpecState P.n) (ExtendedLabel P.n M E) :=
  (WCC.specFamily P).mapIdle (coinLabelMap P.n)

@[simp] theorem coinOverExtendedAlphabet_init (P : Parameters) (M E : Type) :
    (coinOverExtendedAlphabet P M E).init = (WCC.specFamily P).init := rfl

/-! ### The common coin's idle transition over the shared alphabet -/

/-- The common coin idles on a shared label that is neither `τ`, nor a
call or return of one of its own rounds, nor `fail`. Read through the pullback
`coinLabelMap`, this is the coin's transition in every synchronised step — of a protocol
system, of its composed system, and of the protocol-shaped specification
(`ABA/Composition/Hybrid.lean`) — that leaves the coin unchanged. -/
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
