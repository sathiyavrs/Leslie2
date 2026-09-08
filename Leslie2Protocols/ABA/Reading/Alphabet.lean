/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels
import Leslie2Protocols.ABA.Spec.WCC
import Leslie2Protocols.Framework.IdleFamily
import Leslie2Protocols.Framework.Relabel

/-!
# The extended alphabet

The shared alphabet `Lab n` names what an observer of the protocol sees: the
ABA interface, the two sub-protocol interfaces, and corruption. It cannot name
a multicast, a delivery, or a Byzantine drive, because those are joint steps of
components whose boundary the observer does not see. The extended alphabet
`NLab n M` adds them, and the composition hides them again.

The alphabet is parametric in the graded-agreement message type `M`. Every
constructor but the two that carry a stage message is independent of which
graded-agreement implementation is being read, and so is everything defined
over the alphabet here: the hidden-label set, the labels a process acts on
(D23), the coin oracle's label pullback, and the lifted oracle itself. A
reading fixes `M` and inherits all of it.

The graded-agreement return `retG` carries `GbcaOut`, the interface's grade,
which is the specification's own value type and is shared by every
implementation.
-/

namespace PLTS
namespace ABA
namespace Net

/-! ### The rendezvous alphabet -/

/-- The rendezvous alphabet: the two networks, the Byzantine drives, and the
handshake branches the shared alphabet does not distinguish. The stage
multicast and the stage delivery carry a message of the graded-agreement
implementation being read. -/
inductive NetEvtP (n : ℕ) (M : Type) : Type
  /-- Stage-`r` multicast: sender `j` writes its record and the network pools
  `m` under `j`. -/
  | gsnd (r : ℕ) (j : Fin n) (m : M)
  /-- Stage-`r` delivery: `m`, pooled under sender `j`, reaches receiver `i`. -/
  | gdlv (r : ℕ) (i j : Fin n) (m : M)
  /-- DECIDED relay: sender `j` publishes `⟨DECIDED, b⟩` on an `f + 1` quorum. -/
  | dsnd (j : Fin n) (b : Bool)
  /-- DECIDED delivery: sender `j`'s `⟨DECIDED, b⟩` reaches receiver `i`. -/
  | ddlv (i j : Fin n) (b : Bool)
  /-- The coin return fused with a `⟨DECIDED, b⟩` publication (D10): the
  round-`r` coin `c` returns to `id`, whose grade was `A b`. -/
  | retWPub (r : ℕ) (id : Fin n) (c : Bool) (b : Bool)
  /-- The graded-agreement call against an already-called stage record. -/
  | gcallLoop (r : ℕ) (id : Fin n) (b : Bool)
  /-- A corrupted process drives the graded-agreement call, opening the stage
  record (D11). -/
  | byzCallG (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process drives the graded-agreement call against an
  already-called stage record (D11). -/
  | byzCallGLoop (r : ℕ) (k : Fin n) (b : Bool)
  /-- A corrupted process takes a graded-agreement return (D11). -/
  | byzRetG (r : ℕ) (k : Fin n) (out : GbcaOut)
  /-- A corrupted process drives the coin call (D11). -/
  | byzCallW (r : ℕ) (k : Fin n)
  /-- A corrupted process takes the coin return (D11). -/
  | byzRetW (r : ℕ) (k : Fin n) (b : Bool)
  deriving DecidableEq

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev NLabP (n : ℕ) (M : Type) : Type := Lab n ⊕ NetEvtP n M

/-- The rendezvous labels, hidden by the composition. -/
def netEvtLabels (n : ℕ) {M : Type} : Set (NLabP n M) :=
  {l | ∃ e : NetEvtP n M, l = Sum.inr e}

@[simp] theorem inl_notMem_netEvtLabels {n : ℕ} {M : Type} (l : Lab n) :
    Sum.inl l ∉ netEvtLabels (M := M) n := by
  simp [netEvtLabels]

@[simp] theorem inr_mem_netEvtLabels {n : ℕ} {M : Type} (e : NetEvtP n M) :
    Sum.inr e ∈ netEvtLabels (M := M) n := ⟨e, rfl⟩

@[simp] theorem nlab_tau (n : ℕ) (M : Type) :
    (Silent.τ : NLabP n M) = Sum.inl Lab.tau := rfl

/-! ### The labels a process acts on

A corruption replaces the program of the process it names (D23). The replaced
program stands still on every label it can take at all, and it can take every
label except the ones below: those on which the process would act on its own
sub-protocol traffic. That traffic is the business of the Byzantine drives
(D11), which carry it with no row at the process they name. -/

/-- The labels on which process `j` acts on its own sub-protocol traffic: its
own graded-agreement call and return, its own stage multicast, the stage and
DECIDED deliveries addressed to it, its own call against an already-called
stage record, its own fused coin return, and the graded-agreement drives that
name it. -/
def actsAt {n : ℕ} {M : Type} (j : Fin n) : NLabP n M → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _) => id = j
  | Sum.inr (.gsnd _ k _) => k = j
  | Sum.inr (.gdlv _ i _ _) => i = j
  | Sum.inr (.ddlv i _ _) => i = j
  | Sum.inr (.gcallLoop _ id _) => id = j
  | Sum.inr (.retWPub _ id _ _) => id = j
  | Sum.inr (.byzCallG _ k _) => k = j
  | Sum.inr (.byzCallGLoop _ k _) => k = j
  | Sum.inr (.byzRetG _ k _) => k = j
  | _ => False

instance {n : ℕ} {M : Type} (j : Fin n) :
    DecidablePred (actsAt (M := M) j) := fun l => by
  match l with
  | Sum.inl l => cases l <;> unfold actsAt <;> infer_instance
  | Sum.inr e => cases e <;> unfold actsAt <;> infer_instance

/-! ### The label pullback of the coin oracle -/

/-- The pullback along which the coin oracle is read over the extended
alphabet: a shared label is its own, the Byzantine handshake drives and the
fused coin return are the oracle's own handshakes, and every other rendezvous
label leaves the oracle idle. -/
def wccPull (n : ℕ) {M : Type} : NLabP n M → Option (Lab n)
  | Sum.inl l => some l
  | Sum.inr (.byzCallW r k) => some (.callW r k)
  | Sum.inr (.byzRetW r k b) => some (.retW r k b)
  | Sum.inr (.retWPub r id c _) => some (.retW r id c)
  | Sum.inr _ => none

@[simp] theorem wccPull_inl {n : ℕ} {M : Type} (l : Lab n) :
    wccPull (M := M) n (Sum.inl l) = some l := rfl

@[simp] theorem wccPull_byzCallW {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) :
    wccPull (M := M) n (Sum.inr (.byzCallW r k)) = some (.callW r k) := rfl

@[simp] theorem wccPull_byzRetW {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    wccPull (M := M) n (Sum.inr (.byzRetW r k b)) = some (.retW r k b) := rfl

@[simp] theorem wccPull_retWPub {n : ℕ} {M : Type} (r : ℕ) (id : Fin n) (c b : Bool) :
    wccPull (M := M) n (Sum.inr (.retWPub r id c b)) = some (.retW r id c) := rfl

@[simp] theorem wccPull_gsnd {n : ℕ} {M : Type} (r : ℕ) (j : Fin n) (m : M) :
    wccPull n (Sum.inr (.gsnd r j m)) = none := rfl

@[simp] theorem wccPull_gdlv {n : ℕ} {M : Type} (r : ℕ) (i j : Fin n) (m : M) :
    wccPull n (Sum.inr (.gdlv r i j m)) = none := rfl

@[simp] theorem wccPull_dsnd {n : ℕ} {M : Type} (j : Fin n) (b : Bool) :
    wccPull (M := M) n (Sum.inr (.dsnd j b)) = none := rfl

@[simp] theorem wccPull_ddlv {n : ℕ} {M : Type} (i j : Fin n) (b : Bool) :
    wccPull (M := M) n (Sum.inr (.ddlv i j b)) = none := rfl

@[simp] theorem wccPull_gcallLoop {n : ℕ} {M : Type} (r : ℕ) (id : Fin n) (b : Bool) :
    wccPull (M := M) n (Sum.inr (.gcallLoop r id b)) = none := rfl

@[simp] theorem wccPull_byzCallG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    wccPull (M := M) n (Sum.inr (.byzCallG r k b)) = none := rfl

@[simp] theorem wccPull_byzCallGLoop {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (b : Bool) :
    wccPull (M := M) n (Sum.inr (.byzCallGLoop r k b)) = none := rfl

@[simp] theorem wccPull_byzRetG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) (out : GbcaOut) :
    wccPull (M := M) n (Sum.inr (.byzRetG r k out)) = none := rfl

/-! ### The lifted coin oracle -/

/-- The coin oracle, read over the extended alphabet through the pullback. A
reading fixes `M` and names the result `wccLift`. -/
noncomputable def wccLiftP (P : Params) (M : Type) :
    System (ℕ → WCC.SpecState P.n) (NLabP P.n M) :=
  (WCC.specFamily P).mapIdle (wccPull P.n)

@[simp] theorem wccLiftP_init (P : Params) (M : Type) :
    (wccLiftP P M).init = (WCC.specFamily P).init := rfl

/-! ### The coin oracle's idle row over the shared alphabet -/

/-- The coin oracle idles on a shared label that is neither `τ`, nor a
handshake of one of its own rounds, nor `fail`. Read through the pullback
`wccPull`, this is the oracle's row in every joint transition — of a protocol
system, of its composed reading, and of the protocol-shaped specification
(`ABA/ABDY/Hybrid.lean`) — that leaves the coin standing still. -/
theorem wccFamilyN_idle (P : Params) (o : ℕ → WCC.SpecState P.n) {l : Lab P.n}
    (hl : l ≠ Lab.tau) (hr : Lab.wccRound l = none) (hf : ¬ Lab.isFail l) :
    (WCC.specFamily P).step o l (PMF.pure o) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hl, hr, hf, rfl⟩))

/-! ### Dirac successors

A Dirac distribution determines its point. -/

theorem pureN_inj {α : Type} {a b : α}
    (h : (PMF.pure a : PMF α) = PMF.pure b) : a = b := by
  have hm : a ∈ (PMF.pure b).support := by rw [← h]; simp
  simpa using hm

end Net
end ABA
end PLTS
