/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.ProcessAndNetworkState
import Leslie2.Systems.LTS

/-!
# The gather specification (blueprint Transition System 4, repaired: D26)

The specification of one gather instance over an arbitrary payload type `X`,
on its own alphabet `Gather.Label n X`. Processes call with a payload and may
return a partial map `g : Fin n → Option X`. Safety only: Termination is out
of scope.

## The state

* `call` — the environment's call records, one entry per process.
* `val` — the committed entries: the one value each process's contribution
  can ever deliver. Each entry is written at most once, by the internal
  transition `commit`, whose guard `k ∈ F ∨ call k = some v` says a corrupted
  process contributes anything and a correct one only its call. This is the
  same split of the source's call field that the BRB specification makes
  (`ABA/ReliableBroadcast/Specification.lean`), one level up: entries are sent by reliable
  broadcast, so a process corrupted after a correct call can still direct its committed
  entry until first use, and a specification that fixed the entry at call
  time would refuse that execution. The source's Byzantine-call τ-rule is the
  corrupted half of `commit` (deviation D26).
* `core` — the binding content: one payload set, written at most once, by
  the internal transition `bindCore`. Its entries are committed entries, it
  has at least `n − f` of them, and every return carries it.
* `ret`, `F` — the return flags and the corrupted set.

Agreement and Validity are linear. Two returns agree wherever both are
defined, both being sub-maps of the write-once `val`; a never-corrupted
process's entry is its genuine call, by `commit`'s guard.

## The core

The instance binds one payload set: the `core`, written before the first
return by `bindCore`, of at least `n − f` committed entries, and carried by
every return.

The core is a ghost output. No process holds it; the set a return hands out
is specification state. The return label carries it — `ret id g C` names the
returner, the map it is handed and the core — so the binding content is
read off a trace rather than off a state, and a system that embeds this
instance binds by reading its labels.

Two guards of `bindCore` are what a return then delivers: `hval` makes the
core's entries committed entries, `hcard` gives it at least `n − f` of them.
Both are discharged at the core write, from the prefix alone. `Gather/CommonCoreCounting.lean`
carries the argument for the gather implementation: the core is the `ECHO`
payload of a sender whose payload lies below every `VOTE` of `n − f − |F|`
processes outside `F`, and the size bound is that payload's own.

Every transition is Dirac, so the instance is an LTS. `fail` is the
determinised D1 corruption.
-/

namespace PLTS
namespace ABA
namespace Gather

/-- A payload set: finitely many `(process, value)` pairs. -/
abbrev AcceptedPairs (n : ℕ) (X : Type) : Type := Finset (Fin n × X)

/-- The entries of `U` are entries of the partial map `h`. -/
def AcceptedPairs.subMap {n : ℕ} {X : Type} (U : AcceptedPairs n X) (h : Fin n → Option X) : Prop :=
  ∀ p ∈ U, h p.1 = some p.2

/-- `subMap` is monotone in the payload set. -/
theorem AcceptedPairs.subMap_mono {n : ℕ} {X : Type} {U V : AcceptedPairs n X}
    {h : Fin n → Option X} (hUV : U ⊆ V) (hV : V.subMap h) : U.subMap h :=
  fun p hp => hV p (hUV hp)

/-- The alphabet of one gather instance over payload type `X`. -/
inductive Label (n : ℕ) (X : Type) : Type
  /-- The silent label. -/
  | tau
  /-- The environment calls process `id` with payload `x`. -/
  | call (id : Fin n) (x : X)
  /-- Process `id` returns the partial map `g`, and the instance's core is
  `C`. -/
  | ret (id : Fin n) (g : Fin n → Option X) (C : AcceptedPairs n X)
  /-- Corruption of process `id`. -/
  | fail (id : Fin n)

instance {n : ℕ} {X : Type} : Silent (Label n X) := ⟨Label.tau⟩

@[simp] theorem Label.silent_eq {n : ℕ} {X : Type} :
    (Silent.τ : Label n X) = Label.tau := rfl

/-- The state of one gather specification instance. -/
structure SpecState (n : ℕ) (X : Type) : Type where
  /-- The environment's call records. -/
  call : Fin n → Option X
  /-- The committed entries: what each process's contribution delivers.
  Each entry is written at most once, by `commit`. -/
  val : Fin n → Option X
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The core: every return carries it. Written at most once, by
  `bindCore`. -/
  core : Option (AcceptedPairs n X)
  /-- The corrupted set (local copy, kept equal by `fail` broadcast). -/
  F : Finset (Fin n)

namespace SpecState

variable {n : ℕ} {X : Type}

/-- The initial gather instance state. -/
def initial (n : ℕ) (X : Type) : SpecState n X where
  call := fun _ => none
  val := fun _ => none
  ret := fun _ => false
  core := none
  F := ∅

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : SpecState P.n X) : SpecState P.n X :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-! ### Corruption frame lemmas -/

variable {X : Type}

@[simp] theorem corrupt_call (P : Parameters) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).call = s.call := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_val (P : Parameters) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).val = s.val := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret (P : Parameters) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_core (P : Parameters) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).core = s.core := by
  unfold SpecState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. Not a simp lemma: it introduces an
`ite`. -/
theorem SpecState.corrupt_F (P : Parameters) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold SpecState.corrupt
  split_ifs <;> rfl

/-- The step relation of the gather specification instance (blueprint
Transition System 4, with the committed entries in place of the source's
call-borne values). -/
inductive Step (P : Parameters) [DecidableEq X] :
    SpecState P.n X → Label P.n X → PMF (SpecState P.n X) → Prop
  /-- A process inputs its payload. -/
  | call (s : SpecState P.n X) (id : Fin P.n) (x : X) (h : s.call id = none) :
      Step P s (.call id x)
        (PMF.pure { s with call := Function.update s.call id (some x) })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n X) (id : Fin P.n) (x : X) :
      Step P s (.call id x) (PMF.pure s)
  /-- Process `k`'s contribution commits: anything if `k` is corrupted, its
  call otherwise. Each entry is written at most once. -/
  | commit (s : SpecState P.n X) (k : Fin P.n) (v : X)
      (hv : s.val k = none) (hm : k ∈ s.F ∨ s.call k = some v) :
      Step P s .tau (PMF.pure { s with val := Function.update s.val k (some v) })
  /-- Binding: write the core. Its entries are committed entries and it has
  at least `n − f` of them. Fires at most once per instance. -/
  | bindCore (s : SpecState P.n X) (S : AcceptedPairs P.n X)
      (h0 : s.core = none)
      (hval : AcceptedPairs.subMap S s.val)
      (hcard : P.n - P.f ≤ S.card) :
      Step P s .tau (PMF.pure { s with core := some S })
  /-- A process returns a sub-map of the committed entries containing the
  core, which the label carries. -/
  | ret (s : SpecState P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (C : AcceptedPairs P.n X) (hC : s.core = some C)
      (hmem : AcceptedPairs.subMap C g)
      (hsub : ∀ k x, g k = some x → s.val k = some x)
      (hr : s.ret id = false) :
      Step P s (.ret id g C)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n X) (id : Fin P.n) :
      Step P s (.fail id) (PMF.pure (s.corrupt P id))

variable [DecidableEq X]

/-- The gather specification instance. -/
noncomputable def specInst (P : Parameters) (X : Type) [DecidableEq X] :
    System (SpecState P.n X) (Label P.n X) where
  init := SpecState.initial P.n X
  step := Step P

@[simp] theorem specInst_init (P : Parameters) :
    (specInst P X).init = SpecState.initial P.n X := rfl

@[simp] theorem specInst_step (P : Parameters) (s : SpecState P.n X)
    (l : Label P.n X) (μ : PMF (SpecState P.n X)) :
    (specInst P X).step s l μ ↔ Step P s l μ := Iff.rfl

/-- Every gather spec transition is Dirac: the instance is an LTS. -/
theorem specInst_isLTS (P : Parameters) : (specInst P X).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end Gather
end ABA
end PLTS
