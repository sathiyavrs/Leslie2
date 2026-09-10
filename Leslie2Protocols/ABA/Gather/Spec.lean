/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.MsgState
import Leslie2.Systems.LTS

/-!
# The gather specification (blueprint Transition System 4, repaired: D25, D26)

The specification of one gather instance over an arbitrary payload type `X`,
on its own alphabet `Gather.Lab n X`. Processes call with a payload and may
return a partial map `g : Fin n → Option X`. Safety only: Termination is out
of scope.

## The state

* `call` — the environment's call records, one entry per process.
* `val` — the committed entries: the one value each process's contribution
  can ever deliver. Each entry is written at most once, by the internal
  transition `commit`, whose guard `k ∈ F ∨ call k = some v` says a corrupted
  process contributes anything and an honest one only its call. This is the
  same split of the source's call field that the BRB specification makes
  (`ABA/Broadcast/Spec.lean`), one level up: entries travel by reliable broadcast,
  so a process corrupted after an honest call can still direct its committed
  entry until first use, and a specification that pinned the entry at call
  time would refuse that execution. The source's Byzantine-call τ-rule is the
  corrupted half of `commit` (deviation D26).
* `cores` — the binding content: a family of payload sets, written at most
  once, by the internal transition `bindCores`. Every member's entries are
  committed entries, any two members share at least `n − f` entries, and
  every return must contain some member.
* `ret`, `F` — the return flags and the corrupted set.

Agreement and Validity are linear. Two returns agree wherever both are
defined, both being sub-maps of the write-once `val`; a never-corrupted
process's entry is its genuine call, by `commit`'s guard.

## The core family (repair of the source's single bound core, deviation D25)

The source's TS 4 binds a *single* core set: one `S` of size at least
`n − f`, fixed before the first return, contained in every return. The
implementations this specification abstracts (the ECHO/VOTE/BIND rounds
of the source's Algorithm 4) do satisfy that property, but its proof
identifies the core only in hindsight: the core is the intersection of
`f + 1` fixed payloads, and the bound `n − f` on that intersection is
witnessed by the common core of a *completed* execution — at the moment the
first process returns, only `n − 2f` honest votes are guaranteed cast, and no
counting over the prefix alone reaches the bound at `n = 3f + 1`. A
forward-simulation proof sees only the prefix, so the single-core rule is not
dischargeable as stated.

The family form carries exactly the prefix-checkable content. `bindCores`
freezes a nonempty family of committed payload sets, pairwise sharing at
least `n − f` entries — the self-pair making every member itself that large —
and each return dominates *some* member. Every consequence the consumers need
is recovered pairwise: values heavy in two different members are both heavy
on the shared `n − f ≥ 2f + 1` entries, hence equal; and a member's
`n − f ≥ 2f + 1` entries put `f + 1` honest committed entries behind every
heavy value. The source's single core is the family's intersection —
contained in every return through whichever member that return dominates —
and its `n − f` size bound is exactly the part that holds only in completed
executions.

Every transition is Dirac, so the instance is an LTS. `fail` is the
determinised D1 corruption.
-/

namespace PLTS
namespace ABA
namespace Gather

/-- A payload set: finitely many `(process, value)` pairs. -/
abbrev APSet (n : ℕ) (X : Type) : Type := Finset (Fin n × X)

/-- The entries of `U` are entries of the partial map `h`. -/
def APSet.subMap {n : ℕ} {X : Type} (U : APSet n X) (h : Fin n → Option X) : Prop :=
  ∀ p ∈ U, h p.1 = some p.2

/-- `subMap` is monotone in the payload set. -/
theorem APSet.subMap_mono {n : ℕ} {X : Type} {U V : APSet n X}
    {h : Fin n → Option X} (hUV : U ⊆ V) (hV : V.subMap h) : U.subMap h :=
  fun p hp => hV p (hUV hp)

/-- The alphabet of one gather instance over payload type `X`. -/
inductive Lab (n : ℕ) (X : Type) : Type
  /-- The silent label. -/
  | tau
  /-- The environment calls process `id` with payload `x`. -/
  | call (id : Fin n) (x : X)
  /-- Process `id` returns the partial map `g`. -/
  | ret (id : Fin n) (g : Fin n → Option X)
  /-- Corruption of process `id`. -/
  | fail (id : Fin n)

instance {n : ℕ} {X : Type} : Silent (Lab n X) := ⟨Lab.tau⟩

@[simp] theorem Lab.silent_eq {n : ℕ} {X : Type} :
    (Silent.τ : Lab n X) = Lab.tau := rfl

/-- The state of one gather specification instance. -/
structure SpecState (n : ℕ) (X : Type) : Type where
  /-- The environment's call records. -/
  call : Fin n → Option X
  /-- The committed entries: what each process's contribution delivers.
  Each entry is written at most once, by `commit`. -/
  val : Fin n → Option X
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The core family: every return contains some member. Written at most
  once, by `bindCores`. -/
  cores : Option (Finset (APSet n X))
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)

namespace SpecState

variable {n : ℕ} {X : Type}

/-- The initial gather instance state. -/
def initial (n : ℕ) (X : Type) : SpecState n X where
  call := fun _ => none
  val := fun _ => none
  ret := fun _ => false
  cores := none
  F := ∅

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n X) : SpecState P.n X :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-! ### Corruption frame lemmas -/

variable {X : Type}

@[simp] theorem corrupt_call (P : Params) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).call = s.call := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_val (P : Params) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).val = s.val := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret (P : Params) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_cores (P : Params) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).cores = s.cores := by
  unfold SpecState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. Not a simp lemma: it introduces an
`ite`. -/
theorem SpecState.corrupt_F (P : Params) (s : SpecState P.n X) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold SpecState.corrupt
  split_ifs <;> rfl

/-- The step relation of the gather specification instance (blueprint
Transition System 4, with the committed entries and the core family in place
of the source's call-borne values and single bound core). -/
inductive Step (P : Params) [DecidableEq X] :
    SpecState P.n X → Lab P.n X → PMF (SpecState P.n X) → Prop
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
  /-- Binding: freeze the core family. Every member's entries are committed,
  and any two members — the self-pair included — share at least `n − f`
  entries. Fires at most once per instance. -/
  | bindCores (s : SpecState P.n X) (Cs : Finset (APSet P.n X))
      (h0 : s.cores = none) (hne : Cs.Nonempty)
      (hval : ∀ U ∈ Cs, APSet.subMap U s.val)
      (hpair : ∀ U ∈ Cs, ∀ V ∈ Cs, P.n - P.f ≤ (U ∩ V).card) :
      Step P s .tau (PMF.pure { s with cores := some Cs })
  /-- A process returns a sub-map of the committed entries containing some
  member of the core family. -/
  | ret (s : SpecState P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (Cs : Finset (APSet P.n X)) (hCs : s.cores = some Cs)
      (hmem : ∃ U ∈ Cs, APSet.subMap U g)
      (hsub : ∀ k x, g k = some x → s.val k = some x)
      (hr : s.ret id = false) :
      Step P s (.ret id g)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n X) (id : Fin P.n) :
      Step P s (.fail id) (PMF.pure (s.corrupt P id))

variable [DecidableEq X]

/-- The gather specification instance. -/
noncomputable def specInst (P : Params) (X : Type) [DecidableEq X] :
    System (SpecState P.n X) (Lab P.n X) where
  init := SpecState.initial P.n X
  step := Step P

@[simp] theorem specInst_init (P : Params) :
    (specInst P X).init = SpecState.initial P.n X := rfl

@[simp] theorem specInst_step (P : Params) (s : SpecState P.n X)
    (l : Lab P.n X) (μ : PMF (SpecState P.n X)) :
    (specInst P X).step s l μ ↔ Step P s l μ := Iff.rfl

/-- Every gather spec transition is Dirac: the instance is an LTS. -/
theorem specInst_isLTS (P : Params) : (specInst P X).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end Gather
end ABA
end PLTS
