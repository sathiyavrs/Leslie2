/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.ProcessAndNetworkState
import Leslie2.Systems.LTS

/-!
# The BRB specification (blueprint Transition System 6)

The specification of one Byzantine Reliable Broadcast instance with designated
leader `ldr`, over an arbitrary payload type `M`, on its own alphabet
`BRB.Lab n M`. Safety only: of the blueprint's three properties, Validity and
Agreement are carried and Totality is out of scope (deviation D27, with the
development's standing scope cut on liveness).

The state splits the source's single `call` field in two. `input` records the
environment's call to the leader; `val` is the value the instance is committed
to deliver, written at most once by the internal transition `commit`. The
source couples them — its call transition writes the committed value directly,
and a separate τ-rule lets a Byzantine leader overwrite it while no process
has returned. The split states the same content without an overwrite: `commit`
fires once, at any point, and its guard `ldr ∈ F ∨ input = some m` says a
corrupted leader commits anything while an honest one commits only its input.
Decoupling the commit from the call is not a strengthening but the honest
reading of the source's overwrite window: a leader corrupted *after* an honest
call can still direct the delivered value anywhere until the first return, and
a spec that pinned `val` at call time would refuse that execution.

Both properties are then linear. Agreement: `ret` hands out `val`, and `val`
is written once. Validity: if the leader is never corrupted then `commit`'s
guard forces `val = input`.

Every transition is Dirac, so the instance is an LTS. `fail` is the
determinised D1 corruption.
-/

namespace PLTS
namespace ABA
namespace BRB

/-- The alphabet of one BRB instance over payload type `M`: the leader's call,
the per-process returns, and corruption. -/
inductive Lab (n : ℕ) (M : Type) : Type
  /-- The silent label. -/
  | tau
  /-- The environment calls the leader with payload `m`. -/
  | call (m : M)
  /-- Process `id` returns the delivered payload `m`. -/
  | ret (id : Fin n) (m : M)
  /-- Corruption of process `id`. -/
  | fail (id : Fin n)
  deriving DecidableEq

instance {n : ℕ} {M : Type} : Silent (Lab n M) := ⟨Lab.tau⟩

@[simp] theorem Lab.silent_eq {n : ℕ} {M : Type} :
    (Silent.τ : Lab n M) = Lab.tau := rfl

/-- The state of one BRB specification instance. -/
structure SpecState (n : ℕ) (M : Type) : Type where
  /-- The environment's call to the leader (`none` before the call). -/
  input : Option M
  /-- The committed value: what every return delivers. Written at most once,
  by `commit`. -/
  val : Option M
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace SpecState

variable {n : ℕ} {M : Type}

/-- The initial BRB instance state. -/
def initial (n : ℕ) (M : Type) : SpecState n M where
  input := none
  val := none
  ret := fun _ => false
  F := ∅

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Params) (id : Fin P.n) (s : SpecState P.n M) : SpecState P.n M :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-! ### Corruption frame lemmas -/

variable {M : Type}

@[simp] theorem corrupt_input (P : Params) (s : SpecState P.n M) (id : Fin P.n) :
    (s.corrupt P id).input = s.input := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_val (P : Params) (s : SpecState P.n M) (id : Fin P.n) :
    (s.corrupt P id).val = s.val := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret (P : Params) (s : SpecState P.n M) (id : Fin P.n) :
    (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. Not a simp lemma: it introduces an
`ite`. -/
theorem SpecState.corrupt_F (P : Params) (s : SpecState P.n M) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold SpecState.corrupt
  split_ifs <;> rfl

/-- The step relation of the BRB specification instance with leader `ldr`
(blueprint Transition System 6, deviations D1/D27). -/
inductive Step (P : Params) (ldr : Fin P.n) :
    SpecState P.n M → Lab P.n M → PMF (SpecState P.n M) → Prop
  /-- The environment calls the leader. -/
  | call (s : SpecState P.n M) (m : M) (h : s.input = none) :
      Step P ldr s (.call m) (PMF.pure { s with input := some m })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n M) (m : M) :
      Step P ldr s (.call m) (PMF.pure s)
  /-- The instance commits its delivered value: anything under a corrupted
  leader, the leader's input otherwise. Fires at most once — the guard is
  `val = none` — and no rule unwrites `val`. -/
  | commit (s : SpecState P.n M) (m : M)
      (hv : s.val = none) (hm : ldr ∈ s.F ∨ s.input = some m) :
      Step P ldr s .tau (PMF.pure { s with val := some m })
  /-- A process returns the committed value. -/
  | ret (s : SpecState P.n M) (id : Fin P.n) (m : M)
      (hm : s.val = some m) (hr : s.ret id = false) :
      Step P ldr s (.ret id m)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n M) (id : Fin P.n) :
      Step P ldr s (.fail id) (PMF.pure (s.corrupt P id))

/-- The BRB specification instance with leader `ldr`. -/
noncomputable def specInst (P : Params) (ldr : Fin P.n) (M : Type) :
    System (SpecState P.n M) (Lab P.n M) where
  init := SpecState.initial P.n M
  step := Step P ldr

@[simp] theorem specInst_init (P : Params) (ldr : Fin P.n) :
    (specInst P ldr M).init = SpecState.initial P.n M := rfl

@[simp] theorem specInst_step (P : Params) (ldr : Fin P.n) (s : SpecState P.n M)
    (l : Lab P.n M) (μ : PMF (SpecState P.n M)) :
    (specInst P ldr M).step s l μ ↔ Step P ldr s l μ := Iff.rfl

/-- Every BRB spec transition is Dirac: the instance is an LTS. -/
theorem specInst_isLTS (P : Params) (ldr : Fin P.n) : (specInst P ldr M).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end BRB
end ABA
end PLTS
