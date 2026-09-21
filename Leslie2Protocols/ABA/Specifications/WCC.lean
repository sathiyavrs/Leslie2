/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The WCC specification instance (blueprint Transition System 3)

The round-`r` instance of the Weak Common Coin specification. The coin
resolves inside the `(f+1)`st recorded access: the call that carries the number of
callers above `f` at an unresolved `val` draws `val` from `wccPMF` -- each bit
with probability `ε` (all correct processes receive that bit), the failure
outcome with probability `δ`, and `⊤` with the remaining mass. Under `⊤`
delivery happens and each process's returned bit is left to the adversary.
That call is the only probabilistic transition of the instance, and the only
one of the whole development besides `ABA.Spec`'s.

The call label therefore carries two rows. The recording call takes a caller
that does not cross the threshold, or one at an already resolved `val`, and
records it. The resolving call takes the crossing caller at `val = ⊥`, and
records it while drawing `val`. Their guards are exclusive.

The coin's value domain `ABA.CoinValue` is declared here, together with the map
`ABA.CoinOutcome.toCoinValue` that sends a `wccPMF` outcome to the value the
resolution writes.

## Why the corrupted set is not counted

The threshold is `P.f < |{id | called id}|`: it counts accesses. A corrupted
process reaches the instance as a caller, since `coinLabelMap` sends its
`byzantineCallW r k` to `callW r k`, so `called` already counts it. Were `F` added
to the count, a corruption would be able to carry the count across the
threshold; the family combinator broadcasts `fail` by a deterministic
transform, so that resolution would have to be drawn on a Dirac row.

Deviations: the `guess` label is omitted (D4 -- it exists solely for the
out-of-scope Unpredictability property), and `fail` is the determinised
`corrupt` (D1).

* **D17 (δ-mass failure outcome).** The coin implementation the source builds
  on is an `ε`-correct verifiable secret sharing scheme, whose delivery
  guarantee holds only up to a failure probability `δ`; the specification
  inherits that failure as an outcome of its own. `wccPMF` therefore carries a
  fourth outcome `undelivered` of mass `δ`, pushed into `val := CoinValue.undelivered`. An
  `undelivered` round enables no `ret`: the return rule's guard is positive
  (`val = ⊤ ∨ val = bit b`), so a failed resolution silently delivers nothing
  and the round's callers wait forever. This is distinct from `⊤`, where
  delivery does happen and the adversary merely picks each process's returned
  bit.

* **D31 (resolution inside the crossing access).** The coin resolves inside
  the access that crosses the threshold, and the threshold counts accesses
  alone, following Fig. 7 of *Asynchronous Randomized Consensus with Ghost
  Variables* (working draft, 2026). Transition System 3 resolves
  by a separately scheduled rule and counts the corrupted set alongside the
  callers. The crossing access is a recorded one: `WCC.Step.callLoop` carries
  the call label at every state and records no caller, so a call may be
  answered there, and the scheduler may defer the resolution past any number
  of calls. No safety theorem of the development depends on the coin
  resolving.

The instance only steps on its own round-`r` API labels and `fail`; it has no
silent row (`WCC.step_tau_inv`), and the family combinator (`System.family`)
supplies idle self-loops on every other label.
-/

namespace PLTS
namespace ABA

/-- A `⊤`-completed value: `⊥`, `⊤`, a bit, or a failed resolution. The value
domain of the weak common coin, written by `WCC.Step.callResolve` and read by
`WCC.Step.ret`. -/
inductive CoinValue : Type
  /-- Unresolved (`⊥`). -/
  | bot
  /-- Adversarial outcome (`⊤`): every process may receive either bit. -/
  | top
  /-- The common bit `b`. -/
  | bit (b : Bool)
  /-- Failed resolution: the coin resolved without delivering, so no process
  ever receives a value. Distinct from `⊥` (not yet resolved) and from `⊤`
  (delivered, with the adversary choosing each process's bit). -/
  | undelivered
  deriving DecidableEq, Repr

/-- The `CoinValue` recorded by a coin resolution with the given outcome: the common
bit, `⊤` for the adversarial outcome, and `undelivered` for delivery failure. -/
def CoinOutcome.toCoinValue : CoinOutcome → CoinValue
  | .bit b => .bit b
  | .adversarial => .top
  | .undelivered => .undelivered

/-- `toCoinValue` is injective: the four coin outcomes land on four distinct
`CoinValue`s. -/
theorem CoinOutcome.toCoinValue_injective : Function.Injective CoinOutcome.toCoinValue := by
  intro a b h; cases a <;> cases b <;> simp_all [CoinOutcome.toCoinValue]

namespace WCC

/-- The state of one WCC specification instance. -/
structure SpecState (n : ℕ) where
  /-- Which processes have called this instance. -/
  called : Fin n → Bool
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The coin outcome (`⊥` until resolved). -/
  val : CoinValue
  /-- The corrupted set (local copy, kept in lockstep by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial WCC instance state. -/
def initial (n : ℕ) : SpecState n where
  called := fun _ => false
  ret := fun _ => false
  val := .bot
  F := ∅

/-- The state with `id`'s access recorded. Both call rows produce their
successor from it, and the resolution threshold is read at it. -/
def record (s : SpecState n) (id : Fin n) : SpecState n :=
  { s with called := Function.update s.called id true }

@[simp] theorem record_called_self (s : SpecState n) (id : Fin n) :
    (s.record id).called id = true := by simp [record]

@[simp] theorem record_called_ne (s : SpecState n) {id j : Fin n} (h : j ≠ id) :
    (s.record id).called j = s.called j := by simp [record, h]

@[simp] theorem record_val (s : SpecState n) (id : Fin n) :
    (s.record id).val = s.val := rfl

@[simp] theorem record_ret (s : SpecState n) (id : Fin n) :
    (s.record id).ret = s.ret := rfl

@[simp] theorem record_F (s : SpecState n) (id : Fin n) :
    (s.record id).F = s.F := rfl

/-- The resolution threshold `|{id | called id}| > f`. -/
def threshold (P : Parameters) (s : SpecState P.n) : Prop :=
  P.f < (Finset.univ.filter (fun id => s.called id)).card

/-- Corruption (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-- The step relation of the round-`r` WCC specification instance. -/
inductive Step (P : Parameters) (r : ℕ) :
    SpecState P.n → Label P.n → PMF (SpecState P.n) → Prop
  /-- A process calls the coin and the call records nothing further: either the
  call leaves the caller count at `f` or below, or `val` is already resolved. -/
  | callRecord (s : SpecState P.n) (id : Fin P.n) (h : s.called id = false)
      (hres : ¬ ((s.record id).threshold P ∧ s.val = .bot)) :
      Step P r s (.callW r id) (PMF.pure (s.record id))
  /-- A process calls the coin, its access carries the caller count above `f`,
  and `val` is unresolved: the call records the caller and draws `val` from
  `wccPMF`. This is the instance's only probabilistic row. Outcome
  `undelivered` (mass `δ`, deviation D17) resolves the coin without
  delivering. -/
  | callResolve (s : SpecState P.n) (id : Fin P.n) (h : s.called id = false)
      (hv : s.val = .bot) (ht : (s.record id).threshold P) :
      Step P r s (.callW r id)
        (P.wccPMF.map (fun o => { s.record id with val := o.toCoinValue }))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.callW r id) (PMF.pure s)
  /-- A process receives its return: the common bit if `val = bit b`, an
  adversary-chosen bit if `val = ⊤`. The guard is positive, so an `undelivered`
  resolution (D17) enables no return at all. -/
  | ret (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.val = .top ∨ s.val = .bit b) (h₂ : s.ret id = false) :
      Step P r s (.retW r id b)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.fail id) (PMF.pure (s.corrupt P id))

/-- The three rows of the call label: the input-enabledness loop, the recording
call, and the resolving call. -/
theorem step_callW_inv {P : Parameters} {r : ℕ} {s : SpecState P.n} {id : Fin P.n}
    {μ : PMF (SpecState P.n)} (h : Step P r s (.callW r id) μ) :
    μ = PMF.pure s ∨
      (s.called id = false ∧ ¬ ((s.record id).threshold P ∧ s.val = .bot) ∧
        μ = PMF.pure (s.record id)) ∨
      (s.called id = false ∧ s.val = .bot ∧ (s.record id).threshold P ∧
        μ = P.wccPMF.map (fun o => { s.record id with val := o.toCoinValue })) := by
  cases h with
  | callRecord _ h hres => exact Or.inr (Or.inl ⟨h, hres, rfl⟩)
  | callResolve _ h hv ht => exact Or.inr (Or.inr ⟨h, hv, ht, rfl⟩)
  | callLoop => exact Or.inl rfl

/-- The instance has no silent row. -/
theorem step_tau_inv {P : Parameters} {r : ℕ} {s : SpecState P.n}
    {μ : PMF (SpecState P.n)} : ¬ Step P r s .tau μ := by
  intro h; cases h

/-- A state in the support of a call's successor either is the state the call
was taken at -- the input-enabledness loop -- or records the call. -/
theorem step_callW_support {P : Parameters} {r : ℕ} {s : SpecState P.n} {id : Fin P.n}
    {μ : PMF (SpecState P.n)} (h : Step P r s (.callW r id) μ)
    {x : SpecState P.n} (hx : x ∈ μ.support) : x = s ∨ x.called id = true := by
  rcases step_callW_inv h with rfl | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact Or.inl (by simpa using hx)
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact Or.inr (by simp)
  · refine Or.inr ?_
    simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨o, -, rfl⟩ := hx
    simp

/-- The round-`r` WCC specification instance. -/
noncomputable def specInst (P : Parameters) (r : ℕ) : System (SpecState P.n) (Label P.n) where
  init := SpecState.initial P.n
  step := Step P r

@[simp] theorem specInst_init (P : Parameters) (r : ℕ) :
    (specInst P r).init = SpecState.initial P.n := rfl

@[simp] theorem specInst_step (P : Parameters) (r : ℕ) (s : SpecState P.n)
    (l : Label P.n) (μ : PMF (SpecState P.n)) :
    (specInst P r).step s l μ ↔ Step P r s l μ := Iff.rfl

/-- The broadcast transform of the WCC family: corruption on `fail id`,
identity on every other label. -/
def failAct (P : Parameters) : Label P.n → SpecState P.n → SpecState P.n
  | .fail id, s => s.corrupt P id
  | _, s => s

/-- The ℕ-indexed family of WCC specification instances: one instance per
round, `fail` broadcast to all of them, idle on foreign labels. -/
noncomputable def specFamily (P : Parameters) :
    System (ℕ → SpecState P.n) (Label P.n) :=
  System.family (specInst P) Label.wccRound Label.isFail (failAct P)

/-- The family has no silent row: its instances have none, and every remaining
row of `System.family` carries a label other than `τ`. -/
theorem specFamily_tau_inv (P : Parameters) {o : ℕ → SpecState P.n}
    {ω : PMF (ℕ → SpecState P.n)} : ¬ (specFamily P).step o Label.tau ω := by
  rw [specFamily, System.family_step_iff]
  rintro (⟨-, r, μr, hstep, -⟩ | ⟨r, hr, -⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩)
  · exact step_tau_inv hstep
  · exact absurd hr (by simp [Label.wccRound])
  · exact hτ rfl
  · exact hτ rfl

end WCC
end ABA
end PLTS
