/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The WCC specification instance (blueprint Transition System 3)

The round-`r` instance of the Weak Common Coin specification. A call records
its caller. The resolution is a silent transition, enabled at `val = ⊥` once the
number of callers exceeds `f`, and placed by the scheduler. It draws `val` from
`wccPMF`: each bit with probability `ε` (all correct processes receive that
bit), the failure outcome with probability `δ`, and `⊤` with the remaining
mass. Under `⊤` delivery happens and each process's returned bit is left to the
adversary. The resolution is the only probabilistic transition of the
instance, and the only one of the whole development besides `ABA.spec`'s.

The coin's value domain `ABA.CoinValue` is declared here, together with the map
`ABA.CoinOutcome.toCoinValue` that sends a `wccPMF` outcome to the value the
resolution writes.

## The count of callers

The threshold is `P.f < |{id | called id}|`. It counts callers alone, after
Definition 2.1 of ABDY22, which counts accesses to the coin. A corrupted
process reaches the instance as a caller, since `coinLabelMap` sends its
`byzantineCallW r k` to `callW r k`, so `called` counts it. The corrupted set
`F` is not added to the count. The family combinator broadcasts `fail` by a
deterministic transform, so a corruption cannot enable the resolution on its
own.

Deviations: the `guess` label is omitted (D4 -- it exists solely for the
out-of-scope Unpredictability property), and `fail` is the determinised
`corrupt` (D1).

* **D17 (δ-mass failure outcome).** The coin implementation the source builds
  on is an `ε`-correct verifiable secret sharing scheme, whose delivery
  guarantee holds only up to a failure probability `δ`; the specification
  inherits that failure as an outcome of its own. `wccPMF` therefore carries a
  fourth outcome `undelivered` of mass `δ`, pushed into `val := CoinValue.undelivered`. An
  `undelivered` round enables no `ret`: the return transition's guard is positive
  (`val = ⊤ ∨ val = bit b`), so a failed resolution silently delivers nothing
  and the round's callers wait forever. This is distinct from `⊤`, where
  delivery does happen and the adversary merely picks each process's returned
  bit.

The instance steps on its own round-`r` API labels, on `fail`, and on `τ` by the
resolution (`WCC.step_tau_cases`). The family combinator (`System.family`)
supplies idle self-loops on every other label.
-/

namespace PLTS
namespace ABA

/-- A `⊤`-completed value: `⊥`, `⊤`, a bit, or a failed resolution. The value
domain of the weak common coin, written by `WCC.Step.resolve` and read by
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
  /-- The corrupted set (local copy, kept equal by `fail` broadcast). -/
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

/-- The state with `id`'s access recorded: the successor of `id`'s call. -/
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
  /-- A process calls the coin, and the call records the caller. -/
  | call (s : SpecState P.n) (id : Fin P.n) (h : s.called id = false) :
      Step P r s (.callW r id) (PMF.pure (s.record id))
  /-- The coin resolves: at an unresolved `val` with the number of callers above
  `f`, `val` is drawn from `wccPMF`. This is the instance's only probabilistic
  transition. Outcome `undelivered` (mass `δ`, deviation D17) resolves the coin
  without delivering. -/
  | resolve (s : SpecState P.n) (hv : s.val = .bot) (ht : s.threshold P) :
      Step P r s .tau (P.wccPMF.map (fun o => { s with val := o.toCoinValue }))
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

/-- The two transitions of the call label: the input-enabledness loop and the call that
records the caller. -/
theorem step_callW_cases {P : Parameters} {r : ℕ} {s : SpecState P.n} {id : Fin P.n}
    {μ : PMF (SpecState P.n)} (h : Step P r s (.callW r id) μ) :
    μ = PMF.pure s ∨ (s.called id = false ∧ μ = PMF.pure (s.record id)) := by
  cases h with
  | call _ h => exact Or.inr ⟨h, rfl⟩
  | callLoop => exact Or.inl rfl

/-- The silent transition of the instance is the resolution: it is enabled at an
unresolved `val` with the number of callers above `f`, and draws `val` from `wccPMF`. -/
theorem step_tau_cases {P : Parameters} {r : ℕ} {s : SpecState P.n}
    {μ : PMF (SpecState P.n)} (h : Step P r s .tau μ) :
    s.val = .bot ∧ s.threshold P ∧
      μ = P.wccPMF.map (fun o => { s with val := o.toCoinValue }) := by
  cases h with
  | resolve hv ht => exact ⟨hv, ht, rfl⟩

/-- A state in the support of a call's successor either is the state the call
was taken at -- the input-enabledness loop -- or records the call. -/
theorem step_callW_support {P : Parameters} {r : ℕ} {s : SpecState P.n} {id : Fin P.n}
    {μ : PMF (SpecState P.n)} (h : Step P r s (.callW r id) μ)
    {x : SpecState P.n} (hx : x ∈ μ.support) : x = s ∨ x.called id = true := by
  rcases step_callW_cases h with rfl | ⟨-, rfl⟩
  · exact Or.inl (by simpa using hx)
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact Or.inr (by simp)

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
round, `fail` broadcast to all of them, idle on the labels it does not own. -/
noncomputable def specFamily (P : Parameters) :
    System (ℕ → SpecState P.n) (Label P.n) :=
  System.family (specInst P) Label.wccRound Label.isFail (failAct P)

/-- The silent transition of the family is one instance's resolution: some round `r`
takes its `τ`, and every other round is unchanged. -/
theorem specFamily_tau_cases (P : Parameters) {o : ℕ → SpecState P.n}
    {ω : PMF (ℕ → SpecState P.n)} (h : (specFamily P).step o Label.tau ω) :
    ∃ r μr, Step P r (o r) .tau μr ∧ ω = μr.map (Function.update o r) := by
  rw [specFamily, System.family_step_iff] at h
  rcases h with ⟨-, r, μr, hstep, rfl⟩ | ⟨r, hr, -⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · exact ⟨r, μr, hstep, rfl⟩
  · exact absurd hr (by simp [Label.wccRound])
  · exact absurd rfl hτ
  · exact absurd rfl hτ

end WCC
end ABA
end PLTS
