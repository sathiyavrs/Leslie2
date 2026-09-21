/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.Specification
import Leslie2Protocols.ABA.Specifications.ABASafety
import Leslie2Protocols.Framework.TraceDistributionSupport

/-!
# Safety of the GBCA specification instance

Binding is the promise a Graded Binding Crusader Agreement instance makes about
its *future*: there is a bit the instance will never hand out, in this run or in
any extension of it. On the specification state that promise is a field rather
than a theorem. `SpecState.excluded : Finset Bool` is the set of bits the instance
can no longer hand out; the value-bearing returns refuse an excluded bit and demand
that the other bit be excluded. Every return, whatever its grade, announces a bit
`β` on its label under the guard `(!β) ∈ excluded`, which is what puts the
promise on the trace.

Binding and the value clause of graded agreement rest on one fact: `excluded`
only grows. The single writer is the internal `bindUnset`, which inserts, and
`corrupt` does not touch the field — so `Step.excluded_mono` holds rule by rule,
and `is_exec_stable` lifts it to whole executions (`excluded_mem_stable`). Binding is
therefore structural: a bit excluded at any point of a run is excluded at every
later point, and a guard reading `∉ excluded` can never be re-enabled. That writer
also fires only from `excluded = ∅`, so the exclusion set never holds more than one
bit (`excluded_card_le_one`, from the step-level `Step.excluded_card_le_one`): the exclusion
commits the round, and the surviving bit stays available to every later return.

* `retG_value_agree` — **graded agreement, value clause**. ABDY22's
  Definition 3.2 has two clauses; this is the first. Two returns of one
  execution that hand out a bit hand out the same bit. A return of `v₁` fires
  from a state with `(!v₁) ∈ excluded`; monotonicity carries that membership to
  the state of any other return; that return needs its own bit alive, so its bit
  is not `!v₁`, so on `Bool` it is `v₁`. No invariant, no quorum arithmetic, no
  reachability hypothesis beyond membership in one execution.
* `retG_grade_exclusive` — **graded agreement, A/C clause**. The second clause
  of Definition 3.2: no execution carries both an `A`-return and a `C`-return.
  The `grade` field is the lock. `retA` writes `some true` and `retC` writes
  `some false`, each firing only from a state whose grade is unset or already on
  its own side, and no other rule touches the field, so `Step.grade_mono` holds
  rule by rule and `grade_stable` carries the written value to every later
  state. `specInst_grade_agree` is the same statement read off the trace.
* `retG_bound_agree` — **one bound bit per round**. Any two returns of one
  execution announce the same bit. Each return excludes the complement of the bit
  it announces, the run carries that exclusion forward, and no state excludes two
  bits.
* `specInst_binding` — binding read off the trace (`BindingTrace`). Every
  positive-probability trace of `specInst P r` carries a single round-`r`
  announced bit (`BoundTrace`), and every round-`r` return that names a bit
  (`outValue`, defined here: `A b` and `B b` name `b`, `C` names nothing) names
  the announced one. The graded-agreement reading — any two bit-naming returns of
  the trace name the same bit — is `BindingTrace.value_agree`.
* `retC_excluded_nonempty` — the **Graded Binding witness**, as the bit the
  `C`-return announces. After a `C`-return announcing `β`, `excluded` is nonempty
  in every later state of the execution, `!β` being the member. A member of
  `excluded` is a bit no non-faulty party can be handed at grade `≥ 1` in any
  extension, which is ABDY22's Graded Binding clause; the witness is produced at
  the `C`-return and survives because `excluded` never shrinks.
* `specInst_validity` — **Validity, safety half**. If every round-`r` call of
  the trace carries the bit `v` unless its caller is corrupted somewhere along
  the trace (`UnanimousInput`), then every round-`r` return of the trace hands
  out `v` (`ValidityTrace`). That the grade is the top one is a safety statement
  as well, and is carried by `specInst_no_retC` and `specInst_no_retB` together:
  neither the `C`-return nor the `B`-return is reachable under unanimity, so
  every round-`r` return of such a trace is an `A`-return of the input bit. The
  remaining half of the papers' Validity clause — that every non-faulty process
  is answered at all — is a fairness statement about which runs the scheduler
  must extend, outside the scope of a safety file.

"Corrupted somewhere along the trace" is `SpecSafety`'s never-corrupted
formulation, taken verbatim: `NeverCorrupted P t id` is non-membership in
`failSet P t k` for every `k`, the trace-level fold of D1-`corrupt` over the
`fail` labels, so a `fail id` that the budget refuses does not count as
corruption. Validity is the D15 counts read against that budget. The state
carries no invariant beyond a bookkeeping one (`CallInv`: every pending input
is attributed to a `callG` event of the history, and `F` is the fold of the
history's `fail` labels); the argument is then a pigeonhole. At any state,
every id supporting the dissenting bit `!v` is corrupted at some stage of the
trace — a caller of `!v` by unanimity, an `F`-member by the fold — and
`failSet` is monotone in the stage, so the whole support set sits inside one
`failSet P t K`, of size at most `f` (`supp_le_of_unanimous`). The D15 guards
asking `f + 1` there are therefore unreachable: `bindUnset v` never fires, so
`v` is alive at every state (`excluded_notMem_of_unanimous`), which forces the
value-bearing returns to hand out `v`; the same cap refutes the `C`-return's
count at `!v` and the `B`-return's dissent count outright.

The scope is the specification instance alone. That the implementation refines
it — hence inherits these properties — is the subject of the per-instance
forward simulation.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

variable {P : Parameters} {r : ℕ}

/-! ### Monotonicity of the exclusion set -/

/-- **The exclusion set never shrinks.** -/
theorem Step.excluded_mono {s s' : SpecState P.n} {l : Label P.n}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s l μ) (hs' : s' ∈ μ.support) :
    s.excluded ⊆ s'.excluded := by
  cases hstep <;>
    · rw [PMF.mem_support_pure_iff] at hs'
      subst hs'
      first
        | exact Finset.subset_insert _ _
        | exact Finset.Subset.refl _
        | (rw [corrupt_excluded])

/-! ### Run-level monotonicity -/

/-- **An excluded bit stays excluded along a run.** -/
theorem excluded_mem_stable {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b : Bool}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hb : b ∈ s₁.excluded) : b ∈ s₂.excluded :=
  is_exec_stable (sys := specInst P r) (fun s => b ∈ s.excluded)
    (fun _ _ _ _ hmem hstep hs' => Step.excluded_mono hstep hs' hmem)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hb

/-! ### The exclusion set holds at most one bit -/

/-- **One exclude per instance, step level.** `bindUnset` is the only writer and
it fires only from `excluded = ∅`, so it leaves a singleton; every other rule
leaves the field alone. -/
theorem Step.excluded_card_le_one {s s' : SpecState P.n} {l : Label P.n}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s l μ) (hs' : s' ∈ μ.support)
    (h : s.excluded.card ≤ 1) : s'.excluded.card ≤ 1 := by
  cases hstep with
  | bindUnset b hq hw hd0 =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    change (insert b s.excluded).card ≤ 1
    rw [hd0]
    simp
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    rw [corrupt_excluded]
    exact h
  | _ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact h

/-- **One exclude per instance.** Every state of every execution of the round-`r`
instance has `excluded.card ≤ 1`: the field starts empty and the single writer
fires only from `∅`. Together with `Step.excluded_mono` this pins the reachable
shape to `excluded ∈ {∅, {b}}` — the excluded-bit reading of the source blueprint's
bound value (D19). -/
theorem excluded_card_le_one {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k : ℕ} {s : SpecState P.n}
    (hst : e.stateAt k = some s) : s.excluded.card ≤ 1 :=
  is_exec_stable (sys := specInst P r) (fun s => s.excluded.card ≤ 1)
    (fun _ _ _ _ h hstep hs' => Step.excluded_card_le_one hstep hs' h)
    he 0 k e.init s (Nat.zero_le k) rfl hst
    (by rw [← he.2]; simp [specInst, SpecState.initial])

/-! ### Monotonicity of the grade lock -/

/-- **The grade lock never changes once set.** `retA` writes `some true` and
`retC` writes `some false`, each from a state whose grade is unset or already
on the side it writes; no other rule touches the field, `corrupt` included. -/
theorem Step.grade_mono {s s' : SpecState P.n} {l : Label P.n} {g : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s l μ) (hs' : s' ∈ μ.support)
    (hg : s.grade = some g) : s'.grade = some g := by
  cases hstep with
  | retA id v bnd hlive hexcluded hbnd hgd hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain rfl : g = true := by
      rcases hgd with h | h
      · rw [h] at hg; exact absurd hg (by simp)
      · rw [h] at hg; exact (Option.some.inj hg).symm
    rfl
  | retC id bnd hbnd hwT hwF hgd hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain rfl : g = false := by
      rcases hgd with h | h
      · rw [h] at hg; exact absurd hg (by simp)
      · rw [h] at hg; exact (Option.some.inj hg).symm
    rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    rw [corrupt_grade]
    exact hg
  | _ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hg

/-- **A locked grade stays locked along a run.** -/
theorem grade_stable {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {g : Bool}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hg : s₁.grade = some g) : s₂.grade = some g :=
  is_exec_stable (sys := specInst P r) (fun s => s.grade = some g)
    (fun _ _ _ _ hmem hstep hs' => Step.grade_mono hstep hs' hmem)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hg

/-! ### Inverting the return rows -/

/-- The bit a graded outcome hands out, if any: `A b` and `B b` hand out `b`,
`C` hands out nothing. -/
def outValue : GBCAOutput → Option Bool
  | .A b => some b
  | .B b => some b
  | .C => none

@[simp] theorem outValue_A (b : Bool) : outValue (.A b) = some b := rfl

@[simp] theorem outValue_B (b : Bool) : outValue (.B b) = some b := rfl

@[simp] theorem outValue_C : outValue .C = none := rfl

/-- An `A`-return pins its bit alive and the other bit excluded. -/
private theorem retA_inv {s : SpecState P.n} {id : Fin P.n} {v β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.A v) β) μ) :
    v ∉ s.excluded ∧ (!v) ∈ s.excluded :=
  match hstep with
  | .retA _ _ _ _ hlive hexcluded _ _ _ => ⟨hlive, hexcluded⟩

/-- A `B`-return pins its bit alive and the other bit excluded. -/
private theorem retB_inv {s : SpecState P.n} {id : Fin P.n} {v β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.B v) β) μ) :
    v ∉ s.excluded ∧ (!v) ∈ s.excluded :=
  match hstep with
  | .retB _ _ _ _ hlive hexcluded _ _ _ => ⟨hlive, hexcluded⟩

/-- **The guard of the announced bit.** Every return rule, whatever its grade,
fires from a state where the complement of the announced bit `β` is excluded. -/
theorem retG_bound_guard {s : SpecState P.n} {id : Fin P.n} {o : GBCAOutput}
    {β : Bool} {μ : PMF (SpecState P.n)}
    (hstep : Step P r s (.retG r id o β) μ) : (!β) ∈ s.excluded := by
  cases hstep <;> assumption

/-- **The guard pair of a value-bearing return.** Whatever its grade, a return
that hands out `v` fires from a state where `v` is alive and `!v` is excluded. -/
theorem retG_value_guards {s : SpecState P.n} {id : Fin P.n} {o : GBCAOutput}
    {v β : Bool} {μ : PMF (SpecState P.n)}
    (hstep : Step P r s (.retG r id o β) μ) (ho : outValue o = some v) :
    v ∉ s.excluded ∧ (!v) ∈ s.excluded := by
  cases o with
  | A w =>
    obtain rfl : w = v := by
      simpa using ho
    exact retA_inv hstep
  | B w =>
    obtain rfl : w = v := by
      simpa using ho
    exact retB_inv hstep
  | C => exact absurd ho (by simp)

/-- The D15 dissent count of a `B`-return: `f + 1` support at the bit it does
not hand out. -/
private theorem retB_supp {s : SpecState P.n} {id : Fin P.n} {v β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.B v) β) μ) :
    P.f + 1 ≤
      (Finset.univ.filter (fun id' => s.call id' = some (!v) ∨ id' ∈ s.F)).card :=
  match hstep with
  | .retB _ _ _ _ _ _ _ hw _ => hw

/-- An `A`-return fires from a state whose grade is unset or already on the
A-side. -/
private theorem retA_grade_guard {s : SpecState P.n} {id : Fin P.n} {v β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.A v) β) μ) :
    s.grade = none ∨ s.grade = some true :=
  match hstep with
  | .retA _ _ _ _ _ _ _ hg _ => hg

/-- A `C`-return fires from a state whose grade is unset or already on the
C-side. -/
private theorem retC_grade_guard {s : SpecState P.n} {id : Fin P.n} {β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id .C β) μ) :
    s.grade = none ∨ s.grade = some false :=
  match hstep with
  | .retC _ _ _ _ _ _ hg _ => hg

/-- An `A`-return locks the grade to the A-side. -/
private theorem retA_grade {s s' : SpecState P.n} {id : Fin P.n} {v β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id (.A v) β) μ)
    (hs' : s' ∈ μ.support) : s'.grade = some true := by
  cases hstep
  rw [PMF.mem_support_pure_iff] at hs'
  subst hs'
  rfl

/-- A `C`-return locks the grade to the C-side. -/
private theorem retC_grade {s s' : SpecState P.n} {id : Fin P.n} {β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id .C β) μ)
    (hs' : s' ∈ μ.support) : s'.grade = some false := by
  cases hstep
  rw [PMF.mem_support_pure_iff] at hs'
  subst hs'
  rfl

/-- Two bits excluded at one state of an execution are equal: the exclusion set
holds at most one bit. -/
private theorem excluded_eq_of_mem {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k : ℕ} {s : SpecState P.n} {b₁ b₂ : Bool}
    (hst : e.stateAt k = some s) (h₁ : b₁ ∈ s.excluded) (h₂ : b₂ ∈ s.excluded) :
    b₁ = b₂ :=
  Finset.card_le_one.mp (excluded_card_le_one he hst) _ h₁ _ h₂

/-- **A value-bearing return announces the bit it hands out.** The value guard
excludes `!v` and the bound guard excludes `!β`, and a state of an execution
excludes at most one bit. -/
theorem retG_value_eq_bound {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k : ℕ} {s : SpecState P.n} {id : Fin P.n}
    {o : GBCAOutput} {v β : Bool} {μ : PMF (SpecState P.n)}
    (hst : e.stateAt k = some s) (hstep : Step P r s (.retG r id o β) μ)
    (ho : outValue o = some v) : v = β := by
  have h := excluded_eq_of_mem he hst (retG_value_guards hstep ho).2
    (retG_bound_guard hstep)
  revert h
  cases v <;> cases β <;> simp

/-! ### Binding and graded agreement along a run -/

/-- Two value-bearing returns of one run agree on the bit (`k₁ ≤ k₂` case). -/
private theorem retG_value_agree_le {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput}
    {v₁ v₂ β₁ β₂ : Bool} {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂)
    (ho₁ : outValue o₁ = some v₁) (ho₂ : outValue o₂ = some v₂) : v₁ = v₂ := by
  obtain ⟨-, hexcluded₁⟩ := retG_value_guards hstep₁ ho₁
  obtain ⟨hlive₂, -⟩ := retG_value_guards hstep₂ ho₂
  have hcarry : (!v₁) ∈ s₂.excluded := excluded_mem_stable he hk hst₁ hst₂ hexcluded₁
  have hne : v₂ ≠ !v₁ := fun h => hlive₂ (h ▸ hcarry)
  revert hne
  cases v₁ <;> cases v₂ <;> simp

/-- **Binding / graded agreement.** Any two value-bearing returns occurring
along one execution of the round-`r` specification instance hand out the same
bit, whatever their grades and whichever processes they answer. The whole
argument is the guard pair plus monotonicity: the first return pins `!v₁` into
`excluded`, `excluded` only grows, and the second return refuses an excluded bit. -/
theorem retG_value_agree {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput}
    {v₁ v₂ β₁ β₂ : Bool} {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂)
    (ho₁ : outValue o₁ = some v₁) (ho₂ : outValue o₂ = some v₂) : v₁ = v₂ := by
  rcases le_total k₁ k₂ with h | h
  · exact retG_value_agree_le he h hst₁ hst₂ hstep₁ hstep₂ ho₁ ho₂
  · exact (retG_value_agree_le he h hst₂ hst₁ hstep₂ hstep₁ ho₂ ho₁).symm

/-- Two returns of one run announce the same bit (`k₁ ≤ k₂` case). -/
private theorem retG_bound_agree_le {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput} {β₁ β₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂) : β₁ = β₂ := by
  have hcarry : (!β₁) ∈ s₂.excluded :=
    excluded_mem_stable he hk hst₁ hst₂ (retG_bound_guard hstep₁)
  have h := excluded_eq_of_mem he hst₂ hcarry (retG_bound_guard hstep₂)
  revert h
  cases β₁ <;> cases β₂ <;> simp

/-- **One bound bit per round.** Any two returns occurring along one execution of
the round-`r` specification instance announce the same bit. Each fires under
`(!β) ∈ excluded`, the exclusion set only grows, and no state of an execution
excludes two bits. -/
theorem retG_bound_agree {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ}
    {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput} {β₁ β₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂) : β₁ = β₂ := by
  rcases le_total k₁ k₂ with h | h
  · exact retG_bound_agree_le he h hst₁ hst₂ hstep₁ hstep₂
  · exact (retG_bound_agree_le he h hst₂ hst₁ hstep₂ hstep₁).symm

/-- **The Graded Binding witness**, as the bit the `C`-return announces. The
return fires under `(!β) ∈ excluded`, so the exclusion set is nonempty in every
later state of the execution: `!β` is a bit no extension of the run can ever hand
out, and the announced `β` is the clause's witness. -/
theorem retC_excluded_nonempty {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {id : Fin P.n} {β : Bool} {μ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep : Step P r s₁ (.retG r id .C β) μ) : s₂.excluded.Nonempty :=
  ⟨!β, excluded_mem_stable he hk hst₁ hst₂ (retG_bound_guard hstep)⟩

/-- **A/C exclusivity along a run.** No execution of the round-`r`
specification instance carries both an `A`-return and a `C`-return. The
`A`-return locks the grade to `some true` and the `C`-return to `some false`,
each fires only from a state whose grade is unset or already on its own side,
and `grade_stable` carries the earlier lock to the later return's state. -/
theorem retG_grade_exclusive {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (specInst P r)) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂)
    {s₁' s₂' : SpecState P.n} {id₁ id₂ : Fin P.n} {v β₁ β₂ : Bool}
    (hg₁ : e.trans.get? k₁ = some (.retG r id₁ (.A v) β₁, s₁'))
    (hg₂ : e.trans.get? k₂ = some (.retG r id₂ .C β₂, s₂')) : False := by
  obtain ⟨s₁, μ₁, hst₁, hstep₁, hsupp₁⟩ := he.1 k₁ _ _ hg₁
  obtain ⟨s₂, μ₂, hst₂, hstep₂, hsupp₂⟩ := he.1 k₂ _ _ hg₂
  have hnext₁ : e.stateAt (k₁ + 1) = some s₁' := by
    rw [show e.stateAt (k₁ + 1) = (e.trans.get? k₁).map Prod.snd from rfl, hg₁]
    rfl
  have hnext₂ : e.stateAt (k₂ + 1) = some s₂' := by
    rw [show e.stateAt (k₂ + 1) = (e.trans.get? k₂).map Prod.snd from rfl, hg₂]
    rfl
  rcases lt_or_gt_of_ne hne with h | h
  · have hlock : s₂.grade = some true :=
      grade_stable he h hnext₁ hst₂ (retA_grade hstep₁ hsupp₁)
    rcases retC_grade_guard hstep₂ with hc | hc <;> rw [hlock] at hc <;> simp at hc
  · have hlock : s₁.grade = some false :=
      grade_stable he h hnext₂ hst₁ (retC_grade hstep₂ hsupp₂)
    rcases retA_grade_guard hstep₁ with hc | hc <;> rw [hlock] at hc <;> simp at hc

/-! ### The trace-level statement -/

/-- **The announced bit is one bit (trace form).** Any two round-`r` returns
appearing in the trace announce the same bit. -/
def BoundTrace (P : Parameters) (r : ℕ) (t : Seq (Label P.n)) : Prop :=
  ∀ (id₁ id₂ : Fin P.n) (o₁ o₂ : GBCAOutput) (β₁ β₂ : Bool),
    Label.retG r id₁ o₁ β₁ ∈ t → Label.retG r id₂ o₂ β₂ ∈ t → β₁ = β₂

/-- **Binding (trace form).** The round is bound to one bit on the trace: all
round-`r` returns of the trace announce the same bit, and every one of them that
hands out a value hands out that bit. -/
def BindingTrace (P : Parameters) (r : ℕ) (t : Seq (Label P.n)) : Prop :=
  BoundTrace P r t ∧
    ∀ (id : Fin P.n) (o : GBCAOutput) (β v : Bool),
      Label.retG r id o β ∈ t → outValue o = some v → v = β

/-- **Graded agreement (trace form).** Any two round-`r` returns of a bound trace
that hand out a bit hand out the same bit: each hands out the bit it announces,
and the two announcements agree. -/
theorem BindingTrace.value_agree {t : Seq (Label P.n)} (h : BindingTrace P r t)
    {id₁ id₂ : Fin P.n} {o₁ o₂ : GBCAOutput} {β₁ β₂ v₁ v₂ : Bool}
    (h₁ : Label.retG r id₁ o₁ β₁ ∈ t) (h₂ : Label.retG r id₂ o₂ β₂ ∈ t)
    (ho₁ : outValue o₁ = some v₁) (ho₂ : outValue o₂ = some v₂) : v₁ = v₂ := by
  rw [h.2 id₁ o₁ β₁ v₁ h₁ ho₁, h.2 id₂ o₂ β₂ v₂ h₂ ho₂]
  exact h.1 id₁ id₂ o₁ o₂ β₁ β₂ h₁ h₂

/-- **Binding of the GBCA specification instance**: every trace in the support
of every achievable trace distribution of `GBCA.specInst P r` satisfies
`BindingTrace`. The announced bits agree because each return excludes the
complement of the one it announces, an exclusion the run carries forward, and a
state excludes at most one bit; a value-bearing return announces the bit it hands
out by the same cardinality bound at its own state. -/
theorem specInst_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      BindingTrace P r t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ :=
    exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  constructor
  · intro id₁ id₂ o₁ o₂ β₁ β₂ h₁ h₂
    obtain ⟨-, k₁, s₁', hg₁⟩ := (h_char _).mp h₁
    obtain ⟨-, k₂, s₂', hg₂⟩ := (h_char _).mp h₂
    obtain ⟨s₁, μ₁, hst₁, hstep₁, -⟩ := h_exec.1 k₁ _ _ hg₁
    obtain ⟨s₂, μ₂, hst₂, hstep₂, -⟩ := h_exec.1 k₂ _ _ hg₂
    exact retG_bound_agree h_exec hst₁ hst₂ hstep₁ hstep₂
  · intro id o β v h_mem ho
    obtain ⟨-, k, s', hg⟩ := (h_char _).mp h_mem
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    exact retG_value_eq_bound h_exec hst hstep ho

/-- **A/C exclusivity of the GBCA specification instance**: no trace in the
support of an achievable trace distribution of `GBCA.specInst P r` carries both
an `A`-return and a `C`-return. This is the second clause of ABDY22's
Definition 3.2 (Graded Agreement); the first, that any two returns handing out
a bit hand out the same bit, is `retG_value_agree`, read on the trace by
`BindingTrace.value_agree`. -/
theorem specInst_grade_agree (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      ∀ (id₁ id₂ : Fin P.n) (v β₁ β₂ : Bool),
        Label.retG r id₁ (.A v) β₁ ∈ t → Label.retG r id₂ .C β₂ ∉ t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne id₁ id₂ v β₁ β₂ hA hC
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ :=
    exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  obtain ⟨-, k₁, s₁', hg₁⟩ := (h_char _).mp hA
  obtain ⟨-, k₂, s₂', hg₂⟩ := (h_char _).mp hC
  refine retG_grade_exclusive h_exec ?_ hg₁ hg₂
  rintro rfl
  rw [hg₁] at hg₂
  simp at hg₂

/-! ### Validity: the trace-level hypothesis and conclusion -/

/-- **Unanimous honest input `v`** (trace form): every round-`r` call of the
trace carries `v`, unless its caller is corrupted somewhere along the trace.
Corruption is `SpecSafety`'s trace-level notion (`NeverCorrupted`, the fold
`failSet` of D1-`corrupt` over the `fail` labels), not the bare presence of a
`fail` label: a `fail` the budget refuses corrupts nobody. -/
def UnanimousInput (P : Parameters) (r : ℕ) (v : Bool) (t : Seq (Label P.n)) : Prop :=
  ∀ (id : Fin P.n) (b : Bool), Label.callG r id b ∈ t →
    b = v ∨ ¬ NeverCorrupted P t id

/-- **Validity, safety half** (trace form): every round-`r` return of the trace
hands out `v`. Returner-unconditional, and it excludes `C` outright, `C`
handing out nothing. -/
def ValidityTrace (P : Parameters) (r : ℕ) (v : Bool) (t : Seq (Label P.n)) : Prop :=
  ∀ (id : Fin P.n) (o : GBCAOutput) (β : Bool),
    Label.retG r id o β ∈ t → outValue o = some v

/-! ### The bookkeeping invariant -/

/-- `corrupt` acts on `F` exactly as the bare-set fold step `corruptSet`. -/
theorem corrupt_F (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).F = corruptSet P id s.F := by
  unfold SpecState.corrupt corruptSet; split <;> rfl

/-- The history-aware bookkeeping invariant: every pending input is attributed
to a `callG` event of the label history, and the corrupted set is exactly the
fold of D1-`corrupt` over that history. Both conjuncts are read off the rules:
`call` is written only by the `callG`-labelled rule, `F` only by `fail`. -/
structure CallInv (P : Parameters) (r : ℕ) (pre : List (Label P.n))
    (s : SpecState P.n) : Prop where
  /-- Every pending input has a `callG` event behind it. -/
  call_src : ∀ id b, s.call id = some b → Label.callG r id b ∈ pre
  /-- The corrupted set is the fold of the history's `fail` labels. -/
  F_eq : s.F = failSetOfList P pre

theorem CallInv.initial (P : Parameters) (r : ℕ) :
    CallInv P r [] (SpecState.initial P.n) where
  call_src := fun _ _ h => absurd h (by simp [SpecState.initial])
  F_eq := rfl

/-- **Bookkeeping-invariant preservation.** -/
theorem CallInv.step {pre : List (Label P.n)} {s : SpecState P.n} {l : Label P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n}
    (hI : CallInv P r pre s) (hstep : Step P r s l μ) (hs' : s' ∈ μ.support) :
    CallInv P r (pre ++ [l]) s' := by
  have mono : ∀ {l' : Label P.n}, l' ∈ pre → l' ∈ pre ++ [l] :=
    fun h => List.mem_append_left _ h
  cases hstep with
  | call id b h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨?_, ?_⟩
    · intro id' b' h_in
      replace h_in : Function.update s.call id (some b) id' = some b' := h_in
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_in
        obtain rfl := Option.some.inj h_in
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · rw [Function.update_of_ne h_eq] at h_in
        exact mono (hI.call_src id' b' h_in)
    · rw [failSetOfList_append]
      exact hI.F_eq
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨?_, ?_⟩
    · intro id' b' h_in
      rw [corrupt_call] at h_in
      exact mono (hI.call_src id' b' h_in)
    · rw [failSetOfList_append, corrupt_F, hI.F_eq]
      rfl
  | _ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨fun id' b' h_in => mono (hI.call_src id' b' h_in), by
      rw [failSetOfList_append]; exact hI.F_eq⟩

/-! ### The budget bound on support for the dissenting bit -/

/-- **The D15 count at the dissenting bit is unreachable.** Under unanimous
input `v`, every id the count `f + 1 ≤ #{id | call id = some (!v) ∨ id ∈ F}`
could draw on is corrupted at some stage of the trace: a caller of `!v` by the
unanimity hypothesis, an `F`-member because `F` is the trace-level fold. The
stages form a chain, so the whole set sits inside a single `failSet P t K`,
which the budget caps at `f`. -/
theorem supp_le_of_unanimous {t : Seq (Label P.n)} {v : Bool} {s : SpecState P.n}
    {j : ℕ} (hun : UnanimousInput P r v t)
    (hcall : ∀ id b, s.call id = some b → Label.callG r id b ∈ t)
    (hF : s.F = failSet P t j) :
    (Finset.univ.filter (fun id => s.call id = some (!v) ∨ id ∈ s.F)).card
      ≤ P.f := by
  classical
  have hall : ∀ id ∈ Finset.univ.filter
      (fun id => s.call id = some (!v) ∨ id ∈ s.F), ∃ k, id ∈ failSet P t k := by
    intro id hid
    rcases (Finset.mem_filter.mp hid).2 with hc | hm
    · rcases hun id (!v) (hcall id (!v) hc) with heq | hnc
      · exact absurd heq (by cases v <;> simp)
      · unfold NeverCorrupted at hnc
        obtain ⟨k, hk⟩ := not_forall.mp hnc
        exact ⟨k, not_not.mp hk⟩
    · exact ⟨j, hF ▸ hm⟩
  obtain ⟨K, hK⟩ := exists_uniform_prefix t _ hall
  exact le_trans (Finset.card_le_card (fun id hid => hK id hid))
    (failSet_card_le t K)

/-! ### The state-to-trace transfer -/

/-- **The transfer.** At every state of a genuine execution whose label list is
`labs` and whose trace is the external filter of `labs`, every pending input
has its `callG` event in the trace, and the corrupted set is the trace-level
fold at some stage. Both come from `CallInv` on the history `labs.take k`,
which the filter carries to the trace: it keeps every `fail` label, so the
fold is unchanged, and prefixes stay prefixes. -/
theorem trace_transfer {e : AlterSeq (SpecState P.n) (Label P.n)}
    {labs : List (Label P.n)} {t : Seq (Label P.n)} {p : Label P.n → Bool}
    (he : is_exec e (specInst P r))
    (h_map : e.trans.map Prod.fst = Seq.ofList labs)
    (hpfail : ∀ id : Fin P.n, p (.fail id) = true)
    (hpcall : ∀ (r' : ℕ) (id : Fin P.n) (b : Bool), p (.callG r' id b) = true)
    (h_t : Seq.ofList (labs.filter p) = t)
    {k : ℕ} {s : SpecState P.n} (hst : e.stateAt k = some s) :
    (∀ id b, s.call id = some b → Label.callG r id b ∈ t) ∧
      ∃ j, s.F = failSet P t j := by
  have hI := is_exec_induction_labels (sys := specInst P r) (CallInv P r)
    (CallInv.initial P r) (fun pre s l μ s' hI hstep hs' => hI.step hstep hs')
    he k s hst
  rw [AlterSeq.labelsUpTo_eq_take h_map k] at hI
  obtain ⟨m, hm⟩ : ∃ m, ((labs.take k).filter p).length = m := ⟨_, rfl⟩
  refine ⟨fun id b h => ?_, ⟨m, ?_⟩⟩
  · rw [← h_t, Seq_mem_ofList, List.mem_filter]
    exact ⟨List.mem_of_mem_take (hI.call_src id b h), hpcall r id b⟩
  · rw [hI.F_eq, ← failSetOfList_filter hpfail (labs.take k),
      take_filter_eq_take p labs hm, ← h_t, failSet_ofList]

/-! ### The surviving bit stays alive -/

/-- **Under unanimous input `v`, the bit `v` is alive at every state.** The
only rule that could exclude it is `bindUnset v`, whose D15 guard counts `f + 1`
supporters of `!v` — refuted by `supp_le_of_unanimous` at the very state where
the rule would fire. -/
theorem excluded_notMem_of_unanimous {e : AlterSeq (SpecState P.n) (Label P.n)}
    {t : Seq (Label P.n)} {v : Bool} (he : is_exec e (specInst P r))
    (hbr : ∀ (k : ℕ) (s : SpecState P.n), e.stateAt k = some s →
      (∀ id b, s.call id = some b → Label.callG r id b ∈ t) ∧
        ∃ j, s.F = failSet P t j)
    (hun : UnanimousInput P r v t) :
    ∀ k s, e.stateAt k = some s → v ∉ s.excluded := by
  intro k
  induction k with
  | zero =>
    intro s hs
    obtain rfl : e.init = s := Option.some.inj hs
    rw [← he.2]
    simp [specInst, SpecState.initial]
  | succ k ih =>
    intro s hs
    obtain ⟨⟨l, s''⟩, h_get, h_snd⟩ : ∃ q : Label P.n × SpecState P.n,
        e.trans.get? k = some q ∧ q.2 = s := by
      cases hg : e.trans.get? k with
      | none =>
        rw [show e.stateAt (k + 1) = (e.trans.get? k).map Prod.snd from rfl,
          hg] at hs
        exact absurd hs (by simp)
      | some q =>
        rw [show e.stateAt (k + 1) = (e.trans.get? k).map Prod.snd from rfl,
          hg] at hs
        exact ⟨q, rfl, Option.some.inj hs⟩
    obtain ⟨s₀, μ, h_state, h_step, h_supp⟩ := he.1 k l s'' h_get
    have hprev : v ∉ s₀.excluded := ih s₀ h_state
    obtain ⟨hcall, j, hF⟩ := hbr k s₀ h_state
    subst h_snd
    cases h_step with
    | bindUnset b hq hw hd0 =>
      rw [PMF.mem_support_pure_iff] at h_supp
      subst h_supp
      have hbv : b ≠ v := by
        intro hb
        subst hb
        have := supp_le_of_unanimous hun hcall hF
        omega
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hbv h.symm, hprev⟩
    | fail id =>
      rw [PMF.mem_support_pure_iff] at h_supp
      subst h_supp
      rw [corrupt_excluded]
      exact hprev
    | _ =>
      rw [PMF.mem_support_pure_iff] at h_supp
      subst h_supp
      exact hprev

/-! ### The return refutation -/

/-- Both D15 counts of a `C`-return: `f + 1` support at each bit. -/
private theorem retC_supp {s : SpecState P.n} {id : Fin P.n} {β : Bool}
    {μ : PMF (SpecState P.n)} (hstep : Step P r s (.retG r id .C β) μ)
    (c : Bool) :
    P.f + 1 ≤
      (Finset.univ.filter (fun id' => s.call id' = some c ∨ id' ∈ s.F)).card :=
  match hstep with
  | .retC _ _ _ _ hwT hwF _ _ =>
    by
    cases c with
    | false => exact hwF
    | true => exact hwT

/-- **Every return of a state where `v` is alive hands out `v`.** A
value-bearing return needs the other bit excluded, and `v` is not; a `C`-return
needs `f + 1` support at both bits, and the dissenting one is capped by the
budget. -/
theorem retG_value_of_unanimous {t : Seq (Label P.n)} {v β : Bool}
    {s : SpecState P.n} {id : Fin P.n} {o : GBCAOutput} {μ : PMF (SpecState P.n)}
    (hun : UnanimousInput P r v t)
    (hcall : ∀ id b, s.call id = some b → Label.callG r id b ∈ t)
    (hF : ∃ j, s.F = failSet P t j) (hlive : v ∉ s.excluded)
    (hstep : Step P r s (.retG r id o β) μ) : outValue o = some v := by
  have key : ∀ w : Bool, (!w) ∈ s.excluded → w = v := by
    intro w hexcluded
    by_contra hne
    have hflip : (!w) = v := by
      cases w <;> cases v <;> simp_all
    exact hlive (hflip ▸ hexcluded)
  cases o with
  | A w =>
    rw [key w (retG_value_guards hstep (outValue_A w)).2]
    rfl
  | B w =>
    rw [key w (retG_value_guards hstep (outValue_B w)).2]
    rfl
  | C =>
    exfalso
    obtain ⟨j, hFj⟩ := hF
    have h1 := retC_supp hstep (!v)
    have h2 := supp_le_of_unanimous hun hcall hFj
    omega

/-- Pulling a trace label back to an event of the witness execution. -/
private theorem event_of_mem_trace {e : AlterSeq (SpecState P.n) (Label P.n)}
    {labs : List (Label P.n)} {t : Seq (Label P.n)} {p : Label P.n → Bool}
    {l : Label P.n} (h_map : e.trans.map Prod.fst = Seq.ofList labs)
    (h_t : Seq.ofList (labs.filter p) = t) (h_mem : l ∈ t) :
    ∃ k s', e.trans.get? k = some (l, s') := by
  rw [← h_t, Seq_mem_ofList, List.mem_filter] at h_mem
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h_mem.1
  have hget : (e.trans.get? k).map Prod.fst = labs[k]? := by
    rw [← Seq.map_get?, h_map, Seq.ofList_get?]
  rw [hk] at hget
  cases hg : e.trans.get? k with
  | none => rw [hg] at hget; exact absurd hget (by simp)
  | some q =>
    rw [hg] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    exact ⟨k, q.2, by rw [hg, ← hget]⟩

/-- **The state behind a return of the trace.** Under unanimous input `v`,
every round-`r` return of a positive-probability trace fires, in a witness
execution for that trace, from a state whose pending inputs are `callG` events
of the trace, whose corrupted set is the trace-level fold at some stage, and at
which `v` is still alive. These are exactly the hypotheses the state-level
refutations take. -/
private theorem return_state_of_unanimous {v : Bool}
    {D : Seq (Label P.n) → ENNReal} (hD : D ∈ achievableTraceDists (specInst P r))
    {t : Seq (Label P.n)} (h_ne : D t ≠ 0) (hun : UnanimousInput P r v t)
    {id : Fin P.n} {o : GBCAOutput} {β : Bool} (h_mem : Label.retG r id o β ∈ t) :
    ∃ (s : SpecState P.n) (μ : PMF (SpecState P.n)),
      (∀ (id' : Fin P.n) (b : Bool),
          s.call id' = some b → Label.callG r id' b ∈ t) ∧
        (∃ j, s.F = failSet P t j) ∧ v ∉ s.excluded ∧
        Step P r s (.retG r id o β) μ := by
  obtain ⟨pe, h_init, h_D⟩ := hD
  rw [← h_D t] at h_ne
  obtain ⟨e, labs, h_exec, h_map, h_t⟩ :=
    exists_exec_of_traceProb_ne_zero_ord pe h_init t h_ne
  rw [Seq.ofList_filter] at h_t
  -- generalise the external-label filter to an opaque Boolean predicate
  obtain ⟨p, hpfail, hpcall, h_t⟩ : ∃ p : Label P.n → Bool,
      (∀ id : Fin P.n, p (.fail id) = true) ∧
      (∀ (r' : ℕ) (id : Fin P.n) (b : Bool), p (.callG r' id b) = true) ∧
      Seq.ofList (labs.filter p) = t :=
    ⟨_, fun id => by simp, fun r' id b => by simp, h_t⟩
  have hbr : ∀ (k : ℕ) (s : SpecState P.n), e.stateAt k = some s →
      (∀ id b, s.call id = some b → Label.callG r id b ∈ t) ∧
        ∃ j, s.F = failSet P t j :=
    fun k s hst => trace_transfer h_exec h_map hpfail hpcall h_t hst
  have halive := excluded_notMem_of_unanimous h_exec hbr hun
  obtain ⟨k, s', h_get⟩ := event_of_mem_trace h_map h_t h_mem
  obtain ⟨s, μ, h_state, h_step, -⟩ := h_exec.1 k _ _ h_get
  obtain ⟨hcall, hF⟩ := hbr k s h_state
  exact ⟨s, μ, hcall, hF, halive k s h_state, h_step⟩

/-- **Validity (safety half) of the GBCA specification instance**: on every
trace in the support of every achievable trace distribution of
`GBCA.specInst P r`, unanimous honest input `v` forces every round-`r` return
to hand out `v`. The instance cannot invent the other bit, and cannot fall
back on `C`. -/
theorem specInst_validity (P : Parameters) (r : ℕ) (v : Bool) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      UnanimousInput P r v t → ValidityTrace P r v t := by
  intro D hD t h_ne hun id o β h_mem
  obtain ⟨s, μ, hcall, hF, hlive, hstep⟩ :=
    return_state_of_unanimous hD h_ne hun h_mem
  exact retG_value_of_unanimous hun hcall hF hlive hstep

/-- **No `C`-return under unanimous honest input.** The `C`-return's D15
guards ask `f + 1` support at *both* bits; the dissenting one is capped by the
corruption budget. -/
theorem specInst_no_retC (P : Parameters) (r : ℕ) (v : Bool) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      UnanimousInput P r v t →
      ∀ (id : Fin P.n) (β : Bool), Label.retG r id .C β ∉ t := by
  intro D hD t h_ne hun id β h_mem
  have h := specInst_validity P r v D hD t h_ne hun id .C β h_mem
  simp at h

/-- **No `B`-return under unanimous honest input.** The B-half of Validity's
grade clause, the C-half being `specInst_no_retC`: under unanimity every
round-`r` return is an `A`-return of the input bit. A `B`-return hands out `v`
(`retG_value_of_unanimous`), and its D15 dissent guard then asks `f + 1`
support at the other bit, which the corruption budget caps at `f`. -/
theorem specInst_no_retB (P : Parameters) (r : ℕ) (v : Bool) :
    ∀ D ∈ achievableTraceDists (specInst P r), ∀ t, D t ≠ 0 →
      UnanimousInput P r v t →
      ∀ (id : Fin P.n) (w β : Bool), Label.retG r id (.B w) β ∉ t := by
  intro D hD t h_ne hun id w β h_mem
  obtain ⟨s, μ, hcall, ⟨j, hFj⟩, hlive, hstep⟩ :=
    return_state_of_unanimous hD h_ne hun h_mem
  obtain rfl : w = v := by
    have h := retG_value_of_unanimous hun hcall ⟨j, hFj⟩ hlive hstep
    simpa using h
  have h1 := retB_supp hstep
  have h2 := supp_le_of_unanimous hun hcall hFj
  omega

/-! ### Mechanical axiom check

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.GBCA.retG_value_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms retG_value_agree

/-- info: 'PLTS.ABA.GBCA.specInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_binding

/-- info: 'PLTS.ABA.GBCA.retG_bound_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms retG_bound_agree

/-- info: 'PLTS.ABA.GBCA.BindingTrace.value_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BindingTrace.value_agree

/-- info: 'PLTS.ABA.GBCA.excluded_card_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms excluded_card_le_one

/-- info: 'PLTS.ABA.GBCA.specInst_validity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_validity

/-- info: 'PLTS.ABA.GBCA.specInst_no_retC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_no_retC

/-- info: 'PLTS.ABA.GBCA.specInst_no_retB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_no_retB

/-- info: 'PLTS.ABA.GBCA.specInst_grade_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_grade_agree

end GBCA
end ABA
end PLTS
