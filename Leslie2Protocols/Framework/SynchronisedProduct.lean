/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.ProcessAlgebra.Composition
import Leslie2.Systems.LTS

/-!
# Full-synchronisation product of a finite family

`System.synchronisedProduct sys` composes a finite family `sys i : System (State i) Label`
over one shared alphabet under **full synchronisation**: on every visible label
*all* components step simultaneously on that label, and the joint next-state
distribution is the independent product `piPMF`. The silent label `τ` is the sole
exception — it is interleaved, exactly one component moving while the others hold
their state, as in `System.parallel`.

This is the dual of `System.interleave` (in `ProcessAlgebra/Composition.lean`),
which synchronises nothing; the sync-set composition `∥_S` sits between the two
and is recovered from `synchronisedProduct` by the **rendezvous idiom**:

* every component carries idle self-loops (`System.withIdle`, in
  `Framework/LoopsAndInstanceFamilies.lean`) on the labels it does not own, so a component that
  is not a participant answers a foreign handshake by unchanged;
* a label owned by exactly two components is then a communication: it moves those
  two and leaves every other component where it is;
* a label owned by no component is blocked — no component offers it, so the
  conjunction over all components is unsatisfiable and the product has no such
  transition.

Ownership is thus expressed on the components, not on the product operator, which
keeps the operator itself uniform: a single conjunction over the whole family.

Forward simulation is a congruence for the product
(`ForwardSimulation.synchronisedProduct`, `Framework/Congruence.lean`): per-component
simulations lift to the pointwise relation on the product, so a component of a
synchronised product may be replaced by a system that simulates it, as a factor of
`System.parallel` may. Contextual refinement therefore covers contexts built from
`synchronisedProduct` as well.

Full synchronisation preserves `System.IsLTS` (`System.synchronisedProduct_isLTS`): a
product of Diracs is the Dirac on the tuple of their points (`piPMF_pure`), and a
single-coordinate update of an all-Dirac family is a Dirac too
(`piPMF_update_pure`). The binary composition `System.parallel` preserves it for
the same reason, through the two-factor `prodPMF_pure_pure`
(`System.parallel_isLTS`).
-/

namespace PLTS

/-! ### Products of Diracs -/

/-- Collapse a product of two Dirac distributions to a single Dirac. -/
theorem prodPMF_pure_pure {α β : Type*} (a : α) (b : β) :
    prodPMF (PMF.pure a) (PMF.pure b) = PMF.pure (a, b) := by
  rw [prodPMF_pure_left, PMF.pure_map]

/-- The mass a `prodPMF` with Dirac left factor puts on `(a, y)` is `ν y` (used
to read off a probabilistic factor's mass through idle product factors). -/
theorem prodPMF_pure_left_apply {α β : Type*}
    (a : α) (ν : PMF β) (y : β) : prodPMF (PMF.pure a) ν (a, y) = ν y := by
  rw [prodPMF_pure_left, PMF.map_apply]
  refine (tsum_eq_single y ?_).trans ?_
  · intro b hb
    simp only [Prod.mk.injEq, true_and, ite_eq_right_iff]
    exact fun h => absurd h (Ne.symm hb)
  · simp

/-- A product of two Dirac factors beside a third distribution. -/
theorem prodPMF_two_pure_factors {α β γ : Type*} (a : α) (b : β) (ν : PMF γ) :
    prodPMF (PMF.pure a) (prodPMF (PMF.pure b) ν) = ν.map (fun c => (a, b, c)) := by
  rw [prodPMF_pure_left, prodPMF_pure_left, PMF.map_comp]
  rfl

/-- A product of three Dirac factors beside a fourth distribution. -/
theorem prodPMF_three_pure_factors {α β γ δ : Type*} (a : α) (b : β) (c : γ) (ν : PMF δ) :
    prodPMF (PMF.pure a) (prodPMF (PMF.pure b) (prodPMF (PMF.pure c) ν)) =
      ν.map (fun d => (a, b, c, d)) := by
  rw [prodPMF_pure_left, prodPMF_two_pure_factors, PMF.map_comp]
  rfl

/-- Pushing an injective `f` forward, the mass at `f x` is the mass at `x`. -/
theorem map_apply_inj {α β : Type*} {f : α → β} (hf : Function.Injective f)
    (p : PMF α) (x : α) : (p.map f) (f x) = p x := by
  rw [PMF.map_apply, tsum_eq_single x]
  · rw [if_pos rfl]
  · intro a ha; rw [if_neg]; exact fun h => ha (hf h.symm)

/-! ### The independent product of Diracs -/

section ProductOfDiracs
variable {ι : Type} [Fintype ι] {α : ι → Type}

/-- The independent product of Diracs is the Dirac on the tuple of their points. -/
theorem piPMF_pure (x : ∀ i, α i) : piPMF (fun i => PMF.pure (x i)) = PMF.pure x := by
  classical
  ext f
  simp only [piPMF_apply, PMF.pure_apply]
  by_cases hf : f = x
  · subst hf; simp
  · rw [if_neg hf]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end ProductOfDiracs
/-! ### The full-synchronisation product -/

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι] {State : ι → Type} {Label : Type} [Silent Label]

namespace System

/-- **Full-synchronisation composition** of a finite family of PLTS over a common
label alphabet. On a visible label `l ≠ τ` *every* component steps simultaneously
on `l`, and the joint next-state distribution is the independent product `piPMF`
of the per-component distributions; on the silent label `τ` exactly one component
steps and all the others hold their state (the `Function.update` of the all-Dirac
family used by `System.interleave`). -/
def synchronisedProduct (sys : ∀ i, System (State i) Label) :
    System (∀ i, State i) Label where
  init := fun i => (sys i).init
  step s l μ :=
    -- Synchronised visible step: `l ≠ τ` and every component steps on `l`.
    (l ≠ Silent.τ ∧ ∃ μ_ : ∀ i, PMF (State i),
      (∀ i, (sys i).step (s i) l (μ_ i)) ∧ μ = piPMF μ_) ∨
    -- Interleaved `τ`-step: one component steps, the others hold their state.
    (l = Silent.τ ∧ ∃ (i : ι) (μ_i : PMF (State i)),
      (sys i).step (s i) Silent.τ μ_i ∧
      μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i))

@[simp] theorem synchronisedProduct_init (sys : ∀ i, System (State i) Label) :
    (synchronisedProduct sys).init = fun i => (sys i).init := rfl

@[simp] theorem synchronisedProduct_step (sys : ∀ i, System (State i) Label) (s : ∀ i, State i)
    (l : Label) (μ : PMF (∀ i, State i)) :
    (synchronisedProduct sys).step s l μ ↔
      (l ≠ Silent.τ ∧ ∃ μ_ : ∀ i, PMF (State i),
        (∀ i, (sys i).step (s i) l (μ_ i)) ∧ μ = piPMF μ_) ∨
      (l = Silent.τ ∧ ∃ (i : ι) (μ_i : PMF (State i)),
        (sys i).step (s i) Silent.τ μ_i ∧
        μ = piPMF (Function.update (fun j => PMF.pure (s j)) i μ_i)) :=
  Iff.rfl

/-- A full-synchronisation product of LTS components is an LTS: the synchronised
distribution is a product of Diracs, and the interleaved one a single-coordinate
update of an all-Dirac family. -/
theorem synchronisedProduct_isLTS {sys : ∀ i, System (State i) Label}
    (h : ∀ i, (sys i).IsLTS) : (synchronisedProduct sys).IsLTS := by
  classical
  rintro s l μ (⟨-, μ_, hstep, rfl⟩ | ⟨-, i, μ_i, hstep, rfl⟩)
  · choose x hx using fun i => h i (s i) l (μ_ i) (hstep i)
    exact ⟨x, by rw [funext hx]; exact piPMF_pure x⟩
  · obtain ⟨x, rfl⟩ := h i (s i) Silent.τ μ_i hstep
    exact ⟨Function.update s i x, by rw [piPMF_update_pure, PMF.pure_map]⟩

end System

end Family

/-! ### Determinacy of a binary composition

Binary parallel composition preserves the LTS property, the companion of
`System.synchronisedProduct_isLTS`: a synchronised step is a product of two Diracs and
an interleaved one holds the other component's state. -/

/-- **A binary composition of LTS components is an LTS.** -/
theorem System.parallel_isLTS {S₁ S₂ L : Type} [Silent L] {sys₁ : System S₁ L}
    {sys₂ : System S₂ L} (h₁ : sys₁.IsLTS) (h₂ : sys₂.IsLTS) :
    (sys₁.parallel sys₂).IsLTS := by
  rintro ⟨a, b⟩ l μ hstep
  rw [System.parallel_step] at hstep
  rcases hstep with ⟨-, μ₁, μ₂, ha, hb, rfl⟩ | ⟨-, μ₁, ha, rfl⟩ | ⟨-, μ₂, hb, rfl⟩
  · obtain ⟨a', rfl⟩ := h₁ _ _ _ ha
    obtain ⟨b', rfl⟩ := h₂ _ _ _ hb
    exact ⟨(a', b'), prodPMF_pure_pure a' b'⟩
  · obtain ⟨a', rfl⟩ := h₁ _ _ _ ha
    exact ⟨(a', b), prodPMF_pure_pure a' b⟩
  · obtain ⟨b', rfl⟩ := h₂ _ _ _ hb
    exact ⟨(a, b'), prodPMF_pure_pure a b'⟩

end PLTS
