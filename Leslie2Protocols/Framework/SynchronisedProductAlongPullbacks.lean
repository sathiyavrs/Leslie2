/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The synchronised product of a family read along pullbacks

A family of systems, each read along its own pullback of the shared alphabet
(`System.mapIdle`), under the synchronised product (`System.synchronisedProduct`).
A label with no image at a component leaves that component unchanged, so a label
naming one component moves that component alone. On a visible label every
component steps, and the joint distribution is the Dirac of the family of the
components' targets. A silent transition of the product is a silent transition
of exactly one component, on the label its pullback carries `τ` to.

`dirac_steps_update` is the pointwise reading of such a family of Dirac steps:
one component's step beside every other component's stutter.
-/

namespace PLTS
namespace System

/-! ### The synchronised product of the components

The `n` components, each read along its own pullback, under full
synchronisation. A component whose pullback has no image at the label is
unchanged, so a label naming one component moves that component alone. -/

section SynchronisedProduct
variable {n : ℕ} {B Lbl Λ : Type} [Silent Λ] {A : ∀ _ : Fin n, System B Lbl}
  {φ : Fin n → Λ → Option Lbl} {a a' : ∀ _ : Fin n, B} {L : Λ}
  {μ : PMF (∀ _ : Fin n, B)}

omit [Silent Λ] in
/-- A component whose pullback has no image at the label is unchanged. -/
theorem mapIdle_unchanged {A₀ : System B Lbl} {ψ : Λ → Option Lbl} {c : B} (hψ : ψ L = none) :
    (A₀.mapIdle ψ).step c L (PMF.pure c) :=
  (System.mapIdle_step_none hψ _).mpr rfl

/-- A transition of the synchronised product on a visible label: every
component steps, and the joint distribution is Dirac. -/
theorem synchronisedProductMapIdle_inversion (hA : ∀ k, (A k).IsLTS) (hL : L ≠ Silent.τ)
    (h : (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a L μ) :
    ∃ a' : ∀ _ : Fin n, B, μ = PMF.pure a' ∧
      ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨hτ, -⟩
  · have hx : ∀ k, ∃ c, μ_ k = PMF.pure c :=
      fun k => System.mapIdle_isLTS (φ k) (hA k) _ _ _ (hall k)
    choose y hy using hx
    refine ⟨y, ?_, fun k => ?_⟩
    · rw [show μ_ = fun k => PMF.pure (y k) from funext hy]
      exact piPMF_pure y
    · rw [← hy k]; exact hall k
  · exact absurd hτ hL

/-- Build a transition of the synchronised product from per-component
Dirac steps. -/
theorem synchronisedProductMapIdle_pure (hL : L ≠ Silent.τ)
    (h : ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k))) :
    (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a L (PMF.pure a') := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hL, fun k => PMF.pure (a' k), h, (piPMF_pure a').symm⟩

/-- On a label no pullback has an image at, the synchronised product is unchanged. -/
theorem synchronisedProductMapIdle_none (hL : L ≠ Silent.τ) (hφ : ∀ k, φ k L = none) :
    (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a L (PMF.pure a) :=
  synchronisedProductMapIdle_pure hL fun k => mapIdle_unchanged (hφ k)

/-- A silent transition of the synchronised product is a silent transition of
exactly one component. -/
theorem synchronisedProductMapIdle_tau_inversion [Silent Lbl] (hA : ∀ k, (A k).IsLTS)
    (hτ : ∀ k, φ k (Silent.τ : Λ) = some (Silent.τ : Lbl))
    (h : (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a (Silent.τ : Λ) μ) :
    ∃ (k : Fin n) (c : B), μ = PMF.pure (Function.update a k c) ∧
      (A k).step (a k) (Silent.τ : Lbl) (PMF.pure c) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨hne, -⟩ | ⟨-, k, μ_k, hstep, rfl⟩
  · exact absurd rfl hne
  · rw [System.mapIdle_step_some (hτ k)] at hstep
    obtain ⟨c, rfl⟩ := hA k _ _ _ hstep
    exact ⟨k, c, by rw [piPMF_update_pure, PMF.pure_map], hstep⟩

/-- A silent transition of one component is a silent transition of the
synchronised product. -/
theorem synchronisedProductMapIdle_tau_step [Silent Lbl] {k : Fin n} {c : B}
    (hτ : φ k (Silent.τ : Λ) = some (Silent.τ : Lbl))
    (h : (A k).step (a k) (Silent.τ : Lbl) (PMF.pure c)) :
    (System.synchronisedProduct (fun k => (A k).mapIdle (φ k))).step a (Silent.τ : Λ)
      (PMF.pure (Function.update a k c)) := by
  rw [System.synchronisedProduct_step]
  refine Or.inr ⟨rfl, k, PMF.pure c, ?_, ?_⟩
  · rw [System.mapIdle_step_some hτ]; exact h
  · rw [piPMF_update_pure, PMF.pure_map]

end SynchronisedProduct
/-! ### One component's step, by the pullback's value -/

section ComponentAlongPullback
variable {S B Lbl Λ : Type} {A₀ : System S Lbl} {ψ : Λ → Option Lbl} {s s' : S} {L : Λ}

/-- A component whose pullback has no image at the label is unchanged. -/
theorem mapIdle_eq_of_step_none (hψ : ψ L = none)
    (h : (A₀.mapIdle ψ).step s L (PMF.pure s')) : s' = s :=
  PMF.pure_injective ((System.mapIdle_step_none hψ _).mp h)

/-- A component whose pullback has an image at the label steps on that
image. -/
theorem step_of_mapIdle_step {l₀ : Lbl} (hψ : ψ L = some l₀)
    (h : (A₀.mapIdle ψ).step s L (PMF.pure s')) : A₀.step s l₀ (PMF.pure s') :=
  (System.mapIdle_step_some hψ _).mp h

/-- A step of a component is a transition read along the pullback. -/
theorem mapIdle_step_of_step {l₀ : Lbl} (hψ : ψ L = some l₀) (h : A₀.step s l₀ (PMF.pure s')) :
    (A₀.mapIdle ψ).step s L (PMF.pure s') :=
  (System.mapIdle_step_some hψ _).mpr h

variable {n : ℕ} {A : ∀ _ : Fin n, System B Lbl} {φ : Fin n → Λ → Option Lbl}
  {a a' : ∀ _ : Fin n, B} {k : Fin n}

/-- A label naming one component moves that component alone. -/
theorem mapIdle_step_update {l₀ : Lbl} {c : B} (hk : φ k L = some l₀)
    (hother : ∀ k', k' ≠ k → φ k' L = none) (h : (A k).step (a k) l₀ (PMF.pure c)) :
    ∀ k', ((A k').mapIdle (φ k')).step (a k') L (PMF.pure (Function.update a k c k')) := by
  intro k'
  by_cases hkk : k' = k
  · subst hkk; rw [Function.update_self, System.mapIdle_step_some hk]; exact h
  · rw [Function.update_of_ne hkk]; exact mapIdle_unchanged (hother k' hkk)

/-- A label with an image at every component moves them all. -/
theorem mapIdle_step_all {l₀ : Fin n → Lbl} (hk : ∀ k, φ k L = some (l₀ k))
    (h : ∀ k, (A k).step (a k) (l₀ k) (PMF.pure (a' k))) :
    ∀ k, ((A k).mapIdle (φ k)).step (a k) L (PMF.pure (a' k)) :=
  fun k => (System.mapIdle_step_some (hk k) _).mpr (h k)

end ComponentAlongPullback
end System

/-! ### The family of Dirac steps at an update of one component -/

section DiracStepsAtUpdate
variable {ι S L : Type} [DecidableEq ι] {Step : ι → S → L → PMF S → Prop}
  {u : ι → S} {j : ι} {s : S} {l : L}

/-- One component's Dirac step beside the Dirac stutter of every other
component: every component steps into the family updated at the acting one. -/
theorem dirac_steps_update (hj : Step j (u j) l (PMF.pure s))
    (hother : ∀ i, i ≠ j → Step i (u i) l (PMF.pure (u i))) :
    ∀ i, Step i (u i) l (PMF.pure (Function.update u j s i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hother i hi

end DiracStepsAtUpdate
end PLTS
