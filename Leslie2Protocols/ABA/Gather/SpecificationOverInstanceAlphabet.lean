/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Composition

/-!
# The gather specification over the instance's interface

The gather specification speaks `Label n X`. The gather instance speaks
`InstanceLabel n X`, in which the call loop is a label of its own.
`specificationLabelMap` sends the call loop to the call it stands for and every
other interface label to its own copy. `specificationOverInstanceAlphabet` is the
specification read along that map: the specification's own rows at the labels the
map carries, and a Dirac self-loop at the rest. It is an LTS.

A weak run of the specification is read back over the interface along a section of
`specificationLabelMap`. `labelSection` is the left injection, the interface label a
specification label sits at. `sectionAt l₀ l` answers the interface label `l` over the
specification label `l₀` and agrees with `labelSection` elsewhere.
`weakLSilent_specificationOverInstanceAlphabet` carries a silent weak run;
`weakLStep_specificationOverInstanceAlphabet` carries a labelled one to any interface
label over the same specification label.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type}

/-! ### The specification read over the instance's interface

The specification speaks `Label n X`; the instance speaks `InstanceLabel n X`, in which
the call loop is a label of its own. `specificationLabelMap` identifies the loop with the
specification label it stands for, so that the specification's own loop row
answers it. -/

/-- The projection of the interface alphabet onto the specification's
alphabet. -/
def specificationLabelMap (n : ℕ) (X : Type) : InstanceLabel n X → Option (Label n X)
  | Sum.inl l => some l
  | Sum.inr (.callLoop id x) => some (.call id x)

@[simp] theorem specificationLabelMap_inl {n : ℕ} (l : Label n X) : specificationLabelMap n X
  (Sum.inl l) = some l := rfl

@[simp] theorem specificationLabelMap_callLoop {n : ℕ} (id : Fin n) (x : X) :
    specificationLabelMap n X (Sum.inr (.callLoop id x)) = some (.call id x) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specificationLabelMap_tau (n : ℕ) (X : Type) :
    specificationLabelMap n X (Silent.τ : InstanceLabel n X) = some (Silent.τ : Label n X) := rfl

/-- Only the silent label projects to the silent label: the call loop projects
to the call. -/
theorem specificationLabelMap_eq_tau {n : ℕ} {l : InstanceLabel n X}
    (h : specificationLabelMap n X l = some Label.tau) : l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e; simp at h

/-- Every interface label carries a specification label. -/
theorem specificationLabelMap_isSome {n : ℕ} (l : InstanceLabel n X) : ∃ l₀,
  specificationLabelMap n X l = some l₀ := by
    cases l with
  | inl l₀ => exact ⟨l₀, rfl⟩
  | inr e => cases e; exact ⟨_, rfl⟩

/-- **The lifted specification**: the gather specification read over the
instance's interface. -/
noncomputable def specificationOverInstanceAlphabet (P : Parameters) (X : Type) [DecidableEq X] :
    System (SpecState P.n X) (InstanceLabel P.n X) :=
  (specInst P X).mapIdle (specificationLabelMap P.n X)

@[simp] theorem specificationOverInstanceAlphabet_init (P : Parameters) [DecidableEq X] :
    (specificationOverInstanceAlphabet P X).init = SpecState.initial P.n X := rfl

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverInstanceAlphabet_isLTS (P : Parameters) [DecidableEq X] :
  (specificationOverInstanceAlphabet P X).IsLTS :=
  System.mapIdle_isLTS _ (specInst_isLTS P)

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `specificationLabelMap`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the instance
actually took. -/

/-- The left injection: the interface label a specification label sits at. -/
def labelSection {n : ℕ} : Label n X → InstanceLabel n X := Sum.inl

open scoped Classical in
/-- The section of `specificationLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
noncomputable def sectionAt {n : ℕ} (l₀ : Label n X) (l : InstanceLabel n X) : Label n X →
  InstanceLabel n X :=
  fun x => if x = l₀ then l else labelSection x

@[simp] theorem specificationLabelMap_labelSection {n : ℕ} (x : Label n X) : specificationLabelMap n
  X (labelSection x) = some x := rfl

/-- The left injection reflects the silent label. -/
theorem labelSection_eq_tau {n : ℕ} (x : Label n X) :
    (labelSection x : InstanceLabel n X) = (Silent.τ : InstanceLabel n X) ↔ x =
    (Silent.τ : Label n X) :=
  inl_eq_tau_iff x

theorem specificationLabelMap_sectionAt {n : ℕ} {l₀ : Label n X} {l : InstanceLabel n X}
    (hl : specificationLabelMap n X l = some l₀) (x : Label n X) : specificationLabelMap n X
      (sectionAt l₀ l x) = some x := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specificationLabelMap_labelSection]

theorem sectionAt_tau {n : ℕ} {l₀ : Label n X} {l : InstanceLabel n X}
    (hl : specificationLabelMap n X l = some l₀) (hl₀ : l₀ ≠ (Silent.τ : Label n X)) (x : Label n X)
    : sectionAt l₀ l x = (Silent.τ : InstanceLabel n X) ↔ x = (Silent.τ : Label n X) := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Label n X) := by
        rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    exact labelSection_eq_tau x

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_specificationOverInstanceAlphabet [DecidableEq X] (P : Parameters)
    {s s' : SpecState P.n X} (h : (specInst P X).weakLSilent s s') :
    (specificationOverInstanceAlphabet P X).weakLSilent s s' :=
  System.weakLSilent_mapIdle labelSection (fun _ => rfl) (fun x => labelSection_eq_tau x) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_specificationOverInstanceAlphabet [DecidableEq X] (P : Parameters)
    {s s' : SpecState P.n X} {l₀ : Label P.n X} {l : InstanceLabel P.n X}
    (hl₀ : l₀ ≠ (Silent.τ : Label P.n X)) (hl : specificationLabelMap P.n X l = some l₀)
    (h : (specInst P X).weakLStep s l₀ s') :
    (specificationOverInstanceAlphabet P X).weakLStep s l s' :=
  System.weakLStep_mapIdle (sectionAt l₀ l) (specificationLabelMap_sectionAt hl) (sectionAt_tau hl
    hl₀)
    (by simp [sectionAt]) h

end Gather
end ABA
end PLTS
