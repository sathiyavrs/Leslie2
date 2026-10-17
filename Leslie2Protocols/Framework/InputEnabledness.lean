/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# Input-enabledness and compatibility

LeslieBP §1.3 and the simulations paper (Assumption 1 and Definition 2) restrict composition to
components whose labels are partitioned into input labels and output labels, whose input labels
are always enabled, and whose output labels are distinct. This file states the two conditions:

* `System.InputEnabled sys A`: every label of `A` has a transition of `sys` at every state. The
  silent label is a label like any other for the predicate, so `Silent.τ ∈ A` asks for a silent
  transition at every state.
* `InputOutputLabels`: the input labels and the output labels of a component, with
  `InputOutputLabels.Compatible` for two components that share no output label.

The combinators the compositions are built from preserve input-enabledness. Let `sys` be
input-enabled on `A`. Then `System.withIdle sys busy` is input-enabled on `A` and on every label
outside `busy` (`System.InputEnabled.withIdle`), and `System.mapIdle φ sys` on every label with
no image under `φ` and every label whose image lies in `A` (`System.InputEnabled.mapIdle`).
`System.parallel` is input-enabled on the intersection of the two sets
(`System.InputEnabled.parallel`), and `System.synchronisedProduct` on the intersection of all of
them (`System.InputEnabled.synchronisedProduct`). `System.family` is input-enabled on every
visible label no instance owns, broadcast or not, and on every label at which the instance owning
it is input-enabled (`System.InputEnabled.family`). `System.InputEnabled.mono` and
`System.InputEnabled.union` change the set of labels.
-/

namespace PLTS

variable {State Label : Type}

/-! ### The two conditions -/

/-- Every label of `A` has a transition at every state. -/
def System.InputEnabled (sys : System State Label) (A : Set Label) : Prop :=
  ∀ s, ∀ l ∈ A, ∃ μ, sys.step s l μ

/-- The input labels and the output labels of a component. -/
structure InputOutputLabels (Label : Type) where
  /-- The input labels of the component. -/
  inputLabels : Set Label
  /-- The output labels of the component. -/
  outputLabels : Set Label

/-- Two components are compatible when they share no output label (the simulations paper,
Definition 2). -/
def InputOutputLabels.Compatible (a b : InputOutputLabels Label) : Prop :=
  Disjoint a.outputLabels b.outputLabels

/-- Compatibility is symmetric. -/
theorem InputOutputLabels.Compatible.symm {a b : InputOutputLabels Label}
    (h : a.Compatible b) : b.Compatible a :=
  Disjoint.symm h

/-! ### Proving and changing the set of labels -/

namespace System.InputEnabled

variable {sys : System State Label} {A B : Set Label}

/-- Input-enabledness by cases on the label, then on the state. -/
theorem of_forall_step (h : ∀ l ∈ A, ∀ s, ∃ μ, sys.step s l μ) : sys.InputEnabled A :=
  fun s l hl => h l hl s

/-- Input-enabledness by a Dirac transition at every state. -/
theorem of_forall_LStep (h : ∀ l ∈ A, ∀ s, ∃ s', sys.LStep s l s') : sys.InputEnabled A :=
  fun s l hl =>
    let ⟨s', hs'⟩ := h l hl s
    ⟨PMF.pure s', hs'⟩

/-- Input-enabledness on `A` gives input-enabledness on every subset of `A`. -/
theorem mono (h : sys.InputEnabled A) (hBA : B ⊆ A) : sys.InputEnabled B :=
  fun s l hl => h s l (hBA hl)

/-- Input-enabledness on two sets gives input-enabledness on their union. -/
theorem union (hA : sys.InputEnabled A) (hB : sys.InputEnabled B) : sys.InputEnabled (A ∪ B) := by
  rintro s l (hl | hl)
  · exact hA s l hl
  · exact hB s l hl

end System.InputEnabled

/-- Every system is input-enabled on the empty set of labels. -/
theorem System.inputEnabled_empty (sys : System State Label) : sys.InputEnabled ∅ :=
  fun _ _ hl => absurd hl (Set.notMem_empty _)

/-! ### The combinators -/

/-- Idle padding is input-enabled on `A` and on every label outside `busy`. -/
theorem System.InputEnabled.withIdle {sys : System State Label} {A : Set Label}
    (h : sys.InputEnabled A) (busy : Label → Prop) :
    (sys.withIdle busy).InputEnabled (A ∪ {l | ¬ busy l}) := by
  rintro s l (hl | hl)
  · obtain ⟨μ, hμ⟩ := h s l hl
    exact ⟨μ, Or.inl hμ⟩
  · exact ⟨PMF.pure s, Or.inr ⟨hl, rfl⟩⟩

/-- A system read along a partial label map `φ` is input-enabled on every label with no image
under `φ` and on every label whose image lies in `A`. -/
theorem System.InputEnabled.mapIdle {S L L' : Type} {sys : System S L} {A : Set L}
    (h : sys.InputEnabled A) (φ : L' → Option L) :
    (sys.mapIdle φ).InputEnabled ({l' | φ l' = none} ∪ {l' | ∃ l ∈ A, φ l' = some l}) := by
  rintro s l' (hl' | ⟨l, hl, hφ⟩)
  · exact ⟨PMF.pure s, (System.mapIdle_step_none hl' _).mpr rfl⟩
  · obtain ⟨μ, hμ⟩ := h s l hl
    exact ⟨μ, (System.mapIdle_step_some hφ μ).mpr hμ⟩

variable [Silent Label]

/-- The binary composition is input-enabled on the intersection of the two sets: a visible
label moves both components, and the silent label moves the left one. -/
theorem System.InputEnabled.parallel {S₁ S₂ : Type} {sys₁ : System S₁ Label}
    {sys₂ : System S₂ Label} {A₁ A₂ : Set Label} (h₁ : sys₁.InputEnabled A₁)
    (h₂ : sys₂.InputEnabled A₂) : (sys₁.parallel sys₂).InputEnabled (A₁ ∩ A₂) := by
  rintro ⟨s₁, s₂⟩ l ⟨hl₁, hl₂⟩
  obtain ⟨μ₁, hμ₁⟩ := h₁ s₁ l hl₁
  by_cases hτ : l = Silent.τ
  · exact ⟨prodPMF μ₁ (PMF.pure s₂), Or.inr (Or.inl ⟨hτ, μ₁, hμ₁, rfl⟩)⟩
  · obtain ⟨μ₂, hμ₂⟩ := h₂ s₂ l hl₂
    exact ⟨prodPMF μ₁ μ₂, Or.inl ⟨hτ, μ₁, μ₂, hμ₁, hμ₂, rfl⟩⟩

section SynchronisedProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {StateOf : ι → Type}
  {sys : ∀ i, System (StateOf i) Label} {A : ι → Set Label}

/-- The full-synchronisation product is input-enabled on every visible label of the intersection
of the components' sets: every component moves. -/
theorem System.InputEnabled.synchronisedProduct_visible (h : ∀ i, (sys i).InputEnabled (A i)) :
    (System.synchronisedProduct sys).InputEnabled ((⋂ i, A i) \ {Silent.τ}) := by
  rintro s l ⟨hl, hτ⟩
  rw [Set.mem_iInter] at hl
  choose μ hμ using fun i => h i (s i) l (hl i)
  exact ⟨piPMF μ, Or.inl ⟨hτ, μ, hμ, rfl⟩⟩

/-- The full-synchronisation product of a nonempty family is input-enabled on the intersection
of the components' sets: a visible label moves every component, and the silent label moves one. -/
theorem System.InputEnabled.synchronisedProduct [Nonempty ι]
    (h : ∀ i, (sys i).InputEnabled (A i)) :
    (System.synchronisedProduct sys).InputEnabled (⋂ i, A i) := by
  intro s l hl
  by_cases hτ : l = Silent.τ
  · subst hτ
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨μi, hμi⟩ := h i (s i) Silent.τ (Set.mem_iInter.mp hl i)
    exact ⟨_, Or.inr ⟨rfl, i, μi, hμi, rfl⟩⟩
  · exact System.InputEnabled.synchronisedProduct_visible h s l ⟨hl, hτ⟩

end SynchronisedProduct

/-- An instance family is input-enabled on every visible label no instance owns, a broadcast
label or not, and on every label `l` owned by a round `r` with `l ∈ A r`, where the instance
`inst r` is input-enabled on `A r` at every state, the untouched instance included. -/
theorem System.InputEnabled.family {σ : Type} {inst : ℕ → System σ Label} {A : ℕ → Set Label}
    (h : ∀ r, (inst r).InputEnabled (A r)) (owns : Label → Option ℕ) (glob : Label → Prop)
    (act : Label → σ → σ) (initial : σ) :
    (System.family inst owns glob act initial).InputEnabled
      ({l | ¬ l = Silent.τ ∧ owns l = none} ∪ {l | ∃ r, owns l = some r ∧ l ∈ A r}) := by
  rintro g l (⟨hτ, hnowns⟩ | ⟨r, howns, hl⟩)
  · by_cases hg : glob l
    · exact ⟨_, Or.inr (Or.inr (Or.inl ⟨hτ, hnowns, hg, rfl⟩))⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨hτ, hnowns, hg, rfl⟩))⟩
  · obtain ⟨μ, hμ⟩ := h r (g r) l hl
    exact ⟨_, Or.inr (Or.inl ⟨r, howns, μ, hμ, rfl⟩)⟩

end PLTS
