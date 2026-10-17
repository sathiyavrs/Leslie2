/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.GBCA.Specification

/-!
# The graded agreement specification over the round's alphabet

The graded agreement specification is over the shared alphabet `Label n`. The alphabet of a
graded-agreement round is the extended alphabet `Composition.ExtendedLabel n M`, over the type `M`
of the messages the round exchanges, in which a corrupted process's call of round `r` is a label of
its own, `byzantineCallG r k b`, output by the ABA network (D11). `specificationLabelMap` is the
projection that identifies it with the specification's call `callG r k b`, which the specification
takes on its call or on its input-enabledness loop. Every other network event idles: the
synchronisation of the protocol's networks and the coin's calls are off the specification's
interface.

`specificationOverRoundAlphabet` is the specification read back along `specificationLabelMap`. It
is the system a round is replaced by, and both graded-agreement implementations reach it:
ABDY22's round through `GBCA/ABDY/RefinesSpecification.lean` and the two-gather round through
`GBCA/AFW/RefinesSpecification.lean`. Its inputs at round `r` are the calls `callG r _ _` and
`byzantineCallG r _ _`, and its outputs the returns `retG r _ _` and the announcements
`boundG r _` (D29). It takes both calls and the corruption `fail` at every state
(`specificationOverRoundAlphabet_inputEnabled`).

A weak run of the specification is read back over the extended alphabet along a section of
`specificationLabelMap`. `labelSection l₀ l` sends every label to its own copy on the left, except
`l₀`, which it sends to `l`. `weakLSilent_specificationOverRoundAlphabet` carries a silent weak run.
`weakLStep_specificationOverRoundAlphabet` carries a labelled one to any extended label projecting
to the same specification label, which is what matches a corrupted process's call by the
specification's own call.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The specification read over the round's interface -/

/-- The projection of the extended alphabet onto the specification's alphabet: a shared label is
its own, a corrupted process's graded-agreement call is the specification's call, and every other
network event has no image. `M` is the type of the messages a graded-agreement round exchanges. -/
def specificationLabelMap (n : ℕ) {M : Type} : ExtendedLabel n M → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.byzantineCallG r k b) => some (.callG r k b)
  | Sum.inr _ => none

@[simp] theorem specificationLabelMap_inl {n : ℕ} {M : Type} (l : Label n) :
    specificationLabelMap (M := M) n (Sum.inl l) = some l := rfl

@[simp] theorem specificationLabelMap_byzantineCallG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n)
    (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.byzantineCallG r k b)) = some (.callG r k b) := rfl

@[simp] theorem specificationLabelMap_gbcaSend {n : ℕ} {M : Type} (r : ℕ) (j : Fin n) (m : M) :
    specificationLabelMap n (Sum.inr (.gbcaSend r j m)) = none := rfl

@[simp] theorem specificationLabelMap_gbcaDeliver {n : ℕ} {M : Type} (r : ℕ) (i j : Fin n)
    (m : M) :
    specificationLabelMap n (Sum.inr (.gbcaDeliver r i j m)) = none := rfl

@[simp] theorem specificationLabelMap_decidedRelay {n : ℕ} {M : Type} (j : Fin n) (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.decidedRelay j b)) = none := rfl

@[simp] theorem specificationLabelMap_decidedDeliver {n : ℕ} {M : Type} (i j : Fin n) (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.decidedDeliver i j b)) = none := rfl

@[simp] theorem specificationLabelMap_decidedSend {n : ℕ} {M : Type} (j : Fin n) (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.decidedSend j b)) = none := rfl

@[simp] theorem specificationLabelMap_byzantineCallW {n : ℕ} {M : Type} (r : ℕ) (k : Fin n) :
    specificationLabelMap (M := M) n (Sum.inr (.byzantineCallW r k)) = none := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specificationLabelMap_tau (n : ℕ) {M : Type} :
    specificationLabelMap n (Silent.τ : ExtendedLabel n M) = some (Silent.τ : Label n) := rfl

/-- Only the silent label projects to the silent label: a corrupted process's call projects to a
call, and every other network event has no image. -/
theorem specificationLabelMap_eq_tau {n : ℕ} {M : Type} {l : ExtendedLabel n M}
    (h : specificationLabelMap n l = some Label.tau) :
    l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e =>
    cases e
    case gbcaRoundEvent _ _ e => exact e.elim
    all_goals simp at h

/-- **The specification over the round's alphabet**: the round-`r` graded agreement specification
read over the round's interface. Its inputs are the calls `callG r _ _` and `byzantineCallG r _ _`,
and its outputs the returns `retG r _ _` and the announcements `boundG r _`. -/
noncomputable def specificationOverRoundAlphabet (P : Parameters) (M : Type) [DecidableEq M]
    (r : ℕ) : System (GBCA.SpecState P.n) (ExtendedLabel P.n M) :=
  (GBCA.specInst P r).mapIdle (specificationLabelMap P.n)

@[simp] theorem specificationOverRoundAlphabet_init (P : Parameters) (M : Type) [DecidableEq M]
    (r : ℕ) : (specificationOverRoundAlphabet P M r).init = GBCA.SpecState.initial P.n := rfl

/-- The specification over the round's alphabet is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverRoundAlphabet_isLTS (P : Parameters) (M : Type) [DecidableEq M] (r : ℕ) :
    (specificationOverRoundAlphabet P M r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.specInst_isLTS P r)

/-- **The specification over the round's alphabet is input-enabled** on the calls of round `r`,
on a corrupted process's calls of round `r` and on the corruptions. `specificationLabelMap` sends
each of these labels to an input of `GBCA.specInst` (`GBCA.specInst_inputEnabled`), and the
specification read back takes it on the transition the specification takes on the image
(`System.InputEnabled.mapIdle`). -/
theorem specificationOverRoundAlphabet_inputEnabled (P : Parameters) (M : Type) [DecidableEq M]
    (r : ℕ) :
    (specificationOverRoundAlphabet P M r).InputEnabled
      {l | (∃ id b, l = Sum.inl (.callG r id b)) ∨ (∃ k b, l = Sum.inr (.byzantineCallG r k b)) ∨
        ∃ id, l = Sum.inl (.fail id)} := by
  refine ((specInst_inputEnabled P r).mapIdle (specificationLabelMap P.n)).mono ?_
  rintro l (⟨id, b, rfl⟩ | ⟨k, b, rfl⟩ | ⟨id, rfl⟩)
  · exact Or.inr ⟨.callG r id b, Or.inl ⟨id, b, rfl⟩, rfl⟩
  · exact Or.inr ⟨.callG r k b, Or.inl ⟨k, b, rfl⟩, rfl⟩
  · exact Or.inr ⟨.fail id, Or.inr ⟨id, rfl⟩, rfl⟩

/-! ### Weak runs of the specification over the round's alphabet

A weak run of the specification is read back along a section of `specificationLabelMap`. The
section sends every label to its own copy on the left, except the one label the round's step
projects from, which it sends to the interface label the round took. This is what turns a
specification `callG` run into the matching run for a corrupted process's call. -/

/-- The section of `specificationLabelMap` that sends the specification label `l₀` to the
interface label `l`. -/
def labelSection {n : ℕ} {M : Type} (l₀ : Label n) (l : ExtendedLabel n M) :
    Label n → ExtendedLabel n M :=
  fun x => if x = l₀ then l else Sum.inl x

theorem specificationLabelMap_labelSection {n : ℕ} {M : Type} {l₀ : Label n}
    {l : ExtendedLabel n M}
    (hl : specificationLabelMap n l = some l₀) (x : Label n) :
    specificationLabelMap n (labelSection l₀ l x) = some x := by
  unfold labelSection
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specificationLabelMap_inl]

theorem labelSection_tau {n : ℕ} {M : Type} {l₀ : Label n} {l : ExtendedLabel n M}
    (hl : specificationLabelMap n l = some l₀) (hl₀ : l₀ ≠ (Silent.τ : Label n)) (x : Label n) :
    labelSection l₀ l x = (Silent.τ : ExtendedLabel n M) ↔ x = (Silent.τ : Label n) := by
  unfold labelSection
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Label n) := by
        rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    simp [Label.silent_eq]

/-- A silent weak run of the specification is a silent weak run of the specification over the
round's alphabet. -/
theorem weakLSilent_specificationOverRoundAlphabet (P : Parameters) (M : Type) [DecidableEq M]
    (r : ℕ) {s s' : GBCA.SpecState P.n} (h : (GBCA.specInst P r).weakLSilent s s') :
    (specificationOverRoundAlphabet P M r).weakLSilent s s' :=
  System.weakLSilent_mapIdle Sum.inl (fun _ => rfl) (fun _ => by simp) h

/-- A labelled weak run of the specification is a weak run of the specification over the round's
alphabet at any interface label projecting to the same specification label. -/
theorem weakLStep_specificationOverRoundAlphabet (P : Parameters) (M : Type) [DecidableEq M]
    (r : ℕ) {s s' : GBCA.SpecState P.n} {l₀ : Label P.n} {l : ExtendedLabel P.n M}
    (hl₀ : l₀ ≠ (Silent.τ : Label P.n)) (hl : specificationLabelMap P.n l = some l₀)
    (h : (GBCA.specInst P r).weakLStep s l₀ s') :
    (specificationOverRoundAlphabet P M r).weakLStep s l s' :=
  System.weakLStep_mapIdle (labelSection l₀ l) (specificationLabelMap_labelSection hl)
    (labelSection_tau hl hl₀)
    (by simp [labelSection]) h

end GBCA
end ABA
end PLTS
