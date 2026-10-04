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
of the messages the round exchanges, in which the three Byzantine call and return transitions and
the call loop of round `r` are separate labels. `specificationLabelMap` is the projection that
identifies them with the specification labels they stand for: a Byzantine call is a
call, a Byzantine return is a return, and the two call loops are calls, which the specification
takes on its input-enabledness transitions (D11). Every other extended label idles: the protocol
network's synchronisation and the coin's call and return are off the specification's interface.

`specificationOverRoundAlphabet` is the specification read back along `specificationLabelMap`. It
is the system a round is replaced by, and both graded-agreement implementations reach it:
ABDY22's round through `GBCA/ABDY/RefinesSpecification.lean` and the two-gather round through
`GBCA/AFW/RefinesSpecification.lean`. The call and return labels stay visible at this boundary,
and their authorisation is the surrounding network's business.

A weak run of the specification is read back over the extended alphabet along a section of
`specificationLabelMap`. `labelSection l₀ l` sends every label to its own copy on the left, except
`l₀`, which it sends to `l`. `weakLSilent_specificationOverRoundAlphabet` carries a silent weak run.
`weakLStep_specificationOverRoundAlphabet` carries a labelled one to any extended label projecting
to the same specification label, which is what answers a Byzantine call or return by the
specification's own call or return.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The specification read over the round's interface -/

/-- The projection of the extended alphabet onto the specification's alphabet. `M` is the type of
the messages a graded-agreement round exchanges. -/
def specificationLabelMap (n : ℕ) {M : Type} : ExtendedLabel n M → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.gbcaCallLoop r id b) => some (.callG r id b)
  | Sum.inr (.byzantineCallG r k b) => some (.callG r k b)
  | Sum.inr (.byzantineCallGLoop r k b) => some (.callG r k b)
  | Sum.inr (.byzantineRetG r k out bnd) => some (.retG r k out bnd)
  | Sum.inr _ => none

@[simp] theorem specificationLabelMap_inl {n : ℕ} {M : Type} (l : Label n) :
    specificationLabelMap (M := M) n (Sum.inl l) = some l := rfl

@[simp] theorem specificationLabelMap_gbcaCallLoop {n : ℕ} {M : Type} (r : ℕ) (id : Fin n)
    (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.gbcaCallLoop r id b)) = some (.callG r id b) := rfl

@[simp] theorem specificationLabelMap_byzantineCallG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n)
    (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.byzantineCallG r k b)) = some (.callG r k b) := rfl

@[simp] theorem specificationLabelMap_byzantineCallGLoop {n : ℕ} {M : Type} (r : ℕ) (k : Fin n)
    (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.byzantineCallGLoop r k b))
      = some (.callG r k b) := rfl

@[simp] theorem specificationLabelMap_byzantineRetG {n : ℕ} {M : Type} (r : ℕ) (k : Fin n)
    (out : GBCAOutput) (bnd : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.byzantineRetG r k out bnd))
      = some (.retG r k out bnd) := rfl

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

@[simp] theorem specificationLabelMap_byzantineRetW {n : ℕ} {M : Type} (r : ℕ) (k : Fin n)
    (b : Bool) :
    specificationLabelMap (M := M) n (Sum.inr (.byzantineRetW r k b)) = none := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specificationLabelMap_tau (n : ℕ) {M : Type} :
    specificationLabelMap n (Silent.τ : ExtendedLabel n M) = some (Silent.τ : Label n) := rfl

/-- Only the silent label projects to the silent label: a call or a return projects to a call or a
return port, and every other extended label idles. -/
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
read over the round's interface. -/
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

/-! ### Weak runs of the specification over the round's alphabet

A weak run of the specification is read back along a section of `specificationLabelMap`. The
section sends every label to its own copy on the left, except the one label the round's step
projects from, which it sends to the interface label the round took. This is what turns a
specification `callG` run into the matching run for a Byzantine call. -/

/-- The section of `specificationLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
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
