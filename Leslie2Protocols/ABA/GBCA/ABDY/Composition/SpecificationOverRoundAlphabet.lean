/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Composition.Instance

/-!
# The graded agreement specification over the round's alphabet

The graded agreement specification speaks the shared alphabet `Label n`. The round instance speaks
the extended alphabet `ExtendedLabel n`, in which the three Byzantine handshake rows and the call
loop of round `r` are separate labels. `gbcaLabelMap` is the projection that identifies them with
the specification labels they stand for: a Byzantine call is a call, a Byzantine return is a
return, and the two call loops are calls, which the specification takes on its input-enabledness
row (D11). Every other extended label idles: the protocol network's rendezvous and the coin
handshake rows are off the specification's interface.

`specificationOverRoundAlphabet` is the specification read back along `gbcaLabelMap`. It is the
system that replaces the round instance. The handshake-row labels stay visible at this boundary,
and their authorisation is the surrounding network's business.

A weak run of the specification is read back over the extended alphabet along a section of
`gbcaLabelMap`. `labelSection l₀ l` sends every label to its own copy on the left, except `l₀`,
which it sends to `l`. `weakLSilent_specificationOverRoundAlphabet` carries a silent weak run.
`weakLStep_specificationOverRoundAlphabet` carries a labelled one to any extended label projecting
to the same specification label, which is what answers a Byzantine handshake row by the
specification's own call or return row.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation Composition

/-! ### The specification read over the instance's interface

The graded agreement specification speaks the shared alphabet `Label n`; the
instance speaks the extended alphabet `ExtendedLabel n`, in which the three Byzantine
handshake rows and the call loop of round `r` are separate labels. `gbcaLabelMap` is the
projection that identifies them with the specification labels they stand for:
a Byzantine call is a call, a Byzantine return is a return, and the two
call loops are calls, which the specification takes on its input-enabledness
row. Every other extended label — the protocol network's rendezvous, the coin
handshake rows — are off the specification's interface and idles.

The lifted specification `specificationOverRoundAlphabet` is the specification read back along
`gbcaLabelMap`. It is what the instance is replaced by: the handshake-row labels stay visible
at this boundary, and their authorisation is the surrounding network's business
(D11). -/

/-- The projection of the extended alphabet onto the specification's alphabet.
-/
def gbcaLabelMap (n : ℕ) : ExtendedLabel n → Option (Label n)
  | Sum.inl l => some l
  | Sum.inr (.gbcaCallLoop r id b) => some (.callG r id b)
  | Sum.inr (.byzantineCallG r k b) => some (.callG r k b)
  | Sum.inr (.byzantineCallGLoop r k b) => some (.callG r k b)
  | Sum.inr (.byzantineRetG r k out bnd) => some (.retG r k out bnd)
  | Sum.inr _ => none

@[simp] theorem gbcaLabelMap_inl {n : ℕ} (l : Label n) : gbcaLabelMap n (Sum.inl l) = some l := rfl

@[simp] theorem gbcaLabelMap_gbcaCallLoop {n : ℕ} (r : ℕ) (id : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.gbcaCallLoop r id b)) = some (.callG r id b) := rfl

@[simp] theorem gbcaLabelMap_byzantineCallG {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineCallG r k b)) = some (.callG r k b) := rfl

@[simp] theorem gbcaLabelMap_byzantineCallGLoop {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineCallGLoop r k b)) = some (.callG r k b) := rfl

@[simp] theorem gbcaLabelMap_byzantineRetG {n : ℕ} (r : ℕ) (k : Fin n) (out : GBCAOutput)
    (bnd : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineRetG r k out bnd)) = some (.retG r k out bnd) := rfl

@[simp] theorem gbcaLabelMap_gbcaSend {n : ℕ} (r : ℕ) (j : Fin n) (m : GBCA.ByABDY.Message) :
    gbcaLabelMap n (Sum.inr (.gbcaSend r j m)) = none := rfl

@[simp] theorem gbcaLabelMap_gbcaDeliver {n : ℕ} (r : ℕ) (i j : Fin n) (m : GBCA.ByABDY.Message) :
    gbcaLabelMap n (Sum.inr (.gbcaDeliver r i j m)) = none := rfl

@[simp] theorem gbcaLabelMap_decidedSend {n : ℕ} (j : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.decidedSend j b)) = none := rfl

@[simp] theorem gbcaLabelMap_decidedDeliver {n : ℕ} (i j : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.decidedDeliver i j b)) = none := rfl

@[simp] theorem gbcaLabelMap_retWPublish {n : ℕ} (r : ℕ) (id : Fin n) (c b : Bool) :
    gbcaLabelMap n (Sum.inr (.retWPublish r id c b)) = none := rfl

@[simp] theorem gbcaLabelMap_byzantineCallW {n : ℕ} (r : ℕ) (k : Fin n) :
    gbcaLabelMap n (Sum.inr (.byzantineCallW r k)) = none := rfl

@[simp] theorem gbcaLabelMap_byzantineRetW {n : ℕ} (r : ℕ) (k : Fin n) (b : Bool) :
    gbcaLabelMap n (Sum.inr (.byzantineRetW r k b)) = none := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem gbcaLabelMap_tau (n : ℕ) :
    gbcaLabelMap n (Silent.τ : ExtendedLabel n) = some (Silent.τ : Label n) := rfl

/-- Only the silent label projects to the silent label: a handshake row projects to a
handshake port, and every other extended label idles. -/
theorem gbcaLabelMap_eq_tau {n : ℕ} {l : ExtendedLabel n} (h : gbcaLabelMap n l = some Label.tau) :
    l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e <;> simp at h

/-- **The lifted specification**: the round-`r` graded agreement specification
read over the instance's interface. -/
noncomputable def specificationOverRoundAlphabet (P : Parameters) (r : ℕ) :
    System (GBCA.SpecState P.n) (ExtendedLabel P.n) :=
  (GBCA.specInst P r).mapIdle (gbcaLabelMap P.n)

@[simp] theorem specificationOverRoundAlphabet_init (P : Parameters) (r : ℕ) :
    (specificationOverRoundAlphabet P r).init = GBCA.SpecState.initial P.n := rfl

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverRoundAlphabet_isLTS (P : Parameters) (r : ℕ) :
    (specificationOverRoundAlphabet P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.specInst_isLTS P r)

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `gbcaLabelMap`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the
instance actually took — this is what turns a specification `callG` run into
the answer to a Byzantine call row. -/

/-- The section of `gbcaLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
def labelSection {n : ℕ} (l₀ : Label n) (l : ExtendedLabel n) : Label n → ExtendedLabel n :=
  fun x => if x = l₀ then l else Sum.inl x

theorem gbcaLabelMap_labelSection {n : ℕ} {l₀ : Label n} {l : ExtendedLabel n}
    (hl : gbcaLabelMap n l = some l₀) (x : Label n) :
    gbcaLabelMap n (labelSection l₀ l x) = some x := by
  unfold labelSection
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, gbcaLabelMap_inl]

theorem labelSection_tau {n : ℕ} {l₀ : Label n} {l : ExtendedLabel n}
    (hl : gbcaLabelMap n l = some l₀) (hl₀ : l₀ ≠ (Silent.τ : Label n)) (x : Label n) :
    labelSection l₀ l x = (Silent.τ : ExtendedLabel n) ↔ x = (Silent.τ : Label n) := by
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

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_specificationOverRoundAlphabet (P : Parameters) (r : ℕ)
    {s s' : GBCA.SpecState P.n} (h : (GBCA.specInst P r).weakLSilent s s') :
    (specificationOverRoundAlphabet P r).weakLSilent s s' :=
  System.weakLSilent_mapIdle Sum.inl (fun _ => rfl) (fun _ => by simp) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_specificationOverRoundAlphabet (P : Parameters) (r : ℕ)
    {s s' : GBCA.SpecState P.n} {l₀ : Label P.n} {l : ExtendedLabel P.n}
    (hl₀ : l₀ ≠ (Silent.τ : Label P.n)) (hl : gbcaLabelMap P.n l = some l₀)
    (h : (GBCA.specInst P r).weakLStep s l₀ s') :
    (specificationOverRoundAlphabet P r).weakLStep s l s' :=
  System.weakLStep_mapIdle (labelSection l₀ l) (gbcaLabelMap_labelSection hl) (labelSection_tau hl
    hl₀)
    (by simp [labelSection]) h

end GBCA.ByABDY
end ABA
end PLTS
