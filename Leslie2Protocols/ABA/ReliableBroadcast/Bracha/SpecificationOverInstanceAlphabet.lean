/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Composition

/-!
# The reliable-broadcast specification over the instance's interface

The broadcast specification speaks `Label n M`. The reliable-broadcast instance speaks
`InstanceLabel n M`, in which the call loop is a label of its own. `specificationLabelMap`
sends the call loop to the call it stands for and every other interface label to its own
copy. `specificationOverInstanceAlphabet` is the specification read along that map: the
specification's own rows at the labels the map carries, and a Dirac self-loop at the rest.

Every program rule and every network rule is Dirac, so the programs, the network, the
instance and the lifted specification are each an LTS. No program rule fires on the silent
label, so the instance's silent transitions are the network's injections and the hidden
rendezvous.

A weak run of the specification is read back over the interface along a section of
`specificationLabelMap`. `labelSection` is the left injection, the interface label a
specification label sits at. `sectionAt l₀ l` answers the interface label `l` over the
specification label `l₀` and agrees with `labelSection` elsewhere.
`weakLSilent_specificationOverInstanceAlphabet` carries a silent weak run;
`weakLStep_specificationOverInstanceAlphabet` carries a labelled one to any interface
label over the same specification label.

## Model and deviations

* **D27 (safety only).** The specification the instance is replaced by carries Validity
  and Agreement; Totality is out of scope.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M]

/-! ### The specification read over the instance's interface

The specification speaks `Label n M`; the instance speaks `InstanceLabel n M`, in which
the call loop is a label of its own. `specificationLabelMap` is the projection that
identifies the loop with the specification label it stands for, so that the
specification's own loop row answers it. -/

/-- The projection of the interface alphabet onto the specification's
alphabet. -/
def specificationLabelMap (n : ℕ) (M : Type) : InstanceLabel n M → Option (Label n M)
  | Sum.inl l => some l
  | Sum.inr (.callLoop m) => some (.call m)

@[simp] theorem specificationLabelMap_inl {n : ℕ} {M : Type} (l : Label n M) :
    specificationLabelMap n M (Sum.inl l) = some l := rfl

@[simp] theorem specificationLabelMap_callLoop {n : ℕ} {M : Type} (m : M) :
    specificationLabelMap n M (Sum.inr (.callLoop m)) = some (.call m) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem specificationLabelMap_tau (n : ℕ) (M : Type) :
    specificationLabelMap n M (Silent.τ : InstanceLabel n M) = some (Silent.τ : Label n M) := rfl

/-- Only the silent label projects to the silent label: the call loop projects
to the call. -/
theorem specificationLabelMap_eq_tau {n : ℕ} {M : Type} {l : InstanceLabel n M}
    (h : specificationLabelMap n M l = some Label.tau) : l = Sum.inl Label.tau := by
  cases l with
  | inl l₀ => rw [Option.some.inj h]
  | inr e => cases e; simp at h

/-- Every interface label carries a specification label. -/
theorem specificationLabelMap_isSome {n : ℕ} {M : Type} (l : InstanceLabel n M) : ∃ l₀,
  specificationLabelMap n M l = some l₀ := by
    cases l with
  | inl l₀ => exact ⟨l₀, rfl⟩
  | inr e => cases e; exact ⟨_, rfl⟩

/-- **The lifted specification**: the specification instance with leader `ldr`,
read over the instance's interface. -/
noncomputable def specificationOverInstanceAlphabet (P : Parameters) (ldr : Fin P.n) (M : Type) :
    System (SpecState P.n M) (InstanceLabel P.n M) :=
  (specInst P ldr M).mapIdle (specificationLabelMap P.n M)

@[simp] theorem specificationOverInstanceAlphabet_init {M : Type} (P : Parameters) (ldr : Fin P.n) :
    (specificationOverInstanceAlphabet P ldr M).init = SpecState.initial P.n M := rfl

/-! ### Determinacy

Every program rule and every network rule is Dirac, so the instance is an LTS. -/

/-- Every program transition is Dirac. -/
theorem programStep_dirac {P : Parameters} {ldr j : Fin P.n}
    {p : LocalState P.n (ProcessRecord M) (Message M)} {l : BroadcastLabel P.n M}
    {ν : PMF (LocalState P.n (ProcessRecord M) (Message M))} (h : ProgramStep P ldr j p l ν) :
    ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem networkStep_dirac {P : Parameters} {ldr : Fin P.n} {w : NetworkState P.n (Message M)}
    {l : BroadcastLabel P.n M} {μ : PMF (NetworkState P.n (Message M))}
    (h : NetworkStep P ldr w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem broadcastProgram_isLTS (P : Parameters) (ldr j : Fin P.n) :
    (broadcastProgram P ldr j (M := M)).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The network is an LTS. -/
theorem broadcastNetwork_isLTS (P : Parameters) (ldr : Fin P.n) : (broadcastNetwork P ldr M).IsLTS
  :=
  fun _ _ _ h => networkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem broadcastProgramProduct_isLTS (P : Parameters) (ldr : Fin P.n) :
    (System.synchronisedProduct (broadcastProgram P ldr (M := M))).IsLTS :=
  System.synchronisedProduct_isLTS (broadcastProgram_isLTS P ldr)

/-- The programs beside the network form an LTS. -/
theorem brachaInstanceExtended_isLTS (P : Parameters) (ldr : Fin P.n) :
    (brachaInstanceExtended P ldr M).IsLTS :=
  System.parallel_isLTS (broadcastProgramProduct_isLTS P ldr) (broadcastNetwork_isLTS P ldr)

/-- The instance is an LTS. -/
theorem brachaInstance_isLTS (P : Parameters) (ldr : Fin P.n) : (brachaInstance P ldr M).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (brachaInstanceExtended_isLTS P ldr) _)

/-- The lifted specification is an LTS: the specification is, and reading it
back adds only Dirac self-loops. -/
theorem specificationOverInstanceAlphabet_isLTS {M : Type} (P : Parameters) (ldr : Fin P.n) :
  (specificationOverInstanceAlphabet P ldr M).IsLTS :=
  System.mapIdle_isLTS _ (specInst_isLTS P ldr)

/-- No program rule fires on `τ`: a program only ever moves in a rendezvous or
on one of the instance's interface labels. The instance's silent transitions
are therefore exactly the network's injections and the hidden rendezvous. -/
theorem programStep_no_tau {P : Parameters} {ldr j : Fin P.n}
    {p : LocalState P.n (ProcessRecord M) (Message M)}
    {ν : PMF (LocalState P.n (ProcessRecord M) (Message M))}
    (h : ProgramStep P ldr j p (Silent.τ : BroadcastLabel P.n M) ν) : False := by
  rw [broadcastLabel_tau] at h; cases h

/-! ### Weak runs of the lifted specification

A weak run of the specification is read back along a section of `specificationLabelMap`. The
section sends every label to its own copy on the left, except the one label the
instance's step projects from, which is sent to the interface label the
instance actually took — this is what turns a specification `call` run into the
answer to the call loop. -/

/-- The left injection: the interface label a specification label sits at. -/
def labelSection {n : ℕ} {M : Type} : Label n M → InstanceLabel n M := Sum.inl

open scoped Classical in
/-- The section of `specificationLabelMap` that answers the interface label `l` over the
specification label `l₀`. -/
noncomputable def sectionAt {n : ℕ} {M : Type} (l₀ : Label n M) (l : InstanceLabel n M) :
    Label n M → InstanceLabel n M :=
  fun x => if x = l₀ then l else labelSection x

@[simp] theorem specificationLabelMap_labelSection {n : ℕ} {M : Type} (x : Label n M) :
    specificationLabelMap n M (labelSection x) = some x := rfl

/-- The left injection reflects the silent label. -/
theorem labelSection_eq_tau {n : ℕ} {M : Type} (x : Label n M) :
    (labelSection x : InstanceLabel n M) = (Silent.τ : InstanceLabel n M) ↔ x =
    (Silent.τ : Label n M) :=
  inl_eq_tau_iff x

theorem specificationLabelMap_sectionAt {n : ℕ} {M : Type} {l₀ : Label n M} {l : InstanceLabel n M}
    (hl : specificationLabelMap n M l = some l₀) (x : Label n M) : specificationLabelMap n M
      (sectionAt l₀ l x) = some x := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hl, hx]
  · rw [if_neg hx, specificationLabelMap_labelSection]

theorem sectionAt_tau {n : ℕ} {M : Type} {l₀ : Label n M} {l : InstanceLabel n M}
    (hl : specificationLabelMap n M l = some l₀)
    (hl₀ : l₀ ≠ (Silent.τ : Label n M)) (x : Label n M) :
    sectionAt l₀ l x = (Silent.τ : InstanceLabel n M) ↔ x = (Silent.τ : Label n M) := by
  unfold sectionAt
  by_cases hx : x = l₀
  · rw [if_pos hx, hx]
    constructor
    · intro hlτ
      have h2 : some l₀ = some (Silent.τ : Label n M) := by
        rw [← hl, hlτ]; rfl
      exact absurd (Option.some.inj h2) hl₀
    · intro h; exact absurd h hl₀
  · rw [if_neg hx]
    exact labelSection_eq_tau x

/-- A silent weak run of the specification is a silent weak run of the lifted
specification. -/
theorem weakLSilent_specificationOverInstanceAlphabet {M : Type} (P : Parameters) (ldr : Fin P.n)
    {s s' : SpecState P.n M} (h : (specInst P ldr M).weakLSilent s s') :
    (specificationOverInstanceAlphabet P ldr M).weakLSilent s s' :=
  System.weakLSilent_mapIdle labelSection (fun _ => rfl) (fun x => labelSection_eq_tau x) h

/-- A labelled weak run of the specification is a weak run of the lifted
specification at any interface label projecting to the same specification
label. -/
theorem weakLStep_specificationOverInstanceAlphabet {M : Type} (P : Parameters) (ldr : Fin P.n)
    {s s' : SpecState P.n M} {l₀ : Label P.n M} {l : InstanceLabel P.n M}
    (hl₀ : l₀ ≠ (Silent.τ : Label P.n M)) (hl : specificationLabelMap P.n M l = some l₀)
    (h : (specInst P ldr M).weakLStep s l₀ s') :
    (specificationOverInstanceAlphabet P ldr M).weakLStep s l s' :=
  System.weakLStep_mapIdle (sectionAt l₀ l) (specificationLabelMap_sectionAt hl) (sectionAt_tau hl
    hl₀)
    (by simp [sectionAt]) h

end BRB
end ABA
end PLTS
