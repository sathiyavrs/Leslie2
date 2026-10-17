/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Specification
import Leslie2Protocols.Framework.TraceDistributionSupport
import Leslie2.Results

/-!
# Safety of the gather specification instance

The common core is what a gather instance promises about the set it announces. `CoreTrace`
states it over the labels of a run: every announced core has at least `n − f` entries, two
announcements announce the same set, and every returned map contains every announced core. This
is the source's Transition System 4 core clause, quantified over the labels of a run rather than
over the states of one. `specInst_core` is `CoreTrace` at the gather specification
`Gather.specInst` (`ABA/Gather/Specification.lean`).

At the specification the three clauses come from the transitions alone. `bindCore` is the only
writer of the `core` field and fires only from `core = none`, so the field, once written, keeps its
value (`core_stable`), and two states of one execution that hold a core hold the same one
(`core_eq_of_stateAt`). `announceCore` announces the field's value, and `ret` asks for a core below
the returned map. The size bound is the guard `hcard` of `bindCore`, carried forward as the state
invariant `core_card`.

An implementation inherits the predicate along the soundness of its refinement
(`PLTS.safety_transfer`, `Framework/TraceDistributionSupport.lean`), and the two gather
implementations carry it in `ABA/Gather/CommonCore.lean`. What makes that transfer say anything is
that the core is announced on a label of its own (D29): an implementation holds it in a field no
process reads, and its refinements match its announcement by the specification's.
-/

open Stream'

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The core along a run -/

/-- The guards of a return: the core is written and lies below the returned map. -/
theorem ret_guards {s : SpecState P.n X} {id : Fin P.n} {g : Fin P.n → Option X}
    {μ : PMF (SpecState P.n X)} (hstep : Step P s (.ret id g) μ) :
    ∃ C, s.core = some C ∧ AcceptedPairs.subMap C g := by
  cases hstep with
  | ret _ _ C hC hmem _ _ => exact ⟨C, hC, hmem⟩

/-- The guard of an announcement: the announced set is the core. -/
theorem announceCore_guard {s : SpecState P.n X} {C : AcceptedPairs P.n X}
    {μ : PMF (SpecState P.n X)} (hstep : Step P s (.core C) μ) : s.core = some C := by
  cases hstep with
  | announceCore _ h => exact h

/-- **The core is written once.** `bindCore` is its only writer and fires
only from `core = none`, so the value is unchanged by every later transition and every
corruption. -/
theorem core_stable {C : AcceptedPairs P.n X} :
    ∀ (s : SpecState P.n X) (l : Label P.n X) (μ : PMF (SpecState P.n X))
      (s' : SpecState P.n X), s.core = some C → Step P s l μ → s' ∈ μ.support →
      s'.core = some C := by
  intro s l μ s' hC hstep hs'
  cases hstep with
  | bindCore S h0 hval hcard =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      rw [h0] at hC; exact absurd hC (by simp)
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      rw [corrupt_core]; exact hC
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hC

/-- **The size bound is an invariant.** The core is written only by
`bindCore`, whose guard `hcard` is the bound. -/
theorem core_card {e : AlterSeq (SpecState P.n X) (Label P.n X)}
    (he : is_exec e (specInst P X)) :
    ∀ (k : ℕ) (s : SpecState P.n X), e.stateAt k = some s →
      ∀ C, s.core = some C → P.n - P.f ≤ C.card := by
  refine is_exec_induction (sys := specInst P X)
    (fun s => ∀ C, s.core = some C → P.n - P.f ≤ C.card) ?_ ?_ he
  · intro C hC
    rw [show (specInst P X).init = SpecState.initial P.n X from rfl,
      show (SpecState.initial P.n X).core = none from rfl] at hC
    exact absurd hC (by simp)
  · intro s l μ s' hI hstep hs'
    cases hstep with
    | bindCore S h0 hval hcard =>
        rw [PMF.mem_support_pure_iff] at hs'; subst hs'
        intro C hC
        obtain rfl : S = C := Option.some.inj hC
        exact hcard
    | fail id =>
        rw [PMF.mem_support_pure_iff] at hs'; subst hs'
        intro C hC
        rw [corrupt_core] at hC
        exact hI C hC
    | _ =>
        rw [PMF.mem_support_pure_iff] at hs'; subst hs'
        exact hI

/-- **The core is one set along an execution.** Two states of one execution that hold a core
hold the same core, since the core is written once (`core_stable`). -/
theorem core_eq_of_stateAt {e : AlterSeq (SpecState P.n X) (Label P.n X)}
    (he : is_exec e (specInst P X)) {k₁ k₂ : ℕ} {s₁ s₂ : SpecState P.n X}
    {C₁ C₂ : AcceptedPairs P.n X} (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hC₁ : s₁.core = some C₁) (hC₂ : s₂.core = some C₂) : C₁ = C₂ := by
  rcases le_total k₁ k₂ with hk | hk
  · have hcarry := is_exec_stable (sys := specInst P X)
      (fun s => s.core = some C₁) (fun s l μ s' => core_stable s l μ s')
      he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hC₁
    rw [hcarry] at hC₂
    exact Option.some.inj hC₂
  · have hcarry := is_exec_stable (sys := specInst P X)
      (fun s => s.core = some C₂) (fun s l μ s' => core_stable s l μ s')
      he k₂ k₁ s₂ s₁ hk hst₂ hst₁ hC₂
    rw [hcarry] at hC₁
    exact (Option.some.inj hC₁).symm

/-! ### The trace-level statement -/

/-- **The common core on a trace.** Every announced core has at least `n − f` entries, two
announcements announce the same set, and every returned map contains every announced core. -/
def CoreTrace (P : Parameters) {X : Type} (t : Seq (Label P.n X)) : Prop :=
  (∀ C : AcceptedPairs P.n X, Label.core C ∈ t → P.n - P.f ≤ C.card) ∧
  (∀ C₁ C₂ : AcceptedPairs P.n X, Label.core C₁ ∈ t → Label.core C₂ ∈ t → C₁ = C₂) ∧
  (∀ (id : Fin P.n) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X),
    Label.ret id g ∈ t → Label.core C ∈ t → AcceptedPairs.subMap C g)

/-- **The specification instance binds one core.** An announcement reads the core of the state
it fires at, a return asks for a core below its map, and the core is one set along an
execution. -/
theorem specInst_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (specInst P X), ∀ t, D t ≠ 0 → CoreTrace P t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ :=
    exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  have hcore : ∀ C, Label.core C ∈ t →
      ∃ (k : ℕ) (s : SpecState P.n X), e.stateAt k = some s ∧ s.core = some C := by
    intro C h
    obtain ⟨-, k, s', hg⟩ := (h_char _).mp h
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    exact ⟨k, s, hst, announceCore_guard hstep⟩
  refine ⟨?_, ?_, ?_⟩
  · intro C h
    obtain ⟨k, s, hst, hC⟩ := hcore C h
    exact core_card h_exec k s hst C hC
  · intro C₁ C₂ h₁ h₂
    obtain ⟨k₁, s₁, hst₁, hC₁⟩ := hcore C₁ h₁
    obtain ⟨k₂, s₂, hst₂, hC₂⟩ := hcore C₂ h₂
    exact core_eq_of_stateAt h_exec hst₁ hst₂ hC₁ hC₂
  · intro id g C h₁ h₂
    obtain ⟨-, k₁, s₁', hg₁⟩ := (h_char _).mp h₁
    obtain ⟨s₁, μ₁, hst₁, hstep₁, -⟩ := h_exec.1 k₁ _ _ hg₁
    obtain ⟨C', hC', hmem⟩ := ret_guards hstep₁
    obtain ⟨k₂, s₂, hst₂, hC₂⟩ := hcore C h₂
    rw [core_eq_of_stateAt h_exec hst₂ hst₁ hC₂ hC']
    exact hmem

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.specInst_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_core

end Gather
end ABA
end PLTS
