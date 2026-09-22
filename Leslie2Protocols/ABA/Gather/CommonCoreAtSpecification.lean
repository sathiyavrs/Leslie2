/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Specification
import Leslie2Protocols.Framework.TraceDistributionSupport
import Leslie2.Results

/-!
# The binding of a gather instance, read off its traces

`CoreTrace` is the instance-level statement of the core. Every return label of
the trace carries the same payload set `C`, that set has at least `n − f`
entries, and the returned map has every entry of it. This is the source's
Transition System 4 binding clause, quantified over the labels of a run
rather than over the states of one.

At the specification the three clauses come from the rules alone. `bindCore`
is the only writer of the `core` field and fires only from `core = none`, so
the field, once written, keeps its value (`core_stable`) and every return
reads the same set. `ret` demands `C.subMap g` outright. The size bound is
the guard `hcard` of `bindCore`, carried forward as the state invariant
`core_card`.

An implementation inherits the predicate along the soundness of its refinement
(`PLTS.safety_transfer`, `Framework/TraceDistributionSupport.lean`). What makes that
transfer say anything is that the core is on the label: an implementation holds
it in a field no process reads, and its refinement matches the labels that
carry it.
-/

open Stream'

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The core along a run -/

/-- The guards of a return, read off its label. -/
theorem ret_guards {s : SpecState P.n X} {id : Fin P.n} {g : Fin P.n → Option X}
    {C : AcceptedPairs P.n X} {μ : PMF (SpecState P.n X)}
    (hstep : Step P s (.ret id g C) μ) :
    s.core = some C ∧ AcceptedPairs.subMap C g := by
  cases hstep with
  | ret id' g' C' hC hmem _ _ => exact ⟨hC, hmem⟩

/-- **The core is written once.** `bindCore` is its only writer and fires
only from `core = none`, so the value survives every later rule and every
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

/-! ### The trace-level statement -/

/-- **The core on a trace.** Every return label of the trace carries one and
the same payload set, that set has at least `n − f` entries, and the returned
map has every entry of it. -/
def CoreTrace (P : Parameters) {X : Type} (t : Seq (Label P.n X)) : Prop :=
  (∀ (id : Fin P.n) (g : Fin P.n → Option X) (C : AcceptedPairs P.n X),
      Label.ret id g C ∈ t → P.n - P.f ≤ C.card ∧ AcceptedPairs.subMap C g) ∧
    ∀ (id₁ id₂ : Fin P.n) (g₁ g₂ : Fin P.n → Option X) (C₁ C₂ : AcceptedPairs P.n X),
      Label.ret id₁ g₁ C₁ ∈ t → Label.ret id₂ g₂ C₂ ∈ t → C₁ = C₂

/-- **The specification instance binds one core.** -/
theorem specInst_core (P : Parameters) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (specInst P X), ∀ t, D t ≠ 0 → CoreTrace P t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ :=
    exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  refine ⟨?_, ?_⟩
  · intro id g C h₁
    obtain ⟨-, k, s', hg⟩ := (h_char _).mp h₁
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    obtain ⟨hC, hmem⟩ := ret_guards hstep
    exact ⟨core_card h_exec k s hst C hC, hmem⟩
  · intro id₁ id₂ g₁ g₂ C₁ C₂ h₁ h₂
    obtain ⟨-, k₁, s₁', hg₁⟩ := (h_char _).mp h₁
    obtain ⟨-, k₂, s₂', hg₂⟩ := (h_char _).mp h₂
    obtain ⟨s₁, μ₁, hst₁, hstep₁, -⟩ := h_exec.1 k₁ _ _ hg₁
    obtain ⟨s₂, μ₂, hst₂, hstep₂, -⟩ := h_exec.1 k₂ _ _ hg₂
    obtain ⟨hC₁, -⟩ := ret_guards hstep₁
    obtain ⟨hC₂, -⟩ := ret_guards hstep₂
    rcases le_total k₁ k₂ with hk | hk
    · have hcarry := is_exec_stable (sys := specInst P X)
        (fun s => s.core = some C₁) (fun s l μ s' => core_stable s l μ s')
        h_exec k₁ k₂ s₁ s₂ hk hst₁ hst₂ hC₁
      rw [hcarry] at hC₂
      exact Option.some.inj hC₂
    · have hcarry := is_exec_stable (sys := specInst P X)
        (fun s => s.core = some C₂) (fun s l μ s' => core_stable s l μ s')
        h_exec k₂ k₁ s₂ s₁ hk hst₂ hst₁ hC₂
      rw [hcarry] at hC₁
      exact (Option.some.inj hC₁).symm

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.specInst_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specInst_core

end Gather
end ABA
end PLTS
