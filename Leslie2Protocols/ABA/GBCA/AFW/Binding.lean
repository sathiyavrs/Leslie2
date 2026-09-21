/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.RefinesSpecification
import Leslie2Protocols.ABA.GBCA.AFW.GatherSubstitutions
import Leslie2Protocols.ABA.GBCA.SpecificationSafety
import Leslie2.Results

/-!
# Binding of the round over the family alphabet

The round speaks the family alphabet `NLab n`, in which a round-`r` return
appears twice: as `Sum.inl (Lab.retG r id out bnd)` and as the Byzantine row
`Sum.inr (.byzRetG r id out bnd)`. `GBCA.ByABDY.gPull` sends both to the same
specification return, and `GBCA.BindingTraceN` states binding at every
label of a trace that `GBCA.ByABDY.gPull` sends to a round-`r` return, so both forms
count.

`GBCA.liftedSpec_binding` proves binding of the specification read over
that alphabet, `GBCA.ByABDY.liftedSpec`. An execution of the lifted system has the
states of a `GBCA.specInst` execution: a transition on a label `GBCA.ByABDY.gPull`
names is a `GBCA.Step` transition at that label, and a transition on a label it
leaves unnamed is a self-loop. The exclusion set therefore only grows along
such an execution and holds at most one bit, which is what the binding
argument of `ABA/GBCA/SpecificationSafety.lean` runs on.

The three tiers of the round reach the lifted specification through
`GBCA.ByAFW.pairRefines` and the two substitutions of `GBCA/AFW/GatherSubstitutions.lean`.
Each inherits binding along its inclusion: `GBCA.pairInst_binding`,
`GBCA.idealInst_binding` and `GBCA.lowPairInst_binding`.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA

open Implementation Composition GBCA.ByAFW

variable {P : Params} {r : ℕ}

/-! ### Binding over the family alphabet -/

/-- **Binding (trace form) over the family alphabet.** The round is bound to
one bit on the trace: all labels the trace carries that name a round-`r` return
announce the same bit, and every one of them that hands out a value hands out
that bit. A return is named by `Sum.inl (Lab.retG r id out bnd)` and by the
Byzantine row `Sum.inr (.byzRetG r id out bnd)` alike, `GBCA.ByABDY.gPull` sending
both to the specification's return. -/
def BindingTraceN (P : Params) (r : ℕ) (t : Seq (NLab P.n)) : Prop :=
  (∀ (l₁ l₂ : NLab P.n) (id₁ id₂ : Fin P.n) (o₁ o₂ : GbcaOut) (β₁ β₂ : Bool),
      l₁ ∈ t → l₂ ∈ t → GBCA.ByABDY.gPull P.n l₁ = some (Lab.retG r id₁ o₁ β₁) →
      GBCA.ByABDY.gPull P.n l₂ = some (Lab.retG r id₂ o₂ β₂) → β₁ = β₂) ∧
    ∀ (l : NLab P.n) (id : Fin P.n) (o : GbcaOut) (β v : Bool),
      l ∈ t → GBCA.ByABDY.gPull P.n l = some (Lab.retG r id o β) →
      outValue o = some v → v = β

/-! ### Transitions of the lifted specification -/

/-- A transition of the lifted specification on a label `GBCA.ByABDY.gPull` names is a
transition of the specification at that label. -/
theorem liftedSpec_step_some {s : SpecState P.n} {l : NLab P.n} {l₀ : Lab P.n}
    {μ : PMF (SpecState P.n)} (hpull : GBCA.ByABDY.gPull P.n l = some l₀)
    (h : (GBCA.ByABDY.liftedSpec P r).step s l μ) : Step P r s l₀ μ :=
  (System.mapIdle_step_some (sys := specInst P r) hpull μ).mp h

/-- A transition of the lifted specification is a transition of the
specification at the label `GBCA.ByABDY.gPull` names, or a self-loop. -/
theorem liftedSpec_step_cases {s s' : SpecState P.n} {l : NLab P.n}
    {μ : PMF (SpecState P.n)} (h : (GBCA.ByABDY.liftedSpec P r).step s l μ)
    (hs' : s' ∈ μ.support) :
    (∃ l₀, GBCA.ByABDY.gPull P.n l = some l₀ ∧ Step P r s l₀ μ) ∨ s' = s := by
  rcases (System.mapIdle_step (GBCA.ByABDY.gPull P.n) (specInst P r) s l μ).mp h with
    ⟨l₀, hpull, hstep⟩ | ⟨-, rfl⟩
  · exact Or.inl ⟨l₀, hpull, hstep⟩
  · exact Or.inr ((PMF.mem_support_pure_iff _ _).mp hs')

/-! ### The exclusion set along an execution of the lifted specification -/

/-- **The exclusion set never shrinks**, along a transition of the lifted
specification: a named label takes a specification row, and an unnamed one
leaves the state alone. -/
theorem liftedSpec_excluded_mono {s s' : SpecState P.n} {l : NLab P.n}
    {μ : PMF (SpecState P.n)} (h : (GBCA.ByABDY.liftedSpec P r).step s l μ)
    (hs' : s' ∈ μ.support) : s.excluded ⊆ s'.excluded := by
  rcases liftedSpec_step_cases h hs' with ⟨_, -, hstep⟩ | rfl
  · exact Step.excluded_mono hstep hs'
  · exact Finset.Subset.refl _

/-- **An excluded bit stays excluded along a run** of the lifted
specification. -/
theorem liftedSpec_excluded_mem_stable {e : AlterSeq (SpecState P.n) (NLab P.n)}
    (he : is_exec e (GBCA.ByABDY.liftedSpec P r)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b : Bool}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hb : b ∈ s₁.excluded) : b ∈ s₂.excluded :=
  is_exec_stable (sys := GBCA.ByABDY.liftedSpec P r) (fun s => b ∈ s.excluded)
    (fun _ _ _ _ hmem hstep hs' => liftedSpec_excluded_mono hstep hs' hmem)
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hb

/-- **One exclude per instance**, at every state of an execution of the lifted
specification. -/
theorem liftedSpec_excluded_card_le_one {e : AlterSeq (SpecState P.n) (NLab P.n)}
    (he : is_exec e (GBCA.ByABDY.liftedSpec P r)) {k : ℕ} {s : SpecState P.n}
    (hst : e.stateAt k = some s) : s.excluded.card ≤ 1 :=
  is_exec_stable (sys := GBCA.ByABDY.liftedSpec P r) (fun s => s.excluded.card ≤ 1)
    (fun _ _ _ _ hcard hstep hs' => by
      rcases liftedSpec_step_cases hstep hs' with ⟨_, -, hrow⟩ | rfl
      · exact Step.excluded_card_le_one hrow hs' hcard
      · exact hcard)
    he 0 k e.init s (Nat.zero_le k) rfl hst
    (by rw [← he.2]; simp [SpecState.initial])

/-! ### The two returns of a run -/

/-- Two bits excluded at one state of an execution of the lifted specification
are equal: the exclusion set holds at most one bit. -/
private theorem liftedSpec_excluded_eq_of_mem
    {e : AlterSeq (SpecState P.n) (NLab P.n)} (he : is_exec e (GBCA.ByABDY.liftedSpec P r))
    {k : ℕ} {s : SpecState P.n} {b₁ b₂ : Bool} (hst : e.stateAt k = some s)
    (h₁ : b₁ ∈ s.excluded) (h₂ : b₂ ∈ s.excluded) : b₁ = b₂ :=
  Finset.card_le_one.mp (liftedSpec_excluded_card_le_one he hst) _ h₁ _ h₂

/-- Two returns of one run of the lifted specification announce the same bit
(`k₁ ≤ k₂` case). -/
private theorem liftedSpec_retG_bound_agree_le
    {e : AlterSeq (SpecState P.n) (NLab P.n)} (he : is_exec e (GBCA.ByABDY.liftedSpec P r))
    {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {s₁ s₂ : SpecState P.n} {id₁ id₂ : Fin P.n}
    {o₁ o₂ : GbcaOut} {β₁ β₂ : Bool} {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂) : β₁ = β₂ := by
  have hcarry : (!β₁) ∈ s₂.excluded :=
    liftedSpec_excluded_mem_stable he hk hst₁ hst₂ (retG_bound_guard hstep₁)
  have h := liftedSpec_excluded_eq_of_mem he hst₂ hcarry (retG_bound_guard hstep₂)
  revert h
  cases β₁ <;> cases β₂ <;> simp

/-- **One bound bit per round**, along an execution of the lifted
specification. Each return fires under `(!β) ∈ excluded`, the exclusion set
only grows, and no state of an execution excludes two bits. -/
theorem liftedSpec_retG_bound_agree {e : AlterSeq (SpecState P.n) (NLab P.n)}
    (he : is_exec e (GBCA.ByABDY.liftedSpec P r)) {k₁ k₂ : ℕ} {s₁ s₂ : SpecState P.n}
    {id₁ id₂ : Fin P.n} {o₁ o₂ : GbcaOut} {β₁ β₂ : Bool}
    {μ₁ μ₂ : PMF (SpecState P.n)}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hstep₁ : Step P r s₁ (.retG r id₁ o₁ β₁) μ₁)
    (hstep₂ : Step P r s₂ (.retG r id₂ o₂ β₂) μ₂) : β₁ = β₂ := by
  rcases le_total k₁ k₂ with h | h
  · exact liftedSpec_retG_bound_agree_le he h hst₁ hst₂ hstep₁ hstep₂
  · exact (liftedSpec_retG_bound_agree_le he h hst₂ hst₁ hstep₂ hstep₁).symm

/-- **A value-bearing return announces the bit it hands out**, along an
execution of the lifted specification. The value guard excludes `!v`, the bound
guard excludes `!β`, and a state of an execution excludes at most one bit. -/
theorem liftedSpec_retG_value_eq_bound {e : AlterSeq (SpecState P.n) (NLab P.n)}
    (he : is_exec e (GBCA.ByABDY.liftedSpec P r)) {k : ℕ} {s : SpecState P.n}
    {id : Fin P.n} {o : GbcaOut} {v β : Bool} {μ : PMF (SpecState P.n)}
    (hst : e.stateAt k = some s) (hstep : Step P r s (.retG r id o β) μ)
    (ho : outValue o = some v) : v = β := by
  have h := liftedSpec_excluded_eq_of_mem he hst (retG_value_guards hstep ho).2
    (retG_bound_guard hstep)
  revert h
  cases v <;> cases β <;> simp

/-! ### Binding of the lifted specification -/

/-- **Binding of the specification read over the family alphabet**: every trace
in the support of every achievable trace distribution of `GBCA.ByABDY.liftedSpec P r`
satisfies `BindingTraceN`. -/
theorem liftedSpec_binding (P : Params) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (GBCA.ByABDY.liftedSpec P r), ∀ t, D t ≠ 0 →
      BindingTraceN P r t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ := exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  have hret : ∀ (l : NLab P.n) (id : Fin P.n) (o : GbcaOut) (β : Bool),
      l ∈ t → GBCA.ByABDY.gPull P.n l = some (Lab.retG r id o β) →
      ∃ (k : ℕ) (s : SpecState P.n) (μ : PMF (SpecState P.n)),
        e.stateAt k = some s ∧ Step P r s (Lab.retG r id o β) μ := by
    intro l id o β hl hpull
    obtain ⟨-, k, s', hg⟩ := (h_char l).mp hl
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    exact ⟨k, s, μ, hst, liftedSpec_step_some hpull hstep⟩
  constructor
  · intro l₁ l₂ id₁ id₂ o₁ o₂ β₁ β₂ h₁ h₂ hp₁ hp₂
    obtain ⟨k₁, s₁, μ₁, hst₁, hstep₁⟩ := hret l₁ id₁ o₁ β₁ h₁ hp₁
    obtain ⟨k₂, s₂, μ₂, hst₂, hstep₂⟩ := hret l₂ id₂ o₂ β₂ h₂ hp₂
    exact liftedSpec_retG_bound_agree h_exec hst₁ hst₂ hstep₁ hstep₂
  · intro l id o β v h_mem hpull ho
    obtain ⟨k, s, μ, hst, hstep⟩ := hret l id o β h_mem hpull
    exact liftedSpec_retG_value_eq_bound h_exec hst hstep ho

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather specifications in
the specification read over the round's interface, the soundness of
`pairRefines`. -/
theorem pairInst_refines (P : Params) (r : ℕ) :
    achievableTraceDists (pairInst P r) ⊆ achievableTraceDists (GBCA.ByABDY.liftedSpec P r) :=
  (ForwardSimulation.toProbabilistic (pairInst_isLTS P r) (GBCA.ByABDY.liftedSpec_isLTS P r)
    (pairRel_init P r) (pairRefines P r)).achievableTraceDists_subset

/-- **The round over the gather instances over Bracha's broadcast refines the
specification**: the two substitutions and the counting simulation, each taken
probabilistically, joined by Result 2
(`ProbabilisticForwardSimulation.trans`). -/
theorem gatherImplRefines (P : Params) (r : ℕ) :
    ProbabilisticForwardSimulation (lowPairInst P r) (GBCA.ByABDY.liftedSpec P r)
      (compRel (diracRel (LowPairRel P))
        (compRel (diracRel (IdealRel P)) (diracRel (PairRel P)))) :=
  (ForwardSimulation.toProbabilistic (lowPairInst_isLTS P r) (idealInst_isLTS P r)
      (lowPairRel_init P r) (lowPairRefines P r)).trans
    ((ForwardSimulation.toProbabilistic (idealInst_isLTS P r) (pairInst_isLTS P r)
        (idealRel_init P r) (idealRefines P r)).trans
      (ForwardSimulation.toProbabilistic (pairInst_isLTS P r) (GBCA.ByABDY.liftedSpec_isLTS P r)
        (pairRel_init P r) (pairRefines P r)))

/-- The soundness inclusion of the round reading: every trace distribution
achievable by the round over the gather instances over Bracha's broadcast is
achievable by the lifted specification. -/
theorem gatherRoundRefines (P : Params) (r : ℕ) :
    achievableTraceDists (lowPairInst P r) ⊆ achievableTraceDists (GBCA.ByABDY.liftedSpec P r) :=
  (gatherImplRefines P r).achievableTraceDists_subset

/-- The soundness inclusion of the gather substitution above the counting
simulation: every trace distribution achievable by the round over the gather
instances over the broadcast specification is achievable by the lifted
specification. -/
theorem idealRoundRefines (P : Params) (r : ℕ) :
    achievableTraceDists (idealInst P r) ⊆ achievableTraceDists (GBCA.ByABDY.liftedSpec P r) :=
  Set.Subset.trans (idealInst_refines P r) (pairInst_refines P r)

/-- The soundness inclusion of the counting simulation alone: every trace
distribution achievable by the round over the gather specifications is
achievable by the lifted specification. -/
theorem pairRoundRefines (P : Params) (r : ℕ) :
    achievableTraceDists (pairInst P r) ⊆ achievableTraceDists (GBCA.ByABDY.liftedSpec P r) :=
  pairInst_refines P r

/-! ### Binding of the three tiers -/

/-- **Binding of the round over the gather specifications, on a trace.** Every
positive-probability trace of the round is bound to one bit: all its round-`r`
returns announce that bit, and every one of them that hands out a value hands
out it. Binding is a property of the labels (`BindingTraceN`), so
`pairRoundRefines` carries it from `liftedSpec_binding`. -/
theorem pairInst_binding (P : Params) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (pairInst P r), ∀ t, D t ≠ 0 →
      BindingTraceN P r t :=
  safety_transfer (pairRoundRefines P r) (liftedSpec_binding P r)

/-- **Binding of the round over the gather instances over the broadcast
specification, on a trace**, along the inclusion `idealRoundRefines`. -/
theorem idealInst_binding (P : Params) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (idealInst P r), ∀ t, D t ≠ 0 →
      BindingTraceN P r t :=
  safety_transfer (idealRoundRefines P r) (liftedSpec_binding P r)

/-- **Binding of the round over the gather instances over Bracha's broadcast,
on a trace**, along the three-tier inclusion `gatherRoundRefines`. -/
theorem lowPairInst_binding (P : Params) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (lowPairInst P r), ∀ t, D t ≠ 0 →
      BindingTraceN P r t :=
  safety_transfer (gatherRoundRefines P r) (liftedSpec_binding P r)

/-! ### Mechanical axiom check

No headline may acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.GBCA.liftedSpec_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms liftedSpec_binding

/-- info: 'PLTS.ABA.GBCA.gatherImplRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherImplRefines

/-- info: 'PLTS.ABA.GBCA.gatherRoundRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherRoundRefines

/-- info: 'PLTS.ABA.GBCA.pairInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairInst_binding

/-- info: 'PLTS.ABA.GBCA.idealInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idealInst_binding

/-- info: 'PLTS.ABA.GBCA.lowPairInst_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowPairInst_binding

end GBCA
end ABA
end PLTS
