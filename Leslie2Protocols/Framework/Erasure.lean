/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Results
import Leslie2.Simulation.ForwardLTS
import Leslie2.Simulation.TraceMap
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# Erasure of an auxiliary state component

A system is often written with a state component that no transition's firing depends on: a
record of what has already happened, carried so that an invariant can be stated over it. A
step may read the component to decide a value it announces, never whether it fires. Such a
component is an auxiliary variable in the sense of Abadi and Lamport, *The existence of
refinement mappings* (1991), here between systems whose steps are distributions. Erasing it
has to leave the observable behaviour untouched.

`StateErasure sysA sys0 π φ` is that statement. The map `π : SA → S0` deletes the component
and `φ : L → L` identifies the labels that differ only in the value the component announces.
Two clauses carry the content.

* `project` — every transition `s -[l]→ μ` of `sysA` is a transition `π s -[l]→ μ.map π` of
  `sys0`, on the same label. The component adds no step, and the distribution over what
  survives `π` is unchanged.
* `lift` — every transition `π s -[l]→ μ` of `sys0` is met by a transition `s -[l']→ ν` of
  `sysA` with `φ l' = φ l` and `μ = ν.map π`. The component blocks no step.

The two clauses are not symmetric. A label of `sysA` may announce the value of
the erased component, and from a state `s` only the announcement `s` carries is available,
whereas `sys0` has nothing to announce from and offers every label of the `φ`-fibre. So the
projection is exact on labels and only the lift is taken up to `φ`. A third clause,
`silent`, keeps `τ` alone in its `φ`-fibre (`SeparatesSilent`), so a lift never answers an
internal step with an external one or the reverse.

`project` is a functional label-preserving simulation, hence the inclusion
`StateErasure.achievableTraceDists_subset`. At `φ = id` the lift is label-exact, so it is a
probabilistic forward simulation in the opposite direction
(`ProbabilisticForwardSimulation.ofStrongFunctional_converse`) and the two sets of
achievable trace distributions coincide: `StateErasure.achievableTraceDists_eq`. A general
`φ` reaches that equality through `StateErasure.abstract_collapse`, which hides every label
`φ` identifies with a different label and returns an erasure at `φ = id`.

## Congruences

An erasure survives parallel composition in either position, against a component whose step relation
is saturated along `φ` (`System.LabelSaturated`); abstraction of a `φ`-saturated set of labels; and
restriction along the left summand of an extended alphabet (`Framework/Relabel.lean`). Saturation
itself is preserved by parallel composition, abstraction, the full-synchronisation product
(`Framework/SynchronisedProduct.lean`) and the partial label pullback `System.mapIdle`
(`Framework/LoopsAndInstanceFamilies.lean`). -/

namespace PLTS

variable {SA S0 SC L : Type} [Silent L]

/-! ### The two label conditions -/

/-- `φ` **separates the silent label**: `τ` is alone in its `φ`-fibre. An erasure asks this
of its label identification, so that the fibre of an internal label holds no external one. -/
def SeparatesSilent (φ : L → L) : Prop :=
  ∀ l, φ l = φ (Silent.τ : L) → l = Silent.τ

/-- The identity separates the silent label: its fibres are singletons. -/
theorem separatesSilent_id : SeparatesSilent (id : L → L) := fun _ h => h

/-- A system is **saturated along `φ`** when its step relation is constant on the `φ`-fibres of the
label: labels with the same `φ`-image have the same outgoing transitions. This is the hypothesis
under which a system is a neighbour of an erasure in a composition — it accepts whichever
representative of a fibre the ghost-free system announces. -/
def System.LabelSaturated (sys : System SC L) (φ : L → L) : Prop :=
  ∀ s l l' μ, φ l = φ l' → sys.step s l μ → sys.step s l' μ

omit [Silent L] in
/-- Every system is saturated along the identity. -/
theorem System.labelSaturated_id (sys : System SC L) : sys.LabelSaturated (id : L → L) := by
  intro _ l l' _ h hstep
  have hll : l = l' := h
  exact hll ▸ hstep

/-! ### Erasure -/

/-- **Erasure of an auxiliary state component.** `π` deletes the component and `φ` identifies
the labels that differ only in the value the component announces. -/
structure StateErasure (sysA : System SA L) (sys0 : System S0 L) (π : SA → S0) (φ : L → L) :
    Prop where
  /-- `π` carries the initial state to the initial state. -/
  init : π sysA.init = sys0.init
  /-- `τ` is alone in its `φ`-fibre. -/
  silent : SeparatesSilent φ
  /-- Every transition of `sysA` projects to a transition of `sys0` on the same label. -/
  project : ∀ s l μ, sysA.step s l μ → sys0.step (π s) l (μ.map π)
  /-- Every transition of `sys0` out of a `π`-image lifts, up to `φ`, to a transition of
  `sysA`. -/
  lift : ∀ s l μ, sys0.step (π s) l μ → ∃ l' ν, φ l' = φ l ∧ sysA.step s l' ν ∧ μ = ν.map π

namespace StateErasure

variable {sysA : System SA L} {sys0 : System S0 L} {π : SA → S0} {φ : L → L}

/-- **Erasure includes trace distributions.** The projection clause is a functional,
label-preserving simulation, so every trace distribution of the system carrying the
component is achieved by the system without it. -/
theorem achievableTraceDists_subset (h : StateErasure sysA sys0 π φ) :
    achievableTraceDists sysA ⊆ achievableTraceDists sys0 :=
  achievableTraceDists_map π h.init h.project

/-- **An erasure at `φ = id` preserves trace distributions.** The projection gives one
inclusion; the lift, being label-exact, is a probabilistic forward simulation of `sys0` by
`sysA` and gives the other. -/
theorem achievableTraceDists_eq (h : StateErasure sysA sys0 π id) :
    achievableTraceDists sysA = achievableTraceDists sys0 := by
  refine Set.Subset.antisymm h.achievableTraceDists_subset ?_
  refine (ProbabilisticForwardSimulation.ofStrongFunctional_converse π h.init ?_)
    |>.achievableTraceDists_subset
  intro s l μ hstep
  obtain ⟨l', ν, hl, hA, hμ⟩ := h.lift s l μ hstep
  have hll : l' = l := hl
  exact ⟨ν, hll ▸ hA, hμ⟩

/-! ### Parallel composition -/

section Parallel

variable {sysA : System SA L} {sys0 : System S0 L} {π : SA → S0} {φ : L → L}
  {sysC : System SC L}

omit [Silent L] in
/-- The pushforward of an independent product along a map of its left factor. -/
private theorem map_prodPMF_right (f : SA → S0) (μ₁ : PMF SA) (μ₂ : PMF SC) :
    (prodPMF μ₁ μ₂).map (Prod.map f id) = prodPMF (μ₁.map f) μ₂ := by
  rw [show (Prod.map f (id : SC → SC)) = (fun p : SA × SC => (f p.1, id p.2)) from rfl,
    prodPMF_map, PMF.map_id]

omit [Silent L] in
/-- The pushforward of an independent product along a map of its right factor. -/
private theorem map_prodPMF_left (f : SA → S0) (μ₁ : PMF SC) (μ₂ : PMF SA) :
    (prodPMF μ₁ μ₂).map (Prod.map id f) = prodPMF μ₁ (μ₂.map f) := by
  rw [show (Prod.map (id : SC → SC) f) = (fun p : SC × SA => (id p.1, f p.2)) from rfl,
    prodPMF_map, PMF.map_id]

/-- **Erasure is a congruence for parallel composition on the left factor.** The neighbour `sysC` is
untouched by `π`, and on a synchronised step it has to accept whichever representative of the
`φ`-fibre the ghost-free system announces, which is what `hsat` grants. The clause `h.silent` is
what keeps the two interleaving disjuncts apart from the synchronised one: a lift of an internal
step is again internal. -/
theorem parallel_right (h : StateErasure sysA sys0 π φ) (hsat : sysC.LabelSaturated φ) :
    StateErasure (sysA.parallel sysC) (sys0.parallel sysC) (Prod.map π id) φ where
  init := by
    change (π sysA.init, sysC.init) = (sys0.init, sysC.init)
    rw [h.init]
  silent := h.silent
  project := by
    rintro ⟨a, c⟩ l μ (⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · exact Or.inl ⟨hl, μ₁.map π, μ₂, h.project a l μ₁ h1, h2, map_prodPMF_right π μ₁ μ₂⟩
    · exact Or.inr (Or.inl ⟨rfl, μ₁.map π, h.project a Silent.τ μ₁ h1,
        map_prodPMF_right π μ₁ (PMF.pure c)⟩)
    · refine Or.inr (Or.inr ⟨rfl, μ₂, h2, ?_⟩)
      rw [map_prodPMF_right π (PMF.pure a) μ₂, PMF.pure_map]
      rfl
  lift := by
    rintro ⟨a, c⟩ l μ (⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · obtain ⟨l', ν₁, hlab, hA, rfl⟩ := h.lift a l μ₁ h1
      have hl' : l' ≠ Silent.τ := fun hτ => hl (h.silent l (by rw [← hlab, hτ]))
      exact ⟨l', prodPMF ν₁ μ₂, hlab,
        Or.inl ⟨hl', ν₁, μ₂, hA, hsat c l l' μ₂ hlab.symm h2, rfl⟩,
        (map_prodPMF_right π ν₁ μ₂).symm⟩
    · obtain ⟨l', ν₁, hlab, hA, rfl⟩ := h.lift a Silent.τ μ₁ h1
      obtain rfl : l' = Silent.τ := h.silent l' hlab
      exact ⟨Silent.τ, prodPMF ν₁ (PMF.pure c), rfl, Or.inr (Or.inl ⟨rfl, ν₁, hA, rfl⟩),
        (map_prodPMF_right π ν₁ (PMF.pure c)).symm⟩
    · refine ⟨Silent.τ, prodPMF (PMF.pure a) μ₂, rfl,
        Or.inr (Or.inr ⟨rfl, μ₂, h2, rfl⟩), ?_⟩
      rw [map_prodPMF_right π (PMF.pure a) μ₂, PMF.pure_map]
      rfl

/-- **Erasure is a congruence for parallel composition on the right factor.** The mirror of
`StateErasure.parallel_right`. -/
theorem parallel_left (h : StateErasure sysA sys0 π φ) (hsat : sysC.LabelSaturated φ) :
    StateErasure (sysC.parallel sysA) (sysC.parallel sys0) (Prod.map id π) φ where
  init := by
    change (sysC.init, π sysA.init) = (sysC.init, sys0.init)
    rw [h.init]
  silent := h.silent
  project := by
    rintro ⟨c, a⟩ l μ (⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · exact Or.inl ⟨hl, μ₁, μ₂.map π, h1, h.project a l μ₂ h2, map_prodPMF_left π μ₁ μ₂⟩
    · refine Or.inr (Or.inl ⟨rfl, μ₁, h1, ?_⟩)
      rw [map_prodPMF_left π μ₁ (PMF.pure a), PMF.pure_map]
      rfl
    · exact Or.inr (Or.inr ⟨rfl, μ₂.map π, h.project a Silent.τ μ₂ h2,
        map_prodPMF_left π (PMF.pure c) μ₂⟩)
  lift := by
    rintro ⟨c, a⟩ l μ (⟨hl, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · obtain ⟨l', ν₂, hlab, hA, rfl⟩ := h.lift a l μ₂ h2
      have hl' : l' ≠ Silent.τ := fun hτ => hl (h.silent l (by rw [← hlab, hτ]))
      exact ⟨l', prodPMF μ₁ ν₂, hlab,
        Or.inl ⟨hl', μ₁, ν₂, hsat c l l' μ₁ hlab.symm h1, hA, rfl⟩,
        (map_prodPMF_left π μ₁ ν₂).symm⟩
    · refine ⟨Silent.τ, prodPMF μ₁ (PMF.pure a), rfl,
        Or.inr (Or.inl ⟨rfl, μ₁, h1, rfl⟩), ?_⟩
      rw [map_prodPMF_left π μ₁ (PMF.pure a), PMF.pure_map]
      rfl
    · obtain ⟨l', ν₂, hlab, hA, rfl⟩ := h.lift a Silent.τ μ₂ h2
      obtain rfl : l' = Silent.τ := h.silent l' hlab
      exact ⟨Silent.τ, prodPMF (PMF.pure c) ν₂, rfl, Or.inr (Or.inr ⟨rfl, ν₂, hA, rfl⟩),
        (map_prodPMF_left π (PMF.pure c) ν₂).symm⟩

end Parallel


/-! ### Abstraction -/

section Abstract

variable {sysA : System SA L} {sys0 : System S0 L} {π : SA → S0} {φ : L → L}

/-- **Erasure is a congruence for abstraction.** Hiding a set of labels saturated along `φ`
keeps the erasure: a hidden label of `sys0` lifts to a hidden label of `sysA`, and a visible
one to a visible one. -/
theorem abstract (h : StateErasure sysA sys0 π φ) (A : Set L)
    (hsat : ∀ l l', φ l = φ l' → (l ∈ A ↔ l' ∈ A)) :
    StateErasure (sysA.abstract A) (sys0.abstract A) π φ where
  init := h.init
  silent := h.silent
  project := by
    rintro s l μ (⟨rfl, l₀, hl₀, hstep⟩ | ⟨hl, hstep⟩)
    · exact Or.inl ⟨rfl, l₀, hl₀, h.project s l₀ μ hstep⟩
    · exact Or.inr ⟨hl, h.project s l μ hstep⟩
  lift := by
    rintro s l μ (⟨rfl, l₀, hl₀, hstep⟩ | ⟨hl, hstep⟩)
    · obtain ⟨l', ν, hlab, hA, hμ⟩ := h.lift s l₀ μ hstep
      exact ⟨Silent.τ, ν, rfl, Or.inl ⟨rfl, l', (hsat l₀ l' hlab.symm).mp hl₀, hA⟩, hμ⟩
    · obtain ⟨l', ν, hlab, hA, hμ⟩ := h.lift s l μ hstep
      exact ⟨l', ν, hlab, Or.inr ⟨fun hm => hl ((hsat l' l hlab).mp hm), hA⟩, hμ⟩

/-- **Hiding every discrepancy of `φ` collapses the erasure to the identity.** Under `hdisc`
a label identified with a different label lies in `A`, so after hiding `A` the lift returns
the label it was given and `StateErasure.achievableTraceDists_eq` applies. -/
theorem abstract_collapse (h : StateErasure sysA sys0 π φ) (A : Set L)
    (hsat : ∀ l l', φ l = φ l' → (l ∈ A ↔ l' ∈ A))
    (hdisc : ∀ l l', φ l = φ l' → l ≠ l' → l ∈ A) :
    StateErasure (sysA.abstract A) (sys0.abstract A) π id where
  init := h.init
  silent := separatesSilent_id
  project := (h.abstract A hsat).project
  lift := by
    intro s l μ hstep
    obtain ⟨l', ν, hlab, hA, hμ⟩ := (h.abstract A hsat).lift s l μ hstep
    refine ⟨l, ν, rfl, ?_, hμ⟩
    obtain rfl : l' = l := by
      by_contra hne
      have hlA : l ∈ A := hdisc l l' hlab.symm (Ne.symm hne)
      have hl'A : l' ∈ A := (hsat l l' hlab.symm).mp hlA
      rcases hstep with ⟨rfl, -⟩ | ⟨hnm, -⟩
      · rcases hA with ⟨rfl, -⟩ | ⟨hnm', -⟩
        · exact hne rfl
        · exact hnm' hl'A
      · exact hnm hlA
    exact hA

end Abstract

/-! ### Restriction along an extended alphabet -/

section Relabel

variable {E : Type} {sysA : System SA (L ⊕ E)} {sys0 : System S0 (L ⊕ E)} {π : SA → S0}
  {φ : L → L} {ψ : E → E}

/-- **Erasure is a congruence for restriction along the left summand.** An identification of
the extended alphabet that is a sum of identifications restricts to its left component, and
the erasure restricts with it. -/
theorem relabel (h : StateErasure sysA sys0 π (Sum.map φ ψ)) :
    StateErasure sysA.relabel sys0.relabel π φ where
  init := h.init
  silent := by
    intro l hl
    refine (inl_eq_tau_iff (Extra := E) l).mp (h.silent (Sum.inl l) ?_)
    change Sum.inl (φ l) = Sum.inl (φ (Silent.τ : L))
    rw [hl]
  project := fun s l μ hstep => h.project s (Sum.inl l) μ hstep
  lift := by
    intro s l μ hstep
    obtain ⟨l', ν, hlab, hA, hμ⟩ := h.lift s (Sum.inl l) μ hstep
    cases l' with
    | inl l'' =>
      exact ⟨l'', ν, Sum.inl_injective hlab, hA, hμ⟩
    | inr e => exact absurd hlab (by simp)

end Relabel

end StateErasure

/-! ### Saturation is preserved by the combinators

An erasure composes against a neighbour saturated along `φ`, so the neighbour's saturation
has to be established for the systems the case study builds. -/

section Saturation

variable {S1 S2 : Type} {φ : L → L}

/-- Saturation is preserved by parallel composition. `hτ` is what keeps the synchronised
disjunct from being asked to answer with the silent label. -/
theorem System.LabelSaturated.parallel {sys₁ : System S1 L} {sys₂ : System S2 L}
    (h₁ : sys₁.LabelSaturated φ) (h₂ : sys₂.LabelSaturated φ) (hτ : SeparatesSilent φ) :
    (sys₁.parallel sys₂).LabelSaturated φ := by
  rintro p l l' μ hlab (⟨hl, μ₁, μ₂, s1, s2, rfl⟩ | ⟨rfl, μ₁, s1, rfl⟩ | ⟨rfl, μ₂, s2, rfl⟩)
  · have hl' : l' ≠ Silent.τ := fun hc => hl (hτ l (by rw [hlab, hc]))
    exact Or.inl ⟨hl', μ₁, μ₂, h₁ p.1 l l' μ₁ hlab s1, h₂ p.2 l l' μ₂ hlab s2, rfl⟩
  · obtain rfl : l' = Silent.τ := hτ l' hlab.symm
    exact Or.inr (Or.inl ⟨rfl, μ₁, s1, rfl⟩)
  · obtain rfl : l' = Silent.τ := hτ l' hlab.symm
    exact Or.inr (Or.inr ⟨rfl, μ₂, s2, rfl⟩)

/-- Saturation is preserved by abstraction of a `φ`-saturated set of labels. -/
theorem System.LabelSaturated.abstract {sys : System S1 L} (h : sys.LabelSaturated φ)
    (hτ : SeparatesSilent φ) (A : Set L)
    (hsat : ∀ l l', φ l = φ l' → (l ∈ A ↔ l' ∈ A)) :
    (sys.abstract A).LabelSaturated φ := by
  rintro s l l' μ hlab (⟨rfl, l₀, hl₀, hstep⟩ | ⟨hl, hstep⟩)
  · obtain rfl : l' = Silent.τ := hτ l' hlab.symm
    exact Or.inl ⟨rfl, l₀, hl₀, hstep⟩
  · exact Or.inr ⟨fun hm => hl ((hsat l' l hlab.symm).mp hm), h s l l' μ hlab hstep⟩

/-- Saturation is preserved by the full-synchronisation product of a finite family. -/
theorem System.LabelSaturated.synchronisedProduct {ι : Type} [Fintype ι] [DecidableEq ι]
    {State : ι → Type} {sys : ∀ i, System (State i) L}
    (h : ∀ i, (sys i).LabelSaturated φ) (hτ : SeparatesSilent φ) :
    (System.synchronisedProduct sys).LabelSaturated φ := by
  rintro s l l' μ hlab (⟨hl, μ_, hstep, rfl⟩ | ⟨rfl, i, μ_i, hstep, rfl⟩)
  · have hl' : l' ≠ Silent.τ := fun hc => hl (hτ l (by rw [hlab, hc]))
    exact Or.inl ⟨hl', μ_, fun i => h i (s i) l l' (μ_ i) hlab (hstep i), rfl⟩
  · obtain rfl : l' = Silent.τ := hτ l' hlab.symm
    exact Or.inr ⟨rfl, i, μ_i, hstep, rfl⟩

omit [Silent L] in
/-- Saturation is preserved by the partial label pullback `System.mapIdle`, along an
identification `φ'` of the finer alphabet that the pullback carries to `φ`: two labels
identified by `φ'` are both undelegated, or delegate to labels identified by `φ`. -/
theorem System.LabelSaturated.mapIdle {L' : Type} {sys : System S1 L} {ϑ : L' → Option L}
    {φ' : L' → L'} (h : sys.LabelSaturated φ)
    (hϑ : ∀ l₁ l₂, φ' l₁ = φ' l₂ →
      (ϑ l₁ = none ∧ ϑ l₂ = none) ∨
      ∃ m₁ m₂, ϑ l₁ = some m₁ ∧ ϑ l₂ = some m₂ ∧ φ m₁ = φ m₂) :
    (sys.mapIdle ϑ).LabelSaturated φ' := by
  intro s l₁ l₂ μ hlab hstep
  rw [System.mapIdle_step] at hstep ⊢
  rcases hϑ l₁ l₂ hlab with ⟨hn₁, hn₂⟩ | ⟨m₁, m₂, hm₁, hm₂, hm⟩
  · rcases hstep with ⟨m, hmeq, -⟩ | ⟨-, hpure⟩
    · rw [hn₁] at hmeq
      exact absurd hmeq (by simp)
    · exact Or.inr ⟨hn₂, hpure⟩
  · rcases hstep with ⟨m, hmeq, hs⟩ | ⟨hn, -⟩
    · have hmm : m = m₁ := Option.some.inj (by rw [← hmeq, hm₁])
      subst hmm
      exact Or.inl ⟨m₂, hm₂, h s m m₂ μ hm hs⟩
    · rw [hn] at hm₁
      exact absurd hm₁ (by simp)

end Saturation

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.StateErasure.achievableTraceDists_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StateErasure.achievableTraceDists_eq

end PLTS
