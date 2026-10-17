/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Results
import Leslie2.Simulation.ForwardLTS
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# Removal of an auxiliary state component

A system is often written with a state component that no other component of the state depends
on: a history of what has already happened, carried so that an invariant can be stated over it.
Such a component is an auxiliary variable in the sense of Abadi and Lamport, *The existence of
refinement mappings* (1991), here between systems whose steps are distributions. A step may read
the component to decide the value its label announces. A step on a label of a set `K` may also
read it to decide whether it fires, provided the step leaves every other component of the state
where it stands. Removing the component has to leave the observable behaviour untouched once the
labels of `K` are hidden.

`AuxiliaryVariableRemoval sysA sys0 π φ K` is that statement. The map `π : SA → S0` deletes the
component, `φ : L → L` identifies the labels that differ only in the value the component
announces, and `K` holds the labels whose transitions leave the projection where it stands.
Three clauses carry the content.

* `projectUnchanged` — every transition `s -[l]→ μ` of `sysA` with `l ∈ K` leaves the projection
  where it stands: `μ.map π = δ_{π s}`.
* `project` — every transition `s -[l]→ μ` of `sysA` with `l ∉ K` is a transition
  `π s -[l]→ μ.map π` of `sys0` on the same label, or is silent with `μ.map π = δ_{π s}`.
  Outside `K` the component adds no step, and the distribution projected along `π` is unchanged.
* `lift` — every transition `π s -[l]→ μ` of `sys0` is met by a transition `s -[l']→ ν` of
  `sysA` with `φ l' = φ l` and `μ = ν.map π`. The component blocks no transition of `sys0`.

The clauses `project` and `lift` are not symmetric. A label of `sysA` may announce the value of
the removed component, and from a state `s` only the announcement `s` carries is available,
whereas `sys0` has nothing to announce from and offers every label of the `φ`-fibre. So the
projection is exact on labels and only the lift is taken up to `φ`. A fourth clause, `silent`,
keeps `τ` alone in its `φ`-fibre (`SeparatesSilent`), so a lift never matches an internal step
with an external one or the reverse.

A silent transition of `sysA` that leaves the projection where it stands is matched by the weak
transition `weakTau_refl` of `sys0`, from `δ_{π s}` to itself, and every other transition by the
transition `project` gives. When every label of `K` is silent, the graph of `π` is therefore a
probabilistic forward simulation (`AuxiliaryVariableRemoval.probabilisticForwardSimulation`), and
the soundness of probabilistic forward simulation
(`ProbabilisticForwardSimulation.achievableTraceDists_subset`) gives the inclusion
`AuxiliaryVariableRemoval.achievableTraceDists_subset`. At `φ = id` the lift is
label-exact, so it is a probabilistic forward simulation in the opposite direction
(`ProbabilisticForwardSimulation.ofStrongFunctional_converse`), and the two sets of achievable
trace distributions coincide: `AuxiliaryVariableRemoval.achievableTraceDists_eq`. A general `φ`
reaches that equality through `AuxiliaryVariableRemoval.abstract_collapse`, which hides every
label `φ` identifies with a different label and returns a removal at `φ = id`.

## Congruences

A removal is preserved by parallel composition in either position, against a component whose
step relation is saturated along `φ` (`System.LabelSaturated`) and whose transitions on the labels
of `K` are idle self-loops (`System.IdleOn`). It is preserved by abstraction of a `φ`-saturated
set `A` of labels, which turns the transitions on the labels of `K ∩ A` into silent transitions
that leave the projection where it stands, and by restriction along the left summand of an
extended alphabet (`Framework/Relabel.lean`). The idle self-loops on `K` are preserved by the
full-synchronisation product (`Framework/SynchronisedProduct.lean`) and the partial label pullback
`System.mapIdle` (`Framework/LoopsAndInstanceFamilies.lean`). -/

namespace PLTS

variable {SA S0 SC L : Type} [Silent L]

/-! ### The label conditions -/

/-- `φ` **separates the silent label**: `τ` is alone in its `φ`-fibre. A removal asks this
of its label identification, so that the fibre of an internal label holds no external one. -/
def SeparatesSilent (φ : L → L) : Prop :=
  ∀ l, φ l = φ (Silent.τ : L) → l = Silent.τ

/-- The identity separates the silent label: its fibres are singletons. -/
theorem separatesSilent_id : SeparatesSilent (id : L → L) := fun _ h => h

/-- A system is **saturated along `φ`** when its step relation is constant on the `φ`-fibres of the
label: labels with the same `φ`-image have the same outgoing transitions. This is the hypothesis
under which a system is a neighbour of a removal in a composition — it accepts whichever
representative of a fibre the system without the component announces. -/
def System.LabelSaturated (sys : System SC L) (φ : L → L) : Prop :=
  ∀ s l l' μ, φ l = φ l' → sys.step s l μ → sys.step s l' μ

omit [Silent L] in
/-- Every system is saturated along the identity. -/
theorem System.labelSaturated_id (sys : System SC L) : sys.LabelSaturated (id : L → L) := by
  intro _ l l' _ h hstep
  have hll : l = l' := h
  exact hll ▸ hstep

omit [Silent L] in
/-- A system is **idle on `K`** when every transition on a label of `K` is an idle self-loop,
the Dirac distribution on the state it leaves. This is the second hypothesis under which a
system is a neighbour of a removal in a composition: on a label of `K` it takes no transition
that moves its own state. -/
def System.IdleOn (sys : System SC L) (K : Set L) : Prop :=
  ∀ s l μ, l ∈ K → sys.step s l μ → μ = PMF.pure s

/-! ### Removal -/

/-- **Removal of an auxiliary state component.** `π` deletes the component, `φ` identifies
the labels that differ only in the value the component announces, and the transitions on the
labels of `K` leave the projection where it stands. -/
structure AuxiliaryVariableRemoval (sysA : System SA L) (sys0 : System S0 L) (π : SA → S0)
    (φ : L → L) (K : Set L) : Prop where
  /-- `π` carries the initial state to the initial state. -/
  init : π sysA.init = sys0.init
  /-- `τ` is alone in its `φ`-fibre. -/
  silent : SeparatesSilent φ
  /-- Every transition of `sysA` on a label of `K` leaves the projection where it stands. -/
  projectUnchanged : ∀ s l μ, l ∈ K → sysA.step s l μ → μ.map π = PMF.pure (π s)
  /-- Every transition of `sysA` on a label outside `K` projects to a transition of `sys0` on
  the same label, or is silent and leaves the projection where it stands. -/
  project : ∀ s l μ, l ∉ K → sysA.step s l μ →
    sys0.step (π s) l (μ.map π) ∨ (l = Silent.τ ∧ μ.map π = PMF.pure (π s))
  /-- Every transition of `sys0` out of a `π`-image lifts, up to `φ`, to a transition of
  `sysA`. -/
  lift : ∀ s l μ, sys0.step (π s) l μ → ∃ l' ν, φ l' = φ l ∧ sysA.step s l' ν ∧ μ = ν.map π

namespace AuxiliaryVariableRemoval

variable {sysA : System SA L} {sys0 : System S0 L} {π : SA → S0} {φ : L → L} {K : Set L}

/-- **The graph of the projection is a probabilistic forward simulation** when every label of
`K` is silent. The coupling pairs each outcome `s'` of a transition of `sysA` with `δ_{π s'}`.
A transition that `project` carries to `sys0` is matched by that transition, read as a weak
transition. A silent transition that leaves the projection where it stands, which every
transition on a label of `K` is under `hK`, is matched by the weak transition `weakTau_refl` of
`sys0` from `δ_{π s}` to itself. -/
theorem probabilisticForwardSimulation (h : AuxiliaryVariableRemoval sysA sys0 π φ K)
    (hK : ∀ l ∈ K, l = Silent.τ) :
    ProbabilisticForwardSimulation sysA sys0 (diracRel (fun s t => t = π s)) := by
  refine ⟨⟨PMF.pure (π sysA.init), ?_, π sysA.init, rfl, rfl⟩, ?_⟩
  · intro t ht
    rw [PMF.mem_support_pure_iff] at ht
    rw [ht, h.init]
  · rintro s μ_A ⟨t, rfl, rfl⟩ l μ hstep
    refine ⟨μ.map (fun s' => PMF.pure (π s')),
      ⟨μ.map (fun s' => (s', PMF.pure (π s'))), ?_, ?_, ?_⟩, ?_⟩
    · rw [PMF.map_comp]; exact PMF.map_id μ
    · rw [PMF.map_comp]; rfl
    · intro p hp
      rw [PMF.mem_support_map_iff] at hp
      obtain ⟨s', -, rfl⟩ := hp
      exact ⟨π s', rfl, rfl⟩
    · have hbind : (μ.map (fun s' => PMF.pure (π s'))).bind id = μ.map π := by
        rw [PMF.bind_map, Function.id_comp]; rfl
      rw [hbind]
      by_cases hl : l ∈ K
      · rw [h.projectUnchanged s l μ hl hstep]
        exact Or.inl ⟨hK l hl, weakTau_refl sys0 _⟩
      · rcases h.project s l μ hl hstep with h0 | ⟨hτ, hμ⟩
        · by_cases hτ : l = Silent.τ
          · exact Or.inl ⟨hτ, weakTau_of_step hτ h0⟩
          · exact Or.inr ⟨hτ, weakStep_strong h0⟩
        · rw [hμ]
          exact Or.inl ⟨hτ, weakTau_refl sys0 _⟩

/-- **Removal includes trace distributions** when every label of `K` is silent: the graph of
the projection is a probabilistic forward simulation
(`AuxiliaryVariableRemoval.probabilisticForwardSimulation`), and a probabilistic forward
simulation includes trace distributions
(`ProbabilisticForwardSimulation.achievableTraceDists_subset`). -/
theorem achievableTraceDists_subset (h : AuxiliaryVariableRemoval sysA sys0 π φ K)
    (hK : ∀ l ∈ K, l = Silent.τ) :
    achievableTraceDists sysA ⊆ achievableTraceDists sys0 :=
  (h.probabilisticForwardSimulation hK).achievableTraceDists_subset

/-- **A removal at `φ = id` preserves trace distributions** when every label of `K` is silent.
The projection gives one inclusion; the lift, being label-exact, is a probabilistic forward
simulation of `sys0` by `sysA` and gives the other. -/
theorem achievableTraceDists_eq (h : AuxiliaryVariableRemoval sysA sys0 π id K)
    (hK : ∀ l ∈ K, l = Silent.τ) :
    achievableTraceDists sysA = achievableTraceDists sys0 := by
  refine Set.Subset.antisymm (h.achievableTraceDists_subset hK) ?_
  refine (ProbabilisticForwardSimulation.ofStrongFunctional_converse π h.init ?_)
    |>.achievableTraceDists_subset
  intro s l μ hstep
  obtain ⟨l', ν, hl, hA, hμ⟩ := h.lift s l μ hstep
  have hll : l' = l := hl
  exact ⟨ν, hll ▸ hA, hμ⟩

/-! ### Parallel composition -/

section Parallel

variable {sysA : System SA L} {sys0 : System S0 L} {π : SA → S0} {φ : L → L} {K : Set L}
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

/-- **Removal is a congruence for parallel composition on the left factor.** The neighbour `sysC` is
untouched by `π`, and on a synchronised step it has to accept whichever representative of the
`φ`-fibre `sys0` announces, which is what `hsat` grants. On a label of `K` the
neighbour takes its idle self-loop alone (`hidle`), so a transition of the composition on that
label leaves the projection where it stands. The clause `h.silent` is what keeps the two
interleaving disjuncts apart from the synchronised one: a lift of an internal step is again
internal. -/
theorem parallel_right (h : AuxiliaryVariableRemoval sysA sys0 π φ K)
    (hsat : sysC.LabelSaturated φ) (hidle : sysC.IdleOn K) :
    AuxiliaryVariableRemoval (sysA.parallel sysC) (sys0.parallel sysC) (Prod.map π id) φ K where
  init := by
    change (π sysA.init, sysC.init) = (sys0.init, sysC.init)
    rw [h.init]
  silent := h.silent
  projectUnchanged := by
    rintro ⟨a, c⟩ l μ hl (⟨-, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · rw [map_prodPMF_right, h.projectUnchanged a l μ₁ hl h1, hidle c l μ₂ hl h2,
        prodPMF_pure_pure]
      rfl
    · rw [map_prodPMF_right, h.projectUnchanged a _ μ₁ hl h1, prodPMF_pure_pure]
      rfl
    · rw [hidle c _ μ₂ hl h2, map_prodPMF_right, PMF.pure_map, prodPMF_pure_pure]
      rfl
  project := by
    rintro ⟨a, c⟩ l μ hl (⟨hτ, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · rcases h.project a l μ₁ hl h1 with h0 | ⟨hτ', -⟩
      · exact Or.inl (Or.inl ⟨hτ, μ₁.map π, μ₂, h0, h2, map_prodPMF_right π μ₁ μ₂⟩)
      · exact absurd hτ' hτ
    · rcases h.project a _ μ₁ hl h1 with h0 | ⟨-, hμ⟩
      · exact Or.inl (Or.inr (Or.inl ⟨rfl, μ₁.map π, h0,
          map_prodPMF_right π μ₁ (PMF.pure c)⟩))
      · refine Or.inr ⟨rfl, ?_⟩
        rw [map_prodPMF_right, hμ, prodPMF_pure_pure]
        rfl
    · refine Or.inl (Or.inr (Or.inr ⟨rfl, μ₂, h2, ?_⟩))
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

/-- **Removal is a congruence for parallel composition on the right factor.** The mirror of
`AuxiliaryVariableRemoval.parallel_right`. -/
theorem parallel_left (h : AuxiliaryVariableRemoval sysA sys0 π φ K)
    (hsat : sysC.LabelSaturated φ) (hidle : sysC.IdleOn K) :
    AuxiliaryVariableRemoval (sysC.parallel sysA) (sysC.parallel sys0) (Prod.map id π) φ K where
  init := by
    change (sysC.init, π sysA.init) = (sysC.init, sys0.init)
    rw [h.init]
  silent := h.silent
  projectUnchanged := by
    rintro ⟨c, a⟩ l μ hl (⟨-, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · rw [map_prodPMF_left, hidle c l μ₁ hl h1, h.projectUnchanged a l μ₂ hl h2,
        prodPMF_pure_pure]
      rfl
    · rw [hidle c _ μ₁ hl h1, map_prodPMF_left, PMF.pure_map, prodPMF_pure_pure]
      rfl
    · rw [map_prodPMF_left, h.projectUnchanged a _ μ₂ hl h2, prodPMF_pure_pure]
      rfl
  project := by
    rintro ⟨c, a⟩ l μ hl (⟨hτ, μ₁, μ₂, h1, h2, rfl⟩ | ⟨rfl, μ₁, h1, rfl⟩ | ⟨rfl, μ₂, h2, rfl⟩)
    · rcases h.project a l μ₂ hl h2 with h0 | ⟨hτ', -⟩
      · exact Or.inl (Or.inl ⟨hτ, μ₁, μ₂.map π, h1, h0, map_prodPMF_left π μ₁ μ₂⟩)
      · exact absurd hτ' hτ
    · refine Or.inl (Or.inr (Or.inl ⟨rfl, μ₁, h1, ?_⟩))
      rw [map_prodPMF_left π μ₁ (PMF.pure a), PMF.pure_map]
      rfl
    · rcases h.project a _ μ₂ hl h2 with h0 | ⟨-, hμ⟩
      · exact Or.inl (Or.inr (Or.inr ⟨rfl, μ₂.map π, h0,
          map_prodPMF_left π (PMF.pure c) μ₂⟩))
      · refine Or.inr ⟨rfl, ?_⟩
        rw [map_prodPMF_left, hμ, prodPMF_pure_pure]
        rfl
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

variable {sysA : System SA L} {sys0 : System S0 L} {π : SA → S0} {φ : L → L} {K : Set L}

/-- **Removal is a congruence for abstraction.** Hiding a set `A` of labels saturated along `φ`
keeps the removal, at the labels `K \ A`. A hidden label of `sys0` lifts to a hidden label of
`sysA`, and a visible one to a visible one. A transition of `sysA` on a label of `K ∩ A` becomes
a silent transition that leaves the projection where it stands. The silent transitions of the
abstraction also include the hidden transitions on labels outside `K`, which move the
projection, so `hτ` keeps `τ` out of `K \ A`. -/
theorem abstract (h : AuxiliaryVariableRemoval sysA sys0 π φ K) (A : Set L)
    (hsat : ∀ l l', φ l = φ l' → (l ∈ A ↔ l' ∈ A)) (hτ : (Silent.τ : L) ∉ K \ A) :
    AuxiliaryVariableRemoval (sysA.abstract A) (sys0.abstract A) π φ (K \ A) where
  init := h.init
  silent := h.silent
  projectUnchanged := by
    rintro s l μ hl (⟨rfl, -, -, -⟩ | ⟨-, hstep⟩)
    · exact absurd hl hτ
    · exact h.projectUnchanged s l μ hl.1 hstep
  project := by
    rintro s l μ hl (⟨rfl, l₀, hl₀, hstep⟩ | ⟨hlA, hstep⟩)
    · by_cases hK : l₀ ∈ K
      · exact Or.inr ⟨rfl, h.projectUnchanged s l₀ μ hK hstep⟩
      · rcases h.project s l₀ μ hK hstep with h0 | ⟨-, hμ⟩
        · exact Or.inl (Or.inl ⟨rfl, l₀, hl₀, h0⟩)
        · exact Or.inr ⟨rfl, hμ⟩
    · have hK : l ∉ K := fun hm => hl ⟨hm, hlA⟩
      rcases h.project s l μ hK hstep with h0 | hτμ
      · exact Or.inl (Or.inr ⟨hlA, h0⟩)
      · exact Or.inr hτμ
  lift := by
    rintro s l μ (⟨rfl, l₀, hl₀, hstep⟩ | ⟨hl, hstep⟩)
    · obtain ⟨l', ν, hlab, hA, hμ⟩ := h.lift s l₀ μ hstep
      exact ⟨Silent.τ, ν, rfl, Or.inl ⟨rfl, l', (hsat l₀ l' hlab.symm).mp hl₀, hA⟩, hμ⟩
    · obtain ⟨l', ν, hlab, hA, hμ⟩ := h.lift s l μ hstep
      exact ⟨l', ν, hlab, Or.inr ⟨fun hm => hl ((hsat l' l hlab).mp hm), hA⟩, hμ⟩

/-- **Hiding every discrepancy of `φ` collapses the removal to the identity.** Under `hdisc`
a label identified with a different label lies in `A`, so after hiding `A` the lift returns
the label it was given and `AuxiliaryVariableRemoval.achievableTraceDists_eq` applies. -/
theorem abstract_collapse (h : AuxiliaryVariableRemoval sysA sys0 π φ K) (A : Set L)
    (hsat : ∀ l l', φ l = φ l' → (l ∈ A ↔ l' ∈ A))
    (hdisc : ∀ l l', φ l = φ l' → l ≠ l' → l ∈ A) (hτ : (Silent.τ : L) ∉ K \ A) :
    AuxiliaryVariableRemoval (sysA.abstract A) (sys0.abstract A) π id (K \ A) where
  init := h.init
  silent := separatesSilent_id
  projectUnchanged := (h.abstract A hsat hτ).projectUnchanged
  project := (h.abstract A hsat hτ).project
  lift := by
    intro s l μ hstep
    obtain ⟨l', ν, hlab, hA, hμ⟩ := (h.abstract A hsat hτ).lift s l μ hstep
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
  {φ : L → L} {ψ : E → E} {K : Set (L ⊕ E)}

/-- **Removal is a congruence for restriction along the left summand.** An identification of
the extended alphabet that is a sum of identifications restricts to its left component, and
the removal restricts with it, at the labels of `K` on the left summand. -/
theorem relabel (h : AuxiliaryVariableRemoval sysA sys0 π (Sum.map φ ψ) K) :
    AuxiliaryVariableRemoval sysA.relabel sys0.relabel π φ (Sum.inl ⁻¹' K) where
  init := h.init
  silent := by
    intro l hl
    refine (inl_eq_tau_iff (Extra := E) l).mp (h.silent (Sum.inl l) ?_)
    change Sum.inl (φ l) = Sum.inl (φ (Silent.τ : L))
    rw [hl]
  projectUnchanged := fun s l μ hl hstep => h.projectUnchanged s (Sum.inl l) μ hl hstep
  project := by
    intro s l μ hl hstep
    rcases h.project s (Sum.inl l) μ hl hstep with h0 | ⟨hτ, hμ⟩
    · exact Or.inl h0
    · exact Or.inr ⟨(inl_eq_tau_iff (Extra := E) l).mp hτ, hμ⟩
  lift := by
    intro s l μ hstep
    obtain ⟨l', ν, hlab, hA, hμ⟩ := h.lift s (Sum.inl l) μ hstep
    cases l' with
    | inl l'' =>
      exact ⟨l'', ν, Sum.inl_injective hlab, hA, hμ⟩
    | inr e => exact absurd hlab (by simp)

end Relabel

end AuxiliaryVariableRemoval

/-! ### Idle self-loops are preserved by the combinators

A removal composes against a neighbour idle on `K`, so the neighbour's idle self-loops have to
be established for the systems the case study builds. -/

section Idle

variable {S1 : Type} {K : Set L}

/-- The full-synchronisation product of a finite family is idle on `K` when every component is:
on a label of `K` every component that steps returns the Dirac distribution on its own state. -/
theorem System.IdleOn.synchronisedProduct {ι : Type} [Fintype ι] [DecidableEq ι]
    {State : ι → Type} {sys : ∀ i, System (State i) L} (h : ∀ i, (sys i).IdleOn K) :
    (System.synchronisedProduct sys).IdleOn K := by
  rintro s l μ hl (⟨-, μ_, hstep, rfl⟩ | ⟨rfl, i, μ_i, hstep, rfl⟩)
  · have hμ : μ_ = fun i => PMF.pure (s i) := funext fun i => h i (s i) l (μ_ i) hl (hstep i)
    rw [hμ, piPMF_pure]
  · rw [h i (s i) _ μ_i hl hstep]
    have hupdate : Function.update (fun j => PMF.pure (s j)) i (PMF.pure (s i)) =
        fun j => PMF.pure (s j) := Function.update_eq_self i _
    rw [hupdate, piPMF_pure]

omit [Silent L] in
/-- The partial label pullback `System.mapIdle` is idle on `K'` when the underlying system is
idle on `K` and `ϑ` sends every label of `K'` to a label of `K` or to no label: an undelegated
label is an idle self-loop by construction. -/
theorem System.IdleOn.mapIdle {L' : Type} {sys : System S1 L} {ϑ : L' → Option L}
    {K' : Set L'} (h : sys.IdleOn K) (hϑ : ∀ l ∈ K', ∀ m, ϑ l = some m → m ∈ K) :
    (sys.mapIdle ϑ).IdleOn K' := by
  intro s l μ hl hstep
  rw [System.mapIdle_step] at hstep
  rcases hstep with ⟨m, hm, hs⟩ | ⟨-, hpure⟩
  · exact h s m μ (hϑ l hl m hm) hs
  · exact hpure

end Idle

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.AuxiliaryVariableRemoval.achievableTraceDists_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AuxiliaryVariableRemoval.achievableTraceDists_eq

end PLTS
