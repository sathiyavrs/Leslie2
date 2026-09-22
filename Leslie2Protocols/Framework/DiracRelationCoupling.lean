/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Simulation.ForwardLTS

/-!
# The couplings a Dirac-lifted relation admits

A relation `R : S → T → Prop` lifts to distributions as `diracRel R`, which
holds of a source state and a target distribution when that distribution is the
point mass on an `R`-image of the state. Two sources admit a coupling by
`PMFRel (diracRel R)` outright.

`coupling_pure` takes a Dirac source to the point mass on a related target.
`coupling_map` takes a source pushed forward along `f` to the same distribution
pushed forward along `g`, whenever `R (f o) (g o)` holds at every `o` in the
support. Each produces the mixture `Ω` a probabilistic forward simulation asks
for, together with the flattening `Ω.bind id` the answering transition ends in.
-/

namespace PLTS

/-- A Dirac source, coupled to the point mass on a related target. -/
theorem coupling_pure {S T : Type} {R : S → T → Prop} {s : S} {t : T} (h : R s t) :
    ∃ Ω : PMF (PMF T), PMFRel (diracRel R) (PMF.pure s) Ω ∧ Ω.bind id = PMF.pure t := by
  refine ⟨PMF.pure (PMF.pure t), ⟨PMF.pure (s, PMF.pure t), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp
    rw [PMF.mem_support_pure_iff] at hp
    subst hp
    exact ⟨t, rfl, h⟩
  · rw [PMF.pure_bind]
    rfl

/-- A source pushed forward along `f`, coupled outcome by outcome to the same
distribution pushed forward along `g`. -/
theorem coupling_map {O S T : Type} {R : S → T → Prop} (ν : PMF O) (f : O → S) (g : O → T)
    (h : ∀ o ∈ ν.support, R (f o) (g o)) :
    ∃ Ω : PMF (PMF T), PMFRel (diracRel R) (ν.map f) Ω ∧ Ω.bind id = ν.map g := by
  refine ⟨ν.map (fun o => PMF.pure (g o)),
    ⟨ν.map (fun o => (f o, PMF.pure (g o))), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.map_comp]
    rfl
  · rw [PMF.map_comp]
    rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    exact ⟨g o, rfl, h o ho⟩
  · rw [PMF.bind_map]
    rfl

end PLTS
