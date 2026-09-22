/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Composition
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The transitions of the graded-agreement round, read off their labels

The round is `relabel ∘ abstract ∘ parallel` over the round's programs beside the round's
network and the two gather instances. The lemmas here unfold that pipeline in both
directions.

`roundOverGathers_step_iff` splits a transition of the round into a hidden event and a family
label. `roundPrograms_idle_inversion` and `roundPrograms_label_inversion` read the round's
programs beside the round's network: on a family label with no image at a program they remain
unchanged, and on a label with an image every program takes its row at that image and the
round's network takes its. The `_pure` and `_step` lemmas build such a transition from the
factors' rows, and `programStep_update` identifies the program function a joint step delivers
pointwise with the old one updated at the acting process.

`roundOverGathersExtended_joint_inversion` reads a visible transition of the three factors as
their rows and a Dirac product. `roundOverGathersExtended_tau_inversion` reads a silent one as
a step of exactly one gather instance. The `roundOverGathers_*` lemmas carry both across the
hiding and the relabelling.

`programStep_*` reads one graded-agreement program's row off its label: the participant's row
as its guards together with the Dirac it produces, and the idle row of a non-participant as
the identity. `networkStep_*` does the same for the round's network.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation Composition

/-! ### Reading and building the round's transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (parallel ∘ synchronisedProduct,
mapIdle, mapIdle)`; the lemmas below unfold it once and for all, in both
directions. -/

/-- The round's step relation, unfolded to the hidden-event case and the
family-label case. -/
theorem roundOverGathers_step_iff (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool)))
    (s : RoundStateOverGathers P.n G₁ G₂) (l : ExtendedLabel P.n)
    (μ : PMF (RoundStateOverGathers P.n G₁ G₂)) :
    (roundOverGathers P r firstGather secondGather).step s l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : RoundEvent P.n,
        (roundOverGathersExtended P r firstGather secondGather).step s (Sum.inr e) μ) ∨
      (roundOverGathersExtended P r firstGather secondGather).step s (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_roundEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_roundEvents l, hstep⟩

/-! ### The transitions of the round's programs

On a label with no image at a program the round's programs remain unchanged. On a label with an image
every program takes its row at that image and the round's network takes its. -/

section RoundPrograms

variable {P : Parameters} {r : ℕ} {u x : ∀ _ : Fin P.n, ProcessRecord P.n} {v v' : Option Bool}
  {L : RoundLabel P.n}

/-- A label with an image other than the silent one is visible. -/
theorem roundLabel_ne_tau {lp : ProgramLabel P.n} (hlp : programLabelMap P.n L = some lp)
    (hlpτ : lp ≠ ProgramLabel.tau) :
    L ≠ (Silent.τ : RoundLabel P.n) := by
  intro hc
  subst hc
  rw [programLabelMap_tau] at hlp
  exact hlpτ (Option.some.inj hlp).symm

/-- A label with no image at a program is visible. -/
theorem roundLabel_ne_tau_of_none (hlp : programLabelMap P.n L = none) :
    L ≠ (Silent.τ : RoundLabel P.n) := by
  intro hc
  subst hc
  rw [programLabelMap_tau] at hlp
  exact Option.some_ne_none _ hlp

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem programsProduct_inversion (hL : L ≠ (Silent.τ : RoundLabel P.n))
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n)}
    (h : (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap
      P.n))).step u L
      μ) :
    ∃ x : ∀ _ : Fin P.n, ProcessRecord P.n, μ = PMF.pure x ∧
      ∀ i, ((gbcaProgram P r i).mapIdle (programLabelMap P.n)).step (u i) L (PMF.pure (x i)) :=
  System.synchronisedProductMapIdle_inversion (fun i => gbcaProgram_isLTS P r i) hL h

/-- **The round's programs remain unchanged** on a label with no image at a program. -/
theorem roundPrograms_idle_inversion (hlp : programLabelMap P.n L = none)
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) L μ) : μ = PMF.pure (u, v) := by
  have hL := roundLabel_ne_tau_of_none hlp
  rw [roundPrograms, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨y, rfl, hall⟩ := programsProduct_inversion hL hs
    have hy : y = u := funext fun i => System.mapIdle_eq_of_step_none hlp (hall i)
    subst hy
    rw [(System.mapIdle_step_none hlp _).mp hn, prodPMF_pure_pure]
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The joint transition of the round's programs.** Every program takes its row at the label's
image and the round's network takes its. -/
theorem roundPrograms_label_inversion {lp : ProgramLabel P.n}
    (hlp : programLabelMap P.n L = some lp) (hlpτ : lp ≠ ProgramLabel.tau)
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) L μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n) (v' : Option Bool), μ = PMF.pure (x, v') ∧
    (∀ i, ProgramStep P r i (u i) lp (PMF.pure (x i))) ∧ NetworkStep P r v lp (PMF.pure v') := by
  have hL := roundLabel_ne_tau hlp hlpτ
  rw [roundPrograms, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨y, rfl, hall⟩ := programsProduct_inversion hL hs
    have hnet : NetworkStep P r v lp μ₂ := (System.mapIdle_step_some hlp _).mp hn
    obtain ⟨v', rfl⟩ := networkStep_dirac hnet
    exact ⟨y, v', prodPMF_pure_pure _ _, fun i => System.step_of_mapIdle_step hlp (hall i), hnet⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The round's programs refuse** a family label outside the round's interface. -/
theorem roundPrograms_outside_inversion (hlp : programLabelMap P.n L = some ProgramLabel.outside)
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) L μ) : False := by
  obtain ⟨y, w, -, -, hnet⟩ := roundPrograms_label_inversion hlp (by simp) h
  exact networkStep_outside hnet

/-- The stutter of the round's programs, read off a Dirac successor. -/
theorem roundPrograms_idle_pure (hlp : programLabelMap P.n L = none)
    (h : (roundPrograms P r).step (u, v) L (PMF.pure (x, v'))) : x = u ∧ v' = v := by
  have he := PMF.pure_injective (roundPrograms_idle_inversion hlp h)
  rw [Prod.mk.injEq] at he
  exact he

/-- The joint transition of the round's programs, read off a Dirac successor. -/
theorem roundPrograms_label_pure {lp : ProgramLabel P.n} (hlp : programLabelMap P.n L = some lp)
    (hlpτ : lp ≠ ProgramLabel.tau) (h : (roundPrograms P r).step (u, v) L (PMF.pure (x, v'))) :
    (∀ i, ProgramStep P r i (u i) lp (PMF.pure (x i))) ∧ NetworkStep P r v lp (PMF.pure v') := by
  obtain ⟨y, w, hμ, hproc, hnet⟩ := roundPrograms_label_inversion hlp hlpτ h
  have he := PMF.pure_injective hμ
  rw [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hproc, hnet⟩

/-- Build the stutter of the round's programs on a label with no image at a program. -/
theorem roundPrograms_idle_step (hlp : programLabelMap P.n L = none) :
    (roundPrograms P r).step (u, v) L (PMF.pure (u, v)) := by
  rw [roundPrograms, System.parallel_step]
  exact Or.inl ⟨roundLabel_ne_tau_of_none hlp, PMF.pure u, PMF.pure v,
    System.synchronisedProductMapIdle_pure (roundLabel_ne_tau_of_none hlp)
      (fun i => System.mapIdle_unchanged hlp),
    System.mapIdle_unchanged hlp, (prodPMF_pure_pure _ _).symm⟩

/-- Build the joint transition of the round's programs from the programs' rows and the row of the
round's network. -/
theorem roundPrograms_label_step {lp : ProgramLabel P.n} (hlp : programLabelMap P.n L = some lp)
    (hlpτ : lp ≠ ProgramLabel.tau) (hproc : ∀ i, ProgramStep P r i (u i) lp (PMF.pure (x i)))
    (hnet : NetworkStep P r v lp (PMF.pure v')) :
    (roundPrograms P r).step (u, v) L (PMF.pure (x, v')) := by
  rw [roundPrograms, System.parallel_step]
  exact Or.inl ⟨roundLabel_ne_tau hlp hlpτ, PMF.pure x, PMF.pure v',
    System.synchronisedProductMapIdle_pure (roundLabel_ne_tau hlp hlpτ)
      (fun i => System.mapIdle_step_of_step hlp (hproc i)),
    System.mapIdle_step_of_step hlp hnet, (prodPMF_pure_pure _ _).symm⟩

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem programStep_update {j : Fin P.n} {q : ProcessRecord P.n} {lp : ProgramLabel P.n}
    (hj : ProgramStep P r j (u j) lp (PMF.pure q))
    (hne : ∀ i, i ≠ j → ProgramStep P r i (u i) lp (PMF.pure (u i))) :
    ∀ i, ProgramStep P r i (u i) lp (PMF.pure (Function.update u j q i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

end RoundPrograms

/-! ### The round's programs beside the two gather instances

A visible label moves all three factors, and the joint distribution is their Dirac product. A silent
label moves exactly one of the two gather instances: the round's programs have no silent
transition. -/

section RoundPre

variable {P : Parameters} {r : ℕ} {G₁ G₂ : Type}
  {firstGather : System G₁ (Gather.InstanceLabel P.n Bool)}
  {secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))}
  {u x : ∀ _ : Fin P.n, ProcessRecord P.n} {v v' : Option Bool} {c c' : G₁} {d d' : G₂}
  {L : RoundLabel P.n}

/-- **The joint inversion.** A visible transition of the round's programs beside the two gather
instances: every factor steps on the label, and the joint distribution is their Dirac product. -/
theorem roundOverGathersExtended_joint_inversion (h1 : firstGather.IsLTS) (h2 : secondGather.IsLTS)
    (hL : L ≠ (Silent.τ : RoundLabel P.n)) {μ : PMF (RoundStateOverGathers P.n G₁ G₂)}
    (h : (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d)) L μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n) (v' : Option Bool) (c' : G₁) (d' : G₂),
      μ = PMF.pure ((x, v'), (c', d')) ∧
      (roundPrograms P r).step (u, v) L (PMF.pure (x, v')) ∧
      (firstGather.mapIdle (firstGatherLabelMap P.n)).step c L (PMF.pure c') ∧
      (secondGather.mapIdle (secondGatherLabelMap P.n)).step d L (PMF.pure d') := by
  rw [roundOverGathersExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hlay, hga, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨⟨y, w⟩, rfl⟩ := roundPrograms_isLTS P r _ _ _ hlay
    rw [System.parallel_step] at hga
    rcases hga with ⟨-, ρ₁, ρ₂, hc, hd, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨c', rfl⟩ := System.mapIdle_isLTS _ h1 _ _ _ hc
      obtain ⟨d', rfl⟩ := System.mapIdle_isLTS _ h2 _ _ _ hd
      exact ⟨y, w, c', d', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hlay, hc, hd⟩
    · exact absurd hτ hL
    · exact absurd hτ hL
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The silent inversion.** A silent transition of the round's programs beside the two gather
instances is a silent step of one gather instance. -/
theorem roundOverGathersExtended_tau_inversion (h1 : firstGather.IsLTS) (h2 : secondGather.IsLTS)
    {μ : PMF (RoundStateOverGathers P.n G₁ G₂)}
    (h : (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c,
      d)) (Silent.τ : RoundLabel P.n) μ) :
    (∃ c', μ = PMF.pure ((u, v), (c', d)) ∧
      firstGather.step c (Silent.τ : Gather.InstanceLabel P.n Bool) (PMF.pure c')) ∨
    (∃ d', μ = PMF.pure ((u, v), (c, d')) ∧
      secondGather.step d (Silent.τ : Gather.InstanceLabel P.n (Option Bool)) (PMF.pure d')) := by
  rw [roundOverGathersExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hlay, rfl⟩ | ⟨-, μ₂, hga, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hlay roundPrograms_no_tau
  · rw [System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ρ₁, hc, rfl⟩ | ⟨-, ρ₂, hd, rfl⟩
    · exact absurd rfl hτ
    · have hstep := (System.mapIdle_step_some (firstGatherLabelMap_tau P.n) _).mp hc
      obtain ⟨c', rfl⟩ := h1 _ _ _ hstep
      exact Or.inl ⟨c', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩
    · have hstep := (System.mapIdle_step_some (secondGatherLabelMap_tau P.n) _).mp hd
      obtain ⟨d', rfl⟩ := h2 _ _ _ hstep
      exact Or.inr ⟨d', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩

/-- Build a visible transition of the round's programs beside the two gather instances. -/
theorem roundOverGathersExtended_label_step (hL : L ≠ (Silent.τ : RoundLabel P.n))
    (hRoundPrograms : (roundPrograms P r).step (u, v) L (PMF.pure (x, v')))
    (hga1 : (firstGather.mapIdle (firstGatherLabelMap P.n)).step c L (PMF.pure c'))
    (hga2 : (secondGather.mapIdle (secondGatherLabelMap P.n)).step d L (PMF.pure d')) :
    (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d)) L
    (PMF.pure ((x, v'), (c', d'))) := by
  rw [roundOverGathersExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, v'), PMF.pure (c', d'), hRoundPrograms, ?_,
    (prodPMF_pure_pure _ _).symm⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure c', PMF.pure d', hga1, hga2, (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the round's programs beside the two gather instances from a silent
step of the first gather. -/
theorem roundOverGathersExtended_tau_firstGather
    (h : firstGather.step c (Silent.τ : Gather.InstanceLabel P.n Bool) (PMF.pure c')) :
    (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d))
    (Silent.τ : RoundLabel P.n) (PMF.pure ((u, v), (c', d))) := by
  rw [roundOverGathersExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (c', d), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure c',
    (System.mapIdle_step_some (firstGatherLabelMap_tau P.n) _).mpr h, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the round's programs beside the two gather instances from a silent
step of the second gather. -/
theorem roundOverGathersExtended_tau_secondGather
    (h : secondGather.step d (Silent.τ : Gather.InstanceLabel P.n (Option Bool)) (PMF.pure d')) :
    (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d))
    (Silent.τ : RoundLabel P.n) (PMF.pure ((u, v), (c, d'))) := by
  rw [roundOverGathersExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (c, d'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure d',
    (System.mapIdle_step_some (secondGatherLabelMap_tau P.n) _).mpr h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the round. -/
theorem roundOverGathers_event_step (e : RoundEvent P.n)
    (hRoundPrograms : (roundPrograms P r).step (u, v) (Sum.inr e) (PMF.pure (x, v')))
    (hga1 : (firstGather.mapIdle (firstGatherLabelMap P.n)).step c (Sum.inr e) (PMF.pure c'))
    (hga2 : (secondGather.mapIdle (secondGatherLabelMap P.n)).step d (Sum.inr e) (PMF.pure d')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) (Sum.inl Label.tau)
      (PMF.pure ((x, v'), (c', d'))) :=
  (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr
    (Or.inl ⟨rfl, e, roundOverGathersExtended_label_step (by simp) hRoundPrograms hga1 hga2⟩)

/-- A visible family label is a transition of the round. -/
theorem roundOverGathers_label_step {l : ExtendedLabel P.n} (hl : l ≠ Sum.inl Label.tau)
    (hRoundPrograms : (roundPrograms P r).step (u, v) (Sum.inl l) (PMF.pure (x, v')))
    (hga1 : (firstGather.mapIdle (firstGatherLabelMap P.n)).step c (Sum.inl l) (PMF.pure c'))
    (hga2 : (secondGather.mapIdle (secondGatherLabelMap P.n)).step d (Sum.inl l) (PMF.pure d')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) l
    (PMF.pure ((x, v'), (c', d'))) := by
  refine (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr
    (Or.inr (roundOverGathersExtended_label_step ?_ hRoundPrograms hga1 hga2))
  rw [roundLabel_tau]
  simpa using hl

/-- A silent step of the first gather is a silent transition of the round. -/
theorem roundOverGathers_tau_firstGather
    (h : firstGather.step c (Silent.τ : Gather.InstanceLabel P.n Bool) (PMF.pure c')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) (Sum.inl Label.tau)
    (PMF.pure ((u, v), (c', d))) :=
  (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr (Or.inr
    (roundOverGathersExtended_tau_firstGather h))

/-- A silent step of the second gather is a silent transition of the round. -/
theorem roundOverGathers_tau_secondGather
    (h : secondGather.step d (Silent.τ : Gather.InstanceLabel P.n (Option Bool)) (PMF.pure d')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) (Sum.inl Label.tau)
      (PMF.pure ((u, v), (c, d'))) :=
  (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr (Or.inr
    (roundOverGathersExtended_tau_secondGather h))

end RoundPre

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. -/

section ProcInversion

variable {P : Parameters} {r : ℕ} {j : Fin P.n} {p : ProcessRecord P.n} {ν : PMF (ProcessRecord
  P.n)}

/-- A call row names the program's own round. -/
theorem programStep_callG_round {r' : ℕ} {i : Fin P.n} {b : Bool}
    (h : ProgramStep P r j p (.callG r' i b) ν) : r' = r := by cases h <;> rfl

/-- A call-loop row names the program's own round. -/
theorem programStep_callLoop_round {r' : ℕ} {i : Fin P.n} {b : Bool}
    (h : ProgramStep P r j p (.callLoop r' i b) ν) : r' = r := by cases h <;> rfl

/-- A return row names the program's own round. -/
theorem programStep_retG_round {r' : ℕ} {i : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : ProgramStep P r j p (.retG r' i out bnd) ν) : r' = r := by cases h <;> rfl

theorem programStep_callG_own {b : Bool} (h : ProgramStep P r j p (.callG r j b) ν) :
    p.input = none ∧ ν = PMF.pure { p with input := some b } := by
  cases h
  case callG => exact ⟨by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_callG_foreign {i : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.callG r i b) ν) : ν = PMF.pure p := by
  cases h
  case callG => exact absurd rfl hi
  case callGIdle => rfl

theorem programStep_callLoop {i : Fin P.n} {b : Bool}
    (h : ProgramStep P r j p (.callLoop r i b) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl
  case callLoopIdle => rfl

theorem programStep_firstGatherReturn_own {g : Fin P.n → Option Bool}
    {C : Gather.AcceptedPairs P.n Bool} (h : ProgramStep P r j p (.firstGatherReturn j g C) ν) :
    p.input ≠ none ∧ p.candidate = none ∧ ν = PMF.pure
    { p with candidate := some (candidate P g) } := by
  cases h
  case firstGatherReturn => exact ⟨by assumption, by assumption, rfl⟩
  case firstGatherReturnIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_firstGatherReturn_foreign {i : Fin P.n} {g : Fin P.n → Option Bool}
    {C : Gather.AcceptedPairs P.n Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.firstGatherReturn i g C) ν) : ν = PMF.pure p := by
  cases h
  case firstGatherReturn => exact absurd rfl hi
  case firstGatherReturnIdle => rfl

theorem programStep_secondGatherCall_own {x : Option Bool}
    (h : ProgramStep P r j p (.secondGatherCall j x) ν) :
    p.candidate = some x ∧ p.secondGatherCalled = false ∧ ν = PMF.pure
    { p with secondGatherCalled := true } := by
  cases h
  case secondGatherCall => exact ⟨by assumption, by assumption, rfl⟩
  case secondGatherCallIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_secondGatherCall_foreign {i : Fin P.n} {x : Option Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.secondGatherCall i x) ν) : ν = PMF.pure p := by
  cases h
  case secondGatherCall => exact absurd rfl hi
  case secondGatherCallIdle => rfl

theorem programStep_secondGatherReturn_own {g : Fin P.n → Option (Option Bool)}
    {C : Gather.AcceptedPairs P.n (Option Bool)}
    (h : ProgramStep P r j p (.secondGatherReturn j g C) ν) :
    p.secondGatherCalled = true ∧ p.output = none ∧ ν = PMF.pure
    { p with output := some (gradeOf P g) } := by
  cases h
  case secondGatherReturn => exact ⟨by assumption, by assumption, rfl⟩
  case secondGatherReturnIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_secondGatherReturn_foreign {i : Fin P.n} {g : Fin P.n → Option (Option Bool)}
    {C : Gather.AcceptedPairs P.n (Option Bool)} (hi : i ≠ j)
    (h : ProgramStep P r j p (.secondGatherReturn i g C) ν) : ν = PMF.pure p := by
  cases h
  case secondGatherReturn => exact absurd rfl hi
  case secondGatherReturnIdle => rfl

theorem programStep_retG_own {out : GBCAOutput} {bnd : Bool}
    (h : ProgramStep P r j p (.retG r j out bnd) ν) :
    p.output = some out ∧ p.returned = false ∧
      ν = PMF.pure { p with output := none, returned := true } := by
  cases h
  case retG => exact ⟨by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_retG_foreign {i : Fin P.n} {out : GBCAOutput} {bnd : Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.retG r i out bnd) ν) : ν = PMF.pure p := by
  cases h
  case retG => exact absurd rfl hi
  case retGIdle => rfl

end ProcInversion

/-! ### The rules of the round's network, by label class -/

section NetInversion

variable {P : Parameters} {r : ℕ} {w : Option Bool} {μ : PMF (Option Bool)}

theorem networkStep_callG {id : Fin P.n} {b : Bool} (h : NetworkStep P r w (.callG r id b) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_callLoop {id : Fin P.n} {b : Bool}
  (h : NetworkStep P r w (.callLoop r id b) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_firstGatherReturn {id : Fin P.n} {g : Fin P.n → Option Bool}
    {C : Gather.AcceptedPairs P.n Bool}
    (h : NetworkStep P r w (.firstGatherReturn id g C) μ) :
    μ = PMF.pure (some (w.getD (boundOfCore P C))) := by cases h; rfl

theorem networkStep_secondGatherCall {id : Fin P.n} {x : Option Bool} (h : NetworkStep P r w
  (.secondGatherCall id x) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_secondGatherReturn {id : Fin P.n} {g : Fin P.n → Option (Option Bool)}
    {C : Gather.AcceptedPairs P.n (Option Bool)} (h : NetworkStep P r w (.secondGatherReturn id g C)
      μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_retG {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : NetworkStep P r w (.retG r id out bnd) μ) :
    bnd = w.getD (boundOfCore P ∅) ∧ μ = PMF.pure w := by cases h; exact ⟨rfl, rfl⟩

end NetInversion

end GBCA.ByAFW
end ABA
end PLTS
