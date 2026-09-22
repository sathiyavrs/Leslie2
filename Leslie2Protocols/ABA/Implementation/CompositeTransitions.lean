/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndErasures

/-!
# The transitions of the implementation, read off their labels

The implementation is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct` over the
process group, the network and the lifted oracle. The lemmas here unfold that pipeline once and
for all. `programProduct_inversion` reads a synchronised transition of the process group on a
visible label: every process steps, and the joint distribution is their Dirac product.
`programProduct_tau_inversion` reads the silent one, where one process moves and the others stand.
`systemHidden_step_iff` and `system_step_iff` split a composite transition into a hidden event and
a label that survives the hiding. `systemExtended_event_inversion`,
`systemExtended_label_inversion` and `systemExtended_tau_inversion` read a joint step of the three
components backwards, to the rows of the group, of the network and of the oracle.

The two graded-agreement returns are the only rows that read the ghost, and what they read is the
relation `ghostOutput` at the network's state. `systemExtended_retG_bound` and
`systemExtended_byzantineRetG_bound` state what a composite transition on either therefore
requires of the bound bit its label carries.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### Reading composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct`; the
lemmas below unfold it once and for all. -/

section Composite

variable {P : Parameters} {M S : Type}
    {roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop}
    [IsRoundRuleTable P M S roundStep]

/-- A synchronised transition of the process group on a visible label: every
process steps, and the joint distribution is Dirac. -/
theorem programProduct_inversion {u : ∀ _ : Fin P.n, ProcessRecord P.n S} {l : ExtendedLabel P.n M}
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n S)} (hl : l ≠ Silent.τ)
    (h : (System.synchronisedProduct (program P M S roundStep)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, ProcessRecord P.n S,
      μ = PMF.pure x ∧ ∀ i, ProgramStep P M S roundStep i (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => programStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd rfl hl

/-- A silent transition of the process group: `τ` is interleaved, so exactly
one program moves and the rest hold their state. -/
theorem programProduct_tau_inversion {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n S)}
    (h : (System.synchronisedProduct (program P M S roundStep)).step u
      (Silent.τ : ExtendedLabel P.n M) μ) :
    ∃ (i : Fin P.n) (y : ProcessRecord P.n S),
      ProgramStep P M S roundStep i (u i) (Silent.τ : ExtendedLabel P.n M) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y) := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, rfl⟩
  · exact absurd rfl hτ
  · obtain ⟨y, rfl⟩ := programStep_dirac hstep
    exact ⟨i, y, hstep, by rw [piPMF_update_pure, PMF.pure_map]⟩

section WithNet

variable {G : Type} [DecidableEq M] [Inhabited G]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G}
    {ghostOutput : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop}

omit [IsRoundRuleTable P M S roundStep] in
/-- The composite step relation of the group, unfolded to the hidden
rendezvous case and the shared-label case. -/
theorem systemHidden_step_iff (q : State P M S G) (l : Label P.n)
    (μ : PMF (State P M S G)) :
    (systemHidden P M S G roundStep callPayload ghostStep ghostOutput).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n M,
        (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step q (Sum.inr e) μ) ∨
      (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step q
        (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

omit [IsRoundRuleTable P M S roundStep] in
/-- The implementation's step relation: a sub-protocol API label seen as `τ`, or
a label that survives the hiding. -/
theorem system_step_iff (q : State P M S G) (l : Label P.n)
    (μ : PMF (State P M S G)) :
    (system P M S G roundStep callPayload ghostStep ghostOutput).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n,
        (systemHidden P M S G roundStep callPayload ghostStep ghostOutput).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧
        (systemHidden P M S G roundStep callPayload ghostStep ghostOutput).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem systemExtended_event_inversion {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n} {e : NetworkEvent P.n M}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step (u, w, o)
      (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n S) (w' : NetworkState P.n M G)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ProgramStep P M S roundStep i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetworkStep P M G callPayload ghostStep ghostOutput w (Sum.inr e) (PMF.pure w') ∧
      (coinOverExtendedAlphabet P M).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := programProduct_inversion (by simp) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN, hO, rfl⟩
    · simp [extendedLabel_tau] at habs
    · simp [extendedLabel_tau] at habs
  · simp [extendedLabel_tau] at habs
  · simp [extendedLabel_tau] at habs

/-- A visible shared-label transition. -/
theorem systemExtended_label_inversion {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n} {l : Label P.n}
    (hl : l ≠ Label.tau) {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step (u, w, o)
      (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n S) (w' : NetworkState P.n M G)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ProgramStep P M S roundStep i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetworkStep P M G callPayload ghostStep ghostOutput w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ :=
      programProduct_inversion
        (by rw [extendedLabel_tau]; exact fun hh => hl (Sum.inl_injective hh)) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN,
        (System.mapIdle_step_some (coinLabelMap_inl l) μ₃).mp hO, rfl⟩
    · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl
    · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl

/-- A silent shared-label transition: one process terminating, or the network's
own injection. The coin oracle has no silent row, so it contributes none. -/
theorem systemExtended_tau_inversion {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step (u, w, o)
      (Sum.inl Label.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcessRecord P.n S),
      ProgramStep P M S roundStep i (u i) (Sum.inl Label.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetworkStep P M G callPayload ghostStep ghostOutput w (Sum.inl .tau)
        (PMF.pure w') ∧
      μ = PMF.pure (u, w', o)) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hS, rfl⟩ | ⟨-, μ₂₃, hNW, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨i, y, hstep, rfl⟩ := programProduct_tau_inversion hS
    exact Or.inl ⟨i, y, hstep, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hNW
    rcases hNW with ⟨habs, -⟩ | ⟨-, μ₂, hN, rfl⟩ | ⟨-, μ₃, hO, rfl⟩
    · exact absurd rfl habs
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact Or.inr ⟨w', hN, by rw [prodPMF_pure_pure, prodPMF_pure_pure]⟩
    · exact (ABA.WCC.specFamily_tau_inversion P
        ((System.mapIdle_step_some (coinLabelMap_inl Label.tau) μ₃).mp hO)).elim

/-! ### The bound bit on a return

The two graded-agreement returns are the only rows that read the ghost, and
what they read is the relation `ghostOutput` at the network's state. A composite
transition on either therefore constrains the bound bit its label carries. -/

/-- A composite graded-agreement return announces a bit the network's ghost
relation admits. -/
theorem systemExtended_retG_bound {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n}
    {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step (u, w, o)
      (Sum.inl (.retG r id out bnd)) μ) :
    ghostOutput w r id out bnd := by
  have hne : (Label.retG r id out bnd : Label P.n) ≠ Label.tau := by
    simp
  obtain ⟨x, w', ω, -, hN, -, -⟩ := systemExtended_label_inversion hne h
  exact (networkStep_retG hN).1

/-- A composite Byzantine graded-agreement return announces a bit the same
ghost relation admits (D11). -/
theorem systemExtended_byzantineRetG_bound {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n}
    {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOutput).step (u, w, o)
      (Sum.inr (.byzantineRetG r k out bnd)) μ) :
    ghostOutput w r k out bnd := by
  obtain ⟨x, w', μ₃, -, hN, -, -⟩ := systemExtended_event_inversion h
  exact (networkStep_byzantineRetG hN).2.1

end WithNet

end Composite

end Implementation
end ABA
end PLTS
