/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndRemovals

/-!
# The transitions of the implementation, determined by their labels

The implementation is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct` over the
process group, the network and the lifted coin. The lemmas here unfold that pipeline once.
`programProduct_cases` reads a synchronised transition of the process group on a visible label:
every process steps, and the product distribution is their Dirac product. `programProduct_tau_cases`
reads the silent one, where one process moves and the others remain unchanged.
`systemHidden_step_iff` and `system_step_iff` split a composite transition into a hidden event and a
label that the hiding leaves visible. `systemExtended_event_cases`, `systemExtended_label_cases` and
`systemExtended_tau_cases` decompose a synchronised step of the three components into the
transitions of the group, of the network and of the coin.

The announcement of a round's bound bit is the one transition whose guard reads the ghost, and
`systemExtended_announceBound` and `systemExtended_boundG_cases` state the composite transition on
it: the network announces the bit the round's ghost holds, every program idles and the common coin
idles. `systemExtended_byzantineCallG` and `systemExtended_byzantineCallW` state the composite
transitions on a corrupted process's two sub-protocol calls, which the network outputs under
`k ∈ F` at a round of `startedRounds`.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### Reading composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct`; the
lemmas below unfold it once and for all. -/

section Composite

variable {P : Parameters} {M E S : Type}
    {roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop}
    [IsRoundStep P M E S roundStep]

/-- A synchronised transition of the process group on a visible label: every
process steps, and the product distribution is Dirac. -/
theorem programProduct_cases {u : ∀ _ : Fin P.n, ProcessVariables P.n S}
    {l : ExtendedLabel P.n M E}
    {μ : PMF (∀ _ : Fin P.n, ProcessVariables P.n S)} (hl : l ≠ Silent.τ)
    (h : (System.synchronisedProduct (program P M E S roundStep)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, ProcessVariables P.n S,
      μ = PMF.pure x ∧ ∀ i, ProgramStep P M E S roundStep i (u i) l (PMF.pure (x i)) := by
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
theorem programProduct_tau_cases {u : ∀ _ : Fin P.n, ProcessVariables P.n S}
    {μ : PMF (∀ _ : Fin P.n, ProcessVariables P.n S)}
    (h : (System.synchronisedProduct (program P M E S roundStep)).step u
      (Silent.τ : ExtendedLabel P.n M E) μ) :
    ∃ (i : Fin P.n) (y : ProcessVariables P.n S),
      ProgramStep P M E S roundStep i (u i) (Silent.τ : ExtendedLabel P.n M E) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y) := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, rfl⟩
  · exact absurd rfl hτ
  · obtain ⟨y, rfl⟩ := programStep_dirac hstep
    exact ⟨i, y, hstep, by rw [piPMF_update_pure, PMF.pure_map]⟩

/-! ### The transitions of the implementation, determined by their labels -/

section SystemStepCases
variable {G : Type} [DecidableEq M] [Inhabited G]
    {ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G}
    {ghostBound : G → Option Bool}

omit [IsRoundStep P M E S roundStep] in
/-- The composite step relation of the group, unfolded to the hidden-synchronisation
case and the shared-label case. -/
theorem systemHidden_step_iff (q : State P M S G) (l : Label P.n)
    (μ : PMF (State P M S G)) :
    (systemHidden P M E S G roundStep ghostStep ghostBound).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n M E,
        (systemExtended P M E S G roundStep ghostStep ghostBound).step q
          (Sum.inr e) μ) ∨
      (systemExtended P M E S G roundStep ghostStep ghostBound).step q
        (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

omit [IsRoundStep P M E S roundStep] in
/-- The implementation's step relation: a sub-protocol API label seen as `τ`, or
a label that the hiding leaves visible. -/
theorem system_step_iff (q : State P M S G) (l : Label P.n)
    (μ : PMF (State P M S G)) :
    (system P M E S G roundStep ghostStep ghostBound).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n,
        (systemHidden P M E S G roundStep ghostStep ghostBound).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧
        (systemHidden P M E S G roundStep ghostStep ghostBound).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-- A synchronised transition: every process, the network and the lifted coin
move together, and only the coin's successor can fail to be a Dirac. -/
theorem systemExtended_event_cases {u : ∀ _ : Fin P.n, ProcessVariables P.n S}
    {w : NetworkState P.n M G}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {e : NetworkEvent P.n M E}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessVariables P.n S) (w' : NetworkState P.n M G)
      (μ₃ : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))),
      (∀ i, ProgramStep P M E S roundStep i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetworkStep P M E G ghostStep ghostBound w (Sum.inr e) (PMF.pure w') ∧
      (coinOverExtendedAlphabet P M E).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := programProduct_cases (by simp) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN, hO, rfl⟩
    · simp [extendedLabel_tau] at habs
    · simp [extendedLabel_tau] at habs
  · simp [extendedLabel_tau] at habs
  · simp [extendedLabel_tau] at habs

/-- A visible shared-label transition. -/
theorem systemExtended_label_cases {u : ∀ _ : Fin P.n, ProcessVariables P.n S}
    {w : NetworkState P.n M G}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {l : Label P.n}
    (hl : l ≠ Label.tau) {μ : PMF (State P M S G)}
    (h : (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessVariables P.n S) (w' : NetworkState P.n M G)
      (ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))),
      (∀ i, ProgramStep P M E S roundStep i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetworkStep P M E G ghostStep ghostBound w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ :=
      programProduct_cases
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

/-- A silent shared-label transition: one process terminating, the network's own
injection, or the resolution of one round of the common coin's map. -/
theorem systemExtended_tau_cases {u : ∀ _ : Fin P.n, ProcessVariables P.n S}
    {w : NetworkState P.n M G}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inl Label.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcessVariables P.n S),
      ProgramStep P M E S roundStep i (u i) (Sum.inl Label.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetworkStep P M E G ghostStep ghostBound w (Sum.inl .tau)
        (PMF.pure w') ∧
      μ = PMF.pure (u, w', o)) ∨
    (∃ r ∈ o.instanceMap.keys, ∃ μw : PMF (WCC.SpecState P.n), WCC.Step P r (o r) Label.tau μw ∧
      μ = prodPMF (PMF.pure u) (prodPMF (PMF.pure w) (μw.map (o.setInstanceState r)))) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hS, rfl⟩ | ⟨-, μ₂₃, hNW, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨i, y, hstep, rfl⟩ := programProduct_tau_cases hS
    exact Or.inl ⟨i, y, hstep, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hNW
    rcases hNW with ⟨habs, -⟩ | ⟨-, μ₂, hN, rfl⟩ | ⟨-, μ₃, hO, rfl⟩
    · exact absurd rfl habs
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact Or.inr (Or.inl ⟨w', hN, by rw [prodPMF_pure_pure, prodPMF_pure_pure]⟩)
    · obtain ⟨r, hr, μw, hstep, rfl⟩ := ABA.WCC.specFamily_tau_cases P
        ((System.mapIdle_step_some (coinLabelMap_inl Label.tau) μ₃).mp hO)
      exact Or.inr (Or.inr ⟨r, hr, μw, hstep, rfl⟩)

/-! ### The announcement and a corrupted process's calls

The network outputs the announcement of a round's bound bit and a corrupted process's two
sub-protocol calls. Every program idles on the three. The common coin idles on the announcement,
which names no coin round, and on the graded-agreement call, which `coinLabelMap` sends to no
label; it takes the coin call on its own call transition. -/

omit [DecidableEq M] in
/-- The common coin idles on the announcement of a graded-agreement round's bound bit. -/
theorem coinOverExtendedAlphabet_boundG
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) (r : ℕ) (b : Bool) :
    (coinOverExtendedAlphabet P M E).step o (Sum.inl (.boundG r b)) (PMF.pure o) :=
  (System.mapIdle_step_some (coinLabelMap_inl _) _).mpr
    (wccFamily_idle P o (by simp) rfl (by simp [Label.isFail]))

omit [IsRoundStep P M E S roundStep] in
/-- **The composite announcement** (D29): the network announces the bit the round's ghost holds,
every program idles, and the common coin idles. -/
theorem systemExtended_announceBound (u : ∀ _ : Fin P.n, ProcessVariables P.n S)
    (w : NetworkState P.n M G)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {r : ℕ} {b : Bool}
    (h : ghostBound (w.ghost r) = some b) :
    (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inl (.boundG r b))
      (PMF.pure (u, w.writeGhost ghostStep (Sum.inl (.boundG r b)), o)) := by
  have hne : (Sum.inl (.boundG r b) : ExtendedLabel P.n M E) ≠ Silent.τ := by
    rw [extendedLabel_tau]; simp
  rw [systemExtended, System.parallel_step]
  refine Or.inl ⟨hne, PMF.pure u, PMF.pure (w.writeGhost ghostStep (Sum.inl (.boundG r b)), o),
    ?_, ?_, (prodPMF_pure_pure _ _).symm⟩
  · rw [System.synchronisedProduct_step]
    exact Or.inl ⟨hne, fun i => PMF.pure (u i),
      fun i => ProgramStep.boundGIdle (u i).1 (u i).2 r b, (piPMF_pure u).symm⟩
  · rw [System.parallel_step]
    exact Or.inl ⟨hne, _, _, NetworkStep.announceBound w r b h,
      coinOverExtendedAlphabet_boundG o r b, (prodPMF_pure_pure _ _).symm⟩

/-- A composite transition on the announcement of a round's bound bit is the composite
announcement: the round's ghost holds the bit, and only the network's ghost write moves. -/
theorem systemExtended_boundG_cases {u : ∀ _ : Fin P.n, ProcessVariables P.n S}
    {w : NetworkState P.n M G}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {r : ℕ} {b : Bool}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inl (.boundG r b)) μ) :
    ghostBound (w.ghost r) = some b ∧
      μ = PMF.pure (u, w.writeGhost ghostStep (Sum.inl (.boundG r b)), o) := by
  obtain ⟨x, w', ω, hall, hN, hO, rfl⟩ := systemExtended_label_cases (by simp) h
  obtain ⟨hb, hw'⟩ := networkStep_announceBound hN
  have hx : x = u := funext fun i => pure_inj (programStep_boundG (hall i))
  have hω : ω = PMF.pure o := by
    rw [WCC.specFamily, System.family_step_iff] at hO
    rcases hO with ⟨hτ, -⟩ | ⟨r', hown, -⟩ | ⟨-, -, hg, -⟩ | ⟨-, -, -, rfl⟩
    · exact absurd hτ (by simp)
    · exact absurd hown (by simp)
    · exact absurd hg (by simp [Label.isFail])
    · rfl
  subst hx hω
  rw [pure_inj hw', prodPMF_pure_pure, prodPMF_pure_pure]
  exact ⟨hb, rfl⟩

omit [IsRoundStep P M E S roundStep] in
/-- **The composite graded-agreement call of a corrupted process** (D11, D37): the network
outputs it under `k ∈ F` at a started round, every program idles, and the common coin idles. The
round instance that takes it lies in the composed systems, beside the round loops. -/
theorem systemExtended_byzantineCallG (u : ∀ _ : Fin P.n, ProcessVariables P.n S)
    (w : NetworkState P.n M G)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {r : ℕ} {k : Fin P.n}
    {b : Bool} (hF : k ∈ w.F) (hr : r ∈ w.startedRounds) :
    (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inr (.byzantineCallG r k b))
      (PMF.pure (u, w.writeGhost ghostStep (Sum.inr (.byzantineCallG r k b)), o)) := by
  have hne : (Sum.inr (.byzantineCallG r k b) : ExtendedLabel P.n M E) ≠ Silent.τ := by
    rw [extendedLabel_tau]; simp
  rw [systemExtended, System.parallel_step]
  refine Or.inl ⟨hne, PMF.pure u,
    PMF.pure (w.writeGhost ghostStep (Sum.inr (.byzantineCallG r k b)), o),
    ?_, ?_, (prodPMF_pure_pure _ _).symm⟩
  · rw [System.synchronisedProduct_step]
    exact Or.inl ⟨hne, fun i => PMF.pure (u i),
      fun i => ProgramStep.byzantineCallGIdle (u i).1 (u i).2 r k b, (piPMF_pure u).symm⟩
  · rw [System.parallel_step]
    exact Or.inl ⟨hne, _, _, NetworkStep.byzantineCallG w r k b hF hr,
      (System.mapIdle_step_none (coinLabelMap_byzantineCallG r k b) _).mpr rfl,
      (prodPMF_pure_pure _ _).symm⟩

omit [IsRoundStep P M E S roundStep] in
/-- **The composite coin call of a corrupted process** (D11, D37): the network outputs it under
`k ∈ F` at a started round, every program idles, and the common coin takes it as the call of
`k` at round `r`. -/
theorem systemExtended_byzantineCallW (u : ∀ _ : Fin P.n, ProcessVariables P.n S)
    (w : NetworkState P.n M G)
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {r : ℕ} {k : Fin P.n}
    (hF : k ∈ w.F) (hr : r ∈ w.startedRounds)
    {ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    (hO : (WCC.specFamily P).step o (.callW r k) ω) :
    (systemExtended P M E S G roundStep ghostStep ghostBound).step (u, w, o)
      (Sum.inr (.byzantineCallW r k))
      (prodPMF (PMF.pure u)
        (prodPMF (PMF.pure (w.writeGhost ghostStep (Sum.inr (.byzantineCallW r k)))) ω)) := by
  have hne : (Sum.inr (.byzantineCallW r k) : ExtendedLabel P.n M E) ≠ Silent.τ := by
    rw [extendedLabel_tau]; simp
  rw [systemExtended, System.parallel_step]
  refine Or.inl ⟨hne, PMF.pure u, _, ?_, ?_, rfl⟩
  · rw [System.synchronisedProduct_step]
    exact Or.inl ⟨hne, fun i => PMF.pure (u i),
      fun i => ProgramStep.byzantineCallWIdle (u i).1 (u i).2 r k, (piPMF_pure u).symm⟩
  · rw [System.parallel_step]
    exact Or.inl ⟨hne, _, _, NetworkStep.byzantineCallW w r k hF hr,
      (System.mapIdle_step_some (coinLabelMap_byzantineCallW r k) _).mpr hO, rfl⟩

end SystemStepCases
end Composite

end Implementation
end ABA
end PLTS
