/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY.Substitution
import Leslie2Protocols.ABA.Composition.RoundFamilyOwnedLabels
import Leslie2.Results

/-!
# The protocol-shaped specification

`hybrid` is the specification of the ABA protocol read at the protocol's own shape. Four
components run in parallel over `Composition.ExtendedLabel n`: the ℕ-indexed family of round
specifications `gbcaSpecificationFamily`, the `n` round loops, the ABA network and the lifted
coin oracle. The rendezvous alphabet is hidden, the result is read back over `Label n`, and the
sub-protocol API is hidden. The last three components and the alphabet are
`ABA/Composition/Components.lean`.

The round-`r` member of `gbcaSpecificationFamily` is that round's graded-agreement specification
read over the protocol extended alphabet along `GBCA.ByABDY.gbcaLabelMap`
(`Composition/GBCAInstanceByABDY/SpecificationOverRoundAlphabet.lean`). A round-tagged label —
including a Byzantine handshake row of that round — moves its round alone, `τ` moves one round,
`fail` is the broadcast that keeps every round's copy of the corrupted set together, and every
other label idles.

## What this file supplies

`hybrid` and its rows. The builders assemble a transition of the composite out of transitions of
its components (`gbcaSpecificationFamily_owned`, `gbcaSpecificationFamily_idle`,
`gbcaSpecificationFamily_tau`, `gbcaSpecificationFamily_fail`, `hybridExtended_visible_step`,
`hybridExtended_tau_specification`, `hybrid_rendezvous`, `hybrid_hidden`, `hybrid_visible`). The
coin oracle's own rows over the round alphabet are `wccFamily_owned` and `wccFamily_fail`. The
account also runs in the inverse direction, from a composite transition back into the rows its
four components contributed. A labelled transition reaches `hybrid` along one of three routes
through the two hiding frames: a rendezvous label and a sub-protocol API label are both hidden to
`τ`, and every remaining label survives both hidings.

`hybrid` is where the two chains of `ABA/Results.lean` meet.
`ABA/Implementation/ABDY/CompositionChain.lean` carries the composed system of ABDY22's protocol
to it in one stage, and `ABA/Implementation/AFW/CompositionChain.lean` the gather-based
implementation in three. The simulation of `ABA/HybridRefinesSpecification/Simulation.lean` runs
from `hybrid` on this vocabulary, the non-vacuity witnesses of
`ABA/HybridRefinesSpecification/NonVacuity.lean` are built with it, and `ABA/Results.lean` reads
off the protocols' Validity and Agreement guarantee through `safety_transfer`.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-! ## The protocol-shaped specification family

`gbcaSpecificationFamily` is the graded-agreement component: the family of round specifications,
read over the protocol alphabet. It stands where the composed system of
`ABA/Implementation/ABDY/CompositionChain.lean` carries the family of round instances, and the
other three components are the same in both systems. -/

/-- **The specification family of the protocol**: the ℕ-indexed family of round specifications, read
over the protocol extended alphabet along `GBCA.ByABDY.gbcaLabelMap`. A round-tagged label —
including a Byzantine handshake row of that round — moves its round alone, `τ` moves one round, and
`fail` is the broadcast that keeps every round's copy of the corrupted set together. -/
noncomputable def gbcaSpecificationFamily (P : Parameters) :
    System (ℕ → GBCA.SpecState P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByABDY.specificationOverRoundAlphabet P) GBCA.ByABDY.roundOwnsLabel
    GBCA.ByABDY.isFailLabel
    (GBCA.ByABDY.specificationCorruptionAct P)

@[simp] theorem gbcaSpecificationFamily_init (P : Parameters) :
    (gbcaSpecificationFamily P).init = fun _ => GBCA.SpecState.initial P.n := rfl

/-- The specification family is an LTS: every round's specification is. -/
theorem gbcaSpecificationFamily_isLTS (P : Parameters) : (gbcaSpecificationFamily P).IsLTS :=
  System.family_isLTS (GBCA.ByABDY.specificationOverRoundAlphabet_isLTS P) _ _ _

/-- The state of the protocol-shaped specification: the round
specifications beside the round loops, the ABA network and the coin oracle. -/
abbrev HybridState (P : Parameters) : Type :=
  (ℕ → GBCA.SpecState P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- The four components in parallel, over the extended alphabet: the context term of
`ABDY.composedExtended` (`ABA/Implementation/ABDY/CompositionChain.lean`) over the
specification family. -/
noncomputable def hybridExtended (P : Parameters) : System (HybridState P) (ExtendedLabel P.n) :=
  (gbcaSpecificationFamily P).parallel
    ((System.synchronisedProduct (roundLoopProgram P)).parallel ((ABANetwork P).parallel
      (coinOverRoundAlphabet P)))

/-- **The protocol-shaped specification**: the rendezvous alphabet hidden,
the result read back over `Label n`, the sub-protocol API hidden. The pipeline is that of
`ABDY.composed` (`ABA/Implementation/ABDY/CompositionChain.lean`), component for component. -/
noncomputable def hybrid (P : Parameters) : System (HybridState P) (Label P.n) :=
  (((hybridExtended P).abstract (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-! ### The specification family's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else — `GBCA.ByABDY.gbcaInstanceFamily`'s rows with
the round instance replaced by its specification. -/

/-- The specification family idles on a label no round owns and no broadcast. -/
theorem gbcaSpecificationFamily_idle (P : Parameters) (G : ℕ → GBCA.SpecState P.n)
    {L : ExtendedLabel P.n} (hτ : L ≠ Silent.τ) (hown : GBCA.ByABDY.roundOwnsLabel L = none)
    (hf : ¬ GBCA.ByABDY.isFailLabel L) : (gbcaSpecificationFamily P).step G L (PMF.pure G) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round specification. -/
theorem gbcaSpecificationFamily_fail (P : Parameters) (G : ℕ → GBCA.SpecState P.n) (k : Fin P.n) :
    (gbcaSpecificationFamily P).step G (Sum.inl (Label.fail k))
    (PMF.pure fun r => (G r).corrupt P k) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- An owned label is answered by its round alone. -/
theorem gbcaSpecificationFamily_owned_inversion (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {L : ExtendedLabel P.n} {r : ℕ} (hL : GBCA.ByABDY.roundOwnsLabel L = some r) (hτ : L ≠ Silent.τ)
    {μ : PMF (ℕ → GBCA.SpecState P.n)} (h : (gbcaSpecificationFamily P).step G L μ) :
    ∃ X, (GBCA.ByABDY.specificationOverRoundAlphabet P r).step (G r) L (PMF.pure X) ∧
      μ = PMF.pure (Function.update G r X) := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r', hown, μr, hstep, rfl⟩ | ⟨-, hown, -, -⟩ | ⟨-, hown, -, -⟩
  · exact absurd habs hτ
  · obtain rfl : r' = r := by rw [hL] at hown; exact (Option.some.inj hown).symm
    obtain ⟨X, rfl⟩ := GBCA.ByABDY.specificationOverRoundAlphabet_isLTS P r' _ _ _ hstep
    exact ⟨X, hstep, by rw [PMF.pure_map]⟩
  · rw [hL] at hown; exact absurd hown (by simp)
  · rw [hL] at hown; exact absurd hown (by simp)

/-- A round's own row, read into the specification: the label the round owns is answered by that
round, every other round unchanged. -/
theorem gbcaSpecificationFamily_owned (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {L : ExtendedLabel P.n} {l₀ : Label P.n} {r : ℕ} {X : GBCA.SpecState P.n}
    (hown : GBCA.ByABDY.roundOwnsLabel L = some r)
    (hpull : GBCA.ByABDY.gbcaLabelMap P.n L = some l₀) (h : GBCA.Step P r (G r) l₀ (PMF.pure X)) :
    (gbcaSpecificationFamily P).step G L (PMF.pure (Function.update G r X)) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  refine Or.inr (Or.inl ⟨r, hown, PMF.pure X, ?_, by rw [PMF.pure_map]⟩)
  rw [GBCA.ByABDY.specificationOverRoundAlphabet, System.mapIdle_step_some hpull]
  exact h

/-- A round's own silent rule — the specification's binding exclusion — read into the
specification. -/
theorem gbcaSpecificationFamily_tau (P : Parameters) {G : ℕ → GBCA.SpecState P.n} {r : ℕ}
    {X : GBCA.SpecState P.n} (h : GBCA.Step P r (G r) Label.tau (PMF.pure X)) :
    (gbcaSpecificationFamily P).step G (Sum.inl Label.tau) (PMF.pure (Function.update G r X)) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  refine Or.inl ⟨rfl, r, PMF.pure X, ?_, by rw [PMF.pure_map]⟩
  rw [GBCA.ByABDY.specificationOverRoundAlphabet,
    System.mapIdle_step_some (GBCA.ByABDY.gbcaLabelMap_inl (Label.tau : Label P.n))]
  exact h

/-- A label a round specification owns is answered by that round alone, read
back over the specification's own alphabet. -/
theorem gbcaSpecificationFamily_owned_step (P : Parameters) {G G' : ℕ → GBCA.SpecState P.n}
    {L : ExtendedLabel P.n} {l₀ : Label P.n} {r : ℕ}
    (hown : GBCA.ByABDY.roundOwnsLabel L = some r) (hτ : L ≠ Silent.τ)
    (hpull : GBCA.ByABDY.gbcaLabelMap P.n L = some l₀)
    (h : (gbcaSpecificationFamily P).step G L (PMF.pure G')) :
    ∃ X, GBCA.Step P r (G r) l₀ (PMF.pure X) ∧ G' = Function.update G r X := by
  obtain ⟨X, hstep, heq⟩ := gbcaSpecificationFamily_owned_inversion P hown hτ h
  rw [GBCA.ByABDY.specificationOverRoundAlphabet, System.mapIdle_step_some hpull] at hstep
  exact ⟨X, hstep, pure_inj heq⟩

/-- Only the identity successor answers a label no round owns and no
broadcast. -/
theorem gbcaSpecificationFamily_idle_inversion (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {L : ExtendedLabel P.n} {μ : PMF (ℕ → GBCA.SpecState P.n)}
    (h : (gbcaSpecificationFamily P).step G L μ) (hτ : L ≠ Silent.τ)
    (hown : GBCA.ByABDY.roundOwnsLabel L = none) (hf : ¬ GBCA.ByABDY.isFailLabel L) :
    μ = PMF.pure G := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hτ
  · rw [hown] at hr; exact absurd hr (by simp)
  · exact absurd hglob hf
  · rfl

/-- Corruption is broadcast to every round. -/
theorem gbcaSpecificationFamily_fail_inversion (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    (k : Fin P.n) {μ : PMF (ℕ → GBCA.SpecState P.n)}
    (h : (gbcaSpecificationFamily P).step G (Sum.inl (Label.fail k)) μ) :
    μ = PMF.pure (fun r => (G r).corrupt P k) := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd habs (by simp)
  · exact absurd hr (by simp)
  · rfl
  · exact absurd trivial hglob

/-- A silent transition of the family is one round's own silent rule — the
specification's binding exclusion. -/
theorem gbcaSpecificationFamily_tau_inversion (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {μ : PMF (ℕ → GBCA.SpecState P.n)}
    (h : (gbcaSpecificationFamily P).step G (Sum.inl Label.tau) μ) :
    ∃ (r : ℕ) (X : GBCA.SpecState P.n),
      (GBCA.ByABDY.specificationOverRoundAlphabet P r).step (G r) (Sum.inl Label.tau) (PMF.pure X) ∧
      μ = PMF.pure (Function.update G r X) := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨-, r, μr, hstep, rfl⟩ | ⟨r, hr, -⟩ | ⟨habs, -, -, -⟩ | ⟨habs, -, -, -⟩
  · obtain ⟨X, rfl⟩ := GBCA.ByABDY.specificationOverRoundAlphabet_isLTS P r _ _ _ hstep
    exact ⟨r, X, hstep, by rw [PMF.pure_map]⟩
  · exact absurd hr (by simp)
  · exact absurd rfl habs
  · exact absurd rfl habs

/-! ### The coin oracle's rows

The oracle is a family over the same shape: a round-tagged label moves its
round, `fail` is broadcast, and everything else leaves it put. -/

/-- The coin oracle's family idles on a label outside its own API. -/
theorem wccFamily_idle_inversion (P : Parameters) {o : ℕ → WCC.SpecState P.n} {l : Label P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (hl : l ≠ Label.tau) (hr : Label.wccRound l = none)
    (hf : ¬ Label.isFail l) (h : (WCC.specFamily P).step o l ω) : ω = PMF.pure o := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd hτ hl
  · rw [hr] at hr'; exact absurd hr' (by simp)
  · exact absurd hglob hf
  · rfl

/-- A label the coin oracle's family owns is answered by its round alone. -/
theorem wccFamily_owned_inversion (P : Parameters) {o : ℕ → WCC.SpecState P.n} {l : Label P.n}
    {r : ℕ} {ω : PMF (ℕ → WCC.SpecState P.n)} (hl : l ≠ Label.tau)
    (hr : Label.wccRound l = some r) (h : (WCC.specFamily P).step o l ω) :
    ∃ μw', WCC.Step P r (o r) l μw' ∧ ω = μw'.map (Function.update o r) := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r', hr', μw', hstep, rfl⟩ | ⟨-, hr'', -, -⟩ | ⟨-, hr'', -, -⟩
  · exact absurd hτ hl
  · obtain rfl : r' = r := by rw [hr] at hr'; exact (Option.some.inj hr').symm
    exact ⟨μw', hstep, rfl⟩
  · rw [hr] at hr''; exact absurd hr'' (by simp)
  · rw [hr] at hr''; exact absurd hr'' (by simp)

/-- A round of the coin oracle answers the label it owns, every other round
unchanged. -/
theorem wccFamily_owned (P : Parameters) (o : ℕ → WCC.SpecState P.n) {l : Label P.n}
    {r : ℕ} {x : WCC.SpecState P.n} (hr : Label.wccRound l = some r)
    (h : WCC.Step P r (o r) l (PMF.pure x)) :
    (WCC.specFamily P).step o l (PMF.pure (Function.update o r x)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hr, PMF.pure x, h, by rw [PMF.pure_map]⟩)

/-- Corruption is broadcast to every round of the coin oracle's family. -/
theorem wccFamily_fail (P : Parameters) (o : ℕ → WCC.SpecState P.n) (k : Fin P.n) :
    (WCC.specFamily P).step o (.fail k) (PMF.pure fun r => (o r).corrupt P k) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- A corruption broadcast is answered by every round of the coin oracle's
family. -/
theorem wccFamily_fail_inversion (P : Parameters) {o : ℕ → WCC.SpecState P.n} (k : Fin P.n)
    {ω : PMF (ℕ → WCC.SpecState P.n)} (h : (WCC.specFamily P).step o (.fail k) ω) :
    ω = PMF.pure fun r => (o r).corrupt P k := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd hτ (by simp)
  · exact absurd hr (by simp [Label.wccRound])
  · rfl
  · exact absurd trivial hglob

/-! ### Reading a protocol-shaped transition into its four components -/

/-- Build a joint transition of the four components on a visible label, the
oracle's successor left arbitrary. -/
theorem hybridExtended_visible_step (P : Parameters) {G G' : ℕ → GBCA.SpecState P.n}
    {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : ExtendedLabel P.n}
    (hL : L ≠ Silent.τ)
    (hG : (gbcaSpecificationFamily P).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o L ω) :
    (hybridExtended P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [hybridExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, roundLoopProduct_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- A visible transition of the four components: all of them move together, and
only the oracle's successor can fail to be a Dirac. -/
theorem hybridExtended_visible_inversion (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {L : ExtendedLabel P.n} (hL : L ≠ Silent.τ)
    {μ : PMF (HybridState P)} (h : (hybridExtended P).step (G, C, A, o) L μ) :
    ∃ (G' : ℕ → GBCA.SpecState P.n) (C' : ∀ _ : Fin P.n, RoundLoopRecord P.n)
      (A' : ABANetworkState P.n) (ω : PMF (ℕ → WCC.SpecState P.n)),
      (gbcaSpecificationFamily P).step G L (PMF.pure G') ∧
      (∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i))) ∧
      ABANetworkStep P A L (PMF.pure A') ∧ (coinOverRoundAlphabet P).step o L ω ∧
      μ = prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω)) := by
  rw [hybridExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hG, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨G', rfl⟩ := gbcaSpecificationFamily_isLTS P _ _ _ hG
    rw [System.parallel_step] at hrest
    rcases hrest with ⟨-, μ₂, μ₃, hC, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨C', rfl, hall⟩ := roundLoopProduct_inversion hC
      rw [System.parallel_step] at hrest
      rcases hrest with ⟨-, μ₃, ω, hA, hW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
      · obtain ⟨A', rfl⟩ := abaNetworkStep_dirac hA
        exact ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩
      · exact absurd habs hL
      · exact absurd habs hL
    · exact absurd habs hL
    · exact absurd habs hL
  · exact absurd habs hL
  · exact absurd habs hL

/-- Build a silent transition of the four components from a specification one. -/
theorem hybridExtended_tau_specification (P : Parameters) {G G' : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (gbcaSpecificationFamily P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (hybridExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [hybridExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- A silent transition of the four components: no round loop has a `τ` row, and neither has the
coin oracle, so it is the specification family's binding exclusion or the ABA network's own
injection. -/
theorem hybridExtended_tau_inversion (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (HybridState P)} (h : (hybridExtended P).step (G, C, A, o) (Sum.inl Label.tau) μ) :
    (∃ G', (gbcaSpecificationFamily P).step G (Sum.inl Label.tau) (PMF.pure G') ∧
        μ = PMF.pure (G', C, A, o)) ∨
    (∃ A', ABANetworkStep P A (Sum.inl Label.tau) (PMF.pure A') ∧ μ = PMF.pure (G, C, A', o)) := by
  rw [hybridExtended, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hG, rfl⟩ | ⟨-, μ₂, hrest, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨G', rfl⟩ := gbcaSpecificationFamily_isLTS P _ _ _ hG
    exact Or.inl ⟨G', hG, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hrest
    rcases hrest with ⟨habs, -⟩ | ⟨-, μ₂, hC, rfl⟩ | ⟨-, μ₃, hrest, rfl⟩
    · exact absurd rfl habs
    · exact (roundLoopProduct_no_tau hC).elim
    · rw [System.parallel_step] at hrest
      rcases hrest with ⟨habs, -⟩ | ⟨-, μ₃, hA, rfl⟩ | ⟨-, ω, hW, rfl⟩
      · exact absurd rfl habs
      · obtain ⟨A', rfl⟩ := abaNetworkStep_dirac hA
        exact Or.inr ⟨A', hA,
          by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]⟩
      · exact (WCC.specFamily_tau_inversion P
          ((System.mapIdle_step_some (coinLabelMap_inl Label.tau) ω).mp hW)).elim

/-! ### The two hiding frames -/

/-- **The protocol-shaped group**: the rendezvous alphabet hidden, the result
read back over `Label n`. Scaffolding for the row-by-row account below; nothing
outside this file names it. -/
private noncomputable def hybridHidden (P : Parameters) : System (HybridState P) (Label P.n) :=
  ((hybridExtended P).abstract (networkEventLabels P.n)).relabel

/-- The group's step relation, unfolded to the hidden rendezvous case and the
shared-label case. -/
theorem hybridHidden_step_iff (P : Parameters) (q : HybridState P) (l : Label P.n)
    (μ : PMF (HybridState P)) :
    (hybridHidden P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n, (hybridExtended P).step q (Sum.inr e) μ) ∨
      (hybridExtended P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

/-- The protocol-shaped specification's step relation: a sub-protocol API
label seen as `τ`, or a label that survives the hiding. -/
theorem hybrid_step_iff (P : Parameters) (q : HybridState P) (l : Label P.n)
    (μ : PMF (HybridState P)) :
    (hybrid P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n, (hybridHidden P).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧ (hybridHidden P).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-! ### Building a transition through the two hiding frames

A transition of the four components reaches the protocol-shaped specification
along one of three routes, according to its label: a rendezvous label and a
sub-protocol API label are both hidden to `τ`, and every remaining label
survives both hidings. -/

/-- A rendezvous transition is silent: the rendezvous alphabet is hidden. -/
theorem hybrid_rendezvous (P : Parameters) {q : HybridState P} {e : NetworkEvent P.n}
    {μ : PMF (HybridState P)} (h : (hybridExtended P).step q (Sum.inr e) μ) :
    (hybrid P).step q Label.tau μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨by simp, (hybridHidden_step_iff P q Label.tau μ).mpr (Or.inl ⟨rfl, e, h⟩)⟩

/-- A sub-protocol API label is silent: the API is hidden. -/
theorem hybrid_hidden (P : Parameters) {q : HybridState P} {l : Label P.n}
    {μ : PMF (HybridState P)} (hl : l ∈ Label.hiddenAPI P.n)
    (h : (hybridExtended P).step q (Sum.inl l) μ) :
    (hybrid P).step q Label.tau μ := by
  rw [hybrid_step_iff]
  exact Or.inl ⟨rfl, l, hl, (hybridHidden_step_iff P q l μ).mpr (Or.inr h)⟩

/-- A label outside the sub-protocol API survives both hidings. -/
theorem hybrid_visible (P : Parameters) {q : HybridState P} {l : Label P.n}
    {μ : PMF (HybridState P)} (hl : l ∉ Label.hiddenAPI P.n)
    (h : (hybridExtended P).step q (Sum.inl l) μ) :
    (hybrid P).step q l μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨hl, (hybridHidden_step_iff P q l μ).mpr (Or.inr h)⟩

end ABA

end PLTS
