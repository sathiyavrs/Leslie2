/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# The composed chain at the protocol shape

The protocol of `ABA/Implementation/ABDY/System.lean` is `n` programs beside one network and the
coin oracle. A program reads its own replacement flag and nothing else about corruption: not the
corrupted set, not the budget, not another process's status (D23). Each program runs its round
loop and a graded-agreement round at once, and the single adversary holds both kinds of message
sent. `ABDY.composed` reads that same protocol as a composition of four components:

* the graded-agreement family is the round-indexed family `GBCA.ByABDY.gbcaInstanceFamily`. Its
  round-`r` instance is a parallel component in its own right: the graded-agreement programs of
  round `r` beside the network of round `r`, which that instance owns outright
  (`Composition/GBCAInstanceByABDY/Instance.lean`);
* the round loops are `n` separate automata (`roundLoopProgram`), synchronised;
* what is left of the network is the DECIDED sets beside the corrupted set (`ABANetwork`);
* the coin oracle enters through the same label pullback as in the protocol
  (`Composition.coinOverRoundAlphabet`).

The four components speak `Composition.ExtendedLabel n`, the rendezvous labels are hidden, and the
result is read back over `Label n`. The round loops, the ABA network and the lifted oracle are
defined in `ABA/Composition/Components.lean`. The pipeline `ABDY.composedExtended` /
`ABDY.composedHidden` / `ABDY.composed` is the first section below, and it is the context term of
`hybrid` (`ABA/Composition/Hybrid.lean`), character for character.

`ABDY.composed` is carried to `hybrid` in one stage. `familySubstitution` replaces each round's
graded-agreement instance by that round's specification, round by round, and
`ABDY.substitutionSimulation` applies the four congruences of the pipeline to it:
`ProbabilisticForwardSimulation.parallel_right` for the three untouched components, `abstract` for
the rendezvous alphabet, `relabel` for the read-back to `Label n` (`Framework/Relabel.lean`), and
`abstract` again for the sub-protocol API. `ABDY.substitution` is the inclusion of the composed
system's achievable trace distributions in the protocol-shaped specification's, and
`ABA/Results.lean` chains it with the earlier and later inclusions to state the headlines.

## Per-round memory

A round instance is a component of the composite from the start, not an object created by the
round's first call, and it keeps its round records and its network state for the whole run. The
graded-agreement coordinate of a composed state is therefore `ℕ → GBCA.ByABDY.ImplementationState
n`: every round is present at every moment, whichever round each process is in. Those retained
round records are specification state in one respect only: a process record of the protocol holds
its own round records in a finite map and, once it terminates, answers nothing further, where the
round instance answers at every moment (D22).

## The authorisation relocation (D11)

A round instance carries no `k ∈ F` guard on the handshake-row labels `byzantineCallG`,
`byzantineCallGLoop` and `byzantineRetG` (`Composition/GBCAInstanceByABDY/Instance.lean`, D11). A
handshake-row label stays visible at the instance boundary and is authorised outside it. Here
`ABANetwork` is that outside, and it carries the guard on its own copy of the corrupted set. The
two copies are written by one broadcast: `fail` reaches every round's network through the family
(`gbcaInstanceFamily_fail`) and `ABANetwork` on its own `fail` row, and
`GBCA.ByABDY.NetworkState.corrupt` and `ABANetworkState.corrupt` are the same budget-guarded
insertion.

## What this file supplies

The composed system with its rows, and the substitution that carries it to `hybrid`. The builders
assemble a transition of the composite out of transitions of its components
(`composedExtended_visible_step`, `composedExtended_tau_gbca`, `composedExtended_tau_ABANetwork`,
`gbcaInstanceFamily_owned`, `gbcaInstanceFamily_idle`, `gbcaInstanceFamily_tau`,
`gbcaInstanceFamily_fail`, `composedHidden_of_event`, `composedHidden_of_tau`). The per-component
rows these consume and produce are the tables of `ABA/Composition/Components.lean` and
`Composition/GBCAInstanceByABDY/Instance.lean`. The protocol meets the composed system in
`ABA/Implementation/ABDY/Simulation.lean`.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-! ## The composed system

The protocol cut into its components: the graded-agreement family as a round-indexed family of
instances, the round loops as `n` synchronised automata, the DECIDED sets beside the corrupted set,
and the lifted coin oracle. This section composes the four components and reads the rows of the
composite. -/

namespace Composition

/-! ### The composition pipeline -/

/-- The state of the composed system: the round instances, the round loops, the ABA network and the
coin oracle. -/
abbrev ComposedState (P : Parameters) : Type :=
  (ℕ → GBCA.ByABDY.ImplementationState P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

end Composition

namespace ABDY

/-- The four components in parallel, over the extended alphabet. -/
noncomputable def composedExtended (P : Parameters) :
    System (Composition.ComposedState P) (ExtendedLabel P.n) :=
  (GBCA.ByABDY.gbcaInstanceFamily P).parallel
    ((System.synchronisedProduct (Composition.roundLoopProgram P)).parallel
      ((Composition.ABANetwork P).parallel (coinOverRoundAlphabet P)))

/-- **The composed group**: the rendezvous alphabet hidden, the result read
back over `Label n`. -/
noncomputable def composedHidden (P : Parameters) :
    System (Composition.ComposedState P) (Label P.n) :=
  ((composedExtended P).abstract (networkEventLabels P.n)).relabel

/-- **The composed system**: the group with the sub-protocol API hidden. -/
noncomputable def composed (P : Parameters) : System (Composition.ComposedState P) (Label P.n) :=
  (composedHidden P).abstract (Label.hiddenAPI P.n)

end ABDY

namespace Composition

/-! ### Reading and building composite transitions of the composed system -/

/-- The composed group's step relation, unfolded to the hidden rendezvous case
and the shared-label case. -/
theorem composedHidden_step_iff (P : Parameters) (q : ComposedState P) (l : Label P.n)
    (μ : PMF (ComposedState P)) :
    (ABDY.composedHidden P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n, (ABDY.composedExtended P).step q (Sum.inr e) μ) ∨
      (ABDY.composedExtended P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

/-- Build a joint transition of the four components on a visible label, the
oracle's successor left arbitrary. -/
theorem composedExtended_visible_step (P : Parameters)
    {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n} {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A A' : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)}
    {L : ExtendedLabel P.n} (hL : L ≠ Silent.τ)
    (hG : (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A')) (hW : (coinOverRoundAlphabet P).step o L ω) :
    (ABDY.composedExtended P).step (G, C, A, o) L
    (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [ABDY.composedExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, roundLoopProduct_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- Build a silent transition of the four components from a graded-agreement one. -/
theorem composedExtended_tau_gbca (P : Parameters) {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (ABDY.composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [ABDY.composedExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA network injection. -/
theorem composedExtended_tau_ABANetwork (P : Parameters)
    {G : ℕ → GBCA.ByABDY.ImplementationState P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A A' : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    (hA : ABANetworkStep P A (Sum.inl Label.tau) (PMF.pure A')) :
    (ABDY.composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G, C, A', o)) := by
  rw [ABDY.composedExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-! ### The graded-agreement family's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else. -/

/-- The round-`r` instance moves on a label it owns. -/
theorem gbcaInstanceFamily_owned (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n)
    (r : ℕ) {L : ExtendedLabel P.n} (hL : GBCA.ByABDY.roundOwnsLabel L = some r)
    {X : GBCA.ByABDY.ImplementationState P.n}
    (h : (GBCA.ByABDY.composition P r).step (G r) L (PMF.pure X)) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure (Function.update G r X)) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure X, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose instance is unchanged. -/
theorem gbcaInstanceFamily_owned_id (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n)
  (r : ℕ)
    {L : ExtendedLabel P.n} (hL : GBCA.ByABDY.roundOwnsLabel L = some r)
    (h : (GBCA.ByABDY.composition P r).step (G r) L (PMF.pure (G r))) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G) := by
  have hstep := gbcaInstanceFamily_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` instance takes one of its own silent rules. -/
theorem gbcaInstanceFamily_tau (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n)
    (r : ℕ) {X : GBCA.ByABDY.ImplementationState P.n}
    (h : (GBCA.ByABDY.composition P r).step (G r) (Sum.inl Label.tau) (PMF.pure X)) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl Label.tau)
    (PMF.pure (Function.update G r X)) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure X, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem gbcaInstanceFamily_idle (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n)
    {L : ExtendedLabel P.n} (hτ : L ≠ Silent.τ) (hown : GBCA.ByABDY.roundOwnsLabel L = none)
    (hf : ¬ GBCA.ByABDY.isFailLabel L) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's network. -/
theorem gbcaInstanceFamily_fail (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n)
    (k : Fin P.n) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.fail k))
    (PMF.pure (fun r => GBCA.ByABDY.corruptionAct P (Sum.inl (Label.fail k)) (G r))) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-! ### The program tuple of one round -/

/-- One graded-agreement program moves and every other idles. -/
theorem gbcaProgramStep_family {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {L : GBCA.ByABDY.GBCALabel P.n} (id : Fin P.n)
    (nd : GBCA.ByABDY.RoundRecord P.n)
    (hown : GBCA.ByABDY.GBCAProgramStep P r id (u id) L (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → GBCA.ByABDY.GBCAProgramStep P r i (u i) L (PMF.pure (u i))) :
    ∀ i, GBCA.ByABDY.GBCAProgramStep P r i (u i) L (PMF.pure (Function.update u id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

/-! ### Hiding the rendezvous alphabet

The composition hides `NetworkEvent n`, so a transition of `ABDY.composedExtended` on a rendezvous
label is a silent transition of `ABDY.composedHidden`, as is one on `τ`. The two round rendezvous
never reach this point. They are internal to a round instance, hidden inside
`GBCA.ByABDY.composition`, and reach the composite as the family's own `τ`. -/

theorem composedHidden_of_event (P : Parameters) {q : ComposedState P} (e : NetworkEvent P.n)
    {μ : PMF (ComposedState P)} (h : (ABDY.composedExtended P).step q (Sum.inr e) μ) :
    (ABDY.composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedHidden_of_tau (P : Parameters) {q : ComposedState P} {μ : PMF (ComposedState P)}
    (h : (ABDY.composedExtended P).step q (Sum.inl Label.tau) μ) :
    (ABDY.composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inr h)

end Composition

/-! ## The substitution

The graded-agreement family of the protocol is forward simulated by the family
of round specifications, round by round, and the four congruences of the
pipeline carry that simulation to `hybrid`. -/

/-- The pointwise round relation: every round's instance state is related to
that round's specification state. -/
def substitutionRelationFamily (P : Parameters) (s : ℕ → GBCA.ByABDY.ImplementationState P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GBCA.ByABDY.substitutionRelation P r (s r) (t r)

/-- **The family substitution**: the graded-agreement family of the protocol is forward simulated by
the specification, round by round. The per-round simulation is `GBCA.ByABDY.instanceSubstitution`;
the broadcast compatibility is `GBCA.ByABDY.instanceSubstitution_failAct`. -/
theorem familySubstitution (P : Parameters) :
    ForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P) (gbcaSpecificationFamily P)
      (substitutionRelationFamily P) :=
  ForwardSimulation.family GBCA.ByABDY.roundOwnsLabel GBCA.ByABDY.isFailLabel
    (GBCA.ByABDY.corruptionAct P)
    (GBCA.ByABDY.specificationCorruptionAct P)
    (GBCA.ByABDY.instanceSubstitution P) (GBCA.ByABDY.instanceSubstitution_failAct P)

/-- The family substitution as a probabilistic forward simulation: both systems are LTS, and the
relation holds at the initial states. -/
theorem familySubstitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P) (gbcaSpecificationFamily P)
      (diracRel (substitutionRelationFamily P)) :=
  ForwardSimulation.toProbabilistic (GBCA.ByABDY.gbcaInstanceFamily_isLTS P)
    (gbcaSpecificationFamily_isLTS P)
    (fun r => GBCA.ByABDY.instanceSubstitution_init P r) (familySubstitution P)

namespace ABDY

/-- **The substitution simulation at the protocol shape**: the four
congruences applied to the family substitution under the composed system's own
context — `parallel_right` for the three untouched components, `abstract` for the
rendezvous alphabet, `relabel` for the read-back over `Label n`, and `abstract`
for the sub-protocol API. -/
noncomputable def substitutionSimulation (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (hybrid P)
      (parallelRel (diracRel (substitutionRelationFamily P))) :=
  ((((familySubstitutionSimulation P).parallel_right
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- **The substitution inclusion**: every trace distribution achievable by the
composed system is achievable by the protocol-shaped specification. -/
theorem substitution (P : Parameters) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P) :=
  (substitutionSimulation P).achievableTraceDists_subset

end ABDY

end ABA

end PLTS
