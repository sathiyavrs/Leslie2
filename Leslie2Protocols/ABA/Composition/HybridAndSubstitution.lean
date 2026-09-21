/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY
import Leslie2.Results

/-!
# The specification stages: the composed reading and the substitution

Two links of the refinement chain, and the row-by-row readings of the systems
they introduce. The headlines that chain these links with the earlier ones are
in `ABA/Results.lean`.

The first link is the composed reading. The protocol reading of
`ABA/ImplementationByABDY/System.lean` presents the protocol as `n` programs beside one network
adversary and the coin oracle. A program reads its own replacement flag and
nothing else about corruption: not the corrupted set, not the budget, not
another process's status (D23). Each program runs its round
loop and a graded-agreement stage at once, and the single adversary holds both
kinds of message sent. The composed reading reads the same protocol as a
composition of components:

* the graded-agreement side is the round-indexed family `GBCA.ByABDY.gbcaInstanceFamily`. Its
  round-`r` instance is a parallel component in its own right: the stage
  programs of round `r` beside the network of round `r`, which that
  instance owns outright;
* the round loops are `n` separate automata (`roundLoopProgram`), synchronised; * what is left of
the network adversary is the DECIDED sets beside the
  corrupted set (`ABANetwork`);
* the coin oracle enters through the same label pullback as in the protocol
  reading (`Composition.coinOverRoundAlphabet`).

The four components speak the extended alphabet `Composition.ExtendedLabel n`, the rendezvous
labels are hidden, and the result is read back over `Label n`. The round loops,
the ABA-side network and the lifted oracle are defined in `ABA/Composition/Components.lean`,
the round instances in `ABA/Composition/GBCAInstanceByABDY.lean`; the composition pipeline
`ABDY.composedExtended` / `ABDY.composedHidden` / `ABDY.composed` is the first section below.

The second link is the substitution, which replaces each round's
graded-agreement instance by that round's specification. `hybrid` is the
system that results, read at the protocol shape. The substitution is one
application of `ProbabilisticForwardSimulation.parallel_right` under a
syntactically identical context, followed by the three congruences the protocol
pipeline is built from: `abstract` for the rendezvous alphabet, `relabel` for
the read-back to `Label n` (`Framework/Relabel.lean`), and `abstract` again for
the sub-protocol API. The conclusion is `ABDY.substitution`, the inclusion of the
composed system's achievable trace distributions in the specification's.

## Per-round memory

A round instance is a component of the composite from the start, not an object
created by the round's first call, and it keeps its stage records and its
network state for the whole run. The graded-agreement coordinate of a composed state
is therefore `ℕ → GBCA.ByABDY.ImplementationState n`: every round is present at every moment,
whichever round each process is in. Those retained stage records are
specification-side state in one respect only: a process record of the protocol
holds its own stage records in a finite map and, once it terminates, answers
nothing further, where the round instance answers at every moment (D22).

## The authorisation relocation (D11)

A round instance carries no `k ∈ F` guard on the handshake-row labels `byzantineCallG`,
`byzantineCallGLoop` and `byzantineRetG` (`Composition/GBCAInstanceByABDY.lean`, D11). A
handshake-row label stays visible at the instance boundary and is authorised outside it. Here
`ABANetwork` is that outside, and it carries the guard on its own copy of the corrupted set.
The two copies are written by one broadcast: `fail` reaches every round's
network through the family (`gbcaInstanceFamily_fail`) and `ABANetwork` on its own `fail` row,
and `GBCA.ByABDY.NetworkState.corrupt` and `ABANetworkState.corrupt` are the same
budget-guarded insertion.

## What this file supplies

The composed system and its rows, the protocol-shaped specification and its
rows, and the substitution between them. The builders assemble a transition of
a composite out of transitions of its components (`composedExtended_vis_step`,
`composedExtended_tau_gbca`, `composedExtended_tau_ABANetwork`,
`gbcaInstanceFamily_owned`, `gbcaInstanceFamily_idle`, `gbcaInstanceFamily_tau`,
`gbcaInstanceFamily_fail`, `composedHidden_of_event`, `composedHidden_of_tau`, and their
counterparts on the specification side). On the specification side the reading also runs in the
inverse direction, from a composite transition back into the rows its
components contributed, and a labelled transition takes one of three routes through the
two hiding frames. The per-component rows these consume and produce are the tables
of `ABA/Composition/Components.lean` and `ABA/Composition/GBCAInstanceByABDY.lean`.

The core simulation of `ABA/HybridRefinesSpecification/Simulation.lean` runs from `hybrid` on this
vocabulary, and the non-vacuity witnesses of `ABA/HybridRefinesSpecification/NonVacuity.lean` are
built with it; `ABA/Results.lean` chains the simulation with the substitution and,
through `safety_transfer`, reads off the protocol's Validity and
Agreement guarantee.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-! ## The composed reading

The protocol cut into its components: the graded-agreement side as a
round-indexed family of instances, the round loops as `n` synchronised
automata, the DECIDED sets beside the corrupted set, and the lifted coin
oracle. This section
composes the four components and reads the rows of the composite. -/

namespace Composition

/-! ### The composition pipeline -/

/-- The state of the composed system: the round instances, the round loops,
the ABA-side network and the coin oracle. -/
abbrev ComposedState (P : Parameters) : Type :=
  (ℕ → GBCA.ByABDY.ImplementationState P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

end Composition

namespace ABDY

/-- The four components side by side, over the extended alphabet. -/
noncomputable def composedExtended (P : Parameters) : System (Composition.ComposedState P)
  (ExtendedLabel
  P.n) :=
  (GBCA.ByABDY.gbcaInstanceFamily P).parallel
    ((System.syncProduct (Composition.roundLoopProgram P)).parallel
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
theorem composedExtended_vis_step (P : Parameters) {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n}
    {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : ExtendedLabel P.n}
    (hL : L ≠ Silent.τ)
    (hG : (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o L ω) :
    (ABDY.composedExtended P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [ABDY.composedExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, roundLoopProduct_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- Build a silent transition of the four components from a graded-agreement-side
one. -/
theorem composedExtended_tau_gbca (P : Parameters) {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (ABDY.composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [ABDY.composedExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA-side network
injection. -/
theorem composedExtended_tau_ABANetwork (P : Parameters) {G : ℕ → GBCA.ByABDY.ImplementationState
  P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
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

/-! ### The graded-agreement side's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else. -/

/-- The round-`r` instance moves on a label it owns. -/
theorem gbcaInstanceFamily_owned (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n) (r :
  ℕ)
    {L : ExtendedLabel P.n} (hL : GBCA.ByABDY.roundOwnsLabel L = some r) {X :
      GBCA.ByABDY.ImplementationState P.n}
    (h : (GBCA.ByABDY.composition P r).step (G r) L (PMF.pure X)) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure (Function.update G r X)) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure X, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose instance stands still. -/
theorem gbcaInstanceFamily_owned_id (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n)
  (r : ℕ)
    {L : ExtendedLabel P.n} (hL : GBCA.ByABDY.roundOwnsLabel L = some r)
    (h : (GBCA.ByABDY.composition P r).step (G r) L (PMF.pure (G r))) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G) := by
  have hstep := gbcaInstanceFamily_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` instance takes one of its own silent rules. -/
theorem gbcaInstanceFamily_tau (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n) (r :
  ℕ)
    {X : GBCA.ByABDY.ImplementationState P.n}
    (h : (GBCA.ByABDY.composition P r).step (G r) (Sum.inl Label.tau) (PMF.pure X)) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl Label.tau) (PMF.pure (Function.update G r X))
      := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure X, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem gbcaInstanceFamily_idle (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n) {L :
  ExtendedLabel
  P.n}
    (hτ : L ≠ Silent.τ) (hown : GBCA.ByABDY.roundOwnsLabel L = none) (hf : ¬ GBCA.ByABDY.isFailLabel
      L) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's network. -/
theorem gbcaInstanceFamily_fail (P : Parameters) (G : ℕ → GBCA.ByABDY.ImplementationState P.n) (k :
  Fin P.n) :
    (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.fail k))
      (PMF.pure (fun r => GBCA.ByABDY.corruptionAct P (Sum.inl (Label.fail k)) (G r))) := by
  rw [GBCA.ByABDY.gbcaInstanceFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-! ### The stage-program tuple of one round -/

/-- One stage program moves and every other idles. -/
theorem gprocs_family {P : Parameters} {r : ℕ}
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

The composition hides `NetworkEvent n`, so a transition of `ABDY.composedExtended` on a
rendezvous label is a silent transition of `ABDY.composedHidden`, as is one on `τ`.
The two stage rendezvous never reach this point. They are internal to a round
instance, hidden inside `GBCA.ByABDY.composition`, and reach the composite as the family's
own `τ`. -/

theorem composedHidden_of_event (P : Parameters) {q : ComposedState P} (e : NetworkEvent P.n)
    {μ : PMF (ComposedState P)} (h : (ABDY.composedExtended P).step q (Sum.inr e) μ) :
    (ABDY.composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedHidden_of_tau (P : Parameters) {q : ComposedState P} {μ : PMF (ComposedState P)}
    (h : (ABDY.composedExtended P).step q (Sum.inl Label.tau) μ) :
    (ABDY.composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inr h)

end Composition

open Composition

/-! ## The protocol-shaped specification side

The composed system replaces its graded-agreement component `GBCA.ByABDY.gbcaInstanceFamily` —
the family of round instances — by `gbcaSpecificationFamily`, the family of round
specifications read over the protocol alphabet. The other three components are
reused verbatim,
so the substitution is `ProbabilisticForwardSimulation.parallel_right` applied
under the syntactically identical context, followed by the three remaining
congruences: `abstract` for the rendezvous alphabet, `relabel` for the read-back
to `Label n`, and `abstract` again for the sub-protocol API. -/

/-- **The specification side of the protocol**: the ℕ-indexed family
of round specifications, read over the protocol extended alphabet along
`GBCA.ByABDY.gbcaLabelMap`. A round-tagged label — including a Byzantine handshake row of that
round — moves its round alone, `τ` moves one round, and `fail` is the
broadcast that keeps every round's copy of the corrupted set in lockstep. -/
noncomputable def gbcaSpecificationFamily (P : Parameters) :
    System (ℕ → GBCA.SpecState P.n) (ExtendedLabel P.n) :=
  System.family (GBCA.ByABDY.specificationOverRoundAlphabet P) GBCA.ByABDY.roundOwnsLabel
    GBCA.ByABDY.isFailLabel
    (GBCA.ByABDY.specificationCorruptionAct P)

@[simp] theorem gbcaSpecificationFamily_init (P : Parameters) :
    (gbcaSpecificationFamily P).init = fun _ => GBCA.SpecState.initial P.n := rfl

/-- The specification side is an LTS: every round's specification is. -/
theorem gbcaSpecificationFamily_isLTS (P : Parameters) : (gbcaSpecificationFamily P).IsLTS :=
  System.family_isLTS (GBCA.ByABDY.specificationOverRoundAlphabet_isLTS P) _ _ _

/-- The state of the protocol-shaped specification: the round
specifications beside the composed system's other three components. -/
abbrev HybridState (P : Parameters) : Type :=
  (ℕ → GBCA.SpecState P.n) ×
    ((∀ _ : Fin P.n, RoundLoopRecord P.n) × (ABANetworkState P.n × (ℕ → WCC.SpecState P.n)))

/-- The four components side by side, over the extended alphabet:
`ABDY.composedExtended` with its graded-agreement component replaced. -/
noncomputable def hybridExtended (P : Parameters) : System (HybridState P) (ExtendedLabel P.n) :=
  (gbcaSpecificationFamily P).parallel
    ((System.syncProduct (roundLoopProgram P)).parallel ((ABANetwork P).parallel
      (coinOverRoundAlphabet P)))

/-- **The protocol-shaped specification**: the rendezvous alphabet hidden,
the result read back over `Label n`, the sub-protocol API hidden — the pipeline
of `ABDY.composed`, component for component. -/
noncomputable def hybrid (P : Parameters) : System (HybridState P) (Label P.n) :=
  (((hybridExtended P).abstract (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-! ### The substitution -/

/-- The pointwise round relation: every round's instance state is related to
that round's specification state. -/
def RsubAll (P : Parameters) (s : ℕ → GBCA.ByABDY.ImplementationState P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GBCA.ByABDY.Rsub P r (s r) (t r)

/-- **The family substitution**: the graded-agreement side of the protocol is
forward simulated by the specification side, round by round. The per-round
simulation is `GBCA.ByABDY.subSim`; the broadcast compatibility is
`GBCA.ByABDY.subSim_failAct`. -/
theorem famSubSim (P : Parameters) :
    ForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P) (gbcaSpecificationFamily P) (RsubAll P) :=
  ForwardSimulation.family GBCA.ByABDY.roundOwnsLabel GBCA.ByABDY.isFailLabel
    (GBCA.ByABDY.corruptionAct P)
    (GBCA.ByABDY.specificationCorruptionAct P)
    (GBCA.ByABDY.subSim P) (GBCA.ByABDY.subSim_failAct P)

/-- The family substitution as a probabilistic forward simulation: both sides
are LTS, and the relation holds at the initial states. -/
theorem famSubSimProb (P : Parameters) :
    ProbabilisticForwardSimulation (GBCA.ByABDY.gbcaInstanceFamily P) (gbcaSpecificationFamily P)
      (diracRel (RsubAll P)) :=
  ForwardSimulation.toProbabilistic (GBCA.ByABDY.gbcaInstanceFamily_isLTS P)
    (gbcaSpecificationFamily_isLTS P)
    (fun r => GBCA.ByABDY.subSim_init P r) (famSubSim P)

namespace ABDY

/-- **The substitution simulation at the protocol shape**: the four
congruences applied to the family substitution under the composed system's own
context — `parallel_right` for the three untouched components, `abstract` for the
rendezvous alphabet, `relabel` for the read-back over `Label n`, and `abstract`
for the sub-protocol API. -/
noncomputable def substSim (P : Parameters) :
    ProbabilisticForwardSimulation (composed P) (hybrid P)
      (parallelRel (diracRel (RsubAll P))) :=
  ((((famSubSimProb P).parallel_right
    ((System.syncProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
        (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)

/-- **The substitution inclusion**: every trace distribution achievable by the
composed system is achievable by the protocol-shaped specification. -/
theorem substitution (P : Parameters) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P) :=
  (substSim P).achievableTraceDists_subset

end ABDY

/-! ### The specification side's rows

The family routes a round-tagged label to its round, takes `τ` at any round,
broadcasts `fail`, and idles on everything else — `GBCA.ByABDY.gbcaInstanceFamily`'s rows with
the round instance replaced by its specification. -/

/-- The specification side idles on a label no round owns and no broadcast. -/
theorem gbcaSpecificationFamily_idle (P : Parameters) (G : ℕ → GBCA.SpecState P.n) {L :
  ExtendedLabel
  P.n}
    (hτ : L ≠ Silent.τ) (hown : GBCA.ByABDY.roundOwnsLabel L = none) (hf : ¬ GBCA.ByABDY.isFailLabel
      L) :
    (gbcaSpecificationFamily P).step G L (PMF.pure G) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round specification. -/
theorem gbcaSpecificationFamily_fail (P : Parameters) (G : ℕ → GBCA.SpecState P.n) (k : Fin P.n) :
    (gbcaSpecificationFamily P).step G (Sum.inl (Label.fail k)) (PMF.pure fun r => (G r).corrupt P
      k) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- An owned label is answered by its round alone. -/
theorem gbcaSpecificationFamily_owned_inv (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
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

/-- A round's own row, read into the specification side: the label the round
owns is answered by that round, every other round standing still. -/
theorem gbcaSpecificationFamily_owned (P : Parameters) {G : ℕ → GBCA.SpecState P.n} {L :
  ExtendedLabel
  P.n}
    {l₀ : Label P.n} {r : ℕ} {X : GBCA.SpecState P.n}
    (hown : GBCA.ByABDY.roundOwnsLabel L = some r) (hpull : GBCA.ByABDY.gbcaLabelMap P.n L = some
      l₀)
    (h : GBCA.Step P r (G r) l₀ (PMF.pure X)) :
    (gbcaSpecificationFamily P).step G L (PMF.pure (Function.update G r X)) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  refine Or.inr (Or.inl ⟨r, hown, PMF.pure X, ?_, by rw [PMF.pure_map]⟩)
  rw [GBCA.ByABDY.specificationOverRoundAlphabet, System.mapIdle_step_some hpull]
  exact h

/-- A round's own silent rule — the specification's binding exclusion — read into
the specification side. -/
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
  obtain ⟨X, hstep, heq⟩ := gbcaSpecificationFamily_owned_inv P hown hτ h
  rw [GBCA.ByABDY.specificationOverRoundAlphabet, System.mapIdle_step_some hpull] at hstep
  exact ⟨X, hstep, pure_inj heq⟩

/-- Only the identity successor answers a label no round owns and no
broadcast. -/
theorem gbcaSpecificationFamily_idle_inv (P : Parameters) {G : ℕ → GBCA.SpecState P.n} {L :
  ExtendedLabel P.n}
    {μ : PMF (ℕ → GBCA.SpecState P.n)} (h : (gbcaSpecificationFamily P).step G L μ)
    (hτ : L ≠ Silent.τ) (hown : GBCA.ByABDY.roundOwnsLabel L = none) (hf : ¬ GBCA.ByABDY.isFailLabel
      L) :
    μ = PMF.pure G := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hτ
  · rw [hown] at hr; exact absurd hr (by simp)
  · exact absurd hglob hf
  · rfl

/-- Corruption is broadcast to every round. -/
theorem gbcaSpecificationFamily_fail_inv (P : Parameters) {G : ℕ → GBCA.SpecState P.n} (k : Fin P.n)
    {μ : PMF (ℕ → GBCA.SpecState P.n)}
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
theorem gbcaSpecificationFamily_tau_inv (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
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
theorem wccFamily_idle_inv (P : Parameters) {o : ℕ → WCC.SpecState P.n} {l : Label P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)} (hl : l ≠ Label.tau) (hr : Label.wccRound l = none)
    (hf : ¬ Label.isFail l) (h : (WCC.specFamily P).step o l ω) : ω = PMF.pure o := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd hτ hl
  · rw [hr] at hr'; exact absurd hr' (by simp)
  · exact absurd hglob hf
  · rfl

/-- A label the coin oracle's family owns is answered by its round alone. -/
theorem wccFamily_owned_inv (P : Parameters) {o : ℕ → WCC.SpecState P.n} {l : Label P.n}
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
standing still. -/
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
theorem wccFamily_fail_inv (P : Parameters) {o : ℕ → WCC.SpecState P.n} (k : Fin P.n)
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
theorem hybridExtended_vis_step (P : Parameters) {G G' : ℕ → GBCA.SpecState P.n}
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
theorem hybridExtended_vis_inv (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
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
    · obtain ⟨C', rfl, hall⟩ := roundLoopProduct_inv hC
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

/-- Build a silent transition of the four components from a specification-side
one. -/
theorem hybridExtended_tau_spec (P : Parameters) {G G' : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (gbcaSpecificationFamily P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (hybridExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [hybridExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- A silent transition of the four components: no round loop has a `τ` row, and
neither has the coin oracle, so it is the specification family's binding
exclusion or the ABA-side network's own injection. -/
theorem hybridExtended_tau_inv (P : Parameters) {G : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {μ : PMF (HybridState P)}
    (h : (hybridExtended P).step (G, C, A, o) (Sum.inl Label.tau) μ) :
    (∃ G', (gbcaSpecificationFamily P).step G (Sum.inl Label.tau) (PMF.pure G') ∧
        μ = PMF.pure (G', C, A, o)) ∨
    (∃ A', ABANetworkStep P A (Sum.inl Label.tau) (PMF.pure A') ∧
        μ = PMF.pure (G, C, A', o)) := by
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
      · exact (WCC.specFamily_tau_inv P
          ((System.mapIdle_step_some (coinLabelMap_inl Label.tau) ω).mp hW)).elim

/-! ### The two hiding frames -/

/-- **The protocol-shaped group**: the rendezvous alphabet hidden, the result
read back over `Label n`. Scaffolding for the row-by-row reading below; nothing
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
theorem hybrid_vis (P : Parameters) {q : HybridState P} {l : Label P.n}
    {μ : PMF (HybridState P)} (hl : l ∉ Label.hiddenAPI P.n)
    (h : (hybridExtended P).step q (Sum.inl l) μ) :
    (hybrid P).step q l μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨hl, (hybridHidden_step_iff P q l μ).mpr (Or.inr h)⟩

end ABA

end PLTS
