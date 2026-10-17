/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.CompositionStepCases
import Leslie2Protocols.ABA.Gather.AlgorithmOverBroadcastSpecification
import Leslie2Protocols.ABA.Gather.RefinesSpecification
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The gather substitution inside the round

`GBCA.ByAFW.gatherSubstitution`: the round over the gather instances over the broadcast
specification (`GBCA.ByAFW.roundOverBroadcastSpecification`) is forward simulated by the round over
the gather specifications (`GBCA.ByAFW.roundOverGatherSpecifications`), along
`GBCA.ByAFW.GatherSubstitutionRelation`: the round's programs and the round's network held equal,
and each of the two gather coordinates related by the gather refinement relation
(`Gather.SpecificationRelation`).

The proof is the congruence argument alone. The two rounds are one expression over the two gather
instances, so the substitution of one of them is carried through the operators that expression
is built from: `ForwardSimulation.mapIdle` reads one gather instance over the round-internal
alphabet, `ForwardSimulation.parallel_right` and `ForwardSimulation.parallel_left` hold the other
gather instance and then the round's programs, and `ForwardSimulation.abstract` and
`ForwardSimulation.relabel` hide the round's events and read the result back over the family
alphabet. The two gather instances are replaced one after the other and the two steps are joined by
`ForwardSimulation.trans`. `ForwardSimulation.congr` then reshapes the composite relation: the
intermediate state the composite quantifies over is the first coordinate of the abstract system
beside the second coordinate of the concrete system.

Both rounds are LTS, so the substitution reads as an inclusion of achievable trace distributions,
`roundOverBroadcastSpecification_refines`. `gatherSubstitutionRelation_corrupt` states that the
relation is preserved by corrupting both rounds at once, in the shape the family congruence
consumes (`ForwardSimulation.family`, `hglob`); the gather instance's own compatibility lemma,
`Gather.specificationRelation_corrupt`, is in `ABA/Gather/SpecificationRelation.lean`.

## The first step at an untouched round

The family congruence (`ForwardSimulation.family`) asks that a transition on a label the round owns
be matched by a transition on the same label followed by a silent run. A family label reaches the
first gather as a call or a corruption and the second gather as a corruption. The gather
specification matches a call of the gather instance by its call or its loop and a corruption by
its corruption (`gatherSubstitution_call`, `gatherSubstitution_fail`), so every visible transition
of the round is matched by one transition on its label (`gatherSubstitution_visibleStep`), the
same round program's transition in both rounds. `gatherSubstitution_untouchedFirstStep` is the
hypothesis of the family congruence, at every state the relation holds.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

/-! ### The gather substitution -/

/-- The gather substitution relation of the round: the round's programs equal, and each gather
coordinate related to its specification coordinate by the gather refinement relation. -/
structure GatherSubstitutionRelation (P : Parameters) (s : RoundStateOverBroadcastSpecification P.n)
    (t : RoundStateOverGatherSpecifications P.n) : Prop where
  /-- The programs and the round's network are untouched by the substitution. -/
  roundPrograms_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  firstGatherRelation : Gather.SpecificationRelation P (firstGather s) (firstGather t)
  /-- The second gather coordinate is substituted. -/
  secondGatherRelation : Gather.SpecificationRelation P (secondGather s) (secondGather t)

/-- The relation holds initially. -/
theorem gatherSubstitutionRelation_init (P : Parameters) (r : ℕ) :
    GatherSubstitutionRelation P (roundOverBroadcastSpecification P r).init
      (roundOverGatherSpecifications P r).init
      :=
  ⟨rfl, Gather.specificationRelation_init, Gather.specificationRelation_init⟩

/-- **The gather substitution inside the round.** The round over the gather
instances over the broadcast specification is forward simulated by the round
over the gather specifications. -/
theorem gatherSubstitution (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverBroadcastSpecification P r) (roundOverGatherSpecifications P r)
      (GatherSubstitutionRelation P) := by
  have h1 : ForwardSimulation ((Gather.instanceOverBroadcastSpecification P Bool).mapIdle
    (firstGatherLabelMap P.n))
      ((Gather.specInst P Bool).mapIdle (firstGatherLabelMap P.n))
        (Gather.SpecificationRelation P) :=
    ForwardSimulation.mapIdle (firstGatherLabelMap P.n) (firstGatherLabelMap_tau P.n)
      (fun _ h => firstGatherLabelMap_eq_tau h) (Gather.refinesSpecification P Bool)
  have h2 : ForwardSimulation ((Gather.instanceOverBroadcastSpecification P (Option Bool)).mapIdle
    (secondGatherLabelMap P.n))
      ((Gather.specInst P (Option Bool)).mapIdle (secondGatherLabelMap P.n))
        (Gather.SpecificationRelation P) :=
    ForwardSimulation.mapIdle (secondGatherLabelMap P.n) (secondGatherLabelMap_tau P.n)
      (fun _ h => secondGatherLabelMap_eq_tau h) (Gather.refinesSpecification P (Option Bool))
  have hGa := (h1.parallel_right ((Gather.instanceOverBroadcastSpecification P (Option
    Bool)).mapIdle (secondGatherLabelMap P.n))).trans
    (h2.parallel_left ((Gather.specInst P Bool).mapIdle (firstGatherLabelMap P.n)))
  have hRound := ((hGa.parallel_left (roundPrograms P r)).abstract (roundEvents P.n)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hRound
  constructor
  · rintro ⟨hRoundPrograms, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hRoundPrograms, h1', h2'⟩
  · rintro ⟨hRoundPrograms, h1', h2'⟩
    exact ⟨hRoundPrograms, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather instances over
the broadcast specification in the round over the gather specifications. -/
theorem roundOverBroadcastSpecification_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBroadcastSpecification P r) ⊆ achievableTraceDists
      (roundOverGatherSpecifications P r) :=
  (ForwardSimulation.toProbabilistic (roundOverBroadcastSpecification_isLTS P r)
    (roundOverGatherSpecifications_isLTS P r)
    (gatherSubstitutionRelation_init P r) (gatherSubstitution P r)).achievableTraceDists_subset

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility of the gather substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem gatherSubstitutionRelation_corrupt {P : Parameters}
    {s : RoundStateOverBroadcastSpecification P.n} {t : RoundStateOverGatherSpecifications P.n}
    (hR : GatherSubstitutionRelation P s t) (id : Fin P.n) :
    GatherSubstitutionRelation P
      (corruptAll P id
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i))
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i))
        s)
      (corruptAll P id (fun i => Gather.SpecState.corrupt P i)
        (fun i => Gather.SpecState.corrupt P i) t) :=
  ⟨hR.roundPrograms_eq, Gather.specificationRelation_corrupt hR.firstGatherRelation id,
    Gather.specificationRelation_corrupt hR.secondGatherRelation id⟩


/-! ### The first step at an untouched round -/

section GatherSteps
variable {X : Type} [DecidableEq X] {P : Parameters}

/-- The gather specification matches a call of the gather instance over the broadcast
specification by one transition: its call where the gather program records the payload, its loop
where the program holds one. -/
theorem gatherSubstitution_call {c c' : Gather.StateOverBroadcastSpecification P.n X}
    {e : Gather.SpecState P.n X} {id : Fin P.n} {x : X} (hR : Gather.SpecificationRelation P c e)
    (h : (Gather.instanceOverBroadcastSpecification P X).step c (.call id x) (PMF.pure c')) :
    ∃ e', (Gather.specInst P X).step e (.call id x) (PMF.pure e') ∧
      Gather.SpecificationRelation P c' e' := by
  have ha := (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P c _ _).mp h
  generalize hμ : (PMF.pure c' : PMF (Gather.StateOverBroadcastSpecification P.n X)) = μ at ha
  cases ha with
  | call _ _ h0 =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact ⟨_, (Gather.specInst_step P _ _ _).mpr
      (Gather.Step.call e id x (by rw [hR.call_eq id]; exact h0)),
      Gather.specificationRelation_call hR h0⟩
  | callLoop _ _ hin =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact ⟨e, (Gather.specInst_step P _ _ _).mpr (Gather.Step.callLoop e id x), hR⟩

/-- The gather specification matches a corruption of the gather instance over the broadcast
specification by its corruption. -/
theorem gatherSubstitution_fail {c c' : Gather.StateOverBroadcastSpecification P.n X}
    {e : Gather.SpecState P.n X} {id : Fin P.n} (hR : Gather.SpecificationRelation P c e)
    (h : (Gather.instanceOverBroadcastSpecification P X).step c (.fail id) (PMF.pure c')) :
    ∃ e', (Gather.specInst P X).step e (.fail id) (PMF.pure e') ∧
      Gather.SpecificationRelation P c' e' := by
  have ha := (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P c _ _).mp h
  generalize hμ : (PMF.pure c' : PMF (Gather.StateOverBroadcastSpecification P.n X)) = μ at ha
  cases ha with
  | fail _ =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact ⟨_, (Gather.specInst_step P _ _ _).mpr (Gather.Step.fail e id),
      Gather.specificationRelation_corrupt hR id⟩

end GatherSteps

/-- **A visible transition matched by one step.** At related states, a visible transition of the
round over the gather instances over the broadcast specification is matched by one transition on
the same label of the round over the gather specifications. -/
theorem gatherSubstitution_visibleStep (P : Parameters) (r : ℕ)
    {s : RoundStateOverBroadcastSpecification P.n} {t : RoundStateOverGatherSpecifications P.n}
    (hR : GatherSubstitutionRelation P s t) {l : Composition.ExtendedLabel P.n Empty}
    (hl : l ≠ Sum.inl Label.tau) {μ : PMF (RoundStateOverBroadcastSpecification P.n)}
    (hstep : (roundOverBroadcastSpecification P r).step s l μ)
    {x : RoundStateOverBroadcastSpecification P.n} (hx : x ∈ μ.support) :
    ∃ y, GatherSubstitutionRelation P x y ∧
      (roundOverGatherSpecifications P r).step t l (PMF.pure y) := by
  obtain ⟨y, h1, h2, h3, hstepA⟩ := roundOverGathers_visibleStep_transfer
    (Gather.instanceOverBroadcastSpecification_isLTS P)
    (Gather.instanceOverBroadcastSpecification_isLTS P)
    (Gather.SpecificationRelation P) (Gather.SpecificationRelation P)
    (fun _ _ _ _ _ hR' h => gatherSubstitution_call hR' h)
    (fun _ _ _ _ hR' h => gatherSubstitution_fail hR' h)
    (fun _ _ _ _ hR' h => gatherSubstitution_fail hR' h)
    hR.roundPrograms_eq hR.firstGatherRelation hR.secondGatherRelation hl hstep hx
  exact ⟨y, ⟨h1, h2, h3⟩, hstepA⟩

/-- **The first step at an untouched round.** From related states reached by a list of
broadcasts, a transition of the round on a label the round owns is matched by one transition on
the same label, the same round program's transition in both rounds. -/
theorem gatherSubstitution_untouchedFirstStep (P : Parameters)
    (owns : Composition.ExtendedLabel P.n Empty → Option ℕ) (hOwnsSilent : owns Silent.τ = none)
    (actC : Composition.ExtendedLabel P.n Empty → RoundStateOverBroadcastSpecification P.n →
      RoundStateOverBroadcastSpecification P.n)
    (actA : Composition.ExtendedLabel P.n Empty → RoundStateOverGatherSpecifications P.n →
      RoundStateOverGatherSpecifications P.n)
    (initialC : RoundStateOverBroadcastSpecification P.n)
    (initialA : RoundStateOverGatherSpecifications P.n) :
    ∀ (r : ℕ) (broadcasts : List (Composition.ExtendedLabel P.n Empty))
      (l : Composition.ExtendedLabel P.n Empty), owns l = some r →
      GatherSubstitutionRelation P (broadcasts.foldr actC initialC)
        (broadcasts.foldr actA initialA) →
      ∀ μ, (roundOverBroadcastSpecification P r).step (broadcasts.foldr actC initialC) l μ →
      ∀ x ∈ μ.support, ∃ y, GatherSubstitutionRelation P x y ∧
        ∃ ν, (roundOverGatherSpecifications P r).step (broadcasts.foldr actA initialA) l ν ∧
          ∃ z ∈ ν.support, (roundOverGatherSpecifications P r).weakLSilent z y := by
  intro r broadcasts l howns hR μ hstep x hx
  have hl : l ≠ Sum.inl Label.tau := by
    rintro rfl
    exact absurd (howns.symm.trans hOwnsSilent) (by simp)
  obtain ⟨y, hRxy, hstepA⟩ := gatherSubstitution_visibleStep P r hR hl hstep hx
  exact ⟨y, hRxy, PMF.pure y, hstepA, y, (PMF.mem_support_pure_iff _ _).mpr rfl,
    System.weakLSilent_refl _ y⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.gatherSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherSubstitution

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverBroadcastSpecification_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBroadcastSpecification_refines

/-- info: 'PLTS.ABA.GBCA.ByAFW.gatherSubstitution_untouchedFirstStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherSubstitution_untouchedFirstStep

end GBCA.ByAFW
end ABA
end PLTS
