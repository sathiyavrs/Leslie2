/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.CompositionStepCases
import Leslie2Protocols.ABA.Gather.AlgorithmOverBracha
import Leslie2Protocols.ABA.Gather.AlgorithmOverBroadcastSpecification
import Leslie2Protocols.ABA.Gather.BroadcastSubstitution
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.FinerAlphabetCongruence
import Leslie2.Results

/-!
# The broadcast substitution inside the round

`GBCA.ByAFW.broadcastSubstitution`: the round over the gather instances over Bracha's broadcast
(`GBCA.ByAFW.roundOverBracha`) is forward simulated by the round over the gather instances over the
broadcast specification (`GBCA.ByAFW.roundOverBroadcastSpecification`), along
`GBCA.ByAFW.BroadcastSubstitutionRelation`: the round's programs and the round's network held
equal, and each of the two gather coordinates related by the broadcast substitution of that
gather instance (`Gather.BroadcastSubstitutionRelation`).

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
`roundOverBracha_refines`. `broadcastSubstitutionRelation_corrupt` states that the relation is
preserved by corrupting both rounds at once, in the shape the family congruence consumes
(`ForwardSimulation.family`, `hglob`); the gather instance's own compatibility lemma,
`Gather.broadcastSubstitutionRelation_corrupt`, is in `ABA/Gather/BroadcastSubstitution.lean`.

## The first step at an untouched round

The family congruence (`ForwardSimulation.family`) asks that a transition on a label the round owns
be matched by a transition on the same label followed by a silent run. A family label reaches the
first gather as a call or a corruption and the second gather as a corruption, and the broadcast
substitution of a gather instance matches each of them by the same transition of the gather
programs (`gatherBroadcastSubstitution_call`, `gatherBroadcastSubstitution_fail`). Every visible
transition of the round is therefore matched by one transition on its label
(`broadcastSubstitution_visibleStep`), and `broadcastSubstitution_untouchedFirstStep` is the
hypothesis of the family congruence, at every state the relation holds.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

/-! ### The broadcast substitution -/

/-- The broadcast substitution relation of the round: the round's programs equal, and each gather
coordinate related to its broadcast-specification coordinate by the gather substitution relation. -/
structure BroadcastSubstitutionRelation (P : Parameters) (s : RoundStateOverBracha P.n)
    (t : RoundStateOverBroadcastSpecification P.n) : Prop where
  /-- The programs and the round's network are untouched by the substitution. -/
  roundPrograms_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  firstGatherRelation : Gather.BroadcastSubstitutionRelation P (firstGather s) (firstGather t)
  /-- The second gather coordinate is substituted. -/
  secondGatherRelation : Gather.BroadcastSubstitutionRelation P (secondGather s) (secondGather t)

/-- The relation holds initially. -/
theorem broadcastSubstitutionRelation_init (P : Parameters) (r : ℕ) :
    BroadcastSubstitutionRelation P (roundOverBracha P r).init
    (roundOverBroadcastSpecification P r).init :=
  ⟨rfl, Gather.broadcastSubstitutionRelation_init, Gather.broadcastSubstitutionRelation_init⟩

/-- **The broadcast substitution inside the round.** The round over the gather
instances over Bracha's broadcast is forward simulated by the round over the
gather instances over the broadcast specification. Each gather coordinate
carries the substitution; the congruences carry it through the round. -/
theorem broadcastSubstitution (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverBracha P r) (roundOverBroadcastSpecification P r)
      (BroadcastSubstitutionRelation P) :=
      by
  have h1 : ForwardSimulation ((Gather.instanceOverBracha P Bool).mapIdle (firstGatherLabelMap P.n))
      ((Gather.instanceOverBroadcastSpecification P Bool).mapIdle (firstGatherLabelMap P.n))
        (Gather.BroadcastSubstitutionRelation P) :=
    ForwardSimulation.mapIdle (firstGatherLabelMap P.n) (firstGatherLabelMap_tau P.n)
      (fun _ h => firstGatherLabelMap_eq_tau h) (Gather.broadcastSubstitution P Bool)
  have h2 : ForwardSimulation ((Gather.instanceOverBracha P (Option Bool)).mapIdle
    (secondGatherLabelMap P.n))
      ((Gather.instanceOverBroadcastSpecification P (Option Bool)).mapIdle (secondGatherLabelMap
        P.n)) (Gather.BroadcastSubstitutionRelation P) :=
    ForwardSimulation.mapIdle (secondGatherLabelMap P.n) (secondGatherLabelMap_tau P.n)
      (fun _ h => secondGatherLabelMap_eq_tau h) (Gather.broadcastSubstitution P (Option Bool))
  have hGa := (h1.parallel_right ((Gather.instanceOverBracha P (Option Bool)).mapIdle
    (secondGatherLabelMap P.n))).trans
    (h2.parallel_left ((Gather.instanceOverBroadcastSpecification P Bool).mapIdle
      (firstGatherLabelMap P.n)))
  have hRound := ((hGa.parallel_left (roundPrograms P r)).abstract (roundEvents P.n)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hRound
  constructor
  · rintro ⟨hRoundPrograms, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hRoundPrograms, h1', h2'⟩
  · rintro ⟨hRoundPrograms, h1', h2'⟩
    exact ⟨hRoundPrograms, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather instances over
Bracha's broadcast in the round over the gather instances over the broadcast
specification. -/
theorem roundOverBracha_refines (P : Parameters) (r : ℕ) :
    achievableTraceDists (roundOverBracha P r) ⊆ achievableTraceDists
      (roundOverBroadcastSpecification P r) :=
  (ForwardSimulation.toProbabilistic (roundOverBracha_isLTS P r)
    (roundOverBroadcastSpecification_isLTS P r)
    (broadcastSubstitutionRelation_init P r) (broadcastSubstitution P
      r)).achievableTraceDists_subset

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility of the broadcast substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem broadcastSubstitutionRelation_corrupt {P : Parameters} {s : RoundStateOverBracha P.n}
    {t : RoundStateOverBroadcastSpecification P.n} (hR : BroadcastSubstitutionRelation P s t)
    (id : Fin P.n) :
    BroadcastSubstitutionRelation P
      (corruptAll P id
        (fun i => Gather.corruptAll P i (InstanceState.corrupt P i))
        (fun i => Gather.corruptAll P i (InstanceState.corrupt P i)) s)
      (corruptAll P id
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i))
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i))
        t) :=
  ⟨hR.roundPrograms_eq, Gather.broadcastSubstitutionRelation_corrupt hR.firstGatherRelation id,
    Gather.broadcastSubstitutionRelation_corrupt hR.secondGatherRelation id⟩


/-! ### The first step at an untouched round -/

section GatherSteps
variable {X : Type} [DecidableEq X] {P : Parameters}

/-- The broadcast substitution of a gather instance matches a call by one call: the gather
programs take the same transition in both instances. -/
theorem gatherBroadcastSubstitution_call {c c' : Gather.StateOverBracha P.n X}
    {e : Gather.StateOverBroadcastSpecification P.n X} {id : Fin P.n} {x : X}
    (hR : Gather.BroadcastSubstitutionRelation P c e)
    (h : (Gather.instanceOverBracha P X).step c (.call id x) (PMF.pure c')) :
    ∃ e', (Gather.instanceOverBroadcastSpecification P X).step e (.call id x) (PMF.pure e') ∧
      Gather.BroadcastSubstitutionRelation P c' e' := by
  have hga : Gather.gatherProgramsAndNetwork c = Gather.gatherProgramsAndNetwork e := by
    unfold Gather.gatherProgramsAndNetwork
    rw [hR.gatherProgramsAndNetwork_eq]
  have hset : ∀ T, (Gather.setGatherProgramsAndNetwork c T).1 =
      (Gather.setGatherProgramsAndNetwork e T).1 := by
    intro T
    unfold Gather.setGatherProgramsAndNetwork
    rw [hR.gatherProgramsAndNetwork_eq]
  have ha := (Gather.instanceOverBracha_step_iff_algorithm P c _ _).mp h
  generalize hμ : (PMF.pure c' : PMF (Gather.StateOverBracha P.n X)) = μ at ha
  cases ha with
  | call _ _ h0 =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    rw [hga] at h0
    refine ⟨_, (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P e _ _).mpr
      (Gather.AlgorithmOverBroadcastSpecification.call e id x h0), ?_,
      hR.inputBroadcastRelation⟩
    rw [hga]
    exact hset _
  | callLoop _ _ hin =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    rw [hga] at hin
    exact ⟨e, (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P e _ _).mpr
      (Gather.AlgorithmOverBroadcastSpecification.callLoop e id x hin), hR⟩

/-- The broadcast substitution of a gather instance matches a corruption by one corruption. -/
theorem gatherBroadcastSubstitution_fail {c c' : Gather.StateOverBracha P.n X}
    {e : Gather.StateOverBroadcastSpecification P.n X} {id : Fin P.n}
    (hR : Gather.BroadcastSubstitutionRelation P c e)
    (h : (Gather.instanceOverBracha P X).step c (.fail id) (PMF.pure c')) :
    ∃ e', (Gather.instanceOverBroadcastSpecification P X).step e (.fail id) (PMF.pure e') ∧
      Gather.BroadcastSubstitutionRelation P c' e' := by
  have ha := (Gather.instanceOverBracha_step_iff_algorithm P c _ _).mp h
  generalize hμ : (PMF.pure c' : PMF (Gather.StateOverBracha P.n X)) = μ at ha
  cases ha with
  | fail _ =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact ⟨_, (Gather.instanceOverBroadcastSpecification_step_iff_algorithm P e _ _).mpr
      (Gather.AlgorithmOverBroadcastSpecification.fail e id),
      Gather.broadcastSubstitutionRelation_corrupt hR id⟩

end GatherSteps

/-- **A visible transition matched by one step.** At related states, a visible transition of the
round over the gather instances over Bracha's broadcast is matched by one transition on the same
label of the round over the gather instances over the broadcast specification. -/
theorem broadcastSubstitution_visibleStep (P : Parameters) (r : ℕ) {s : RoundStateOverBracha P.n}
    {t : RoundStateOverBroadcastSpecification P.n} (hR : BroadcastSubstitutionRelation P s t)
    {l : Composition.ExtendedLabel P.n Empty} (hl : l ≠ Sum.inl Label.tau)
    {μ : PMF (RoundStateOverBracha P.n)} (hstep : (roundOverBracha P r).step s l μ)
    {x : RoundStateOverBracha P.n} (hx : x ∈ μ.support) :
    ∃ y, BroadcastSubstitutionRelation P x y ∧
      (roundOverBroadcastSpecification P r).step t l (PMF.pure y) := by
  obtain ⟨y, h1, h2, h3, hstepA⟩ := roundOverGathers_visibleStep_transfer
    (Gather.instanceOverBracha_isLTS P) (Gather.instanceOverBracha_isLTS P)
    (Gather.BroadcastSubstitutionRelation P) (Gather.BroadcastSubstitutionRelation P)
    (fun _ _ _ _ _ hR' h => gatherBroadcastSubstitution_call hR' h)
    (fun _ _ _ _ hR' h => gatherBroadcastSubstitution_fail hR' h)
    (fun _ _ _ _ hR' h => gatherBroadcastSubstitution_fail hR' h)
    hR.roundPrograms_eq hR.firstGatherRelation hR.secondGatherRelation hl hstep hx
  exact ⟨y, ⟨h1, h2, h3⟩, hstepA⟩

/-- **The first step at an untouched round.** From related states reached by a list of
broadcasts, a transition of the round on a label the round owns is matched by one transition on
the same label, the same round program's transition in both rounds. -/
theorem broadcastSubstitution_untouchedFirstStep (P : Parameters)
    (owns : Composition.ExtendedLabel P.n Empty → Option ℕ) (hOwnsSilent : owns Silent.τ = none)
    (actC : Composition.ExtendedLabel P.n Empty → RoundStateOverBracha P.n →
      RoundStateOverBracha P.n)
    (actA : Composition.ExtendedLabel P.n Empty → RoundStateOverBroadcastSpecification P.n →
      RoundStateOverBroadcastSpecification P.n)
    (initialC : RoundStateOverBracha P.n) (initialA : RoundStateOverBroadcastSpecification P.n) :
    ∀ (r : ℕ) (broadcasts : List (Composition.ExtendedLabel P.n Empty))
      (l : Composition.ExtendedLabel P.n Empty), owns l = some r →
      BroadcastSubstitutionRelation P (broadcasts.foldr actC initialC)
        (broadcasts.foldr actA initialA) →
      ∀ μ, (roundOverBracha P r).step (broadcasts.foldr actC initialC) l μ →
      ∀ x ∈ μ.support, ∃ y, BroadcastSubstitutionRelation P x y ∧
        ∃ ν, (roundOverBroadcastSpecification P r).step (broadcasts.foldr actA initialA) l ν ∧
          ∃ z ∈ ν.support, (roundOverBroadcastSpecification P r).weakLSilent z y := by
  intro r broadcasts l howns hR μ hstep x hx
  have hl : l ≠ Sum.inl Label.tau := by
    rintro rfl
    exact absurd (howns.symm.trans hOwnsSilent) (by simp)
  obtain ⟨y, hRxy, hstepA⟩ := broadcastSubstitution_visibleStep P r hR hl hstep hx
  exact ⟨y, hRxy, PMF.pure y, hstepA, y, (PMF.mem_support_pure_iff _ _).mpr rfl,
    System.weakLSilent_refl _ y⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.broadcastSubstitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms broadcastSubstitution

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverBracha_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundOverBracha_refines

/-- info: 'PLTS.ABA.GBCA.ByAFW.broadcastSubstitution_untouchedFirstStep' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms broadcastSubstitution_untouchedFirstStep

end GBCA.ByAFW
end ABA
end PLTS
