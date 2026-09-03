/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCALowSim
import Leslie2Protocols.ABA.GBCAIdealSim
import Leslie2Protocols.ABA.GBCAPairSim
import Leslie2Protocols.ABA.Results
import Leslie2Protocols.Framework.MapIdleSim

/-!
# The gather-based implementation chain

The graded-agreement specification has two verified implementations. The
ladder implementation (`ABA/GBCAImpl.lean`, deviation D18) enters the
protocol reading through `GSub.gbcaSide` and is replaced by the
specification family in `ABA/Hybrid.lean`. The gather-based implementation
(`ABA/GBCALow.lean`) is carried to the same specification here, by the three
tier simulations of its own tower:

1. `GBCA.lowRefines` (`ABA/GBCALowSim.lean`) — the broadcast substitution:
   each Bracha instance replaced by its specification;
2. `GBCA.idealRefines` (`ABA/GBCAIdealSim.lean`) — the gather substitution:
   each gather-over-BRB instance replaced by the gather specification;
3. `GBCA.pairRefines` (`ABA/GBCAPairSim.lean`) — the counting simulation
   into `GBCA.specInst`.

Two readings are given, mirroring `ABA/Results.lean`.

**The round reading.** `GBCA.gatherImplRefines` composes the three tier
simulations probabilistically: the round-`r` gather-based implementation
refines the round-`r` specification. `GBCA.gatherRoundRefines` is its
soundness inclusion.

**The protocol-shaped reading.** Each tier instance is read over the extended
alphabet along `GSub.gPull` — the read-back that defines `GSub.liftedSpecG` —
and gathered into a ℕ-indexed family with the corruption broadcast:
`lowSideG`, `idealSideG` and `pairSideG` are the graded-agreement sides of
three systems `composedG`, `hybridG1` and `hybridG2`, each built by the
composed reading's own pipeline beside its other three components. Between
consecutive systems the family substitution runs under the four congruences
(`parallel_right`, `abstract`, `relabel`, `abstract`), exactly as
`substSim` does for the ladder chain. The third stage lands on `hybrid P`
itself: from there the shared links `hybrid_spec` and `coreSim` carry both
implementation chains to the ABA specification. `substitutionG` is the
three-stage inclusion, `refinesG` chains it with `hybrid_spec`,
`composedG_safe` reads off Validity and Agreement, and `chainSimG` composes
the simulations themselves.

The `#print axioms` blocks are the mechanical firewall: every headline is
pinned to the clean axiom list.
-/

namespace PLTS
namespace ABA

open Net Comp

/-! ## The round reading -/

namespace GBCA

/-- **The gather-based implementation refines the specification**, round by
round: the three tier simulations, each taken probabilistically, joined by
Result 2 (`ProbabilisticForwardSimulation.trans`). -/
theorem gatherImplRefines (P : Params) (r : ℕ) :
    ProbabilisticForwardSimulation (lowPairInst P r) (specInst P r)
      (compRel (diracRel (LowPairRel P))
        (compRel (diracRel (IdealRel P)) (diracRel (PairRel P)))) :=
  (ForwardSimulation.toProbabilistic (lowPairInst_isLTS P r) (idealInst_isLTS P r)
      lowPairRel_init (lowRefines P r)).trans
    ((ForwardSimulation.toProbabilistic (idealInst_isLTS P r) (pairInst_isLTS P r)
        idealRel_init (idealRefines P r)).trans
      (ForwardSimulation.toProbabilistic (pairInst_isLTS P r) (specInst_isLTS P r)
        pairRel_init (pairRefines P r)))

/-- The soundness inclusion of the round reading: every trace distribution
achievable by the round-`r` gather-based implementation is achievable by the
round-`r` specification. -/
theorem gatherRoundRefines (P : Params) (r : ℕ) :
    achievableTraceDists (lowPairInst P r) ⊆ achievableTraceDists (specInst P r) :=
  (gatherImplRefines P r).achievableTraceDists_subset

end GBCA

/-! ## The lifted tiers

Each tier instance is read over the extended alphabet along `GSub.gPull`,
exactly as `GSub.liftedSpecG` reads the specification: a delegating label
takes the tier's own row, every other extended label idles. The broadcast
corruption acts are the tiers' own `fail` successors, taken on the extended
`fail` label. -/

namespace GSub

/-- The gather-based implementation read over the extended alphabet. -/
noncomputable def liftedLowG (P : Params) (r : ℕ) :
    System (GBCA.LowPairState P.n) (NLab P.n) :=
  (GBCA.lowPairInst P r).mapIdle (gPull P.n)

/-- The lifted tier is an LTS: the tier is, and reading it back adds only
Dirac self-loops. -/
theorem liftedLowG_isLTS (P : Params) (r : ℕ) : (liftedLowG P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.lowPairInst_isLTS P r)

/-- The GBCA-over-gather-over-BRB tier read over the extended alphabet. -/
noncomputable def liftedIdealG (P : Params) (r : ℕ) :
    System (GBCA.IdealState P.n) (NLab P.n) :=
  (GBCA.idealInst P r).mapIdle (gPull P.n)

/-- The lifted tier is an LTS. -/
theorem liftedIdealG_isLTS (P : Params) (r : ℕ) : (liftedIdealG P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.idealInst_isLTS P r)

/-- The GBCA-over-gather tier read over the extended alphabet. -/
noncomputable def liftedPairG (P : Params) (r : ℕ) :
    System (GBCA.PairState P.n) (NLab P.n) :=
  (GBCA.pairInst P r).mapIdle (gPull P.n)

/-- The lifted tier is an LTS. -/
theorem liftedPairG_isLTS (P : Params) (r : ℕ) : (liftedPairG P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.pairInst_isLTS P r)

/-! ### The broadcast corruption acts -/

/-- The broadcast corruption act on a gather-based implementation state: both
gather-over-Bracha instances record it at once (D1). -/
def gActLow (P : Params) : NLab P.n → GBCA.LowPairState P.n → GBCA.LowPairState P.n
  | Sum.inl (.fail k), s => (s.1.corruptAll P k, s.2.corruptAll P k)
  | _, s => s

/-- The broadcast corruption act on a GBCA-over-gather-over-BRB state. -/
def gActIdeal (P : Params) : NLab P.n → GBCA.IdealState P.n → GBCA.IdealState P.n
  | Sum.inl (.fail k), s => (s.1.corruptAll P k, s.2.corruptAll P k)
  | _, s => s

/-- The broadcast corruption act on a GBCA-over-gather state. -/
def gActPair (P : Params) : NLab P.n → GBCA.PairState P.n → GBCA.PairState P.n
  | Sum.inl (.fail k), s => (s.1.corrupt P k, s.2.corrupt P k)
  | _, s => s

/-! ### The lifted tier simulations

Forward simulation is a congruence for the read-back
(`ForwardSimulation.mapIdle`, `Framework/MapIdleSim.lean`); the τ round-trip
of `gPull` is `gPull_tau` and `gPull_eq_tau`. -/

/-- The broadcast substitution, read over the extended alphabet. -/
theorem liftedLowSim (P : Params) (r : ℕ) :
    ForwardSimulation (liftedLowG P r) (liftedIdealG P r) (GBCA.LowPairRel P) :=
  ForwardSimulation.mapIdle (gPull P.n) (gPull_tau P.n)
    (fun _ h => gPull_eq_tau h) (GBCA.lowRefines P r)

/-- The gather substitution, read over the extended alphabet. -/
theorem liftedIdealSim (P : Params) (r : ℕ) :
    ForwardSimulation (liftedIdealG P r) (liftedPairG P r) (GBCA.IdealRel P) :=
  ForwardSimulation.mapIdle (gPull P.n) (gPull_tau P.n)
    (fun _ h => gPull_eq_tau h) (GBCA.idealRefines P r)

/-- The counting simulation, read over the extended alphabet. -/
theorem liftedPairSim (P : Params) (r : ℕ) :
    ForwardSimulation (liftedPairG P r) (liftedSpecG P r) (GBCA.PairRel P) :=
  ForwardSimulation.mapIdle (gPull P.n) (gPull_tau P.n)
    (fun _ h => gPull_eq_tau h) (GBCA.pairRefines P r)

/-! ### Broadcast compatibility

The three relations survive the corruption broadcast: the tiers' own
lockstep-corruption statements, taken on the extended `fail` label. -/

/-- Corruption preserves the broadcast substitution relation. -/
theorem lowSim_failAct (P : Params) :
    ∀ l : NLab P.n, isFailN l → ∀ (_ : ℕ) (x : GBCA.LowPairState P.n)
      (y : GBCA.IdealState P.n), GBCA.LowPairRel P x y →
      GBCA.LowPairRel P (gActLow P l x) (gActIdeal P l y) := by
  rintro l hl _ x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.lowPairRel_corrupt hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-- Corruption preserves the gather substitution relation. -/
theorem idealSim_failAct (P : Params) :
    ∀ l : NLab P.n, isFailN l → ∀ (_ : ℕ) (x : GBCA.IdealState P.n)
      (y : GBCA.PairState P.n), GBCA.IdealRel P x y →
      GBCA.IdealRel P (gActIdeal P l x) (gActPair P l y) := by
  rintro l hl _ x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.idealRel_corrupt hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

/-- Corruption preserves the counting relation. -/
theorem pairSim_failAct (P : Params) :
    ∀ l : NLab P.n, isFailN l → ∀ (_ : ℕ) (x : GBCA.PairState P.n)
      (y : GBCA.SpecState P.n), GBCA.PairRel P x y →
      GBCA.PairRel P (gActPair P l x) (gActSpec P l y) := by
  rintro l hl r x y hR
  cases l with
  | inr e => cases e <;> exact hl.elim
  | inl l₀ =>
    cases l₀ with
    | fail k => exact GBCA.pairRel_corrupt (r := r) hR k
    | tau => exact hl.elim
    | callABA id b => exact hl.elim
    | retABA id b => exact hl.elim
    | callG r' id b => exact hl.elim
    | retG r' id out => exact hl.elim
    | callW r' id => exact hl.elim
    | retW r' id b => exact hl.elim

end GSub

/-! ## The graded-agreement sides

Three ℕ-indexed families over the shape of `GSub.gbcaSide` and `specSide`: a
round-tagged label moves its round alone, `τ` moves one round, `fail` is the
broadcast that keeps every round's copy of the corrupted set in lockstep, and
everything else idles. -/

/-- The gather-based graded-agreement side: the family of lifted round
implementations. -/
noncomputable def lowSideG (P : Params) :
    System (ℕ → GBCA.LowPairState P.n) (NLab P.n) :=
  System.family (GSub.liftedLowG P) GSub.gOwns GSub.isFailN (GSub.gActLow P)

/-- The side is an LTS: every round's tier is. -/
theorem lowSideG_isLTS (P : Params) : (lowSideG P).IsLTS :=
  System.family_isLTS (GSub.liftedLowG_isLTS P) _ _ _

/-- The GBCA-over-gather-over-BRB side. -/
noncomputable def idealSideG (P : Params) :
    System (ℕ → GBCA.IdealState P.n) (NLab P.n) :=
  System.family (GSub.liftedIdealG P) GSub.gOwns GSub.isFailN (GSub.gActIdeal P)

/-- The side is an LTS. -/
theorem idealSideG_isLTS (P : Params) : (idealSideG P).IsLTS :=
  System.family_isLTS (GSub.liftedIdealG_isLTS P) _ _ _

/-- The GBCA-over-gather side. -/
noncomputable def pairSideG (P : Params) :
    System (ℕ → GBCA.PairState P.n) (NLab P.n) :=
  System.family (GSub.liftedPairG P) GSub.gOwns GSub.isFailN (GSub.gActPair P)

/-- The side is an LTS. -/
theorem pairSideG_isLTS (P : Params) : (pairSideG P).IsLTS :=
  System.family_isLTS (GSub.liftedPairG_isLTS P) _ _ _

/-! ### The family substitutions -/

/-- The pointwise round relation of the broadcast substitution. -/
def RlowAll (P : Params) (s : ℕ → GBCA.LowPairState P.n)
    (t : ℕ → GBCA.IdealState P.n) : Prop :=
  ∀ r, GBCA.LowPairRel P (s r) (t r)

/-- The pointwise round relation of the gather substitution. -/
def RidealAll (P : Params) (s : ℕ → GBCA.IdealState P.n)
    (t : ℕ → GBCA.PairState P.n) : Prop :=
  ∀ r, GBCA.IdealRel P (s r) (t r)

/-- The pointwise round relation of the counting simulation. -/
def RpairAll (P : Params) (s : ℕ → GBCA.PairState P.n)
    (t : ℕ → GBCA.SpecState P.n) : Prop :=
  ∀ r, GBCA.PairRel P (s r) (t r)

/-- The family substitution of the first stage, round by round. -/
theorem famLowSimG (P : Params) :
    ForwardSimulation (lowSideG P) (idealSideG P) (RlowAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (GSub.gActLow P)
    (GSub.gActIdeal P) (GSub.liftedLowSim P) (GSub.lowSim_failAct P)

/-- The family substitution of the second stage. -/
theorem famIdealSimG (P : Params) :
    ForwardSimulation (idealSideG P) (pairSideG P) (RidealAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (GSub.gActIdeal P)
    (GSub.gActPair P) (GSub.liftedIdealSim P) (GSub.idealSim_failAct P)

/-- The family substitution of the third stage, into the specification
side. -/
theorem famPairSimG (P : Params) :
    ForwardSimulation (pairSideG P) (specSide P) (RpairAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (GSub.gActPair P)
    (GSub.gActSpec P) (GSub.liftedPairSim P) (GSub.pairSim_failAct P)

/-- The first family substitution, probabilistically. -/
theorem famLowSimProbG (P : Params) :
    ProbabilisticForwardSimulation (lowSideG P) (idealSideG P)
      (diracRel (RlowAll P)) :=
  ForwardSimulation.toProbabilistic (lowSideG_isLTS P) (idealSideG_isLTS P)
    (fun _ => GBCA.lowPairRel_init) (famLowSimG P)

/-- The second family substitution, probabilistically. -/
theorem famIdealSimProbG (P : Params) :
    ProbabilisticForwardSimulation (idealSideG P) (pairSideG P)
      (diracRel (RidealAll P)) :=
  ForwardSimulation.toProbabilistic (idealSideG_isLTS P) (pairSideG_isLTS P)
    (fun _ => GBCA.idealRel_init) (famIdealSimG P)

/-- The third family substitution, probabilistically. -/
theorem famPairSimProbG (P : Params) :
    ProbabilisticForwardSimulation (pairSideG P) (specSide P)
      (diracRel (RpairAll P)) :=
  ForwardSimulation.toProbabilistic (pairSideG_isLTS P) (specSide_isLTS P)
    (fun _ => GBCA.pairRel_init) (famPairSimG P)

/-! ## The protocol-shaped systems

The composed reading's pipeline — the graded-agreement side beside the round
loops, the ABA-side network and the coin oracle, the rendezvous alphabet
hidden, the result read back over `Lab n`, the sub-protocol API hidden —
taken at each tier of the gather-based tower. -/

/-- The state of the gather-based composed reading. -/
abbrev ComposedGState (P : Params) : Type :=
  (ℕ → GBCA.LowPairState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the middle tier. -/
abbrev HybridG1State (P : Params) : Type :=
  (ℕ → GBCA.IdealState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the upper tier. -/
abbrev HybridG2State (P : Params) : Type :=
  (ℕ → GBCA.PairState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- **The gather-based composed reading**: the gather-based graded-agreement
side beside the composed reading's other three components, through the two
hiding frames. -/
noncomputable def composedG (P : Params) : System (ComposedGState P) (Lab P.n) :=
  ((((lowSideG P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The middle tier at the protocol shape. -/
noncomputable def hybridG1 (P : Params) : System (HybridG1State P) (Lab P.n) :=
  ((((idealSideG P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The upper tier at the protocol shape. -/
noncomputable def hybridG2 (P : Params) : System (HybridG2State P) (Lab P.n) :=
  ((((pairSideG P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-! ### The three-stage substitution -/

/-- The first stage at the protocol shape: the four congruences applied to the
first family substitution under the composed reading's own context. -/
noncomputable def substSimLowG (P : Params) :
    ProbabilisticForwardSimulation (composedG P) (hybridG1 P)
      (parallelRel (diracRel (RlowAll P))) :=
  ((((famLowSimProbG P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The second stage at the protocol shape. -/
noncomputable def substSimIdealG (P : Params) :
    ProbabilisticForwardSimulation (hybridG1 P) (hybridG2 P)
      (parallelRel (diracRel (RidealAll P))) :=
  ((((famIdealSimProbG P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The third stage at the protocol shape, into the protocol-shaped
specification `hybrid P` — the point where the gather-based chain meets the
ladder chain. -/
noncomputable def substSimPairG (P : Params) :
    ProbabilisticForwardSimulation (hybridG2 P) (hybrid P)
      (parallelRel (diracRel (RpairAll P))) :=
  ((((famPairSimProbG P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- **The gather-based substitution simulation**: the three stages joined by
Result 2. -/
noncomputable def substSimG (P : Params) :
    ProbabilisticForwardSimulation (composedG P) (hybrid P)
      (compRel (parallelRel (diracRel (RlowAll P)))
        (compRel (parallelRel (diracRel (RidealAll P)))
          (parallelRel (diracRel (RpairAll P))))) :=
  (substSimLowG P).trans ((substSimIdealG P).trans (substSimPairG P))

/-- **The gather-based substitution inclusion**: every trace distribution
achievable by the gather-based composed reading is achievable by the
protocol-shaped specification. The three stage inclusions are chained by
`Set.Subset.trans`; the inclusion never invokes transitivity of
simulation. -/
theorem substitutionG (P : Params) :
    achievableTraceDists (composedG P) ⊆ achievableTraceDists (hybrid P) :=
  Set.Subset.trans (substSimLowG P).achievableTraceDists_subset
    (Set.Subset.trans (substSimIdealG P).achievableTraceDists_subset
      (substSimPairG P).achievableTraceDists_subset)

/-! ## The headlines -/

/-- **Trace-distribution refinement of the gather-based reading**: every trace
distribution achievable by the gather-based composed reading is achievable by
the ABA specification. The substitution gives the first inclusion, the shared
core simulation the second. -/
theorem refinesG (P : Params) :
    achievableTraceDists (composedG P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (substitutionG P) (hybrid_spec P)

/-- **Safety of the gather-based reading**: every positive-probability trace
of every achievable trace distribution of the gather-based composed reading
satisfies Validity and Agreement. -/
theorem composedG_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (composedG P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (refinesG P) (spec_safe P)

/-- **The composed gather-based simulation** `composedG ⊑ ABA.spec`: the
three-stage substitution joined with the shared core simulation by
Result 2. -/
noncomputable def chainSimG (P : Params) :
    ProbabilisticForwardSimulation (composedG P) (spec P)
      (compRel
        (compRel (parallelRel (diracRel (RlowAll P)))
          (compRel (parallelRel (diracRel (RidealAll P)))
            (parallelRel (diracRel (RpairAll P)))))
        (coreRel P)) :=
  (substSimG P).trans (coreSim P)

/-! ### Mechanical axiom firewall -/

/-- info: 'PLTS.ABA.GBCA.gatherImplRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GBCA.gatherImplRefines

/-- info: 'PLTS.ABA.GBCA.gatherRoundRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GBCA.gatherRoundRefines

/-- info: 'PLTS.ABA.substitutionG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substitutionG

/-- info: 'PLTS.ABA.refinesG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesG

/-- info: 'PLTS.ABA.composedG_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composedG_safe

/-- info: 'PLTS.ABA.chainSimG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainSimG

end ABA
end PLTS
