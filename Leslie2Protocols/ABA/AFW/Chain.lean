/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Round.LowSim
import Leslie2Protocols.ABA.Round.IdealSim
import Leslie2Protocols.ABA.Round.PairSim
import Leslie2Protocols.ABA.Results
import Leslie2Protocols.Framework.MapIdleSim

/-!
# The gather-based implementation chain

The graded-agreement specification has two verified implementations. The
ladder implementation (`ABA/ABDY/Ladder.lean`, deviation D18) enters the
protocol reading through `GSub.gbcaSide` and is replaced by the
specification family in `ABA/ABDY/Hybrid.lean`. The gather-based implementation
(`ABA/Round/Low.lean`) is carried to the same specification here, by the three
tier simulations of its own tower:

1. `GBCA.lowRefines` (`ABA/Round/LowSim.lean`) — the broadcast substitution:
   each Bracha instance replaced by its specification;
2. `GBCA.idealRefines` (`ABA/Round/IdealSim.lean`) — the gather substitution:
   each gather-over-BRB instance replaced by the gather specification;
3. `GBCA.pairRefines` (`ABA/Round/PairSim.lean`) — the counting simulation
   into `GBCA.specInst`.

Two readings are given, mirroring `ABA/Results.lean`.

**The round reading.** `GBCA.gatherImplRefines` composes the three tier
simulations probabilistically: the round-`r` gather-based implementation
refines the round-`r` specification. `GBCA.gatherRoundRefines` is its
soundness inclusion.

**The protocol-shaped reading.** Everything the gather-based chain builds at
protocol shape sits in the namespace `AFW`, after Attiya, Flam and Welch, so
each of its systems and headlines carries the name of its ladder-chain
counterpart: `AFW.composed` beside `composed`, `AFW.substitution` beside
`substitution`. The names below are read in that namespace.

Each tier instance is read over the extended alphabet along `GSub.gPull` —
the read-back that defines `GSub.liftedSpec` — and gathered into a ℕ-indexed
family with the corruption broadcast: `lowSide`, `idealSide` and `pairSide`
are the graded-agreement sides of three systems `composed`, `hybrid1` and
`hybrid2`, each built by the composed reading's own pipeline beside its other
three components. Between
consecutive systems the family substitution runs under the four congruences
(`parallel_right`, `abstract`, `relabel`, `abstract`), exactly as
`substSim` does for the ladder chain. The third stage lands on `hybrid P`
itself: from there the shared links `hybrid_spec` and `coreSim` carry both
implementation chains to the ABA specification. `substitution` is the
three-stage inclusion, `composed_refines` chains it with `hybrid_spec`,
`composed_safe` reads off Validity and Agreement, and `chainSimComposed`
composes the simulations themselves. `ABA/AFW/FlatSim.lean` carries these
one level lower, to the gather-based protocol as it runs.

The `#print axioms` blocks are the mechanical firewall: every headline is
pinned to the clean axiom list.
-/

namespace PLTS
namespace ABA

open Net Comp GSub

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
exactly as `GSub.liftedSpec` reads the specification: a delegating label
takes the tier's own row, every other extended label idles. The broadcast
corruption acts are the tiers' own `fail` successors, taken on the extended
`fail` label. -/

namespace AFW

/-- The gather-based implementation read over the extended alphabet. -/
noncomputable def liftedLow (P : Params) (r : ℕ) :
    System (GBCA.LowPairState P.n) (NLab P.n) :=
  (GBCA.lowPairInst P r).mapIdle (gPull P.n)

/-- The lifted tier is an LTS: the tier is, and reading it back adds only
Dirac self-loops. -/
theorem liftedLow_isLTS (P : Params) (r : ℕ) : (liftedLow P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.lowPairInst_isLTS P r)

/-- The GBCA-over-gather-over-BRB tier read over the extended alphabet. -/
noncomputable def liftedIdeal (P : Params) (r : ℕ) :
    System (GBCA.IdealState P.n) (NLab P.n) :=
  (GBCA.idealInst P r).mapIdle (gPull P.n)

/-- The lifted tier is an LTS. -/
theorem liftedIdeal_isLTS (P : Params) (r : ℕ) : (liftedIdeal P r).IsLTS :=
  System.mapIdle_isLTS _ (GBCA.idealInst_isLTS P r)

/-- The GBCA-over-gather tier read over the extended alphabet. -/
noncomputable def liftedPair (P : Params) (r : ℕ) :
    System (GBCA.PairState P.n) (NLab P.n) :=
  (GBCA.pairInst P r).mapIdle (gPull P.n)

/-- The lifted tier is an LTS. -/
theorem liftedPair_isLTS (P : Params) (r : ℕ) : (liftedPair P r).IsLTS :=
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
    ForwardSimulation (liftedLow P r) (liftedIdeal P r) (GBCA.LowPairRel P) :=
  ForwardSimulation.mapIdle (gPull P.n) (gPull_tau P.n)
    (fun _ h => gPull_eq_tau h) (GBCA.lowRefines P r)

/-- The gather substitution, read over the extended alphabet. -/
theorem liftedIdealSim (P : Params) (r : ℕ) :
    ForwardSimulation (liftedIdeal P r) (liftedPair P r) (GBCA.IdealRel P) :=
  ForwardSimulation.mapIdle (gPull P.n) (gPull_tau P.n)
    (fun _ h => gPull_eq_tau h) (GBCA.idealRefines P r)

/-- The counting simulation, read over the extended alphabet. -/
theorem liftedPairSim (P : Params) (r : ℕ) :
    ForwardSimulation (liftedPair P r) (liftedSpec P r) (GBCA.PairRel P) :=
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


/-! ## The graded-agreement sides

Three ℕ-indexed families over the shape of `GSub.gbcaSide` and `specSide`: a
round-tagged label moves its round alone, `τ` moves one round, `fail` is the
broadcast that keeps every round's copy of the corrupted set in lockstep, and
everything else idles. -/

/-- The gather-based graded-agreement side: the family of lifted round
implementations. -/
noncomputable def lowSide (P : Params) :
    System (ℕ → GBCA.LowPairState P.n) (NLab P.n) :=
  System.family (liftedLow P) GSub.gOwns GSub.isFailN (gActLow P)

/-- The side is an LTS: every round's tier is. -/
theorem lowSide_isLTS (P : Params) : (lowSide P).IsLTS :=
  System.family_isLTS (liftedLow_isLTS P) _ _ _

/-- The GBCA-over-gather-over-BRB side. -/
noncomputable def idealSide (P : Params) :
    System (ℕ → GBCA.IdealState P.n) (NLab P.n) :=
  System.family (liftedIdeal P) GSub.gOwns GSub.isFailN (gActIdeal P)

/-- The side is an LTS. -/
theorem idealSide_isLTS (P : Params) : (idealSide P).IsLTS :=
  System.family_isLTS (liftedIdeal_isLTS P) _ _ _

/-- The GBCA-over-gather side. -/
noncomputable def pairSide (P : Params) :
    System (ℕ → GBCA.PairState P.n) (NLab P.n) :=
  System.family (liftedPair P) GSub.gOwns GSub.isFailN (gActPair P)

/-- The side is an LTS. -/
theorem pairSide_isLTS (P : Params) : (pairSide P).IsLTS :=
  System.family_isLTS (liftedPair_isLTS P) _ _ _

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
theorem famLowSim (P : Params) :
    ForwardSimulation (lowSide P) (idealSide P) (RlowAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (gActLow P)
    (gActIdeal P) (liftedLowSim P) (lowSim_failAct P)

/-- The family substitution of the second stage. -/
theorem famIdealSim (P : Params) :
    ForwardSimulation (idealSide P) (pairSide P) (RidealAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (gActIdeal P)
    (gActPair P) (liftedIdealSim P) (idealSim_failAct P)

/-- The family substitution of the third stage, into the specification
side. -/
theorem famPairSim (P : Params) :
    ForwardSimulation (pairSide P) (specSide P) (RpairAll P) :=
  ForwardSimulation.family GSub.gOwns GSub.isFailN (gActPair P)
    (GSub.gActSpec P) (liftedPairSim P) (pairSim_failAct P)

/-- The first family substitution, probabilistically. -/
theorem famLowSimProb (P : Params) :
    ProbabilisticForwardSimulation (lowSide P) (idealSide P)
      (diracRel (RlowAll P)) :=
  ForwardSimulation.toProbabilistic (lowSide_isLTS P) (idealSide_isLTS P)
    (fun _ => GBCA.lowPairRel_init) (famLowSim P)

/-- The second family substitution, probabilistically. -/
theorem famIdealSimProb (P : Params) :
    ProbabilisticForwardSimulation (idealSide P) (pairSide P)
      (diracRel (RidealAll P)) :=
  ForwardSimulation.toProbabilistic (idealSide_isLTS P) (pairSide_isLTS P)
    (fun _ => GBCA.idealRel_init) (famIdealSim P)

/-- The third family substitution, probabilistically. -/
theorem famPairSimProb (P : Params) :
    ProbabilisticForwardSimulation (pairSide P) (specSide P)
      (diracRel (RpairAll P)) :=
  ForwardSimulation.toProbabilistic (pairSide_isLTS P) (specSide_isLTS P)
    (fun _ => GBCA.pairRel_init) (famPairSim P)

/-! ## The protocol-shaped systems

The composed reading's pipeline — the graded-agreement side beside the round
loops, the ABA-side network and the coin oracle, the rendezvous alphabet
hidden, the result read back over `Lab n`, the sub-protocol API hidden —
taken at each tier of the gather-based tower. -/

/-- The state of the gather-based composed reading. -/
abbrev ComposedState (P : Params) : Type :=
  (ℕ → GBCA.LowPairState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the middle tier. -/
abbrev Hybrid1State (P : Params) : Type :=
  (ℕ → GBCA.IdealState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- The state at the upper tier. -/
abbrev Hybrid2State (P : Params) : Type :=
  (ℕ → GBCA.PairState P.n) ×
    ((∀ _ : Fin P.n, CoreRec P.n) × (ANetState P.n × (ℕ → WCC.SpecState P.n)))

/-- **The gather-based composed reading**: the gather-based graded-agreement
side beside the composed reading's other three components, through the two
hiding frames. -/
noncomputable def composed (P : Params) : System (ComposedState P) (Lab P.n) :=
  ((((lowSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The middle tier at the protocol shape. -/
noncomputable def hybrid1 (P : Params) : System (Hybrid1State P) (Lab P.n) :=
  ((((idealSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The upper tier at the protocol shape. -/
noncomputable def hybrid2 (P : Params) : System (Hybrid2State P) (Lab P.n) :=
  ((((pairSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-! ### The three-stage substitution -/

/-- The first stage at the protocol shape: the four congruences applied to the
first family substitution under the composed reading's own context. -/
noncomputable def substSimLow (P : Params) :
    ProbabilisticForwardSimulation (composed P) (hybrid1 P)
      (parallelRel (diracRel (RlowAll P))) :=
  ((((famLowSimProb P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The second stage at the protocol shape. -/
noncomputable def substSimIdeal (P : Params) :
    ProbabilisticForwardSimulation (hybrid1 P) (hybrid2 P)
      (parallelRel (diracRel (RidealAll P))) :=
  ((((famIdealSimProb P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- The third stage at the protocol shape, into the protocol-shaped
specification `hybrid P` — the point where the gather-based chain meets the
ladder chain. -/
noncomputable def substSimPair (P : Params) :
    ProbabilisticForwardSimulation (hybrid2 P) (hybrid P)
      (parallelRel (diracRel (RpairAll P))) :=
  ((((famPairSimProb P).parallel_right
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))).abstract
        (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)

/-- **The gather-based substitution simulation**: the three stages joined by
Result 2. -/
noncomputable def substSim (P : Params) :
    ProbabilisticForwardSimulation (composed P) (hybrid P)
      (compRel (parallelRel (diracRel (RlowAll P)))
        (compRel (parallelRel (diracRel (RidealAll P)))
          (parallelRel (diracRel (RpairAll P))))) :=
  (substSimLow P).trans ((substSimIdeal P).trans (substSimPair P))

/-- **The gather-based substitution inclusion**: every trace distribution
achievable by the gather-based composed reading is achievable by the
protocol-shaped specification. The three stage inclusions are chained by
`Set.Subset.trans`; the inclusion never invokes transitivity of
simulation. -/
theorem substitution (P : Params) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (hybrid P) :=
  Set.Subset.trans (substSimLow P).achievableTraceDists_subset
    (Set.Subset.trans (substSimIdeal P).achievableTraceDists_subset
      (substSimPair P).achievableTraceDists_subset)

/-! ## The headlines -/

/-- **Trace-distribution refinement of the gather-based composed reading**:
every trace distribution achievable by it is achievable by the ABA
specification. The substitution gives the first inclusion, the shared core
simulation the second. -/
theorem composed_refines (P : Params) :
    achievableTraceDists (composed P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (substitution P) (hybrid_spec P)

/-- **Safety of the gather-based reading**: every positive-probability trace
of every achievable trace distribution of the gather-based composed reading
satisfies Validity and Agreement. -/
theorem composed_safe (P : Params) :
    ∀ D ∈ achievableTraceDists (composed P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (composed_refines P) (spec_safe P)

/-- **The composed gather-based simulation** `composed ⊑ ABA.spec`: the
three-stage substitution joined with the shared core simulation by
Result 2. -/
noncomputable def chainSimComposed (P : Params) :
    ProbabilisticForwardSimulation (composed P) (spec P)
      (compRel
        (compRel (parallelRel (diracRel (RlowAll P)))
          (compRel (parallelRel (diracRel (RidealAll P)))
            (parallelRel (diracRel (RpairAll P)))))
        (coreRel P)) :=
  (substSim P).trans (coreSim P)

/-! ### Mechanical axiom firewall -/

/-- info: 'PLTS.ABA.GBCA.gatherImplRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GBCA.gatherImplRefines

/-- info: 'PLTS.ABA.GBCA.gatherRoundRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GBCA.gatherRoundRefines

/-- info: 'PLTS.ABA.AFW.substitution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms substitution

/-- info: 'PLTS.ABA.AFW.composed_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composed_refines

/-- info: 'PLTS.ABA.AFW.composed_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composed_safe

/-- info: 'PLTS.ABA.AFW.chainSimComposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainSimComposed

end AFW

end ABA
end PLTS
