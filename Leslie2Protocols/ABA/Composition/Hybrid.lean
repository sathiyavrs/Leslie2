/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.Composition.InputEnabledness
import Leslie2Protocols.ABA.GBCA.ABDY.RefinesSpecification
import Leslie2Protocols.ABA.GBCA.ABDY.RoundFamilyOwnedLabels
import Leslie2.Results

/-!
# The protocol-shaped specification

`hybrid` is the specification of the ABA protocol read at the protocol's own shape. Four
components run in parallel over `Composition.ExtendedLabel n M`, where `M` is the type of the
messages a graded-agreement round exchanges: the ℕ-indexed family of round specifications
`gbcaSpecificationFamily`, the `n` round loops, the ABA network and the lifted common coin.
`hybrid P M` is stated for every such type. ABDY22's chain takes `GBCA.ByABDY.Message` for `M`
(`ABA/ABDY/Substitution.lean`); the gather-based chain takes `Empty`, so the round multicast and
the round delivery name no label there (`ABA/AFW/Substitution.lean`). The synchronisation labels
are hidden, the result is read back over `Label n`, and the sub-protocol API is hidden. The last
three components and the alphabet are `ABA/Composition/Components.lean`.

The round-`r` member of `gbcaSpecificationFamily` is that round's graded-agreement specification
read over the protocol extended alphabet along `GBCA.specificationLabelMap`
(`GBCA/SpecificationOverRoundAlphabet.lean`). The family's state is an `InstanceFamilyState`: the
corruptions applied and the round specifications the family has touched, every other round reading
the initial specification under the recorded corruptions. A label a round owns, a call, a
corrupted process's call, a return or an announcement of that round, moves that round alone; `τ`
moves one round of the map; `fail` is the broadcast that keeps every round's copy of the corrupted
set together; every other label idles. The common coin is a family of the same shape over
`Label n`. The announcement `boundG r b` is a self-loop of every component: the family's round `r`
announces the bit it leaves not excluded, and the round loops, the ABA network and the coin idle
(D29).

Each component takes every one of its inputs at every state, and no two components share an
output (`gbcaSpecificationFamily_inputEnabled`, `composedComponents_compatible`; the simulations
paper, Assumption 1 and Definition 2).

## What this file supplies

`hybrid` and its transitions. The builders assemble a transition of the composite out of
transitions of its components (`gbcaSpecificationFamily_owned`, `gbcaSpecificationFamily_idle`,
`gbcaSpecificationFamily_tau`, `gbcaSpecificationFamily_fail`, `gbcaSpecificationFamily_boundG`,
`hybridExtended_visible_step`, `hybridExtended_boundG`, `hybridExtended_tau_specification`,
`hybridExtended_tau_coin`, `hybrid_synchronisation`, `hybrid_hidden`, `hybrid_visible`). The
common coin's own transitions over the shared alphabet are `wccFamily_owned` and `wccFamily_fail`
here, and `wccFamily_idle` and the resolution `wccFamily_tau` in
`ABA/Implementation/Alphabet.lean`. The lemmas named `…_cases` decompose a composite transition
into the transitions its four components contributed. A labelled transition reaches `hybrid`
through the two hidings in one of three ways: a synchronisation label and a sub-protocol API label
are both hidden to `τ`, and every remaining label is hidden by neither hiding.

`hybrid` is where the two chains of `ABA/Results.lean` meet.
`ABA/ABDY/Substitution.lean` carries the composed system of ABDY22's protocol
to it in one stage, and `ABA/AFW/Substitution.lean` carries `AFW.composed`, the composed
system of the gather-based protocol, in three stages. The simulation of
`ABA/HybridRefinesSpecification/Simulation.lean` runs from `hybrid` on this vocabulary, the
non-vacuity witnesses of `ABA/HybridRefinesSpecification/NonVacuity.lean` are built with it, and
`ABA/Results.lean` derives the protocols' Validity and Agreement guarantee through
`safety_transfer`.
-/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ## The protocol-shaped specification family

`gbcaSpecificationFamily` is the graded-agreement component: the family of round specifications,
read over the protocol alphabet. It stands where the composed system of
`ABA/ABDY/Composition.lean` carries the family of round instances, and the
other three components are the same in both systems. -/

/-- The state of `gbcaSpecificationFamily`: the corruptions the family has applied and the round
specifications it has touched. `M` is the type of the messages a graded-agreement round
exchanges. -/
abbrev GBCASpecificationFamilyState (P : Parameters) (M : Type) : Type :=
  InstanceFamilyState (GBCA.SpecState.initial P.n)
    (GBCA.ByABDY.specificationCorruptionAct (M := M) P)

/-- **The specification family of the protocol**: the ℕ-indexed family of round specifications,
read over the protocol extended alphabet along `GBCA.specificationLabelMap`. A label a round owns
moves that round alone, `τ` moves one round of the map, and `fail` is the broadcast that keeps
every round's copy of the corrupted set together. -/
noncomputable def gbcaSpecificationFamily (P : Parameters) (M : Type) [DecidableEq M] :
    System (GBCASpecificationFamilyState P M) (ExtendedLabel P.n M) :=
  System.family (GBCA.specificationOverRoundAlphabet P M) GBCA.ByABDY.roundOwnsLabel
    GBCA.ByABDY.isFailLabel (GBCA.ByABDY.specificationCorruptionAct P)
    (GBCA.SpecState.initial P.n)

@[simp] theorem gbcaSpecificationFamily_init (P : Parameters) (M : Type) [DecidableEq M] :
    (gbcaSpecificationFamily P M).init = InstanceFamilyState.initial := rfl

/-- The family starts from the initial specification at every round. -/
theorem gbcaSpecificationFamily_init_apply (P : Parameters) (M : Type) [DecidableEq M] (r : ℕ) :
    (gbcaSpecificationFamily P M).init r = GBCA.SpecState.initial P.n := rfl

/-- The specification family is an LTS: every round's specification is. -/
theorem gbcaSpecificationFamily_isLTS (P : Parameters) (M : Type) [DecidableEq M] :
    (gbcaSpecificationFamily P M).IsLTS :=
  System.family_isLTS (GBCA.specificationOverRoundAlphabet_isLTS P M) _ _ _ _

/-- The state of the protocol-shaped specification: the round
specifications beside the round loops, the ABA network and the common coin. -/
abbrev HybridState (P : Parameters) (M : Type) : Type :=
  GBCASpecificationFamilyState P M ×
    ((∀ _ : Fin P.n, RoundLoopVariables P.n) ×
      (ABANetworkState P.n × InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)))

/-- The four components in parallel, over the extended alphabet: the context term of
`ABDY.composedExtended` (`ABA/ABDY/Composition.lean`) over the
specification family. -/
noncomputable def hybridExtended (P : Parameters) (M : Type) [DecidableEq M] :
    System (HybridState P M) (ExtendedLabel P.n M) :=
  (gbcaSpecificationFamily P M).parallel
    ((System.synchronisedProduct (roundLoopProgram P M)).parallel ((ABANetwork P M).parallel
      (coinOverRoundAlphabet P M)))

/-- **The protocol-shaped specification**: the synchronisation labels hidden,
the result read back over `Label n`, the sub-protocol API hidden. The pipeline is that of
`ABDY.composed` (`ABA/ABDY/Composition.lean`), component for component. -/
noncomputable def hybrid (P : Parameters) (M : Type) [DecidableEq M] :
    System (HybridState P M) (Label P.n) :=
  (((hybridExtended P M).abstract (networkEventLabels P.n)).relabel).abstract
    (Label.hiddenAPI P.n)

/-! ### Inputs and outputs

The four components of `hybridExtended` are the `n` round loops, the ABA network, the round
family and the common coin. Their label sets are `roundLoopInputOutputLabels`,
`abaNetworkInputOutputLabels`, `roundFamilyInputOutputLabels`
(`ABA/Composition/InputEnabledness.lean`) and `coinInputOutputLabels`
(`ABA/Implementation/InputEnabledness.lean`), and `composedComponents_compatible` states that
their outputs are pairwise disjoint. -/

/-- **The specification family is input-enabled** on every non-silent label other than a return
and an announcement. A call and a corrupted process's call of round `r` are taken by the
specification of round `r` at every state of it
(`GBCA.specificationOverRoundAlphabet_inputEnabled`), and every label no round owns by the
broadcast or by the idle transition (`System.InputEnabled.family`). This set is all that
`System.InputEnabled.family` gives from the rounds' input-enabledness: the returns and the
announcements are the family's outputs. -/
theorem gbcaSpecificationFamily_inputEnabled (P : Parameters) (M : Type) [DecidableEq M] :
    (gbcaSpecificationFamily P M).InputEnabled (roundFamilyInputOutputLabels P M).inputLabels := by
  refine (System.InputEnabled.family (GBCA.specificationOverRoundAlphabet_inputEnabled P M)
    GBCA.ByABDY.roundOwnsLabel GBCA.ByABDY.isFailLabel (GBCA.ByABDY.specificationCorruptionAct P)
    (GBCA.SpecState.initial P.n)).mono ?_
  rintro l ⟨hτ, hret, hbound⟩
  rcases l with (_ | ⟨id, b⟩ | ⟨id, b⟩ | ⟨r, id, b⟩ | ⟨r, id, out⟩ | ⟨r, b⟩ | ⟨r, id⟩ |
      ⟨r, id, co⟩ | id) |
    (⟨r, k, m⟩ | ⟨r, i, k, m⟩ | ⟨k, b⟩ | ⟨k, b⟩ | ⟨i, k, b⟩ | ⟨r, k, e⟩ | ⟨r, k, b⟩ | ⟨r, k⟩)
  · exact absurd rfl hτ
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inr ⟨r, rfl, Or.inl ⟨id, b, rfl⟩⟩
  · exact absurd rfl (hret r id out)
  · exact absurd rfl (hbound r b)
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact Or.inl ⟨hτ, rfl⟩
  · exact e.elim
  · exact Or.inr ⟨r, rfl, Or.inr (Or.inl ⟨k, b, rfl⟩)⟩
  · exact Or.inl ⟨hτ, rfl⟩

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]

/-! ### The specification family's transitions

The family passes a label a round owns to the specification of that round, takes `τ` at a round
of its map, broadcasts `fail`, and idles on everything else: `GBCA.ByABDY.gbcaInstanceFamily`'s
transitions with the round instance replaced by its specification. -/

/-- The specification family idles on a label no round owns and no broadcast. -/
theorem gbcaSpecificationFamily_idle (P : Parameters) (G : GBCASpecificationFamilyState P M)
    {L : ExtendedLabel P.n M} (hτ : L ≠ Silent.τ) (hown : GBCA.ByABDY.roundOwnsLabel L = none)
    (hf : ¬ GBCA.ByABDY.isFailLabel L) : (gbcaSpecificationFamily P M).step G L (PMF.pure G) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round specification, in the map or not. -/
theorem gbcaSpecificationFamily_fail (P : Parameters) (G : GBCASpecificationFamilyState P M)
    (k : Fin P.n) :
    (gbcaSpecificationFamily P M).step G (Sum.inl (Label.fail k))
      (PMF.pure (G.applyBroadcast (Sum.inl (Label.fail k)))) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- An owned label is taken by its round alone. -/
theorem gbcaSpecificationFamily_owned_cases (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {L : ExtendedLabel P.n M} {r : ℕ} (hL : GBCA.ByABDY.roundOwnsLabel L = some r)
    (hτ : L ≠ Silent.τ) {μ : PMF (GBCASpecificationFamilyState P M)}
    (h : (gbcaSpecificationFamily P M).step G L μ) :
    ∃ X, (GBCA.specificationOverRoundAlphabet P M r).step (G r) L (PMF.pure X) ∧
      μ = PMF.pure (G.setInstanceState r X) := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r', hown, μr, hstep, rfl⟩ | ⟨-, hown, -, -⟩ | ⟨-, hown, -, -⟩
  · exact absurd habs hτ
  · obtain rfl : r' = r := by rw [hL] at hown; exact (Option.some.inj hown).symm
    obtain ⟨X, rfl⟩ := GBCA.specificationOverRoundAlphabet_isLTS P M r' _ _ _ hstep
    exact ⟨X, hstep, by rw [PMF.pure_map]⟩
  · rw [hL] at hown; exact absurd hown (by simp)
  · rw [hL] at hown; exact absurd hown (by simp)

/-- A round's own transition, read into the specification: the label the round owns is taken by
that round, in the map or not, every other round unchanged. -/
theorem gbcaSpecificationFamily_owned (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {L : ExtendedLabel P.n M} {l₀ : Label P.n} {r : ℕ} {X : GBCA.SpecState P.n}
    (hown : GBCA.ByABDY.roundOwnsLabel L = some r)
    (hpull : GBCA.specificationLabelMap P.n L = some l₀) (h : GBCA.Step P r (G r) l₀ (PMF.pure X)) :
    (gbcaSpecificationFamily P M).step G L (PMF.pure (G.setInstanceState r X)) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  refine Or.inr (Or.inl ⟨r, hown, PMF.pure X, ?_, by rw [PMF.pure_map]⟩)
  rw [GBCA.specificationOverRoundAlphabet, System.mapIdle_step_some hpull]
  exact h

/-- A round's own silent transition, the specification's binding exclusion, at a round of the
map. -/
theorem gbcaSpecificationFamily_tau (P : Parameters) {G : GBCASpecificationFamilyState P M} {r : ℕ}
    (hr : r ∈ G.instanceMap.keys) {X : GBCA.SpecState P.n}
    (h : GBCA.Step P r (G r) Label.tau (PMF.pure X)) :
    (gbcaSpecificationFamily P M).step G (Sum.inl Label.tau)
      (PMF.pure (G.setInstanceState r X)) := by
  rw [gbcaSpecificationFamily, System.family_step_iff]
  refine Or.inl ⟨rfl, r, hr, PMF.pure X, ?_, by rw [PMF.pure_map]⟩
  rw [GBCA.specificationOverRoundAlphabet,
    System.mapIdle_step_some (GBCA.specificationLabelMap_inl (Label.tau : Label P.n))]
  exact h

/-- A label a round specification owns is taken by that round alone, read
back over the specification's own alphabet. -/
theorem gbcaSpecificationFamily_owned_step (P : Parameters)
    {G G' : GBCASpecificationFamilyState P M} {L : ExtendedLabel P.n M} {l₀ : Label P.n} {r : ℕ}
    (hown : GBCA.ByABDY.roundOwnsLabel L = some r) (hτ : L ≠ Silent.τ)
    (hpull : GBCA.specificationLabelMap P.n L = some l₀)
    (h : (gbcaSpecificationFamily P M).step G L (PMF.pure G')) :
    ∃ X, GBCA.Step P r (G r) l₀ (PMF.pure X) ∧ G' = G.setInstanceState r X := by
  obtain ⟨X, hstep, heq⟩ := gbcaSpecificationFamily_owned_cases P hown hτ h
  rw [GBCA.specificationOverRoundAlphabet, System.mapIdle_step_some hpull] at hstep
  exact ⟨X, hstep, pure_inj heq⟩

/-- A label no round owns and no broadcast is taken on the identity successor
alone. -/
theorem gbcaSpecificationFamily_idle_cases (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {L : ExtendedLabel P.n M} {μ : PMF (GBCASpecificationFamilyState P M)}
    (h : (gbcaSpecificationFamily P M).step G L μ) (hτ : L ≠ Silent.τ)
    (hown : GBCA.ByABDY.roundOwnsLabel L = none) (hf : ¬ GBCA.ByABDY.isFailLabel L) :
    μ = PMF.pure G := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd habs hτ
  · rw [hown] at hr; exact absurd hr (by simp)
  · exact absurd hglob hf
  · rfl

/-- Corruption is broadcast to every round. -/
theorem gbcaSpecificationFamily_fail_cases (P : Parameters) {G : GBCASpecificationFamilyState P M}
    (k : Fin P.n) {μ : PMF (GBCASpecificationFamilyState P M)}
    (h : (gbcaSpecificationFamily P M).step G (Sum.inl (Label.fail k)) μ) :
    μ = PMF.pure (G.applyBroadcast (Sum.inl (Label.fail k))) := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨habs, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd habs (by simp)
  · exact absurd hr (by simp)
  · rfl
  · exact absurd trivial hglob

/-- A silent transition of the family is the binding exclusion of one round of its map. -/
theorem gbcaSpecificationFamily_tau_cases (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {μ : PMF (GBCASpecificationFamilyState P M)}
    (h : (gbcaSpecificationFamily P M).step G (Sum.inl Label.tau) μ) :
    ∃ r ∈ G.instanceMap.keys, ∃ X : GBCA.SpecState P.n,
      GBCA.Step P r (G r) Label.tau (PMF.pure X) ∧ μ = PMF.pure (G.setInstanceState r X) := by
  rw [gbcaSpecificationFamily, System.family_step_iff] at h
  rcases h with ⟨-, r, hr, μr, hstep, rfl⟩ | ⟨r, hr, -⟩ | ⟨habs, -, -, -⟩ | ⟨habs, -, -, -⟩
  · obtain ⟨X, rfl⟩ := GBCA.specificationOverRoundAlphabet_isLTS P M r _ _ _ hstep
    rw [GBCA.specificationOverRoundAlphabet,
      System.mapIdle_step_some (GBCA.specificationLabelMap_inl (Label.tau : Label P.n))] at hstep
    exact ⟨r, hr, X, hstep, by rw [PMF.pure_map]⟩
  · exact absurd hr (by simp)
  · exact absurd rfl habs
  · exact absurd rfl habs

/-! #### The announcement

A round outside the map reads the initial specification under the recorded corruptions, which
excludes no bit, so the announcement of a round's bound bit fires at a round of the map, and there
the specification's `announceBound` leaves the family state as it stands. -/

omit [DecidableEq M] in
/-- The untouched round specification excludes no bit: a corruption writes `F` alone. -/
theorem gbcaSpecificationFamily_untouchedInstance_excluded {P : Parameters}
    (G : GBCASpecificationFamilyState P M) :
    G.untouchedInstance.excluded = ∅ := by
  unfold InstanceFamilyState.untouchedInstance
  induction G.broadcasts with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, GBCA.ByABDY.specificationCorruptionAct_excluded, ih]

omit [DecidableEq M] in
/-- A round whose specification excludes a bit is a round of the map. -/
theorem gbcaSpecificationFamily_mem_keys_of_excluded {P : Parameters}
    {G : GBCASpecificationFamilyState P M}
    {r : ℕ} {b : Bool} (h : b ∈ (G r).excluded) : r ∈ G.instanceMap.keys := by
  by_contra hr
  rw [InstanceFamilyState.apply_of_notMem hr,
    gbcaSpecificationFamily_untouchedInstance_excluded] at h
  exact Finset.notMem_empty b h

/-- The announcement of round `r`'s bound bit `b` is a self-loop of the family under the guard
`(!b) ∈ excluded` of the round's specification (D29). -/
theorem gbcaSpecificationFamily_boundG (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {r : ℕ} {b : Bool} (h : (!b) ∈ (G r).excluded) :
    (gbcaSpecificationFamily P M).step G (Sum.inl (Label.boundG r b)) (PMF.pure G) := by
  have hstep := gbcaSpecificationFamily_owned P (L := Sum.inl (Label.boundG r b)) rfl rfl
    (GBCA.Step.announceBound (G r) b h)
  rwa [InstanceFamilyState.setInstanceState_apply_self
    (gbcaSpecificationFamily_mem_keys_of_excluded h)] at hstep

/-- A transition of the family on the announcement of round `r`'s bound bit `b` is the self-loop,
under the guard `(!b) ∈ excluded`. -/
theorem gbcaSpecificationFamily_boundG_cases (P : Parameters)
    {G : GBCASpecificationFamilyState P M} {r : ℕ} {b : Bool}
    {μ : PMF (GBCASpecificationFamilyState P M)}
    (h : (gbcaSpecificationFamily P M).step G (Sum.inl (Label.boundG r b)) μ) :
    (!b) ∈ (G r).excluded ∧ μ = PMF.pure G := by
  obtain ⟨X, hstep, rfl⟩ := gbcaSpecificationFamily_owned_cases P
    (L := Sum.inl (Label.boundG r b)) rfl (by simp) h
  rw [GBCA.specificationOverRoundAlphabet,
    System.mapIdle_step_some (GBCA.specificationLabelMap_inl (Label.boundG r b))] at hstep
  obtain ⟨hex, hX⟩ := GBCA.step_boundG_cases hstep
  obtain rfl : X = G r := pure_inj hX
  exact ⟨hex, by rw [InstanceFamilyState.setInstanceState_apply_self
    (gbcaSpecificationFamily_mem_keys_of_excluded hex)]⟩

/-! ### The common coin's transitions

The coin is a family over the same shape: a label of a coin round moves that round, `fail` is
broadcast, and everything else leaves it as it stands. -/

/-- The common coin's family idles on a label outside its own API. -/
theorem wccFamily_idle_cases (P : Parameters)
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {l : Label P.n}
    {ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    (hl : l ≠ Label.tau) (hr : Label.wccRound l = none) (hf : ¬ Label.isFail l)
    (h : (WCC.specFamily P).step o l ω) : ω = PMF.pure o := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr', -⟩ | ⟨-, -, hglob, -⟩ | ⟨-, -, -, rfl⟩
  · exact absurd hτ hl
  · rw [hr] at hr'; exact absurd hr' (by simp)
  · exact absurd hglob hf
  · rfl

/-- A label the common coin's family owns moves its round alone, in the map or not. -/
theorem wccFamily_owned_cases (P : Parameters)
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {l : Label P.n}
    {r : ℕ} {ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    (hl : l ≠ Label.tau) (hr : Label.wccRound l = some r) (h : (WCC.specFamily P).step o l ω) :
    ∃ μw', WCC.Step P r (o r) l μw' ∧ ω = μw'.map (o.setInstanceState r) := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r', hr', μw', hstep, rfl⟩ | ⟨-, hr'', -, -⟩ | ⟨-, hr'', -, -⟩
  · exact absurd hτ hl
  · obtain rfl : r' = r := by rw [hr] at hr'; exact (Option.some.inj hr').symm
    exact ⟨μw', hstep, rfl⟩
  · rw [hr] at hr''; exact absurd hr'' (by simp)
  · rw [hr] at hr''; exact absurd hr'' (by simp)

/-- A round of the common coin moves on the label it owns, in the map or not, every other round
unchanged. -/
theorem wccFamily_owned (P : Parameters)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {l : Label P.n}
    {r : ℕ} {x : WCC.SpecState P.n} (hr : Label.wccRound l = some r)
    (h : WCC.Step P r (o r) l (PMF.pure x)) :
    (WCC.specFamily P).step o l (PMF.pure (o.setInstanceState r x)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hr, PMF.pure x, h, by rw [PMF.pure_map]⟩)

/-- Corruption is broadcast to every round of the common coin's family. -/
theorem wccFamily_fail (P : Parameters)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) (k : Fin P.n) :
    (WCC.specFamily P).step o (.fail k) (PMF.pure (o.applyBroadcast (.fail k))) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- A corruption broadcast moves every round of the common coin's
family. -/
theorem wccFamily_fail_cases (P : Parameters)
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} (k : Fin P.n)
    {ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    (h : (WCC.specFamily P).step o (.fail k) ω) : ω = PMF.pure (o.applyBroadcast (.fail k)) := by
  rw [WCC.specFamily, System.family_step_iff] at h
  rcases h with ⟨hτ, -⟩ | ⟨r, hr, -⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, hglob, -⟩
  · exact absurd hτ (by simp)
  · exact absurd hr (by simp [Label.wccRound])
  · rfl
  · exact absurd trivial hglob

/-! ### Reading a protocol-shaped transition into its four components -/

/-- Build a synchronised transition of the four components on a visible label, the
coin's successor left arbitrary. -/
theorem hybridExtended_visible_step (P : Parameters) {G G' : GBCASpecificationFamilyState P M}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))}
    {L : ExtendedLabel P.n M} (hL : L ≠ Silent.τ)
    (hG : (gbcaSpecificationFamily P M).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P M).step o L ω) :
    (hybridExtended P M).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [hybridExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω, roundLoopProduct_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- A visible transition of the four components: all of them move together, and
only the coin's successor can fail to be a Dirac. -/
theorem hybridExtended_visible_cases (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {L : ExtendedLabel P.n M} (hL : L ≠ Silent.τ)
    {μ : PMF (HybridState P M)} (h : (hybridExtended P M).step (G, C, A, o) L μ) :
    ∃ (G' : GBCASpecificationFamilyState P M) (C' : ∀ _ : Fin P.n, RoundLoopVariables P.n)
      (A' : ABANetworkState P.n)
      (ω : PMF (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))),
      (gbcaSpecificationFamily P M).step G L (PMF.pure G') ∧
      (∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i))) ∧
      ABANetworkStep P A L (PMF.pure A') ∧ (coinOverRoundAlphabet P M).step o L ω ∧
      μ = prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω)) := by
  rw [hybridExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hG, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨G', rfl⟩ := gbcaSpecificationFamily_isLTS P M _ _ _ hG
    rw [System.parallel_step] at hrest
    rcases hrest with ⟨-, μ₂, μ₃, hC, hrest, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨C', rfl, hall⟩ := roundLoopProduct_cases hC
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

/-- **The announcement of round `r`'s bound bit `b`** is a self-loop of the four components
under the guard `(!b) ∈ excluded` of the round's specification: the family's round `r` announces,
every round loop and the ABA network take `boundGIdle`, and the coin idles, the label naming no
coin round and no corruption (D29). -/
theorem hybridExtended_boundG (P : Parameters) {G : GBCASpecificationFamilyState P M}
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) {r : ℕ} {b : Bool}
    (h : (!b) ∈ (G r).excluded) :
    (hybridExtended P M).step (G, C, A, o) (Sum.inl (Label.boundG r b))
      (PMF.pure (G, C, A, o)) := by
  have hstep := hybridExtended_visible_step (M := M) P (L := Sum.inl (Label.boundG r b))
    (by simp) (gbcaSpecificationFamily_boundG P h) (fun i => RoundLoopStep.boundGIdle (C i) r b)
    (ABANetworkStep.boundGIdle A r b)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.boundG r b)) _).mpr
      (wccFamily_idle P o (by simp) rfl (by simp [Label.isFail])))
  rwa [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at hstep

/-- Build a silent transition of the four components from a specification one. -/
theorem hybridExtended_tau_specification (P : Parameters)
    {G G' : GBCASpecificationFamilyState P M}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hG : (gbcaSpecificationFamily P M).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (hybridExtended P M).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [hybridExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from the resolution of one round of the
common coin's map. -/
theorem hybridExtended_tau_coin (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {r : ℕ}
    (hr : r ∈ o.instanceMap.keys) {μw : PMF (WCC.SpecState P.n)}
    (hW : WCC.Step P r (o r) Label.tau μw) :
    (hybridExtended P M).step (G, C, A, o) (Sum.inl Label.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
        (prodPMF (PMF.pure A) (μw.map (o.setInstanceState r))))) := by
  rw [hybridExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, _, coinOverExtendedAlphabet_tau P M Empty o hr hW, rfl⟩)

/-- A silent transition of the four components: no round loop has a `τ` transition, so it is the
binding exclusion of one round of the specification family's map, the ABA network's DECIDED
injection, or the resolution of one round of the common coin's map. -/
theorem hybridExtended_tau_cases (P : Parameters) {G : GBCASpecificationFamilyState P M}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    {μ : PMF (HybridState P M)}
    (h : (hybridExtended P M).step (G, C, A, o) (Sum.inl Label.tau) μ) :
    (∃ G', (gbcaSpecificationFamily P M).step G (Sum.inl Label.tau) (PMF.pure G') ∧
        μ = PMF.pure (G', C, A, o)) ∨
    (∃ A', ABANetworkStep P A (Sum.inl Label.tau : ExtendedLabel P.n M) (PMF.pure A') ∧
      μ = PMF.pure (G, C, A', o)) ∨
    (∃ r ∈ o.instanceMap.keys, ∃ μw : PMF (WCC.SpecState P.n),
      WCC.Step P r (o r) Label.tau μw ∧
      μ = prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
        (prodPMF (PMF.pure A) (μw.map (o.setInstanceState r))))) := by
  rw [hybridExtended, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hG, rfl⟩ | ⟨-, μ₂, hrest, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨G', rfl⟩ := gbcaSpecificationFamily_isLTS P M _ _ _ hG
    exact Or.inl ⟨G', hG, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hrest
    rcases hrest with ⟨habs, -⟩ | ⟨-, μ₂, hC, rfl⟩ | ⟨-, μ₃, hrest, rfl⟩
    · exact absurd rfl habs
    · exact (roundLoopProduct_no_tau hC).elim
    · rw [System.parallel_step] at hrest
      rcases hrest with ⟨habs, -⟩ | ⟨-, μ₃, hA, rfl⟩ | ⟨-, ω, hW, rfl⟩
      · exact absurd rfl habs
      · obtain ⟨A', rfl⟩ := abaNetworkStep_dirac hA
        exact Or.inr (Or.inl ⟨A', hA,
          by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]⟩)
      · obtain ⟨r, hr, μw, hstep, rfl⟩ := WCC.specFamily_tau_cases P
          ((System.mapIdle_step_some (coinLabelMap_inl Label.tau) ω).mp hW)
        exact Or.inr (Or.inr ⟨r, hr, μw, hstep, rfl⟩)

/-! ### The two hidings -/

/-- **The protocol-shaped group**: the synchronisation labels hidden, the result
read back over `Label n`. The account below reads a transition of `hybrid` through it, label
class by label class; nothing outside this file names it. -/
private noncomputable def hybridHidden (P : Parameters) (M : Type) [DecidableEq M] :
    System (HybridState P M) (Label P.n) :=
  ((hybridExtended P M).abstract (networkEventLabels P.n)).relabel

/-- The group's step relation, unfolded to the hidden-synchronisation case and the
shared-label case. -/
theorem hybridHidden_step_iff (P : Parameters) (q : HybridState P M) (l : Label P.n)
    (μ : PMF (HybridState P M)) :
    (hybridHidden P M).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n M, (hybridExtended P M).step q (Sum.inr e) μ) ∨
      (hybridExtended P M).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

/-- The protocol-shaped specification's step relation: a sub-protocol API
label seen as `τ`, or a label that the hiding leaves visible. -/
theorem hybrid_step_iff (P : Parameters) (q : HybridState P M) (l : Label P.n)
    (μ : PMF (HybridState P M)) :
    (hybrid P M).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n, (hybridHidden P M).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧ (hybridHidden P M).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-! ### Building a transition through the two hidings

A transition of the four components reaches the protocol-shaped specification
in one of three ways, according to its label: a synchronisation label and a
sub-protocol API label are both hidden to `τ`, and every remaining label
is hidden by neither hiding. -/

/-- A synchronised transition is silent: the synchronisation labels are hidden. -/
theorem hybrid_synchronisation (P : Parameters) {q : HybridState P M} {e : NetworkEvent P.n M}
    {μ : PMF (HybridState P M)} (h : (hybridExtended P M).step q (Sum.inr e) μ) :
    (hybrid P M).step q Label.tau μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨by simp, (hybridHidden_step_iff P q Label.tau μ).mpr (Or.inl ⟨rfl, e, h⟩)⟩

/-- A sub-protocol API label is silent: the API is hidden. -/
theorem hybrid_hidden (P : Parameters) {q : HybridState P M} {l : Label P.n}
    {μ : PMF (HybridState P M)} (hl : l ∈ Label.hiddenAPI P.n)
    (h : (hybridExtended P M).step q (Sum.inl l) μ) :
    (hybrid P M).step q Label.tau μ := by
  rw [hybrid_step_iff]
  exact Or.inl ⟨rfl, l, hl, (hybridHidden_step_iff P q l μ).mpr (Or.inr h)⟩

/-- A label outside the sub-protocol API is hidden by neither hiding. -/
theorem hybrid_visible (P : Parameters) {q : HybridState P M} {l : Label P.n}
    {μ : PMF (HybridState P M)} (hl : l ∉ Label.hiddenAPI P.n)
    (h : (hybridExtended P M).step q (Sum.inl l) μ) :
    (hybrid P M).step q l μ := by
  rw [hybrid_step_iff]
  exact Or.inr ⟨hl, (hybridHidden_step_iff P q l μ).mpr (Or.inr h)⟩

end ABA

end PLTS
