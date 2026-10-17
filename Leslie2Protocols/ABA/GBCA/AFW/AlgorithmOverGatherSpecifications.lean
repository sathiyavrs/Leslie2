/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.CompositionStepCases
import Leslie2Protocols.ABA.GBCA.SpecificationOverRoundAlphabet
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The algorithm of the round over the gather specifications

`GBCA.ByAFW.AlgorithmOverGatherSpecifications` states the transitions of
`GBCA.ByAFW.roundOverGatherSpecifications` (`GBCA/AFW/Composition.lean`), the `n`
graded-agreement programs beside the round's network, in parallel with two gather specifications,
over the round's state, through the four projections `programs`, `network`, `firstGather` and
`secondGather`. It is a relation on that state; the system is the composition.

`roundOverGatherSpecifications_step_iff_algorithm` is the characterisation: at every label `l`,
the `l`-transitions of the round are exactly the `l`-transitions of
`AlgorithmOverGatherSpecifications`, on the same state and with the same distribution.

## The gather specifications

A gather instance's own transitions are `Gather.Step` (`ABA/Gather/Specification.lean`), and a
transition of the round carries them as the hypothesis
`Gather.Step P (firstGather s) l₀ (PMF.pure t1)`. The specification takes `call id x` on two
transitions, the call and the input-enabledness loop, at the one label `Gather.Label.call id x`:
the round's `callG` and its `callLoop` therefore carry the same hypothesis, and which of the two
the gather takes is the gather's own business. The round's call and a corrupted process's call
are both cases of `callG` and `callLoop`, at the labels `GBCA.specificationLabelMap` sends to the
call (`callLabel_maps`).

The first gather's announcement of its core is the case `firstGatherCore`: the round's network
records the core where none is recorded. A gather's return to a program whose guards refuse it is
the case `firstGatherReturnLoop` or `secondGatherReturnLoop`, and the round's network announces
the bound bit of the recorded core in the case `announceBound`.

## Corruption

The `fail` transition corrupts the two gather instances and leaves the programs and the round's
network untouched. The label is in the round's alphabet, and in the family of rounds it is a
broadcast, applied at every round by the family's broadcast act.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### Reading a gather specification through a pullback -/

section GatherSpecificationAlongPullback
variable {X : Type} [DecidableEq X] {P : Parameters} {c c' : Gather.SpecState P.n X}
  {L : RoundLabel P.n} {ψ : RoundLabel P.n → Option (Gather.Label P.n X)}

/-- A gather specification's step read along a pullback, at a label with an image, is the
specification's own step at that image. -/
theorem specInst_mapIdle_step {l₀ : Gather.Label P.n X} (hψ : ψ L = some l₀)
    (h : ((Gather.specInst P X).mapIdle ψ).step c L (PMF.pure c')) :
    Gather.Step P c l₀ (PMF.pure c') :=
  (System.mapIdle_step_some hψ _).mp h

/-- Build a gather specification's step read along a pullback, at a label with an image. -/
theorem specInst_mapIdle_step_of_step {l₀ : Gather.Label P.n X} (hψ : ψ L = some l₀)
    (h : Gather.Step P c l₀ (PMF.pure c')) :
    ((Gather.specInst P X).mapIdle ψ).step c L (PMF.pure c') :=
  (System.mapIdle_step_some hψ _).mpr h

/-- The one corruption transition of the gather specification. -/
theorem specStep_fail {id : Fin P.n} {μ : PMF (Gather.SpecState P.n X)}
    (h : Gather.Step P c (.fail id) μ) : μ = PMF.pure (c.corrupt P id) := by cases h; rfl

/-- The one announcement transition of the gather specification: a self-loop under the guard
that the announced set is the core. -/
theorem specStep_core {C : Gather.AcceptedPairs P.n X} {μ : PMF (Gather.SpecState P.n X)}
    (h : Gather.Step P c (.core C) μ) : c.core = some C ∧ μ = PMF.pure c := by
  cases h with
  | announceCore _ hC => exact ⟨hC, rfl⟩

end GatherSpecificationAlongPullback

/-! ### The labels of a call

`GBCA.specificationLabelMap` sends two labels to the call `callG r id b`: the round's call and a
corrupted process's call `byzantineCallG r id b`. Both reach a program as the call and the first
gather as its call. -/

/-- The two labels of a call: the round's call and a corrupted process's call. -/
theorem callLabel_cases {n : ℕ} {r : ℕ} {id : Fin n} {b : Bool} {l : ExtendedLabel n Empty}
    (hl : GBCA.specificationLabelMap n l = some (.callG r id b)) :
    l = Sum.inl (.callG r id b) ∨ l = Sum.inr (.byzantineCallG r id b) := by
  rcases l with l₀ | e
  · rw [GBCA.specificationLabelMap_inl] at hl
    exact Or.inl (by rw [Option.some.inj hl])
  · cases e
    case gbcaRoundEvent e => exact e.elim
    case byzantineCallG r' k b' =>
      obtain ⟨rfl, rfl, rfl⟩ := Label.callG.inj (Option.some.inj hl)
      exact Or.inr rfl
    all_goals simp at hl

/-- A label of a call reaches a program as the call, the first gather as its call, and the second
gather not at all, and it is visible. -/
theorem callLabel_maps {n : ℕ} {r : ℕ} {id : Fin n} {b : Bool} {l : ExtendedLabel n Empty}
    (hl : GBCA.specificationLabelMap n l = some (.callG r id b)) :
    programLabelMap n (Sum.inl l) = some (.callG r id b) ∧
      firstGatherLabelMap n (Sum.inl l) = some (.call id b) ∧
      secondGatherLabelMap n (Sum.inl l) = none ∧ l ≠ Sum.inl Label.tau := by
  rcases callLabel_cases hl with rfl | rfl <;> exact ⟨rfl, rfl, rfl, by simp⟩

/-! ### The algorithm -/

/-- The transitions of the round over the gather specifications
(`GBCA.ByAFW.roundOverGatherSpecifications`), stated over the round's state, label by label. All
transitions are Dirac. -/
inductive AlgorithmOverGatherSpecifications (P : Parameters) (r : ℕ) :
    RoundStateOverGatherSpecifications P.n → ExtendedLabel P.n Empty →
      PMF (RoundStateOverGatherSpecifications P.n) → Prop
  /-- The call arrives at a program holding no input: program `id` records the input and the
  first gather takes the call. The label is the round's call or a corrupted process's call. -/
  | callG (s : RoundStateOverGatherSpecifications P.n) (l : ExtendedLabel P.n Empty) (id : Fin P.n)
      (b : Bool) (hl : GBCA.specificationLabelMap P.n l = some (.callG r id b))
      (t1 : Gather.SpecState P.n Bool) (h0 : (programs s id).input = none)
      (h : Gather.Step P (firstGather s) (.call id b) (PMF.pure t1)) :
      AlgorithmOverGatherSpecifications P r s l
        (PMF.pure (setFirstGather (setPrograms s (Function.update (programs s) id
          { programs s id with input := some b })) t1))
  /-- The call arrives at a program holding an input: no program moves and the first gather takes
  the call. -/
  | callLoop (s : RoundStateOverGatherSpecifications P.n) (l : ExtendedLabel P.n Empty)
      (id : Fin P.n) (b : Bool) (hl : GBCA.specificationLabelMap P.n l = some (.callG r id b))
      (t1 : Gather.SpecState P.n Bool) (hin : (programs s id).input ≠ none)
      (h : Gather.Step P (firstGather s) (.call id b) (PMF.pure t1)) :
      AlgorithmOverGatherSpecifications P r s l (PMF.pure (setFirstGather s t1))
  /-- An internal step of the first gather. -/
  | firstGatherTau (s : RoundStateOverGatherSpecifications P.n) (t1 : Gather.SpecState P.n Bool)
      (h : Gather.Step P (firstGather s) Gather.Label.tau (PMF.pure t1)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau) (PMF.pure (setFirstGather s t1))
  /-- An internal step of the second gather. -/
  | secondGatherTau (s : RoundStateOverGatherSpecifications P.n)
      (t2 : Gather.SpecState P.n (Option Bool))
      (h : Gather.Step P (secondGather s) Gather.Label.tau (PMF.pure t2)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau) (PMF.pure (setSecondGather s t2))
  /-- The first gather returns to a called program `id` holding no candidate: program `id`
  records the candidate. -/
  | firstGatherReturn (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n)
      (g : Fin P.n → Option Bool) (t1 : Gather.SpecState P.n Bool)
      (hin : (programs s id).input ≠ none) (hc : (programs s id).candidate = none)
      (h : Gather.Step P (firstGather s) (.ret id g) (PMF.pure t1)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau)
        (PMF.pure (setFirstGather (setPrograms s (Function.update (programs s) id
          { programs s id with candidate := some (candidate P g) })) t1))
  /-- The first gather returns to a program that has not called or holds a candidate: no program
  moves. -/
  | firstGatherReturnLoop (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n)
      (g : Fin P.n → Option Bool) (t1 : Gather.SpecState P.n Bool)
      (hloop : ¬ ((programs s id).input ≠ none ∧ (programs s id).candidate = none))
      (h : Gather.Step P (firstGather s) (.ret id g) (PMF.pure t1)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau) (PMF.pure (setFirstGather s t1))
  /-- The first gather announces its core `C`: the round's network records it where no core is
  recorded. -/
  | firstGatherCore (s : RoundStateOverGatherSpecifications P.n) (C : Gather.AcceptedPairs P.n Bool)
      (hC : (firstGather s).core = some C) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau)
        (PMF.pure (setNetwork s
          { network s with firstGatherCore := some ((network s).firstGatherCore.getD C) }))
  /-- Program `id` calls the second gather with the candidate it holds. -/
  | secondGatherCall (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (x : Option Bool)
      (t2 : Gather.SpecState P.n (Option Bool)) (hc : (programs s id).candidate = some x)
      (h2 : (programs s id).secondGatherCalled = false)
      (h : Gather.Step P (secondGather s) (.call id x) (PMF.pure t2)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau)
        (PMF.pure (setSecondGather (setPrograms s (Function.update (programs s) id
          { programs s id with secondGatherCalled := true })) t2))
  /-- The second gather returns to a program `id` that has called it and holds no grade: program
  `id` records the grade. -/
  | secondGatherReturn (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n)
      (g : Fin P.n → Option (Option Bool)) (t2 : Gather.SpecState P.n (Option Bool))
      (h2 : (programs s id).secondGatherCalled = true) (ho : (programs s id).output = none)
      (h : Gather.Step P (secondGather s) (.ret id g) (PMF.pure t2)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau)
        (PMF.pure (setSecondGather (setPrograms s (Function.update (programs s) id
          { programs s id with output := some (gradeOf P g) })) t2))
  /-- The second gather returns to a program that has not called it or holds a grade: no program
  moves. -/
  | secondGatherReturnLoop (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n)
      (g : Fin P.n → Option (Option Bool)) (t2 : Gather.SpecState P.n (Option Bool))
      (hloop : ¬ ((programs s id).secondGatherCalled = true ∧ (programs s id).output = none))
      (h : Gather.Step P (secondGather s) (.ret id g) (PMF.pure t2)) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl .tau) (PMF.pure (setSecondGather s t2))
  /-- The round returns the grade program `id` holds: the variables drop it and the round's
  network records the return. -/
  | retG (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (out : GBCAOutput)
      (ho : (programs s id).output = some out) (hr : (programs s id).returned = false) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl (.retG r id out))
        (PMF.pure (setNetwork (setPrograms s (Function.update (programs s) id
          { programs s id with output := none, returned := true }))
          { network s with returned := true }))
  /-- The round's network announces the bound bit of the recorded core once the round has
  returned. Nothing moves. -/
  | announceBound (s : RoundStateOverGatherSpecifications P.n) (C : Gather.AcceptedPairs P.n Bool)
      (hC : (network s).firstGatherCore = some C) (hr : (network s).returned = true) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl (.boundG r (boundOfCore P C))) (PMF.pure s)
  /-- Corruption (deviation D1): the two gather instances corrupted together, the programs and the
  round's network untouched. -/
  | fail (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) :
      AlgorithmOverGatherSpecifications P r s (Sum.inl (.fail id))
        (PMF.pure (corruptAll P id (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s))

/-! ### The characterisation by the algorithm -/

section Characterisation
variable {P : Parameters} {r : ℕ}

/-- A transition of the round on a label of a call is the algorithm's call or call loop. -/
theorem algorithm_of_callStep {r' : ℕ} {u : ∀ _ : Fin P.n, ProcessVariables P.n}
    {v : NetworkState P.n} {c : Gather.SpecState P.n Bool} {d : Gather.SpecState P.n (Option Bool)}
    {l : ExtendedLabel P.n Empty} {id : Fin P.n} {b : Bool}
    (hl : GBCA.specificationLabelMap P.n l = some (.callG r' id b))
    {x : ∀ _ : Fin P.n, ProcessVariables P.n} {v' : NetworkState P.n}
    {c' : Gather.SpecState P.n Bool} {d' : Gather.SpecState P.n (Option Bool)}
    (hRoundPrograms : (roundPrograms P r).step (u, v) (Sum.inl l) (PMF.pure (x, v')))
    (hga1 : ((Gather.specInst P Bool).mapIdle (firstGatherLabelMap P.n)).step c (Sum.inl l)
      (PMF.pure c'))
    (hga2 : ((Gather.specInst P (Option Bool)).mapIdle (secondGatherLabelMap P.n)).step d
      (Sum.inl l) (PMF.pure d')) :
    AlgorithmOverGatherSpecifications P r ((u, v), (c, d)) l (PMF.pure ((x, v'), (c', d'))) := by
  obtain ⟨hp, h1, h2, -⟩ := callLabel_maps hl
  obtain ⟨hproc, hnet⟩ := roundPrograms_label_pure hp (by simp) hRoundPrograms
  obtain rfl : r' = r := programStep_callG_round (hproc id)
  have hfor : ∀ i, i ≠ id → x i = u i :=
    fun i hi => PMF.pure_injective (programStep_callG_notOwn (Ne.symm hi) (hproc i))
  have hv : v' = v := PMF.pure_injective (networkStep_callG hnet)
  have hg1 : Gather.Step P c (.call id b) (PMF.pure c') := specInst_mapIdle_step h1 hga1
  have hd : d' = d := System.mapIdle_eq_of_step_none h2 hga2
  subst hv hd
  rcases programStep_callG_own (hproc id) with ⟨h0, hxid⟩ | ⟨hin, hxid⟩
  · have hx := Function.eq_update_iff.mpr ⟨PMF.pure_injective hxid, hfor⟩
    subst hx
    exact AlgorithmOverGatherSpecifications.callG _ l id b hl c' h0 hg1
  · have hx : x = u := funext fun i => by
      by_cases hi : i = id
      · subst hi
        exact PMF.pure_injective hxid
      · exact hfor i hi
    subst hx
    exact AlgorithmOverGatherSpecifications.callLoop _ l id b hl c' hin hg1

/-- **The projection.** Every transition of the round is a transition of the algorithm on the
same label. -/
theorem roundOverGatherSpecifications_step_algorithm (P : Parameters) (r : ℕ) :
    ∀ (s : RoundStateOverGatherSpecifications P.n) (l : ExtendedLabel P.n Empty)
      (μ : PMF (RoundStateOverGatherSpecifications P.n)),
      (roundOverGatherSpecifications P r).step s l μ →
        AlgorithmOverGatherSpecifications P r s l μ := by
  have h1 : (Gather.specInst P Bool).IsLTS := Gather.specInst_isLTS P
  have h2 : (Gather.specInst P (Option Bool)).IsLTS := Gather.specInst_isLTS P
  rintro ⟨⟨u, v⟩, c, d⟩ l μ hstep
  rcases (roundOverGathers_step_iff P r (Gather.specInst P Bool) (Gather.specInst P (Option Bool))
      _ l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · obtain ⟨x, v', c', d', rfl, hRoundPrograms, hga1, hga2⟩ :=
      roundOverGathersExtended_synchronised_cases h1 h2 (by simp) hev
    cases e with
    | firstGatherReturn id g =>
      obtain ⟨hproc, hnet⟩ := roundPrograms_label_pure (lp := .firstGatherReturn id g) (by simp)
        (by simp) hRoundPrograms
      have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
        PMF.pure_injective (programStep_firstGatherReturn_notOwn (Ne.symm hi) (hproc i))
      have hv : v' = v := PMF.pure_injective (networkStep_firstGatherReturn hnet)
      have hg1 : Gather.Step P c (.ret id g) (PMF.pure c') := specInst_mapIdle_step (by simp) hga1
      have hd : d' = d := System.mapIdle_eq_of_step_none (by simp) hga2
      subst hv hd
      rcases programStep_firstGatherReturn_own (hproc id) with ⟨hin, hc, hxid⟩ | ⟨hloop, hxid⟩
      · have hx := Function.eq_update_iff.mpr ⟨PMF.pure_injective hxid, hfor⟩
        subst hx
        exact AlgorithmOverGatherSpecifications.firstGatherReturn _ id g c' hin hc hg1
      · have hx : x = u := funext fun i => by
          by_cases hi : i = id
          · subst hi
            exact PMF.pure_injective hxid
          · exact hfor i hi
        subst hx
        exact AlgorithmOverGatherSpecifications.firstGatherReturnLoop _ id g c' hloop hg1
    | firstGatherCore C =>
      obtain ⟨hproc, hnet⟩ := roundPrograms_label_pure (lp := .firstGatherCore C) (by simp)
        (by simp) hRoundPrograms
      have hx : x = u := funext fun i => PMF.pure_injective (programStep_firstGatherCore (hproc i))
      have hv := PMF.pure_injective (networkStep_firstGatherCore hnet)
      obtain ⟨hC, hc⟩ := specStep_core (specInst_mapIdle_step (l₀ := .core C) (by simp) hga1)
      have hc' : c' = c := PMF.pure_injective hc
      have hd : d' = d := System.mapIdle_eq_of_step_none (by simp) hga2
      subst hx hv hc' hd
      exact AlgorithmOverGatherSpecifications.firstGatherCore _ C hC
    | secondGatherCall id y =>
      obtain ⟨hproc, hnet⟩ :=
        roundPrograms_label_pure (lp := .secondGatherCall id y) (by simp) (by simp) hRoundPrograms
      obtain ⟨hc, h2', hxid⟩ := programStep_secondGatherCall_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_secondGatherCall_notOwn (Ne.symm hi) (hproc i))
      have hx := Function.eq_update_iff.mpr ⟨PMF.pure_injective hxid, hfor⟩
      have hv : v' = v := PMF.pure_injective (networkStep_secondGatherCall hnet)
      have hc1 : c' = c := System.mapIdle_eq_of_step_none (by simp) hga1
      have hg2 : Gather.Step P d (.call id y) (PMF.pure d') := specInst_mapIdle_step (by simp) hga2
      subst hx hv hc1
      exact AlgorithmOverGatherSpecifications.secondGatherCall _ id y d' hc h2' hg2
    | secondGatherReturn id g =>
      obtain ⟨hproc, hnet⟩ := roundPrograms_label_pure (lp := .secondGatherReturn id g) (by simp)
        (by simp) hRoundPrograms
      have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
        PMF.pure_injective (programStep_secondGatherReturn_notOwn (Ne.symm hi) (hproc i))
      have hv : v' = v := PMF.pure_injective (networkStep_secondGatherReturn hnet)
      have hc1 : c' = c := System.mapIdle_eq_of_step_none (by simp) hga1
      have hg2 : Gather.Step P d (.ret id g) (PMF.pure d') := specInst_mapIdle_step (by simp) hga2
      subst hv hc1
      rcases programStep_secondGatherReturn_own (hproc id) with ⟨h2', ho, hxid⟩ | ⟨hloop, hxid⟩
      · have hx := Function.eq_update_iff.mpr ⟨PMF.pure_injective hxid, hfor⟩
        subst hx
        exact AlgorithmOverGatherSpecifications.secondGatherReturn _ id g d' h2' ho hg2
      · have hx : x = u := funext fun i => by
          by_cases hi : i = id
          · subst hi
            exact PMF.pure_injective hxid
          · exact hfor i hi
        subst hx
        exact AlgorithmOverGatherSpecifications.secondGatherReturnLoop _ id g d' hloop hg2
  · by_cases hlτ : l = Sum.inl Label.tau
    · subst hlτ
      rcases roundOverGathersExtended_tau_cases h1 h2 hlab with ⟨c', rfl, hs⟩ | ⟨d', rfl, hs⟩
      · exact AlgorithmOverGatherSpecifications.firstGatherTau _ c' hs
      · exact AlgorithmOverGatherSpecifications.secondGatherTau _ d' hs
    · obtain ⟨x, v', c', d', rfl, hRoundPrograms, hga1, hga2⟩ :=
        roundOverGathersExtended_synchronised_cases h1 h2 (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | retABA id b => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | callW r' id => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | retW r' id b => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | callG r' id b => exact algorithm_of_callStep rfl hRoundPrograms hga1 hga2
        | retG r' id out =>
          obtain ⟨hproc, hnet⟩ :=
            roundPrograms_label_pure (lp := .retG r' id out) (by simp) (by simp) hRoundPrograms
          obtain rfl : r' = r := programStep_retG_round (hproc id)
          obtain ⟨ho, hr, hxid⟩ := programStep_retG_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_retG_notOwn (Ne.symm hi) (hproc i))
          have hx := Function.eq_update_iff.mpr ⟨PMF.pure_injective hxid, hfor⟩
          have hv : v' = { v with returned := true } := PMF.pure_injective (networkStep_retG hnet)
          have hc1 : c' = c := System.mapIdle_eq_of_step_none (by simp) hga1
          have hd : d' = d := System.mapIdle_eq_of_step_none (by simp) hga2
          subst hx hv hc1 hd
          exact AlgorithmOverGatherSpecifications.retG _ id out ho hr
        | boundG r' b =>
          obtain ⟨hproc, hnet⟩ :=
            roundPrograms_label_pure (lp := .boundG r' b) (by simp) (by simp) hRoundPrograms
          obtain ⟨rfl, C, hC, hr, rfl, hv⟩ := networkStep_boundG hnet
          have hx : x = u := funext fun i => PMF.pure_injective (programStep_boundG (hproc i)).2
          have hv' : v' = v := PMF.pure_injective hv
          have hc1 : c' = c := System.mapIdle_eq_of_step_none (by simp) hga1
          have hd : d' = d := System.mapIdle_eq_of_step_none (by simp) hga2
          subst hx hv' hc1 hd
          exact AlgorithmOverGatherSpecifications.announceBound _ C hC hr
        | fail id =>
          obtain ⟨hx, hv⟩ := roundPrograms_idle_pure (by simp) hRoundPrograms
          have hg1 : Gather.Step P c (.fail id) (PMF.pure c') :=
            specInst_mapIdle_step (by simp) hga1
          have hg2 : Gather.Step P d (.fail id) (PMF.pure d') :=
            specInst_mapIdle_step (by simp) hga2
          have hc1 : c' = c.corrupt P id := PMF.pure_injective (specStep_fail hg1)
          have hd1 : d' = d.corrupt P id := PMF.pure_injective (specStep_fail hg2)
          subst hx hv hc1 hd1
          exact AlgorithmOverGatherSpecifications.fail _ id
      | inr ev =>
        cases ev with
        | gbcaRoundEvent r' j e => exact e.elim
        | gbcaSend r' j m => exact m.elim
        | gbcaDeliver r' i j m => exact m.elim
        | decidedRelay j b => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | decidedDeliver i j b => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | decidedSend j b => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | byzantineCallW r' k => exact (roundPrograms_outside_cases (by simp) hRoundPrograms).elim
        | byzantineCallG r' k b => exact algorithm_of_callStep rfl hRoundPrograms hga1 hga2

/-- **The embedding.** Every transition of the algorithm is a transition of the round on the
same label. -/
theorem algorithm_roundOverGatherSpecifications_step (P : Parameters) (r : ℕ) :
    ∀ (s : RoundStateOverGatherSpecifications P.n) (l : ExtendedLabel P.n Empty)
      (μ : PMF (RoundStateOverGatherSpecifications P.n)),
      AlgorithmOverGatherSpecifications P r s l μ →
        (roundOverGatherSpecifications P r).step s l μ := by
  rintro ⟨⟨u, v⟩, c, d⟩ l μ htransition
  cases htransition with
  | callG l' id b hl t1 h0 h =>
    obtain ⟨hp, h1, h2, hlτ⟩ := callLabel_maps hl
    exact roundOverGathers_label_step hlτ
      (roundPrograms_label_step (lp := .callG r id b) hp (by simp)
        (dirac_steps_update (ProgramStep.callG (u id) b h0)
          (fun i hi => ProgramStep.callGIdle (u i) id b (Ne.symm hi)))
        (NetworkStep.callG v id b))
      (specInst_mapIdle_step_of_step h1 h) (System.mapIdle_unchanged h2)
  | callLoop l' id b hl t1 hin h =>
    obtain ⟨hp, h1, h2, hlτ⟩ := callLabel_maps hl
    refine roundOverGathers_label_step hlτ
      (roundPrograms_label_step (lp := .callG r id b) hp (by simp) (fun i => ?_)
        (NetworkStep.callG v id b))
      (specInst_mapIdle_step_of_step h1 h) (System.mapIdle_unchanged h2)
    by_cases hi : i = id
    · subst hi
      exact ProgramStep.callLoop (u i) b hin
    · exact ProgramStep.callGIdle (u i) id b (Ne.symm hi)
  | firstGatherTau t1 h => exact roundOverGathers_tau_firstGather h
  | secondGatherTau t2 h => exact roundOverGathers_tau_secondGather h
  | firstGatherReturn id g t1 hin hc h =>
    exact roundOverGathers_event_step (.firstGatherReturn id g)
      (roundPrograms_label_step (lp := .firstGatherReturn id g) (by simp) (by simp)
        (dirac_steps_update (ProgramStep.firstGatherReturn (u id) g hin hc)
          (fun i hi => ProgramStep.firstGatherReturnIdle (u i) id g (Ne.symm hi)))
        (NetworkStep.firstGatherReturn v id g))
      (specInst_mapIdle_step_of_step (by simp) h) (System.mapIdle_unchanged (by simp))
  | firstGatherReturnLoop id g t1 hloop h =>
    refine roundOverGathers_event_step (.firstGatherReturn id g)
      (roundPrograms_label_step (lp := .firstGatherReturn id g) (by simp) (by simp) (fun i => ?_)
        (NetworkStep.firstGatherReturn v id g))
      (specInst_mapIdle_step_of_step (by simp) h) (System.mapIdle_unchanged (by simp))
    by_cases hi : i = id
    · subst hi
      exact ProgramStep.firstGatherReturnLoop (u i) g hloop
    · exact ProgramStep.firstGatherReturnIdle (u i) id g (Ne.symm hi)
  | firstGatherCore C hC =>
    exact roundOverGathers_event_step (.firstGatherCore C)
      (roundPrograms_label_step (lp := .firstGatherCore C) (by simp) (by simp)
        (fun i => ProgramStep.firstGatherCoreIdle (u i) C) (NetworkStep.firstGatherCore v C))
      (specInst_mapIdle_step_of_step (by simp) (Gather.Step.announceCore c C hC))
      (System.mapIdle_unchanged (by simp))
  | secondGatherCall id y t2 hc h2 h =>
    exact roundOverGathers_event_step (.secondGatherCall id y)
      (roundPrograms_label_step (lp := .secondGatherCall id y) (by simp) (by simp)
        (dirac_steps_update (ProgramStep.secondGatherCall (u id) y hc h2)
          (fun i hi => ProgramStep.secondGatherCallIdle (u i) id y (Ne.symm hi)))
        (NetworkStep.secondGatherCall v id y))
      (System.mapIdle_unchanged (by simp)) (specInst_mapIdle_step_of_step (by simp) h)
  | secondGatherReturn id g t2 h2 ho h =>
    exact roundOverGathers_event_step (.secondGatherReturn id g)
      (roundPrograms_label_step (lp := .secondGatherReturn id g) (by simp) (by simp)
        (dirac_steps_update (ProgramStep.secondGatherReturn (u id) g h2 ho)
          (fun i hi => ProgramStep.secondGatherReturnIdle (u i) id g (Ne.symm hi)))
        (NetworkStep.secondGatherReturn v id g))
      (System.mapIdle_unchanged (by simp)) (specInst_mapIdle_step_of_step (by simp) h)
  | secondGatherReturnLoop id g t2 hloop h =>
    refine roundOverGathers_event_step (.secondGatherReturn id g)
      (roundPrograms_label_step (lp := .secondGatherReturn id g) (by simp) (by simp) (fun i => ?_)
        (NetworkStep.secondGatherReturn v id g))
      (System.mapIdle_unchanged (by simp)) (specInst_mapIdle_step_of_step (by simp) h)
    by_cases hi : i = id
    · subst hi
      exact ProgramStep.secondGatherReturnLoop (u i) g hloop
    · exact ProgramStep.secondGatherReturnIdle (u i) id g (Ne.symm hi)
  | retG id out ho hr =>
    exact roundOverGathers_label_step (by simp)
      (roundPrograms_label_step (lp := .retG r id out) (by simp) (by simp)
        (dirac_steps_update (ProgramStep.retG (u id) out ho hr)
          (fun i hi => ProgramStep.retGIdle (u i) id out (Ne.symm hi)))
        (NetworkStep.retG v id out))
      (System.mapIdle_unchanged (by simp)) (System.mapIdle_unchanged (by simp))
  | announceBound C hC hr =>
    exact roundOverGathers_label_step (by simp)
      (roundPrograms_label_step (lp := .boundG r (boundOfCore P C)) (by simp) (by simp)
        (fun i => ProgramStep.boundGIdle (u i) _) (NetworkStep.announceBound v C hC hr))
      (System.mapIdle_unchanged (by simp)) (System.mapIdle_unchanged (by simp))
  | fail id =>
    exact roundOverGathers_label_step (by simp) (roundPrograms_idle_step (by simp))
      (specInst_mapIdle_step_of_step (by simp) (Gather.Step.fail c id))
      (specInst_mapIdle_step_of_step (by simp) (Gather.Step.fail d id))

/-- **The characterisation by the algorithm.** At every label `l`, the `l`-transitions of the
round over the gather specifications are exactly the `l`-transitions of
`AlgorithmOverGatherSpecifications`, on the same state and with the same distribution. -/
theorem roundOverGatherSpecifications_step_iff_algorithm (P : Parameters) (r : ℕ)
    (s : RoundStateOverGatherSpecifications P.n) (l : ExtendedLabel P.n Empty)
    (μ : PMF (RoundStateOverGatherSpecifications P.n)) :
    (roundOverGatherSpecifications P r).step s l μ ↔ AlgorithmOverGatherSpecifications P r s l μ :=
  ⟨roundOverGatherSpecifications_step_algorithm P r s l μ,
    algorithm_roundOverGatherSpecifications_step P r s l μ⟩

end Characterisation

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms roundOverGatherSpecifications_step_iff_algorithm

end GBCA.ByAFW
end ABA
end PLTS
