/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Composition

/-!
# The rows of the round over the gather specifications

`GBCA.ByAFW.StepOverGatherSpecifications` is the rule table of
`GBCA.ByAFW.roundOverGatherSpecifications` (`GBCA/AFW/Composition.lean`) — the `n` graded-agreement
programs beside the layer's network, in parallel with two gather specifications — stated over the
round's state through the four views `programs`, `bound`, `firstGather`, `secondGather`. It is a
relation on that state; the system is the composition.

`roundOverGatherSpecifications_step_iff_row` is the row characterisation: at a shared label `l₀`,
the transitions of the round over the labels `GBCA.ByABDY.gbcaLabelMap` sends to `l₀` are exactly
the `l₀`-rows of `StepOverGatherSpecifications`, on the same state and with the same
distribution.

## The gather tier

A gather instance's own rows are `Gather.Step` (`ABA/Gather/Specification.lean`), and a
row carries them as the hypothesis `Gather.Step P (firstGather s) l₀ (PMF.pure t1)`, as
`GBCA.ByAFW.StepOverGatherSpecifications` does. The specification answers `call id x` on two rows,
the call and the input-enabledness loop, and both sit at the one label
`Gather.Label.call id x` of the lifted specification: the round's `callG` row and
its `callLoop` row therefore carry the same hypothesis, and which of the two
specification rows fires is the gather's own business.

## Corruption

The `fail` row corrupts the two gather instances and leaves the programs and
the round's bound bit untouched. The label is in the round's alphabet, and in
the family of rounds it is the broadcast act that answers it.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation Composition

/-! ### Reading a lifted gather specification through a pullback -/

section SpecRows

variable {X : Type} [DecidableEq X] {P : Parameters} {c c' : Gather.SpecState P.n X}
  {L : RoundLabel P.n} {ψ : RoundLabel P.n → Option (Gather.InstanceLabel P.n X)}

/-- A lifted gather specification's step at an interface label on the left is
the specification's own step there. -/
theorem specificationOverInstanceAlphabet_step {l₀ : Gather.Label P.n X} (hψ : ψ L = some (Sum.inl
  l₀))
    (h : ((Gather.specificationOverInstanceAlphabet P X).mapIdle ψ).step c L (PMF.pure c')) :
    Gather.Step P c l₀ (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specificationLabelMap_inl l₀) _).mp (Gather.lift_step_some hψ h)

/-- A lifted gather specification's step at the call-loop label is its step at
the call that label stands for. -/
theorem specificationOverInstanceAlphabet_loop_step {id : Fin P.n} {x : X}
    (hψ : ψ L = some (Sum.inr (Gather.LoopLabel.callLoop id x)))
    (h : ((Gather.specificationOverInstanceAlphabet P X).mapIdle ψ).step c L (PMF.pure c')) :
    Gather.Step P c (.call id x) (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specificationLabelMap_callLoop id x) _).mp
    (Gather.lift_step_some hψ h)

/-- A lifted gather specification's silent step is the specification's own. -/
theorem specificationOverInstanceAlphabet_tau_step
    (h : (Gather.specificationOverInstanceAlphabet P X).step c (Silent.τ : Gather.InstanceLabel P.n
      X) (PMF.pure c')) :
    Gather.Step P c Gather.Label.tau (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specificationLabelMap_tau P.n X) _).mp h

/-- Build a lifted gather specification's step at an interface label on the
left. -/
theorem row_specificationOverInstanceAlphabet_step {l₀ : Gather.Label P.n X} (hψ : ψ L = some
  (Sum.inl l₀))
    (h : Gather.Step P c l₀ (PMF.pure c')) :
    ((Gather.specificationOverInstanceAlphabet P X).mapIdle ψ).step c L (PMF.pure c') :=
  Gather.row_lift_step hψ ((System.mapIdle_step_some (Gather.specificationLabelMap_inl l₀) _).mpr h)

/-- Build a lifted gather specification's step at the call-loop label. -/
theorem row_specificationOverInstanceAlphabet_loop_step {id : Fin P.n} {x : X}
    (hψ : ψ L = some (Sum.inr (Gather.LoopLabel.callLoop id x)))
    (h : Gather.Step P c (.call id x) (PMF.pure c')) :
    ((Gather.specificationOverInstanceAlphabet P X).mapIdle ψ).step c L (PMF.pure c') :=
  Gather.row_lift_step hψ ((System.mapIdle_step_some (Gather.specificationLabelMap_callLoop id x)
    _).mpr h)

/-- Build a lifted gather specification's silent step. -/
theorem row_specificationOverInstanceAlphabet_tau_step (h : Gather.Step P c Gather.Label.tau
  (PMF.pure c')) :
    (Gather.specificationOverInstanceAlphabet P X).step c (Silent.τ : Gather.InstanceLabel P.n X)
      (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specificationLabelMap_tau P.n X) _).mpr h

/-- The one corruption row of the gather specification. -/
theorem specStep_fail {id : Fin P.n} {μ : PMF (Gather.SpecState P.n X)}
    (h : Gather.Step P c (.fail id) μ) : μ = PMF.pure (c.corrupt P id) := by cases h; rfl

end SpecRows

/-! ### The rows -/

/-- The rows of the round over the gather specifications
  (`GBCA.ByAFW.roundOverGatherSpecifications`),
stated over the round's state: one constructor per case of
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_row`. All transitions are Dirac. -/
inductive StepOverGatherSpecifications (P : Parameters) (r : ℕ) :
    RoundStateOverGatherSpecifications P.n → Label P.n → PMF (RoundStateOverGatherSpecifications
      P.n) → Prop
  /-- The call arrives: program `id` records the input and the first gather
  takes the call. -/
  | callG (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (b : Bool)
      (t1 : Gather.SpecState P.n Bool) (h0 : (programs s id).input = none)
      (h : Gather.Step P (firstGather s) (.call id b) (PMF.pure t1)) :
      StepOverGatherSpecifications P r s (.callG r id b)
        (PMF.pure (setFirstGather (setPrograms s (Function.update (programs s) id
          { programs s id with input := some b })) t1))
  /-- The call loop: no program moves and the first gather takes the call. -/
  | callLoop (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (b : Bool)
      (t1 : Gather.SpecState P.n Bool)
      (h : Gather.Step P (firstGather s) (.call id b) (PMF.pure t1)) :
      StepOverGatherSpecifications P r s (.callG r id b) (PMF.pure (setFirstGather s t1))
  /-- An internal step of the first gather. -/
  | firstGatherTau (s : RoundStateOverGatherSpecifications P.n) (t1 : Gather.SpecState P.n Bool)
      (h : Gather.Step P (firstGather s) Gather.Label.tau (PMF.pure t1)) :
      StepOverGatherSpecifications P r s .tau (PMF.pure (setFirstGather s t1))
  /-- An internal step of the second gather. -/
  | secondGatherTau (s : RoundStateOverGatherSpecifications P.n) (t2 : Gather.SpecState P.n (Option
    Bool))
      (h : Gather.Step P (secondGather s) Gather.Label.tau (PMF.pure t2)) :
      StepOverGatherSpecifications P r s .tau (PMF.pure (setSecondGather s t2))
  /-- The first gather returns to `id`: program `id` records the candidate, and
  the round's bound bit is written from the core the return carries if it is
  unwritten. -/
  | firstGatherReturn (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (g : Fin P.n →
    Option Bool)
      (C : Gather.AcceptedPairs P.n Bool) (t1 : Gather.SpecState P.n Bool)
      (hin : (programs s id).input ≠ none) (hc : (programs s id).candidate = none)
      (h : Gather.Step P (firstGather s) (.ret id g C) (PMF.pure t1)) :
      StepOverGatherSpecifications P r s .tau
        (PMF.pure (setBound (setFirstGather (setPrograms s (Function.update (programs s) id
            { programs s id with candidate := some (candidate P g) })) t1)
          (some ((bound s).getD (boundOfCore P C)))))
  /-- Program `id` calls the second gather with the candidate it holds. -/
  | secondGatherCall (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (x : Option Bool)
      (t2 : Gather.SpecState P.n (Option Bool)) (hc : (programs s id).candidate = some x)
      (h2 : (programs s id).called2 = false)
      (h : Gather.Step P (secondGather s) (.call id x) (PMF.pure t2)) :
      StepOverGatherSpecifications P r s .tau
        (PMF.pure (setSecondGather (setPrograms s (Function.update (programs s) id
          { programs s id with called2 := true })) t2))
  /-- The second gather returns to `id`: program `id` records the grade. -/
  | secondGatherReturn (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (g : Fin P.n →
    Option (Option
    Bool))
      (C : Gather.AcceptedPairs P.n (Option Bool)) (t2 : Gather.SpecState P.n (Option Bool))
      (h2 : (programs s id).called2 = true) (ho : (programs s id).out = none)
      (h : Gather.Step P (secondGather s) (.ret id g C) (PMF.pure t2)) :
      StepOverGatherSpecifications P r s .tau
        (PMF.pure (setSecondGather (setPrograms s (Function.update (programs s) id
          { programs s id with out := some (gradeOf P g) })) t2))
  /-- The round returns the grade program `id` holds, announcing the round's
  bound bit. The return announces the grade and the record drops it. -/
  | retG (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) (out : GBCAOutput)
      (ho : (programs s id).out = some out) (hr : (programs s id).returned = false) :
      StepOverGatherSpecifications P r s (.retG r id out ((bound s).getD (boundOfCore P ∅)))
        (PMF.pure (setPrograms s (Function.update (programs s) id
          { programs s id with out := none, returned := true })))
  /-- Corruption (deviation D1): the two gather instances corrupted in
  lockstep, the programs and the round's bound bit untouched. -/
  | fail (s : RoundStateOverGatherSpecifications P.n) (id : Fin P.n) :
      StepOverGatherSpecifications P r s (.fail id)
        (PMF.pure (corruptAll P id (Gather.SpecState.corrupt P)
          (Gather.SpecState.corrupt P) s))

/-! ### The row characterisation -/

/-- **The projection.** -/
theorem roundOverGatherSpecifications_step_row (P : Parameters) (r : ℕ) :
    ∀ (s : RoundStateOverGatherSpecifications P.n) (l : ExtendedLabel P.n) (μ : PMF
      (RoundStateOverGatherSpecifications P.n)),
      (roundOverGatherSpecifications P r).step s l μ →
      ∃ l₀, GBCA.ByABDY.gbcaLabelMap P.n l = some l₀ ∧ StepOverGatherSpecifications P r s l₀ μ := by
  have h1 : (Gather.specificationOverInstanceAlphabet P Bool).IsLTS :=
    Gather.specificationOverInstanceAlphabet_isLTS P
  have h2 : (Gather.specificationOverInstanceAlphabet P (Option Bool)).IsLTS :=
    Gather.specificationOverInstanceAlphabet_isLTS P
  rintro ⟨⟨u, v⟩, c, d⟩ l μ hstep
  rcases (roundOverGathers_step_iff P r (Gather.specificationOverInstanceAlphabet P Bool)
      (Gather.specificationOverInstanceAlphabet P (Option Bool)) _ l μ).mp hstep with ⟨rfl, e,
        hev⟩ | hlab
  · obtain ⟨x, v', c', d', rfl, hlayer, hga1, hga2⟩ :=
      roundOverGathersExtended_joint_inv h1 h2 (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | firstGatherReturn id g C =>
      obtain ⟨hproc,
        hnet⟩ := roundPrograms_label_pure (lp := .firstGatherReturn id g C) (by simp) (by simp)
          hlayer
      obtain ⟨hin, hc, hxid⟩ := programStep_firstGatherReturn_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_firstGatherReturn_foreign (Ne.symm hi) (hproc
          i))
      have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
      have hv : v' = some (v.getD (boundOfCore P C)) := PMF.pure_injective
        (networkStep_firstGatherReturn hnet)
      have hg1 : Gather.Step P c (.ret id g C) (PMF.pure c') :=
        specificationOverInstanceAlphabet_step (by simp) hga1
      have hd : d' = d := Gather.lift_step_none (by simp) hga2
      subst hx; subst hv; subst hd
      exact StepOverGatherSpecifications.firstGatherReturn _ id g C c' hin hc hg1
    | secondGatherCall id y =>
      obtain ⟨hproc,
        hnet⟩ := roundPrograms_label_pure (lp := .secondGatherCall id y) (by simp) (by simp) hlayer
      obtain ⟨hc, h2', hxid⟩ := programStep_secondGatherCall_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_secondGatherCall_foreign (Ne.symm hi) (hproc i))
      have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
      have hv : v' = v := PMF.pure_injective (networkStep_secondGatherCall hnet)
      have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
      have hg2 : Gather.Step P d (.call id y) (PMF.pure d') :=
        specificationOverInstanceAlphabet_step (by simp) hga2
      subst hx; subst hv; subst hc1
      exact StepOverGatherSpecifications.secondGatherCall _ id y d' hc h2' hg2
    | secondGatherReturn id g C =>
      obtain ⟨hproc,
        hnet⟩ := roundPrograms_label_pure (lp := .secondGatherReturn id g C) (by simp) (by simp)
          hlayer
      obtain ⟨h2', ho, hxid⟩ := programStep_secondGatherReturn_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_secondGatherReturn_foreign (Ne.symm hi) (hproc
          i))
      have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
      have hv : v' = v := PMF.pure_injective (networkStep_secondGatherReturn hnet)
      have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
      have hg2 : Gather.Step P d (.ret id g C) (PMF.pure d') :=
        specificationOverInstanceAlphabet_step (by simp) hga2
      subst hx; subst hv; subst hc1
      exact StepOverGatherSpecifications.secondGatherReturn _ id g C d' h2' ho hg2
  · by_cases hlτ : l = Sum.inl Label.tau
    · subst hlτ
      refine ⟨Label.tau, rfl, ?_⟩
      rcases roundOverGathersExtended_tau_inv h1 h2 hlab with ⟨c', rfl, hs⟩ | ⟨d', rfl, hs⟩
      · exact StepOverGatherSpecifications.firstGatherTau _ c'
          (specificationOverInstanceAlphabet_tau_step
          hs)
      · exact StepOverGatherSpecifications.secondGatherTau _ d'
          (specificationOverInstanceAlphabet_tau_step
          hs)
    · obtain ⟨x, v', c', d', rfl, hlayer, hga1, hga2⟩ :=
        roundOverGathersExtended_joint_inv h1 h2 (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | retABA id b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | callW r' id => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | retW r' id b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | callG r' id b =>
          obtain ⟨hproc,
            hnet⟩ := roundPrograms_label_pure (lp := .callG r' id b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := programStep_callG_round (hproc id)
          obtain ⟨h0, hxid⟩ := programStep_callG_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_callG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
          have hv : v' = v := PMF.pure_injective (networkStep_callG hnet)
          have hg1 : Gather.Step P c (.call id b) (PMF.pure c') :=
            specificationOverInstanceAlphabet_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, StepOverGatherSpecifications.callG _ id b c' h0 hg1⟩
        | retG r' id out bnd =>
          obtain ⟨hproc, hnet⟩ :=
            roundPrograms_label_pure (lp := .retG r' id out bnd) (by simp) (by simp) hlayer
          obtain rfl : r' = r := programStep_retG_round (hproc id)
          obtain ⟨ho, hr, hxid⟩ := programStep_retG_own (hproc id)
          obtain ⟨rfl, hv⟩ := networkStep_retG hnet
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_retG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
          have hv' : v' = v := PMF.pure_injective hv
          have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv'; subst hc1; subst hd
          exact ⟨_, rfl, StepOverGatherSpecifications.retG _ id out ho hr⟩
        | fail id =>
          obtain ⟨hx, hv⟩ := roundPrograms_idle_pure (by simp) hlayer
          have hg1 : Gather.Step P c (.fail id) (PMF.pure c') :=
            specificationOverInstanceAlphabet_step (by simp) hga1
          have hg2 : Gather.Step P d (.fail id) (PMF.pure d') :=
            specificationOverInstanceAlphabet_step (by simp) hga2
          have hc1 : c' = c.corrupt P id := PMF.pure_injective (specStep_fail hg1)
          have hd1 : d' = d.corrupt P id := PMF.pure_injective (specStep_fail hg2)
          subst hx; subst hv; subst hc1; subst hd1
          exact ⟨_, rfl, StepOverGatherSpecifications.fail _ id⟩
      | inr ev =>
        cases ev with
        | gbcaSend r' j m => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | gbcaDeliver r' i j m => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | decidedSend j b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | decidedDeliver i j b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | retWPublish r' id cc b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | byzantineCallW r' k => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | byzantineRetW r' k b => exact (roundPrograms_outside_inv (by simp) hlayer).elim
        | gbcaCallLoop r' id b =>
          obtain ⟨hproc, hnet⟩ :=
            roundPrograms_label_pure (lp := .callLoop r' id b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := programStep_callLoop_round (hproc id)
          have hx : x = u := funext fun i => PMF.pure_injective (programStep_callLoop (hproc i))
          have hv : v' = v := PMF.pure_injective (networkStep_callLoop hnet)
          have hg1 : Gather.Step P c (.call id b) (PMF.pure c') :=
            specificationOverInstanceAlphabet_loop_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, StepOverGatherSpecifications.callLoop _ id b c' hg1⟩
        | byzantineCallG r' k b =>
          obtain ⟨hproc,
            hnet⟩ := roundPrograms_label_pure (lp := .callG r' k b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := programStep_callG_round (hproc k)
          obtain ⟨h0, hxid⟩ := programStep_callG_own (hproc k)
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_callG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
          have hv : v' = v := PMF.pure_injective (networkStep_callG hnet)
          have hg1 : Gather.Step P c (.call k b) (PMF.pure c') :=
            specificationOverInstanceAlphabet_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, StepOverGatherSpecifications.callG _ k b c' h0 hg1⟩
        | byzantineCallGLoop r' k b =>
          obtain ⟨hproc, hnet⟩ :=
            roundPrograms_label_pure (lp := .callLoop r' k b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := programStep_callLoop_round (hproc k)
          have hx : x = u := funext fun i => PMF.pure_injective (programStep_callLoop (hproc i))
          have hv : v' = v := PMF.pure_injective (networkStep_callLoop hnet)
          have hg1 : Gather.Step P c (.call k b) (PMF.pure c') :=
            specificationOverInstanceAlphabet_loop_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, StepOverGatherSpecifications.callLoop _ k b c' hg1⟩
        | byzantineRetG r' k out bnd =>
          obtain ⟨hproc, hnet⟩ :=
            roundPrograms_label_pure (lp := .retG r' k out bnd) (by simp) (by simp) hlayer
          obtain rfl : r' = r := programStep_retG_round (hproc k)
          obtain ⟨ho, hr, hxid⟩ := programStep_retG_own (hproc k)
          obtain ⟨rfl, hv⟩ := networkStep_retG hnet
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_retG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funUpdate (PMF.pure_injective hxid) hfor
          have hv' : v' = v := PMF.pure_injective hv
          have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv'; subst hc1; subst hd
          exact ⟨_, rfl, StepOverGatherSpecifications.retG _ k out ho hr⟩

/-- **The embedding.** -/
theorem row_roundOverGatherSpecifications_step (P : Parameters) (r : ℕ) :
    ∀ (s : RoundStateOverGatherSpecifications P.n) (l₀ : Label P.n) (μ : PMF
      (RoundStateOverGatherSpecifications P.n)),
      StepOverGatherSpecifications P r s l₀ μ →
      ∃ l,
        GBCA.ByABDY.gbcaLabelMap P.n l = some l₀ ∧ (roundOverGatherSpecifications P r).step s l μ :=
          by
  rintro ⟨⟨u, v⟩, c, d⟩ l₀ μ hrow
  cases hrow with
  | callG id b t1 h0 h =>
    have hlayer : (roundPrograms P r).step (u, v) (Sum.inl (Sum.inl (Label.callG r id b)))
        (PMF.pure (Function.update u id { u id with input := some b }, v)) :=
      roundPrograms_label_step (lp := .callG r id b) (by simp) (by simp)
        (programStep_update (ProgramStep.callG (u id) b h0)
          (fun i hi => ProgramStep.callGIdle (u i) id b (Ne.symm hi)))
        (NetworkStep.callG v id b)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inl (Sum.inl (Label.callG r id b))) (PMF.pure t1) :=
      row_specificationOverInstanceAlphabet_step (by simp) h
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inl (Sum.inl (Label.callG r id b))) (PMF.pure d) := Gather.lift_idle (by simp)
    exact ⟨Sum.inl (.callG r id b), rfl, roundOverGathers_label_step (by simp) hlayer hg1 hg2⟩
  | callLoop id b t1 h =>
    have hlayer : (roundPrograms P r).step (u,
        v) (Sum.inl (Sum.inr (Implementation.NetworkEvent.gbcaCallLoop r id b))) (PMF.pure (u,
          v)) := by
      refine roundPrograms_label_step (lp := .callLoop r id b) (by simp) (by simp) (fun i => ?_)
        (NetworkStep.callLoop v id b)
      by_cases hi : i = id
      · subst hi; exact ProgramStep.callLoop (u i) b
      · exact ProgramStep.callLoopIdle (u i) id b (Ne.symm hi)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inl (Sum.inr (Implementation.NetworkEvent.gbcaCallLoop r id b))) (PMF.pure t1) :=
      row_specificationOverInstanceAlphabet_loop_step (by simp) h
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inl (Sum.inr (Implementation.NetworkEvent.gbcaCallLoop r id b))) (PMF.pure d) :=
      Gather.lift_idle (by simp)
    exact ⟨Sum.inr (.gbcaCallLoop r id b), rfl,
      roundOverGathers_label_step (by simp) hlayer hg1 hg2⟩
  | firstGatherTau t1 h =>
    exact ⟨Sum.inl Label.tau, rfl,
      roundOverGathers_tau_firstGather (row_specificationOverInstanceAlphabet_tau_step h)⟩
  | secondGatherTau t2 h =>
    exact ⟨Sum.inl Label.tau, rfl,
      roundOverGathers_tau_secondGather (row_specificationOverInstanceAlphabet_tau_step h)⟩
  | firstGatherReturn id g C t1 hin hc h =>
    have hlayer : (roundPrograms P r).step (u, v) (Sum.inr (RoundEvent.firstGatherReturn id g C))
        (PMF.pure (Function.update u id { u id with candidate := some (candidate P g) },
          some (v.getD (boundOfCore P C)))) :=
      roundPrograms_label_step (lp := .firstGatherReturn id g C) (by simp) (by simp)
        (programStep_update (ProgramStep.firstGatherReturn (u id) g C hin hc)
          (fun i hi => ProgramStep.firstGatherReturnIdle (u i) id g C (Ne.symm hi)))
        (NetworkStep.firstGatherReturn v id g C)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inr (RoundEvent.firstGatherReturn id g C)) (PMF.pure t1) :=
          row_specificationOverInstanceAlphabet_step (by simp) h
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inr (RoundEvent.firstGatherReturn id g C)) (PMF.pure d) := Gather.lift_idle (by simp)
    exact ⟨Sum.inl Label.tau, rfl, roundOverGathers_event_step _ hlayer hg1 hg2⟩
  | secondGatherCall id y t2 hc h2 h =>
    have hlayer : (roundPrograms P r).step (u, v) (Sum.inr (RoundEvent.secondGatherCall id y))
        (PMF.pure (Function.update u id { u id with called2 := true }, v)) :=
      roundPrograms_label_step (lp := .secondGatherCall id y) (by simp) (by simp)
        (programStep_update (ProgramStep.secondGatherCall (u id) y hc h2)
          (fun i hi => ProgramStep.secondGatherCallIdle (u i) id y (Ne.symm hi)))
        (NetworkStep.secondGatherCall v id y)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inr (RoundEvent.secondGatherCall id y)) (PMF.pure c) := Gather.lift_idle (by simp)
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inr (RoundEvent.secondGatherCall id y)) (PMF.pure t2) :=
          row_specificationOverInstanceAlphabet_step (by simp) h
    exact ⟨Sum.inl Label.tau, rfl, roundOverGathers_event_step _ hlayer hg1 hg2⟩
  | secondGatherReturn id g C t2 h2 ho h =>
    have hlayer : (roundPrograms P r).step (u, v) (Sum.inr (RoundEvent.secondGatherReturn id g C))
        (PMF.pure (Function.update u id { u id with out := some (gradeOf P g) }, v)) :=
      roundPrograms_label_step (lp := .secondGatherReturn id g C) (by simp) (by simp)
        (programStep_update (ProgramStep.secondGatherReturn (u id) g C h2 ho)
          (fun i hi => ProgramStep.secondGatherReturnIdle (u i) id g C (Ne.symm hi)))
        (NetworkStep.secondGatherReturn v id g C)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inr (RoundEvent.secondGatherReturn id g C)) (PMF.pure c) := Gather.lift_idle (by simp)
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inr (RoundEvent.secondGatherReturn id g C)) (PMF.pure t2) :=
          row_specificationOverInstanceAlphabet_step (by simp) h
    exact ⟨Sum.inl Label.tau, rfl, roundOverGathers_event_step _ hlayer hg1 hg2⟩
  | retG id out ho hr =>
    have hlayer : (roundPrograms P r).step (u, v)
        (Sum.inl (Sum.inl (Label.retG r id out (v.getD (boundOfCore P ∅)))))
        (PMF.pure (Function.update u id { u id with out := none, returned := true }, v)) :=
      roundPrograms_label_step (lp := .retG r id out (v.getD (boundOfCore P ∅))) (by simp) (by simp)
        (programStep_update (ProgramStep.retG (u id) out _ ho hr)
          (fun i hi => ProgramStep.retGIdle (u i) id out _ (Ne.symm hi)))
        (NetworkStep.retG v id out)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inl (Sum.inl (Label.retG r id out (v.getD (boundOfCore P ∅))))) (PMF.pure c) :=
      Gather.lift_idle (by simp)
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inl (Sum.inl (Label.retG r id out (v.getD (boundOfCore P ∅))))) (PMF.pure d) :=
      Gather.lift_idle (by simp)
    exact ⟨Sum.inl (.retG r id out (v.getD (boundOfCore P ∅))), rfl,
      roundOverGathers_label_step (by simp) hlayer hg1 hg2⟩
  | fail id =>
    have hlayer : (roundPrograms P r).step (u, v) (Sum.inl (Sum.inl (Label.fail id)))
        (PMF.pure (u, v)) := roundPrograms_idle_step (by simp)
    have hg1 : ((Gather.specificationOverInstanceAlphabet P Bool).mapIdle (firstGatherLabelMap
      P.n)).step c
        (Sum.inl (Sum.inl (Label.fail id))) (PMF.pure (c.corrupt P id)) :=
      row_specificationOverInstanceAlphabet_step (by simp) (Gather.Step.fail c id)
    have hg2 : ((Gather.specificationOverInstanceAlphabet P (Option Bool)).mapIdle
      (secondGatherLabelMap P.n)).step d
        (Sum.inl (Sum.inl (Label.fail id))) (PMF.pure (d.corrupt P id)) :=
      row_specificationOverInstanceAlphabet_step (by simp) (Gather.Step.fail d id)
    exact ⟨Sum.inl (.fail id), rfl, roundOverGathers_label_step (by simp) hlayer hg1 hg2⟩

/-- **The row characterisation.** At a shared label `l₀`, the transitions of
the round over the labels `GBCA.ByABDY.gbcaLabelMap` sends to `l₀` are exactly the `l₀`-rows
of `StepOverGatherSpecifications`, on the same state and with the same distribution. -/
theorem roundOverGatherSpecifications_step_iff_row (P : Parameters) (r : ℕ) (s :
  RoundStateOverGatherSpecifications P.n) (l₀ : Label P.n)
    (μ : PMF (RoundStateOverGatherSpecifications P.n)) :
    (∃ l,
      GBCA.ByABDY.gbcaLabelMap P.n l = some l₀ ∧ (roundOverGatherSpecifications P r).step s l μ) ↔
        StepOverGatherSpecifications P r s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := roundOverGatherSpecifications_step_row P r s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_roundOverGatherSpecifications_step P r s l₀ μ

/-- info: 'PLTS.ABA.GBCA.ByAFW.roundOverGatherSpecifications_step_iff_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms roundOverGatherSpecifications_step_iff_row

end GBCA.ByAFW
end ABA
end PLTS
