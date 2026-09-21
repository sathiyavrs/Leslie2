/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Composition

/-!
# The rows of the round over the gather specifications

`GBCA.ByAFW.PairStep` is the rule table of `GBCA.ByAFW.pairInst` (`GBCA/AFW/Composition.lean`) —
the `n` graded-agreement programs beside the layer's network, in parallel with
two gather specifications — stated over the round's state through the four
views `procs`, `bound`, `ga1`, `ga2`. It is a relation on that state; the
system is the composition.

`pairInst_step_iff_row` is the row characterisation: at a shared label `l₀`, the
transitions of the round over the labels `GBCA.ByABDY.gPull` sends to `l₀` are exactly
the `l₀`-rows of `PairStep`, on the same state and with the same
distribution.

## The gather tier

A gather instance's own rows are `Gather.Step` (`ABA/Gather/Specification.lean`), and a
row carries them as the hypothesis `Gather.Step P (ga1 s) l₀ (PMF.pure t1)`, as
`GBCA.ByAFW.PairStep` does. The specification answers `call id x` on two rows, the
call and the input-enabledness loop, and both sit at the one label
`Gather.Lab.call id x` of the lifted specification: the round's `callG` row and
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

variable {X : Type} [DecidableEq X] {P : Params} {c c' : Gather.SpecState P.n X}
  {L : RLab P.n} {ψ : RLab P.n → Option (Gather.InstLab P.n X)}

/-- A lifted gather specification's step at an interface label on the left is
the specification's own step there. -/
theorem liftedSpec_step {l₀ : Gather.Lab P.n X} (hψ : ψ L = some (Sum.inl l₀))
    (h : ((Gather.liftedSpec P X).mapIdle ψ).step c L (PMF.pure c')) :
    Gather.Step P c l₀ (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specPull_inl l₀) _).mp (Gather.lift_step_some hψ h)

/-- A lifted gather specification's step at the call-loop label is its step at
the call that label stands for. -/
theorem liftedSpec_loop_step {id : Fin P.n} {x : X}
    (hψ : ψ L = some (Sum.inr (Gather.Extra.callLoop id x)))
    (h : ((Gather.liftedSpec P X).mapIdle ψ).step c L (PMF.pure c')) :
    Gather.Step P c (.call id x) (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specPull_callLoop id x) _).mp (Gather.lift_step_some hψ h)

/-- A lifted gather specification's silent step is the specification's own. -/
theorem liftedSpec_tau_step
    (h : (Gather.liftedSpec P X).step c (Silent.τ : Gather.InstLab P.n X) (PMF.pure c')) :
    Gather.Step P c Gather.Lab.tau (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specPull_tau P.n X) _).mp h

/-- Build a lifted gather specification's step at an interface label on the
left. -/
theorem row_liftedSpec_step {l₀ : Gather.Lab P.n X} (hψ : ψ L = some (Sum.inl l₀))
    (h : Gather.Step P c l₀ (PMF.pure c')) :
    ((Gather.liftedSpec P X).mapIdle ψ).step c L (PMF.pure c') :=
  Gather.row_lift_step hψ ((System.mapIdle_step_some (Gather.specPull_inl l₀) _).mpr h)

/-- Build a lifted gather specification's step at the call-loop label. -/
theorem row_liftedSpec_loop_step {id : Fin P.n} {x : X}
    (hψ : ψ L = some (Sum.inr (Gather.Extra.callLoop id x)))
    (h : Gather.Step P c (.call id x) (PMF.pure c')) :
    ((Gather.liftedSpec P X).mapIdle ψ).step c L (PMF.pure c') :=
  Gather.row_lift_step hψ ((System.mapIdle_step_some (Gather.specPull_callLoop id x) _).mpr h)

/-- Build a lifted gather specification's silent step. -/
theorem row_liftedSpec_tau_step (h : Gather.Step P c Gather.Lab.tau (PMF.pure c')) :
    (Gather.liftedSpec P X).step c (Silent.τ : Gather.InstLab P.n X) (PMF.pure c') :=
  (System.mapIdle_step_some (Gather.specPull_tau P.n X) _).mpr h

/-- The one corruption row of the gather specification. -/
theorem specStep_fail {id : Fin P.n} {μ : PMF (Gather.SpecState P.n X)}
    (h : Gather.Step P c (.fail id) μ) : μ = PMF.pure (c.corrupt P id) := by cases h; rfl

end SpecRows

/-! ### The rows -/

/-- The rows of the round over the gather specifications (`GBCA.ByAFW.pairInst`),
stated over the round's state: one constructor per case of
`GBCA.ByAFW.pairInst_step_iff_row`. All transitions are Dirac. -/
inductive PairStep (P : Params) (r : ℕ) :
    PairState P.n → Lab P.n → PMF (PairState P.n) → Prop
  /-- The call arrives: program `id` records the input and the first gather
  takes the call. -/
  | callG (s : PairState P.n) (id : Fin P.n) (b : Bool)
      (t1 : Gather.SpecState P.n Bool) (h0 : (procs s id).input = none)
      (h : Gather.Step P (ga1 s) (.call id b) (PMF.pure t1)) :
      PairStep P r s (.callG r id b)
        (PMF.pure (setGa1 (setProcs s (Function.update (procs s) id
          { procs s id with input := some b })) t1))
  /-- The call loop: no program moves and the first gather takes the call. -/
  | callLoop (s : PairState P.n) (id : Fin P.n) (b : Bool)
      (t1 : Gather.SpecState P.n Bool)
      (h : Gather.Step P (ga1 s) (.call id b) (PMF.pure t1)) :
      PairStep P r s (.callG r id b) (PMF.pure (setGa1 s t1))
  /-- An internal step of the first gather. -/
  | ga1Tau (s : PairState P.n) (t1 : Gather.SpecState P.n Bool)
      (h : Gather.Step P (ga1 s) Gather.Lab.tau (PMF.pure t1)) :
      PairStep P r s .tau (PMF.pure (setGa1 s t1))
  /-- An internal step of the second gather. -/
  | ga2Tau (s : PairState P.n) (t2 : Gather.SpecState P.n (Option Bool))
      (h : Gather.Step P (ga2 s) Gather.Lab.tau (PMF.pure t2)) :
      PairStep P r s .tau (PMF.pure (setGa2 s t2))
  /-- The first gather returns to `id`: program `id` records the candidate, and
  the round's bound bit is written from the core the return carries if it is
  unwritten. -/
  | ret1 (s : PairState P.n) (id : Fin P.n) (g : Fin P.n → Option Bool)
      (C : Gather.APSet P.n Bool) (t1 : Gather.SpecState P.n Bool)
      (hin : (procs s id).input ≠ none) (hc : (procs s id).cand = none)
      (h : Gather.Step P (ga1 s) (.ret id g C) (PMF.pure t1)) :
      PairStep P r s .tau
        (PMF.pure (setBound (setGa1 (setProcs s (Function.update (procs s) id
            { procs s id with cand := some (cand P g) })) t1)
          (some ((bound s).getD (boundOfCore P C)))))
  /-- Program `id` calls the second gather with the candidate it holds. -/
  | call2 (s : PairState P.n) (id : Fin P.n) (x : Option Bool)
      (t2 : Gather.SpecState P.n (Option Bool)) (hc : (procs s id).cand = some x)
      (h2 : (procs s id).called2 = false)
      (h : Gather.Step P (ga2 s) (.call id x) (PMF.pure t2)) :
      PairStep P r s .tau
        (PMF.pure (setGa2 (setProcs s (Function.update (procs s) id
          { procs s id with called2 := true })) t2))
  /-- The second gather returns to `id`: program `id` records the grade. -/
  | ret2 (s : PairState P.n) (id : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.APSet P.n (Option Bool)) (t2 : Gather.SpecState P.n (Option Bool))
      (h2 : (procs s id).called2 = true) (ho : (procs s id).out = none)
      (h : Gather.Step P (ga2 s) (.ret id g C) (PMF.pure t2)) :
      PairStep P r s .tau
        (PMF.pure (setGa2 (setProcs s (Function.update (procs s) id
          { procs s id with out := some (gradeOf P g) })) t2))
  /-- The round returns the grade program `id` holds, announcing the round's
  bound bit. The return announces the grade and the record drops it. -/
  | retG (s : PairState P.n) (id : Fin P.n) (out : GbcaOut)
      (ho : (procs s id).out = some out) (hr : (procs s id).returned = false) :
      PairStep P r s (.retG r id out ((bound s).getD (boundOfCore P ∅)))
        (PMF.pure (setProcs s (Function.update (procs s) id
          { procs s id with out := none, returned := true })))
  /-- Corruption (deviation D1): the two gather instances corrupted in
  lockstep, the programs and the round's bound bit untouched. -/
  | fail (s : PairState P.n) (id : Fin P.n) :
      PairStep P r s (.fail id)
        (PMF.pure (corruptAll P id (Gather.SpecState.corrupt P)
          (Gather.SpecState.corrupt P) s))

/-! ### The row characterisation -/

/-- **The projection.** -/
theorem pairInst_step_row (P : Params) (r : ℕ) :
    ∀ (s : PairState P.n) (l : NLab P.n) (μ : PMF (PairState P.n)),
      (pairInst P r).step s l μ →
      ∃ l₀, GBCA.ByABDY.gPull P.n l = some l₀ ∧ PairStep P r s l₀ μ := by
  have h1 : (Gather.liftedSpec P Bool).IsLTS := Gather.liftedSpec_isLTS P
  have h2 : (Gather.liftedSpec P (Option Bool)).IsLTS := Gather.liftedSpec_isLTS P
  rintro ⟨⟨u, v⟩, c, d⟩ l μ hstep
  rcases (roundInstAt_step_iff P r (Gather.liftedSpec P Bool)
      (Gather.liftedSpec P (Option Bool)) _ l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · obtain ⟨x, v', c', d', rfl, hlayer, hga1, hga2⟩ :=
      roundPreAt_joint_inv h1 h2 (by simp) hev
    refine ⟨Lab.tau, rfl, ?_⟩
    cases e with
    | ret1 id g C =>
      obtain ⟨hproc, hnet⟩ := layer_lab_pure (lp := .ret1 id g C) (by simp) (by simp) hlayer
      obtain ⟨hin, hc, hxid⟩ := procStep_ret1_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (procStep_ret1_foreign (Ne.symm hi) (hproc i))
      have hx := Gather.funPin (PMF.pure_injective hxid) hfor
      have hv : v' = some (v.getD (boundOfCore P C)) := PMF.pure_injective (netStep_ret1 hnet)
      have hg1 : Gather.Step P c (.ret id g C) (PMF.pure c') := liftedSpec_step (by simp) hga1
      have hd : d' = d := Gather.lift_step_none (by simp) hga2
      subst hx; subst hv; subst hd
      exact PairStep.ret1 _ id g C c' hin hc hg1
    | call2 id y =>
      obtain ⟨hproc, hnet⟩ := layer_lab_pure (lp := .call2 id y) (by simp) (by simp) hlayer
      obtain ⟨hc, h2', hxid⟩ := procStep_call2_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (procStep_call2_foreign (Ne.symm hi) (hproc i))
      have hx := Gather.funPin (PMF.pure_injective hxid) hfor
      have hv : v' = v := PMF.pure_injective (netStep_call2 hnet)
      have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
      have hg2 : Gather.Step P d (.call id y) (PMF.pure d') := liftedSpec_step (by simp) hga2
      subst hx; subst hv; subst hc1
      exact PairStep.call2 _ id y d' hc h2' hg2
    | ret2 id g C =>
      obtain ⟨hproc, hnet⟩ := layer_lab_pure (lp := .ret2 id g C) (by simp) (by simp) hlayer
      obtain ⟨h2', ho, hxid⟩ := procStep_ret2_own (hproc id)
      have hfor : ∀ i, i ≠ id → x i = u i :=
        fun i hi => PMF.pure_injective (procStep_ret2_foreign (Ne.symm hi) (hproc i))
      have hx := Gather.funPin (PMF.pure_injective hxid) hfor
      have hv : v' = v := PMF.pure_injective (netStep_ret2 hnet)
      have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
      have hg2 : Gather.Step P d (.ret id g C) (PMF.pure d') := liftedSpec_step (by simp) hga2
      subst hx; subst hv; subst hc1
      exact PairStep.ret2 _ id g C d' h2' ho hg2
  · by_cases hlτ : l = Sum.inl Lab.tau
    · subst hlτ
      refine ⟨Lab.tau, rfl, ?_⟩
      rcases roundPreAt_tau_inv h1 h2 hlab with ⟨c', rfl, hs⟩ | ⟨d', rfl, hs⟩
      · exact PairStep.ga1Tau _ c' (liftedSpec_tau_step hs)
      · exact PairStep.ga2Tau _ d' (liftedSpec_tau_step hs)
    · obtain ⟨x, v', c', d', rfl, hlayer, hga1, hga2⟩ :=
        roundPreAt_joint_inv h1 h2 (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (layer_outside_inv (by simp) hlayer).elim
        | retABA id b => exact (layer_outside_inv (by simp) hlayer).elim
        | callW r' id => exact (layer_outside_inv (by simp) hlayer).elim
        | retW r' id b => exact (layer_outside_inv (by simp) hlayer).elim
        | callG r' id b =>
          obtain ⟨hproc, hnet⟩ := layer_lab_pure (lp := .callG r' id b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := procStep_callG_round (hproc id)
          obtain ⟨h0, hxid⟩ := procStep_callG_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (procStep_callG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funPin (PMF.pure_injective hxid) hfor
          have hv : v' = v := PMF.pure_injective (netStep_callG hnet)
          have hg1 : Gather.Step P c (.call id b) (PMF.pure c') := liftedSpec_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, PairStep.callG _ id b c' h0 hg1⟩
        | retG r' id out bnd =>
          obtain ⟨hproc, hnet⟩ :=
            layer_lab_pure (lp := .retG r' id out bnd) (by simp) (by simp) hlayer
          obtain rfl : r' = r := procStep_retG_round (hproc id)
          obtain ⟨ho, hr, hxid⟩ := procStep_retG_own (hproc id)
          obtain ⟨rfl, hv⟩ := netStep_retG hnet
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (procStep_retG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funPin (PMF.pure_injective hxid) hfor
          have hv' : v' = v := PMF.pure_injective hv
          have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv'; subst hc1; subst hd
          exact ⟨_, rfl, PairStep.retG _ id out ho hr⟩
        | fail id =>
          obtain ⟨hx, hv⟩ := layer_idle_pure (by simp) hlayer
          have hg1 : Gather.Step P c (.fail id) (PMF.pure c') := liftedSpec_step (by simp) hga1
          have hg2 : Gather.Step P d (.fail id) (PMF.pure d') := liftedSpec_step (by simp) hga2
          have hc1 : c' = c.corrupt P id := PMF.pure_injective (specStep_fail hg1)
          have hd1 : d' = d.corrupt P id := PMF.pure_injective (specStep_fail hg2)
          subst hx; subst hv; subst hc1; subst hd1
          exact ⟨_, rfl, PairStep.fail _ id⟩
      | inr ev =>
        cases ev with
        | gsnd r' j m => exact (layer_outside_inv (by simp) hlayer).elim
        | gdlv r' i j m => exact (layer_outside_inv (by simp) hlayer).elim
        | dsnd j b => exact (layer_outside_inv (by simp) hlayer).elim
        | ddlv i j b => exact (layer_outside_inv (by simp) hlayer).elim
        | retWPub r' id cc b => exact (layer_outside_inv (by simp) hlayer).elim
        | byzCallW r' k => exact (layer_outside_inv (by simp) hlayer).elim
        | byzRetW r' k b => exact (layer_outside_inv (by simp) hlayer).elim
        | gcallLoop r' id b =>
          obtain ⟨hproc, hnet⟩ :=
            layer_lab_pure (lp := .callLoop r' id b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := procStep_callLoop_round (hproc id)
          have hx : x = u := funext fun i => PMF.pure_injective (procStep_callLoop (hproc i))
          have hv : v' = v := PMF.pure_injective (netStep_callLoop hnet)
          have hg1 : Gather.Step P c (.call id b) (PMF.pure c') :=
            liftedSpec_loop_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, PairStep.callLoop _ id b c' hg1⟩
        | byzCallG r' k b =>
          obtain ⟨hproc, hnet⟩ := layer_lab_pure (lp := .callG r' k b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := procStep_callG_round (hproc k)
          obtain ⟨h0, hxid⟩ := procStep_callG_own (hproc k)
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (procStep_callG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funPin (PMF.pure_injective hxid) hfor
          have hv : v' = v := PMF.pure_injective (netStep_callG hnet)
          have hg1 : Gather.Step P c (.call k b) (PMF.pure c') := liftedSpec_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, PairStep.callG _ k b c' h0 hg1⟩
        | byzCallGLoop r' k b =>
          obtain ⟨hproc, hnet⟩ :=
            layer_lab_pure (lp := .callLoop r' k b) (by simp) (by simp) hlayer
          obtain rfl : r' = r := procStep_callLoop_round (hproc k)
          have hx : x = u := funext fun i => PMF.pure_injective (procStep_callLoop (hproc i))
          have hv : v' = v := PMF.pure_injective (netStep_callLoop hnet)
          have hg1 : Gather.Step P c (.call k b) (PMF.pure c') :=
            liftedSpec_loop_step (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv; subst hd
          exact ⟨_, rfl, PairStep.callLoop _ k b c' hg1⟩
        | byzRetG r' k out bnd =>
          obtain ⟨hproc, hnet⟩ :=
            layer_lab_pure (lp := .retG r' k out bnd) (by simp) (by simp) hlayer
          obtain rfl : r' = r := procStep_retG_round (hproc k)
          obtain ⟨ho, hr, hxid⟩ := procStep_retG_own (hproc k)
          obtain ⟨rfl, hv⟩ := netStep_retG hnet
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (procStep_retG_foreign (Ne.symm hi) (hproc i))
          have hx := Gather.funPin (PMF.pure_injective hxid) hfor
          have hv' : v' = v := PMF.pure_injective hv
          have hc1 : c' = c := Gather.lift_step_none (by simp) hga1
          have hd : d' = d := Gather.lift_step_none (by simp) hga2
          subst hx; subst hv'; subst hc1; subst hd
          exact ⟨_, rfl, PairStep.retG _ k out ho hr⟩

/-- **The embedding.** -/
theorem row_pairInst_step (P : Params) (r : ℕ) :
    ∀ (s : PairState P.n) (l₀ : Lab P.n) (μ : PMF (PairState P.n)),
      PairStep P r s l₀ μ →
      ∃ l, GBCA.ByABDY.gPull P.n l = some l₀ ∧ (pairInst P r).step s l μ := by
  rintro ⟨⟨u, v⟩, c, d⟩ l₀ μ hrow
  cases hrow with
  | callG id b t1 h0 h =>
    have hlayer : (layer P r).step (u, v) (Sum.inl (Sum.inl (Lab.callG r id b)))
        (PMF.pure (Function.update u id { u id with input := some b }, v)) :=
      layer_lab_step (lp := .callG r id b) (by simp) (by simp)
        (procStep_update (ProcStep.callG (u id) b h0)
          (fun i hi => ProcStep.callGIdle (u i) id b (Ne.symm hi)))
        (NetStep.callG v id b)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inl (Sum.inl (Lab.callG r id b))) (PMF.pure t1) :=
      row_liftedSpec_step (by simp) h
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inl (Sum.inl (Lab.callG r id b))) (PMF.pure d) := Gather.lift_idle (by simp)
    exact ⟨Sum.inl (.callG r id b), rfl, roundInstAt_lab_step (by simp) hlayer hg1 hg2⟩
  | callLoop id b t1 h =>
    have hlayer : (layer P r).step (u,
        v) (Sum.inl (Sum.inr (Implementation.NetEvtP.gcallLoop r id b))) (PMF.pure (u, v)) := by
      refine layer_lab_step (lp := .callLoop r id b) (by simp) (by simp) (fun i => ?_)
        (NetStep.callLoop v id b)
      by_cases hi : i = id
      · subst hi; exact ProcStep.callLoop (u i) b
      · exact ProcStep.callLoopIdle (u i) id b (Ne.symm hi)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inl (Sum.inr (Implementation.NetEvtP.gcallLoop r id b))) (PMF.pure t1) :=
      row_liftedSpec_loop_step (by simp) h
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inl (Sum.inr (Implementation.NetEvtP.gcallLoop r id b))) (PMF.pure d) :=
      Gather.lift_idle (by simp)
    exact ⟨Sum.inr (.gcallLoop r id b), rfl, roundInstAt_lab_step (by simp) hlayer hg1 hg2⟩
  | ga1Tau t1 h =>
    exact ⟨Sum.inl Lab.tau, rfl, roundInstAt_tau_ga1 (row_liftedSpec_tau_step h)⟩
  | ga2Tau t2 h =>
    exact ⟨Sum.inl Lab.tau, rfl, roundInstAt_tau_ga2 (row_liftedSpec_tau_step h)⟩
  | ret1 id g C t1 hin hc h =>
    have hlayer : (layer P r).step (u, v) (Sum.inr (REvt.ret1 id g C))
        (PMF.pure (Function.update u id { u id with cand := some (cand P g) },
          some (v.getD (boundOfCore P C)))) :=
      layer_lab_step (lp := .ret1 id g C) (by simp) (by simp)
        (procStep_update (ProcStep.ret1 (u id) g C hin hc)
          (fun i hi => ProcStep.ret1Idle (u i) id g C (Ne.symm hi)))
        (NetStep.ret1 v id g C)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inr (REvt.ret1 id g C)) (PMF.pure t1) := row_liftedSpec_step (by simp) h
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inr (REvt.ret1 id g C)) (PMF.pure d) := Gather.lift_idle (by simp)
    exact ⟨Sum.inl Lab.tau, rfl, roundInstAt_event_step _ hlayer hg1 hg2⟩
  | call2 id y t2 hc h2 h =>
    have hlayer : (layer P r).step (u, v) (Sum.inr (REvt.call2 id y))
        (PMF.pure (Function.update u id { u id with called2 := true }, v)) :=
      layer_lab_step (lp := .call2 id y) (by simp) (by simp)
        (procStep_update (ProcStep.call2 (u id) y hc h2)
          (fun i hi => ProcStep.call2Idle (u i) id y (Ne.symm hi)))
        (NetStep.call2 v id y)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inr (REvt.call2 id y)) (PMF.pure c) := Gather.lift_idle (by simp)
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inr (REvt.call2 id y)) (PMF.pure t2) := row_liftedSpec_step (by simp) h
    exact ⟨Sum.inl Lab.tau, rfl, roundInstAt_event_step _ hlayer hg1 hg2⟩
  | ret2 id g C t2 h2 ho h =>
    have hlayer : (layer P r).step (u, v) (Sum.inr (REvt.ret2 id g C))
        (PMF.pure (Function.update u id { u id with out := some (gradeOf P g) }, v)) :=
      layer_lab_step (lp := .ret2 id g C) (by simp) (by simp)
        (procStep_update (ProcStep.ret2 (u id) g C h2 ho)
          (fun i hi => ProcStep.ret2Idle (u i) id g C (Ne.symm hi)))
        (NetStep.ret2 v id g C)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inr (REvt.ret2 id g C)) (PMF.pure c) := Gather.lift_idle (by simp)
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inr (REvt.ret2 id g C)) (PMF.pure t2) := row_liftedSpec_step (by simp) h
    exact ⟨Sum.inl Lab.tau, rfl, roundInstAt_event_step _ hlayer hg1 hg2⟩
  | retG id out ho hr =>
    have hlayer : (layer P r).step (u, v)
        (Sum.inl (Sum.inl (Lab.retG r id out (v.getD (boundOfCore P ∅)))))
        (PMF.pure (Function.update u id { u id with out := none, returned := true }, v)) :=
      layer_lab_step (lp := .retG r id out (v.getD (boundOfCore P ∅))) (by simp) (by simp)
        (procStep_update (ProcStep.retG (u id) out _ ho hr)
          (fun i hi => ProcStep.retGIdle (u i) id out _ (Ne.symm hi)))
        (NetStep.retG v id out)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inl (Sum.inl (Lab.retG r id out (v.getD (boundOfCore P ∅))))) (PMF.pure c) :=
      Gather.lift_idle (by simp)
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inl (Sum.inl (Lab.retG r id out (v.getD (boundOfCore P ∅))))) (PMF.pure d) :=
      Gather.lift_idle (by simp)
    exact ⟨Sum.inl (.retG r id out (v.getD (boundOfCore P ∅))), rfl,
      roundInstAt_lab_step (by simp) hlayer hg1 hg2⟩
  | fail id =>
    have hlayer : (layer P r).step (u, v) (Sum.inl (Sum.inl (Lab.fail id)))
        (PMF.pure (u, v)) := layer_idle_step (by simp)
    have hg1 : ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)).step c
        (Sum.inl (Sum.inl (Lab.fail id))) (PMF.pure (c.corrupt P id)) :=
      row_liftedSpec_step (by simp) (Gather.Step.fail c id)
    have hg2 : ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)).step d
        (Sum.inl (Sum.inl (Lab.fail id))) (PMF.pure (d.corrupt P id)) :=
      row_liftedSpec_step (by simp) (Gather.Step.fail d id)
    exact ⟨Sum.inl (.fail id), rfl, roundInstAt_lab_step (by simp) hlayer hg1 hg2⟩

/-- **The row characterisation.** At a shared label `l₀`, the transitions of
the round over the labels `GBCA.ByABDY.gPull` sends to `l₀` are exactly the `l₀`-rows
of `PairStep`, on the same state and with the same distribution. -/
theorem pairInst_step_iff_row (P : Params) (r : ℕ) (s : PairState P.n) (l₀ : Lab P.n)
    (μ : PMF (PairState P.n)) :
    (∃ l, GBCA.ByABDY.gPull P.n l = some l₀ ∧ (pairInst P r).step s l μ) ↔ PairStep P r s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := pairInst_step_row P r s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Lab P.n)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_pairInst_step P r s l₀ μ

/-- info: 'PLTS.ABA.GBCA.ByAFW.pairInst_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairInst_step_iff_row

end GBCA.ByAFW
end ABA
end PLTS
