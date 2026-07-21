/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Simulation.Equivalences
import Leslie2.Weak.Bounds

/-!
# Flattening a `𝒟(sys^w)`-internal weak transition (Stage 2)

Stage 2 of the plan for `weakTau_lift_pure` (the last crux of
forward-simulation transitivity): an internal weak transition of the lifted
system `𝒟(sys^w)` out of a Dirac macro-state collapses to an internal weak
transition of `sys` itself:

`weakTau_flatten : weakTau (𝒟(sys^w)) (PMF.pure μ) Ν → weakTau sys μ (Ν.bind id)`

Each single internal macro-step already collapses through the proven bridge
`weakTau_of_hyperStep_weakClosure` (`weakTau_of_distStep` below); the content
of the theorem is the **ω-composition**: countably many a.s.-halting
`sys`-`weakTau`s, glued along an a.s.-halting macro-run, compose into one
a.s.-halting `sys`-`weakTau` whose end-state distribution is the macro
end-state mixture `Ν.bind id`.

Together with Stage 1 (`StrongProbabilisticSimulation.weakTau_lift`) and the
forward⇔strong correspondence, this discharges `weakTau_lift_pure` — see the
reduction in `Simulation/Transitivity.lean`.
-/

open Stream'
open scoped BigOperators

namespace PLTS

variable {State Label : Type} [Silent Label]

/-! ### Layer 0: one macro-step collapses through the proven bridge -/

/-- A single internal step of `𝒟(sys^w)` out of the macro-state `m` is an
internal weak transition of `sys` from `m` to the successor mixture. -/
theorem weakTau_of_distStep {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) :
    weakTau sys m (ω.bind id) := by
  have h' : hyperStep (sys^w) m Silent.τ (ω.bind id) := h
  exact weakTau_of_hyperStep_weakClosure rfl h'

/-! ### The flattening theorem (Stage 2)

The ω-composition. Proven across the layers of this file (finite recursion,
depth stratification, the composite belief scheduler, its integral fixpoint,
and the two halting-integral identities). -/

/-! **Flattening** (`weakTau_flatten`) is stated and proved at the end of the
file, after the decision-point belief scheduler `dSched` it is instantiated
with. -/

/-! ### Layer 1: the finite depth-`n` macro-future recursion -/

/-- Append one internal (`τ`) macro-transition into `m'` onto the macro-history
`E`. -/
def macroExtend (E : AlterSeq (PMF State) Label) (m' : PMF State) :
    AlterSeq (PMF State) Label :=
  ⟨E.init, E.trans.append (Seq.cons (Silent.τ, m') Seq.nil)⟩

/-- The one-step extension of a terminating macro-history again terminates. -/
theorem macroExtend_term {E : AlterSeq (PMF State) Label}
    (hT : E.trans.Terminates) (m' : PMF State) :
    (macroExtend E m').trans.Terminates :=
  ⟨Nat.find hT + 1,
    Stream'.Seq.terminatedAt_append_find hT
      (show (Seq.cons (Silent.τ, m') Seq.nil : Seq (Label × PMF State)).TerminatedAt 1 from rfl)⟩

/-- The end-state of a one-step extension is the appended macro-state `m'`. -/
theorem macroExtend_endState {E : AlterSeq (PMF State) Label}
    (hT : E.trans.Terminates) (m' : PMF State) :
    (macroExtend E m').endState (macroExtend_term hT m') = m' :=
  AlterSeq.endState_append_singleton E hT Silent.τ m'

/-- The **depth-`n` truncated macro-future** of the composite belief scheduler
`Σ` from the macro-history `E`: run `Σ` for at most `n` internal macro-steps and,
on a forced halt (depth `0`) or a scheduler stop (`none`), collapse to the
current macro end-state. Genuinely a `PMF State`. -/
noncomputable def macroFuture_trunc {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → PMF State
  | 0, E, hT => E.endState hT
  | n + 1, E, hT =>
      (S.next E).bind (fun o => match o with
        | none => E.endState hT
        | some (_, ω) => ω.bind (fun m' =>
            macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m')))

/-- **Finite macro-future collapse.** Each depth-`n` truncated macro-future of
`S` from a terminating macro-history `E` is an internal weak transition of `sys`
out of `E`'s macro end-state. Proven by induction on `n`: the base is
reflexivity; the step is target-convexity over the scheduler's emission
(`weakTau_mix`), collapsing one macro-step through `weakTau_of_distStep` and
gluing the sampled successor's induction hypothesis with `weakTau_trans`. -/
theorem weakTau_macroFuture_trunc {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    weakTau sys (E.endState hT) (macroFuture_trunc S n E hT) := by
  induction n generalizing E hT with
  | zero => exact weakTau_refl sys (E.endState hT)
  | succ n IH =>
    -- pointwise weak-τ for each scheduler emission `o`
    have hbranch : ∀ o ∈ (S.next E).support,
        weakTau sys (E.endState hT)
          ((fun o => match o with
            | none => E.endState hT
            | some (_, ω) => ω.bind (fun m' =>
                macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) o) := by
      rintro (_ | ⟨l, ω⟩) ho
      · exact weakTau_refl sys (E.endState hT)
      · -- the emission is a valid internal step out of `E`'s end-state
        have hl : l = Silent.τ := S.internal_only E l ω ho
        subst hl
        have hstep : (𝒟(sys^w)).step (E.endState hT) Silent.τ ω :=
          S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
            (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω ho
        -- collapse the single macro-step, then continue via the IH per successor
        have hτ1 : weakTau sys (E.endState hT) (ω.bind id) := weakTau_of_distStep hstep
        have hτ2 : weakTau sys (ω.bind id)
            (ω.bind (fun m' =>
              macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) := by
          refine weakTau_mix ω id
            (fun m' => macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))
            (fun m' _ => ?_)
          have IHm := IH (macroExtend E m') (macroExtend_term hT m')
          rw [macroExtend_endState hT m'] at IHm
          exact IHm
        exact weakTau_trans hτ1 hτ2
    -- assemble via target-convexity, rewriting the source through `bind_const`
    have key := weakTau_mix (S.next E) (fun _ => E.endState hT)
      (fun o => match o with
        | none => E.endState hT
        | some (_, ω) => ω.bind (fun m' =>
            macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) hbranch
    rw [PMF.bind_const] at key
    exact key

/-- **Root corollary.** From a Dirac-free source `μ` (the nil macro-history), the
depth-`n` truncated macro-future is an internal weak transition of `sys` out of
`μ`. -/
theorem weakTau_macroFuture_trunc_root {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (μ : PMF State) :
    weakTau sys μ
      (macroFuture_trunc S n ⟨μ, Seq.nil⟩ Stream'.Seq.terminates_nil) := by
  have h := weakTau_macroFuture_trunc S n ⟨μ, Seq.nil⟩ Stream'.Seq.terminates_nil
  rwa [AlterSeq.endState_of_trans_nil (⟨μ, Seq.nil⟩ : AlterSeq (PMF State) Label) rfl
    Stream'.Seq.terminates_nil] at h

/-! ### Layer 2: macro depth stratification

The flattened halting sub-distribution split by the exact macro-depth at which
mass halts, and the single identity `macroHalt_tsum_depth` decomposing the
end-state mixture `Ν.bind id` of a `weakTau (𝒟(sys^w)) (PMF.pure μ0) Ν` into a
countable sum over that depth. Stated against an **abstract** a.s.-stopping
scheduler `S` via the pushforward hypothesis `hpush`, so Layer 5 can instantiate
it with `h.witnessScheduler`/`h.witness_pushforward` for any witness `h`, or with
a bespoke scheduler it builds; the crux (the `g`-integrated single-macro-step
collapse) is re-derived locally, so nothing here depends on `weakTau_flatten`. -/

open Classical in
/-- **`g`-integrated collapse for an abstract scheduler.** If `S`'s halting
pushforward (from `PMF.pure μ0`) is the macro-mixture `Ν` (hypothesis `hpush`),
then integrating any `g` over the halting macro end-state equals integrating `g`
against `Ν`. Re-derivation of the `weakTau.integrate` argument, decoupled from
the classical witness extraction. -/
private theorem macroIntegrate_of_pushforward {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (Ν : PMF (PMF State))
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (g : PMF State → ENNReal) :
    (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * g (E.1.endState E.2))
      = ∑' m, Ν m * g m := by
  classical
  symm
  calc (∑' m, Ν m * g m)
      = ∑' m, (∑' E, S.haltMass (PMF.pure μ0) E *
            (if E.1.endState E.2 = m then 1 else 0)) * g m :=
        tsum_congr (fun m => by rw [hpush m])
    _ = ∑' m, ∑' E, S.haltMass (PMF.pure μ0) E *
            (if E.1.endState E.2 = m then 1 else 0) * g m :=
        tsum_congr (fun m => by rw [ENNReal.tsum_mul_right])
    _ = ∑' E, ∑' m, S.haltMass (PMF.pure μ0) E *
            (if E.1.endState E.2 = m then 1 else 0) * g m := ENNReal.tsum_comm
    _ = ∑' E, S.haltMass (PMF.pure μ0) E * g (E.1.endState E.2) := by
        refine tsum_congr (fun E => ?_)
        rw [tsum_congr (fun m => by ring :
            ∀ m, S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0) * g m
              = S.haltMass (PMF.pure μ0) E *
                ((if E.1.endState E.2 = m then 1 else 0) * g m)),
          ENNReal.tsum_mul_left]
        congr 1
        rw [tsum_eq_single (E.1.endState E.2)
            (fun m' hm' => by rw [if_neg (fun heq => hm' heq.symm), zero_mul]),
          if_pos rfl, one_mul]

/-- **Flattened halting sub-distribution at macro-depth `k`.** The mass that,
under scheduler `S` run from `PMF.pure μ0`, halts along a terminating macro-run
of exactly `k` internal macro-steps, pushed forward to `State` through the macro
end-state. Summing over `k` recovers the whole flattened mixture
(`macroHalt_tsum_depth`). -/
noncomputable def macroHaltDepth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ) : State → ENNReal :=
  fun s => ∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
      E.1.trans.length E.2 = k},
    S.haltMass (PMF.pure μ0) E.1 * (E.1.1.endState E.1.2) s

open Classical in
/-- **Macro-depth stratification.** The end-state mixture `Ν.bind id` of a
macro-`weakTau` (captured abstractly by the pushforward `hpush` of an
a.s.-stopping scheduler `S`) equals the countable sum, over macro-depth `k`, of
the depth-`k` flattened halting sub-distributions. Proof: expand `Ν.bind id`
pointwise (`PMF.bind_apply`), collapse the macro end-state integral
(`macroIntegrate_of_pushforward` at `g := (· s)`), then stratify the execution
sum by transition-length via the fiber equivalence `Equiv.sigmaFiberEquiv` and
`ENNReal.tsum_sigma'`. -/
theorem macroHalt_tsum_depth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) {Ν : PMF (PMF State)}
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (s : State) :
    (Ν.bind id) s = ∑' k : ℕ, macroHaltDepth S μ0 k s := by
  classical
  have key : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (E.1.endState E.2) s)
      = ∑' k : ℕ, macroHaltDepth S μ0 k s := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv
        (fun E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} =>
          E.1.trans.length E.2)), ENNReal.tsum_sigma']
    rfl
  rw [PMF.bind_apply, ← key]
  exact (macroIntegrate_of_pushforward S μ0 Ν hpush (fun m => m s)).symm

/-! ### Layer 3: the recursion↔stratification halting decomposition

Per the design's R3-fallback: **no new scheduler is constructed**. Instead the
depth-`n` macro-future `macroFuture_trunc S n E` (Layer 1) is split, by pure
`PMF`/`ENNReal` algebra over its own recursion, into a monotone
**halted-within-`n`** sub-distribution `macroHalted` (mass that hit a scheduler
stop within the first `n` levels, collapsed at that macro end-state) and a
**residual** sub-distribution `macroResidual` (mass still running after `n`
levels, pushed through the depth-`n` macro-state). On the stratification side
(Layer 2) the depth-`k` halting masses `macroHaltDepth` sum to the full scheduler
halting mass, so under a.s.-halting the halted total rises to `1` and the residual
total mass `macroSurvive` falls to `0`. The bridge identifying the two
"halted-within-`n`" notions is the handoff crux (see the note at the end). -/

/-- The **residual** of the depth-`n` macro-future from `E`: the mass that takes a
scheduler step at every one of the first `n` levels (never stops) and is pushed
through the depth-`n` macro end-state. A sub-distribution of
`macroFuture_trunc S n E`. -/
noncomputable def macroResidual {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → State → ENNReal
  | 0, E, hT, s => (E.endState hT) s
  | n + 1, E, hT, s =>
      ∑' o, (S.next E) o * (match o with
        | none => 0
        | some (_, ω) => ∑' m', ω m' *
            macroResidual S n (macroExtend E m') (macroExtend_term hT m') s)

/-- The **halted-within-`n`** sub-distribution of the depth-`n` macro-future from
`E`: the mass that, within the first `n` recursion levels, hits a scheduler stop
(`none`) and collapses to the macro end-state at that moment. -/
noncomputable def macroHalted {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → E.trans.Terminates → State → ENNReal
  | 0, _, _, _ => 0
  | n + 1, E, hT, s =>
      ∑' o, (S.next E) o * (match o with
        | none => (E.endState hT) s
        | some (_, ω) => ∑' m', ω m' *
            macroHalted S n (macroExtend E m') (macroExtend_term hT m') s)

/-- **Recursion-side decomposition.** The depth-`n` macro-future splits, pointwise,
into the halted-within-`n` part plus the residual. -/
theorem macroFuture_trunc_decompose {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    (macroFuture_trunc S n E hT) s
      = macroHalted S n E hT s + macroResidual S n E hT s := by
  induction n generalizing E hT with
  | zero => simp only [macroFuture_trunc, macroHalted, macroResidual, zero_add]
  | succ n IH =>
    simp only [macroHalted, macroResidual, macroFuture_trunc]
    rw [PMF.bind_apply, ← ENNReal.tsum_add]
    apply tsum_congr
    intro o
    cases o with
    | none => simp
    | some p =>
      obtain ⟨l, ω⟩ := p
      rw [← mul_add]
      refine congrArg _ ?_
      rw [PMF.bind_apply, ← ENNReal.tsum_add]
      apply tsum_congr
      intro m'
      rw [← mul_add, IH (macroExtend E m') (macroExtend_term hT m')]

/-- One-step unfolding of the halted-within-`n` sub-distribution. -/
theorem macroHalted_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    macroHalted S (n + 1) E hT s
      = ∑' o, (S.next E) o * (match o with
          | none => (E.endState hT) s
          | some (_, ω) => ∑' m', ω m' *
              macroHalted S n (macroExtend E m') (macroExtend_term hT m') s) := rfl

/-- One-step unfolding of the residual sub-distribution. -/
theorem macroResidual_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    macroResidual S (n + 1) E hT s
      = ∑' o, (S.next E) o * (match o with
          | none => 0
          | some (_, ω) => ∑' m', ω m' *
              macroResidual S n (macroExtend E m') (macroExtend_term hT m') s) := rfl

/-- **The halted part is monotone in the depth.** Running one more level can only
add halting mass. -/
theorem macroHalted_mono {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (s : State) :
    macroHalted S n E hT s ≤ macroHalted S (n + 1) E hT s := by
  induction n generalizing E hT with
  | zero => simp [macroHalted]
  | succ n IH =>
    rw [macroHalted_succ, macroHalted_succ]
    refine ENNReal.tsum_le_tsum (fun o => ?_)
    cases o with
    | none => exact le_refl _
    | some p =>
      obtain ⟨l, ω⟩ := p
      refine mul_le_mul_left' (ENNReal.tsum_le_tsum (fun m' => ?_)) _
      exact mul_le_mul_left' (IH (macroExtend E m') (macroExtend_term hT m')) _

/-- **Total residual mass** surviving `n` internal macro-levels from `E`: the total
mass of the depth-`n` residual sub-distribution. Antitone in `n`; its limit is `0`
under a.s.-halting (see the stratification side). -/
noncomputable def macroSurvive {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) : ENNReal :=
  ∑' s, macroResidual S n E hT s

/-- At depth `0` nothing has stopped: the whole (unit) mass survives. -/
theorem macroSurvive_zero {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    macroSurvive S 0 E hT = 1 := by
  unfold macroSurvive
  simp only [macroResidual]
  exact PMF.tsum_coe _

/-- One-step recursion of the total residual mass: survive `n+1` levels iff the
scheduler steps now and the sampled successor survives `n` more. -/
theorem macroSurvive_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    macroSurvive S (n + 1) E hT
      = ∑' o, (S.next E) o * (match o with
          | none => 0
          | some (_, ω) => ∑' m', ω m' *
              macroSurvive S n (macroExtend E m') (macroExtend_term hT m')) := by
  unfold macroSurvive
  simp only [macroResidual]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro o
  rw [ENNReal.tsum_mul_left]
  congr 1
  cases o with
  | none => simp
  | some p =>
    obtain ⟨l, ω⟩ := p
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro m'
    rw [ENNReal.tsum_mul_left]

/-- **Halted total + survive = 1.** The depth-`n` macro-future is a `PMF`, so its
halted-within-`n` total mass and its residual total mass `macroSurvive` partition
the unit mass. Monotone/antitone consequence: as the halted total rises to `1`
(stratification side), `macroSurvive` falls to `0`. -/
theorem macroHalted_total_add_macroSurvive {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    (∑' s, macroHalted S n E hT s) + macroSurvive S n E hT = 1 := by
  unfold macroSurvive
  rw [← ENNReal.tsum_add,
    tsum_congr (fun s => (macroFuture_trunc_decompose S n E hT s).symm)]
  exact PMF.tsum_coe _

/-! #### Stratification side: depth-`k` halting totals sum to the halting mass -/

/-- Total mass of the depth-`k` flattened halting sub-distribution (Layer 2's
`macroHaltDepth`): the halting mass carried by terminating macro-runs of exactly
`k` internal steps. -/
theorem macroHaltDepth_total {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ) :
    (∑' s, macroHaltDepth S μ0 k s)
      = ∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k}, S.haltMass (PMF.pure μ0) E.1 := by
  unfold macroHaltDepth
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro E
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- **Depth totals sum to the total halting mass.** Summing the depth-`k` halting
totals over `k` recovers the scheduler's whole halting mass from `PMF.pure μ0`
(reverse of Layer 2's fiber stratification). -/
theorem macroHaltDepth_tsum {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) :
    (∑' k : ℕ, ∑' s, macroHaltDepth S μ0 k s)
      = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
          S.haltMass (PMF.pure μ0) E := by
  simp_rw [macroHaltDepth_total]
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv
      (fun E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} =>
        E.1.trans.length E.2)), ENNReal.tsum_sigma']
  rfl

/-- **Halted total rises to `1` under a.s.-halting.** If the scheduler `S` halts
almost surely from `PMF.pure μ0` (`hhalt`), the supremum over the truncation depth
`n` of the halting mass accumulated in the first `n` macro-depths is `1`. This is
the residual-vanishing fact `macroSurvive → 0` in `iSup` form (partial sums of the
depth totals), the stratification-side deliverable F5 consumes. -/
theorem macroHalted_iSup_eq_one {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (hhalt : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E) = 1) :
    (⨆ n : ℕ, ∑ k ∈ Finset.range n, ∑' s, macroHaltDepth S μ0 k s) = 1 := by
  rw [← ENNReal.tsum_eq_iSup_nat, macroHaltDepth_tsum]
  exact hhalt

/-! #### HANDOFF (F3 → F6): the remaining bridge and the closure lemma

Two self-contained sides are delivered above, both `[propext, Classical.choice,
Quot.sound]`-only and independent of the `weakTau_flatten` stub:

* **recursion side** — `macroFuture_trunc_decompose` splits Layer 1's depth-`n`
  macro-future into `macroHalted` (monotone in `n`, `macroHalted_mono`) plus
  `macroResidual`, whose total mass `macroSurvive` satisfies
  `macroHalted_total_add_macroSurvive` (`halted-total + macroSurvive = 1`);
* **stratification side** — `macroHaltDepth_tsum` sums Layer 2's depth-`k`
  halting totals to the full halting mass, so `macroHalted_iSup_eq_one` drives the
  accumulated halted mass to `1` (equivalently `macroSurvive → 0`) under a.s.-halting.

**The one gap (crux, deferred to F6).** Identifying the two "halted-within-`n`"
notions:
  `(∑' s, macroHalted S n ⟨μ0, Seq.nil⟩ _ s) = ∑ k ∈ Finset.range n, ∑' s, macroHaltDepth S μ0 k s`.
LHS accumulates halts through the LOCAL recursion (`S.next` at histories extending
`⟨μ0, nil⟩`); RHS is the GLOBAL `haltMass` (`probOf` from `PMF.pure μ0`).
Establishing it is an unrolling of `probOf` as the product of per-step kernel
choices, matching each scheduler emission `some (τ, ω)` and sampled successor `m'`
against one macro-transition — structurally the `bind_haltMass`/`probOf_append_singleton`
telescoping (WeakScheduler.lean ~554–804), i.e. a several-hundred-line execution↔
recursion induction. It is the analogue of `Scheduler.bind_haltMass` and is judged
FEASIBLE but out of scope for F3.

**The weakTau-limit-closure lemma F6 needs.** With the bridge, F6 wants:
  if `weakTau sys μ (D n)` for all `n`, and `D n s = H n s + R n s` with `H n`
  monotone in `n`, `⨆ n, ∑' s, H n s = 1` (residual total `∑' s, R n s → 0`), and
  `T s = ⨆ n, H n s`, then `weakTau sys μ T`.
Here `D n := macroFuture_trunc S n ⟨μ, Seq.nil⟩`, `H := macroHalted`,
`R := macroResidual`, and `T = Ν.bind id` (Layer 2's `macroHalt_tsum_depth` gives
`(Ν.bind id) s = ∑' k, macroHaltDepth = ⨆ n, ∑ k ∈ range n, macroHaltDepth`, which
matches `⨆ n, H n s` once the bridge is available pointwise).
ASSESSMENT: this closure is NOT obviously constructible from the existing
`WeakScheduler` combinators without a new scheduler, because `weakTau` targets a
single `PMF` and the natural witness must carry, at each sys-history, the belief
"which macro-depth am I in" — the original Layer-3/4 depth-indexed scheduler (R3's
two-component hidden state). The cheaper route the fallback buys: since the bridge
makes `D (n+1)` DEFINITIONALLY the depth-`n+1` recursion whose first level is a
`bind`-shaped mixture over `S.next E`, F6 can instead assemble the witness as a
per-depth `WeakScheduler.bind` chain (design R3-fallback) and invoke the proven
`WeakScheduler.bind_haltMass` at each level, so the a.s.-halting of the composite
is exactly `macroHalted_iSup_eq_one` and no bespoke fixpoint/belief-normalization
is needed. Recommendation for F6: build that finite `bind`-chain witness at each
`n`, take the halting-mass supremum via `macroHalted_iSup_eq_one`, and read off the
pushforward from `macroHalt_tsum_depth`. -/

/-! ### Layer 4b: the ω-witness scheduler and its one-step haltMass recursion

The crux artifact: a single `WeakScheduler sys` realizing the ω-composition, and
the identities tying its `haltMass` to the Layer-3 recursion.

**Design (approved D1).** The hidden configuration behind an observed
`sys`-history `e` is a *decomposition* of `e` into completed inner macro-segments
plus a current in-progress inner prefix. Rather than an n-ary bijection, the
carrier and the belief weight are defined by recursion mirroring one another.
Per-macro-step inner witnesses are extracted classically from
`weakTau_of_distStep`, exactly as `weakTau.witnessScheduler`. -/

open Classical in
/-- **Per-emission inner witness.** For a macro-state `m : PMF State` and a
macro-emission `ω : PMF (PMF State)`, the witnessing internal `sys`-scheduler for
the single-macro-step weak transition `weakTau sys m (ω.bind id)`
(`weakTau_of_distStep`); off the support (no such internal macro-step) it is the
immediately-stopping scheduler. Classical, mirroring `weakTau.witnessScheduler`. -/
noncomputable def innerWitness (sys : System State Label) (m : PMF State)
    (ω : PMF (PMF State)) : WeakScheduler sys :=
  if h : (𝒟(sys^w)).step m Silent.τ ω then (weakTau_of_distStep h).witnessScheduler
  else WeakScheduler.stop sys

/-- On the support, the inner witness halts almost surely from source `m`. -/
theorem innerWitness_halts {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) :
    (∑' e, (innerWitness sys m ω).haltMass m e) = 1 := by
  rw [innerWitness, dif_pos h]; exact (weakTau_of_distStep h).witness_halts

/-- On the support, the inner witness's `g`-integrated halting end-state equals
the `g`-integral against the macro-mixture `ω.bind id` (the single-step collapse,
`g`-integrated). Taking `g = 1` recovers `innerWitness_halts`; `g = [· = s]` the
end-state pushforward. -/
theorem innerWitness_integrate {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) (g : State → ENNReal) :
    (∑' e, (innerWitness sys m ω).haltMass m e * g (e.1.endState e.2))
      = ∑' s, (ω.bind id) s * g s := by
  rw [innerWitness, dif_pos h]; exact (weakTau_of_distStep h).integrate g

open Classical in
/-- On the support, the inner witness's halting end-state pushforward is the
macro-mixture `ω.bind id`. -/
theorem innerWitness_pushforward {sys : System State Label} {m : PMF State}
    {ω : PMF (PMF State)} (h : (𝒟(sys^w)).step m Silent.τ ω) (s : State) :
    (ω.bind id) s
      = ∑' e, (innerWitness sys m ω).haltMass m e * (if e.1.endState e.2 = s then 1 else 0) := by
  rw [innerWitness, dif_pos h]; exact (weakTau_of_distStep h).witness_pushforward s

/-! ### Layer 4a: the local↔global halting bridge

Identifies the two "halted-within-`n`" notions rooted at `⟨μ0, Seq.nil⟩`: the
LOCAL recursion `macroHalted` (Layer 3, `S.next` at histories extending
`⟨μ0, nil⟩`) versus the GLOBAL depth-`k` halting masses
`S.haltMass (PMF.pure μ0) ·` (Layer 2). The bridge is the execution↔recursion
telescoping, routed through the conditional depth totals `condDepth` (a
`pathWeight`-weighted halt-mass sum over the `k`-step continuations of a base
macro-history). Both sides satisfy the same front-peel recursion; at the root
`condDepth` is the global depth-`k` halting mass (via `probOf_eq_pathWeight`
and the Dirac collapse of the source). -/

/-- Total halted-within-`n` mass from a macro-history `E`. -/
private noncomputable def macroHaltTotal {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) : ENNReal :=
  ∑' s, macroHalted S n E hT s

/-- One-step recursion of the halted-within-`n` total mass. -/
private theorem macroHaltTotal_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) :
    macroHaltTotal S (n + 1) E hT
      = ∑' o, (S.next E) o * (match o with
          | none => 1
          | some (_, ω) => ∑' m', ω m' *
              macroHaltTotal S n (macroExtend E m') (macroExtend_term hT m')) := by
  unfold macroHaltTotal
  simp only [macroHalted]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro o
  rw [ENNReal.tsum_mul_left]
  congr 1
  cases o with
  | none => exact PMF.tsum_coe _
  | some p =>
    obtain ⟨l, ω⟩ := p
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro m'
    rw [ENNReal.tsum_mul_left]

/-- The conditional depth-`k` halt total from base macro-history `E`: the total
mass, over the `k`-step continuations of `E`, of the path-weight to the
continuation times the scheduler-stop probability there. -/
private noncomputable def condDepth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ)
    (E : AlterSeq (PMF State) Label) : ENNReal :=
  ∑' K : {K : List (Label × PMF State) // K.length = k},
    (⟨PMF.pure μ0, S.toScheduler⟩ : ProbabilisticExecution (𝒟(sys^w))).pathWeight E K.1
      * S.next ⟨E.init, E.trans.append (Seq.ofList K.1)⟩ none

/-- Split an `ENNReal` tsum over `Option γ` into the `none` value plus the tsum
over `some`. (Local copy of `Scheduler`'s private helper.) -/
private theorem tsumOpt {γ : Type} (f : Option γ → ENNReal) :
    (∑' o, f o) = f none + ∑' n, f (some n) := by
  rw [← (Equiv.optionEquivSumPUnit.{0} γ).symm.tsum_eq f,
    Summable.tsum_sum ENNReal.summable ENNReal.summable, add_comm]
  congr 1
  rw [tsum_eq_single PUnit.unit (by rintro ⟨⟩ h; exact absurd rfl h)]
  rfl

/-- `condDepth` at depth `0` is the scheduler-stop probability at `E`. -/
private theorem condDepth_zero {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (E : AlterSeq (PMF State) Label) :
    condDepth S μ0 0 E = S.next E none := by
  unfold condDepth
  rw [tsum_eq_single (⟨[], rfl⟩ : {K : List (Label × PMF State) // K.length = 0})
    (fun K hK => absurd (Subtype.ext (List.length_eq_zero_iff.mp K.2)) hK)]
  have hpw : (⟨PMF.pure μ0, S.toScheduler⟩ :
      ProbabilisticExecution (𝒟(sys^w))).pathWeight E [] = 1 := by
    unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
  rw [hpw, one_mul, Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]

/-- Cons bijection: length-`(k+1)` lists ↔ (head, length-`k` tail). -/
private def consLenEquiv {γ : Type} (k : ℕ) :
    (γ × {K : List γ // K.length = k}) ≃ {L : List γ // L.length = k + 1} where
  toFun p := ⟨p.1 :: p.2.1, by rw [List.length_cons, p.2.2]⟩
  invFun L := (L.1.head (List.ne_nil_of_length_pos (by rw [L.2]; exact Nat.succ_pos k)),
    ⟨L.1.tail, by rw [List.length_tail, L.2, Nat.add_sub_cancel]⟩)
  left_inv := by
    rintro ⟨x, ⟨K, hK⟩⟩
    exact Prod.ext rfl (Subtype.ext (by simp))
  right_inv := by
    rintro ⟨L, hL⟩
    exact Subtype.ext (List.cons_head_tail _)

/-- One-step recursion of `condDepth`: front-peel of the continuation list. -/
private theorem condDepth_succ {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ)
    (E : AlterSeq (PMF State) Label) :
    condDepth S μ0 (k + 1) E
      = ∑' o, (S.next E) o * (match o with
          | none => 0
          | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m')) := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  -- the common normal form both sides reduce to
  set C : ENNReal := ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
      * ∑' m', ω m' * condDepth S μ0 k (macroExtend E m') with hC
  have hRHS : (∑' o, (S.next E) o * (match o with
        | none => (0 : ENNReal)
        | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m'))) = C := by
    rw [tsumOpt (fun o => (S.next E) o * (match o with
        | none => (0 : ENNReal)
        | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m')))]
    simp only [mul_zero, zero_add]
    rw [ENNReal.tsum_prod']
    rw [tsum_eq_single Silent.τ (fun l hl => by
      rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
  have hker0 : ∀ (l : Label) (m' : PMF State), l ≠ Silent.τ →
      (⟨PMF.pure μ0, S.toScheduler⟩ :
        ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m') = 0 := by
    intro l m' hl
    unfold ProbabilisticExecution.kernel
    rw [ENNReal.tsum_eq_zero]
    intro ω
    rw [hzero l ω hl, zero_mul]
  have hpath : ∀ (l : Label) (m' : PMF State)
      (K' : {K : List (Label × PMF State) // K.length = k}),
      (⟨PMF.pure μ0, S.toScheduler⟩ :
          ProbabilisticExecution (𝒟(sys^w))).pathWeight E ((l, m') :: K'.1)
          * S.next ⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ none
        = (⟨PMF.pure μ0, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m')
          * ((⟨PMF.pure μ0, S.toScheduler⟩ :
              ProbabilisticExecution (𝒟(sys^w))).pathWeight
                ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩ K'.1
              * S.next ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
                  (Seq.ofList K'.1)⟩ none) := by
    intro l m' K'
    rw [ProbabilisticExecution.pathWeight_cons,
      show E.trans.append (Seq.ofList ((l, m') :: K'.1))
          = (E.trans.append (Seq.cons (l, m') Seq.nil)).append (Seq.ofList K'.1) from by
        rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
          Stream'.Seq.nil_append]]
    ring
  have hLHS : condDepth S μ0 (k + 1) E = C := by
    unfold condDepth
    rw [← Equiv.tsum_eq (consLenEquiv (γ := Label × PMF State) k),
      ENNReal.tsum_prod', ENNReal.tsum_prod']
    simp only [consLenEquiv, Equiv.coe_fn_mk]
    rw [tsum_congr (fun l => tsum_congr (fun m' => tsum_congr (fun K' => hpath l m' K'))),
      tsum_congr (fun l => tsum_congr (fun _ => ENNReal.tsum_mul_left)),
      tsum_eq_single Silent.τ (fun l hl => by
        rw [ENNReal.tsum_eq_zero]; intro m'; rw [hker0 l m' hl, zero_mul])]
    rw [hC]
    simp only [ProbabilisticExecution.kernel]
    rw [tsum_congr (fun _ => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
    apply tsum_congr; intro ω
    rw [tsum_congr (fun m' => mul_assoc _ _ _), ENNReal.tsum_mul_left]
    rfl
  rw [hLHS]; exact hRHS.symm

/-- `macroHaltTotal` is the partial sum of the conditional depth totals. -/
private theorem macroHaltTotal_eq_sum_condDepth {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    macroHaltTotal S n E hT = ∑ k ∈ Finset.range n, condDepth S μ0 k E := by
  induction n generalizing E hT with
  | zero =>
    simp only [macroHaltTotal, macroHalted, tsum_zero, Finset.range_zero, Finset.sum_empty]
  | succ n IH =>
    have hIH : ∀ m', macroHaltTotal S n (macroExtend E m') (macroExtend_term hT m')
        = ∑ k ∈ Finset.range n, condDepth S μ0 k (macroExtend E m') :=
      fun m' => IH (macroExtend E m') (macroExtend_term hT m')
    have hLHS : macroHaltTotal S (n + 1) E hT
        = ∑' o, (S.next E) o * (match o with
            | none => (1 : ENNReal)
            | some (_, ω) => ∑' m', ω m' *
                ∑ k ∈ Finset.range n, condDepth S μ0 k (macroExtend E m')) := by
      rw [macroHaltTotal_succ]
      apply tsum_congr; intro o
      congr 1
      cases o with
      | none => rfl
      | some p => obtain ⟨l, ω⟩ := p; apply tsum_congr; intro m'; rw [hIH m']
    have hRHS : (∑ k ∈ Finset.range (n + 1), condDepth S μ0 k E)
        = ∑' o, (S.next E) o * (match o with
            | none => (1 : ENNReal)
            | some (_, ω) => ∑' m', ω m' *
                ∑ k ∈ Finset.range n, condDepth S μ0 k (macroExtend E m')) := by
      rw [Finset.sum_range_succ', condDepth_zero]
      have hswap : (∑ k ∈ Finset.range n, condDepth S μ0 (k + 1) E)
          = ∑' o, (S.next E) o * (match o with
              | none => (0 : ENNReal)
              | some (_, ω) => ∑' m', ω m' *
                  ∑ k ∈ Finset.range n, condDepth S μ0 k (macroExtend E m')) := by
        rw [show (∑ k ∈ Finset.range n, condDepth S μ0 (k + 1) E)
            = ∑ k ∈ Finset.range n, ∑' o, (S.next E) o * (match o with
                | none => (0 : ENNReal)
                | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m'))
            from Finset.sum_congr rfl (fun k _ => condDepth_succ S μ0 k E)]
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        apply tsum_congr; intro o
        rw [← Finset.mul_sum]
        congr 1
        cases o with
        | none => simp
        | some p =>
          obtain ⟨l, ω⟩ := p
          symm
          simp_rw [Finset.mul_sum]
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      rw [hswap,
        tsumOpt (fun o => (S.next E) o * (match o with
          | none => (0 : ENNReal)
          | some (_, ω) => ∑' m', ω m' *
              ∑ k ∈ Finset.range n, condDepth S μ0 k (macroExtend E m'))),
        tsumOpt (fun o => (S.next E) o * (match o with
          | none => (1 : ENNReal)
          | some (_, ω) => ∑' m', ω m' *
              ∑ k ∈ Finset.range n, condDepth S μ0 k (macroExtend E m')))]
      simp only [mul_zero, mul_one, zero_add]
      rw [add_comm]
    rw [hLHS]; exact hRHS.symm

/-- Length-`k` terminating macro-histories ↔ (initial macro-state, length-`k`
transition list). -/
private def rootEquiv (k : ℕ) :
    (PMF State × {K : List (Label × PMF State) // K.length = k})
      ≃ {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k} where
  toFun p := ⟨⟨⟨p.1, Seq.ofList p.2.1⟩, Stream'.Seq.terminates_ofList p.2.1⟩, by
    rw [WeakScheduler.length_ofList]; exact p.2.2⟩
  invFun E := (E.1.1.init, ⟨E.1.1.trans.toList E.1.2, by
    rw [Stream'.Seq.length_toList]; exact E.2⟩)
  left_inv := by
    rintro ⟨s, ⟨K, hK⟩⟩
    exact Prod.ext rfl (Subtype.ext (Stream'.Seq.toList_ofList K))
  right_inv := by
    rintro ⟨⟨⟨i, tr⟩, hterm⟩, hlen⟩
    refine Subtype.ext (Subtype.ext ?_)
    change (⟨i, Seq.ofList (tr.toList hterm)⟩ : AlterSeq (PMF State) Label) = ⟨i, tr⟩
    rw [Stream'.Seq.ofList_toList]

/-- At the root, `condDepth` is the global depth-`k` halting mass. -/
private theorem condDepth_root {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (k : ℕ) :
    condDepth S μ0 k ⟨μ0, Seq.nil⟩
      = ∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k}, S.haltMass (PMF.pure μ0) E.1 := by
  have hsummand : ∀ (s : PMF State) (K : {K : List (Label × PMF State) // K.length = k}),
      S.haltMass (PMF.pure μ0) (rootEquiv k (s, K)).1
        = PMF.pure μ0 s * ((⟨PMF.pure μ0, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).pathWeight ⟨s, Seq.nil⟩ K.1
              * S.next ⟨s, Seq.ofList K.1⟩ none) := by
    intro s K
    show S.haltMass (PMF.pure μ0)
        ⟨⟨s, Seq.ofList K.1⟩, Stream'.Seq.terminates_ofList K.1⟩ = _
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_eq_pathWeight,
      ProbabilisticExecution.init_eq_initState, mul_assoc]
  unfold condDepth
  simp only [Stream'.Seq.nil_append]
  rw [← Equiv.tsum_eq (rootEquiv k), ENNReal.tsum_prod']
  rw [tsum_congr (fun s => tsum_congr (fun K => hsummand s K))]
  rw [tsum_congr (fun s => ENNReal.tsum_mul_left)]
  rw [tsum_eq_single μ0 (fun s hs => by rw [PMF.pure_apply, if_neg hs, zero_mul]),
    PMF.pure_apply_self, one_mul]

/-- **The local↔global halting bridge.** The halted-within-`n` total mass of the
local recursion `macroHalted` from the root `⟨μ0, Seq.nil⟩` equals the sum, over
macro-depth `k < n`, of the global depth-`k` halting masses
`S.haltMass (PMF.pure μ0) ·`. This is the F3-handoff's one remaining gap. -/
theorem macroHalted_total_eq_depth_sum {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (n : ℕ) :
    (∑' s, macroHalted S n ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil s)
      = ∑ k ∈ Finset.range n, (∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k}, S.haltMass (PMF.pure μ0) E.1) := by
  have h := macroHaltTotal_eq_sum_condDepth S μ0 n ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil
  rw [show (∑' s, macroHalted S n ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil s)
      = macroHaltTotal S n ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil from rfl, h]
  exact Finset.sum_congr rfl (fun k _ => condDepth_root S μ0 k)

/-- **Survive corollary (ENNReal-`+` form).** The accumulated depth-`k` halting
masses (`k < n`) plus the residual total `macroSurvive` partition the unit mass.
Combined with `macroHalted_iSup_eq_one`, this drives `macroSurvive → 0` under
a.s.-halting (directly consumable by F4b/F5). -/
theorem macroSurvive_root_add_depth_sum {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) (n : ℕ) :
    (∑ k ∈ Finset.range n, (∑' E : {E : {e : AlterSeq (PMF State) Label // e.trans.Terminates} //
          E.1.trans.length E.2 = k}, S.haltMass (PMF.pure μ0) E.1))
      + macroSurvive S n ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil = 1 := by
  rw [← macroHalted_total_eq_depth_sum]
  exact macroHalted_total_add_macroSurvive S n ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil

/-! ### Layer 4b (cont.): the `flattenSched` belief scheduler — HANDOFF

**Landed here (sorry-free, axiom-clean):** `innerWitness` and its three fidelity
lemmas `innerWitness_halts` / `innerWitness_integrate` / `innerWitness_pushforward`
— the per-macro-emission inner `sys`-witness extracted classically from
`weakTau_of_distStep`, mirroring `weakTau.witnessScheduler`. These discharge the
"per-emission inner witnesses with halts/pushforward" requirement of deliverable 1
and are the raw material every clause below consumes. The remaining belief-
scheduler stack is specified below with its exact obligations; it is deferred to
keep the build green for the concurrently-authored Layer 4a.

**Carrier (deliverable 1).** For an observed terminating `sys`-history `e`, a
*flatten configuration* is a decomposition of `e` into completed inner
macro-segments plus a current in-progress inner prefix:
```
FlatConfig := Σ (E : {e : AlterSeq (PMF State) Label // e.trans.Terminates}),
  -- one completed inner sys-execution per macro-transition of E, plus the
  -- current inner prefix; the sampled successor macro-states are the states of E.
  (List {p : AlterSeq State Label // p.trans.Terminates}) ×
    {p : AlterSeq State Label // p.trans.Terminates}
```
Per D1 (NO n-ary bijection): consistency of a config with `e` — that the
CONCATENATION of the completed inner executions followed by the current prefix
equals `e` — is defined by RECURSION on the config's step list (fold `AlterSeq`
concatenation via `Stream'.Seq.append`), and the weight recursion mirrors it.

**Weight (deliverable 1).** `flatWeight (config) :=`
  (macro-path measure of `E` under `S`, i.e. `probOf`/`pathWeight` — reuse Layer
    4a's `ProbabilisticExecution.pathWeight`)
  × `∏ᵢ` `innerWitness (E.stateAt i) (ωᵢ)`.haltMass (completed segment `i`)
  × `probOf` of the current inner prefix under `innerWitness (endState-so-far) ω_cur`.
Guard by `e`-consistency (weight `0` when the concatenation ≠ `e`); zero-length
inner runs yield distinct configs with several completed-empty steps at the same
sys-point — the tsum treats them as distinct, well-definedness carried by the
weights, not by exclusion (as flagged in the design).

**`flattenNum` / `flattenSched` (deliverable 2).**
`flattenNum e o := ∑' config, [config consistent with e] * flatWeight config *`
  `(nextMove config o)`, where `nextMove config` is: the current inner witness's
  move at the current prefix; PLUS, at an inner-halt boundary, the macro-level
  move `S.next E` — `none ↦` contributes to `o = none`; `some (τ, ω) ↦` opens a
  fresh inner run whose first move is `innerWitness (endState) ω`.next ⟨endState, nil⟩.
Then, exactly as `mapWeakBeliefSched` (`WeakTauLift.lean:59–140`):
```
flattenNext e := if h0 : flattenDenom e = 0 then PMF.pure none
                 else PMF.normalize (flattenNum e) (h0) (flattenDenom_ne_top e)
flattenSched  := { next := flattenNext, valid := …, internal_only := … }
```
`flattenDenom e := ∑' o, flattenNum e o` (so `flattenNum_tsum` is `rfl`).
`flattenDenom_ne_top`: bound each config's weight by `1` and restrict the support,
the `bindWeight_tsum_ne_top` pattern (`WeakScheduler.lean:274`).
`valid` / `internal_only`: from `flattenNum e (some (l,ν)) ≠ 0` extract a config
whose emitted move is some `innerWitness … : WeakScheduler sys` move; delegate to
that witness's `.valid` at the current suffix `⟨stateAfter e j, e.trans.drop j⟩`,
bridging to `e`'s end-state via `WeakScheduler.endState_drop`, and to its
`.internal_only` — precisely `Scheduler.bind`'s `some j` branch
(`WeakScheduler.lean:415–436`, `1140–1178`).

**Cancellation (deliverable 3).** `flattenDenom e * flattenNext e o = flattenNum e o`,
the verbatim `mapWeakBeliefSched_cancel` / `weakTau_bind` `hcancel` argument
(`WeakTauLift.lean:144–168`): both branches of the `dif`, using
`ENNReal.mul_inv_cancel (flattenDenom≠0) (flattenDenom≠⊤)` and, on the `=0`
branch, `∑' o, flattenNum e o = 0`.

**Deliverable 4 — the one-step haltMass recursion (THE deliverable).** State, as
the `mapWeakBeliefSched_probOf`/`_integrate` analogue:
```
flatten_integrate_step :
  (∑' e, (flattenSched S μ0).haltMass μ0 e * g (e.1.endState e.2))
    = (S.next ⟨μ0, Seq.nil⟩ none) * (∑' s, μ0 s * g s)          -- immediate macro-halt
      + ∑' (ω : PMF (PMF State)), S.next ⟨μ0, Seq.nil⟩ (some (Silent.τ, ω))
          * ∑' m', ω m' * (flattenSched S (…extended root at m'…)).haltMass … g   -- recurse
```
i.e. the SAME one-macro-level unfolding as Layer 3's `macroResidual_succ` /
`macroHalted_succ`. Proof template = `mapWeakBeliefSched_probOf` (belief path
measure telescoped via `probOf_append_singleton`, `WeakTauLift.lean:175–290`)
then `mapWeakBeliefSched_integrate` (fibrewise regroup, `:350–398`), with the
per-macro-step collapse supplied by `innerWitness_integrate` (landed above) and
the local↔global reconciliation by Layer 4a's `macroHalted_total_eq_depth_sum`
(cite; do NOT re-prove). Feeding the `iSup` from `macroHalted_iSup_eq_one`
(a.s.-halting) and the pushforward from `macroHalt_tsum_depth` then closes
`weakTau_flatten` (line 58). -/

/-! ### Layer 4c: the ω-witness segment machinery

**Superseded by Layer 4d (decision-point compression); retained where reused.**
The naive normalizer of the original `flattenSched` belief scheduler (an
unbounded-empty-segment carrier) is divergent — see the design doc — so its
belief numerator/denominator/scheduler and closing identities were removed. What
survives is the segment/weight/connection machinery below
(`FlatSeg`/`segTrans`/`segSrc`/`segHist`/`segWeight`/`chained`/`moveTerm`, and
`endState_append_shift`/`chained_endState`), transplanted verbatim into the
Layer-4d decision-point carrier `DConfig`/`dSched`. Per design D1, the hidden
configuration behind an observed `sys`-history is a list of completed inner
macro-segments; the belief weight is defined by recursion mirroring the segment
list. -/

/-- A completed inner macro-segment behind an observed `sys`-history: the
macro-emission `emit`, the sampled successor macro-state `succ`, and the
completed inner `sys`-execution `run` (a terminating run of the associated
`innerWitness`). -/
structure FlatSeg (State Label : Type) where
  /-- The macro-emission `ω : PMF (PMF State)` chosen for this macro-step. -/
  emit : PMF (PMF State)
  /-- The sampled successor macro-state `m' ~ emit`. -/
  succ : PMF State
  /-- The completed inner `sys`-execution witnessing this macro-step. -/
  run : AlterSeq State Label
  /-- The inner execution terminates. -/
  runT : run.trans.Terminates

variable {sys : System State Label}

/-- The concatenated transition sequence of the completed segments' inner runs,
followed by the current prefix `c`. Fold-append per D1. -/
noncomputable def segTrans :
    List (FlatSeg State Label) → Stream'.Seq (Label × State) → Stream'.Seq (Label × State)
  | [], c => c
  | List.cons seg rest, c => seg.run.trans.append (segTrans rest c)

/-- The current source macro-state after the completed segments, threading from
the root source `src0`: the last segment's successor (or `src0` if none). -/
noncomputable def segSrc (src0 : PMF State) : List (FlatSeg State Label) → PMF State
  | [] => src0
  | List.cons seg rest => segSrc seg.succ rest

/-- The current macro-history after the completed segments, threading from the
root history `E` by `macroExtend` at each segment's successor. -/
noncomputable def segHist (E : AlterSeq (PMF State) Label) :
    List (FlatSeg State Label) → AlterSeq (PMF State) Label
  | [] => E
  | List.cons seg rest => segHist (macroExtend E seg.succ) rest

/-- The belief path-weight of the completed segments: the macro path-measure of
the chosen emissions/successors times each inner run's halting mass, by recursion
mirroring the segment list. Threads the current source `src0` and macro-history
`E`. -/
noncomputable def segWeight (S : WeakScheduler (𝒟(sys^w))) (src0 : PMF State)
    (E : AlterSeq (PMF State) Label) : List (FlatSeg State Label) → ENNReal
  | [] => 1
  | List.cons seg rest =>
      S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
        * (innerWitness sys src0 seg.emit).haltMass src0 ⟨seg.run, seg.runT⟩
        * segWeight S seg.succ (macroExtend E seg.succ) rest

/-- Connection predicate: threading the connecting state `s0`, each completed
run starts where the previous one ended, and the current prefix starts where the
last completed run ended (or at `s0` if there are none). Forces the config to be a
genuine decomposition of a single connected `sys`-execution. -/
def chained (s0 : State) : List (FlatSeg State Label) → State → Prop
  | [], curInit => curInit = s0
  | List.cons seg rest, curInit =>
      seg.run.init = s0 ∧ chained (seg.run.endState seg.runT) rest curInit

open Classical in
/-- The next-move contribution of a config's *current* inner run (belief over the
emission `ω`) at prefix `cur`, source `src`, macro-history `Ec`:
* `some (l, ν)`: the current inner run continues, emitting `(l, ν)` — path measure
  to `cur` under `innerWitness src ω`, times its next move, summed over `ω`
  weighted by the macro choice `S.next Ec (some (τ, ω))`.
* `none`: the composite halts at the macro-boundary — only when the current prefix
  is empty (the completed runs reconstruct all of `e`), contributing `S.next Ec none`. -/
noncomputable def moveTerm (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) :
    Option (Label × PMF State) → ENNReal
  | none => if cur.1.trans = Stream'.Seq.nil then S.next Ec none else 0
  | some (l, ν) => ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
      * (⟨src, (innerWitness sys src ω).toScheduler⟩
          : ProbabilisticExecution sys).probOf cur.1 cur.2
      * (innerWitness sys src ω).next cur.1 (some (l, ν))

/-- **End-state after append.** Appending `B` after `A` yields an end-state that
is the end-state of `⟨endState of A, B⟩` — the last transition wins, and when `B`
is empty the end-state of `A` carries through. -/
theorem endState_append_shift (i : State) (A B : Stream'.Seq (Label × State))
    (hA : A.Terminates) (hAB : (A.append B).Terminates) (hB : B.Terminates) :
    (⟨i, A.append B⟩ : AlterSeq State Label).endState hAB
      = (⟨(⟨i, A⟩ : AlterSeq State Label).endState hA, B⟩ : AlterSeq State Label).endState hB := by
  classical
  rw [AlterSeq.endState_eq_getLast?, AlterSeq.endState_eq_getLast?,
    AlterSeq.endState_eq_getLast?]
  have htl : (A.append B).toList hAB = A.toList hA ++ B.toList hB :=
    Stream'.Seq.toList_append A B hA hB hAB
  simp only [htl]
  cases hBl : B.toList hB with
  | nil => simp only [List.append_nil, List.getLast?_nil, Option.elim]
  | cons x xs =>
    have hne : (x :: xs) ≠ [] := by simp
    rw [List.getLast?_append_of_ne_nil _ hne]
    cases hgl : (x :: xs).getLast? with
    | none => simp at hgl
    | some z => simp only [Option.elim]

/-- **Chained end-state.** When a config `chained`s from `s0` and its segments'
runs (with the current prefix) reconstruct `e`'s transitions, the composite
end-state is the current prefix's end-state. -/
theorem chained_endState :
    ∀ (segs : List (FlatSeg State Label)) (s0 : State)
      (cur : {p : AlterSeq State Label // p.trans.Terminates})
      (hT : (⟨s0, segTrans segs cur.1.trans⟩ : AlterSeq State Label).trans.Terminates),
      chained s0 segs cur.1.init →
      (⟨s0, segTrans segs cur.1.trans⟩ : AlterSeq State Label).endState hT
        = cur.1.endState cur.2
  | [], s0, cur, hT, hch => by
      have hs : cur.1.init = s0 := hch
      refine AlterSeq.endState_congr_pub ?_ hT cur.2
      simp only [segTrans]
      rw [← hs]
  | List.cons seg rest, s0, cur, hT, hch => by
      simp only [segTrans] at hT ⊢
      simp only [chained] at hch
      have hAterm : seg.run.trans.Terminates := seg.runT
      have hBterm : (segTrans rest cur.1.trans).Terminates := by
        refine ⟨Nat.find hT, ?_⟩
        have happ : (seg.run.trans.append (segTrans rest cur.1.trans)).TerminatedAt
            (Nat.find hAterm + Nat.find hT) :=
          Stream'.Seq.terminated_stable _ (Nat.le_add_left (Nat.find hT) (Nat.find hAterm))
            (Nat.find_spec hT)
        have hget := Stream'.Seq.get?_append_find hAterm (segTrans rest cur.1.trans) (Nat.find hT)
        change (segTrans rest cur.1.trans).get? (Nat.find hT) = none
        rw [← hget]; exact happ
      rw [endState_append_shift s0 seg.run.trans (segTrans rest cur.1.trans) hAterm hT hBterm]
      have heqseg : (⟨s0, seg.run.trans⟩ : AlterSeq State Label) = seg.run := by rw [← hch.1]
      have hj : (⟨s0, seg.run.trans⟩ : AlterSeq State Label).endState hAterm
          = seg.run.endState seg.runT :=
        AlterSeq.endState_congr_pub heqseg hAterm seg.runT
      rw [hj]
      exact chained_endState rest (seg.run.endState seg.runT) cur hBterm hch.2

/-! ### Layer 4d: the ω-witness under DESIGN v3 (decision-point compression)

Supersedes Layer 4c's false normalizer (retained above as documentation of the
false-normalizer pitfall). The interleaved empty macro-steps ("stalls") that made
4c's belief normalizer diverge are here compressed into an analytic factor
`stallSum` (deliverable S). Conditioned on the composite `sys`-execution sitting at
a concrete state `s0`, the empty-inner-run masses of the per-macro-step inner
witnesses are genuine PMF-conditional quantities, so the decisive outcomes reached
after a run of empty macro-steps — halt at a macro-boundary, or a genuine
(nonempty) first inner move — are disjoint and their total mass is `≤ 1`
(`stallSum_le_one`). This is the (S)-side sub-probability bound that feeds the
(N)-argument's finite normalizer. -/

/-- Conditional immediate-halt (empty-inner-run) probability of the per-emission
inner witness `innerWitness sys src ω`, at concrete state `s0`. -/
noncomputable def iwHaltMass (sys : System State Label) (src : PMF State)
    (ω : PMF (PMF State)) (s0 : State) : ENNReal :=
  (innerWitness sys src ω).next ⟨s0, Seq.nil⟩ none

/-- Conditional first-move (nonempty-inner-run) total mass of the per-emission
inner witness `innerWitness sys src ω`, at concrete state `s0`. -/
noncomputable def iwMoveMass (sys : System State Label) (src : PMF State)
    (ω : PMF (PMF State)) (s0 : State) : ENNReal :=
  ∑' lν : Label × PMF State, (innerWitness sys src ω).next ⟨s0, Seq.nil⟩ (some lν)

/-- The inner witness's move and halt masses partition its unit step-mass at `s0`. -/
theorem iwMoveMass_add_iwHaltMass (sys : System State Label) (src : PMF State)
    (ω : PMF (PMF State)) (s0 : State) :
    iwMoveMass sys src ω s0 + iwHaltMass sys src ω s0 = 1 := by
  unfold iwMoveMass iwHaltMass
  rw [add_comm, ← tsumOpt (fun o => (innerWitness sys src ω).next ⟨s0, Seq.nil⟩ o)]
  exact PMF.tsum_coe _

/-- **The stall partial sum.** The decisive mass captured within the first `n`
empty macro-steps from macro-history `E` (macro-source `src`), conditioned on the
composite sitting at concrete state `s0`. Mirrors `macroHalted`: at each level the
composite either halts (`S.next E none`), makes a genuine first inner move
(`iwMoveMass`), or the inner witness stalls (`iwHaltMass`) and the macro-run steps
into `macroExtend E m'` with new source `m'`, still at `s0`. -/
noncomputable def stallPart (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label) (s0 : State) : ℕ → ENNReal
  | 0 => 0
  | n + 1 => S.next E none
      + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * (iwMoveMass sys src ω s0
              + iwHaltMass sys src ω s0 * ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n)

/-- **The stall sum** (deliverable S): the total decisive mass from `E`, as the
supremum over the stall depth. -/
noncomputable def stallSum (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label) (s0 : State) : ENNReal :=
  ⨆ n : ℕ, stallPart S src E s0 n

/-- Each stall partial sum is a sub-probability. The engine of argument (S): the
decisive outcomes reachable within `n` stall steps are disjoint, so their total is
`≤ 1`. Proof by induction on `n`; the step uses that `iwMoveMass + iwHaltMass = 1`
and that `S.next E` is a PMF (its `none` mass plus its internal-`τ` masses sum to
`1`). -/
theorem stallPart_le_one (S : WeakScheduler (𝒟(sys^w))) (s0 : State) (n : ℕ) :
    ∀ (src : PMF State) (E : AlterSeq (PMF State) Label), stallPart S src E s0 n ≤ 1 := by
  induction n with
  | zero => intro src E; simp only [stallPart]; exact zero_le_one
  | succ n IH =>
    intro src E
    simp only [stallPart]
    -- each ω-summand is bounded by the raw macro-choice mass `S.next E (some (τ, ω))`
    have hinner : ∀ ω : PMF (PMF State),
        iwMoveMass sys src ω s0
            + iwHaltMass sys src ω s0 * ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n
          ≤ 1 := by
      intro ω
      have hle : (∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n) ≤ 1 := by
        calc (∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n)
            ≤ ∑' m', ω m' * 1 :=
              ENNReal.tsum_le_tsum (fun m' => mul_le_mul_left' (IH m' (macroExtend E m')) _)
          _ = 1 := by rw [tsum_congr (fun m' => mul_one _)]; exact PMF.tsum_coe _
      calc iwMoveMass sys src ω s0
              + iwHaltMass sys src ω s0 * ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n
          ≤ iwMoveMass sys src ω s0 + iwHaltMass sys src ω s0 * 1 := by gcongr
        _ = 1 := by rw [mul_one]; exact iwMoveMass_add_iwHaltMass sys src ω s0
    have hinj : (∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)))
        ≤ ∑' lν : Label × PMF (PMF State), S.next E (some lν) :=
      ENNReal.tsum_comp_le_tsum_of_injective
        (fun a b h => congrArg Prod.snd h) (fun lν => S.next E (some lν))
    calc S.next E none
            + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
                * (iwMoveMass sys src ω s0 + iwHaltMass sys src ω s0
                    * ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n)
        ≤ S.next E none + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) * 1 := by
          gcongr with ω; exact hinner ω
      _ = S.next E none + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) := by
          simp only [mul_one]
      _ ≤ S.next E none + ∑' lν : Label × PMF (PMF State), S.next E (some lν) := by gcongr
      _ = ∑' o, S.next E o := (tsumOpt (S.next E)).symm
      _ = 1 := PMF.tsum_coe _

/-- **(S) sub-probability bound.** The stall sum is `≤ 1` (`stallSum_le_one`). -/
theorem stallSum_le_one (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label) (s0 : State) : stallSum S src E s0 ≤ 1 :=
  iSup_le (fun n => stallPart_le_one S s0 n src E)

/-- The stall partial sums are monotone in the depth: one more level only adds
decisive mass. -/
theorem stallPart_mono (S : WeakScheduler (𝒟(sys^w))) (s0 : State) (n : ℕ) :
    ∀ (src : PMF State) (E : AlterSeq (PMF State) Label),
      stallPart S src E s0 n ≤ stallPart S src E s0 (n + 1) := by
  induction n with
  | zero => intro src E; simp only [stallPart]; exact zero_le'
  | succ n IH =>
    intro src E
    simp only [stallPart]
    gcongr with ω m'
    exact IH m' (macroExtend E m')

/-- **Monotone `tsum`↔`iSup` interchange.** For an `ENNReal` family monotone in
its `ℕ` parameter, the countable sum of the pointwise suprema equals the supremum
of the countable sums (monotone convergence for the counting measure). Broadly
useful; here it drives `stall_unfold`. -/
theorem tsum_iSup_of_monotone {ι : Type} (f : ℕ → ι → ENNReal)
    (hf : ∀ i, Monotone (fun n => f n i)) :
    ∑' i, ⨆ n, f n i = ⨆ n, ∑' i, f n i := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone (f := fun a n => f n a) hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]

/-- **`stall_unfold` — the stall fixpoint.** The stall sum satisfies the
one-macro-step fixpoint equation: from `E` the composite either halts now
(`S.next E none`), or takes a macro-emission `ω`, whereupon it either makes a
genuine first inner move (`iwMoveMass`) or the inner witness stalls
(`iwHaltMass`) and the stall continues from the sampled successor `m'`. Proved by
the monotone `⨆`↔`∑'`/`+`/`*` interchange over the stall depth. -/
theorem stall_unfold (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label) (s0 : State) :
    stallSum S src E s0 = S.next E none
      + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * (iwMoveMass sys src ω s0
              + iwHaltMass sys src ω s0
                * ∑' m', ω m' * stallSum S m' (macroExtend E m') s0) := by
  have hmono : ∀ (src' : PMF State) (E' : AlterSeq (PMF State) Label),
      Monotone (fun n => stallPart S src' E' s0 n) :=
    fun src' E' => monotone_nat_of_le_succ (fun n => stallPart_mono S s0 n src' E')
  have hXmono : ∀ ω : PMF (PMF State),
      Monotone (fun n => ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n) :=
    fun ω _ _ hab => ENNReal.tsum_le_tsum
      (fun m' => mul_le_mul_left' (hmono m' (macroExtend E m') hab) (ω m'))
  have hhmono : ∀ ω : PMF (PMF State),
      Monotone (fun n => iwMoveMass sys src ω s0
        + iwHaltMass sys src ω s0 * ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n) :=
    fun ω _ _ hab => add_le_add le_rfl
      (mul_le_mul_left' (hXmono ω hab) (iwHaltMass sys src ω s0))
  have hX : ∀ ω : PMF (PMF State),
      (⨆ n, ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n)
        = ∑' m', ω m' * stallSum S m' (macroExtend E m') s0 := by
    intro ω
    rw [← tsum_iSup_of_monotone (fun n m' => ω m' * stallPart S m' (macroExtend E m') s0 n)
      (fun m' _ _ hab => mul_le_mul_left' (hmono m' (macroExtend E m') hab) (ω m'))]
    exact tsum_congr (fun m' => by rw [← ENNReal.mul_iSup]; rfl)
  have hshift : (⨆ n, stallPart S src E s0 (n + 1)) = stallSum S src E s0 :=
    (hmono src E).iSup_nat_add 1
  rw [← hshift]
  simp only [stallPart]
  rw [← ENNReal.add_iSup]
  congr 1
  rw [← tsum_iSup_of_monotone
    (fun n ω => S.next E (some (Silent.τ, ω))
      * (iwMoveMass sys src ω s0 + iwHaltMass sys src ω s0
          * ∑' m', ω m' * stallPart S m' (macroExtend E m') s0 n))
    (fun ω _ _ hab => mul_le_mul_left' (hhmono ω hab) (S.next E (some (Silent.τ, ω))))]
  refine tsum_congr (fun ω => ?_)
  rw [← ENNReal.mul_iSup]
  congr 1
  rw [← ENNReal.add_iSup]
  congr 1
  rw [← ENNReal.mul_iSup]
  congr 1
  exact hX ω

/-! ### Layer 4d (cont.): the DConfig carrier + `dSched` (DESIGN v3, D2+D3)

The decision-point carrier and its normalized belief scheduler. Per DESIGN v3 the
hidden configuration behind an observed `sys`-history is a list of **nonempty**
completed inner segments plus a current in-progress inner prefix. Nonemptiness is
the fix for 4c's divergent normalizer: each completed segment consumes ≥ 1
observed step, so a length-`ℓ` history admits only finitely many segmentations,
and the belief masses (disjoint-run contributions) sum to `≤ 1` — the
`dDenom_ne_top` jewel. The segment/weight/move machinery is transplanted verbatim
from 4c's PROVEN `segTrans`/`chained`/`segWeight`/`moveTerm`; only the
nonemptiness guard is added. -/

/-- **The decision-point carrier.** A hidden configuration behind an observed
`sys`-history: completed inner segments `segs` (each nonempty, enforced by
`dConsistent`) plus the current in-progress inner prefix `cur`. -/
structure DConfig (State Label : Type) where
  /-- Completed inner macro-segments (all nonempty at a decision point). -/
  segs : List (FlatSeg State Label)
  /-- Current in-progress inner prefix (may be empty at a fresh decision point). -/
  cur : AlterSeq State Label
  /-- The current prefix terminates. -/
  curT : cur.trans.Terminates

/-- Consistency of a `DConfig` with an observed history `e`: every completed
segment's inner run is nonempty (the decision-point invariant), the segments and
the current prefix reconstruct `e`'s transitions, and the runs chain from
`e.init`. -/
def dConsistent (e : AlterSeq State Label) (c : DConfig State Label) : Prop :=
  (∀ seg ∈ c.segs, seg.run.trans ≠ Stream'.Seq.nil)
    ∧ segTrans c.segs c.cur.trans = e.trans ∧ chained e.init c.segs c.cur.init

open Classical in
/-- **The DConfig belief numerator** rooted at macro-history `E` (source `μ0`), at
observed `sys`-history `e` and move `o`: sum over decision-point configs
consistent with `e` of the segment path-weight times the current-run move
contribution. Identical to 4c's `flattenNum` except the config space is the
nonempty-segment carrier `DConfig` (guarded by `dConsistent`). -/
noncomputable def dNum (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates})
    (o : Option (Label × PMF State)) : ENNReal :=
  ∑' c : DConfig State Label,
    (if dConsistent e.1 c then (1 : ENNReal) else 0)
      * segWeight S μ0 E c.segs
      * moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩ o

/-- The DConfig belief denominator: total numerator mass over all moves. -/
noncomputable def dDenom (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) : ENNReal :=
  ∑' o, dNum S μ0 E e o

/-- By definition `dDenom = ∑' o, dNum`. -/
theorem dNum_tsum (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (∑' o, dNum S μ0 E e o) = dDenom S μ0 E e := rfl

/-- Total current-run move mass of a config at prefix `cur`, source `src`,
history `Ec`: `∑' o, moveTerm o`. -/
noncomputable def moveTot (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) : ENNReal :=
  ∑' o, moveTerm S src Ec cur o

/-- The current-run move total is a sub-probability (`≤ 1`): its `none` mass is
`≤ S.next Ec none`, and each `some`-emission `ω`-summand is bounded by
`S.next Ec (some (τ,ω))` since `probOf ≤ 1` and the inner witness's `some`-total
`≤ 1`; together they sum to `∑' o, S.next Ec o = 1`. -/
theorem moveTot_le_one (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (Ec : AlterSeq (PMF State) Label)
    (cur : {p : AlterSeq State Label // p.trans.Terminates}) :
    moveTot S src Ec cur ≤ 1 := by
  unfold moveTot
  rw [tsumOpt (moveTerm S src Ec cur)]
  have hnone : moveTerm S src Ec cur none ≤ S.next Ec none := by
    simp only [moveTerm]; split <;> simp
  have hsome : (∑' lν : Label × PMF State, moveTerm S src Ec cur (some lν))
      ≤ ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω)) := by
    have e1 : ∀ lν : Label × PMF State, moveTerm S src Ec cur (some lν)
        = ∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω))
            * (⟨src, (innerWitness sys src ω).toScheduler⟩ :
                ProbabilisticExecution sys).probOf cur.1 cur.2
            * (innerWitness sys src ω).next cur.1 (some lν) := fun ⟨l, ν⟩ => rfl
    simp only [e1]
    rw [ENNReal.tsum_comm]
    refine ENNReal.tsum_le_tsum (fun ω => ?_)
    have hp : (⟨src, (innerWitness sys src ω).toScheduler⟩ :
        ProbabilisticExecution sys).probOf cur.1 cur.2 ≤ 1 :=
      (ProbabilisticExecution.probOf_le_init _ _ _).trans (PMF.coe_le_one _ _)
    have hm : (∑' lν : Label × PMF State, (innerWitness sys src ω).next cur.1 (some lν)) ≤ 1 := by
      calc (∑' lν : Label × PMF State, (innerWitness sys src ω).next cur.1 (some lν))
          ≤ ∑' o, (innerWitness sys src ω).next cur.1 o := by
            rw [tsumOpt]; exact le_add_self
        _ = 1 := PMF.tsum_coe _
    rw [ENNReal.tsum_mul_left]
    calc S.next Ec (some (Silent.τ, ω))
            * (⟨src, (innerWitness sys src ω).toScheduler⟩ :
                ProbabilisticExecution sys).probOf cur.1 cur.2
            * ∑' lν : Label × PMF State, (innerWitness sys src ω).next cur.1 (some lν)
        = S.next Ec (some (Silent.τ, ω))
            * ((⟨src, (innerWitness sys src ω).toScheduler⟩ :
                ProbabilisticExecution sys).probOf cur.1 cur.2
                * ∑' lν : Label × PMF State, (innerWitness sys src ω).next cur.1 (some lν)) := by
          ring
      _ ≤ S.next Ec (some (Silent.τ, ω)) * 1 := mul_le_mul_left' (mul_le_one' hp hm) _
      _ = S.next Ec (some (Silent.τ, ω)) := mul_one _
  have hinj : (∑' ω : PMF (PMF State), S.next Ec (some (Silent.τ, ω)))
      ≤ ∑' lν : Label × PMF (PMF State), S.next Ec (some lν) :=
    ENNReal.tsum_comp_le_tsum_of_injective
      (fun a b h => congrArg Prod.snd h) (fun lν => S.next Ec (some lν))
  calc moveTerm S src Ec cur none
          + ∑' lν : Label × PMF State, moveTerm S src Ec cur (some lν)
      ≤ S.next Ec none + ∑' lν : Label × PMF (PMF State), S.next Ec (some lν) := by
        exact add_le_add hnone (hsome.trans hinj)
    _ = ∑' o, S.next Ec o := (tsumOpt (S.next Ec)).symm
    _ = 1 := PMF.tsum_coe _

open Classical in
/-- The denominator as the config-sum of segment weight times the current-run
move total (swap `∑' o`/`∑' c`, then `∑' o` factors as `moveTot`). -/
theorem dDenom_eq_moveTot (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    dDenom S μ0 E e = ∑' c : DConfig State Label,
      (if dConsistent e.1 c then (1 : ENNReal) else 0) * segWeight S μ0 E c.segs
        * moveTot S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩ := by
  unfold dDenom dNum moveTot
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun c => ?_)
  rw [← ENNReal.tsum_mul_left]

/-- Dropping the exact length of a terminating left factor from an `append`
recovers the right factor. -/
private theorem drop_append_length {α : Type} (A Y : Stream'.Seq α)
    (hA : A.Terminates) : (A.append Y).drop (A.length hA) = Y := by
  apply Stream'.Seq.ext
  intro m
  rw [Stream'.Seq.drop_get?]
  exact Stream'.Seq.get?_append_find hA Y m

/-- Length is additive over `append` of terminating sequences. -/
private theorem length_append_seq {α : Type} (A B : Stream'.Seq α)
    (hA : A.Terminates) (hB : B.Terminates) (hAB : (A.append B).Terminates) :
    (A.append B).length hAB = A.length hA + B.length hB := by
  rw [← Stream'.Seq.length_toList _ hAB,
    Stream'.Seq.toList_append A B hA hB hAB, List.length_append,
    Stream'.Seq.length_toList, Stream'.Seq.length_toList]

/-- Length is invariant under equality of the underlying sequence. -/
private theorem length_congr {α : Type} (s t : Stream'.Seq α)
    (hs : s.Terminates) (ht : t.Terminates) (h : s = t) : s.length hs = t.length ht := by
  subst h; rfl

/-- `DConfig` reindexes as a `(segs, current)` pair. -/
private def dcE : DConfig State Label ≃
    List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates} where
  toFun c := (c.segs, ⟨c.cur, c.curT⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl

/-- `FlatSeg` reindexes as `(emit, succ, run)`. -/
private def flatSegEquiv : FlatSeg State Label ≃
    PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates} where
  toFun s := (s.emit, s.succ, ⟨s.run, s.runT⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, ⟨_, _⟩⟩ => rfl

/-- Peel the head of a `List`-indexed `ENNReal` tsum. -/
private def listOptEquiv (X : Type) : List X ≃ Option (X × List X) where
  toFun l := l.casesOn none (fun x t => some (x, t))
  invFun o := o.casesOn List.nil (fun p => List.cons p.1 p.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩) <;> rfl

private theorem listSplit {X : Type} (f : List X → ENNReal) :
    ∑' l : List X, f l = f [] + ∑' q : X × List X, f (q.1 :: q.2) := by
  have h := tsumOpt (fun o => f ((listOptEquiv X).symm o))
  rw [Equiv.tsum_eq (listOptEquiv X).symm f] at h
  exact h

/-- The residual observed history after peeling a first segment `seg` from `e`:
start at the segment's end-state, transitions are `e`'s with the run's prefix
dropped. -/
private noncomputable def dResidual
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) : {q : AlterSeq State Label // q.trans.Terminates} :=
  ⟨⟨seg.run.endState seg.runT,
      e.1.trans.drop (seg.run.trans.length seg.runT)⟩,
    WeakScheduler.drop_terminates e.2 _⟩

/-- A first segment `seg` is a legal peel from `e`: its run starts at `e.init`,
its (nonempty) transition prefix is a genuine prefix of `e`'s transitions. -/
private def segPre (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) : Prop :=
  seg.run.init = e.1.init
    ∧ seg.run.trans.append (e.1.trans.drop (seg.run.trans.length seg.runT)) = e.1.trans
    ∧ seg.run.trans ≠ Stream'.Seq.nil

/-- **Segment-peeling decomposition of `dConsistent`.** A config with a head
segment is consistent with `e` iff that head is a legal prefix peel (`segPre`)
and the tail config is consistent with the residual history. -/
private theorem dConsistent_cons_iff
    (e : {q : AlterSeq State Label // q.trans.Terminates})
    (seg : FlatSeg State Label) (rest : List (FlatSeg State Label))
    (curA : AlterSeq State Label) (hcur : curA.trans.Terminates) :
    dConsistent e.1 ⟨seg :: rest, curA, hcur⟩ ↔
      segPre e seg ∧ dConsistent (dResidual e seg).1 ⟨rest, curA, hcur⟩ := by
  have hdrop : (seg.run.trans.append (segTrans rest curA.trans)).drop
        (seg.run.trans.length seg.runT) = segTrans rest curA.trans :=
    drop_append_length seg.run.trans (segTrans rest curA.trans) seg.runT
  simp only [dConsistent, segPre, dResidual, segTrans, chained,
    List.forall_mem_cons]
  constructor
  · rintro ⟨⟨hne, hrest_ne⟩, htrans, hinit, hchain⟩
    have hYeq : e.1.trans.drop (seg.run.trans.length seg.runT) = segTrans rest curA.trans := by
      rw [← htrans]; exact hdrop
    refine ⟨⟨hinit, ?_, hne⟩, hrest_ne, ?_, hchain⟩
    · rw [hYeq]; exact htrans
    · exact hYeq.symm
  · rintro ⟨⟨hinit, hpre, hne⟩, hrest_ne, hseg, hchain⟩
    refine ⟨⟨hne, hrest_ne⟩, ?_, hinit, hchain⟩
    rw [hseg]; exact hpre

open Classical in
/-- The denominator sum, reindexed over `(segs, current)` pairs — the recursion
carrier for the peeling induction. -/
private noncomputable def dW (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) : ENNReal :=
  ∑' p : List (FlatSeg State Label) × {q : AlterSeq State Label // q.trans.Terminates},
    (if dConsistent e.1 ⟨p.1, p.2.1, p.2.2⟩ then (1 : ENNReal) else 0)
      * segWeight S src E p.1
      * moveTot S (segSrc src p.1) (segHist E p.1) p.2

open Classical in
private theorem dDenom_eq_dW (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    dDenom S μ0 E e = dW S μ0 E e := by
  rw [dDenom_eq_moveTot]
  exact (Equiv.tsum_eq dcE.symm _).symm

open Classical in
/-- The head-segment weight sum is a sub-probability: dropping the peel guard and
the successor mass, the remaining `emit`-indexed mass is `≤ ∑' o, S.next o = 1`
via the inner witnesses' Kraft bound (`haltMass_tsum_le_one`). -/
private theorem headSum_le_one (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    (∑' seg : FlatSeg State Label,
      (if segPre e seg then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)) ≤ 1 := by
  calc (∑' seg : FlatSeg State Label,
          (if segPre e seg then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩))
      ≤ ∑' seg : FlatSeg State Label,
          S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩ :=
        ENNReal.tsum_le_tsum (fun seg => by split_ifs with h <;> simp)
    _ = ∑' t : PMF (PMF State) × PMF State × {q : AlterSeq State Label // q.trans.Terminates},
          S.next E (some (Silent.τ, t.1)) * t.1 t.2.1
            * (innerWitness sys src t.1).haltMass src t.2.2 :=
        Equiv.tsum_eq flatSegEquiv (fun t => S.next E (some (Silent.τ, t.1)) * t.1 t.2.1
          * (innerWitness sys src t.1).haltMass src t.2.2)
    _ = ∑' emit, ∑' succ, ∑' r, S.next E (some (Silent.τ, emit)) * emit succ
            * (innerWitness sys src emit).haltMass src r := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr (fun emit => ?_)
        rw [ENNReal.tsum_prod']
    _ ≤ ∑' emit : PMF (PMF State), S.next E (some (Silent.τ, emit)) :=
        ENNReal.tsum_le_tsum (fun emit => by
          calc (∑' succ, ∑' r, S.next E (some (Silent.τ, emit)) * emit succ
                  * (innerWitness sys src emit).haltMass src r)
              = ∑' r, ∑' succ, S.next E (some (Silent.τ, emit)) * emit succ
                  * (innerWitness sys src emit).haltMass src r := ENNReal.tsum_comm
            _ = ∑' r, (S.next E (some (Silent.τ, emit))
                    * (innerWitness sys src emit).haltMass src r) * ∑' succ, emit succ := by
                refine tsum_congr (fun r => ?_)
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr (fun succ => by ring)
            _ = ∑' r, S.next E (some (Silent.τ, emit))
                  * (innerWitness sys src emit).haltMass src r := by
                simp only [PMF.tsum_coe, mul_one]
            _ = S.next E (some (Silent.τ, emit))
                  * ∑' r, (innerWitness sys src emit).haltMass src r := ENNReal.tsum_mul_left
            _ ≤ S.next E (some (Silent.τ, emit)) * 1 := by
                gcongr; exact WeakScheduler.haltMass_tsum_le_one _ _
            _ = S.next E (some (Silent.τ, emit)) := mul_one _)
    _ ≤ ∑' lν : Label × PMF (PMF State), S.next E (some lν) :=
        ENNReal.tsum_comp_le_tsum_of_injective
          (fun a b h => congrArg Prod.snd h) (fun lν => S.next E (some lν))
    _ ≤ ∑' o, S.next E o := by rw [tsumOpt]; exact le_add_self
    _ = 1 := PMF.tsum_coe _

/-- A config with no completed segments is consistent with `e` iff its current
prefix *is* `e`. -/
private theorem dConsistent_nil_iff
    (e cur : {q : AlterSeq State Label // q.trans.Terminates}) :
    dConsistent e.1 ⟨[], cur.1, cur.2⟩ ↔ cur = e := by
  constructor
  · rintro ⟨_, htr, hin⟩
    obtain ⟨cval, cproof⟩ := cur
    obtain ⟨ci, ct⟩ := cval
    apply Subtype.ext
    show (⟨ci, ct⟩ : AlterSeq State Label) = e.1
    have e1 : ci = e.1.init := hin
    have e2 : ct = e.1.trans := htr
    rw [e1, e2]
  · rintro rfl
    exact ⟨fun s hs => by simp at hs, rfl, rfl⟩

open Classical in
/-- Base case of the peel: the no-segment configs contribute exactly the
current-run move total at `e`. -/
private theorem peelBase (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    (∑' cur : {q : AlterSeq State Label // q.trans.Terminates},
      (if dConsistent e.1 (⟨[], cur.1, cur.2⟩ : DConfig State Label) then (1 : ENNReal) else 0)
        * segWeight S src E ([] : List (FlatSeg State Label))
        * moveTot S (segSrc src ([] : List (FlatSeg State Label)))
            (segHist E ([] : List (FlatSeg State Label))) cur)
      = moveTot S src E e := by
  rw [tsum_eq_single e ?_]
  · rw [if_pos ((dConsistent_nil_iff e e).mpr rfl)]
    simp [segWeight, segSrc, segHist]
  · intro cur hne
    rw [if_neg (fun hc => hne ((dConsistent_nil_iff e cur).mp hc)), zero_mul, zero_mul]

open Classical in
/-- Per-segment reduction: the configs whose first completed segment is `seg`
contribute the head weight times the residual denominator (nonzero only when
`seg` is a legal prefix peel). -/
private theorem peelSeg (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) (seg : FlatSeg State Label) :
    (∑' rest : List (FlatSeg State Label),
      ∑' cur : {q : AlterSeq State Label // q.trans.Terminates},
        (if dConsistent e.1 ⟨seg :: rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
          * segWeight S src E (seg :: rest)
          * moveTot S (segSrc src (seg :: rest)) (segHist E (seg :: rest)) cur)
      = (if segPre e seg then (1 : ENNReal) else 0)
          * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
              * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)
          * dW S seg.succ (macroExtend E seg.succ) (dResidual e seg) := by
  by_cases hsp : segPre e seg
  · rw [if_pos hsp, one_mul]
    unfold dW
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun rest => ?_)
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr (fun cur => ?_)
    simp only [dConsistent_cons_iff, hsp, true_and]
    show (if dConsistent (dResidual e seg).1 ⟨rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
        * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
            * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩
            * segWeight S seg.succ (macroExtend E seg.succ) rest)
        * moveTot S (segSrc seg.succ rest) (segHist (macroExtend E seg.succ) rest) cur
      = (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
          * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)
        * ((if dConsistent (dResidual e seg).1 ⟨rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
            * segWeight S seg.succ (macroExtend E seg.succ) rest
            * moveTot S (segSrc seg.succ rest) (segHist (macroExtend E seg.succ) rest) cur)
    ring
  · rw [if_neg hsp, zero_mul, zero_mul]
    have hzero : ∀ (rest : List (FlatSeg State Label))
        (cur : {q : AlterSeq State Label // q.trans.Terminates}),
        (if dConsistent e.1 ⟨seg :: rest, cur.1, cur.2⟩ then (1 : ENNReal) else 0)
            * segWeight S src E (seg :: rest)
            * moveTot S (segSrc src (seg :: rest)) (segHist E (seg :: rest)) cur = 0 := by
      intro rest cur
      rw [if_neg (fun hc => hsp ((dConsistent_cons_iff e seg rest cur.1 cur.2).mp hc).1),
        zero_mul, zero_mul]
    simp only [hzero, tsum_zero]

open Classical in
/-- **The peeling recursion for `dW`.** The denominator carrier splits into the
no-segment base (`moveTot`) plus the head-segment contributions, each recursing
into the residual history's denominator. -/
private theorem dW_peel (S : WeakScheduler (𝒟(sys^w))) (src : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {q : AlterSeq State Label // q.trans.Terminates}) :
    dW S src E e = moveTot S src E e
      + ∑' seg : FlatSeg State Label,
          (if segPre e seg then (1 : ENNReal) else 0)
            * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)
            * dW S seg.succ (macroExtend E seg.succ) (dResidual e seg) := by
  conv_lhs => rw [dW, ENNReal.tsum_prod', listSplit]
  rw [peelBase]
  congr 1
  rw [ENNReal.tsum_prod']
  exact tsum_congr (fun seg => peelSeg S src E e seg)

open Classical in
/-- **The denominator is bounded by `length e + 1`**, by strong induction on the
observed-history length: peel the first completed segment, whose nonempty run
strictly shortens the residual history (so the IH applies), and the head-segment
mass sums to `≤ 1` (`headSum_le_one`); the base `moveTot ≤ 1`. -/
private theorem dW_le (S : WeakScheduler (𝒟(sys^w))) :
    ∀ (n : ℕ) (src : PMF State) (E : AlterSeq (PMF State) Label)
      (e : {q : AlterSeq State Label // q.trans.Terminates}),
      e.1.trans.length e.2 = n → dW S src E e ≤ ((n + 1 : ℕ) : ENNReal) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro src E e he
    rw [dW_peel]
    have hmove : moveTot S src E e ≤ 1 := moveTot_le_one S src E e
    have hrec : (∑' seg : FlatSeg State Label,
        (if segPre e seg then (1 : ENNReal) else 0)
          * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
              * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)
          * dW S seg.succ (macroExtend E seg.succ) (dResidual e seg)) ≤ (n : ENNReal) := by
      calc (∑' seg : FlatSeg State Label,
              (if segPre e seg then (1 : ENNReal) else 0)
                * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                    * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)
                * dW S seg.succ (macroExtend E seg.succ) (dResidual e seg))
          ≤ ∑' seg : FlatSeg State Label,
              (if segPre e seg then (1 : ENNReal) else 0)
                * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                    * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩)
                * (n : ENNReal) := by
            refine ENNReal.tsum_le_tsum (fun seg => ?_)
            by_cases hsp : segPre e seg
            · have hkpos : 1 ≤ seg.run.trans.length seg.runT := by
                rw [Nat.one_le_iff_ne_zero]
                exact fun h0 => hsp.2.2 (Stream'.Seq.length_eq_zero.mp h0)
              have hlen : e.1.trans.length e.2
                  = seg.run.trans.length seg.runT
                    + (e.1.trans.drop (seg.run.trans.length seg.runT)).length
                        (WeakScheduler.drop_terminates e.2 _) := by
                rw [← length_append_seq seg.run.trans
                    (e.1.trans.drop (seg.run.trans.length seg.runT)) seg.runT
                    (WeakScheduler.drop_terminates e.2 _) (by rw [hsp.2.1]; exact e.2)]
                exact length_congr _ _ e.2 _ hsp.2.1.symm
              have hdw := IH ((e.1.trans.drop (seg.run.trans.length seg.runT)).length
                  (WeakScheduler.drop_terminates e.2 _)) (by omega) seg.succ
                  (macroExtend E seg.succ) (dResidual e seg) rfl
              rw [if_pos hsp]
              gcongr
              exact hdw.trans (Nat.cast_le.mpr (by omega))
            · rw [if_neg hsp]; simp
        _ = (∑' seg : FlatSeg State Label,
              (if segPre e seg then (1 : ENNReal) else 0)
                * (S.next E (some (Silent.τ, seg.emit)) * seg.emit seg.succ
                    * (innerWitness sys src seg.emit).haltMass src ⟨seg.run, seg.runT⟩))
              * (n : ENNReal) := by rw [ENNReal.tsum_mul_right]
        _ ≤ 1 * (n : ENNReal) := by gcongr; exact headSum_le_one S src E e
        _ = (n : ENNReal) := one_mul _
    refine le_trans (add_le_add hmove hrec) (le_of_eq ?_)
    push_cast; ring

/-- **The DConfig belief denominator is finite (the design-validating jewel).**
Where 4c's `flattenDenom` diverged (unbounded empty completed segments), the
decision-point carrier admits only finitely many segmentations of `e`: each
completed segment is nonempty (consumes ≥ 1 observed transition), so the segment
count is bounded by `e`'s length, and the disjoint-run belief masses telescope to
`≤ 1` against `S.next`'s and the inner witnesses' unit totals. -/
theorem dDenom_ne_top (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    dDenom S μ0 E e ≠ ⊤ := by
  -- Reindex to `dW`, bounded by `length e + 1` (strong induction, peeling the
  -- first nonempty completed segment): a finite `ℕ` cast, hence `≠ ⊤`.
  rw [dDenom_eq_dW]
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
    (dW_le S (e.1.trans.length e.2) μ0 E e rfl)

open Classical in
/-- **The DConfig composite ω-witness scheduler** rooted at macro-history `E`,
source `μ0`: at each observed `sys`-history the belief numerator normalized.
`valid`/`internal_only` transplanted verbatim from 4c's proven `flattenSched`
(same extraction: config → current inner witness's genuine move). -/
noncomputable def dSched (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) : WeakScheduler sys where
  next e := if hT : e.trans.Terminates then
      (if h0 : dDenom S μ0 E ⟨e, hT⟩ = 0 then PMF.pure none
        else PMF.normalize (dNum S μ0 E ⟨e, hT⟩) (by rw [dNum_tsum]; exact h0)
          (by rw [dNum_tsum]; exact dDenom_ne_top S μ0 E ⟨e, hT⟩))
    else PMF.pure none
  valid := by
    classical
    intro e n s hterm hstate l ν hsupp
    by_cases hT : e.trans.Terminates
    · rw [dif_pos hT] at hsupp
      by_cases h0 : dDenom S μ0 E ⟨e, hT⟩ = 0
      · rw [dif_pos h0, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
        exact absurd rfl hsupp
      · rw [dif_neg h0, PMF.mem_support_normalize_iff] at hsupp
        have hgne : dNum S μ0 E ⟨e, hT⟩ (some (l, ν)) ≠ 0 := hsupp
        rw [dNum] at hgne
        obtain ⟨c, hc⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hgne)
        have hguard : dConsistent e c := by
          by_contra hcon
          rw [if_neg hcon, zero_mul, zero_mul] at hc; exact hc rfl
        have hmove : moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩
            (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hc
        simp only [moveTerm] at hmove
        obtain ⟨ω, hω⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hmove)
        have hnext : (innerWitness sys (segSrc μ0 c.segs) ω).next c.cur (some (l, ν)) ≠ 0 :=
          right_ne_zero_of_mul hω
        have hsend : s = e.endState hT := by
          have hle1 : Nat.find hT ≤ n := Nat.find_le hterm
          have hle2 : n ≤ Nat.find hT := by
            by_contra hlt
            push_neg at hlt
            obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
            have hget : e.trans.get? m = none :=
              Stream'.Seq.terminated_stable e.trans (by omega) (Nat.find_spec hT)
            rw [hm] at hstate
            change (e.trans.get? m).map Prod.snd = some s at hstate
            rw [hget] at hstate; simp at hstate
          have hn : n = Nat.find hT := le_antisymm hle2 hle1
          rw [hn, AlterSeq.stateAt_find_eq_endState e hT] at hstate
          exact (Option.some.inj hstate).symm
        have heqe : (⟨e.init, segTrans c.segs c.cur.trans⟩ : AlterSeq State Label) = e := by
          rw [hguard.2.1]
        have hTeq' : (⟨e.init, segTrans c.segs c.cur.trans⟩ :
            AlterSeq State Label).trans.Terminates := by rw [heqe]; exact hT
        have hcend : e.endState hT = c.cur.endState c.curT := by
          rw [← AlterSeq.endState_congr_pub heqe hTeq' hT]
          exact chained_endState c.segs e.init ⟨c.cur, c.curT⟩ hTeq' hguard.2.2
        have hstepIW := (innerWitness sys (segSrc μ0 c.segs) ω).valid c.cur
          (Nat.find c.curT) (c.cur.endState c.curT) (Nat.find_spec c.curT)
          (AlterSeq.stateAt_find_eq_endState c.cur c.curT) l ν
          ((PMF.mem_support_iff _ _).mpr hnext)
        rw [hsend, hcend]; exact hstepIW
    · rw [dif_neg hT, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
  internal_only := by
    classical
    intro e l ν hsupp
    by_cases hT : e.trans.Terminates
    · rw [dif_pos hT] at hsupp
      by_cases h0 : dDenom S μ0 E ⟨e, hT⟩ = 0
      · rw [dif_pos h0, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
        exact absurd rfl hsupp
      · rw [dif_neg h0, PMF.mem_support_normalize_iff] at hsupp
        have hgne : dNum S μ0 E ⟨e, hT⟩ (some (l, ν)) ≠ 0 := hsupp
        rw [dNum] at hgne
        obtain ⟨c, hc⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hgne)
        have hmove : moveTerm S (segSrc μ0 c.segs) (segHist E c.segs) ⟨c.cur, c.curT⟩
            (some (l, ν)) ≠ 0 := right_ne_zero_of_mul hc
        simp only [moveTerm] at hmove
        obtain ⟨ω, hω⟩ := not_forall.mp (mt ENNReal.tsum_eq_zero.mpr hmove)
        have hnext : (innerWitness sys (segSrc μ0 c.segs) ω).next c.cur (some (l, ν)) ≠ 0 :=
          right_ne_zero_of_mul hω
        exact (innerWitness sys (segSrc μ0 c.segs) ω).internal_only c.cur l ν
          ((PMF.mem_support_iff _ _).mpr hnext)
    · rw [dif_neg hT, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp

/-- **Cancellation.** The denominator cancels the `PMF.normalize`, leaving the
numerator (verbatim `flattenSched_cancel`). -/
theorem dSched_cancel (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (e : AlterSeq State Label) (hT : e.trans.Terminates)
    (o : Option (Label × PMF State)) :
    dDenom S μ0 E ⟨e, hT⟩ * (dSched S μ0 E).next e o = dNum S μ0 E ⟨e, hT⟩ o := by
  classical
  have hnext : (dSched S μ0 E).next e
      = if h0 : dDenom S μ0 E ⟨e, hT⟩ = 0 then PMF.pure none
        else PMF.normalize (dNum S μ0 E ⟨e, hT⟩) (by rw [dNum_tsum]; exact h0)
          (by rw [dNum_tsum]; exact dDenom_ne_top S μ0 E ⟨e, hT⟩) := by
    change (dite e.trans.Terminates _ _) = _
    rw [dif_pos hT]
  by_cases h0 : dDenom S μ0 E ⟨e, hT⟩ = 0
  · rw [h0, zero_mul]
    have hall : dNum S μ0 E ⟨e, hT⟩ o = 0 :=
      (ENNReal.tsum_eq_zero.mp ((dNum_tsum S μ0 E ⟨e, hT⟩).trans h0) o)
    exact hall.symm
  · rw [hnext, dif_neg h0, PMF.normalize_apply, dNum_tsum]
    rw [← mul_assoc, mul_comm (dDenom S μ0 E ⟨e, hT⟩) (dNum S μ0 E ⟨e, hT⟩ o),
      mul_assoc, ENNReal.mul_inv_cancel h0 (dDenom_ne_top S μ0 E ⟨e, hT⟩), mul_one]

/-! ### Layer 4d (cont.): the halting-integral recursion and closing identities

The `g`-integrated one-macro-level unfolding of the composite `dSched`'s halting
end-state integral (V1), and the two closing identities (V2 a.s.-halting, V3
end-state pushforward) it drives, discharging `weakTau_flatten`. -/

/-- The `g`-integrated halting end-state integral of the composite `dSched`
rooted at macro-history `E` (source `μ0`). -/
noncomputable def dHM (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (g : State → ENNReal) : ENNReal :=
  ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
    (dSched S μ0 E).haltMass μ0 e * g (e.1.endState e.2)

/-- **V1 — the one-step integrate recursion (rooted).** Integrating `g` against
the composite's halting end-states unfolds one macro level: either the macro
scheduler halts now (mass `S.next E none`, end-state distributed as the current
source `μ0`), or it takes a macro-emission `ω` and successor `m'`, whereupon the
integral recurses at the advanced configuration `(m', macroExtend E m')`.

**AUDIT (STEP 1 — the suspected "double-source" defect; verdict: REFUTED, keep
current definitions).** The move-branch of `moveTerm` weights by the general-source
inner `probOf ⟨src, iw src ω⟩ cur`, whose init factor `src (cur.init)` duplicates
the outer source already carried by `segWeight`. This makes `dDenom ≠ probOf` at the
base: `probOf_{⟨μ0,dSched⟩}(⟨s0,nil⟩) = μ0 s0` (forced source mass, `probOf_nil`)
while `dDenom(⟨s0,nil⟩) = moveTot(μ0,E,⟨s0,nil⟩) = S.next E none + μ0 s0 · ∑'ω S.next
E(some τ ω)·iwMoveMass` (`peelBase` + `dConsistent_nil_iff`). The proposed fix
(reweight the move-branch to the Dirac-initialized inner `probOf ⟨pure cur.init, iw⟩`,
dropping `src (cur.init)`) does NOT restore a true posterior: it only touches the
`some`-branch, so the `none`-branch `S.next E none` (an `s0`-independent term, always
present) still forces `dDenom'(⟨s0,nil⟩) = S.next E none + ∑'ω S.next E(some τ ω)·
iwMoveMass = stallPart S μ0 E s0 1 ≠ μ0 s0`. The pointwise invariant `probOf = dDenom`
is UNACHIEVABLE by any move-branch reweighting — the structural reason is that the
composite `sys`-scheduler genuinely loses mass to hidden macro-STALLS (macro-steps
whose inner witness produces an empty run), and that lost mass is exactly `stallSum`;
a true posterior needs each hidden config's move-distribution to be a full PMF, but
here `moveTot ≤ 1` strictly. So the `mapWeakBeliefSched_probOf` template (`probOf =
denom`) does NOT transfer regardless of weighting. Crucially, the duplicated
`src (cur.init)` factor is NOT a correctness bug for THIS lemma: `dSched.next e o =
dNum(e,o)/dDenom(e)`, so any factor inside `dNum`'s branches is shared with `dDenom`
and cancels in the normalized kernel; the only source factor surviving into
`haltMass(dSched,μ0,e) = probOf·dSched.next e none` is the single one from `probOf`.
Hence: DO NOT redefine (a redefinition buys no pointwise identity and would force
re-proving the entire landed 4d stack + `d_halts`/`d_pushforward`). Prove V1 by the
GLOBAL-resummation route below.

**Proof plan (global resummation, current definitions).** Term A
`S.next E none · ∑'s μ0 s·g s` is the stall-then-halt mass, recovered only across all
execution lengths via the `stall_unfold` fixpoint + `tsum_iSup_of_monotone`
interchange; term B (the recursion into `dHM S m' (macroExtend E m')`) falls to a
`haltMass`-config peel analogous to `dW_peel`. Recommended sub-lemmas: (i) a
config-summed cancellation telescope for `∑'e haltMass·g` via `dSched_cancel` (NOT the
false pointwise `probOf = dDenom`); (ii) the no-segment stall component via `stallSum`
limits; (iii) the first-genuine-segment peel for term B; then assemble.

### PHASE-P VERDICT (paper proof audit of `d_integrate_step`)

**Status: identity TRUE and subtle; both candidate routes reduce to ONE unlanded
bridging lemma (`probOf_beliefMass`, stated below). No route closes on the current
landed stack alone. Frontier isolated; no Lean attempt beyond this, per method.**

Notation. `σ := dSched S μ0 E : WeakScheduler sys`; `pe := ⟨μ0, σ⟩`. By definition
`dHM S μ0 E g = ∑'e, haltMass(σ,μ0,e)·g(e.end)` with
`haltMass(σ,μ0,e) = probOf pe e · σ.next e none` (forward path-measure × halt), and
`σ.next e o = dNum(e,o)/dDenom(e)` (normalized), `dSched_cancel :
dDenom(e)·σ.next e o = dNum(e,o)`.

**(T) The identity is true but requires global resummation (not a base atom).**
For the atom `e = ⟨s0,nil⟩`, only the empty-segment config is `dConsistent`, so
`dNum(⟨s0,nil⟩,none) = moveTerm(none) = S.next E none` while (via `dW_peel`, no
segment peels a `nil` history) `dDenom(⟨s0,nil⟩) = moveTot(μ0,E,⟨s0,nil⟩) =
S.next E none + μ0 s0 · ∑'ω S.next E(τ,ω)·iwMoveMass(ω,s0)`. Hence
`haltMass(σ,μ0,⟨s0,nil⟩) = μ0 s0 · S.next E none / dDenom(⟨s0,nil⟩)`, STRICTLY below
the target term-A summand `S.next E none · μ0 s0`. The deficit is the normalizer
shrinkage; it is recovered ONLY by summing the longer stall-executions (composite
takes a macro-emission whose inner witness produces an empty run, then re-halts),
which is exactly the geometric object `stallPart`/`stall_unfold` resums via
`tsum_iSup_of_monotone`. So term A is a genuine `⨆ₙ` limit, not a single term.

**Both routes reduce to the SAME missing bridge.** Term B (recursion into
`dHM S m' (macroExtend E m')`) wants a numerator/config peel analogous to the proven
denominator peel `dW_peel`: configs whose FIRST completed segment is `seg` factor as
`headWeight(seg) · [fresh-root belief at (m'=seg.succ, macroExtend E m', dResidual e seg)]`.
`dW_peel`/`peelSeg` already establish this for the TOTAL denominator `dDenom = dW`.
The obstruction is UNIFORM across (≥)-sandwich, (≤)-sandwich, and renewal:

  `dHM` is built from `probOf pe e` — the FORWARD path-measure, a product over the
  execution's prefixes `∏ⱼ K(eⱼ, stepⱼ₊₁)` with `K(eⱼ,(l,s')) = ∑ν σ.next eⱼ(l,ν)·ν s'
  = ∑ν dNum(eⱼ,(l,ν))/dDenom(eⱼ)·ν s'`. Each prefix carries its OWN normalizer
  `1/dDenom(eⱼ)`. `dSched_cancel` cancels `dDenom(e)` against `σ.next e ·` only at a
  FIXED `e`; it does NOT telescope across consecutive prefixes, because `dDenom(eⱼ₊₁)`
  (configs of the longer history) is unrelated to any numerator factor produced at
  step `j`. The config-level lemmas (`dW_peel`, `stall_unfold`) describe the belief
  masses `segWeight·moveTerm` and their peel/fixpoint, but they live on the raw
  (un-normalized-across-steps) config side; `probOf` interleaves a per-prefix
  normalizer that no landed lemma reconciles. Consequently:
    - the (≤) product-telescope hypothesized in the docstring does NOT close (the
      per-prefix `1/dDenom(eⱼ)` factors have no cancelling partner);
    - the renewal/mixture route does NOT close either: the belief at an extended
      history `seg.run ++ e'` is a `headWeight`-weighted MIXTURE of fresh-root
      beliefs (ratio-of-sums), and a mixture-of-ratios does not compose into the
      product form `probOf` requires, so `dSched S μ0 E` is not a sub-scheduler /
      bind of the advanced `dSched S m' (macroExtend E m')` — exhibiting such a
      decomposition is equivalent to V1 (circular).

**The single missing lemma (the frontier).** A per-history forward/belief joint-mass
identity, provable by induction on `e.trans.length` via cons-end `probOf` +
`dSched_cancel` + `dW_peel`, but NOT among the landed lemmas:

  `probOf_beliefMass` :
    `probOf pe e · dDenom(e) = ∑'c, [dConsistent e c] · segWeight S μ0 E c.segs
        · probOf ⟨segSrc μ0 c.segs, (currentInnerWitness c)⟩ c.cur c.curT`
  (equivalently: `probOf pe e = beliefMass(e) / dDenom(e)`, the forward mass as the
  config-summed joint mass normalized once).

GIVEN `probOf_beliefMass`, the per-prefix normalizers reorganize into a SINGLE outer
normalizer, `haltMass·g` becomes a clean config sum, term B falls to a `dNum`-analogue
of `peelSeg` (fresh roots, `headWeight` factored), and term A falls to the
`stall_unfold` resummation — both then assemble by the landed 4d stack. Without it,
neither term is reachable. RECOMMENDATION for the next agent: prove `probOf_beliefMass`
first (standalone length-induction, ~1 substantial lemma), then V1 is a mechanical
assembly of `peelSeg`/`stall_unfold`/`tsum_iSup_of_monotone`. -/
theorem d_integrate_step (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (E : AlterSeq (PMF State) Label) (g : State → ENNReal) :
    dHM S μ0 E g = S.next E none * (∑' s, μ0 s * g s)
      + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * dHM S m' (macroExtend E m') g := by
  sorry

/-- `condDepth` one-step recursion in the `∑ω`-form matching `d_integrate_step`. -/
private theorem condDepth_succ' (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (k : ℕ) (E : AlterSeq (PMF State) Label) :
    condDepth S μ0 (k + 1) E
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * condDepth S μ0 k (macroExtend E m') := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  rw [condDepth_succ, tsumOpt (fun o => (S.next E) o * (match o with
      | none => (0 : ENNReal)
      | some (_, ω) => ∑' m', ω m' * condDepth S μ0 k (macroExtend E m')))]
  simp only [mul_zero, zero_add]
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]

/-- Iterating `d_integrate_step` at `g := 1`: the partial sum of conditional
depth totals lower-bounds the composite's total halting mass. -/
private theorem dHalt_ge (S : WeakScheduler (𝒟(sys^w))) (n : ℕ) :
    ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label),
      (∑ k ∈ Finset.range n, condDepth S μ0 k E) ≤ dHM S μ0 E (fun _ => 1) := by
  induction n with
  | zero => intro μ0 E; simp
  | succ n IH =>
    intro μ0 E
    rw [d_integrate_step S μ0 E (fun _ => 1)]
    rw [Finset.sum_range_succ', condDepth_zero]
    have hswap : (∑ k ∈ Finset.range n, condDepth S μ0 (k + 1) E)
        ≤ ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * dHM S m' (macroExtend E m') (fun _ => 1) := by
      rw [Finset.sum_congr rfl (fun k _ => condDepth_succ' S μ0 k E)]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine ENNReal.tsum_le_tsum (fun ω => ?_)
      rw [← Finset.mul_sum]
      refine mul_le_mul_left' ?_ _
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine ENNReal.tsum_le_tsum (fun m' => ?_)
      rw [← Finset.mul_sum]
      exact mul_le_mul_left' (IH m' (macroExtend E m')) _
    have hsrc : S.next E none = S.next E none * (∑' s, μ0 s * (1 : ENNReal)) := by
      rw [tsum_congr (fun s => mul_one _), PMF.tsum_coe, mul_one]
    rw [add_comm]
    exact add_le_add (le_of_eq hsrc) hswap

/-- **V2 — a.s.-halting.** Given `S` halts almost surely from `PMF.pure μ0`, the
composite `dSched` halts almost surely from `μ0`. -/
theorem d_halts (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (hhalt : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E) = 1) :
    (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
        (dSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e) = 1 := by
  have hle : (∑' e : {e : AlterSeq State Label // e.trans.Terminates},
      (dSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e) ≤ 1 :=
    WeakScheduler.haltMass_tsum_le_one _ _
  have hHM : dHM S μ0 ⟨μ0, Seq.nil⟩ (fun _ => 1)
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (dSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e := by
    unfold dHM; exact tsum_congr (fun e => mul_one _)
  refine le_antisymm hle ?_
  rw [← macroHalted_iSup_eq_one S μ0 hhalt]
  refine iSup_le (fun n => ?_)
  rw [show (∑ k ∈ Finset.range n, ∑' s, macroHaltDepth S μ0 k s)
      = ∑ k ∈ Finset.range n, condDepth S μ0 k ⟨μ0, Seq.nil⟩ from
    Finset.sum_congr rfl (fun k _ => by rw [macroHaltDepth_total, ← condDepth_root])]
  rw [← hHM]
  exact dHalt_ge S n μ0 ⟨μ0, Seq.nil⟩

/-- Appending a finite list to a terminating macro-history's transitions again
terminates. -/
private theorem append_ofList_term (E : AlterSeq (PMF State) Label)
    (hT : E.trans.Terminates) (K : List (Label × PMF State)) :
    (E.trans.append (Seq.ofList K)).Terminates :=
  ⟨Nat.find hT + Nat.find (Stream'.Seq.terminates_ofList K),
    Stream'.Seq.terminatedAt_append_find hT
      (Nat.find_spec (Stream'.Seq.terminates_ofList K))⟩

/-- The `g := [· = s]`-weighted conditional depth-`k` halt total from base
macro-history `E`: `condDepth` with the extra factor of the depth-`k`
continuation's macro end-state evaluated at `s`. -/
private noncomputable def condDepthG (S : WeakScheduler (𝒟(sys^w))) (k : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) : ENNReal :=
  ∑' K : {K : List (Label × PMF State) // K.length = k},
    (⟨PMF.pure E.init, S.toScheduler⟩ : ProbabilisticExecution (𝒟(sys^w))).pathWeight E K.1
      * S.next ⟨E.init, E.trans.append (Seq.ofList K.1)⟩ none
      * (⟨E.init, E.trans.append (Seq.ofList K.1)⟩ :
          AlterSeq (PMF State) Label).endState (append_ofList_term E hT K.1) s

/-- `condDepthG` at depth `0` is the stop probability at `E` times `E`'s own
macro end-state at `s`. -/
private theorem condDepthG_zero (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) :
    condDepthG S 0 E hT s = S.next E none * (E.endState hT) s := by
  unfold condDepthG
  rw [tsum_eq_single (⟨[], rfl⟩ : {K : List (Label × PMF State) // K.length = 0})
    (fun K hK => absurd (Subtype.ext (List.length_eq_zero_iff.mp K.2)) hK)]
  have hpw : (⟨PMF.pure E.init, S.toScheduler⟩ :
      ProbabilisticExecution (𝒟(sys^w))).pathWeight E [] = 1 := by
    unfold ProbabilisticExecution.pathWeight; rw [List.reverseRecOn_nil]
  rw [hpw, one_mul]
  have hE : (⟨E.init, E.trans.append (Seq.ofList ([] : List (Label × PMF State)))⟩
      : AlterSeq (PMF State) Label) = E := by
    rw [Stream'.Seq.ofList_nil, Stream'.Seq.append_nil]
  congr 1
  · rw [hE]
  · congr 1
    exact AlterSeq.endState_congr_pub hE (append_ofList_term E hT []) hT

/-- One-step recursion of `condDepthG` in the `∑ω`-form (front-peel of the
continuation list; the end-state factor rides along the `consLenEquiv` peel). -/
private theorem condDepthG_succ' (S : WeakScheduler (𝒟(sys^w))) (k : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) :
    condDepthG S (k + 1) E hT s
      = ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
          * ∑' m', ω m' * condDepthG S k (macroExtend E m') (macroExtend_term hT m') s := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have hker0 : ∀ (l : Label) (m' : PMF State), l ≠ Silent.τ →
      (⟨PMF.pure E.init, S.toScheduler⟩ :
        ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m') = 0 := by
    intro l m' hl
    unfold ProbabilisticExecution.kernel
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul]
  have hText : ∀ (l : Label) (m' : PMF State),
      (⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩ :
        AlterSeq (PMF State) Label).trans.Terminates :=
    fun l m' => ⟨Nat.find hT + 1, Stream'.Seq.terminatedAt_append_find hT
      (show (Seq.cons (l, m') Seq.nil : Seq (Label × PMF State)).TerminatedAt 1 from rfl)⟩
  have hpath : ∀ (l : Label) (m' : PMF State)
      (K' : {K : List (Label × PMF State) // K.length = k}),
      (⟨PMF.pure E.init, S.toScheduler⟩ :
          ProbabilisticExecution (𝒟(sys^w))).pathWeight E ((l, m') :: K'.1)
          * S.next ⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ none
          * (⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ :
              AlterSeq (PMF State) Label).endState (append_ofList_term E hT _) s
        = (⟨PMF.pure E.init, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).kernel E (l, m')
          * ((⟨PMF.pure E.init, S.toScheduler⟩ :
              ProbabilisticExecution (𝒟(sys^w))).pathWeight
                ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩ K'.1
            * S.next ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
                (Seq.ofList K'.1)⟩ none
            * (⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
                (Seq.ofList K'.1)⟩ : AlterSeq (PMF State) Label).endState
                (append_ofList_term ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩
                  (hText l m') K'.1) s) := by
    intro l m' K'
    have hHeq : E.trans.append (Seq.ofList ((l, m') :: K'.1))
        = (E.trans.append (Seq.cons (l, m') Seq.nil)).append (Seq.ofList K'.1) := by
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.append_assoc, Stream'.Seq.cons_append,
        Stream'.Seq.nil_append]
    have hAeq : (⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ :
          AlterSeq (PMF State) Label)
        = ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append (Seq.ofList K'.1)⟩ := by
      rw [hHeq]
    have hnext : S.next ⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ none
        = S.next ⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
            (Seq.ofList K'.1)⟩ none := by rw [hHeq]
    have hend : (⟨E.init, E.trans.append (Seq.ofList ((l, m') :: K'.1))⟩ :
            AlterSeq (PMF State) Label).endState (append_ofList_term E hT _)
        = (⟨E.init, (E.trans.append (Seq.cons (l, m') Seq.nil)).append
            (Seq.ofList K'.1)⟩ : AlterSeq (PMF State) Label).endState
            (append_ofList_term ⟨E.init, E.trans.append (Seq.cons (l, m') Seq.nil)⟩
              (hText l m') K'.1) :=
      AlterSeq.endState_congr_pub hAeq _ _
    rw [ProbabilisticExecution.pathWeight_cons, hnext, hend]
    ring
  unfold condDepthG
  rw [← Equiv.tsum_eq (consLenEquiv (γ := Label × PMF State) k),
    ENNReal.tsum_prod', ENNReal.tsum_prod']
  simp only [consLenEquiv, Equiv.coe_fn_mk]
  rw [tsum_congr (fun l => tsum_congr (fun m' => tsum_congr (fun K' => hpath l m' K'))),
    tsum_congr (fun l => tsum_congr (fun _ => ENNReal.tsum_mul_left)),
    tsum_eq_single Silent.τ (fun l hl => by
      rw [ENNReal.tsum_eq_zero]; intro m'; rw [hker0 l m' hl, zero_mul])]
  simp only [ProbabilisticExecution.kernel]
  rw [tsum_congr (fun _ => ENNReal.tsum_mul_right.symm), ENNReal.tsum_comm]
  apply tsum_congr; intro ω
  rw [tsum_congr (fun m' => mul_assoc _ _ _), ENNReal.tsum_mul_left]
  rfl

/-- At the root, `condDepthG` is the global depth-`k` end-state pushforward
`macroHaltDepth`. -/
private theorem condDepthG_root (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (k : ℕ) (s : State) :
    condDepthG S k ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil s = macroHaltDepth S μ0 k s := by
  have hsummand : ∀ (i : PMF State) (K : {K : List (Label × PMF State) // K.length = k}),
      S.haltMass (PMF.pure μ0) (rootEquiv k (i, K)).1
          * ((rootEquiv k (i, K)).1.1.endState (rootEquiv k (i, K)).1.2) s
        = PMF.pure μ0 i * ((⟨PMF.pure μ0, S.toScheduler⟩ :
            ProbabilisticExecution (𝒟(sys^w))).pathWeight ⟨i, Seq.nil⟩ K.1
              * S.next ⟨i, Seq.ofList K.1⟩ none
              * ((⟨i, Seq.ofList K.1⟩ : AlterSeq (PMF State) Label).endState
                  (Stream'.Seq.terminates_ofList K.1)) s) := by
    intro i K
    show S.haltMass (PMF.pure μ0)
        ⟨⟨i, Seq.ofList K.1⟩, Stream'.Seq.terminates_ofList K.1⟩
        * ((⟨i, Seq.ofList K.1⟩ : AlterSeq (PMF State) Label).endState
            (Stream'.Seq.terminates_ofList K.1)) s = _
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [ProbabilisticExecution.probOf_eq_pathWeight,
      ProbabilisticExecution.init_eq_initState]
    ring
  unfold macroHaltDepth
  rw [← Equiv.tsum_eq (rootEquiv k), ENNReal.tsum_prod',
    tsum_congr (fun i => tsum_congr (fun K => hsummand i K)),
    tsum_congr (fun i => ENNReal.tsum_mul_left),
    tsum_eq_single μ0 (fun i hi => by rw [PMF.pure_apply, if_neg hi, zero_mul]),
    PMF.pure_apply_self, one_mul]
  unfold condDepthG
  refine tsum_congr (fun K => ?_)
  have hnil : (Seq.nil.append (Seq.ofList K.1) : Seq (Label × PMF State)) = Seq.ofList K.1 :=
    Stream'.Seq.nil_append _
  have hAeq : (⟨μ0, Seq.nil.append (Seq.ofList K.1)⟩ : AlterSeq (PMF State) Label)
      = ⟨μ0, Seq.ofList K.1⟩ := by rw [hnil]
  rw [show S.next ⟨μ0, Seq.nil.append (Seq.ofList K.1)⟩ none
        = S.next ⟨μ0, Seq.ofList K.1⟩ none from by rw [hnil],
    AlterSeq.endState_congr_pub hAeq
      (append_ofList_term ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil K.1)
      (Stream'.Seq.terminates_ofList K.1)]

open Classical in
/-- Iterating `d_integrate_step` at `g := [· = s]`: the partial sum of the
depth-`k` end-state pushforwards lower-bounds the composite's `s`-integral,
along the invariant that the source is the current macro end-state. -/
private theorem dHalt_ge_G (S : WeakScheduler (𝒟(sys^w))) (s : State) (n : ℕ) :
    ∀ (μ0 : PMF State) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates),
      μ0 = E.endState hT →
      (∑ k ∈ Finset.range n, condDepthG S k E hT s)
        ≤ dHM S μ0 E (fun x => if x = s then 1 else 0) := by
  induction n with
  | zero => intro μ0 E hT hinv; simp
  | succ n IH =>
    intro μ0 E hT hinv
    rw [d_integrate_step S μ0 E (fun x => if x = s then 1 else 0),
      Finset.sum_range_succ', condDepthG_zero]
    have hswap : (∑ k ∈ Finset.range n, condDepthG S (k + 1) E hT s)
        ≤ ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * dHM S m' (macroExtend E m') (fun x => if x = s then 1 else 0) := by
      rw [Finset.sum_congr rfl (fun k _ => condDepthG_succ' S k E hT s),
        ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine ENNReal.tsum_le_tsum (fun ω => ?_)
      rw [← Finset.mul_sum]
      refine mul_le_mul_left' ?_ _
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine ENNReal.tsum_le_tsum (fun m' => ?_)
      rw [← Finset.mul_sum]
      exact mul_le_mul_left'
        (IH m' (macroExtend E m') (macroExtend_term hT m')
          (macroExtend_endState hT m').symm) _
    have hhalt : S.next E none * ((E.endState hT) s)
        = S.next E none * (∑' s', μ0 s' * (if s' = s then (1 : ENNReal) else 0)) := by
      rw [tsum_eq_single s (fun s' hs' => by rw [if_neg hs', mul_zero]), if_pos rfl, mul_one,
        ← hinv]
    rw [add_comm]
    exact add_le_add (le_of_eq hhalt) hswap

open Classical in
/-- **V3 — pushforward.** The composite `dSched`'s halting end-state pushforward
is the macro mixture `Ν.bind id`. -/
theorem d_pushforward (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State)
    (Ν : PMF (PMF State))
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (s : State) :
    (Ν.bind id) s
      = ∑' e : {e : AlterSeq State Label // e.trans.Terminates},
          (dSched S μ0 ⟨μ0, Seq.nil⟩).haltMass μ0 e
            * (if e.1.endState e.2 = s then 1 else 0) := by
  -- a.s.-halting is implied by the pushforward (sum `hpush` over `m`).
  have hhalt : (∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
      S.haltMass (PMF.pure μ0) E) = 1 := by
    have h := (PMF.tsum_coe Ν).symm
    rw [tsum_congr (fun m => hpush m), ENNReal.tsum_comm,
      tsum_congr (fun E => by
        rw [ENNReal.tsum_mul_left,
          tsum_eq_single (E.1.endState E.2)
            (fun m hm => if_neg (fun heq => hm heq.symm)), if_pos rfl, mul_one])] at h
    exact h.symm
  -- the composite's `s`-integral, as a function of `s`.
  set F : State → ENNReal :=
    fun s' => dHM S μ0 ⟨μ0, Seq.nil⟩ (fun x => if x = s' then 1 else 0) with hF
  have htotF : (∑' s', F s') = 1 := by
    simp only [hF, dHM]
    rw [ENNReal.tsum_comm,
      tsum_congr (fun e => by
        rw [ENNReal.tsum_mul_left,
          tsum_eq_single (e.1.endState e.2)
            (fun s' hs' => if_neg (fun heq => hs' heq.symm)), if_pos rfl, mul_one])]
    exact d_halts S μ0 hhalt
  have hle : ∀ s0, (Ν.bind id) s0 ≤ F s0 := by
    intro s0
    rw [macroHalt_tsum_depth S μ0 hpush s0, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le (fun n => ?_)
    rw [show (∑ k ∈ Finset.range n, macroHaltDepth S μ0 k s0)
        = ∑ k ∈ Finset.range n, condDepthG S k ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil s0 from
      Finset.sum_congr rfl (fun k _ => (condDepthG_root S μ0 k s0).symm)]
    exact dHalt_ge_G S s0 n μ0 ⟨μ0, Seq.nil⟩ Stream'.Seq.terminates_nil
      (AlterSeq.endState_of_trans_nil ⟨μ0, Seq.nil⟩ rfl Stream'.Seq.terminates_nil).symm
  have hge : F s ≤ (Ν.bind id) s := by
    have hFsplit : (∑' s', F s') = F s + ∑' s', if s' = s then 0 else F s' :=
      ENNReal.tsum_eq_add_tsum_ite s
    have hNsplit : (∑' s', (Ν.bind id) s') = (Ν.bind id) s
        + ∑' s', if s' = s then 0 else (Ν.bind id) s' :=
      ENNReal.tsum_eq_add_tsum_ite s
    have hRle : (∑' s', if s' = s then 0 else (Ν.bind id) s')
        ≤ ∑' s', if s' = s then 0 else F s' :=
      ENNReal.tsum_le_tsum (fun s' => by split_ifs; exacts [le_refl 0, hle s'])
    have hRfin : (∑' s', if s' = s then 0 else F s') ≠ ⊤ := by
      have hb : (∑' s', if s' = s then 0 else F s') ≤ ∑' s', F s' :=
        ENNReal.tsum_le_tsum (fun s' => by split_ifs; exacts [zero_le', le_refl _])
      rw [htotF] at hb
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hb
    have hle2 : F s + (∑' s', if s' = s then 0 else F s')
        ≤ (Ν.bind id) s + (∑' s', if s' = s then 0 else F s') := by
      calc F s + (∑' s', if s' = s then 0 else F s')
          = ∑' s', F s' := hFsplit.symm
        _ = 1 := htotF
        _ = ∑' s', (Ν.bind id) s' := (PMF.tsum_coe _).symm
        _ = (Ν.bind id) s + ∑' s', if s' = s then 0 else (Ν.bind id) s' := hNsplit
        _ ≤ (Ν.bind id) s + ∑' s', if s' = s then 0 else F s' :=
            add_le_add le_rfl hRle
    exact (ENNReal.add_le_add_iff_right hRfin).mp hle2
  show (Ν.bind id) s = F s
  exact le_antisymm (hle s) hge

/-- **Flattening.** An internal weak transition of `𝒟(sys^w)` out of the Dirac
macro-state `PMF.pure μ` collapses to an internal weak transition of `sys` from
`μ` to the end-state mixture. Witnessed by the decision-point belief scheduler
`dSched` instantiated at the macro witness of `h`. -/
theorem weakTau_flatten (sys : System State Label) {μ : PMF State}
    {Ν : PMF (PMF State)} (h : weakTau (𝒟(sys^w)) (PMF.pure μ) Ν) :
    weakTau sys μ (Ν.bind id) := by
  classical
  refine ⟨dSched h.witnessScheduler μ ⟨μ, Seq.nil⟩, ?_, ?_⟩
  · exact d_halts h.witnessScheduler μ h.witness_halts
  · exact fun s => d_pushforward h.witnessScheduler μ Ν
      (fun m => h.witness_pushforward m) s

end PLTS
