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

open Classical in
/-- **Pushforward as a monotone limit.** The flatten target `Ν.bind id`, evaluated
pointwise at `s`, is the supremum over the truncation depth `n` of the halting mass
accumulated in the first `n` macro-depths — the pointwise companion of
`macroHalted_iSup_eq_one` (which is the `∑' s`-summed, mass-`1` form). Together they
say the flatten pushforward is exactly the monotone limit of the depth-stratified
halting sub-distributions: the object any limit witness `σ*` must realize. Immediate
from `macroHalt_tsum_depth` (the depth stratification of `Ν.bind id`) and the
`ENNReal` `tsum`-as-`iSup`-of-partial-sums identity. -/
theorem macroHalt_bind_id_eq_iSup {sys : System State Label}
    (S : WeakScheduler (𝒟(sys^w))) (μ0 : PMF State) {Ν : PMF (PMF State)}
    (hpush : ∀ m, Ν m = ∑' E : {e : AlterSeq (PMF State) Label // e.trans.Terminates},
        S.haltMass (PMF.pure μ0) E * (if E.1.endState E.2 = m then 1 else 0))
    (s : State) :
    (Ν.bind id) s = ⨆ n : ℕ, ∑ k ∈ Finset.range n, macroHaltDepth S μ0 k s := by
  rw [macroHalt_tsum_depth S μ0 hpush s]
  exact ENNReal.tsum_eq_iSup_nat

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

/-- Integrating a test `g` against a `PMF.bind` splits as the source-weighted sum
of the branch integrals (the `∑'`-form of `∫ g d(p.bind f) = ∑ₐ p a · ∫ g d(f a)`). -/
private theorem tsum_bind_mul {γ : Type} (p : PMF γ) (f : γ → PMF State)
    (g : State → ENNReal) :
    (∑' s, (p.bind f) s * g s) = ∑' a, p a * ∑' s, f a s * g s := by
  have h1 : (∑' s, (p.bind f) s * g s) = ∑' s, ∑' a, p a * f a s * g s :=
    tsum_congr fun s => by rw [PMF.bind_apply, ENNReal.tsum_mul_right]
  rw [h1, ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun s => by ring

/-- **One-layer distribution integrate identity.** Integrating `g` against the
depth-`(n+1)` truncated macro-future distribution unfolds one macro level: halt
now (mass `S.next E none`, integral against the current source `E.endState hT`), or
take a macro-emission `ω` and successor `m'` and recurse at depth `n` from
`macroExtend E m'`. This is the distribution-side (`macroFuture_trunc`) analogue of
the scheduler-side target `d_integrate_step`; it is the pushforward that route-(b)'s
`oneDecision := (weakTau_macroFuture_trunc S 1 E hT).witnessScheduler` delivers. -/
theorem macroFuture_trunc_integrate_succ (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' s, macroFuture_trunc S (n + 1) E hT s * g s)
      = S.next E none * (∑' s, (E.endState hT) s * g s)
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s, macroFuture_trunc S n (macroExtend E m')
                (macroExtend_term hT m') s * g s) := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have hunfold : macroFuture_trunc S (n + 1) E hT
      = (S.next E).bind (fun o => match o with
          | none => E.endState hT
          | some (_, ω) => ω.bind (fun m' =>
              macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m'))) := rfl
  rw [hunfold, tsum_bind_mul]
  rw [tsumOpt]
  congr 1
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
  refine tsum_congr fun ω => ?_
  rw [tsum_bind_mul]

/-- **`oneDecision` (route (b)).** The single-layer witness scheduler for the
depth-1 truncated macro-future, extracted non-constructively from the landed
`weakTau_macroFuture_trunc S 1 E hT`. No bespoke mixture construction is needed:
`weakTau`'s own `witnessScheduler` / `witness_halts` / `integrate` /
`witness_pushforward` supply every identity the one layer requires. -/
noncomputable def oneDecision (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys :=
  (weakTau_macroFuture_trunc S 1 E hT).witnessScheduler

/-- `oneDecision` halts almost surely from the current source `E.endState hT`. -/
theorem oneDecision_halts (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    (∑' e, (oneDecision S E hT).haltMass (E.endState hT) e) = 1 :=
  (weakTau_macroFuture_trunc S 1 E hT).witness_halts

/-- **One-layer integrate identity for `oneDecision`.** Exactly `d_integrate_step`'s
shape, truncated at depth `0`: halt now (integral against the source `E.endState hT`),
or take a macro-emission `ω` and successor `m'`, whereupon the successor integral is
against the sampled `m'` itself (the depth-0 macro-future). The genuine work left for
the full recursion is to replace this `∑' s, m' s * g s` by `dHM S m' (macroExtend E m')`
via the depth tower / limit closure. -/
theorem oneDecision_integrate (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (oneDecision S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = S.next E none * (∑' s, (E.endState hT) s * g s)
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s, (macroExtend E m').endState (macroExtend_term hT m')
                s * g s) := by
  rw [oneDecision, (weakTau_macroFuture_trunc S 1 E hT).integrate g]
  exact macroFuture_trunc_integrate_succ S 0 E hT g

/-! ### The numerator-exposed single-layer scheduler `oneDecisionC`

A concrete-`next` rebuild of `oneDecision` as a **mixture-of-common-source belief
scheduler**. The single hidden index is the macro-emission `x : Option (Label ×
PMF (PMF State))` sampled from `S.next E`; each branch runs a genuine `sys`-weak
scheduler `odFam x` from the common source `E.endState hT` (the immediately-stopping
scheduler at `none`, the per-emission inner witness `innerWitness sys src ω` at
`some (_, ω)`). The belief `next e o` is the normalized numerator `odNum e o /
odDenom e`; `odDenom` is the composite path measure and is `≤ 1` (single layer, so
the total emission weight `∑' x, S.next E x = 1` — no stall leak). -/

/-- The branch scheduler family for `oneDecisionC`. -/
noncomputable def odFam (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    Option (Label × PMF (PMF State)) → WeakScheduler sys
  | none => WeakScheduler.stop sys
  | some (_, ω) => innerWitness sys (E.endState hT) ω

open Classical in
/-- The per-branch path measure at an observed inner history `e` (0 off-termination). -/
noncomputable def odBranchProb (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (x : Option (Label × PMF (PMF State))) (e : AlterSeq State Label) : ENNReal :=
  if h : e.trans.Terminates then
    (⟨E.endState hT, (odFam S E hT x).toScheduler⟩ : ProbabilisticExecution sys).probOf e h
  else 0

/-- The exposed **numerator** of `oneDecisionC.next e` at emission `o`. -/
noncomputable def odNum (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) (o : Option (Label × PMF State)) : ENNReal :=
  ∑' x, S.next E x * odBranchProb S E hT x e * (odFam S E hT x).next e o

/-- The exposed **denominator** (composite path measure) of `oneDecisionC` at `e`. -/
noncomputable def odDenom (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) : ENNReal :=
  ∑' x, S.next E x * odBranchProb S E hT x e

/-- Each branch path measure is a sub-probability. -/
theorem odBranchProb_le_one (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (x : Option (Label × PMF (PMF State))) (e : AlterSeq State Label) :
    odBranchProb S E hT x e ≤ 1 := by
  classical
  unfold odBranchProb
  split
  · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
  · exact zero_le_one

/-- The numerators over `o` sum to the denominator (each branch's `next e` is a PMF). -/
theorem odNum_tsum (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    (∑' o, odNum S E hT e o) = odDenom S E hT e := by
  unfold odNum odDenom
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- The denominator is a sub-probability (`∑' x, S.next E x = 1`, `odBranchProb ≤ 1`). -/
theorem odDenom_le_one (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    odDenom S E hT e ≤ 1 := by
  unfold odDenom
  calc (∑' x, S.next E x * odBranchProb S E hT x e)
      ≤ ∑' x, S.next E x :=
        ENNReal.tsum_le_tsum (fun x => mul_le_of_le_one_right' (odBranchProb_le_one S E hT x e))
    _ = 1 := (S.next E).tsum_coe

/-- The denominator is never `⊤` (the trivial single-layer bound; feeds later `⨆`). -/
theorem odDenom_ne_top (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    odDenom S E hT e ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (odDenom_le_one S E hT e)

open Classical in
/-- **`oneDecisionC` (numerator-exposed route (b)).** The single-macro-layer belief
scheduler with EXPLICIT `next`: the normalized mixture posterior `odNum e o / odDenom e`
over the hidden emission `x`. `valid`/`internal_only` reduce to the branch schedulers'
(each `odFam x` is a genuine `sys`-weak scheduler). -/
noncomputable def oneDecisionC (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys where
  next e := if h : odDenom S E hT e = 0 then PMF.pure none
    else PMF.normalize (odNum S E hT e) (by rw [odNum_tsum]; exact h)
      (by rw [odNum_tsum]; exact odDenom_ne_top S E hT e)
  valid := by
    classical
    intro e n s hterm hstate l ν hsupp
    by_cases hd : odDenom S E hT e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : odNum S E hT e (some (l, ν)) ≠ 0 := hsupp
      rw [odNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (odFam S E hT x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (odFam S E hT x).valid e n s hterm hstate l ν ((PMF.mem_support_iff _ _).mpr hnextne)
  internal_only := by
    classical
    intro e l ν hsupp
    by_cases hd : odDenom S E hT e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : odNum S E hT e (some (l, ν)) ≠ 0 := hsupp
      rw [odNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (odFam S E hT x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (odFam S E hT x).internal_only e l ν ((PMF.mem_support_iff _ _).mpr hnextne)

/-- **Cancellation:** `odDenom · oneDecisionC.next = odNum` (the belief-scheduler
normalization identity; the `mapWeakBeliefSched_cancel` analogue). -/
theorem oneDecisionC_cancel (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) (o : Option (Label × PMF State)) :
    odDenom S E hT e * (oneDecisionC S E hT).next e o = odNum S E hT e o := by
  classical
  by_cases hd : odDenom S E hT e = 0
  · have hnext : (oneDecisionC S E hT).next e = PMF.pure none := dif_pos hd
    rw [hnext, hd, zero_mul]
    have hall : ∀ o', odNum S E hT e o' = 0 := by
      rw [← ENNReal.tsum_eq_zero, odNum_tsum]; exact hd
    exact (hall o).symm
  · have hnext : (oneDecisionC S E hT).next e o
        = odNum S E hT e o * (odDenom S E hT e)⁻¹ := by
      have h1 : (oneDecisionC S E hT).next e
          = PMF.normalize (odNum S E hT e) (by rw [odNum_tsum]; exact hd)
            (by rw [odNum_tsum]; exact odDenom_ne_top S E hT e) := dif_neg hd
      rw [h1, PMF.normalize_apply, odNum_tsum]
    rw [hnext, ← mul_assoc, mul_comm (odDenom S E hT e) (odNum S E hT e o), mul_assoc,
      ENNReal.mul_inv_cancel hd (odDenom_ne_top S E hT e), mul_one]

/-- **Belief consistency (pointwise).** The `oneDecisionC`-path measure of a
terminating inner history `e`, from the common source `E.endState hT`, is exactly the
denominator `odDenom e`. Because the single layer carries total emission weight
`∑' x, S.next E x = 1`, the `nil` base collapses to the source with NO stall term — the
pointwise form that failed for the recursive belief scheduler `dSched`. Induction on
`e` (`List.reverseRecOn`), the append case telescoping each branch's own `probOf`. -/
theorem oneDecisionC_probOf (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    (⟨E.endState hT, (oneDecisionC S E hT).toScheduler⟩ : ProbabilisticExecution sys).probOf e hFin
      = odDenom S E hT e := by
  classical
  set pe : ProbabilisticExecution sys :=
    ⟨E.endState hT, (oneDecisionC S E hT).toScheduler⟩ with hpe
  change pe.probOf e hFin = odDenom S E hT e
  suffices hgen : ∀ (L : List (Label × State)) (s₀ : State)
      (hFin : (Seq.ofList L : Seq (Label × State)).Terminates),
      pe.probOf ⟨s₀, Seq.ofList L⟩ hFin = odDenom S E hT ⟨s₀, Seq.ofList L⟩ by
    have hofl : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)) = e.trans :=
      Stream'.Seq.ofList_toList e.trans hFin
    have hFin' : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)).Terminates := by
      rw [hofl]; exact hFin
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [hofl]
    have hkey := hgen (e.trans.toList hFin) e.init hFin'
    rw [pe.probOf_congr ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e hEeq hFin' hFin] at hkey
    rw [hkey, hEeq]
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro s₀ hFin
    rw [pe.probOf_congr ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil, Stream'.Seq.ofList_nil]
    have hbp : ∀ x, odBranchProb S E hT x ⟨s₀, Seq.nil⟩ = (E.endState hT) s₀ := by
      intro x
      unfold odBranchProb
      rw [dif_pos Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil,
        ProbabilisticExecution.init_eq_initState]
    change (E.endState hT) s₀ = odDenom S E hT ⟨s₀, Seq.nil⟩
    unfold odDenom
    rw [tsum_congr (fun x => by rw [hbp x]), ENNReal.tsum_mul_right, (S.next E).tsum_coe, one_mul]
  | append_singleton rest last ih =>
    intro s₀ hFin
    obtain ⟨l, s'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, s')]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    set E' : AlterSeq State Label := ⟨s₀, Seq.ofList rest⟩ with hE'
    -- per-branch: probOf(E') * (branch kernel at (l,s')) = probOf(full)
    have hbpstep : ∀ x, odBranchProb S E hT x E'
        * (∑' ν, (odFam S E hT x).next E' (some (l, ν)) * ν s')
        = odBranchProb S E hT x ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ := by
      intro x
      unfold odBranchProb
      rw [dif_pos hrest_fin, dif_pos hFin,
        (⟨E.endState hT, (odFam S E hT x).toScheduler⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin (l, s')
          hFinS, ProbabilisticExecution.kernel]
    set Mid : ENNReal := ∑' x, S.next E x * odBranchProb S E hT x E'
      * (∑' ν, (odFam S E hT x).next E' (some (l, ν)) * ν s') with hMid
    have hLHS : pe.probOf ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ hFin = Mid := by
      rw [pe.probOf_congr ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe.probOf_append_singleton s₀ (Seq.ofList rest) hrest_fin (l, s') hFinS,
        show pe.probOf E' hrest_fin = odDenom S E hT E' from ih s₀ hrest_fin,
        ProbabilisticExecution.kernel]
      change odDenom S E hT E' * (∑' ν, (oneDecisionC S E hT).next E' (some (l, ν)) * ν s') = Mid
      have hstep2 : ∀ ν, odNum S E hT E' (some (l, ν)) * ν s'
          = ∑' x, S.next E x * odBranchProb S E hT x E'
              * (odFam S E hT x).next E' (some (l, ν)) * ν s' := by
        intro ν; unfold odNum; rw [ENNReal.tsum_mul_right]
      rw [← ENNReal.tsum_mul_left,
        tsum_congr (fun ν => by rw [← mul_assoc, oneDecisionC_cancel S E hT E' (some (l, ν))]),
        tsum_congr hstep2, ENNReal.tsum_comm, hMid]
      refine tsum_congr (fun x => ?_)
      rw [tsum_congr (fun ν => mul_assoc (S.next E x * odBranchProb S E hT x E') _ _),
        ENNReal.tsum_mul_left]
    have hRHS : odDenom S E hT ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ = Mid := by
      unfold odDenom
      rw [hMid]
      refine tsum_congr (fun x => ?_)
      rw [← hbpstep x, ← mul_assoc]
    rw [hLHS, hRHS]

/-- Reindex a terminating-history sum supported on the `nil` fibre onto states
(local copy of `weakTau_reindex_fiber`). -/
private theorem reindexFiber {St Lb : Type}
    (fiber : St → AlterSeq St Lb) (hterm : ∀ s, (fiber s).trans.Terminates)
    (hinj : Function.Injective fiber)
    (F : {e : AlterSeq St Lb // e.trans.Terminates} → ENNReal)
    (hsupp : ∀ e : {e : AlterSeq St Lb // e.trans.Terminates},
        F e ≠ 0 → ∃ s, fiber s = e.1) :
    (∑' e, F e) = ∑' s, F ⟨fiber s, hterm s⟩ := by
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x => (⟨fiber (x : St), hterm x⟩ : {e : AlterSeq St Lb // e.trans.Terminates}))
    ?_ ?_ ?_
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext (hinj hab)
  · intro e he
    obtain ⟨s, hs⟩ := hsupp e (Function.mem_support.mp he)
    have hes : (⟨fiber s, hterm s⟩ : {e : AlterSeq St Lb // e.trans.Terminates}) = e :=
      Subtype.ext hs
    exact ⟨⟨s, by change F ⟨fiber s, hterm s⟩ ≠ 0; rw [hes]; exact Function.mem_support.mp he⟩,
      Subtype.ext hs⟩
  · intro x; rfl

/-- **`stop`-scheduler integrate.** The immediately-stopping scheduler halts on the
`nil` histories, so its `g`-integrated halting end-state is the `g`-integral of the
source (the `none`-branch of `oneDecisionC`). -/
theorem stop_integrate {sys : System State Label} (μ : PMF State) (g : State → ENNReal) :
    (∑' e, (WeakScheduler.stop sys).haltMass μ e * g (e.1.endState e.2)) = ∑' s, μ s * g s := by
  classical
  set pe : ProbabilisticExecution sys := ⟨μ, (WeakScheduler.stop sys).toScheduler⟩ with hpe
  have hker : ∀ (e' : AlterSeq State Label) (st : Label × State), pe.kernel e' st = 0 := by
    intro e' st
    unfold ProbabilisticExecution.kernel
    have h0 : ∀ ν : PMF State, pe.scheduler.next e' (some (st.1, ν)) = 0 :=
      fun ν => PMF.pure_apply_of_ne _ _ (by simp)
    simp only [h0, zero_mul, tsum_zero]
  have hprob_nonnil : ∀ (e' : AlterSeq State Label) (h : e'.trans.Terminates),
      e'.trans ≠ Seq.nil → pe.probOf e' h = 0 := by
    rintro ⟨init', trans'⟩ h hne
    simp only at h hne ⊢
    have hnonempty : trans'.toList h ≠ [] := by
      intro hnil; apply hne
      have := Stream'.Seq.ofList_toList trans' h
      rw [hnil, Stream'.Seq.ofList_nil] at this; exact this.symm
    obtain ⟨previous, last, h_prev, h_split, _, _⟩ :=
      Stream'.Seq.exists_split_last trans' h hnonempty
    subst h_split
    rw [ProbabilisticExecution.probOf_append_singleton _ _ _ h_prev _ h, hker, mul_zero]
  have hhalt_fiber : ∀ s : State,
      (WeakScheduler.stop sys).haltMass μ ⟨⟨s, Seq.nil⟩, Stream'.Seq.terminates_nil⟩ = μ s := by
    intro s
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [← hpe, ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState,
      show (WeakScheduler.stop sys).toScheduler.next ⟨s, Seq.nil⟩ none = 1 from
        PMF.pure_apply_self none, mul_one]
  rw [reindexFiber (fun s => (⟨s, Seq.nil⟩ : AlterSeq State Label))
      (fun _ => Stream'.Seq.terminates_nil) (fun a b hab => congrArg AlterSeq.init hab)
      (fun e => (WeakScheduler.stop sys).haltMass μ e * g (e.1.endState e.2)) ?supp]
  · refine tsum_congr (fun s => ?_)
    rw [hhalt_fiber s, AlterSeq.endState_of_trans_nil _ rfl]
  case supp =>
    intro e hne
    refine ⟨e.1.init, ?_⟩
    by_contra hcontra
    apply hne
    have htrans : e.1.trans ≠ Seq.nil := by
      intro hnil; apply hcontra
      cases e with | mk e' he' => cases e' with | mk i t => simp only at hnil ⊢; rw [hnil]
    have hz : (WeakScheduler.stop sys).haltMass μ e = 0 := by
      unfold WeakScheduler.haltMass Scheduler.haltMass
      rw [← hpe, hprob_nonnil e.1 e.2 htrans, zero_mul]
    rw [hz, zero_mul]

/-- **`oneDecisionC` halting mass as a branch mixture.** The composite halting mass
factors through the hidden emission `x`: `haltMass = ∑' x, S.next E x · (branch halt
mass)`. Immediate from `oneDecisionC_probOf` (path measure `= odDenom`) and
`oneDecisionC_cancel` (`odDenom · next = odNum`). -/
theorem oneDecisionC_haltMass (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (oneDecisionC S E hT).haltMass (E.endState hT) e
      = ∑' x, S.next E x * (odFam S E hT x).haltMass (E.endState hT) e := by
  classical
  have hhalt : (oneDecisionC S E hT).haltMass (E.endState hT) e = odNum S E hT e.1 none := by
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [show (⟨E.endState hT, (oneDecisionC S E hT).toScheduler⟩
          : ProbabilisticExecution sys).probOf e.1 e.2 = odDenom S E hT e.1 from
        oneDecisionC_probOf S E hT e.1 e.2]
    exact oneDecisionC_cancel S E hT e.1 none
  rw [hhalt]
  unfold odNum
  refine tsum_congr (fun x => ?_)
  rw [mul_assoc]
  congr 1
  unfold WeakScheduler.haltMass Scheduler.haltMass odBranchProb
  rw [dif_pos e.2]

/-- **One-layer integrate identity for `oneDecisionC`.** The `g`-integrated halting
end-state of the concrete single-layer scheduler unfolds exactly one macro level —
the SAME right-hand side as the opaque `oneDecision_integrate`, so the tower/limit
tranches see identical shapes. The `none` branch integrates against the source
(`stop_integrate`); each `some (τ, ω)` branch against `ω.bind id` (`innerWitness_integrate`
then `tsum_bind_mul`), matching the depth-0 macro-future `(macroExtend E m').endState = m'`. -/
theorem oneDecisionC_integrate (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = S.next E none * (∑' s, (E.endState hT) s * g s)
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω))
            * ∑' m', ω m' * (∑' s, (macroExtend E m').endState (macroExtend_term hT m')
                s * g s) := by
  classical
  have hA : (∑' e, (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' x, S.next E x
          * (∑' e, (odFam S E hT x).haltMass (E.endState hT) e * g (e.1.endState e.2)) := by
    have he : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
        (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2)
          = ∑' x, S.next E x * (odFam S E hT x).haltMass (E.endState hT) e
              * g (e.1.endState e.2) := by
      intro e
      rw [oneDecisionC_haltMass S E hT e, ENNReal.tsum_mul_right]
    rw [tsum_congr he, ENNReal.tsum_comm]
    refine tsum_congr (fun x => ?_)
    rw [tsum_congr (fun e => mul_assoc (S.next E x) _ _), ENNReal.tsum_mul_left]
  rw [hA, tsumOpt (fun x => S.next E x
    * (∑' e, (odFam S E hT x).haltMass (E.endState hT) e * g (e.1.endState e.2)))]
  congr 1
  · congr 1
    exact stop_integrate (E.endState hT) g
  · have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
        S.next E (some (l, ω)) = 0 := fun l ω hl => by
      by_contra hne
      exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
    rw [ENNReal.tsum_prod',
      tsum_eq_single Silent.τ (fun l hl => by
        rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
    refine tsum_congr (fun ω => ?_)
    by_cases hw : S.next E (some (Silent.τ, ω)) = 0
    · rw [hw, zero_mul, zero_mul]
    · have hstep : (𝒟(sys^w)).step (E.endState hT) Silent.τ ω :=
        S.valid E (Nat.find hT) (E.endState hT) (Nat.find_spec hT)
          (AlterSeq.stateAt_find_eq_endState E hT) Silent.τ ω ((PMF.mem_support_iff _ _).mpr hw)
      congr 1
      show (∑' e, (innerWitness sys (E.endState hT) ω).haltMass (E.endState hT) e
              * g (e.1.endState e.2))
          = ∑' m', ω m' * (∑' s, (macroExtend E m').endState (macroExtend_term hT m') s * g s)
      rw [innerWitness_integrate hstep g, tsum_bind_mul ω id g]
      simp only [id_eq]
      refine tsum_congr (fun m' => ?_)
      rw [macroExtend_endState hT m']

/-- **`oneDecisionC` integrate, macro-future form.** The same identity re-expressed
against the depth-`1` truncated macro-future distribution (`macroFuture_trunc_integrate_succ`),
matching `oneDecision.integrate` — the shape the σ\* squeeze consumes. -/
theorem oneDecisionC_integrate_trunc (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (oneDecisionC S E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S 1 E hT s * g s := by
  rw [oneDecisionC_integrate S E hT g]
  exact (macroFuture_trunc_integrate_succ S 0 E hT g).symm


/-- **`WeakScheduler.bind` compose-integrate law** (the v4 enabling primitive).
The weak-scheduler wrapper over the proven `Scheduler.bind_compose_integrate`:
integrating `g` against the halting end-states of `bind σ k` (from `μ_init`)
factors through `σ`'s halt states `f₁`, continuing with `k (f₁.end)` run from the
Dirac `pure (f₁.end)`. Definitionally the `Scheduler`-level law, since
`WeakScheduler.bind`/`haltMass` unfold to their `Scheduler` counterparts. -/
theorem WeakScheduler.bind_compose_integrate (σ : WeakScheduler sys)
    (k : State → WeakScheduler sys) (μ_init : PMF State) (g : State → ENNReal) :
    (∑' e, (WeakScheduler.bind σ k).haltMass μ_init e * g (e.1.endState e.2))
      = ∑' f₁ : {e : AlterSeq State Label // e.trans.Terminates},
          σ.haltMass μ_init f₁ *
            ∑' f₂ : {e : AlterSeq State Label // e.trans.Terminates},
              (k (f₁.1.endState f₁.2)).haltMass (PMF.pure (f₁.1.endState f₁.2)) f₂
                * g (f₂.1.endState f₂.2) :=
  Scheduler.bind_compose_integrate σ.toScheduler (fun s => (k s).toScheduler) μ_init g

open Classical in
/-- The halting end-state pushforward of an a.s.-halting weak scheduler `σ` from
source `μ`, as a genuine `PMF State` (total mass `1` by the a.s.-halting hypothesis). -/
noncomputable def pushforwardPMF {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) : PMF State :=
  ⟨fun s => ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = s then 1 else 0), by
    have hsum : (∑' s, ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = s then 1 else 0)) = 1 := by
      rw [ENNReal.tsum_comm]
      refine (tsum_congr fun e => ?_).trans hh
      rw [ENNReal.tsum_mul_left, tsum_eq_single (e.1.endState e.2)
        (fun s hs => by rw [if_neg (fun h => hs h.symm)]), if_pos rfl, mul_one]
    have hhs := ENNReal.summable.hasSum
      (f := fun s => ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = s then 1 else 0))
    rwa [hsum] at hhs⟩

open Classical in
/-- An a.s.-halting weak scheduler from source `μ` witnesses `weakTau sys μ` to its
own halting end-state pushforward. -/
theorem weakTau_of_halts {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) :
    weakTau sys μ (pushforwardPMF σ μ hh) :=
  ⟨σ, hh, fun _ => rfl⟩

/-- **Pure-source a.s.-halting corollary.** If `σ` halts a.s. from source `μ`, then it
halts a.s. from the Dirac at every `t ∈ μ.support`. (`M u := ∑'e haltMass (pure u) e ≤ 1`
averages to `1` against `μ`, forcing `M t = 1` on the support.) -/
theorem haltMass_pure_of_source {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) (t : State) (ht : t ∈ μ.support) :
    (∑' e, σ.haltMass (PMF.pure t) e) = 1 := by
  set M : State → ENNReal := fun u => ∑' e, σ.haltMass (PMF.pure u) e with hM
  have hle : ∀ u, M u ≤ 1 := fun u => WeakScheduler.haltMass_tsum_le_one σ (PMF.pure u)
  have hmix : (∑' u, μ u * M u) = 1 := by
    rw [← hh, tsum_congr (fun e => σ.haltMass_init_mix μ e), ENNReal.tsum_comm]
    exact tsum_congr fun u => by rw [hM, ENNReal.tsum_mul_left]
  have hab : ∀ u, μ u * M u ≤ μ u := fun u => mul_le_of_le_one_right' (hle u)
  have hnlt : ¬ (μ t * M t < μ t) := fun hlt => by
    have hcontra := ENNReal.tsum_lt_tsum (f := fun u => μ u * M u) (g := μ) (i := t)
      (by rw [hmix]; exact ENNReal.one_ne_top) hab hlt
    rw [hmix, μ.tsum_coe] at hcontra
    exact lt_irrefl 1 hcontra
  have heqt : μ t * M t = μ t * 1 := by rw [mul_one]; exact le_antisymm (hab t) (not_lt.mp hnlt)
  show M t = 1
  exact (ENNReal.mul_right_inj ((PMF.mem_support_iff μ t).mp ht) (μ.apply_ne_top t)).mp heqt

open Classical in
/-- **Pushforward integrate.** Integrating `g` against `σ`'s halting end-state
pushforward `PMF` equals integrating `g` against the halting end-states directly. -/
theorem pushforwardPMF_integrate {sys : System State Label} (σ : WeakScheduler sys)
    (μ : PMF State) (hh : (∑' e, σ.haltMass μ e) = 1) (g : State → ENNReal) :
    (∑' u, pushforwardPMF σ μ hh u * g u)
      = ∑' e, σ.haltMass μ e * g (e.1.endState e.2) := by
  calc (∑' u, pushforwardPMF σ μ hh u * g u)
      = ∑' u, (∑' e, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0)) * g u := rfl
    _ = ∑' u, ∑' e, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0) * g u :=
        tsum_congr (fun u => by rw [ENNReal.tsum_mul_right])
    _ = ∑' e, ∑' u, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0) * g u :=
        ENNReal.tsum_comm
    _ = ∑' e, σ.haltMass μ e * g (e.1.endState e.2) := by
        refine tsum_congr (fun e => ?_)
        rw [tsum_congr (fun u => by ring :
            ∀ u, σ.haltMass μ e * (if e.1.endState e.2 = u then 1 else 0) * g u
              = σ.haltMass μ e * ((if e.1.endState e.2 = u then 1 else 0) * g u)),
          ENNReal.tsum_mul_left]
        congr 1
        rw [tsum_eq_single (e.1.endState e.2)
            (fun u' hu' => by rw [if_neg (fun heq => hu' heq.symm), zero_mul]),
          if_pos rfl, one_mul]

/-- **Depth-1 truncated macro-future, pointwise.** One macro-step unfolding of
`macroFuture_trunc S 1 E hT` at a state `t`: halt now (`S.next E none`, source
`E.endState hT`) or take an emission `ω` and successor `m'` (weight `ω m'`, value
`m' t`). The pointwise companion of `macroFuture_trunc_integrate_succ`. -/
theorem macroFuture_trunc_one_apply (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    macroFuture_trunc S 1 E hT t
      = S.next E none * (E.endState hT) t
        + ∑' ω : PMF (PMF State), S.next E (some (Silent.τ, ω)) * ∑' m', ω m' * m' t := by
  have hzero : ∀ (l : Label) (ω : PMF (PMF State)), l ≠ Silent.τ →
      S.next E (some (l, ω)) = 0 := fun l ω hl => by
    by_contra hne
    exact hl (S.internal_only E l ω ((PMF.mem_support_iff _ _).mpr hne))
  have hunfold : macroFuture_trunc S 1 E hT
      = (S.next E).bind (fun o => match o with
          | none => E.endState hT
          | some (_, ω) => ω.bind (fun m' =>
              macroFuture_trunc S 0 (macroExtend E m') (macroExtend_term hT m'))) := rfl
  rw [hunfold, PMF.bind_apply, tsumOpt]
  congr 1
  rw [ENNReal.tsum_prod']
  rw [tsum_eq_single Silent.τ (fun l hl => by
    rw [ENNReal.tsum_eq_zero]; intro ω; rw [hzero l ω hl, zero_mul])]
  refine tsum_congr fun ω => ?_
  rw [PMF.bind_apply]
  congr 1
  refine tsum_congr fun m' => ?_
  rw [show macroFuture_trunc S 0 (macroExtend E m') (macroExtend_term hT m') = m' from
    macroExtend_endState hT m']

/-! ### Layer 4d (cont.): the coherent bind tower

The depth-`n` **coherent bind tower** `towerSched S n E hT : WeakScheduler sys`: a
concrete witness for `weakTau sys (E.end) (macroFuture_trunc S n E hT)` built by
`Nat.rec` from `WeakScheduler.bind` and `oneDecision`, so that its halting-integral
identity `towerSched_integrate` COMPOSES through `bind_compose_integrate` (unlike the
opaque classical witness of `weakTau_macroFuture_trunc`). This is the v4 route the
frontier docstring at `d_integrate_step` calls for. -/

/-- Bundled payload of the depth-`n` coherent bind tower rooted at `(E, hT)`: the
scheduler together with its `g`-integrated halting identity against the depth-`n`
truncated macro-future. Bundling is forced: the successor's continuation kernel is
built from the previous level's identity (via `weakTau_mix`), so definition and proof
are mutually recursive. -/
structure TowerData {sys : System State Label} (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) where
  /-- The depth-`n` tower scheduler. -/
  sched : WeakScheduler sys
  /-- Its `g`-integrated halting end-state identity: the coherence dividend. -/
  integrate : ∀ g : State → ENNReal,
    (∑' e, sched.haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s

/-- **Successor step of the coherent bind tower.** Given the depth-`n` family
`prev` (over all extended macro-histories), produce the depth-`(n+1)` tower rooted at
`(E, hT)`: `WeakScheduler.bind (oneDecision S E hT) k`, where the continuation `k t`
witnesses `weakTau sys (pure t) β_t` and `β_t` is the single-layer posterior mixture
over provenance `Option (PMF (PMF State) × PMF State)`. -/
noncomputable def towerStep (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates),
      TowerData S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    TowerData S (n + 1) E hT := by
  classical
  -- provenance weights: none = immediate halt, some (ω, m') = macro-emission
  let w : Option (PMF (PMF State) × PMF State) → State → ENNReal :=
    fun x t => match x with
      | none => S.next E none * (E.endState hT) t
      | some p => S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t
  -- the normalizer equals the depth-1 truncated macro-future
  have hZsum : ∀ t, (∑' x, w x t) = macroFuture_trunc S 1 E hT t := by
    intro t
    rw [tsumOpt (fun x => w x t), macroFuture_trunc_one_apply]
    congr 1
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun ω => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun m' => ?_
    show S.next E (some (Silent.τ, ω)) * ω m' * m' t
      = S.next E (some (Silent.τ, ω)) * (ω m' * m' t)
    rw [mul_assoc]
  have hZne : ∀ t, (∑' x, w x t) ≠ ⊤ := fun t => by
    rw [hZsum t]; exact (macroFuture_trunc S 1 E hT).apply_ne_top t
  -- posterior over provenance (junk when the normalizer vanishes)
  let q : State → PMF (Option (PMF (PMF State) × PMF State)) := fun t =>
    if h0 : (∑' x, w x t) = 0 then PMF.pure none
    else PMF.normalize (fun x => w x t) h0 (hZne t)
  -- the depth-n family halts a.s. from source `m'`
  have prevHalt' : ∀ m',
      (∑' e, (prev (macroExtend E m') (macroExtend_term hT m')).sched.haltMass m' e) = 1 := by
    intro m'
    have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
      macroExtend_endState hT m'
    have h := (prev (macroExtend E m') (macroExtend_term hT m')).integrate (fun _ => 1)
    simp only [mul_one] at h
    rw [hsrc] at h
    rw [h, (macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m')).tsum_coe]
  -- continuation targets: pure-halt (none) or the depth-n pushforward from `pure t`
  let branchTarget : State → Option (PMF (PMF State) × PMF State) → PMF State :=
    fun t x => match x with
      | none => PMF.pure t
      | some p => if ht : t ∈ (p.2).support
          then pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
                (PMF.pure t) (haltMass_pure_of_source _ p.2 (prevHalt' p.2) t ht)
          else PMF.pure t
  -- each posterior mixture is a weak-τ continuation out of `pure t`
  have H : ∀ t, weakTau sys (PMF.pure t) ((q t).bind (branchTarget t)) := by
    intro t
    have hmix : weakTau sys ((q t).bind (fun _ => PMF.pure t)) ((q t).bind (branchTarget t)) := by
      refine weakTau_mix (q t) (fun _ => PMF.pure t) (branchTarget t) ?_
      intro x hx
      match x with
      | none => exact weakTau_refl sys (PMF.pure t)
      | some p =>
          have hwne : w (some p) t ≠ 0 := by
            by_cases h0 : (∑' x, w x t) = 0
            · rw [show q t = PMF.pure none from dif_pos h0, PMF.mem_support_iff,
                PMF.pure_apply, if_neg (Option.some_ne_none p)] at hx
              exact absurd rfl hx
            · rw [show q t = PMF.normalize (fun x => w x t) h0 (hZne t) from dif_neg h0,
                PMF.mem_support_iff, PMF.normalize_apply] at hx
              exact left_ne_zero_of_mul hx
          have ht : t ∈ (p.2).support := by
            rw [PMF.mem_support_iff]; intro hz
            exact hwne (by
              show S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t = 0
              rw [hz, mul_zero])
          have hht := haltMass_pure_of_source
            (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched p.2 (prevHalt' p.2) t ht
          rw [show branchTarget t (some p)
              = pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
                (PMF.pure t) hht from dif_pos ht]
          exact weakTau_of_halts _ (PMF.pure t) hht
    rwa [PMF.bind_const] at hmix
  exact
    { sched := WeakScheduler.bind (oneDecision S E hT) (fun t => (H t).witnessScheduler)
      integrate := fun g => by
        -- normalizer cancellation: `mft1 t · q t x = w x t`
        have hcancel : ∀ t x, macroFuture_trunc S 1 E hT t * q t x = w x t := by
          intro t x
          by_cases h0 : (∑' y, w y t) = 0
          · have hmft : macroFuture_trunc S 1 E hT t = 0 := (hZsum t).symm.trans h0
            have hwx : w x t = 0 := ENNReal.tsum_eq_zero.mp h0 x
            rw [hmft, zero_mul, hwx]
          · rw [show q t = PMF.normalize (fun y => w y t) h0 (hZne t) from dif_neg h0,
              PMF.normalize_apply, ← hZsum t, ← mul_assoc, mul_comm _ (w x t), mul_assoc,
              ENNReal.mul_inv_cancel h0 (hZne t), mul_one]
        -- expectation under a Dirac
        have hpure : ∀ (t : State), (∑' s, (PMF.pure t) s * g s) = g t := fun t => by
          rw [tsum_eq_single t (fun s hs => by rw [PMF.pure_apply, if_neg hs, zero_mul]),
            PMF.pure_apply, if_pos rfl, one_mul]
        -- per-`t` posterior collapse
        have hΦcancel : ∀ t, macroFuture_trunc S 1 E hT t
              * (∑' s, ((q t).bind (branchTarget t)) s * g s)
            = ∑' x, w x t * (∑' s, branchTarget t x s * g s) := by
          intro t
          rw [tsum_bind_mul (q t) (branchTarget t) g, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun x => by rw [← mul_assoc, hcancel t x]
        -- term A (immediate-halt provenance)
        have hTermA : (∑' t, w none t * (∑' s, branchTarget t none s * g s))
            = S.next E none * (∑' s, (E.endState hT) s * g s) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun t => ?_
          show S.next E none * (E.endState hT) t * (∑' s, (PMF.pure t) s * g s)
            = S.next E none * ((E.endState hT) t * g t)
          rw [hpure t, mul_assoc]
        -- term B (macro-emission provenance)
        have hTermB : (∑' p : PMF (PMF State) × PMF State,
              ∑' t, w (some p) t * (∑' s, branchTarget t (some p) s * g s))
            = ∑' ω, S.next E (some (Silent.τ, ω)) * ∑' m', ω m'
                * (∑' s, macroFuture_trunc S n (macroExtend E m')
                    (macroExtend_term hT m') s * g s) := by
          rw [ENNReal.tsum_prod']
          refine tsum_congr fun ω => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun m' => ?_
          set σ' := (prev (macroExtend E m') (macroExtend_term hT m')).sched with hσ'
          have hbridge : (∑' t, m' t * (∑' s, branchTarget t (some (ω, m')) s * g s))
              = ∑' s, macroFuture_trunc S n (macroExtend E m')
                  (macroExtend_term hT m') s * g s := by
            have hstep : ∀ t, m' t * (∑' s, branchTarget t (some (ω, m')) s * g s)
                = m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) := by
              intro t
              by_cases ht : t ∈ (m').support
              · congr 1
                rw [show branchTarget t (some (ω, m'))
                    = pushforwardPMF σ' (PMF.pure t)
                      (haltMass_pure_of_source _ m' (prevHalt' m') t ht) from dif_pos ht]
                exact pushforwardPMF_integrate _ (PMF.pure t) _ g
              · rw [PMF.mem_support_iff, not_not] at ht
                rw [ht, zero_mul, zero_mul]
            rw [tsum_congr hstep]
            have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
              macroExtend_endState hT m'
            have hint := (prev (macroExtend E m') (macroExtend_term hT m')).integrate g
            rw [hsrc, ← hσ'] at hint
            calc (∑' t, m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)))
                = ∑' t, ∑' e, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                  tsum_congr fun t => ENNReal.tsum_mul_left.symm
              _ = ∑' e, ∑' t, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                  ENNReal.tsum_comm
              _ = ∑' e, (∑' t, m' t * σ'.haltMass (PMF.pure t) e) * g (e.1.endState e.2) := by
                  refine tsum_congr fun e => ?_
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun t => by rw [mul_assoc]
              _ = ∑' e, σ'.haltMass m' e * g (e.1.endState e.2) := by
                  refine tsum_congr fun e => ?_
                  rw [← WeakScheduler.haltMass_init_mix]
              _ = ∑' s, macroFuture_trunc S n (macroExtend E m')
                    (macroExtend_term hT m') s * g s := hint
          rw [← hbridge, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun t => ?_
          show S.next E (some (Silent.τ, ω)) * ω m' * m' t
              * (∑' s, branchTarget t (some (ω, m')) s * g s)
            = S.next E (some (Silent.τ, ω))
              * (ω m' * (m' t * (∑' s, branchTarget t (some (ω, m')) s * g s)))
          ring
        -- assemble: bind_compose ↦ mft1-reweight ↦ cancel ↦ split ↦ A + B
        have h123 : (∑' e, (WeakScheduler.bind (oneDecision S E hT)
                (fun t => (H t).witnessScheduler)).haltMass (E.endState hT) e
              * g (e.1.endState e.2))
            = ∑' t, macroFuture_trunc S 1 E hT t
                * (∑' s, ((q t).bind (branchTarget t)) s * g s) := by
          rw [WeakScheduler.bind_compose_integrate]
          have hin : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
              (∑' f₂, (H (f₁.1.endState f₁.2)).witnessScheduler.haltMass
                  (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
              = ∑' s, ((q (f₁.1.endState f₁.2)).bind
                  (branchTarget (f₁.1.endState f₁.2))) s * g s :=
            fun f₁ => (H (f₁.1.endState f₁.2)).integrate g
          simp_rw [hin]
          exact (weakTau_macroFuture_trunc S 1 E hT).integrate
            (fun t => ∑' s, ((q t).bind (branchTarget t)) s * g s)
        rw [h123, macroFuture_trunc_integrate_succ S n E hT g, tsum_congr hΦcancel,
          ENNReal.tsum_comm, tsumOpt, hTermA, hTermB] }

/-- The coherent bind tower, by `Nat.rec`. Depth `0` is the immediate-halt witness
(`weakTau_refl`); depth `n+1` is `WeakScheduler.bind (oneDecision S E hT) k` with the
posterior-mixing continuation `k`.

REMAINING (successor): `k t` is the witness of `weakTau sys (pure t) β_t`, where `β_t`
is the single-layer posterior mixture over provenance `(none | some (ω,m'))` given the
halt-state `t` of `oneDecision`: weight `S.next E none · (E.end) t` continues by
immediate halt, weight `S.next E (τ,ω) · ω m' · m' t` continues by `towerData S n
(macroExtend E m')` (its pure-`t` halting is the `t∈supp(m')` corollary of the depth-`n`
`integrate`). Normalizer `∑ = macroFuture_trunc S 1 E hT t ≤ 1` (`ne_top` trivial). The
`integrate` field then follows: `bind_compose_integrate` factors through `oneDecision`'s
halt states; `(weakTau_macroFuture_trunc S 1 E hT).integrate` reweights by
`macroFuture_trunc S 1`; the normalizer cancels the posterior denominator, leaving
`macroFuture_trunc_integrate_succ`'s two terms closed by depth-`n` `integrate`. -/
noncomputable def towerData {sys : System State Label} (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → (hT : E.trans.Terminates) →
      TowerData S n E hT
  | 0, E, hT =>
    { sched := (weakTau_refl sys (E.endState hT)).witnessScheduler
      integrate := fun g => by
        simpa only [macroFuture_trunc] using (weakTau_refl sys (E.endState hT)).integrate g }
  | n + 1, E, hT => towerStep S n (fun E' hT' => towerData S n E' hT') E hT
  termination_by n => n

/-- The depth-`n` coherent bind tower witnessing
`weakTau sys (E.end) (macroFuture_trunc S n E hT)`. -/
noncomputable def towerSched {sys : System State Label} (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys :=
  (towerData S n E hT).sched

/-- **T2 — the tower realizes the truncation (pushforward/integrate).** The coherence
dividend: the tower's `g`-integrated halting end-state equals the `g`-integral of the
depth-`n` truncated macro-future. -/
theorem towerSched_integrate {sys : System State Label} (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (towerSched S n E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s :=
  (towerData S n E hT).integrate g

/-- **T2 — the tower halts almost surely** from the current source `E.end`. The `g:=1`
specialization of `towerSched_integrate` (the truncated macro-future is a `PMF`). -/
theorem towerSched_halts {sys : System State Label} (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    (∑' e, (towerSched S n E hT).haltMass (E.endState hT) e) = 1 := by
  have h := towerSched_integrate S n E hT (fun _ => 1)
  simp only [mul_one] at h
  rw [h, (macroFuture_trunc S n E hT).tsum_coe]

/-! ### Generic belief scheduler over a branch family

The `oneDecisionC` pattern (a dite-normalized posterior mixture over a hidden index),
abstracted over an arbitrary index type `ι`, weight `PMF ι`, source `μ`, and branch
family `fam : ι → WeakScheduler sys`, so that the concrete continuation `contC` can
reuse the `probOf`/`haltMass`/`integrate` induction verbatim. -/

open Classical in
/-- Per-branch path measure of family member `fam x` from source `μ` (0 off-termination). -/
noncomputable def bBranchProb {ι : Type} (fam : ι → WeakScheduler sys)
    (μ : PMF State) (x : ι) (e : AlterSeq State Label) : ENNReal :=
  if h : e.trans.Terminates then
    (⟨μ, (fam x).toScheduler⟩ : ProbabilisticExecution sys).probOf e h
  else 0

/-- Exposed **numerator** of the belief scheduler at emission `o`. -/
noncomputable def bNum {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) (o : Option (Label × PMF State)) : ENNReal :=
  ∑' x, wt x * bBranchProb fam μ x e * (fam x).next e o

/-- Exposed **denominator** (composite path measure) of the belief scheduler at `e`. -/
noncomputable def bDenom {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) : ENNReal :=
  ∑' x, wt x * bBranchProb fam μ x e

theorem bBranchProb_le_one {ι : Type} (fam : ι → WeakScheduler sys)
    (μ : PMF State) (x : ι) (e : AlterSeq State Label) :
    bBranchProb fam μ x e ≤ 1 := by
  classical
  unfold bBranchProb
  split
  · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
  · exact zero_le_one

theorem bNum_tsum {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) :
    (∑' o, bNum fam wt μ e o) = bDenom fam wt μ e := by
  unfold bNum bDenom
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

theorem bDenom_le_one {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) :
    bDenom fam wt μ e ≤ 1 := by
  unfold bDenom
  calc (∑' x, wt x * bBranchProb fam μ x e)
      ≤ ∑' x, wt x :=
        ENNReal.tsum_le_tsum (fun x => mul_le_of_le_one_right' (bBranchProb_le_one fam μ x e))
    _ = 1 := wt.tsum_coe

theorem bDenom_ne_top {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) :
    bDenom fam wt μ e ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (bDenom_le_one fam wt μ e)

open Classical in
/-- The generic single-layer belief scheduler: normalized posterior `bNum/bDenom`. -/
noncomputable def beliefSched {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) : WeakScheduler sys where
  next e := if h : bDenom fam wt μ e = 0 then PMF.pure none
    else PMF.normalize (bNum fam wt μ e) (by rw [bNum_tsum]; exact h)
      (by rw [bNum_tsum]; exact bDenom_ne_top fam wt μ e)
  valid := by
    classical
    intro e n s hterm hstate l ν hsupp
    by_cases hd : bDenom fam wt μ e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : bNum fam wt μ e (some (l, ν)) ≠ 0 := hsupp
      rw [bNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (fam x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (fam x).valid e n s hterm hstate l ν ((PMF.mem_support_iff _ _).mpr hnextne)
  internal_only := by
    classical
    intro e l ν hsupp
    by_cases hd : bDenom fam wt μ e = 0
    · rw [dif_pos hd, PMF.mem_support_iff, PMF.pure_apply_of_ne _ _ (by simp)] at hsupp
      exact absurd rfl hsupp
    · simp only [dif_neg hd, PMF.mem_support_normalize_iff] at hsupp
      have hgne : bNum fam wt μ e (some (l, ν)) ≠ 0 := hsupp
      rw [bNum] at hgne
      have hex := mt ENNReal.tsum_eq_zero.mpr hgne
      push Not at hex
      obtain ⟨x, hxne⟩ := hex
      have hnextne : (fam x).next e (some (l, ν)) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hxne; exact hxne rfl
      exact (fam x).internal_only e l ν ((PMF.mem_support_iff _ _).mpr hnextne)

/-- **Cancellation:** `bDenom · beliefSched.next = bNum`. -/
theorem beliefSched_cancel {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) (o : Option (Label × PMF State)) :
    bDenom fam wt μ e * (beliefSched fam wt μ).next e o = bNum fam wt μ e o := by
  classical
  by_cases hd : bDenom fam wt μ e = 0
  · have hnext : (beliefSched fam wt μ).next e = PMF.pure none := dif_pos hd
    rw [hnext, hd, zero_mul]
    have hall : ∀ o', bNum fam wt μ e o' = 0 := by
      rw [← ENNReal.tsum_eq_zero, bNum_tsum]; exact hd
    exact (hall o).symm
  · have hnext : (beliefSched fam wt μ).next e o
        = bNum fam wt μ e o * (bDenom fam wt μ e)⁻¹ := by
      have h1 : (beliefSched fam wt μ).next e
          = PMF.normalize (bNum fam wt μ e) (by rw [bNum_tsum]; exact hd)
            (by rw [bNum_tsum]; exact bDenom_ne_top fam wt μ e) := dif_neg hd
      rw [h1, PMF.normalize_apply, bNum_tsum]
    rw [hnext, ← mul_assoc, mul_comm (bDenom fam wt μ e) (bNum fam wt μ e o), mul_assoc,
      ENNReal.mul_inv_cancel hd (bDenom_ne_top fam wt μ e), mul_one]

/-- **Belief consistency (pointwise).** The `beliefSched`-path measure of a terminating
history `e` from source `μ` is exactly `bDenom e`. Induction on `e` (`List.reverseRecOn`). -/
theorem beliefSched_probOf {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : AlterSeq State Label) (hFin : e.trans.Terminates) :
    (⟨μ, (beliefSched fam wt μ).toScheduler⟩ : ProbabilisticExecution sys).probOf e hFin
      = bDenom fam wt μ e := by
  classical
  set pe : ProbabilisticExecution sys := ⟨μ, (beliefSched fam wt μ).toScheduler⟩ with hpe
  change pe.probOf e hFin = bDenom fam wt μ e
  suffices hgen : ∀ (L : List (Label × State)) (s₀ : State)
      (hFin : (Seq.ofList L : Seq (Label × State)).Terminates),
      pe.probOf ⟨s₀, Seq.ofList L⟩ hFin = bDenom fam wt μ ⟨s₀, Seq.ofList L⟩ by
    have hofl : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)) = e.trans :=
      Stream'.Seq.ofList_toList e.trans hFin
    have hFin' : (Seq.ofList (e.trans.toList hFin) : Seq (Label × State)).Terminates := by
      rw [hofl]; exact hFin
    have hEeq : (⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ : AlterSeq State Label) = e := by
      cases e; simp only [hofl]
    have hkey := hgen (e.trans.toList hFin) e.init hFin'
    rw [pe.probOf_congr ⟨e.init, Seq.ofList (e.trans.toList hFin)⟩ e hEeq hFin' hFin] at hkey
    rw [hkey, hEeq]
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro s₀ hFin
    rw [pe.probOf_congr ⟨s₀, Seq.ofList ([] : List (Label × State))⟩ ⟨s₀, Seq.nil⟩
      (by rw [Stream'.Seq.ofList_nil]) hFin Stream'.Seq.terminates_nil,
      ProbabilisticExecution.probOf_nil, Stream'.Seq.ofList_nil]
    have hbp : ∀ x, bBranchProb fam μ x ⟨s₀, Seq.nil⟩ = μ s₀ := by
      intro x
      unfold bBranchProb
      rw [dif_pos Stream'.Seq.terminates_nil, ProbabilisticExecution.probOf_nil,
        ProbabilisticExecution.init_eq_initState]
    change μ s₀ = bDenom fam wt μ ⟨s₀, Seq.nil⟩
    unfold bDenom
    rw [tsum_congr (fun x => by rw [hbp x]), ENNReal.tsum_mul_right, wt.tsum_coe, one_mul]
  | append_singleton rest last ih =>
    intro s₀ hFin
    obtain ⟨l, s'⟩ := last
    have hsplit : (Seq.ofList (rest ++ [(l, s')]) : Seq (Label × State))
        = (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil) := by
      rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
    have hrest_fin : (Seq.ofList rest : Seq (Label × State)).Terminates :=
      Stream'.Seq.terminates_ofList _
    have hFinS : ((Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)).Terminates := by
      rw [← hsplit]; exact hFin
    set E' : AlterSeq State Label := ⟨s₀, Seq.ofList rest⟩ with hE'
    have hbpstep : ∀ x, bBranchProb fam μ x E'
        * (∑' ν, (fam x).next E' (some (l, ν)) * ν s')
        = bBranchProb fam μ x ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ := by
      intro x
      unfold bBranchProb
      rw [dif_pos hrest_fin, dif_pos hFin,
        (⟨μ, (fam x).toScheduler⟩ : ProbabilisticExecution sys).probOf_congr
          ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        ProbabilisticExecution.probOf_append_singleton _ s₀ (Seq.ofList rest) hrest_fin (l, s')
          hFinS, ProbabilisticExecution.kernel]
    set Mid : ENNReal := ∑' x, wt x * bBranchProb fam μ x E'
      * (∑' ν, (fam x).next E' (some (l, ν)) * ν s') with hMid
    have hLHS : pe.probOf ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ hFin = Mid := by
      rw [pe.probOf_congr ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩
          ⟨s₀, (Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ (by rw [hsplit]) hFin hFinS,
        pe.probOf_append_singleton s₀ (Seq.ofList rest) hrest_fin (l, s') hFinS,
        show pe.probOf E' hrest_fin = bDenom fam wt μ E' from ih s₀ hrest_fin,
        ProbabilisticExecution.kernel]
      change bDenom fam wt μ E' * (∑' ν, (beliefSched fam wt μ).next E' (some (l, ν)) * ν s') = Mid
      have hstep2 : ∀ ν, bNum fam wt μ E' (some (l, ν)) * ν s'
          = ∑' x, wt x * bBranchProb fam μ x E'
              * (fam x).next E' (some (l, ν)) * ν s' := by
        intro ν; unfold bNum; rw [ENNReal.tsum_mul_right]
      rw [← ENNReal.tsum_mul_left,
        tsum_congr (fun ν => by rw [← mul_assoc, beliefSched_cancel fam wt μ E' (some (l, ν))]),
        tsum_congr hstep2, ENNReal.tsum_comm, hMid]
      refine tsum_congr (fun x => ?_)
      rw [tsum_congr (fun ν => mul_assoc (wt x * bBranchProb fam μ x E') _ _),
        ENNReal.tsum_mul_left]
    have hRHS : bDenom fam wt μ ⟨s₀, Seq.ofList (rest ++ [(l, s')])⟩ = Mid := by
      unfold bDenom
      rw [hMid]
      refine tsum_congr (fun x => ?_)
      rw [← hbpstep x, ← mul_assoc]
    rw [hLHS, hRHS]

/-- **Belief halting mass as a branch mixture.** -/
theorem beliefSched_haltMass {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    (beliefSched fam wt μ).haltMass μ e
      = ∑' x, wt x * (fam x).haltMass μ e := by
  classical
  have hhalt : (beliefSched fam wt μ).haltMass μ e = bNum fam wt μ e.1 none := by
    unfold WeakScheduler.haltMass Scheduler.haltMass
    rw [show (⟨μ, (beliefSched fam wt μ).toScheduler⟩
          : ProbabilisticExecution sys).probOf e.1 e.2 = bDenom fam wt μ e.1 from
        beliefSched_probOf fam wt μ e.1 e.2]
    exact beliefSched_cancel fam wt μ e.1 none
  rw [hhalt]
  unfold bNum
  refine tsum_congr (fun x => ?_)
  rw [mul_assoc]
  congr 1
  unfold WeakScheduler.haltMass Scheduler.haltMass bBranchProb
  rw [dif_pos e.2]

/-- **Generic integrate identity.** The `g`-integrated halting end-state of `beliefSched`
factors through the hidden index: `∑' x, wt x · (branch integral)`. -/
theorem beliefSched_integrate {ι : Type} (fam : ι → WeakScheduler sys) (wt : PMF ι)
    (μ : PMF State) (g : State → ENNReal) :
    (∑' e, (beliefSched fam wt μ).haltMass μ e * g (e.1.endState e.2))
      = ∑' x, wt x
          * (∑' e, (fam x).haltMass μ e * g (e.1.endState e.2)) := by
  classical
  have he : ∀ e : {e : AlterSeq State Label // e.trans.Terminates},
      (beliefSched fam wt μ).haltMass μ e * g (e.1.endState e.2)
        = ∑' x, wt x * (fam x).haltMass μ e
            * g (e.1.endState e.2) := by
    intro e
    rw [beliefSched_haltMass fam wt μ e, ENNReal.tsum_mul_right]
  rw [tsum_congr he, ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [tsum_congr (fun e => mul_assoc (wt x) _ _), ENNReal.tsum_mul_left]

/-! ### The concrete coherent bind tower `TowerDataC` (numerator-exposed, route (b))

Mirrors `TowerData`/`towerStep`/`towerData`, but built from the numerator-exposed
`oneDecisionC` and a CONCRETE single-layer belief continuation `contC` (an instance of
`beliefSched`) in place of the opaque `Classical.choose` witnesses, so its `next` carries
an exposed numerator for the `⨆ n` limit. -/

/-- Bundled payload of the depth-`n` concrete tower rooted at `(E, hT)`: scheduler plus
its `g`-integrated halting identity against the depth-`n` truncated macro-future.
Identical fields to `TowerData`; kept distinct so the concrete recursion is self-contained. -/
structure TowerDataC {sys : System State Label} (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) where
  /-- The depth-`n` concrete tower scheduler. -/
  sched : WeakScheduler sys
  /-- Its `g`-integrated halting end-state identity. -/
  integrate : ∀ g : State → ENNReal,
    (∑' e, sched.haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s

/-- Provenance weights at halt-state `t`: `none` = immediate halt, `some (ω, m')` =
macro-emission. -/
noncomputable def ctW (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    Option (PMF (PMF State) × PMF State) → State → ENNReal :=
  fun x t => match x with
    | none => S.next E none * (E.endState hT) t
    | some p => S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t

/-- The provenance weights sum to the depth-1 truncated macro-future. -/
theorem ctZsum (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    (∑' x, ctW S E hT x t) = macroFuture_trunc S 1 E hT t := by
  rw [tsumOpt (fun x => ctW S E hT x t), macroFuture_trunc_one_apply]
  congr 1
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun m' => ?_
  show S.next E (some (Silent.τ, ω)) * ω m' * m' t
    = S.next E (some (Silent.τ, ω)) * (ω m' * m' t)
  rw [mul_assoc]

/-- The provenance normalizer is never `⊤`. -/
theorem ctZne (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    (∑' x, ctW S E hT x t) ≠ ⊤ := by
  rw [ctZsum]; exact (macroFuture_trunc S 1 E hT).apply_ne_top t

/-- The normalized provenance posterior at halt-state `t` (junk `pure none` off support). -/
noncomputable def ctPost (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    PMF (Option (PMF (PMF State) × PMF State)) :=
  if h0 : (∑' x, ctW S E hT x t) = 0 then PMF.pure none
  else PMF.normalize (fun x => ctW S E hT x t) h0 (ctZne S E hT t)

/-- Continuation branch family: immediate-halt (`stop`) or the depth-`n` tower at the
extended root `macroExtend E m'`. -/
noncomputable def ctFam (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    Option (PMF (PMF State) × PMF State) → WeakScheduler sys :=
  fun x => match x with
    | none => WeakScheduler.stop sys
    | some p => (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched

/-- The depth-`n` family halts a.s. from source `m'` (the `prevHalt'` of `towerStep`). -/
theorem ctPrevHalt (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (m' : PMF State) :
    (∑' e, (prev (macroExtend E m') (macroExtend_term hT m')).sched.haltMass m' e) = 1 := by
  have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
    macroExtend_endState hT m'
  have h := (prev (macroExtend E m') (macroExtend_term hT m')).integrate (fun _ => 1)
  simp only [mul_one] at h
  rw [hsrc] at h
  rw [h, (macroFuture_trunc S n (macroExtend E m') (macroExtend_term hT m')).tsum_coe]

open Classical in
/-- Continuation targets from the Dirac `pure t`: `none` ↦ `pure t`, `some p` ↦ the
depth-`n` pushforward from `pure t` (`pure t` off `p.2`'s support). -/
noncomputable def branchTargetC (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) :
    Option (PMF (PMF State) × PMF State) → PMF State :=
  fun x => match x with
    | none => PMF.pure t
    | some p => if ht : t ∈ (p.2).support
        then pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
              (PMF.pure t) (haltMass_pure_of_source _ p.2 (ctPrevHalt S prev E hT p.2) t ht)
        else PMF.pure t

/-- **The concrete continuation kernel.** At a halt-state `t` of `oneDecisionC`, the
single-layer belief scheduler mixing the provenance posterior `ctPost t` over the
branch family `ctFam`, run from the Dirac source `pure t`. An instance of `beliefSched`,
so its `next` carries the exposed numerator `bNum (ctFam …) (ctPost … t) (pure t)`. -/
noncomputable def contC (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) : WeakScheduler sys :=
  beliefSched (ctFam S prev E hT) (ctPost S E hT t) (PMF.pure t)

/-- **Continuation integrate (RHS-parity with the opaque `(H t).integrate`).** The
`g`-integrated halting end-state of `contC` from source `pure t` equals the `g`-integral
of the posterior mixture `(ctPost t).bind (branchTargetC t)` — the exact right-hand side
the opaque `towerStep` continuation produced, so the tower integrate proof transplants. -/
theorem contC_integrate (S : WeakScheduler (𝒟(sys^w))) {n : ℕ}
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (t : State) (g : State → ENNReal) :
    (∑' e, (contC S prev E hT t).haltMass (PMF.pure t) e * g (e.1.endState e.2))
      = ∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s := by
  classical
  have hc : contC S prev E hT t
      = beliefSched (ctFam S prev E hT) (ctPost S E hT t) (PMF.pure t) := rfl
  rw [hc, beliefSched_integrate (ctFam S prev E hT) (ctPost S E hT t) (PMF.pure t) g,
    tsum_bind_mul (ctPost S E hT t) (branchTargetC S prev E hT t) g]
  refine tsum_congr fun x => ?_
  cases x with
  | none =>
      congr 1
      show (∑' e, (WeakScheduler.stop sys).haltMass (PMF.pure t) e * g (e.1.endState e.2))
        = ∑' s, (PMF.pure t) s * g s
      exact stop_integrate (PMF.pure t) g
  | some p =>
      by_cases ht : t ∈ (p.2).support
      · congr 1
        rw [show branchTargetC S prev E hT t (some p)
            = pushforwardPMF (prev (macroExtend E p.2) (macroExtend_term hT p.2)).sched
              (PMF.pure t) (haltMass_pure_of_source _ p.2 (ctPrevHalt S prev E hT p.2) t ht)
            from dif_pos ht]
        exact (pushforwardPMF_integrate _ (PMF.pure t) _ g).symm
      · have hw0 : ctW S E hT (some p) t = 0 := by
          show S.next E (some (Silent.τ, p.1)) * p.1 p.2 * p.2 t = 0
          rw [PMF.mem_support_iff, not_not] at ht
          rw [ht, mul_zero]
        have hpost0 : ctPost S E hT t (some p) = 0 := by
          by_cases h0 : (∑' x, ctW S E hT x t) = 0
          · rw [ctPost, dif_pos h0, PMF.pure_apply, if_neg (Option.some_ne_none p)]
          · rw [ctPost, dif_neg h0, PMF.normalize_apply, hw0, zero_mul]
        rw [hpost0, zero_mul, zero_mul]

/-- **Successor step of the concrete tower.** Given the depth-`n` concrete family `prev`,
the depth-`(n+1)` tower rooted at `(E, hT)`: `WeakScheduler.bind (oneDecisionC S E hT) contC`.
Integrate proof transplanted from the opaque `towerStep` (RHS parity), with `contC_integrate`
for `(H t).integrate` and `oneDecisionC_integrate_trunc` for the depth-1 reweight. -/
noncomputable def towerStepC (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (prev : ∀ (E' : AlterSeq (PMF State) Label) (hT' : E'.trans.Terminates), TowerDataC S n E' hT')
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    TowerDataC S (n + 1) E hT :=
  { sched := WeakScheduler.bind (oneDecisionC S E hT) (fun t => contC S prev E hT t)
    integrate := fun g => by
      classical
      have hcancel : ∀ t x, macroFuture_trunc S 1 E hT t * ctPost S E hT t x = ctW S E hT x t := by
        intro t x
        by_cases h0 : (∑' y, ctW S E hT y t) = 0
        · have hmft : macroFuture_trunc S 1 E hT t = 0 := (ctZsum S E hT t).symm.trans h0
          have hwx : ctW S E hT x t = 0 := ENNReal.tsum_eq_zero.mp h0 x
          rw [hmft, zero_mul, hwx]
        · rw [show ctPost S E hT t = PMF.normalize (fun y => ctW S E hT y t) h0 (ctZne S E hT t)
              from dif_neg h0,
            PMF.normalize_apply, ← ctZsum S E hT t, ← mul_assoc, mul_comm _ (ctW S E hT x t),
            mul_assoc, ENNReal.mul_inv_cancel h0 (ctZne S E hT t), mul_one]
      have hpure : ∀ (t : State), (∑' s, (PMF.pure t) s * g s) = g t := fun t => by
        rw [tsum_eq_single t (fun s hs => by rw [PMF.pure_apply, if_neg hs, zero_mul]),
          PMF.pure_apply, if_pos rfl, one_mul]
      have hΦcancel : ∀ t, macroFuture_trunc S 1 E hT t
            * (∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s)
          = ∑' x, ctW S E hT x t * (∑' s, branchTargetC S prev E hT t x s * g s) := by
        intro t
        rw [tsum_bind_mul (ctPost S E hT t) (branchTargetC S prev E hT t) g,
          ← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by rw [← mul_assoc, hcancel t x]
      have hTermA : (∑' t, ctW S E hT none t * (∑' s, branchTargetC S prev E hT t none s * g s))
          = S.next E none * (∑' s, (E.endState hT) s * g s) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        show S.next E none * (E.endState hT) t * (∑' s, (PMF.pure t) s * g s)
          = S.next E none * ((E.endState hT) t * g t)
        rw [hpure t, mul_assoc]
      have hTermB : (∑' p : PMF (PMF State) × PMF State,
            ∑' t, ctW S E hT (some p) t * (∑' s, branchTargetC S prev E hT t (some p) s * g s))
          = ∑' ω, S.next E (some (Silent.τ, ω)) * ∑' m', ω m'
              * (∑' s, macroFuture_trunc S n (macroExtend E m')
                  (macroExtend_term hT m') s * g s) := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun ω => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun m' => ?_
        set σ' := (prev (macroExtend E m') (macroExtend_term hT m')).sched with hσ'
        have hbridge : (∑' t, m' t * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s))
            = ∑' s, macroFuture_trunc S n (macroExtend E m')
                (macroExtend_term hT m') s * g s := by
          have hstep : ∀ t, m' t * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s)
              = m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) := by
            intro t
            by_cases ht : t ∈ (m').support
            · congr 1
              rw [show branchTargetC S prev E hT t (some (ω, m'))
                  = pushforwardPMF σ' (PMF.pure t)
                    (haltMass_pure_of_source _ m' (ctPrevHalt S prev E hT m') t ht) from dif_pos ht]
              exact pushforwardPMF_integrate _ (PMF.pure t) _ g
            · rw [PMF.mem_support_iff, not_not] at ht
              rw [ht, zero_mul, zero_mul]
          rw [tsum_congr hstep]
          have hsrc : (macroExtend E m').endState (macroExtend_term hT m') = m' :=
            macroExtend_endState hT m'
          have hint := (prev (macroExtend E m') (macroExtend_term hT m')).integrate g
          rw [hsrc, ← hσ'] at hint
          calc (∑' t, m' t * (∑' e, σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)))
              = ∑' t, ∑' e, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                tsum_congr fun t => ENNReal.tsum_mul_left.symm
            _ = ∑' e, ∑' t, m' t * (σ'.haltMass (PMF.pure t) e * g (e.1.endState e.2)) :=
                ENNReal.tsum_comm
            _ = ∑' e, (∑' t, m' t * σ'.haltMass (PMF.pure t) e) * g (e.1.endState e.2) := by
                refine tsum_congr fun e => ?_
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun t => by rw [mul_assoc]
            _ = ∑' e, σ'.haltMass m' e * g (e.1.endState e.2) := by
                refine tsum_congr fun e => ?_
                rw [← WeakScheduler.haltMass_init_mix]
            _ = ∑' s, macroFuture_trunc S n (macroExtend E m')
                  (macroExtend_term hT m') s * g s := hint
        rw [← hbridge, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        show S.next E (some (Silent.τ, ω)) * ω m' * m' t
            * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s)
          = S.next E (some (Silent.τ, ω))
            * (ω m' * (m' t * (∑' s, branchTargetC S prev E hT t (some (ω, m')) s * g s)))
        ring
      have h123 : (∑' e, (WeakScheduler.bind (oneDecisionC S E hT)
              (fun t => contC S prev E hT t)).haltMass (E.endState hT) e
            * g (e.1.endState e.2))
          = ∑' t, macroFuture_trunc S 1 E hT t
              * (∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s) := by
        rw [WeakScheduler.bind_compose_integrate]
        have hin : ∀ f₁ : {e : AlterSeq State Label // e.trans.Terminates},
            (∑' f₂, (contC S prev E hT (f₁.1.endState f₁.2)).haltMass
                (PMF.pure (f₁.1.endState f₁.2)) f₂ * g (f₂.1.endState f₂.2))
            = ∑' s, ((ctPost S E hT (f₁.1.endState f₁.2)).bind
                (branchTargetC S prev E hT (f₁.1.endState f₁.2))) s * g s :=
          fun f₁ => contC_integrate S prev E hT (f₁.1.endState f₁.2) g
        simp_rw [hin]
        exact oneDecisionC_integrate_trunc S E hT
          (fun t => ∑' s, ((ctPost S E hT t).bind (branchTargetC S prev E hT t)) s * g s)
      rw [h123, macroFuture_trunc_integrate_succ S n E hT g, tsum_congr hΦcancel,
        ENNReal.tsum_comm, tsumOpt, hTermA, hTermB] }

/-- The concrete coherent bind tower, by `Nat.rec`. Depth `0` is the immediate-stop
witness `WeakScheduler.stop`; depth `n+1` is `towerStepC`. -/
noncomputable def towerDataC (S : WeakScheduler (𝒟(sys^w))) :
    (n : ℕ) → (E : AlterSeq (PMF State) Label) → (hT : E.trans.Terminates) →
      TowerDataC S n E hT
  | 0, E, hT =>
    { sched := WeakScheduler.stop sys
      integrate := fun g => by
        simpa only [macroFuture_trunc] using stop_integrate (E.endState hT) g }
  | n + 1, E, hT => towerStepC S n (fun E' hT' => towerDataC S n E' hT') E hT
  termination_by n => n

/-- The depth-`n` concrete tower scheduler witnessing
`weakTau sys (E.end) (macroFuture_trunc S n E hT)`, with numerator-exposed `next`. -/
noncomputable def towerSchedC (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) : WeakScheduler sys :=
  (towerDataC S n E hT).sched

/-- **The concrete tower realizes the truncation.** -/
theorem towerSchedC_integrate (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (g : State → ENNReal) :
    (∑' e, (towerSchedC S n E hT).haltMass (E.endState hT) e * g (e.1.endState e.2))
      = ∑' s, macroFuture_trunc S n E hT s * g s :=
  (towerDataC S n E hT).integrate g

/-- **The concrete tower halts almost surely** from `E.end`. -/
theorem towerSchedC_halts (S : WeakScheduler (𝒟(sys^w)))
    (n : ℕ) (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) :
    (∑' e, (towerSchedC S n E hT).haltMass (E.endState hT) e) = 1 := by
  have h := towerSchedC_integrate S n E hT (fun _ => 1)
  simp only [mul_one] at h
  rw [h, (macroFuture_trunc S n E hT).tsum_coe]

/-! ### Numerator exposure of the concrete tower (S3)

The unnormalized weights of `towerSchedC S n E hT |>.next e`: the joint (path-measure ×
belief) mass `twNum S n E hT e o = twDenom · next e o`, where `twDenom` is the composite
path measure `probOf e`. Because each layer of the concrete tower is a genuine
belief/`bind` scheduler, `twDenom` is a bona-fide sub-probability (`≤ 1`, uniformly in `n`),
and `∑' o, twNum e o = twDenom e` (the belief `next e` is a PMF). These are the
`⨆`-ready per-history handles the σ\* limit consumes; the monotone end-state spine is the
existing `macroHalted`/`macroHalted_mono` (with `macroFuture_trunc = macroHalted +
macroResidual`), which `towerSchedC_integrate` realizes as the tower's halting pushforward. -/

open Classical in
/-- The exposed **denominator** (composite path measure `probOf e`) of `towerSchedC`'s
belief at a history `e` (0 off-termination). Uniformly `≤ 1` in `n`. -/
noncomputable def twDenom (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    ENNReal :=
  if h : e.trans.Terminates then
    (⟨E.endState hT, (towerSchedC S n E hT).toScheduler⟩ : ProbabilisticExecution sys).probOf e h
  else 0

/-- The exposed **numerator** of `towerSchedC S n E hT |>.next e` at emission `o`: the
unnormalized joint mass `twDenom · next e o`. -/
noncomputable def twNum (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label)
    (o : Option (Label × PMF State)) : ENNReal :=
  twDenom S n E hT e * (towerSchedC S n E hT).next e o

/-- The numerators over `o` sum to the denominator (`next e` is a PMF). -/
theorem twNum_tsum (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    (∑' o, twNum S n E hT e o) = twDenom S n E hT e := by
  unfold twNum
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- **Uniform denominator bound.** `twDenom ≤ 1` for every depth `n` (each path measure
`probOf e ≤ init ≤ 1`): a finite bound independent of `n`, as the σ\* squeeze requires. -/
theorem twDenom_le_one (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    twDenom S n E hT e ≤ 1 := by
  classical
  unfold twDenom
  split
  · exact le_trans (ProbabilisticExecution.probOf_le_init _ _ _) (PMF.coe_le_one _ _)
  · exact zero_le_one

/-- **Monotone end-state spine** (the σ\*-pushforward target). The tower's depth-`n`
halting pushforward `macroFuture_trunc` splits as `macroHalted + macroResidual`, and the
halted-within-`n` part `macroHalted` is monotone (`macroHalted_mono`) and bounded by `1`;
its `⨆ n` is the limit distribution the σ\* witness must realize. -/
theorem macroHalted_le_one (S : WeakScheduler (𝒟(sys^w))) (n : ℕ)
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s : State) :
    macroHalted S n E hT s ≤ 1 := by
  calc macroHalted S n E hT s
      ≤ macroHalted S n E hT s + macroResidual S n E hT s := le_self_add
    _ = macroFuture_trunc S n E hT s := (macroFuture_trunc_decompose S n E hT s).symm
    _ ≤ 1 := (macroFuture_trunc S n E hT).coe_le_one s

/-! ### v5 Layer 1 — the cylinder mass `cylP` (the monotone cylinder limit)

For a fixed observable history `e`, the composite path measure `twDenom S n E hT e = probOf_n(e)`
is monotone non-decreasing in the tower depth `n` (paper verdict F5a): deepening the tower
only lets the `oneDecisionC`-halt-then-continue branch realize deeper cylinders (adding reach
mass), while already-reachable cylinders keep their (`n`-independent) belief weight — the
`beliefSched_probOf` normalizers cancel pointwise, so `probOf e = bDenom e` is an *unnormalized*
config-sum. `cylP e := ⨆ n, twDenom S n E hT e` is the resulting cylinder limit. -/

/-- **Cylinder mass at history `e`** for the depth-`n` concrete tower rooted at `(E, hT)`:
the `⨆ n` of the composite path measure `twDenom S n E hT e = probOf_n(e)`. Layer 1 of the
v5 cylinder-ratio scheduler. -/
noncomputable def cylP (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    ENNReal :=
  ⨆ n, twDenom S n E hT e

/-- `cylP ≤ 1` (uniform `twDenom_le_one` under the `⨆`). -/
theorem cylP_le_one (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (e : AlterSeq State Label) :
    cylP S E hT e ≤ 1 :=
  iSup_le (fun n => twDenom_le_one S n E hT e)

/-- **Base value (telescope root).** At the empty concrete history `⟨s₀, nil⟩` the tower path
measure is the source mass `(E.endState hT) s₀`, `n`-independent, so `cylP = (E.endState hT) s₀`. -/
theorem cylP_root (S : WeakScheduler (𝒟(sys^w)))
    (E : AlterSeq (PMF State) Label) (hT : E.trans.Terminates) (s₀ : State) :
    cylP S E hT ⟨s₀, Seq.nil⟩ = (E.endState hT) s₀ := by
  have hconst : ∀ n, twDenom S n E hT ⟨s₀, Seq.nil⟩ = (E.endState hT) s₀ := by
    intro n
    unfold twDenom
    rw [dif_pos Stream'.Seq.terminates_nil]
    simp only [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
  unfold cylP
  simp only [hconst, iSup_const]

/-! ### σ\* limit-witness frontier — paper assessment (both routes vs. the current stack)

Goal: a single `σ* : WeakScheduler sys`, a.s.-halting from `μ`, with pushforward
`Ν.bind id`. The pushforward TARGET is now pinned as a monotone limit:
`macroHalt_bind_id_eq_iSup` gives `(Ν.bind id) s = ⨆ n, ∑ k ∈ range n, macroHaltDepth S μ k s`,
and `macroHalted_iSup_eq_one` gives its `∑' s`-summed value `= 1` under a.s.-halting.
Both are `[propext, Classical.choice, Quot.sound]`. Since `Ν.bind id` and any a.s.-halting
`σ*`-pushforward are both PMFs (total `1`), the squeeze collapses `≥` to `=`: it SUFFICES to
exhibit `σ*` a.s.-halting whose pushforward dominates `⨆ n, ∑ k<n, macroHaltDepth` pointwise.

The classical-tower verdicts below are now SUPERSEDED by the concrete-tower assessment
(`towerSchedC`, numerator-exposed). Both routes remain BLOCKED, now for sharper, recorded
reasons; numerator exposure is necessary scaffolding but insufficient.

* **Route A (monotone limit of tower numerators) — CONCRETE-TOWER VERDICT: BLOCKED.**
  `towerSchedC` removes the old "opaque `next`" objection: `twNum`/`twDenom` and the
  pointwise `beliefSched_probOf` (`probOf e = bDenom e = ∑' x, wt x · bBranchProb x e`)
  expose every layer. Numerator exposure still does NOT enable `⨆ n`, for two independent
  reasons.
    (i) STALLS PERSIST. The move-branch `odFam (some (_, ω)) = innerWitness sys (E.end) ω`
        can halt on an EMPTY run (`iwHaltMass > 0`, the `stallPart`/`stallSum` object), so a
        macro-`some` step appends 0 sys-transitions. Hence the observed history `e` does NOT
        determine the hidden macro-config (its stall-depth is unbounded at fixed `e`), and
        `(towerSchedC S n E hT).next e` does NOT stabilize in `n`: a deeper tower routes
        extra stall-paths through the SAME `e`.
    (ii) PER-HISTORY MASS IS NON-MONOTONE (F4s). `twNum`/`twDenom` at fixed `(e, o)` are not
        monotone in `n` (deeper towers reroute mass from forced-halt-at-`e` to continue-past-
        `e`), so no monotone `⨆`/limit of the belief `next e` exists to take; `twNum/twDenom`
        neither stabilizes nor converges monotonically.
  The ONLY monotone object is the END-STATE spine `macroHalted` (`macroHalted_mono`), which
  lives at the whole-scheduler PUSHFORWARD level — `towerSchedC_integrate` realizes
  `macroFuture_trunc S n = macroHalted + macroResidual` — NOT at the per-history `next` a
  scheduler definition needs. `⨆ n, macroHalted S n = Ν.bind id` is the pinned target
  (`macroHalt_bind_id_eq_iSup`), but there is no `next`-limit realizing it.
* **Route B (diagonal `σ*.next e := towerSchedC S (|e|+1) root |>.next e`) — CONCRETE-TOWER
  VERDICT: BLOCKED.** Stepwise consistency `next_{|e|+1}(e) = next_{|e|+2}(e)` FAILS by (i):
  the extra macro-layer of depth `|e|+2` feeds stall-paths into the same `e`. The diagonal's
  `probOf e` is a product over prefixes `eⱼ` each using a DIFFERENT tower depth `|eⱼ|+1`;
  `beliefSched_probOf` shapes each factor as a `bDenom`, but consecutive factors belong to
  distinct schedulers and telescope into no single `probOf` — not measure-correct, the
  recorded stall-hidden-depth failure, unchanged by concreteness.
* **Domination-inequality reframing (only `pushforward(σ*) ≥ ⨆ n macroHalted` needed) — does
  NOT dodge the construction.** The honest never-truncating belief process pushes forward to
  exactly `∑ k macroHaltDepth = Ν.bind id`, so it would dominate; but STATING its pushforward
  still requires DEFINING `σ*`, whose `next` is the belief posterior over the INFINITE hidden-
  config (all stall-depths) space — precisely the missing `next`-limit. A convex mixture
  `beliefSched {towerSchedC S n} wt` pushes forward to `∑ n wt n · macroFuture_trunc S n`,
  which averages BELOW the sup (residual noise), so it fails to dominate. No fixed finite or
  mixture candidate on the current stack dominates.
* **Old dSched route:** blocked on the unlanded `probOf_beliefMass` (audit at `d_integrate_step`).
* **Domination on `dSched` (sub-family lower bound, no normalizer cancellation) — REFUTED
  (crux killed by the normalizer sign).** Plan: bound the pushforward `P s := ∑' e,
  dSched.haltMass e · [end e = s]` below by the raw macro×inner config joint masses
  (= `∑ k macroHaltDepth = Ν.bind id`), then squeeze against `∑' s P s ≤ 1` (Kraft,
  `haltMass_tsum_le_one`) to force `P = Ν.bind id`. The chain is
  `haltMass e = probOf e · next e none`, `probOf e = ∏ⱼ next eⱼ stepⱼ`, and each
  `next e o = dNum/dDenom ≥ single-config-summand / dDenom`, so
  `haltMass e ≥ RawMass(τ) / ∏ⱼ dDenom(eⱼ)` per coherent config-trajectory `τ`. Reaching
  `≥ RawMass(τ)` (needed for the strata) requires `∏ⱼ dDenom(eⱼ) ≤ 1`, i.e. `dDenom ≤ 1`
  pointwise. **This FAILS for v3 `dSched`.** `dDenom` is a belief-mass sum over ALL nonempty
  segmentations of `e` (`dDenom_eq_moveTot`/`dDenom_eq_dW`), and `dW_le` bounds it only by
  `|e|+1`, NOT `1`; it genuinely exceeds `1` (≈`|e|` disjoint segmentation "explanations",
  each up to `moveTot ≤ 1`, ADD). There is no `dDenom ≤ 1` lemma and none is provable — the
  `≤ 1` normalizers in the file are all SINGLE-layer/tower objects (`odDenom_le_one`,
  `bDenom_le_one`, `twDenom_le_one`), never the multi-segmentation belief sum. With
  `dDenom > 1`, dividing DEFLATES: `next e o < single-summand`, `∏ⱼ dDenom(eⱼ)` grows with
  `|τ|`, and `RawMass/∏dDenom → 0` relative to `RawMass`. The normalizers HURT, not help
  (the hoped-for "positivity makes sub-family sums lower bounds with no cancellation" is real,
  but the cancellation it dodges is replaced by an ever-growing `∏dDenom` denominator that is
  strictly worse). No per-state `condDepthG` variant is reached — the crux dies before strata.
  Tower fallback (`twDenom ≤ 1` IS landed) does NOT rescue it: `towerSchedC` is a DIFFERENT
  scheduler per `n` (its `next` ≠ `dSched.next`; larger `dDenom` makes `dSched.haltMass`
  potentially SMALLER than tower raw masses — domination points the wrong way), and its
  pushforward `macroFuture_trunc n = macroHalted n + macroResidual n` carries non-vanishing
  force-halt residual junk (Route A, already blocked: no monotone `next`-limit). No landed
  handle relates `dSched.haltMass` to tower raw masses; building one is the missing large
  construction, not a wiring step. VERDICT: dead — same root cause as Routes A/B/mixture. -/
/- (frontier note continues) -/
/-! ### σ\* limit-witness frontier — (assessment continues below)

Net (concrete-tower confirmation): the last `sorry` needs a genuine `WeakScheduler`-LIMIT
combinator, or an honest corecursive belief scheduler over the infinite hidden-config space
with a convergence proof for its belief posteriors — a large new construction, not a wiring
step. The numerator-exposed tower (`towerSchedC`, `beliefSched_probOf`, `twNum`/`twDenom`) is
necessary scaffolding that exposes the layers whose LIMIT is the open frontier. The target
`Ν.bind id = ⨆ n macroHalted` and its mass-`1` companion (`macroHalted_iSup_eq_one`) remain
landed and axiom-clean. -/

/-- **V1 — the one-step integrate recursion (rooted).** Integrating `g` against
the composite's halting end-states unfolds one macro level: either the macro
scheduler halts now (mass `S.next E none`, end-state distributed as the current
source `μ0`), or it takes a macro-emission `ω` and successor `m'`, whereupon the
integral recurses at the advanced configuration `(m', macroExtend E m')`.

### v4 FRONTIER UPDATE (supersedes the AUDIT / PHASE-P verdict below)

The PHASE-P verdict concludes "no route closes on the current landed stack alone"
and isolates a missing bridge `probOf_beliefMass`. That conclusion is correct ONLY
for the *belief-normalized* `dSched` witness. It is now SUPERSEDED by the v4 plan,
whose enabling primitive already exists sorry-free elsewhere in the repository:

  `Scheduler.bind_compose_integrate`  (`Leslie2/Weak/WeakTransition.lean`)
    `∑' e, (bind σ k).haltMass μ e · g(e.end)`
      `= ∑' f₁, σ.haltMass μ f₁ · ∑' f₂, (k f₁.end).haltMass (pure f₁.end) f₂ · g(f₂.end)`
  (and its whole-execution generalization `bind_compose_integrate_gen`, the
  `WeakScheduler.concat` split↔pair reindexing, already consumed by `weakTau_trans`).

This is exactly the "compositionality built in" the DESIGN doc asked for; it is a
LANDED lemma, so the PHASE-P premise ("not among the landed lemmas") is false for
the v4 route. Since the downstream of `d_integrate_step` (`dHalt_ge`, `d_halts`,
`dHalt_ge_G`, `d_pushforward`, `weakTau_flatten`) references the witness ONLY through
`dSched _.haltMass` / `dHM`, the re-route is minimal-churn: KEEP the `dHM` definition
and every downstream lemma verbatim, REDEFINE `dSched` as the v4 bind-recursive
witness, and re-prove THIS lemma via one application of `bind_compose_integrate`.

REMAINING CONSTRUCTION (the genuine work, not yet landed):
  (1) `oneDecision S μ0 E : WeakScheduler sys` — from source `μ0 = E.end`, the
      mixture that with mass `S.next E none` halts immediately (→ term A), and with
      mass `S.next E (τ,ω)` runs `innerWitness sys μ0 ω` to its halt (→ one segment).
      Build the mixture-of-inner-witnesses as a genuine `WeakScheduler` (valid /
      internal_only); the stall series is resummed ONCE here via `stall_unfold` +
      `tsum_iSup_of_monotone`. Its local integrate identity gives term A and the
      `∑'ω S.next E(τ,ω) · [ω-routed segment integral]` shell.
  (2) the posterior continuation kernel `k : State → WeakScheduler sys` mixing the
      recursive `dSched S m' (macroExtend E m')` weighted by the single-layer
      posterior over `(ω,m')` (normalizer ≤ 1, no stall accumulation — `ne_top`
      trivial), fed to `WeakScheduler.bind (oneDecision …) k`.
  (3) `dSched` by strong recursion on observed-history length (`e.trans.length`):
      each non-halt layer consumes ≥ 1 sys-step, so `dSched.next e` is the depth-
      `(|e|+1)` truncated bind tower; prove the tower value at `e` stabilizes for
      depth > `|e|`. Then `d_integrate_step` = `bind_compose_integrate` applied once
      + `oneDecision`'s local identity + the posterior marginalization.

Everything below is the belief-normalized (v3) study, retained as documentation of
why the pointwise posterior route is unreachable; it is not on the v4 critical path.

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
