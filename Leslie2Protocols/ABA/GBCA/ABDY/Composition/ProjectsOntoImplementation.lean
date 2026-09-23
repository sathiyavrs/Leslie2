/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Composition.StepInversion

/-!
# The round instance projects onto the implementation

The round instance and the round-`r` implementation instance (`GBCA/ABDY/Implementation.lean`) run
on the same state: `GBCA.ByABDY.ImplementationState` is the pair of the round records and the
network state, which are exactly the local states the round instance composes.
`composition_projects` says that every transition of the round instance is a transition of the
implementation at that same state, one step for one step, with no stuttering: a joint call is the
implementation's call, a hidden multicast or delivery is the protocol rule or the delivery it
carries, a network injection is the implementation's Byzantine row. The two are one round under two
presentations: a single case list, and `n` programs beside a network. The projection is the strong
and functional first step of `instanceSubstitution`.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation Composition

/-! ### The round instance projects onto the implementation

Every rule of the round instance is one rule of the round-`r` implementation at
the same state, and the correspondence is strong — one step answers one step,
at the specification label the interface label projects to, with no stuttering
anywhere:

| round instance | implementation |
| --- | --- |
| `callG` (caller writes, network records) | `ImplementationStep.call` |
| `gbcaCallLoop`, `byzantineCallGLoop` | `ImplementationStep.callLoop` |
| `byzantineCallG` (D11) | `ImplementationStep.call` |
| `retG` / `byzantineRetG`, by grade | `ImplementationStep.retGrade2` / `retGrade1` / `retGrade0` |
| hidden `send` rendezvous, by level | the eight protocol `τ` rules |
| hidden `deliver` rendezvous | `ImplementationStep.deliver` |
| network-local injection | `ImplementationStep.byzantine` |

The two hidden rendezvous and the network's injection are silent in both systems, and `gbcaLabelMap`
takes `τ` to `τ`. -/

/-- **The strong projection lemma.** -/
theorem composition_projects (P : Parameters) (r : ℕ) :
    ∀ (σ : GBCA.ByABDY.ImplementationState P.n) (l : ExtendedLabel P.n)
    (μ : PMF (GBCA.ByABDY.ImplementationState P.n)), (composition P r).step σ l μ → ∃ l₀,
    gbcaLabelMap P.n l = some l₀ ∧ (GBCA.ByABDY.implementation P r).step σ l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (composition_step_iff P r (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden rendezvous: an internal step of the implementation
    obtain ⟨x, w', rfl, hall, hn⟩ := compositionExtended_joint_inversion (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (gbcaProgramStep_send_foreign (Ne.symm hi) (hall i))
      have hw : w' = w.recordGBCASend j m := PMF.pure_injective (gbcaNetworkStep_send hn)
      subst hw
      cases m with
      | input b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_input_own (hall j)
        rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
        exact GBCA.ByABDY.ImplementationStep.relay _ j b hin hcnt hsend
      | echo b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_echo_own (hall j)
        rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
        exact GBCA.ByABDY.ImplementationStep.echo _ j b hin hcnt hsend
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_voteBit_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.voteBit _ j b hin hcnt hsend
        | none =>
          obtain ⟨hin, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_voteBot_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.voteBot _ j hin hnot hcnt hval hsend
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨hin, hlv, hcnt, hsend, hx⟩ := gbcaProgramStep_send_bindBit_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.bindBit _ j b hin hlv hcnt hsend
        | none =>
          obtain ⟨hin, hlv, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_bindBot_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.bindBot _ j hin hlv hnot hcnt hval hsend
      | «echo5» v =>
        cases v with
        | some b =>
          obtain ⟨hin, hlv, hcnt, hsend, hx⟩ := gbcaProgramStep_send_echo5Bit_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.echo5Bit _ j b hin hlv hcnt hsend
        | none =>
          obtain ⟨hin, hlv, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_echo5Bot_own (hall j)
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.echo5Bot _ j hin hlv hnot hcnt hval hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := gbcaNetworkStep_deliver hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (gbcaProgramStep_deliver_foreign (Ne.symm hi') (hall i'))
      rw [composition_deliver (PMF.pure_injective (gbcaProgramStep_deliver_own (hall i))) hfor]
      exact GBCA.ByABDY.ImplementationStep.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Label.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := compositionExtended_tau_inversion hlab
      obtain ⟨k, m, hF, hw⟩ := gbcaNetworkStep_tau hn
      have hw' : w' = w.recordGBCASend k m := PMF.pure_injective hw
      subst hw'
      refine ⟨Label.tau, rfl, ?_⟩
      rw [composition_recordGBCASend]
      exact GBCA.ByABDY.ImplementationStep.byzantine _ k m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ := compositionExtended_joint_inversion (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (gbcaNetworkStep_callABA_noStep hn).elim
        | retABA id b => exact (gbcaNetworkStep_retABA_noStep hn).elim
        | callW r' id => exact (gbcaNetworkStep_callW_noStep hn).elim
        | retW r' id b => exact (gbcaNetworkStep_retW_noStep hn).elim
        | fail k => exact (gbcaNetworkStep_fail_noStep hn).elim
        | callG r' id b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_callG_round hn
          have hw' : w' = w.recordGBCASend id (.input b) := PMF.pure_injective hw
          subst hw'
          obtain ⟨hin, hx⟩ := gbcaProgramStep_callG_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_callG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.call _ id b hin
        | retG r' id out bnd =>
          obtain ⟨rfl, hbnd, hw⟩ := gbcaNetworkStep_retG_round hn
          have hw' : w' = w.setBound bnd := PMF.pure_injective hw
          subst hw'
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_retG_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | grade2 v =>
            obtain ⟨hin, hlv, hcnt, hret, hx⟩ := gbcaProgramStep_retGGrade2_own (hall id)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade2 _ id v bnd hin hlv hcnt hret hbnd
          | grade1 v =>
            obtain ⟨hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hx⟩ :=
              gbcaProgramStep_retGGrade1_own (hall id)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade1 _ id v bnd hin hlv hnotGrade2 hcnt honce
              hbind hval
              hret hbnd
          | grade0 =>
            obtain ⟨hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hx⟩ :=
              gbcaProgramStep_retGGrade0_own (hall id)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade0 _ id bnd hin hlv hnotGrade2 hnotGrade1
              hcnt hval hret
              hbnd
      | inr ev =>
        cases ev with
        | gbcaSend r' j m => exact (gbcaNetworkStep_gbcaSend_noStep hn).elim
        | gbcaDeliver r' i j m => exact (gbcaNetworkStep_gbcaDeliver_noStep hn).elim
        | decidedSend j b => exact (gbcaNetworkStep_decidedSend_noStep hn).elim
        | decidedDeliver i j b => exact (gbcaNetworkStep_decidedDeliver_noStep hn).elim
        | retWPublish r' id c b => exact (gbcaNetworkStep_retWPublish_noStep hn).elim
        | byzantineCallW r' k => exact (gbcaNetworkStep_byzantineCallW_noStep hn).elim
        | byzantineRetW r' k b => exact (gbcaNetworkStep_byzantineRetW_noStep hn).elim
        | gbcaCallLoop r' id b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_gbcaCallLoop_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          have hidle : ∀ i,
            x i = u i := fun i => PMF.pure_injective (gbcaProgramStep_gbcaCallLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_idle hidle]
          exact GBCA.ByABDY.ImplementationStep.callLoop _ id b
        | byzantineCallG r' k b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_byzantineCallG_round hn
          have hw' : w' = w.recordGBCASend k (.input b) := PMF.pure_injective hw
          subst hw'
          obtain ⟨hin, hx⟩ := gbcaProgramStep_byzantineCallG_own (hall k)
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_byzantineCallG_foreign (Ne.symm hi)
              (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_setProcess_recordGBCASend (PMF.pure_injective hx) hfor]
          exact GBCA.ByABDY.ImplementationStep.call _ k b hin
        | byzantineCallGLoop r' k b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_byzantineCallGLoop_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          have hidle : ∀ i, x i = u i :=
            fun i => PMF.pure_injective (gbcaProgramStep_byzantineCallGLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_idle hidle]
          exact GBCA.ByABDY.ImplementationStep.callLoop _ k b
        | byzantineRetG r' k out bnd =>
          obtain ⟨rfl, hbnd, hw⟩ := gbcaNetworkStep_byzantineRetG_round hn
          have hw' : w' = w.setBound bnd := PMF.pure_injective hw
          subst hw'
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_byzantineRetG_foreign (Ne.symm hi) (hall
              i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | grade2 v =>
            obtain ⟨hin, hlv, hcnt, hret, hx⟩ := gbcaProgramStep_byzantineRetGGrade2_own (hall k)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade2 _ k v bnd hin hlv hcnt hret hbnd
          | grade1 v =>
            obtain ⟨hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hx⟩ :=
              gbcaProgramStep_byzantineRetGGrade1_own (hall k)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade1 _ k v bnd hin hlv hnotGrade2 hcnt honce
              hbind hval
              hret hbnd
          | grade0 =>
            obtain ⟨hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hx⟩ :=
              gbcaProgramStep_byzantineRetGGrade0_own (hall k)
            rw [composition_setProcess_setBound (PMF.pure_injective hx) hfor]
            exact GBCA.ByABDY.ImplementationStep.retGrade0 _ k bnd hin hlv hnotGrade2 hnotGrade1
              hcnt hval hret
              hbnd

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.composition_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composition_projects

end GBCA.ByABDY
end ABA
end PLTS
