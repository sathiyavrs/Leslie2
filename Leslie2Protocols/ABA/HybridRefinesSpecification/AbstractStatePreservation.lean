/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation

/-!
# The core simulation's stutter transitions: `AbstractState` preservation, and the assembly

Stage C of the proof that `hybridSpecificationStateRelation` is a simulation relation, and the
assembly of Stages A–C.

* **Stage C** — `AbstractState` preservation for the stutter transitions. The abstract state is
  untouched by every hidden transition and moves only at the visible ones
  (`callABA`/`retABA`/`fail`, handled in `HybridRefinesSpecification/Simulation.lean`). The
  lemmas are instances of one argument about a write elsewhere, `AbstractState.unchangedBy`, and a
  transition that leaves the state as it stands preserves it outright.
* **Assembly** — `Invariant.step`: `Invariant` is preserved by every `hybrid` step, dispatching on
  the label class through Stage A's step-case lemmas and calling the matching Stage B lemma
  (`HybridRefinesSpecification/InvariantPreservation/`) in each case. `AbstractState.step_tau`:
  `AbstractState` is preserved, at the same abstract state, by every silent `hybrid` step.

Both predicates read the two families through their accessors. A round's write
`setInstanceState r x` reads as `Function.update` at `r`
(`InstanceFamilyState.instanceState_setInstanceState`), the corruption broadcast as the corruption
of every round (`GBCA.instanceState_applyBroadcast_fail`, `WCC.instanceState_applyBroadcast_fail`),
and the started rounds a correct call writes are read by neither (`Invariant.recordStartedRound`,
`AbstractState.recordStartedRound`).
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]


/-! ### Stage C: `AbstractState` preservation for the stutter transitions

Every one of `hybrid_step_tau`'s nine sources is matched by a stutter: the abstract state is
untouched by every hidden transition and only moves at the visible ones
(`callABA`/`retABA`/`fail`), handled in `HybridRefinesSpecification/Simulation.lean`. The lemmas
below are instances of a single argument about a write elsewhere: `AbstractState` inspects only
`F`, the per-process `input`/`returned` projections, and the grade-2 witnesses on `g`, and each
transition preserves all three. -/

/-- `AbstractState` transfers along any write that preserves `F`, the per-process
`input`/`returned` projections, and the grade-2 witness and holder universal. -/
theorem AbstractState.unchangedBy {P : Parameters} {g g' : ℕ → GBCA.SpecState P.n}
    {c c' : ABAState P} {w w' : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hF : c'.F = c.F)
    (hin : ∀ id, (c'.processes id).input = (c.processes id).input)
    (hret : ∀ id, (c'.processes id).returned = (c.processes id).returned)
    (hAF : AbstractStateUnchanged P g g' c c') : AbstractState P g' c' w' a := by
  refine ⟨hA.F_eq.trans hF.symm, fun id => (hA.ret_eq id).trans (hret id).symm,
    hA.mode_flipEnabled,
    fun id hid => (hA.input_sync id (by rw [← hF]; exact hid)).trans (hin id).symm, ?_⟩
  rcases hA.phase with hv | ⟨v, hv, ⟨r, hcv⟩, hpin⟩
  · exact Or.inl hv
  · exact Or.inr ⟨v, hv, hAF.1 r v hcv, hAF.2 v ⟨r, hcv⟩ hpin⟩

/-- `bindUnset`: stutters; the transition's `AbstractStateUnchanged` package carries the
witnesses. -/
theorem AbstractState.step_gbcaTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : AbstractState P g c w a)
    (hI : Invariant P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    AbstractState P (Function.update g r gr') c w a :=
  hA.unchangedBy rfl (fun _ => rfl) (fun _ => rfl) (Invariant.step_gbcaTau hI r hstep hgr').2

/-- A DECIDED message of the projection (delivery, relay, injection): stutters; `F` and
`processes` untouched. -/
theorem AbstractState.step_roundLoopTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : AbstractState P g c w a)
    (hI : Invariant P g c w) {μc : PMF (ABAState P)}
    (hstep :
      (∃ i j b, b ∈ c.decidedSent j ∧ b ∉ c.decidedReceived i j ∧
          μc = PMF.pure (c.deliverDecided i j b)) ∨
        (∃ id b, P.f + 1 ≤ c.decidedCount id b ∧ b ∉ c.decidedSent id ∧
          μc = PMF.pure (c.relayDecided id b)) ∨
        (∃ id b, id ∈ c.F ∧ μc = PMF.pure (c.recordDecided id b)))
    {c' : ABAState P} (hc' : c' ∈ μc.support) : AbstractState P g c' w a := by
  have hAF := (Invariant.step_roundLoopTau hI hstep hc').2
  have hCUnchanged : c'.F = c.F ∧ c'.processes = c.processes := by
    rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · exact ⟨ABAState.deliverDecided_F _ _ _ _, ABAState.deliverDecided_processes _ _ _ _⟩
    · exact ⟨ABAState.relayDecided_F _ _ _, ABAState.relayDecided_processes _ _ _⟩
    · exact ⟨ABAState.recordDecided_F _ _ _, ABAState.recordDecided_processes _ _ _⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id => by rw [hCUnchanged.2])
    (fun id => by rw [hCUnchanged.2]) hAF

/-- A write of the control variables of one process that keeps its `input` and `returned`, or no
write, leaves `F` and the `input` and `returned` projections unchanged. -/
private theorem setProcessVariables_unchanged {P : Parameters} {c c' : ABAState P}
    {id : Fin P.n} {p : RoundLoopState P.n} (hp : p.input = (c.processes id).input ∧
      p.returned = (c.processes id).returned)
    (h : c' = c.setProcessVariables id p ∨ c' = c) :
    c'.F = c.F ∧ ∀ id', (c'.processes id').input = (c.processes id').input ∧
      (c'.processes id').returned = (c.processes id').returned := by
  rcases h with rfl | rfl
  · refine ⟨ABAState.setProcessVariables_F _ _ _, fun id' => ?_⟩
    by_cases h : id' = id
    · subst h; rw [ABAState.setProcessVariables_processes_self]; exact hp
    · rw [ABAState.setProcessVariables_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
  · exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- `callG`: stutters; `AbstractState` reads none of the touched fields, and the witnesses are
carried by the transition's `AbstractStateUnchanged`. -/
theorem AbstractState.step_callG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .toCallG ∧ (c.processes id).round = r ∧
          (c.processes id).estimate = some b ∧
          μc = PMF.pure (c.setProcessVariables id { c.processes id with phase := .awaitG })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    AbstractState P (Function.update g r gr') c' w a := by
  have hAF := (Invariant.step_callG hI r id b hstepG hstepC hgr' hc').2
  have hC := setProcessVariables_unchanged (c' := c') (id := id)
    (p := { c.processes id with phase := .awaitG }) ⟨rfl, rfl⟩ (by
      rcases hstepC with ⟨-, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rw [PMF.mem_support_pure_iff] at hc'
      · exact Or.inl hc'
      · exact Or.inr hc')
  exact hA.unchangedBy hC.1 (fun id' => (hC.2 id').1) (fun id' => (hC.2 id').2) hAF

/-- `retG`: stutters; the witnesses and the holder universal are carried by the transition's
`AbstractStateUnchanged`. The round loop takes the return on `retG` at the phase and round it
waits for, and on its loop or its self-loop elsewhere. -/
theorem AbstractState.step_retG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    (out : GBCAOutput)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitG ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcessVariables id { c.processes id with
            estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
        ((id ∈ c.F ∨ ¬((c.processes id).phase = .awaitG ∧ (c.processes id).round = r)) ∧
          μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    AbstractState P (Function.update g r gr') c' w a := by
  have hAF := (Invariant.step_retG hI r id out hstepG hstepC hgr' hc').2
  have hC := setProcessVariables_unchanged (c' := c') (id := id)
    (p := { c.processes id with
      estimate := out.estimate, lastGrade := some out, phase := .toCallW }) ⟨rfl, rfl⟩ (by
      rcases hstepC with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rw [PMF.mem_support_pure_iff] at hc'
      · exact Or.inl hc'
      · exact Or.inr hc')
  exact hA.unchangedBy hC.1 (fun id' => (hC.2 id').1) (fun id' => (hC.2 id').2) hAF

/-- `callW`: stutters. -/
theorem AbstractState.step_callW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcessVariables id { c.processes id with phase := .awaitW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    AbstractState P g c' (Function.update w r wr') a := by
  have hAF := (Invariant.step_callW hI r id hstepW hstepC hwr' hc').2
  have hC := setProcessVariables_unchanged (c' := c') (id := id)
    (p := { c.processes id with phase := .awaitW }) ⟨rfl, rfl⟩ (by
      rcases hstepC with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rw [PMF.mem_support_pure_iff] at hc'
      · exact Or.inl hc'
      · exact Or.inr hc')
  exact hA.unchangedBy hC.1 (fun id' => (hC.2 id').1) (fun id' => (hC.2 id').2) hAF

/-- `retW`: stutters. The round loop takes the return on `retW` at the phase and round it waits
for, and on its loop or its self-loop elsewhere. -/
theorem AbstractState.step_retW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.stepRound id b)) ∨
        ((id ∈ c.F ∨ ¬((c.processes id).phase = .awaitW ∧ (c.processes id).round = r)) ∧
          μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    AbstractState P g c' (Function.update w r wr') a := by
  have hAF := (Invariant.step_retW hI r id b hstepW hstepC hwr' hc').2
  have hCUnchanged : c'.F = c.F ∧ ∀ id', (c'.processes id').input = (c.processes id').input ∧
      (c'.processes id').returned = (c.processes id').returned := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨-, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨ABAState.stepRound_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h
        exact ⟨ABAState.stepRound_processes_self_input _ _ _,
          ABAState.stepRound_processes_self_returned _ _ _⟩
      · rw [ABAState.stepRound_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id' => (hCUnchanged.2 id').1)
    (fun id' => (hCUnchanged.2 id').2) hAF

/-- The DECIDED send of a grade-2 round: stutters. -/
theorem AbstractState.step_decidedSend {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (id : Fin P.n) (b : Bool)
    (hph : (c.processes id).phase = .toSendDecided)
    (hlg : (c.processes id).lastGrade = some (.grade2 b)) :
    AbstractState P g (c.sendDecidedOnGrade2 id b) w a := by
  have hAF := (Invariant.step_decidedSend hI id b hph hlg).2
  have hCUnchanged : ∀ id', ((c.sendDecidedOnGrade2 id b).processes id').input =
      (c.processes id').input ∧
      ((c.sendDecidedOnGrade2 id b).processes id').returned = (c.processes id').returned := by
    intro id'
    by_cases h : id' = id
    · subst h; rw [ABAState.sendDecidedOnGrade2_processes_self]; exact ⟨rfl, rfl⟩
    · rw [ABAState.sendDecidedOnGrade2_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
  exact hA.unchangedBy (ABAState.sendDecidedOnGrade2_F _ _ _) (fun id' => (hCUnchanged id').1)
    (fun id' => (hCUnchanged id').2) hAF

/-- The coin's resolution: stutters. The resolution writes the coin instance of one round alone,
which `AbstractState` does not read, and leaves `g`, the round loops and the ABA network
unchanged. -/
theorem AbstractState.step_resolve {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (r : ℕ) (wr' : WCC.SpecState P.n) :
    AbstractState P g c (Function.update w r wr') a :=
  hA.unchangedBy rfl (fun _ => rfl) (fun _ => rfl) (AbstractStateUnchanged.refl P g c)

/-! ### Assembly: `Invariant` is preserved by every `hybrid` step -/

/-- Reading a transition where the ABA component moves alone: its own outcome, the common coin
unchanged. -/
theorem mem_support_abaTransition {P : Parameters} {σ : Type} {μc : PMF (ABAState P)} {o w' : σ}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    (h : (C', A', w') ∈ (μc.map fun c => (c.1, c.2, o)).support) :
    (C', A') ∈ μc.support ∧ w' = o := by
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨⟨c1, c2⟩, hc, heq⟩ := h
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨hc, rfl⟩

/-- Reading a graded-agreement call: the ABA component's outcome, the network recording the
round's start, the common coin unchanged. -/
theorem mem_support_startedRoundTransition {P : Parameters} {σ : Type} {μc : PMF (ABAState P)}
    {o w' : σ} {r : ℕ} {id : Fin P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    (h : (C', A', w') ∈ (μc.map fun c => (c.1, c.2.recordStartedRound r id, o)).support) :
    ∃ c ∈ μc.support, C' = c.1 ∧ A' = c.2.recordStartedRound r id ∧ w' = o := by
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨c, hc, heq⟩ := h
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  exact ⟨c, hc, heq.1.symm, heq.2.1.symm, heq.2.2.symm⟩

/-- Reading a transition where the ABA component and the common coin move together. -/
theorem mem_support_coinTransition {P : Parameters} {μc : PMF (ABAState P)}
    {μw' : PMF (WCC.SpecState P.n)}
    {o w' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {r : ℕ}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    (h : (C', A', w') ∈ (μc.bind fun c => prodPMF (PMF.pure c.1)
      (prodPMF (PMF.pure c.2) (μw'.map (o.setInstanceState r)))).support) :
    (C', A') ∈ μc.support ∧ ∃ wr' ∈ μw'.support, w' = o.setInstanceState r wr' := by
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨c1, c2⟩, hc, hmem⟩ := h
  simp only [mem_support_prodPMF, PMF.mem_support_pure_iff, PMF.mem_support_map_iff] at hmem
  obtain ⟨rfl, rfl, wr', hwr', heq⟩ := hmem
  exact ⟨hc, wr', hwr', heq.symm⟩

omit [DecidableEq M] in
/-- Reading a transition where the common coin moves alone: the specification family, the round
loops and the ABA network unchanged, the coin instance of round `r` drawn from its own outcome. -/
theorem mem_support_coinResolution {P : Parameters} {G g' : GBCASpecificationFamilyState P M}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    {μw : PMF (WCC.SpecState P.n)}
    {o w' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {r : ℕ}
    (h : (g', C', A', w') ∈ (prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
      (prodPMF (PMF.pure A) (μw.map (o.setInstanceState r))))).support) :
    g' = G ∧ C' = C ∧ A' = A ∧ ∃ wr' ∈ μw.support, w' = o.setInstanceState r wr' := by
  simp only [mem_support_prodPMF, PMF.mem_support_pure_iff, PMF.mem_support_map_iff] at h
  obtain ⟨rfl, rfl, rfl, wr', hwr', heq⟩ := h
  exact ⟨rfl, rfl, rfl, wr', hwr', heq.symm⟩

/-- **`Invariant` is preserved.** Dispatches on the label class via `hybrid_step_callABA`,
`hybrid_step_retABA`, `hybrid_step_fail` and `hybrid_step_tau` (Stage A), calling the matching
`Invariant.step_*` lemma (Stage B) in each case. A round's write is read through
`InstanceFamilyState.instanceState_setInstanceState`, the corruption broadcast through
`GBCA.instanceState_applyBroadcast_fail` and `WCC.instanceState_applyBroadcast_fail`, and the write
of the started rounds at a correct graded-agreement call through `Invariant.recordStartedRound`. -/
theorem Invariant.step {P : Parameters} {G : GBCASpecificationFamilyState P M}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hI : Invariant P G (C, A) o) {l : Label P.n} {μ : PMF (HybridState P M)}
    (hstep : (hybrid P M).step (G, C, A, o) l μ) {G' : GBCASpecificationFamilyState P M}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    {o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hmem : (G', C', A', o') ∈ μ.support) :
    Invariant P G' (C', A') o' := by
  cases l with
  | tau =>
    rcases hybrid_step_tau P G C A o hI.corrupted_F hI.decidedSent_recorded μ hstep with
      ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ |
      ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, out, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ |
      ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩ |
      ⟨id, b, μc, ⟨-, hph, hlg, rfl⟩, rfl⟩ |
      ⟨r, μw, hstepW, rfl⟩ | rfl
    · simp only [mem_support_prodPMF, PMF.mem_support_map_iff, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨⟨gr', hgr', rfl⟩, rfl, rfl, rfl⟩ := hmem
      rw [InstanceFamilyState.instanceState_setInstanceState]
      exact (Invariant.step_gbcaTau hI r hstepG hgr').1
    · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
      obtain ⟨rfl, h2⟩ := hmem
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
      exact (Invariant.step_roundLoopTau hI hstepC hc2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨gr', hgr', rfl⟩ := h1
      obtain ⟨c', hc', rfl, rfl, rfl⟩ := mem_support_startedRoundTransition h2
      rw [InstanceFamilyState.instanceState_setInstanceState]
      exact (Invariant.step_callG hI r id b hstepG (hstepC.imp_right fun h => ⟨h.1, h.2.2⟩)
        hgr' hc').1.recordStartedRound r id
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨gr', hgr', rfl⟩ := h1
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
      rw [InstanceFamilyState.instanceState_setInstanceState]
      exact (Invariant.step_retG hI r id out hstepG hstepC hgr' hc2).1
    · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
      obtain ⟨rfl, h2⟩ := hmem
      obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinTransition h2
      rw [InstanceFamilyState.instanceState_setInstanceState]
      exact (Invariant.step_callW hI r id hstepW (hstepC.imp_right fun h => ⟨h.1, h.2.2⟩)
        hwr' hc2).1
    · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
      obtain ⟨rfl, h2⟩ := hmem
      obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinTransition h2
      rw [InstanceFamilyState.instanceState_setInstanceState]
      exact (Invariant.step_retW hI r id b hstepW hstepC hwr' hc2).1
    · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
      obtain ⟨rfl, hs2⟩ := hmem
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition hs2
      rw [PMF.mem_support_pure_iff] at hc2
      rw [hc2]
      exact (Invariant.step_decidedSend hI id b hph hlg).1
    · obtain ⟨rfl, rfl, rfl, wr', hwr', rfl⟩ := mem_support_coinResolution hmem
      obtain ⟨hv, ht, rfl⟩ := WCC.step_tau_cases hstepW
      rw [PMF.mem_support_map_iff] at hwr'
      obtain ⟨oc, -, rfl⟩ := hwr'
      rw [InstanceFamilyState.instanceState_setInstanceState]
      exact hI.step_resolve r ht hv oc
    · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
      exact hI
  | callABA id b =>
    rw [hybrid_step_callABA P G C A o id b hI.corrupted_F] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, h2⟩ := hmem
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    exact (Invariant.step_callABA hI id b hstepC hc2).1
  | retABA id b =>
    rw [hybrid_step_retABA P G C A o id b hI.corrupted_F hI.decidedSent_recorded] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, h2⟩ := hmem
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    exact (Invariant.step_retABA hI id b hstepC hc2).1
  | fail id =>
    rw [hybrid_step_fail P G C A o id hI.corrupted_F] at hstep
    obtain ⟨hnew, hbud, rfl⟩ := hstep
    simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, h2⟩ := hmem
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    rw [PMF.mem_support_pure_iff] at hc2
    rw [hc2, GBCA.instanceState_applyBroadcast_fail, WCC.instanceState_applyBroadcast_fail]
    exact (Invariant.step_fail hI id hnew hbud).1
  | callG r id b =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.callG_mem_hiddenAPI r id b)
  | retG r id out =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.retG_mem_hiddenAPI r id out)
  | boundG r b =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.boundG_mem_hiddenAPI r b)
  | callW r id =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.callW_mem_hiddenAPI r id)
  | retW r id b =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.retW_mem_hiddenAPI r id b)

/-- **`AbstractState` is preserved by every silent step of `hybrid`**, at the same abstract state:
the abstract state stutters. Dispatches on the nine sources of `hybrid_step_tau` and calls the
matching Stage C lemma; a transition that leaves the state as it stands preserves it outright. -/
theorem AbstractState.step_tau {P : Parameters} {G : GBCASpecificationFamilyState P M}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n}
    {o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)} {a : SpecState P.n}
    (hA : AbstractState P G (C, A) o a) (hI : Invariant P G (C, A) o)
    {μ : PMF (HybridState P M)} (hstep : (hybrid P M).step (G, C, A, o) Label.tau μ)
    {G' : GBCASpecificationFamilyState P M} {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A' : ABANetworkState P.n}
    {o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
    (hmem : (G', C', A', o') ∈ μ.support) :
    AbstractState P G' (C', A') o' a := by
  rcases hybrid_step_tau P G C A o hI.corrupted_F hI.decidedSent_recorded μ hstep with
    ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ |
    ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
    ⟨r, id, out, μr, μc, hstepG, hstepC, rfl⟩ |
    ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ |
    ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩ |
    ⟨id, b, μc, ⟨-, hph, hlg, rfl⟩, rfl⟩ |
    ⟨r, μw, hstepW, rfl⟩ | rfl
  · simp only [mem_support_prodPMF, PMF.mem_support_map_iff, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    obtain ⟨⟨gr', hgr', rfl⟩, rfl, rfl, rfl⟩ := hmem
    rw [InstanceFamilyState.instanceState_setInstanceState]
    exact hA.step_gbcaTau hI r hstepG hgr'
  · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, h2⟩ := hmem
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    exact hA.step_roundLoopTau hI hstepC hc2
  · simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_map_iff] at h1
    obtain ⟨gr', hgr', rfl⟩ := h1
    obtain ⟨c', hc', rfl, rfl, rfl⟩ := mem_support_startedRoundTransition h2
    rw [InstanceFamilyState.instanceState_setInstanceState]
    exact (hA.step_callG hI r id b hstepG (hstepC.imp_right fun h => ⟨h.1, h.2.2⟩) hgr'
      hc').recordStartedRound r id
  · simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_map_iff] at h1
    obtain ⟨gr', hgr', rfl⟩ := h1
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    rw [InstanceFamilyState.instanceState_setInstanceState]
    exact hA.step_retG hI r id out hstepG hstepC hgr' hc2
  · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, h2⟩ := hmem
    obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinTransition h2
    rw [InstanceFamilyState.instanceState_setInstanceState]
    exact hA.step_callW hI r id hstepW (hstepC.imp_right fun h => ⟨h.1, h.2.2⟩) hwr' hc2
  · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, h2⟩ := hmem
    obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinTransition h2
    rw [InstanceFamilyState.instanceState_setInstanceState]
    exact hA.step_retW hI r id b hstepW hstepC hwr' hc2
  · simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, hs2⟩ := hmem
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition hs2
    rw [PMF.mem_support_pure_iff] at hc2
    rw [hc2]
    exact hA.step_decidedSend hI id b hph hlg
  · obtain ⟨rfl, rfl, rfl, wr', -, rfl⟩ := mem_support_coinResolution hmem
    rw [InstanceFamilyState.instanceState_setInstanceState]
    exact hA.step_resolve r wr'
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact hA

end ABA
end PLTS
