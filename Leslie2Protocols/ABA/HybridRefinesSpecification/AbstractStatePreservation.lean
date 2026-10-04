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
  (`callABA`/`retABA`/`fail`, handled in `HybridRefinesSpecification/Simulation.lean`). All eight
  lemmas are instances of one argument about a write elsewhere, `AbstractState.unchangedBy`.
* **Assembly** — `Invariant.step`: `Invariant` is preserved by every `hybrid` step,
  dispatching on the label class through Stage A's step-case lemmas and calling
  the matching Stage B helper (`HybridRefinesSpecification/InvariantPreservation/`) in each
  case.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]


/-! ### Stage C: `AbstractState` preservation for the stutter transitions

Every one of `hybrid_step_tau`'s eight disjuncts is matched by a stutter: the abstract state is
untouched by every hidden transition and only moves at the visible ones
(`callABA`/`retABA`/`fail`), handled in `HybridRefinesSpecification/Simulation.lean`. All eight
lemmas below are instances of a single argument about a write elsewhere: `AbstractState` inspects
only `F`, the per-process `input`/`returned` projections, and the grade-2 witnesses on
`g` — and each transition preserves all three. -/

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

/-- Core `τ` (DECIDED delivery/echo/byzantine injection): stutters; `F`/`processes` untouched. -/
theorem AbstractState.step_roundLoopTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : AbstractState P g c w a)
    (hI : Invariant P g c w) {μc : PMF (ABAState P)}
    (hstep :
      (∃ i j b, b ∈ c.decidedSent j ∧ b ∉ c.decidedReceived i j ∧ μc = PMF.pure (c.deliverDecided i
      j b)) ∨
      (∃ id b, P.f + 1 ≤ c.decidedCount id b ∧ b ∉ c.decidedSent id ∧ μc = PMF.pure (c.recordDecided
      id b)) ∨ (∃ id b, id ∈ c.F ∧ μc = PMF.pure (c.recordDecided id b)))
    {c' : ABAState P} (hc' : c' ∈ μc.support) : AbstractState P g c' w a := by
  have hAF := (Invariant.step_roundLoopTau hI hstep hc').2
  have hCUnchanged : c'.F = c.F ∧ c'.processes = c.processes := by
    rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · exact ⟨ABAState.deliverDecided_F _ _ _ _, ABAState.deliverDecided_processes _ _ _ _⟩
    · exact ⟨ABAState.recordDecided_F _ _ _, ABAState.recordDecided_processes _ _ _⟩
    · exact ⟨ABAState.recordDecided_F _ _ _, ABAState.recordDecided_processes _ _ _⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id => by rw [hCUnchanged.2]) (fun id => by rw
    [hCUnchanged.2]) hAF

/-- `callG`: stutters; `AbstractState` reads none of the touched fields, witnesses ride the
transition's `AbstractStateUnchanged`. -/
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
  have hCUnchanged : c'.F = c.F ∧ ∀ id', (c'.processes id').input = (c.processes id').input ∧
      (c'.processes id').returned = (c.processes id').returned := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨ABAState.setProcessVariables_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcessVariables_processes_self]; exact ⟨rfl, rfl⟩
      · rw [ABAState.setProcessVariables_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id' => (hCUnchanged.2 id').1) (fun id' => (hCUnchanged.2
    id').2) hAF

/-- `retG`: stutters; witnesses and the holder universal ride the transition's
`AbstractStateUnchanged`. -/
theorem AbstractState.step_retG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    (out : GBCAOutput) (bnd : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out bnd) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitG ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcessVariables id { c.processes id with
            estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    AbstractState P (Function.update g r gr') c' w a := by
  have hAF := (Invariant.step_retG hI r id out bnd hstepG hstepC hgr' hc').2
  have hCUnchanged : c'.F = c.F ∧ ∀ id', (c'.processes id').input = (c.processes id').input ∧
      (c'.processes id').returned = (c.processes id').returned := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨ABAState.setProcessVariables_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcessVariables_processes_self]; exact ⟨rfl, rfl⟩
      · rw [ABAState.setProcessVariables_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id' => (hCUnchanged.2 id').1) (fun id' => (hCUnchanged.2
    id').2) hAF

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
  have hCUnchanged : c'.F = c.F ∧ ∀ id', (c'.processes id').input = (c.processes id').input ∧
      (c'.processes id').returned = (c.processes id').returned := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨ABAState.setProcessVariables_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcessVariables_processes_self]; exact ⟨rfl, rfl⟩
      · rw [ABAState.setProcessVariables_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id' => (hCUnchanged.2 id').1) (fun id' => (hCUnchanged.2
    id').2) hAF

/-- `retW`: stutters. -/
theorem AbstractState.step_retW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} {a : SpecState P.n}
    (hA : AbstractState P g c w a) (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.stepRound id b)) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    AbstractState P g c' (Function.update w r wr') a := by
  have hAF := (Invariant.step_retW hI r id b hstepW hstepC hwr' hc').2
  have hCUnchanged : c'.F = c.F ∧ ∀ id', (c'.processes id').input = (c.processes id').input ∧
      (c'.processes id').returned = (c.processes id').returned := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩ <;>
      rw [PMF.mem_support_pure_iff] at hc' <;> subst hc'
    · refine ⟨ABAState.stepRound_F _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h
        exact ⟨ABAState.stepRound_processes_self_input _ _ _,
          ABAState.stepRound_processes_self_returned _ _ _⟩
      · rw [ABAState.stepRound_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, fun id' => ⟨rfl, rfl⟩⟩
  exact hA.unchangedBy hCUnchanged.1 (fun id' => (hCUnchanged.2 id').1) (fun id' => (hCUnchanged.2
    id').2) hAF

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
standing still. -/
theorem mem_support_abaTransition {P : Parameters} {μc : PMF (ABAState P)} {o w' : ℕ → WCC.SpecState
  P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    (h : (C', A', w') ∈ (μc.map fun c => (c.1, c.2, o)).support) :
    (C', A') ∈ μc.support ∧ w' = o := by
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨⟨c1, c2⟩, hc, heq⟩ := h
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨hc, rfl⟩

/-- Reading a transition where the ABA component and the common coin move together. -/
theorem mem_support_coinTransition {P : Parameters} {μc : PMF (ABAState P)}
    {μw' : PMF (WCC.SpecState P.n)} {o w' : ℕ → WCC.SpecState P.n} {r : ℕ}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    (h : (C', A', w') ∈ (μc.bind fun c => prodPMF (PMF.pure c.1)
      (prodPMF (PMF.pure c.2) (μw'.map (Function.update o r)))).support) :
    (C', A') ∈ μc.support ∧ ∃ wr' ∈ μw'.support, w' = Function.update o r wr' := by
  rw [PMF.mem_support_bind_iff] at h
  obtain ⟨⟨c1, c2⟩, hc, hmem⟩ := h
  simp only [mem_support_prodPMF, PMF.mem_support_pure_iff, PMF.mem_support_map_iff] at hmem
  obtain ⟨rfl, rfl, wr', hwr', heq⟩ := hmem
  exact ⟨hc, wr', hwr', heq.symm⟩

/-- Reading a transition where the common coin moves alone: `g`, the round loops and the ABA
network unchanged, the coin instance of round `r` drawn from its own outcome. -/
theorem mem_support_coinResolution {P : Parameters} {G g' : ℕ → GBCA.SpecState P.n}
    {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A A' : ABANetworkState P.n}
    {μw : PMF (WCC.SpecState P.n)} {o w' : ℕ → WCC.SpecState P.n} {r : ℕ}
    (h : (g', C', A', w') ∈ (prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
      (prodPMF (PMF.pure A) (μw.map (Function.update o r))))).support) :
    g' = G ∧ C' = C ∧ A' = A ∧ ∃ wr' ∈ μw.support, w' = Function.update o r wr' := by
  simp only [mem_support_prodPMF, PMF.mem_support_pure_iff, PMF.mem_support_map_iff] at h
  obtain ⟨rfl, rfl, rfl, wr', hwr', heq⟩ := h
  exact ⟨rfl, rfl, rfl, wr', hwr', heq.symm⟩

/-- **`Invariant` is preserved.** Dispatches on the label class via `hybrid_step_callABA`/
`hybrid_step_retABA`/`hybrid_step_fail` (Stage A1) and `hybrid_step_tau` (Stage A2), calling
the matching `Invariant.step_*` helper (Stage B) in each case. -/
theorem Invariant.step {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A : ABANetworkState P.n} {w : ℕ → WCC.SpecState
      P.n}
    (hI : Invariant P g (C, A) w) {l : Label P.n} {μ : PMF (HybridState P)}
    (hstep : (hybrid P M).step (g, C, A, w) l μ) {g' : ℕ → GBCA.SpecState P.n}
    {C' : ∀ _ : Fin P.n, RoundLoopVariables P.n} {A' : ABANetworkState P.n}
    {w' : ℕ → WCC.SpecState P.n} (hmem : (g', C', A', w') ∈ μ.support) :
    Invariant P g' (C', A') w' := by
  cases l with
  | tau =>
    rcases hybrid_step_tau P g C A w hI.corrupted_F μ hstep with
      ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ |
      ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, out, bnd, μr, μc, hstepG, hstepC, rfl⟩ |
      ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ |
      ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩ |
      ⟨id, b, μc, ⟨-, hph, hlg, rfl⟩, rfl⟩ |
      ⟨r, μw, hstepW, rfl⟩
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      rw [PMF.mem_support_pure_iff] at h2
      obtain ⟨gr', hgr', heq⟩ := h1
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      rw [← heq]
      exact (Invariant.step_gbcaTau hI r hstepG hgr').1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
      rw [h1]
      exact (Invariant.step_roundLoopTau hI hstepC hc2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨gr', hgr', heq⟩ := h1
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
      rw [← heq]
      exact (Invariant.step_callG hI r id b hstepG hstepC hgr' hc2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_map_iff] at h1
      obtain ⟨gr', hgr', heq⟩ := h1
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
      rw [← heq]
      exact (Invariant.step_retG hI r id out bnd hstepG hstepC hgr' hc2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinTransition h2
      rw [h1]
      exact (Invariant.step_callW hI r id hstepW hstepC hwr' hc2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinTransition h2
      rw [h1]
      exact (Invariant.step_retW hI r id b hstepW hstepC hwr' hc2).1
    · simp only [mem_support_prodPMF] at hmem
      obtain ⟨h1, h2⟩ := hmem
      rw [PMF.mem_support_pure_iff] at h1
      obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
      rw [PMF.mem_support_pure_iff] at hc2
      rw [h1, hc2]
      exact (Invariant.step_decidedSend hI id b hph hlg).1
    · obtain ⟨rfl, rfl, rfl, wr', hwr', rfl⟩ := mem_support_coinResolution hmem
      obtain ⟨hv, ht, rfl⟩ := WCC.step_tau_cases hstepW
      rw [PMF.mem_support_map_iff] at hwr'
      obtain ⟨oc, -, rfl⟩ := hwr'
      exact hI.step_resolve r ht hv oc
  | callABA id b =>
    rw [hybrid_step_callABA P g C A w id b hI.corrupted_F] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    rw [h1]
    exact (Invariant.step_callABA hI id b hstepC hc2).1
  | retABA id b =>
    rw [hybrid_step_retABA P g C A w id b hI.corrupted_F] at hstep
    obtain ⟨μc, hstepC, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    rw [h1]
    exact (Invariant.step_retABA hI id b hstepC hc2).1
  | fail id =>
    rw [hybrid_step_fail P g C A w id hI.corrupted_F] at hstep
    obtain ⟨hnew, hbud, rfl⟩ := hstep
    simp only [mem_support_prodPMF] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [PMF.mem_support_pure_iff] at h1
    obtain ⟨hc2, rfl⟩ := mem_support_abaTransition h2
    rw [PMF.mem_support_pure_iff] at hc2
    rw [h1, hc2]
    exact (Invariant.step_fail hI id hnew hbud).1
  | callG r id b =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.callG_mem_hiddenAPI r id b)
  | retG r id out bnd =>
    exfalso; rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨hnotmem, -⟩
    · exact absurd hτ (by simp)
    · exact hnotmem (Label.retG_mem_hiddenAPI r id out bnd)
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

end ABA
end PLTS
