/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# `Invariant` across the `retABA` rows of `hybrid`

`Invariant.step_retABA`, preservation of `Invariant` at a return of the ABA interface. A
never-corrupted process's return only sets `returned`, a field `Invariant` never inspects, so
`Invariant` transfers verbatim modulo the pointwise-unchanged projections of `processes`. A
corrupted process's return is a state identity, and `Invariant` transfers outright.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- `retABA`: a never-corrupted process's return only sets `returned`, a field `Invariant` never
inspects, so `Invariant` transfers verbatim modulo the pointwise-unchanged projections of
`processes`. A corrupted process's return is a state identity, and `Invariant` transfers outright.
-/
theorem Invariant.step_retABA {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (ABAState P)}
    (hstep : (id ∉ c.F ∧ P.n - P.f ≤ c.decidedCount id b ∧ b ∈ c.decidedSent id ∧
        (c.processes id).returned = false ∧
        μc = PMF.pure (c.setProcess id { c.processes id with returned := true })) ∨
      (id ∈ c.F ∧ μc = PMF.pure c))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' w ∧ AbstractStateUnchanged P g g c c' := by
  rcases hstep with hstep | ⟨-, rfl⟩
  · obtain ⟨-, -, -, -, rfl⟩ := hstep
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    set c' := c.setProcess id { c.processes id with returned := true } with hc'def
    have hF : c'.F = c.F := ABAState.setProcess_F _ _ _
    have hCorr : c'.corrupted = c.corrupted := ABAState.setProcess_corrupted _ _ _
    have hDS : c'.decidedSent = c.decidedSent := ABAState.setProcess_decidedSent _ _ _
    have hDR : c'.decidedReceived = c.decidedReceived := ABAState.setProcess_decidedReceived _ _ _
    have hDC : ∀ i b', c'.decidedCount i b' = c.decidedCount i b' :=
      fun i b' => ABAState.setProcess_decidedCount _ _ _ _ _
    have hInput : ∀ id', (c'.processes id').input = (c.processes id').input := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hEst : ∀ id', (c'.processes id').estimate = (c.processes id').estimate := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hRound : ∀ id', (c'.processes id').round = (c.processes id').round := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hPhase : ∀ id', (c'.processes id').phase = (c.processes id').phase := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hLastGrade : ∀ id', (c'.processes id').lastGrade = (c.processes id').lastGrade := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hCarr : ∀ r' id' v, OutcomeHolder P g c' r' id' v → OutcomeHolder P g c r' id' v := by
      intro r' id' v hc
      unfold OutcomeHolder at hc ⊢
      rwa [hEst, hRound, hPhase] at hc
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g c' r' b' := fun r' b' =>
        Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hF] : c.F ⊆ c'.F) hRound hEst (fun id0 v => hCarr r' id0 v)
    have hHold : ∀ id' b', Grade2Holder P c' id' b' → Grade2Holder P c id' b' := by
      intro id' b' h
      unfold Grade2Holder at h ⊢
      rwa [hLastGrade, hDS] at h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
    refine ⟨fun id' => by rw [hCorr, hF]; exact hI.corrupted_F id',
      fun r => (hI.F_gbca r).trans hF.symm, fun r => ?_, ?_, ?_, ?_, ?_,
      hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hInput]; exact h) (fun x hx => by rw [hF]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i j v v' hm hm' h h' => hI.outcomeHolder_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
        (hCarr _ _ _ h) (hCarr _ _ _ h'),
      fun i j b₀ b₀' hm hm' h h' => hI.grade2Lock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
        (hHold _ _ h) (hHold _ _ h')⟩
    · rw [hF]; exact hI.F_wcc r
    · rw [hF]; exact hI.F_card
    · intro id' b' hmem hcall; rw [hInput]; exact hI.input_gbcaRound0 id' b' (hF ▸ hmem) hcall
    · intro r id' hmem hcall; rw [hInput]; exact hI.input_called r id' (hF ▸ hmem) hcall
    · intro id' hmem hne; rw [hPhase] at hne; rw [hInput]; exact hI.phase_input id' (hF ▸ hmem) hne
    · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.received_sound i j b' h
    · intro id' b' hmem h; rw [hDS] at h
      exact (hI.decided_source id' b' (hF ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hg hb
      exact Grade2Commitment.of_unchanged (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hF]) hRound hEst (fun id0 v => hCarr r id0 v) (hI.grade2Lock_commit r b' hg hb)
    · intro id' hmem r hr; exact hI.round_bound id' (hF ▸ hmem) r (hRound id' ▸ hr)
    · intro r v hlast hb hcoin id' hmem hr
      rw [hEst]; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) (hRound id' ▸ hr)
    · intro r id' hmem hcall; rw [hRound]; exact hI.call_round r id' (hF ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hF ▸ hmem) hcalled
    · intro r id' hmem hr; rw [hRound] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
    · intro id' hmem hround hphase
      rw [hRound] at hround; rw [hPhase] at hphase
      rw [hEst, hInput]; exact hI.estimate0 id' (hF ▸ hmem) hround hphase
    · intro id' b' hlg; rw [hLastGrade] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hRound] at hround; rw [hPhase] at hphase
      rw [hEst]; exact hI.estimate_ret r id' (hF ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hF ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst] at hest
      exact hI.estimate_previous r id' (hF ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst]
      exact hI.estimate_previous_ne id' (hF ▸ hmem) hround hphase
    · intro id' b' h
      rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
      · left; rw [hInput]; exact hin
      · right; rw [hF]; exact hf
    · intro r id' hmem hcalled; rw [hRound]; exact hI.wcc_callRound r id' (hF ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun hh => hh) (fun id' => hInput id') hd
    · intro id' hmem hin r'; rw [hInput] at hin; exact hI.idle_no_wccCall id' (hF ▸ hmem) hin r'
    · intro r id' hmem h
      rw [hRound] at h; rw [hPhase] at h
      rcases hI.retG_witness r id' (hF ▸ hmem) h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd
  · rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact ⟨hI, AbstractStateUnchanged.refl P g _⟩

end ABA
end PLTS
