/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.FamilySimulation

/-!
# Forward simulation is a congruence for `System.mapIdle`

A forward simulation between two systems over `L` survives reading both systems over a finer
alphabet `L'` along the same partial label map `φ : L' → Option L` (`System.mapIdle`,
`Framework/LoopsAndInstanceFamilies.lean`): delegated labels are matched through the simulation, and
unmapped labels — idle self-loops in both systems — are matched by idling
(`ForwardSimulation.mapIdle`).

The only hypotheses are a τ round-trip for `φ`: the silent label of `L'`
delegates to the silent label of `L` (`hτ'`), and nothing else does (`hφτ`).
No section of `φ` is required: the weak-run transports
(`System.weakLSilent_mapIdle_of`, `System.weakLStep_mapIdle_of`) relabel the
witness execution per transition — silent transitions to `τ'`, the single
external one to the delegating label `l'` — using that a terminating run's
non-silent labels all occur in its trace (`mem_trace_of_external`,
`Framework/FamilySimulation.lean`).
-/

open Stream'

namespace PLTS

variable {S L L' : Type}

/-- Transport a partial execution along a label map that turns each of the
run's own transitions into a transition of `sys'` — the per-run refinement of
`is_partial_exec_mapLabels` (`Framework/TraceDistributionSupport.lean`). -/
private theorem is_partial_exec_mapLabels_on {sys : System S L} {sys' : System S L'}
    (g : L → L') {e : AlterSeq S L} (hpe : is_partial_exec e sys)
    (hg : ∀ n lq, e.trans.get? n = some lq →
      ∀ sn μ, sys.step sn lq.1 μ → sys'.step sn (g lq.1) μ) :
    is_partial_exec (e.mapLabels g) sys' := by
  intro n l s' hn
  rw [show (e.mapLabels g).trans = e.trans.map (fun lq : L × S => (g lq.1, lq.2)) from rfl,
    Stream'.Seq.map_get?] at hn
  cases hq : e.trans.get? n with
  | none =>
    rw [hq] at hn
    exact absurd hn (by simp)
  | some lq =>
    obtain ⟨l₀, x⟩ := lq
    rw [hq] at hn
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    obtain ⟨sn, μ, hsn, hstep, hmem⟩ := hpe n l₀ x hq
    exact ⟨sn, μ, by rw [AlterSeq.stateAt_mapLabels]; exact hsn,
      hg n (l₀, x) hq sn μ hstep, hmem⟩

/-- Relabelling every transition of a terminating run to `τ'` yields an
empty-trace run. -/
private theorem trace_mapLabels_const_tau [Silent L'] (sys' : System S L')
    (e : AlterSeq S L) (hterm : e.trans.Terminates) :
    sys'.trace (e.mapLabels (fun _ => (Silent.τ : L'))) = (Seq.nil : Seq L') := by
  classical
  unfold System.trace
  rw [show (e.mapLabels (fun _ => (Silent.τ : L'))).trans
      = e.trans.map (fun lq : L × S => ((Silent.τ : L'), lq.2)) from rfl,
    ← Stream'.Seq.ofList_toList e.trans hterm, Stream'.Seq.map_ofList_pub,
    Stream'.Seq.ofList_filter]
  have h2 : ((e.trans.toList hterm).map
        (fun lq : L × S => ((Silent.τ : L'), lq.2))).filter
      (fun a => @decide (¬ (a.1 = (Silent.τ : L'))) (Classical.propDecidable _)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨lq, -, rfl⟩ := List.mem_map.mp ha
    simp
  rw [h2, Stream'.Seq.ofList_nil, Stream'.Seq.map_nil]

section Transport

variable [Silent L] [Silent L'] {sys : System S L} {φ : L' → Option L}

/-- **A silent weak run survives the read-back**, whenever the silent label of
`L'` delegates to the silent label of `L`: the witness execution is silent
throughout, so relabelling every transition to `τ'` transports it. -/
theorem System.weakLSilent_mapIdle_of {q q' : S}
    (hτ' : φ (Silent.τ : L') = some (Silent.τ : L))
    (h : sys.weakLSilent q q') : (sys.mapIdle φ).weakLSilent q q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.mapLabels (fun _ => (Silent.τ : L')),
    (AlterSeq.mapLabels_trans_terminates_iff _ e).mpr hterm, ?_, hinit, ?_, ?_⟩
  · refine is_partial_exec_mapLabels_on _ hpe ?_
    intro n lq hn sn μ hstep
    obtain ⟨l₀, s₀⟩ := lq
    have hτlab : l₀ = Silent.τ := by
      by_contra hne
      obtain ⟨m, hm⟩ := mem_trace_of_external (sys := sys) hterm hn hne
      rw [htr, Stream'.Seq.get?_nil] at hm
      exact absurd hm (by simp)
    subst hτlab
    change (sys.mapIdle φ).step sn (Silent.τ : L') μ
    exact (System.mapIdle_step_some hτ' μ).mpr hstep
  · rw [AlterSeq.endState_mapLabels _ e hterm]
    exact hend
  · exact trace_mapLabels_const_tau _ e hterm

/-- **A labelled weak run survives the read-back** at any delegating label:
`q =l=> q'` of `sys` is `q =l'=> q'` of `sys.mapIdle φ` whenever
`φ l' = some l`. The witness execution is relabelled per transition — silent
transitions to `τ'`, the single external one to `l'`. -/
theorem System.weakLStep_mapIdle_of {q q' : S} {l : L} {l' : L'}
    (hτ' : φ (Silent.τ : L') = some (Silent.τ : L))
    (hφl : φ l' = some l) (hl : ¬ l = Silent.τ) (hl' : ¬ l' = Silent.τ)
    (h : sys.weakLStep q l q') : (sys.mapIdle φ).weakLStep q l' q' := by
  classical
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  set g : L → L' := fun x => if x = Silent.τ then (Silent.τ : L') else l' with hg
  have hgτ : ∀ x, g x = (Silent.τ : L') ↔ x = (Silent.τ : L) := by
    intro x
    by_cases hx : x = Silent.τ
    · simp [hg, hx]
    · simp [hg, hx, hl']
  have hgl : g l = l' := by
    simp [hg, hl]
  refine ⟨e.mapLabels g, (AlterSeq.mapLabels_trans_terminates_iff g e).mpr hterm,
    ?_, hinit, ?_, ?_⟩
  · refine is_partial_exec_mapLabels_on g hpe ?_
    intro n lq hn sn μ hstep
    obtain ⟨l₀, s₀⟩ := lq
    by_cases hτl : l₀ = Silent.τ
    · subst hτl
      have hgτ' : g Silent.τ = (Silent.τ : L') := by
        simp [hg]
      rw [hgτ']
      exact (System.mapIdle_step_some hτ' μ).mpr hstep
    · obtain ⟨m, hm⟩ := mem_trace_of_external (sys := sys) hterm hn hτl
      rw [htr] at hm
      have hl₀ : l₀ = l := by
        cases m with
        | zero =>
          rw [Stream'.Seq.get?_cons_zero] at hm
          exact (Option.some.inj hm).symm
        | succ k =>
          rw [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hm
          exact absurd hm (by simp)
      subst hl₀
      rw [hgl]
      exact (System.mapIdle_step_some hφl μ).mpr hstep
  · rw [AlterSeq.endState_mapLabels g e hterm]
    exact hend
  · rw [System.trace_mapLabels _ sys g hgτ e, htr, Stream'.Seq.map_cons,
      Stream'.Seq.map_nil, hgl]

end Transport

/-! ### The congruence -/

/-- **Forward simulation is a congruence for `System.mapIdle`.** Both systems
read over a finer alphabet along the same `φ`, delegated labels are matched
through the simulation and unmapped labels by idling. The hypotheses are the
τ round-trip of `φ`: `τ'` delegates to `τ` and nothing else does. -/
theorem ForwardSimulation.mapIdle {T : Type} [Silent L] [Silent L']
    {sysC : System S L} {sysA : System T L} {R : S → T → Prop}
    (φ : L' → Option L)
    (hτ' : φ (Silent.τ : L') = some (Silent.τ : L))
    (hφτ : ∀ l', φ l' = some (Silent.τ : L) → l' = (Silent.τ : L'))
    (sim : ForwardSimulation sysC sysA R) :
    ForwardSimulation (sysC.mapIdle φ) (sysA.mapIdle φ) R := by
  constructor
  intro q₁ q₂ hR l' μ hstep q₁' hq₁'
  rw [System.mapIdle_step] at hstep
  rcases hstep with ⟨l, hφ, hstepC⟩ | ⟨hφ, rfl⟩
  · -- Delegated: match through the simulation.
    obtain ⟨q₂', hdisj, hR'⟩ := sim.step q₁ q₂ hR l μ hstepC q₁' hq₁'
    rcases hdisj with ⟨rfl, hsil⟩ | ⟨hlτ, hlab⟩
    · exact ⟨q₂', Or.inl ⟨hφτ l' hφ, System.weakLSilent_mapIdle_of hτ' hsil⟩, hR'⟩
    · have hl'τ : ¬ l' = Silent.τ := by
        intro hEq
        rw [hEq, hτ'] at hφ
        exact hlτ (Option.some.inj hφ).symm
      exact ⟨q₂', Or.inr ⟨hl'τ,
        System.weakLStep_mapIdle_of hτ' hφ hlτ hl'τ hlab⟩, hR'⟩
  · -- Idle self-loop: the abstract system idles on the same label.
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hl'τ : ¬ l' = Silent.τ := by
      intro hEq
      rw [hEq, hτ'] at hφ
      exact absurd hφ (by simp)
    exact ⟨q₂, Or.inr ⟨hl'τ, System.weakLStep_of_step hl'τ
      ((System.mapIdle_step_none hφ _).mpr rfl)⟩, hR⟩

end PLTS
