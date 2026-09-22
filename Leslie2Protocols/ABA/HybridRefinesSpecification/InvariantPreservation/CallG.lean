/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# `Invariant` across the `callG` rows of `hybrid`

`Invariant.step_callG`, preservation of `Invariant` at a call of the graded-agreement
specification. The GBCA instance only ever touches `.call`, never `.F`, `.excluded` or `.grade`,
and the core only ever touches `.phase` at `id`, never `.input`, `.estimate` or `.round`.
`grade2Lock_commit`'s second conjunct comes from its own third conjunct and the correct call guard
`estimate = b`. The correct-fresh-call corner of `input_gbcaRound0` and `input_called` needs
"`estimate = input` before any round-`0` return", a coherence of phase and input that is not an
explicit `Invariant` conjunct, and is handed off.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- `callG`: the GBCA instance only ever touches `.call` (never `.F`/`.excluded`/`.grade`), the
core only ever touches `.phase` at `id` (never `.input`/`.estimate`/`.round`). `input_gbcaRound0`/
`input_called`'s correct-fresh-call corner needs "`estimate = input` before any round-`0` return"
(phase/input coherence, not an explicit `Invariant` conjunct) — handed off; `grade2Lock_commit`'s
second conjunct is derived cleanly from its own third conjunct plus the correct call guard
`estimate = b`. -/
theorem Invariant.step_callG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .toCallG ∧ (c.processes id).round = r ∧
          (c.processes id).estimate = some b ∧
          μc = PMF.pure (c.setProcess id { c.processes id with phase := .awaitG })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P (Function.update g r gr') c' w ∧
      AbstractStateUnchanged P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.excluded = (g r).excluded ∧ gr'.grade = (g r).grade := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').excluded = (g r').excluded := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hGradeeq : ∀ r', (Function.update g r gr' r').grade = (g r').grade := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedReceived =
    c.decidedReceived ∧
      ∀ id',
        (c'.processes id').input = (c.processes id').input ∧ (c'.processes id').estimate =
          (c.processes id').estimate ∧ (c'.processes id').round = (c.processes id').round := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProcess_F _ _ _, ABAState.setProcess_decidedSent _ _ _,
        ABAState.setProcess_decidedReceived _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [ABAState.setProcess_processes_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  -- The one fact needing case analysis: `gr'.call`, as an unconditional description
  -- (`Or.inl`: a fresh correct/byzantine `call` at `id`; `Or.inr`: `callLoop`, unaffected).
  have hGcall : (gr' = { g r with call := Function.update (g r).call id (some b) }) ∨
      gr' = g r := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inl hgr'
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inr hgr'
  have hCcall : ((c.processes id).phase = .toCallG ∧ (c.processes id).round = r ∧
      (c.processes id).estimate = some b ∧
      c' = c.setProcess id { c.processes id with phase := .awaitG }) ∨ (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hest, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- Every fresh call of a correct process, at any `id'` and any round `r'`, agrees with
  -- `estimate` at that `id'`.
  have hGcallval : ∀ id' b', gr'.call id' = some b' → id' ≠ id → (g r).call id' = some b' := by
    rcases hGcall with rfl | rfl
    · intro id' b' h hne; simpa [Function.update_of_ne hne] using h
    · intro id' b' h _; exact h
  -- `call` entries are write-once (`Step.call` fires only on an empty entry), so a fresh call
  -- only ever adds to a support count.
  have hCallMono : ∀ id' b', (g r).call id' = some b' → gr'.call id' = some b' := by
    cases hstepG with
    | call _ _ hfresh =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
      intro id' b' h'
      show Function.update (g r).call id (some b) id' = some b'
      by_cases hid : id' = id
      · rw [hid] at h'; rw [hfresh] at h'; simp at h'
      · rw [Function.update_of_ne hid]; exact h'
    | callLoop =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact fun _ _ h => h
  have hGcallSelf : gr'.call id = some b ∨ gr' = g r := by
    rcases hGcall with rfl | rfl
    · left; simp
    · right; rfl
  have hPhaseNe : ∀ id', id' ≠ id → (c'.processes id').phase = (c.processes id').phase := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id' hne; rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hne]
    · intro id' _; rw [hc'eq]
  have hLastGradeG : ∀ id', (c'.processes id').lastGrade = (c.processes id').lastGrade := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]
      · rw [ABAState.setProcess_processes_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarrTrans : ∀ r₀ id₀ v, id₀ ∉ c.F →
      OutcomeHolder P (Function.update g r gr') c' r₀ id₀ v → OutcomeHolder P g c r₀ id₀ v := by
    intro r₀ id₀ v hmem0 hc0
    rcases hc0 with h | ⟨he, hk⟩
    · by_cases h1 : r₀ + 1 = r
      · rw [h1, Function.update_self] at h
        by_cases hid : id₀ = id
        · subst hid
          rcases hGcallSelf with hself | hself
          · rw [hself, Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
            · exact Or.inr ⟨by rw [hest, h], Or.inr ⟨by rw [hr, h1], Or.inr (Or.inl hph)⟩⟩
            · exact absurd hF hmem0
          · rw [hself] at h
            exact Or.inl (by rw [h1]; exact h)
        · have := hGcallval id₀ v h hid
          exact Or.inl (by rw [h1]; exact this)
      · rw [hGeq (r₀ + 1) h1] at h; exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, ABAState.setProcess_processes_self] at hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · exact Or.inr ⟨hr0, Or.inr (Or.inl hph)⟩
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCommitTrans : ∀ r0 b0, Grade2Commitment P g c r0 b0 →
      Grade2Commitment P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r'' b'' hrr' hbind =>
        h1 r'' b'' hrr' (by rw [← hBindeq r'']; exact hbind),
      fun r'' id' b'' hrr' hmem hcall => ?_, fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem)
        (hCarrTrans r0 id0 v (hCF ▸ hmem) hcar)⟩
    · by_cases hrr : r'' = r
      · rw [hrr, Function.update_self] at hcall
        by_cases hid : id' = id
        · rw [hid] at hcall hmem
          rcases hGcallSelf with hself | hself
          · rw [hself] at hcall; rw [Option.some_inj] at hcall
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · have hh3 := h3 id (hCF ▸ hmem) (by rw [hr, ← hrr]; exact hrr')
              rw [hest] at hh3; rw [Option.some_inj] at hh3
              rw [← hcall, hh3]
            · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
          · rw [hself] at hcall
            exact h2 r'' id b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact hcall)
        · have := hGcallval id' b'' hcall hid
          exact h2 r'' id' b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact this)
      · rw [hGeq r'' hrr] at hcall
        exact h2 r'' id' b'' hrr' (hCF ▸ hmem) hcall
    · rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  have hCertTrans : ∀ r0 b0, Grade2Certificate P g c r0 b0 →
      Grade2Certificate P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg1, hd1, hcm⟩
    exact ⟨by rw [hGradeeq]; exact hg1, by rw [hBindeq]; exact hd1, hCommitTrans r0 b0 hcm⟩
  have hHold : ∀ i0 b0, Grade2Holder P c' i0 b0 → Grade2Holder P c i0 b0 := by
    intro i0 b0 h
    unfold Grade2Holder at h ⊢
    rwa [hLastGradeG, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  have hCcorr : c'.corrupted = c.corrupted := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · rw [hc'eq]; exact ABAState.setProcess_corrupted _ _ _
    · rw [hc'eq]
  refine ⟨fun id' => by rw [hCcorr, hCF]; exact hI.corrupted_F id',
    fun r' => (hFgeq r').trans (hCF ▸ hI.F_gbca r'), fun r' => hCF ▸ hI.F_wcc r',
    hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r' h => by rw [hGradeeq] at h ⊢; exact hI.grade0Lock_chain r' h, ?_,
    hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r' v hb => (hI.bind_support r' v (by rw [← hBindeq r']; exact hb)).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    fun r' b' hgf => GBCA.callSupport_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' b' h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.grade0Lock_support r' b' ((hGradeeq r').symm.trans hgf)),
    fun r' b0 hbd => GBCA.callSupport_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' (!b0) h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.excluded_support r' b0 (by rw [← hBindeq r']; exact hbd)),
    fun r₀ i0 j0 v v' hm hm' h h' => (hI.outcomeHolder_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarrTrans r₀ i0 v (hCF ▸ hm) h) (hCarrTrans r₀ j0 v' (hCF ▸ hm') h')).imp
      (fun x => x) (fun hh => (hGradeeq r₀).trans hh),
    fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · -- input_gbcaRound0
    intro id' b' hmem hcall
    rw [(hCprocs id').1]
    by_cases hr0 : r = 0
    · rw [hr0, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself] at hcall; rw [Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · rw [hid]
            have hmem' : id ∉ c.F := by
              rw [← hCF, ← hid]; exact hmem
            have he0 := hI.estimate0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
            rw [← he0, hest, hcall]
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself, hr0] at hcall
          rw [hid] at hmem ⊢
          exact hI.input_gbcaRound0 id b' (hCF ▸ hmem) hcall
      · have := hGcallval id' b' hcall hid
        rw [hr0] at this
        exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem) this
    · rw [hGeq 0 (Ne.symm hr0)] at hcall
      exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem) hcall
  · -- input_called
    intro r' id' hmem hcall
    rw [(hCprocs id').1]
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall ⊢
        rcases hGcallSelf with hself | hself
        · rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
            exact hI.phase_input id hmem' (by rw [hph]; simp)
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself] at hcall; rw [hid] at hmem; exact hI.input_called r id (hCF ▸ hmem) hcall
      · rcases hGcall with hgeq | hgeq
        · rw [hgeq] at hcall; simp only [Function.update_of_ne hid] at hcall
          exact hI.input_called r id' (hCF ▸ hmem) hcall
        · rw [hgeq] at hcall; exact hI.input_called r id' (hCF ▸ hmem) hcall
    · rw [hGeq r' hrr] at hcall
      exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · -- phase_input
    intro id' hmem hne
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hne
        exact hI.phase_input id' (hCF ▸ hmem) hne
    · rw [hc'eq] at hne
      rw [(hCprocs id').1]
      exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- down_settled
    intro r' h
    rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]
    exact hI.down_settled r' ((RoundSettled.congr (hBindeq (r' + 1)) (hGradeeq (r' + 1))).mp h)
  · -- quiescent
    obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r' hr' h => hR r' hr' ((RoundSettled.congr (hBindeq r') (hGradeeq r')).mp h)⟩
  · -- wcc_bound
    intro r' h; rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]; exact hI.wcc_bound r' h
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.received_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_source id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    rw [hGradeeq] at hgr; rw [hBindeq] at hbr
    exact hCommitTrans r0 b0 (hI.grade2Lock_commit r0 b0 hgr hbr)
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround
    rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]
    exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h; rw [hGradeeq] at h; rw [hBindeq]; exact hI.grade2_needs_bind r' h
  · intro r' id' hmem hcall
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [(hCprocs id').2.2]
        obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hcall
        have hcv := hGcallval id' b' hb' hid
        rw [hrr]
        exact hI.call_round r id' (hCF ▸ hmem) (by rw [hcv]; simp)
    · rw [hGeq r' hrr] at hcall
      rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]
    exact hI.wcc_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        rw [hid, (hCprocs id).2.2] at hround
        rw [hid, (hCprocs id).1, (hCprocs id).2.1]
        exact hI.estimate0 id hmem' hround (Or.inr (Or.inl hph))
      · rw [(hCprocs id').2.2] at hround
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [(hCprocs id').1, (hCprocs id').2.1]
        exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.2] at hround
      rw [(hCprocs id').1, (hCprocs id').2.1]
      exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGradeG] at hlg
    exact (hI.grade2_source id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h <;> simp at h
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · obtain ⟨hg0, hno⟩ := hnone he
          refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
          rw [hGradeeq] at hgr0
          exact hno r₀ hr0 hgr0
        · rw [hBindeq]; exact hsome b hb
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
      refine ⟨fun he => ?_, fun b hb => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · rw [hBindeq]; exact hsome b hb
  · intro r' v h
    rw [hBindeq] at h; rw [hBindeq r', hGradeeq r']
    exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall
    by_cases h1 : r' + 1 = r
    · by_cases hid : id' = id
      · rw [hid] at hcall hmem
        rw [h1, Function.update_self] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself, Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
          · have hround : (c.processes id).round = r' + 1 := by rw [hr, h1]
            have hep := hI.estimate_previous r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) b hest
            rw [hBindeq r', hGradeeq r']
            rwa [hcall] at hep
          · exact absurd hF (hCF ▸ hmem)
        · rw [hself] at hcall
          rw [hBindeq r', hGradeeq r']
          exact hI.call_provenance r' id v (hCF ▸ hmem) (by rw [h1]; exact hcall)
      · rw [h1, Function.update_self] at hcall
        have hcv := hGcallval id' v hcall hid
        rw [hBindeq r', hGradeeq r']
        exact hI.call_provenance r' id' v (hCF ▸ hmem) (by rw [h1]; exact hcv)
    · rw [hGeq (r' + 1) h1] at hcall
      rw [hBindeq r', hGradeeq r']
      exact hI.call_provenance r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest
    rw [hBindeq r', hGradeeq r']
    rcases hCcall with ⟨hph, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround hest
        exact hI.estimate_previous r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) v hest
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rw [(hCprocs id').2.1]
    rcases hCcall with ⟨hph, hr, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround ⊢
        exact hI.estimate_previous_ne id (hCF ▸ hmem) hround (Or.inr (Or.inl hph))
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
  · -- `input_gbcaRound0_permanent`: mirrors `input_gbcaRound0`'s establishment
    -- above, with an `id' ∈ F` escape hatch replacing the correctness hypothesis.
    intro id' b' h
    by_cases hmem : id' ∈ c.F
    · right; rw [hCF]; exact hmem
    · left
      rw [(hCprocs id').1]
      by_cases hr0 : r = 0
      · rw [hr0, Function.update_self] at h
        by_cases hid : id' = id
        · rw [hid] at h
          rcases hGcallSelf with hself | hself
          · rw [hself] at h; rw [Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · rw [hid]
              have hmem' : id ∉ c.F := by
                rw [hid] at hmem; exact hmem
              have he0 := hI.estimate0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
              rw [← he0, hest, h]
            · rw [hid] at hmem; exact absurd hF hmem
          · rw [hself, hr0] at h
            rw [hid] at hmem ⊢
            rcases hI.input_gbcaRound0_permanent id b' h with hin | hf
            · exact hin
            · exact absurd hf hmem
        · have hcv := hGcallval id' b' h hid
          rw [hr0] at hcv
          rcases hI.input_gbcaRound0_permanent id' b' hcv with hin | hf
          · exact hin
          · exact absurd hf hmem
      · rw [hGeq 0 (Ne.symm hr0)] at h
        rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
        · exact hin
        · exact absurd hf hmem
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2.2]; exact hI.wcc_callRound r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_grade2Lock r' h with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin; exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hp' : ((c.processes id').round = r' ∧
        ((c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW)) ∨
        r' < (c.processes id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · refine Or.inl ⟨hround, ?_⟩
        by_cases hid : id' = id
        · rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
          · exfalso
            rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
            rcases hphase with h | h <;> simp at h
          · rw [hid]
            rw [hid, hc'eq] at hphase
            exact hphase
        · rwa [hPhaseNe id' hid] at hphase
      · exact Or.inr hlt
    rw [hGradeeq]
    rcases hI.retG_witness r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    rcases hI.wccCalled_witness r' id' (hCF ▸ hmem) hcalled with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' h
    rw [hBindeq] at h
    refine GBCA.SpecState.quorum_mono (hFgeq r').ge (fun id' hne => ?_) (hI.bound_quorum r' h)
    by_cases hrr : r' = r
    · rw [hrr] at hne ⊢
      rw [Function.update_self]
      rcases hGcall with hg | hg
      · rw [hg]
        show Function.update (g r).call id (some b) id' ≠ none
        by_cases hid : id' = id
        · rw [hid, Function.update_self]; simp
        · rw [Function.update_of_ne hid]; exact hne
      · rw [hg]; exact hne
    · rw [hGeq r' hrr]; exact hne

end ABA
end PLTS
