/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# `Invariant` across the `retW` rows of `hybrid`

`Invariant.step_retW`, preservation of `Invariant` at a return of the coin. `g` is untouched
entirely, the coin instance touches only `.ret`, a field `Invariant` does not inspect, and the
core's `stepRound` touches `estimate`, `lastGrade`, `round` and `phase` at `id`, and
`decidedSent id` on a grade-2. `round_bound`'s freshly included round is covered by `wcc_bound`,
the coin having resolved closing the round. The DECIDED-on-grade-2 witness for `decided_source`,
and the extension of `grade2Lock_commit` and `agree_locked` to `id`'s new round, need the
cross-round correlation of `lastGrade` with `(g r).grade` and `(g r).excluded` (GBCA graded
agreement), which is not a local `Invariant` consequence, and are handed off.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- `retW`: `g` is untouched entirely; the WCC instance only touches `.ret` (not inspected by
`Invariant`); the core's `stepRound` touches `estimate`/`lastGrade`/`round`/`phase` at `id` and
conditionally `decidedSent id` (on a grade-2). `round_bound`'s freshly-included round is
covered by `wcc_bound` (the coin having resolved closes the round); the DECIDED-on-grade-2
witness for `decided_source`, and the `grade2Lock_commit`/`agree_locked` extension to `id`'s new
round, need the cross-round `lastGrade`-to-`(g r).grade/.excluded` correlation (GBCA Graded
Agreement) that isn't a local `Invariant` consequence — handed off. -/
theorem Invariant.step_retW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.stepRound id b)) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' (Function.update w r wr') ∧ AbstractStateUnchanged P g g c c' := by
  have hWeq : (Function.update w r wr' r).F = (w r).F ∧
      (Function.update w r wr' r).val = (w r).val := by
    rw [Function.update_self]; cases hstepW with
    | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']; exact ⟨rfl, rfl⟩
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.1
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.2
    · rw [hWNe r' h]
  have hWval : (w r).val ≠ .bot := by
    cases hstepW with
    | ret _ _ h1 _ => rcases h1 with h1 | h1 <;> rw [h1] <;> simp
  have hCoinEq : ∀ v', (w r).val = .bit v' → b = v' := by
    cases hstepW with
    | ret _ _ h1 _ =>
      intro v' hv'
      rcases h1 with h1 | h1
      · rw [h1] at hv'; simp at hv'
      · rw [h1] at hv'; simpa using hv'
  have hCalledEq : ∀ r', (Function.update w r wr' r').called = (w r').called := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]
      cases hstepW with
      | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']
    · rw [hWNe r' h]
  rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hc'
    have hFeq : (c.stepRound id b).F = c.F := ABAState.stepRound_F _ _ _
    have hDReq : (c.stepRound id b).decidedReceived = c.decidedReceived :=
      ABAState.stepRound_decidedReceived _ _ _
    have hProcNe : ∀ id', id' ≠ id → (c.stepRound id b).processes id' = c.processes id' := by
      intro id' h; exact ABAState.stepRound_processes_ne _ _ _ h
    have hProcSelf : (c.stepRound id b).processes id = { c.processes id with
        estimate := some ((c.processes id).estimate.getD b), lastGrade := none,
        round := (c.processes id).round + 1,
          phase := .toCallG } := ABAState.stepRound_processes_self _ _ _
    have hInputEq : ((c.stepRound id b).processes id).input = (c.processes id).input := by
      rw [hProcSelf]
    have hRoundEq : ((c.stepRound id b).processes id).round = (c.processes id).round + 1 := by
      rw [hProcSelf]
    have hDSeq : (c.stepRound id b).decidedSent = c.decidedSent ∨
        ∃ b0, (c.processes id).lastGrade = some (.grade2 b0) ∧
          (c.stepRound id b).decidedSent =
            Function.update c.decidedSent id (insert b0 (c.decidedSent id)) := by
      by_cases hA : ∃ b0, (c.processes id).lastGrade = some (.grade2 b0)
      · obtain ⟨b0, hlg⟩ := hA
        exact Or.inr ⟨b0, hlg, ABAState.stepRound_decidedSent_of_grade2 c id b b0 hlg⟩
      · exact Or.inl (ABAState.stepRound_decidedSent_of_not_grade2 c id b (fun b1 heq => hA ⟨b1,
          heq⟩))
    have hDR2 : ∀ r', DissentWitness P g c r' → DissentWitness P g (c.stepRound id b) r' := by
      intro r' hd
      refine DissentWitness.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
      by_cases hid2 : id2 = id
      · rw [hid2]; exact hInputEq
      · rw [hProcNe id2 hid2]
    -- OutcomeHolder reduction: a post-`stepRound` carrier is an old one or `id`, now holding the
    -- adopted estimate at the finished round `r`.
    have hRedW : ∀ r₀ i1 v1, OutcomeHolder P g (c.stepRound id b) r₀ i1 v1 →
        OutcomeHolder P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ (c.processes id).estimate.getD b = v1) :=
          by
      intro r₀ i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl hcall)
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at he hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · have hr0' : (c.processes id).round + 1 = r₀ + 1 := by simpa using hr0
            exact Or.inr ⟨hid1, by omega, Option.some_inj.mp he⟩
        · rw [hProcNe i1 hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hIdCarr : ∀ bv, (c.processes id).estimate = some bv → OutcomeHolder P g c r id bv :=
      fun bv hoe => Or.inr ⟨hoe, Or.inl ⟨hr, Or.inr hph⟩⟩
    have hCommitW : ∀ r0 b0, (g r0).grade = some true → Grade2Commitment P g c r0 b0 →
        Grade2Commitment P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
      refine ⟨h1, fun r' id' b'' hrr' hmem hcall => h2 r' id' b'' hrr' (hFeq ▸ hmem) hcall,
        fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
      · by_cases hid : id' = id
        · rw [hid, hRoundEq] at hround
          by_cases hle : r0 < (c.processes id).round
          · have hold := h3 id (hFeq ▸ (hid ▸ hmem)) hle
            rw [hid]; simp [hold]
          · have hr0r : r0 = r := (by omega : r0 = (c.processes id).round).trans hr
            rw [hid]; simp only [hProcSelf]
            rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
            · exfalso
              obtain ⟨hg0', -⟩ :=
                (hI.estimate_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)).1 hoe
              rw [hr0r] at hg0
              exact absurd (hg0.symm.trans hg0') (by simp)
            · have hbv0 : bv = b0 :=
                h4 id bv (hFeq ▸ (hid ▸ hmem)) (hr0r ▸ hIdCarr bv hoe)
              simp [hoe, hbv0]
        · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
          exact h3 id' (hFeq ▸ hmem) hround
      · rcases hRedW r0 id0 v hcar with hold | ⟨heq0, hreq, hev⟩
        · exact h4 id0 v (hFeq ▸ hmem) hold
        · rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
          · obtain ⟨hg0', -⟩ :=
              (hI.estimate_ret r id (hFeq ▸ (heq0 ▸ hmem)) hr (Or.inr hph)).1 hoe
            rw [hreq] at hg0
            exact absurd (hg0.symm.trans hg0') (by simp)
          · have hv : v = bv := by rw [hoe] at hev; simpa using hev.symm
            rw [hv]
            exact h4 id bv (hFeq ▸ (heq0 ▸ hmem)) (hreq ▸ hIdCarr bv hoe)
    have hCertW : ∀ r0 b0,
        Grade2Certificate P g c r0 b0 → Grade2Certificate P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 ⟨hg0, hres0, hcm⟩
      exact ⟨hg0, hres0, hCommitW r0 b0 hg0 hcm⟩
    have hRedHW : ∀ i1 b1, Grade2Holder P (c.stepRound id b) i1 b1 → Grade2Holder P c i1 b1 := by
      intro i1 b1 h1
      rcases h1 with h1 | h1
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at h1; simp at h1
        · rw [hProcNe i1 hid1] at h1; exact Or.inl h1
      · rcases hDSeq with heq | ⟨b2, hlg, heq⟩
        · rw [heq] at h1; exact Or.inr h1
        · rw [heq] at h1
          by_cases hid1 : i1 = id
          · subst hid1
            rw [Function.update_self, Finset.mem_insert] at h1
            rcases h1 with rfl | h1
            · exact Or.inl hlg
            · exact Or.inr h1
          · rw [Function.update_of_ne hid1] at h1
            exact Or.inr h1
    rw [hc']
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertW r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hRedHW j b' hh)⟩
    refine ⟨fun id' => by
        rw [ABAState.stepRound_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r' => hFeq ▸ hI.F_gbca r', fun r' => (hFweq r').trans (hFeq ▸ hI.F_wcc r'),
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent,
      fun r' h => hI.wcc_bound r' (by rw [← hValeq r']; exact h),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.grade0Lock_chain, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r' v hb2 => (hI.bind_support r' v hb2).mono
        (fun id2 b2 h => by
          by_cases hid2 : id2 = id
          · rw [hid2, hInputEq]; exact hid2 ▸ h
          · rw [hProcNe id2 hid2]; exact h)
        (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r₀ i0 j0 v v' hm hm' h h' => by
        rcases hRedW r₀ i0 v h with hold0 | ⟨heq0, hreq0, hev0⟩
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · exact hI.outcomeHolder_agree r₀ i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm') hold0 hold1
          · rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.estimate_ret r id (hFeq ▸ (heq1 ▸ hm')) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq1]; exact hg0)
            · have hv' : v' = bv := by rw [hoe] at hev1; simpa using hev1.symm
              rw [hv']
              exact hI.outcomeHolder_agree r₀ i0 id v bv (hFeq ▸ hm) (hFeq ▸ (heq1 ▸ hm')) hold0
                (hreq1 ▸ hIdCarr bv hoe)
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.estimate_ret r id (hFeq ▸ (heq0 ▸ hm)) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq0]; exact hg0)
            · have hv0 : v = bv := by rw [hoe] at hev0; simpa using hev0.symm
              rw [hv0]
              exact hI.outcomeHolder_agree r₀ id j0 bv v' (hFeq ▸ (heq0 ▸ hm)) (hFeq ▸ hm')
                (hreq0 ▸ hIdCarr bv hoe) hold1
          · exact Or.inl (hev0.symm.trans hev1),
      fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hRedHW i0 b0 h) (hRedHW j0 b0' h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_gbcaRound0 id b' (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_called r' id (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_called r' id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h, hInputEq]; rw [h] at hmem
        exact hI.phase_input id (hFeq ▸ hmem) (by rw [hph]; simp)
      · rw [hProcNe id' h] at hne ⊢
        exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i j b' h
      rw [hDReq] at h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq]; exact hI.received_sound i j b' h
      · rw [heq]
        by_cases hji : j = id
        -- the sent set only grows (D12′): the old receipt stays covered
        · rw [hji] at h ⊢
          rw [Function.update_self]
          exact Finset.mem_insert_of_mem (hI.received_sound i id b' h)
        · rw [Function.update_of_ne hji]; exact hI.received_sound i j b' h
    · intro id' b' hmem h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq] at h
        exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
      · rw [heq] at h
        by_cases hid : id' = id
        · rw [hid, Function.update_self, Finset.mem_insert] at h
          rcases h with rfl | h
          · exact (hI.grade2_source id b' hlg).imp (fun r0 => hCertW r0 b')
          · exact (hI.decided_source id b' (hFeq ▸ hid ▸ hmem) h).imp (fun r0 => hCertW r0 b')
        · rw [Function.update_of_ne hid] at h
          exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
    · intro r0 b0 hgr hbr
      exact hCommitW r0 b0 hgr (hI.grade2Lock_commit r0 b0 hgr hbr)
    · intro id' hmem r' hround
      by_cases h : id' = id
      · rw [h] at hmem; rw [h, hRoundEq] at hround
        by_cases hr' : r' = (c.processes id).round
        · rw [hr', hr]; exact hI.wcc_bound r hWval
        · exact hI.round_bound id (hFeq ▸ hmem) r' (by omega)
      · rw [hProcNe id' h] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r' hround
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        by_cases hle : r' < (c.processes id).round
        · have hold := hI.agree_locked r' v hlast hbr hcoin id (hFeq ▸ (hid ▸ hmem)) hle
          rw [hid]; simp [hold]
        · have hr'eq : r' = (c.processes id).round := by omega
          have hr'r : r' = r := hr'eq.trans hr
          rw [hid]; simp only [hProcSelf]
          obtain ⟨hnone, hsome⟩ := hI.estimate_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
          by_cases holdE : (c.processes id).estimate = none
          · obtain ⟨hg0, -⟩ := hnone holdE
            have hbeqv : b = v := hCoinEq v (by rw [← hr'r]; exact hcoin)
            simp [holdE, hbeqv]
          · obtain ⟨bv, hbv⟩ := Option.ne_none_iff_exists'.mp holdE
            have hbveq := hsome bv hbv
            rw [hr'r] at hbr
            have hbv0 : bv = v := by
              by_contra hne
              have hv' : (!bv) = v := by
                revert hne; cases bv <;> cases v <;> simp
              exact hbr.2 (hv' ▸ hbveq)
            simp [hbv, hbv0]
      · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
        exact hI.agree_locked r' v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · exact hI.grade2_needs_bind
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcall
        exact le_trans (hI.call_round r' id (hFeq ▸ hmem) hcall) (by omega)
      · rw [hProcNe id' h]
        exact hI.call_round r' id' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcc_called r' id' (hFeq ▸ hmem) hcalled
    · intro r' id' hmem hround
      by_cases h : id' = id
      · rw [h, hRoundEq] at hround
        rw [hValeq]
        by_cases hlt : r' < (c.processes id).round
        · exact hI.round_flip r' id (hFeq ▸ (h ▸ hmem)) hlt
        · have hreq : r' = (c.processes id).round := by omega
          rw [hreq, hr]; exact hWval
      · rw [hProcNe id' h] at hround
        rw [hValeq]; exact hI.round_flip r' id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hRoundEq] at hround
        omega
      · rw [hProcNe id' h] at hround hphase ⊢
        exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · exfalso; rw [h, hProcSelf] at hlg; simp at hlg
      · rw [hProcNe id' h] at hlg
        exact (hI.grade2_source id' b' hlg).imp (fun r0 => hCertW r0 b')
    · intro r' id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hProcSelf] at hphase
        rcases hphase with hp | hp <;> simp at hp
      · rw [hProcNe id' h] at hround hphase
        rw [hProcNe id' h]
        exact hI.estimate_ret r' id' (hFeq ▸ hmem) hround hphase
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall
      rw [hValeq r']; exact hI.call_provenance r' id' v (hFeq ▸ hmem) hcall
    · intro r' id' hmem hround hphase v hest
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        have hreq : r' = r := by
          omega
        rw [hreq, hValeq r]
        have hveq : (c.processes id).estimate.getD b = v := by
          have hcopy := hest
          rw [hid, hProcSelf] at hcopy
          exact Option.some_inj.mp hcopy
        have hep := hI.estimate_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
        rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
        · rw [hoe] at hveq; simp at hveq
          obtain ⟨hg0, -⟩ := hep.1 hoe
          have hWtb : (w r).val = .top ∨ (w r).val = .bit b := by
            cases hstepW with | ret _ _ h1 _ => exact h1
          rw [← hveq]; exact Or.inr ⟨hg0, hWtb.symm⟩
        · rw [hoe] at hveq; simp at hveq
          have hbveq := hep.2 bv hoe
          rw [← hveq]; exact Or.inl hbveq
      · rw [hProcNe id' hid] at hround hphase hest
        rw [hValeq r']
        exact hI.estimate_previous r' id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases hid : id' = id
      · rw [hid, hProcSelf]; simp
      · rw [hProcNe id' hid] at hround hphase ⊢
        exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro r' h; rw [hValeq] at h ⊢; exact hI.wcc_order r' h
    · intro id' b' h
      by_cases hid : id' = id
      · rw [hid] at h ⊢
        rcases hI.input_gbcaRound0_permanent id b' h with hin | hf
        · left; rw [hInputEq]; exact hin
        · right; rw [hFeq]; exact hf
      · rw [hProcNe id' hid]
        rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
        · left; exact hin
        · right; rw [hFeq]; exact hf
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcalled
        exact le_trans (hI.wcc_callRound r' id (hFeq ▸ hmem) hcalled) (by omega)
      · rw [hProcNe id' h]
        exact hI.wcc_callRound r' id' (hFeq ▸ hmem) hcalled
    · intro r' h
      rw [hValeq] at h
      rcases hI.flip_grade2Lock r' h with hg | hd
      · left; exact hg
      · right
        refine DissentWitness.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
        by_cases hid2 : id2 = id
        · rw [hid2]; exact hInputEq
        · rw [hProcNe id2 hid2]
    · intro id' hmem hin r'
      rw [hCalledEq]
      by_cases h : id' = id
      · rw [h] at hmem hin
        rw [h]; rw [hInputEq] at hin
        exact hI.idle_no_wccCall id (hFeq ▸ hmem) hin r'
      · rw [hProcNe id' h] at hin
        exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r'
    · intro r' id' hmem hp
      by_cases hid : id' = id
      · rw [hid] at hmem hp
        rcases hp with ⟨hround, hphase⟩ | hlt0
        · exfalso
          rw [hProcSelf] at hphase
          rcases hphase with h | h <;> simp at h
        · rw [hRoundEq] at hlt0
          by_cases hlt : r' < (c.processes id).round
          · rcases hI.retG_witness r' id (hFeq ▸ hmem) (Or.inr hlt) with hg | hd
            · left; exact hg
            · right; exact hDR2 r' hd
          · have hreq : r' = r := by omega
            rcases hI.retG_witness r id (hFeq ▸ hmem) (Or.inl ⟨hr, Or.inr hph⟩) with hg | hd
            · left; rw [hreq]; exact hg
            · right; rw [hreq]; exact hDR2 r hd
      · rw [hProcNe id' hid] at hp
        rcases hI.retG_witness r' id' (hFeq ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDR2 r' hd
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      rcases hI.wccCalled_witness r' id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDR2 r' hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    refine And.intro ?_ (AbstractStateUnchanged.refl P g _)
    refine ⟨hI.corrupted_F, hI.F_gbca, fun r' => (hFweq r').trans (hI.F_wcc r'), hI.F_card,
      hI.input_gbcaRound0, hI.input_called, hI.phase_input, hI.down_settled, hI.quiescent,
      fun r' h => hI.wcc_bound r' (by rw [← hValeq r']; exact h),
      hI.received_sound, hI.decided_source, hI.grade2Lock_commit, hI.round_bound, ?_,
      hI.grade2_needs_bind, hI.call_round, ?_, ?_, hI.estimate0, hI.grade2_source, hI.estimate_ret,
      ?_, ?_, ?_, hI.grade0Lock_chain, hI.estimate_previous_ne,
      ?_, hI.input_gbcaRound0_permanent, ?_, ?_, ?_, hI.retG_witness, ?_, hI.bound_quorum,
      hI.bind_support, hI.grade0Lock_support, hI.excluded_support, hI.outcomeHolder_agree,
        hI.grade2Lock_agree⟩
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      exact hI.agree_locked r' v hlast hbr hcoin id' hmem hround
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcc_called r' id' hmem hcalled
    · intro r' id' hmem hround
      rw [hValeq]; exact hI.round_flip r' id' hmem hround
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall; rw [hValeq r']; exact hI.call_provenance r' id' v hmem hcall
    · intro r' id' hmem hround hphase v hest
      rw [hValeq r']; exact hI.estimate_previous r' id' hmem hround hphase v hest
    · intro r' h; rw [hValeq] at h ⊢; exact hI.wcc_order r' h
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcc_callRound r' id' hmem hcalled
    · intro r' h; rw [hValeq] at h; exact hI.flip_grade2Lock r' h
    · intro id' hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wccCall id' hmem hin r'
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wccCalled_witness r' id' hmem hcalled

end ABA
end PLTS
