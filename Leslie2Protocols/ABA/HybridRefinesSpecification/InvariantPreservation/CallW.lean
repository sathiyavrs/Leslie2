/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# `Invariant` across the `callW` rows of `hybrid`

`Invariant.step_callW`, preservation of `Invariant` at a call of the coin, assembled from the three
rows of `WCC.step_callW_inversion`. The input-enabledness loop and the recording call leave `val`
and `F` alone, the coin instance touching only `.called` and the core only `.phase`, both at `id`
and neither inspected by `Invariant` (`Invariant.step_callW_dirac`). The resolving call records
`id` by that same bookkeeping and writes the drawn outcome to `val`
(`Invariant.step_callW_resolve`), where the clauses reading `(w r).val` come back from the
threshold: `Invariant.exists_correct_wccCaller` supplies a never-corrupted caller of round `r`,
whose `wcc_called`, `wcc_callRound` and `wccCalled_witness` carry `wcc_bound`, `wcc_order` and
`flip_grade2Lock`. `agree_locked`'s round-`r` corner is vacuous: `round_flip` at a never-corrupted
process past round `r` contradicts `val = ⊥`. The record of `id` and the write to `val` compose
into one update, `Function.update` being idempotent at the round it writes.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- A round whose caller count has passed `f` has a never-corrupted caller: the callers
outnumber the corrupted set, which `F_card` bounds by `f`. -/
theorem Invariant.exists_correct_wccCaller {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) {r : ℕ}
    (hq : (w r).threshold P) : ∃ id, id ∉ c.F ∧ (w r).called id = true := by
  by_contra hcon
  have hsub : (Finset.univ.filter (fun id => (w r).called id)) ⊆ c.F := by
    intro id hid
    rw [Finset.mem_filter] at hid
    by_contra hF
    exact hcon ⟨id, hF, hid.2⟩
  have hcard := Finset.card_le_card hsub
  have hFcard := hI.F_card
  rw [WCC.SpecState.threshold] at hq
  omega

/-- The resolving row of `callW`: `Invariant` is preserved when the drawn outcome is written to
`val` at a round whose caller count has passed `f`. -/
theorem Invariant.step_callW_resolve {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ)
    (hq : (w r).threshold P) (hv : (w r).val = .bot) (o : CoinOutcome) :
    Invariant P g c (Function.update w r { w r with val := o.toCoinValue }) := by
  set w' := Function.update w r { w r with val := o.toCoinValue } with hw'def
  have hFeq : ∀ r', (w' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [hw'def, Function.update_self]
    · rw [hw'def, Function.update_of_ne h]
  have hValNe : ∀ r', r' ≠ r → (w' r').val = (w r').val := by
    intro r' h; rw [hw'def, Function.update_of_ne h]
  have hValSelf : (w' r).val = o.toCoinValue := by
    rw [hw'def, Function.update_self]
  have hCalledEq : ∀ r', (w' r').called = (w r').called := by
    intro r'; by_cases h : r' = r
    · subst h; rw [hw'def, Function.update_self]
    · rw [hw'def, Function.update_of_ne h]
  refine ⟨hI.corrupted_F, hI.F_gbca, fun r' => (hFeq r').trans (hI.F_wcc r'), hI.F_card,
    hI.input_gbcaRound0,
    hI.input_called, hI.phase_input, hI.down_settled, hI.quiescent, ?_, hI.received_sound,
    hI.decided_source, hI.grade2Lock_commit, hI.round_bound, ?_, hI.grade2_needs_bind,
      hI.call_round, ?_, ?_,
    hI.estimate0, hI.grade2_source, hI.estimate_ret, ?_, ?_, ?_, hI.grade0Lock_chain,
      hI.estimate_previous_ne,
    ?_, hI.input_gbcaRound0_permanent, ?_, ?_, ?_, hI.retG_witness, ?_, hI.bound_quorum,
    hI.bind_support, hI.grade0Lock_support, hI.excluded_support, hI.outcomeHolder_agree,
      hI.grade2Lock_agree⟩
  · intro r' h
    by_cases h2 : r' = r
    · obtain ⟨id0, hid0cF, hid0called⟩ :=
        hI.exists_correct_wccCaller (r := r') (by rw [h2]; exact hq)
      exact hI.wcc_called r' id0 hid0cF hid0called
    · rw [hValNe r' h2] at h; exact hI.wcc_bound r' h
  · intro r' v hlast hbr hcoin id hmem hround
    by_cases h2 : r' = r
    · have hround' : r < (c.processes id).round := by rw [← h2]; exact hround
      exact absurd hv (hI.round_flip r id hmem hround')
    · rw [hValNe r' h2] at hcoin
      exact hI.agree_locked r' v hlast hbr hcoin id hmem hround
  · intro r' id hmem hcalled
    rw [hCalledEq] at hcalled; exact hI.wcc_called r' id hmem hcalled
  · intro r' id hmem hround
    by_cases h2 : r' = r
    · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toCoinValue]
    · rw [hValNe r' h2]; exact hI.round_flip r' id hmem hround
  · intro r' v h
    have hb := hI.bind_succ r' v h
    by_cases h2 : r' = r
    · rw [h2] at hb ⊢
      rcases hb with hbv | ⟨hg0, hw0⟩
      · exact Or.inl hbv
      · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
    · rw [hValNe r' h2]; exact hb
  · intro r' id v hmem hcall
    have hcp := hI.call_provenance r' id v hmem hcall
    by_cases h2 : r' = r
    · rw [h2] at hcp ⊢
      rcases hcp with hbv | ⟨hg0, hw0⟩
      · exact Or.inl hbv
      · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
    · rw [hValNe r' h2]; exact hcp
  · intro r' id hmem hround hphase v hest
    have hep := hI.estimate_previous r' id hmem hround hphase v hest
    by_cases h2 : r' = r
    · rw [h2] at hep ⊢
      rcases hep with hbv | ⟨hg0, hw0⟩
      · exact Or.inl hbv
      · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
    · rw [hValNe r' h2]; exact hep
  · -- `wcc_order`: pass-through, except at round `r`'s predecessor, where the correct caller
    -- of round `r` has already passed round `r - 1`, so `round_flip` applies to it.
    intro r' h
    by_cases h2 : r' = r
    · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toCoinValue]
    · by_cases h1 : r' + 1 = r
      · obtain ⟨id0, hid0cF, hid0called⟩ := hI.exists_correct_wccCaller (r := r) hq
        have hcr := hI.wcc_callRound r id0 hid0cF hid0called
        rw [hValNe r' h2]
        exact hI.round_flip r' id0 hid0cF (by omega)
      · rw [hValNe (r' + 1) h1] at h; rw [hValNe r' h2]; exact hI.wcc_order r' h
  · intro r' id hmem hcalled; rw [hCalledEq] at hcalled; exact hI.wcc_callRound r' id hmem hcalled
  · -- `flip_grade2Lock`'s establishment: round `r`'s correct caller feeds `wccCalled_witness`
    -- directly.
    intro r' h
    by_cases h2 : r' = r
    · obtain ⟨id0, hid0cF, hid0called⟩ :=
        hI.exists_correct_wccCaller (r := r') (by rw [h2]; exact hq)
      exact hI.wccCalled_witness r' id0 hid0cF hid0called
    · rw [hValNe r' h2] at h; exact hI.flip_grade2Lock r' h
  · intro id hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wccCall id hmem hin r'
  · intro r' id hmem hcalled
    rw [hCalledEq] at hcalled; exact hI.wccCalled_witness r' id hmem hcalled

/-- The Dirac rows of `callW`, the input-enabledness loop and the recording call: `Invariant` is
preserved and the abstract state is unchanged. -/
theorem Invariant.step_callW_dirac {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    {wr' : WCC.SpecState P.n} (hWF : wr'.F = (w r).F) (hWval : wr'.val = (w r).val)
    (hWcalled : ∀ j, j ≠ id → wr'.called j = (w r).called j)
    {c' : ABAState P}
    (hCstep : ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
        c' = c.setProcess id { c.processes id with phase := .awaitW }) ∨ (id ∈ c.F ∧ c' = c)) :
    Invariant P g c' (Function.update w r wr') ∧ AbstractStateUnchanged P g g c c' := by
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hWF
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hWval
    · rw [hWNe r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedReceived =
    c.decidedReceived ∧
      ∀ id',
        (c'.processes id').input = (c.processes id').input ∧ (c'.processes id').estimate =
          (c.processes id').estimate ∧ (c'.processes id').round = (c.processes id').round := by
    rcases hCstep with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · refine ⟨ABAState.setProcess_F _ _ _, ABAState.setProcess_decidedSent _ _ _,
        ABAState.setProcess_decidedReceived _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [ABAState.setProcess_processes_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hLastGrade : ∀ id', (c'.processes id').lastGrade = (c.processes id').lastGrade := by
    rcases hCstep with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]
      · rw [ABAState.setProcess_processes_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarr : ∀ r₀ id₀ v, OutcomeHolder P g c' r₀ id₀ v → OutcomeHolder P g c r₀ id₀ v := by
    intro r₀ id₀ v hc0
    rcases hc0 with h | ⟨he, hk⟩
    · exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCstep with ⟨hph, hrid, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, ABAState.setProcess_processes_self] at hk
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · exact Or.inl ⟨hr0, Or.inl hph⟩
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCert : ∀ r' b', Grade2Certificate P g c r' b' → Grade2Certificate P g c' r' b' :=
    fun r' b' => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hCF] : c.F ⊆ _) (fun id' => (hCprocs id').2.2) (fun id' => (hCprocs id').2.1)
      (fun id0 v => hCarr r' id0 v)
  have hHold : ∀ i0 b0, Grade2Holder P c' i0 b0 → Grade2Holder P c i0 b0 := by
    intro i0 b0 h
    unfold Grade2Holder at h ⊢
    rwa [hLastGrade, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  have hCcorr : c'.corrupted = c.corrupted := by
    rcases hCstep with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · rw [hc'eq]; exact ABAState.setProcess_corrupted _ _ _
    · rw [hc'eq]
  refine ⟨fun id' => by rw [hCcorr, hCF]; exact hI.corrupted_F id',
    fun r' => hCF ▸ hI.F_gbca r', fun r' => (hFweq r').trans (hCF ▸ hI.F_wcc r'),
    hCF ▸ hI.F_card,
    ?_, ?_, ?_, hI.down_settled, hI.quiescent, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.grade0Lock_chain, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
    fun r' v hb => (hI.bind_support r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    hI.grade0Lock_support, hI.excluded_support,
    fun r₀ i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarr _ _ _ h) (hCarr _ _ _ h'),
    fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall; rw [(hCprocs id').1]; exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem)
      hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.processes id').phase ≠ .idle := by
          rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · intro r' h; rw [hValeq] at h; exact hI.wcc_bound r' h
  · intro i j b h; rw [hCDR] at h; rw [hCDS]; exact hI.received_sound i j b h
  · intro id' b' hmem h; rw [hCDS] at h
    exact (hI.decided_source id' b' (hCF ▸ hmem) h).imp (fun r' => hCert r' b')
  · intro r' b' hgr hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r' b' hgr hbr
    refine ⟨h1, fun r'' id' b'' hr hmem hcall => h2 r'' id' b'' hr (hCF ▸ hmem) hcall,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem) (hCarr r' id0 v hcar)⟩
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround; exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    rw [hValeq] at hcoin; rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' id' hmem hcall
    rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · obtain ⟨hnone, hsome⟩ := hI.estimate_ret r id (hCF ▸ hmem) hr (Or.inl hph)
          by_cases hE : (c.processes id).estimate = none
          · exact Or.inr (hnone hE).1
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hE
            exact Or.inl (fun hemp => by
              have hm := hsome b hb
              rw [hemp] at hm
              simp at hm)
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [hWcalled id' hid] at hcalled
        exact hI.wcc_called r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled; exact hI.wcc_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [hValeq]; rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGrade] at hlg
    exact (hI.grade2_source id' b' hlg).imp (fun r' => hCert r' b')
  · intro r' id' hmem hround hphase
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.processes id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, ABAState.setProcess_processes_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        rw [hid, hreq, (hCprocs id).2.1]
        exact hI.estimate_ret r id (hCF ▸ (hid ▸ hmem)) hr (Or.inl hph)
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        exact hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      exact hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
  · intro r' v h; rw [hValeq]; exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall; rw [hValeq]; exact hI.call_provenance r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest; rw [hValeq]
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1]
        exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1]
      exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
  · intro r' h; rw [hValeq] at h ⊢; exact hI.wcc_order r' h
  · intro id' b' h
    rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · -- `wcc_callRound`'s establishment: a correct caller of `WCC_r` just finished `GBCA_r`
    -- (`r ≤ round` from `hr : (c.processes id).round = r`, unaffected by `callW`).
    intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [hWcalled id' hid] at hcalled
        rw [(hCprocs id').2.2]; exact hI.wcc_callRound r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled
      rw [(hCprocs id').2.2]; exact hI.wcc_callRound r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rw [hValeq] at h
    rcases hI.flip_grade2Lock r' h with hg | hd
    · left; exact hg
    · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    by_cases h2 : r' = r
    · rw [h2, Function.update_self]
      rw [(hCprocs id').1] at hin
      by_cases hid : id' = id
      · exfalso
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rw [hid] at hin
          have hmem' : id ∉ c.F := by
            rw [← hCF, ← hid]; exact hmem
          exact absurd hin (hI.phase_input id hmem' (by rw [hph]; simp))
        · rw [hid] at hmem; exact hmem (hCF ▸ hF)
      · rw [hWcalled id' hid]
        exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r
    · rw [hWNe r' h2]
      rw [(hCprocs id').1] at hin
      exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hphaseImp : ((c'.processes id').phase = .toCallW ∨ (c'.processes id').phase = .awaitW) →
        ((c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW) := by
      intro hph2
      rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id' = id
        · exact Or.inl (hid ▸ hph)
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hph2; exact hph2
      · rw [hc'eq] at hph2; exact hph2
    have hp' : ((c.processes id').round = r' ∧
        ((c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW)) ∨
        r' < (c.processes id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · exact Or.inl ⟨hround, hphaseImp hphase⟩
      · exact Or.inr hlt
    rcases hI.retG_witness r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rcases hI.retG_witness r id (hCF ▸ hmem) (Or.inl ⟨hr, Or.inl hph⟩) with hg | hd
          · left; exact hg
          · right
            exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [hWcalled id' hid] at hcalled
        rcases hI.wccCalled_witness r id' (hCF ▸ hmem) hcalled with hg | hd
        · left; exact hg
        · right
          exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
    · rw [hWNe r' h2] at hcalled
      rcases hI.wccCalled_witness r' id' (hCF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd

/-- `callW`: `Invariant` is preserved and the abstract state is unchanged at a call of the
coin. -/
theorem Invariant.step_callW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcess id { c.processes id with phase := .awaitW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' (Function.update w r wr') ∧ AbstractStateUnchanged P g g c c' := by
  have hCstep : ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
      c' = c.setProcess id { c.processes id with phase := .awaitW }) ∨ (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  rcases WCC.step_callW_inversion hstepW with rfl | ⟨-, -, rfl⟩ | ⟨-, hv, ht, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'
    exact hI.step_callW_dirac r id rfl rfl (fun _ _ => rfl) hCstep
  · rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'
    exact hI.step_callW_dirac (wr' := (w r).record id) r id rfl rfl
      (fun j hj => WCC.SpecState.record_called_ne _ hj) hCstep
  · rw [PMF.mem_support_map_iff] at hwr'
    obtain ⟨o, -, rfl⟩ := hwr'
    obtain ⟨hI₁, hAF⟩ := hI.step_callW_dirac (wr' := (w r).record id) r id rfl rfl
      (fun j hj => WCC.SpecState.record_called_ne _ hj) hCstep
    refine ⟨?_, hAF⟩
    have hw₁ : Function.update w r ((w r).record id) r = (w r).record id := by
      rw [Function.update_self]
    have hres := hI₁.step_callW_resolve r (by rw [hw₁]; exact ht) (by rw [hw₁]; simpa using hv) o
    rw [hw₁, Function.update_idem] at hres
    exact hres

end ABA
end PLTS
