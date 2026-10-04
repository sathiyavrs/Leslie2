/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation

/-!
# `Invariant` across the coin's resolution in `hybrid`

`Invariant.step_resolve`, preservation of `Invariant` at the silent resolution of the coin. The
resolution of round `r` is enabled at `val = ⊥` once more than `f` processes have called round `r`,
and it writes the drawn outcome to `val`. The clauses reading `(w r).val` come back from the
threshold: `Invariant.exists_correct_wccCaller` supplies a never-corrupted caller of round `r`,
whose `wcc_called`, `wcc_callRound` and `wccCalled_witness` carry `wcc_bound`, `wcc_order` and
`flip_witness`. `agree_bound`'s round-`r` corner is vacuous: `round_flip` at a never-corrupted
process past round `r` contradicts `val = ⊥`. The resolution leaves `called`, `F`, `g`, the
round loops and the ABA network unchanged, so every other clause passes through.
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

/-- The coin's resolution: `Invariant` is preserved when the drawn outcome is written to `val` at a
round whose caller count has passed `f`. -/
theorem Invariant.step_resolve {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
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
    hI.decided_source, hI.grade2Bound_commit, hI.round_bound, ?_, hI.grade2_needs_bind,
      hI.call_round, ?_, ?_,
    hI.estimate0, hI.grade2_source, hI.estimate_ret, ?_, ?_, ?_, hI.grade0_chain,
      hI.estimate_previous_ne,
    ?_, hI.input_gbcaRound0_permanent, ?_, ?_, ?_, hI.retG_witness, ?_, hI.bound_quorum,
    hI.bind_support, hI.grade0_support, hI.excluded_support, hI.outcomeHolder_agree,
      hI.grade2Bound_agree⟩
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
      exact hI.agree_bound r' v hlast hbr hcoin id hmem hround
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
    have hcp := hI.call_of_previousRound r' id v hmem hcall
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
  · -- `flip_witness`'s establishment: round `r`'s correct caller feeds `wccCalled_witness`
    -- directly.
    intro r' h
    by_cases h2 : r' = r
    · obtain ⟨id0, hid0cF, hid0called⟩ :=
        hI.exists_correct_wccCaller (r := r') (by rw [h2]; exact hq)
      exact hI.wccCalled_witness r' id0 hid0cF hid0called
    · rw [hValNe r' h2] at h; exact hI.flip_witness r' h
  · intro id hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wccCall id hmem hin r'
  · intro r' id hmem hcalled
    rw [hCalledEq] at hcalled; exact hI.wccCalled_witness r' id hmem hcalled

end ABA
end PLTS
