/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Round.Pair
import Leslie2Protocols.ABA.Spec.GBCA
import Leslie2Protocols.Framework.FamilySim

/-!
# The GBCA core refinement: two gathers implement Transition System 2

`GBCA.pairRefines`: the GBCA-over-gather instance (`ABA/Round/Pair.lean`)
forward-simulates the unchanged GBCA specification instance
(`ABA/Spec/GBCA.lean`), along `GBCA.PairRel`.

Everything the specification tracks abstractly — the exclusion set `excluded`,
the grade lock, the D15 support counts — is discharged from the two gather
specifications' committed entries and frozen cores, by the counting kit of
`ABA/Round/Pair.lean`:

* a graded return's value is heavy in the second instance's core
  (`cnt_heavy_of_subMap` on the return's dominated core), and its candidate
  is heavy in the *first* instance's core, recorded by the invariant clause
  `cand_heavy` when the link row computed it;
* a bit heavy in the first core is the round's bound bit
  (`boundOfCore_of_heavy`), which pins the surviving bit: the exclusion
  `bindUnset (!v)` is fired inside the return run, and its `ExcludedEv`
  certificate — the first core counts `!v` below `|S| − f` — is
  `cnt_boundOfCore_light`;
* the A/C grade exclusivity is the second core being heavy at `some v` on the
  A side and light at both bits on the C side, which `|S| ≥ n − f > 2f`
  refutes;
* the D15 support counts are read off the core through the committed-entry
  provenance: a core entry is a committed entry, a committed entry of an
  honest process is its call, and the count is `F`-blind.

## The bound bit on the label

The return label carries the round's bound bit, the third factor of the pair
state. The relation clause `excluded_bound` says the specification's
`excluded` holds nothing but that bit's complement, so a return finds either
`(!bnd) ∈ excluded` already — and fires `ret` alone — or `excluded = ∅` — and
fires `bindUnset (!bnd) ; ret`. A value-bearing return's value is the bound
bit, by `boundOfCore_of_heavy` on the first core, so the specification's guard
pair `v ∉ excluded`, `(!v) ∈ excluded` is the same pair.

The runs are at most two steps — `bindUnset ; ret` through
`weakLStep_tauThen` — the long commit chains live one tier down, inside the
gather instances' own internal rows.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Gather

variable {P : Params}

/-! ### The invariant -/

/-- The `F`-blind committed-entry support count of a bit. -/
def supp1 (t1 : Gather.SpecState P.n Bool) (v : Bool) : ℕ :=
  (Finset.univ.filter (fun id => t1.val id = some v ∨ id ∈ t1.F)).card

/-- The invariant of the GBCA-over-gather instance. The provenance clauses
are the gather commit guards, per instance; `cand_heavy` and `cand_bot`
record, at the link row, what the computed candidate certifies about the
first instance; `call2_bound` and `bound_core` say that the same row writes
the bound bit and that the bit is read off the first instance's core; the
`core*` clauses re-state the freeze guards, which the write-once core keeps
true. -/
structure PairInv (P : Params) (s : PairState P.n) : Prop where
  /-- The corruption budget. -/
  F_card : s.1.F.card ≤ P.f
  /-- The two corrupted sets are in lockstep. -/
  F_eq12 : s.2.1.F = s.1.F
  /-- A committed first-instance entry of an honest process is its call. -/
  val1_prov : ∀ k v, s.1.val k = some v → k ∈ s.1.F ∨ s.1.call k = some v
  /-- A committed second-instance entry of an honest process is its call. -/
  val2_prov : ∀ k c, s.2.1.val k = some c → k ∈ s.1.F ∨ s.2.1.call k = some c
  /-- An honest bit candidate is heavy in the first instance's core. -/
  cand_heavy : ∀ k ∉ s.1.F, ∀ v, s.2.1.call k = some (some v) →
    ∃ S, s.1.core = some S ∧ S.card - P.f ≤ APSet.cnt S v
  /-- An honest `⊥` candidate certifies `f + 1` committed-entry support for
  both bits. -/
  cand_bot : ∀ k ∉ s.1.F, s.2.1.call k = some none →
    P.f + 1 ≤ supp1 s.1 true ∧ P.f + 1 ≤ supp1 s.1 false
  /-- A candidate at all certifies the bound bit is written: the link row
  writes the candidate and the bit together. -/
  call2_bound : ∀ k, s.2.1.call k ≠ none → s.2.2 ≠ none
  /-- The bound bit is the bound bit of the first instance's frozen core. -/
  bound_core : ∀ β, s.2.2 = some β →
    ∃ S, s.1.core = some S ∧ β = boundOfCore P S
  /-- The first instance's core is committed entries. -/
  core1_val : ∀ S, s.1.core = some S → S.subMap s.1.val
  /-- The first instance's core has `n − f` entries. -/
  core1_card : ∀ S, s.1.core = some S → P.n - P.f ≤ S.card
  /-- The second instance's core is committed entries. -/
  core2_val : ∀ S, s.2.1.core = some S → S.subMap s.2.1.val
  /-- The second instance's core has `n − f` entries. -/
  core2_card : ∀ S, s.2.1.core = some S → P.n - P.f ≤ S.card

/-- The invariant holds initially. -/
theorem PairInv.initial : PairInv P (PairState.initial P.n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PairState.initial, Gather.SpecState.initial]

/-- Committed entries only grow: an entry-wise extension preserves `supp1`
and every committed-entry fact. -/
private theorem supp1_mono {t t' : Gather.SpecState P.n Bool}
    (hval : ∀ k v, t.val k = some v → t'.val k = some v) (hF : t.F ⊆ t'.F)
    (v : Bool) : supp1 t v ≤ supp1 t' v := by
  refine Finset.card_le_card ?_
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  rcases hid.2 with h | h
  · exact ⟨hid.1, Or.inl (hval id v h)⟩
  · exact ⟨hid.1, Or.inr (hF h)⟩

/-- The invariant is preserved by every step. -/
theorem PairInv.step {r : ℕ} {s : PairState P.n} {l : Lab P.n}
    {μ : PMF (PairState P.n)} (hInv : PairInv P s) (hstep : PairStep P r s l μ)
    {s' : PairState P.n} (hs' : s' ∈ μ.support) : PairInv P s' := by
  cases hstep with
  | callG id b t1' h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨hInv.F_card, hInv.F_eq12, ?_, hInv.val2_prov, hInv.cand_heavy,
        hInv.cand_bot, hInv.call2_bound, hInv.bound_core, hInv.core1_val,
        hInv.core1_card, hInv.core2_val, hInv.core2_card⟩
      intro k v hv
      dsimp only at hv ⊢
      rcases hInv.val1_prov k v hv with hF | hcall'
      · exact Or.inl hF
      · right
        by_cases hk : k = id
        · subst hk
          rw [hcall] at hcall'
          exact absurd hcall' (by simp)
        · rw [Function.update_of_ne hk]
          exact hcall'
    | callLoop id' b' =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      exact hInv
  | ga1Tau t1' h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      have hvmono : ∀ k' v', s.1.val k' = some v' →
          Function.update s.1.val k (some v) k' = some v' := by
        intro k' v' hv'
        by_cases hk : k' = k
        · subst hk
          rw [hv] at hv'
          exact absurd hv' (by simp)
        · rw [Function.update_of_ne hk]
          exact hv'
      refine ⟨hInv.F_card, hInv.F_eq12, ?_, hInv.val2_prov, hInv.cand_heavy,
        ?_, hInv.call2_bound, hInv.bound_core, ?_, hInv.core1_card,
        hInv.core2_val, hInv.core2_card⟩
      · intro k' v' hv'
        dsimp only at hv'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self] at hv'
          have hveq : v = v' := by injection hv'
          subst hveq
          exact hm
        · rw [Function.update_of_ne hk] at hv'
          exact hInv.val1_prov k' v' hv'
      · intro k' hk' hc
        obtain ⟨h1, h2⟩ := hInv.cand_bot k' hk' hc
        constructor <;>
          exact le_trans (by assumption) (supp1_mono hvmono (by rfl) _)
      · intro S hS
        have hpre := hInv.core1_val S hS
        intro p hp
        exact hvmono p.1 p.2 (hpre p hp)
    | bindCore S h0 hval hcard =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        ?_, hInv.cand_bot, hInv.call2_bound, ?_, ?_, ?_,
        hInv.core2_val, hInv.core2_card⟩
      · intro k hk v hc
        obtain ⟨S', hS', -⟩ := hInv.cand_heavy k hk v hc
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro β hβ
        obtain ⟨S', hS', -⟩ := hInv.bound_core β hβ
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro S' hS'
        dsimp only at hS'
        obtain rfl : S = S' := by injection hS'
        exact hval
      · intro S' hS'
        dsimp only at hS'
        obtain rfl : S = S' := by injection hS'
        exact hcard
  | ga2Tau t2' h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, ?_, hInv.cand_heavy,
        hInv.cand_bot, hInv.call2_bound, hInv.bound_core, hInv.core1_val,
        hInv.core1_card, ?_, hInv.core2_card⟩
      · intro k' c' hc'
        dsimp only at hc'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self] at hc'
          have hceq : c = c' := by injection hc'
          subst hceq
          rcases hm with hF | hin
          · exact Or.inl (by rw [← hInv.F_eq12]; exact hF)
          · exact Or.inr hin
        · rw [Function.update_of_ne hk] at hc'
          exact hInv.val2_prov k' c' hc'
      · intro S hS
        have hpre := hInv.core2_val S hS
        intro p hp
        dsimp only
        by_cases hk : p.1 = k
        · rw [hk, Function.update_self]
          have := hpre p hp
          rw [hk] at this
          rw [hv] at this
          exact absurd this (by simp)
        · rw [Function.update_of_ne hk]
          exact hpre p hp
    | bindCore S h0 hval hcard =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        hInv.cand_heavy, hInv.cand_bot, hInv.call2_bound, hInv.bound_core,
        hInv.core1_val, hInv.core1_card, ?_, ?_⟩
      · intro S' hS'
        dsimp only at hS'
        obtain rfl : S = S' := by injection hS'
        exact hval
      · intro S' hS'
        dsimp only at hS'
        obtain rfl : S = S' := by injection hS'
        exact hcard
  | link id g C t1' h h2 =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      have hCcard : P.n - P.f ≤ C.card := hInv.core1_card C hC
      have hgdom : P.n - P.f ≤ gdom g :=
        le_trans hCcard (APSet.card_le_gdom hmem)
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, ?_, ?_, ?_, ?_, ?_,
        hInv.core1_val, hInv.core1_card, hInv.core2_val, hInv.core2_card⟩
      · intro k c hc
        rcases hInv.val2_prov k c hc with hF | hin
        · exact Or.inl hF
        · right
          dsimp only
          by_cases hk : k = id
          · subst hk
            rw [h2] at hin
            exact absurd hin (by simp)
          · rw [Function.update_of_ne hk]
            exact hin
      · intro k hk v hc
        dsimp only at hc
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hc
          have hcand : cand P g = some v := by injection hc
          exact ⟨C, hC, cnt_heavy_of_subMap hmem (cand_some hcand)⟩
        · rw [Function.update_of_ne hkid] at hc
          exact hInv.cand_heavy k hk v hc
      · intro k hk hc
        dsimp only at hc
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hc
          have hcand : cand P g = none := by injection hc
          have hbot := cand_none hcand
          have hsum := gdom_bool_sum g
          have hf := P.hf
          constructor
          · have hcnt : P.f + 1 ≤ gcount g true := by
              have := hbot false
              omega
            refine le_trans hcnt (Finset.card_le_card ?_)
            intro k' hk'
            rw [Finset.mem_filter] at hk' ⊢
            exact ⟨hk'.1, Or.inl (hsubv k' true hk'.2)⟩
          · have hcnt : P.f + 1 ≤ gcount g false := by
              have := hbot true
              omega
            refine le_trans hcnt (Finset.card_le_card ?_)
            intro k' hk'
            rw [Finset.mem_filter] at hk' ⊢
            exact ⟨hk'.1, Or.inl (hsubv k' false hk'.2)⟩
        · rw [Function.update_of_ne hkid] at hc
          exact hInv.cand_bot k hk hc
      · intro k _
        exact Option.some_ne_none _
      · intro β hβ
        dsimp only at hβ
        obtain rfl : s.2.2.getD (boundOfCore P C) = β := by injection hβ
        rcases hb : s.2.2 with _ | β₀
        · exact ⟨C, hC, rfl⟩
        · exact hInv.bound_core β₀ hb
  | retG id g C t2' h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      exact ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        hInv.cand_heavy, hInv.cand_bot, hInv.call2_bound, hInv.bound_core,
        hInv.core1_val, hInv.core1_card, hInv.core2_val, hInv.core2_card⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hFsub : s.1.F ⊆ (s.1.corrupt P id).F := by
      rw [Gather.SpecState.corrupt_F]
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
    have hF' : ∀ k, k ∉ (s.1.corrupt P id).F → k ∉ s.1.F :=
      fun k hk hkF => hk (hFsub hkF)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · rw [Gather.SpecState.corrupt_F]
      split
      · next hc =>
        have := Finset.card_insert_le id s.1.F
        have h2 := hc.2
        omega
      · exact hInv.F_card
    · rw [Gather.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hInv.F_eq12]
    · intro k v hv
      rw [Gather.corrupt_val] at hv
      rw [Gather.corrupt_call]
      rcases hInv.val1_prov k v hv with hF | hc
      · exact Or.inl (hFsub hF)
      · exact Or.inr hc
    · intro k c hc
      rw [Gather.corrupt_val] at hc
      rw [Gather.corrupt_call]
      rcases hInv.val2_prov k c hc with hF | hin
      · exact Or.inl (hFsub hF)
      · exact Or.inr hin
    · intro k hk v hc
      rw [Gather.corrupt_call] at hc
      obtain ⟨S, hS, hh⟩ := hInv.cand_heavy k (hF' k hk) v hc
      exact ⟨S, by rw [Gather.corrupt_core]; exact hS, hh⟩
    · intro k hk hc
      rw [Gather.corrupt_call] at hc
      obtain ⟨h1, h2⟩ := hInv.cand_bot k (hF' k hk) hc
      have hmono : supp1 s.1 true ≤ supp1 (s.1.corrupt P id) true ∧
          supp1 s.1 false ≤ supp1 (s.1.corrupt P id) false := by
        constructor <;>
          exact supp1_mono (by intro k' v' hv'; rw [Gather.corrupt_val]; exact hv') hFsub _
      exact ⟨le_trans h1 hmono.1, le_trans h2 hmono.2⟩
    · intro k hc
      rw [Gather.corrupt_call] at hc
      exact hInv.call2_bound k hc
    · intro β hβ
      obtain ⟨S, hS, hh⟩ := hInv.bound_core β hβ
      exact ⟨S, by rw [Gather.corrupt_core]; exact hS, hh⟩
    · intro S hS
      rw [Gather.corrupt_core] at hS
      have hpre := hInv.core1_val S hS
      intro p hp
      rw [Gather.corrupt_val]
      exact hpre p hp
    · intro S hS
      rw [Gather.corrupt_core] at hS
      exact hInv.core1_card S hS
    · intro S hS
      rw [Gather.corrupt_core] at hS
      have hpre := hInv.core2_val S hS
      intro p hp
      rw [Gather.corrupt_val]
      exact hpre p hp
    · intro S hS
      rw [Gather.corrupt_core] at hS
      exact hInv.core2_card S hS

/-! ### The discharge kit -/

/-- A filter of more than `f` processes contains an honest one. -/
private theorem exists_honest_filter {F : Finset (Fin P.n)} (hF : F.card ≤ P.f)
    {p : Fin P.n → Prop} [DecidablePred p]
    (h : P.f + 1 ≤ (Finset.univ.filter p).card) : ∃ k, p k ∧ k ∉ F := by
  have hlt : F.card < (Finset.univ.filter p).card := by omega
  obtain ⟨k, hk, hkF⟩ := SubState.exists_honest_of_card_lt hlt
  rw [Finset.mem_filter] at hk
  exact ⟨k, hk.2, hkF⟩

/-- Committed-entry support reads as call support on the specification side:
a committed entry of an honest process is its call, and the count is
`F`-blind. -/
private theorem spec_supp_of_supp1 {s : PairState P.n} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = s.1.call k) (hF : t.F = s.1.F)
    (hprov : ∀ k v, s.1.val k = some v → k ∈ s.1.F ∨ s.1.call k = some v)
    {v : Bool} (h : P.f + 1 ≤ supp1 s.1 v) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card := by
  refine le_trans h (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  refine ⟨hid.1, ?_⟩
  rcases hid.2 with hval | hFm
  · rcases hprov id v hval with hFm | hc
    · exact Or.inr (by rw [hF]; exact hFm)
    · exact Or.inl (by rw [hcall]; exact hc)
  · exact Or.inr (by rw [hF]; exact hFm)

/-- The core's value entries count into `supp1`. -/
private theorem cnt_le_supp1 {s : PairState P.n} {U : APSet P.n Bool}
    (hUval : U.subMap s.1.val) (v : Bool) :
    APSet.cnt U v ≤ supp1 s.1 v := by
  refine le_trans (APSet.cnt_le_gcount hUval v) (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, Or.inl hid.2⟩

/-- Core-heavy support reads as call support on the specification side. -/
private theorem supp_spec_of_core {s : PairState P.n} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = s.1.call k) (hF : t.F = s.1.F)
    (hprov : ∀ k v, s.1.val k = some v → k ∈ s.1.F ∨ s.1.call k = some v)
    {U : APSet P.n Bool} (hUval : U.subMap s.1.val) {v : Bool}
    (hcnt : P.f + 1 ≤ APSet.cnt U v) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card :=
  spec_supp_of_supp1 hcall hF hprov (le_trans hcnt (cnt_le_supp1 hUval v))

/-- The first instance's core discharges the specification's quorum guard:
its `n − f` distinct processes each carry a committed entry, hence a call or
a corruption. -/
private theorem quorum_of_core {s : PairState P.n} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = s.1.call k) (hF : t.F = s.1.F)
    (hprov : ∀ k v, s.1.val k = some v → k ∈ s.1.F ∨ s.1.call k = some v)
    {U : APSet P.n Bool} (hUval : U.subMap s.1.val)
    (hUcard : P.n - P.f ≤ U.card) : t.quorum P := by
  unfold GBCA.SpecState.quorum
  refine le_trans hUcard ?_
  have hinj : Set.InjOn Prod.fst ((U : Finset (Fin P.n × Bool)) : Set (Fin P.n × Bool)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    have h1 := hUval p hp
    have h2 := hUval q hq
    rw [hpq] at h1
    rw [h1] at h2
    have h3 : p.2 = q.2 := by injection h2
    exact Prod.ext hpq h3
  rw [← Finset.card_image_of_injOn hinj]
  refine Finset.card_le_card ?_
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  have h1 := hUval p hp
  rw [Finset.mem_union, Finset.mem_filter]
  rcases hprov p.1 p.2 h1 with hFm | hc
  · exact Or.inr (by rw [hF]; exact hFm)
  · by_cases hin : p.1 ∈ t.F
    · exact Or.inr hin
    · refine Or.inl ⟨Finset.mem_univ _, hin, ?_⟩
      rw [hcall, hc]
      simp

/-! ### The relation -/

/-- The exclusion certificate: the first instance's core counts `b` below
`|S| − f`, so no later candidate is `b`. Frozen — the core is write-once. -/
def ExcludedEv (P : Params) (s : PairState P.n) (b : Bool) : Prop :=
  ∃ S, s.1.core = some S ∧ APSet.cnt S b < S.card - P.f

/-- The GBCA core refinement relation. -/
structure PairRel (P : Params) (s : PairState P.n) (t : GBCA.SpecState P.n) : Prop where
  /-- The pair invariant. -/
  inv : PairInv P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = s.1.call k
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = s.2.1.ret id
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.1.F
  /-- An excluded bit is certified excluded. -/
  excluded_cert : ∀ b ∈ t.excluded, ExcludedEv P s b
  /-- An excluded bit is the complement of the round's bound bit: the
  exclusion is written inside the first return's run, which announces that
  bit. -/
  excluded_bound : ∀ b ∈ t.excluded, ∃ β, s.2.2 = some β ∧ b = !β
  /-- The `A` grade guard is certified by a value heavy in the second
  instance's core. -/
  gradeA_ev : t.grade = some true → ∃ S v, s.2.1.core = some S ∧
    S.card - P.f ≤ APSet.cnt S (some v)
  /-- The `C` grade guard is certified by the second instance's core being
  light at both bits. -/
  gradeC_ev : t.grade = some false → ∃ S, s.2.1.core = some S ∧
    ∀ v, APSet.cnt S (some v) ≤ P.f

/-- The relation holds initially. -/
theorem pairRel_init :
    PairRel P (PairState.initial P.n) (GBCA.SpecState.initial P.n) := by
  refine ⟨PairInv.initial, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PairState.initial, Gather.SpecState.initial, GBCA.SpecState.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem pairRel_corrupt {r : ℕ} {s : PairState P.n} {t : GBCA.SpecState P.n}
    (hR : PairRel P s t) (id : Fin P.n) :
    PairRel P (s.1.corrupt P id, s.2.1.corrupt P id, s.2.2) (t.corrupt P id) := by
  refine ⟨hR.inv.step (r := r) (PairStep.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [GBCA.corrupt_call]
    dsimp only
    rw [Gather.corrupt_call]
    exact hR.call_eq k
  · intro k
    rw [GBCA.corrupt_ret]
    dsimp only
    rw [Gather.corrupt_ret]
    exact hR.ret_eq k
  · show (t.corrupt P id).F = (s.1.corrupt P id).F
    rw [GBCA.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hR.F_eq]
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    obtain ⟨S, hS, hl⟩ := hR.excluded_cert b hb
    exact ⟨S, by dsimp only; rw [Gather.corrupt_core]; exact hS, hl⟩
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    exact hR.excluded_bound b hb
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, v, hS, hh⟩ := hR.gradeA_ev hg
    exact ⟨S, v, by dsimp only; rw [Gather.corrupt_core]; exact hS, hh⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, hS, hl⟩ := hR.gradeC_ev hg
    exact ⟨S, by dsimp only; rw [Gather.corrupt_core]; exact hS, hl⟩

/-! ### The refinement -/

/-- **The GBCA core refinement**: the GBCA-over-gather instance
forward-simulates the unchanged GBCA specification instance. -/
theorem pairRefines (P : Params) (r : ℕ) :
    ForwardSimulation (pairInst P r) (GBCA.specInst P r) (PairRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  rw [pairInst_step] at hstep
  have hInv' := hR.inv.step hstep hq₁'
  cases hstep with
  | callG id b t1' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall))⟩,
        hInv', ?_, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
      intro k
      dsimp only
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.call_eq k
    | callLoop id' b' =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (GBCA.Step.callLoop q₂ id b)⟩, hR⟩
  | ga1Tau t1' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
    | bindCore S h0 hval hcard =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
      intro b hb
      obtain ⟨S', hS', -⟩ := hR.excluded_cert b hb
      rw [h0] at hS'
      exact absurd hS' (by simp)
  | ga2Tau t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
    | bindCore S h0 hval hcard =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        ?_, ?_⟩
      · intro hg
        obtain ⟨S', v, hS', -⟩ := hR.gradeA_ev hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro hg
        obtain ⟨S', hS', -⟩ := hR.gradeC_ev hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
  | link id g C t1' h h2 =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.excluded_cert, ?_,
        hR.gradeA_ev, hR.gradeC_ev⟩
      intro b hb
      obtain ⟨β, hβ, hbβ⟩ := hR.excluded_bound b hb
      exact ⟨β, by dsimp only; rw [hβ]; rfl, hbβ⟩
  | retG id g C t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC₂ hmem₂ hsub₂ hr₂ =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      have hf := P.hf
      have hC₂card : P.n - P.f ≤ C.card := hR.inv.core2_card C hC₂
      have hgdom : P.n - P.f ≤ gdom g :=
        le_trans hC₂card (APSet.card_le_gdom hmem₂)
      have hretflag : q₂.ret id = false := by
        rw [hR.ret_eq id]
        exact hr₂
      have hchain : ∀ k, k ∉ q₁.1.F → ∀ c, g k = some c → q₁.2.1.call k = some c := by
        intro k hkF c hgc
        rcases hR.inv.val2_prov k c (hsub₂ k c hgc) with hF | hc
        · exact absurd hF hkF
        · exact hc
      -- the returner's round has linked, so the bound bit is written
      have hgdom_pos : P.f + 1 ≤ gdom g := by omega
      obtain ⟨k0, hk0, hk0F⟩ := exists_honest_filter
        (F := q₁.1.F) hR.inv.F_card (p := fun k => g k ≠ none) hgdom_pos
      rcases hgk0 : g k0 with _ | c0
      · exact absurd hgk0 hk0
      obtain ⟨β, hβ⟩ : ∃ β, q₁.2.2 = some β :=
        Option.ne_none_iff_exists'.mp
          (hR.inv.call2_bound k0 (by rw [hchain k0 hk0F c0 hgk0]; simp))
      obtain ⟨S, hS, hβS⟩ := hR.inv.bound_core β hβ
      have hScard : P.n - P.f ≤ S.card := hR.inv.core1_card S hS
      have hSval := hR.inv.core1_val S hS
      have hlight : ExcludedEv P q₁ (!β) :=
        ⟨S, hS, by rw [hβS]; exact cnt_boundOfCore_light hScard⟩
      have hexcl : ∀ b ∈ q₂.excluded, b = !β := by
        intro b hb
        obtain ⟨β', hβ', rfl⟩ := hR.excluded_bound b hb
        rw [hβ] at hβ'
        obtain rfl : β = β' := Option.some.inj hβ'
        rfl
      have hbndeq : q₁.2.2.getD (boundOfCore P (∅ : APSet P.n Bool)) = β := by
        rw [hβ]
        rfl
      rw [hbndeq]
      cases hout : gradeOf P g with
      | A v =>
        have hA_ev : C.card - P.f ≤ APSet.cnt C (some v) :=
          cnt_heavy_of_subMap hmem₂ (gradeOf_A hout)
        have hcnt_v : P.f + 1 ≤ gcount g (some v) := by
          have := gradeOf_A hout
          omega
        obtain ⟨kh, hkhg, hkhF⟩ := exists_honest_filter
          (F := q₁.1.F) hR.inv.F_card
          (p := fun k => g k = some (some v)) hcnt_v
        obtain ⟨S', hS', hheavy⟩ :=
          hR.inv.cand_heavy kh hkhF v (hchain kh hkhF (some v) hkhg)
        obtain rfl : S = S' := by rw [hS] at hS'; exact Option.some.inj hS'
        have hβv : β = v := by
          rw [hβS]
          exact boundOfCore_of_heavy hScard hheavy
        have hlive : v ∉ q₂.excluded := by
          intro hv
          have hb := hexcl v hv
          rw [hβv] at hb
          simp at hb
        have hgA : q₂.grade = none ∨ q₂.grade = some true := by
          rcases hgr : q₂.grade with _ | b
          · exact Or.inl rfl
          · cases b
            · exfalso
              obtain ⟨S₂, hS₂, hlight₂⟩ := hR.gradeC_ev hgr
              rw [hC₂] at hS₂
              obtain rfl : C = S₂ := Option.some.inj hS₂
              have := hlight₂ v
              omega
            · exact Or.inr rfl
        by_cases hbv : (!v) ∈ q₂.excluded
        · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (GBCA.Step.retA q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
              hgA hretflag)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, hR.excluded_cert,
            hR.excluded_bound, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro _
            exact ⟨C, v, hC₂, hA_ev⟩
          · intro hgr
            exact absurd hgr (by simp)
        · have hd0 : q₂.excluded = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro b' hb'
            have hb := hexcl b' hb'
            rw [hβv] at hb
            subst hb
            exact hbv hb'
          have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
              { q₂ with excluded := insert (!v) q₂.excluded } :=
            GBCA.Step.bindUnset q₂ (!v)
              (quorum_of_core hR.call_eq hR.F_eq hR.inv.val1_prov hSval hScard)
              (by
                rw [Bool.not_not]
                exact supp_spec_of_core hR.call_eq hR.F_eq hR.inv.val1_prov
                  hSval (by omega))
              hd0
          have hret2 : (GBCA.specInst P r).LStep
              { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.A v) β)
              { q₂ with
                excluded := insert (!v) q₂.excluded
                grade := some true
                ret := Function.update q₂.ret id true } :=
            GBCA.Step.retA _ id v β (by rw [hd0]; simp)
              (Finset.mem_insert_self _ _)
              (by rw [hβv]; exact Finset.mem_insert_self _ _) hgA hretflag
          refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, ?_, ?_, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro b hb
            rw [hd0, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · rw [← hβv]
              exact hlight
            · simp at hb
          · intro b hb
            rw [hd0, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · exact ⟨β, hβ, by rw [hβv]⟩
            · simp at hb
          · intro _
            exact ⟨C, v, hC₂, hA_ev⟩
          · intro hgr
            exact absurd hgr (by simp)
      | B v =>
        obtain ⟨hBcnt, hBnotA⟩ := gradeOf_B hout
        obtain ⟨kh, hkhg, hkhF⟩ := exists_honest_filter
          (F := q₁.1.F) hR.inv.F_card
          (p := fun k => g k = some (some v)) hBcnt
        obtain ⟨S', hS', hheavy⟩ :=
          hR.inv.cand_heavy kh hkhF v (hchain kh hkhF (some v) hkhg)
        obtain rfl : S = S' := by rw [hS] at hS'; exact Option.some.inj hS'
        have hβv : β = v := by
          rw [hβS]
          exact boundOfCore_of_heavy hScard hheavy
        have hlive : v ∉ q₂.excluded := by
          intro hv
          have hb := hexcl v hv
          rw [hβv] at hb
          simp at hb
        have hnv : P.f + 1 ≤ (Finset.univ.filter
            (fun k => g k ≠ none ∧ g k ≠ some (some v))).card := by
          rw [card_ne_gcount]
          have := hBnotA v
          omega
        obtain ⟨kd, hkd, hkdF⟩ := exists_honest_filter hR.inv.F_card hnv
        have hw : P.f + 1 ≤ (Finset.univ.filter
            (fun id' => q₂.call id' = some (!v) ∨ id' ∈ q₂.F)).card := by
          rcases hgkd : g kd with _ | c
          · exact absurd hgkd hkd.1
          have hcall2d := hchain kd hkdF c hgkd
          rcases c with _ | w
          · obtain ⟨hsT, hsF⟩ := hR.inv.cand_bot kd hkdF hcall2d
            cases v
            · exact spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hsT
            · exact spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hsF
          · exfalso
            have hwv : w ≠ v := by
              intro hwv
              subst hwv
              exact hkd.2 hgkd
            obtain ⟨S'', hS'', hheavy'⟩ := hR.inv.cand_heavy kd hkdF w hcall2d
            obtain rfl : S = S'' := by rw [hS] at hS''; exact Option.some.inj hS''
            refine hwv ?_
            rw [← boundOfCore_of_heavy hScard hheavy',
              boundOfCore_of_heavy hScard hheavy]
        by_cases hbv : (!v) ∈ q₂.excluded
        · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (GBCA.Step.retB q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
              hw hretflag)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, hR.excluded_cert,
            hR.excluded_bound, hR.gradeA_ev, hR.gradeC_ev⟩
          intro k
          dsimp only
          by_cases hk : k = id
          · subst hk
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hk, Function.update_of_ne hk]
            exact hR.ret_eq k
        · have hd0 : q₂.excluded = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro b' hb'
            have hb := hexcl b' hb'
            rw [hβv] at hb
            subst hb
            exact hbv hb'
          have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
              { q₂ with excluded := insert (!v) q₂.excluded } :=
            GBCA.Step.bindUnset q₂ (!v)
              (quorum_of_core hR.call_eq hR.F_eq hR.inv.val1_prov hSval hScard)
              (by
                rw [Bool.not_not]
                exact supp_spec_of_core hR.call_eq hR.F_eq hR.inv.val1_prov
                  hSval (by omega))
              hd0
          have hret2 : (GBCA.specInst P r).LStep
              { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.B v) β)
              { q₂ with
                excluded := insert (!v) q₂.excluded
                ret := Function.update q₂.ret id true } :=
            GBCA.Step.retB _ id v β (by rw [hd0]; simp)
              (Finset.mem_insert_self _ _)
              (by rw [hβv]; exact Finset.mem_insert_self _ _) hw hretflag
          refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, ?_, ?_, hR.gradeA_ev,
            hR.gradeC_ev⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro b hb
            rw [hd0, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · rw [← hβv]
              exact hlight
            · simp at hb
          · intro b hb
            rw [hd0, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · exact ⟨β, hβ, by rw [hβv]⟩
            · simp at hb
      | C =>
        have hCgrade := gradeOf_C hout
        have hClight : ∀ w, APSet.cnt C (some w) ≤ P.f := fun w =>
          le_trans (APSet.cnt_le_gcount hmem₂ (some w)) (hCgrade w)
        have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
            (fun id' => q₂.call id' = some b ∨ id' ∈ q₂.F)).card := by
          intro b
          have hcard : P.f + 1 ≤ (Finset.univ.filter
              (fun k => g k ≠ none ∧ g k ≠ some (some (!b)))).card := by
            rw [card_ne_gcount]
            have := hCgrade (!b)
            omega
          obtain ⟨kt, hkt, hktF⟩ := exists_honest_filter hR.inv.F_card hcard
          rcases hgkt : g kt with _ | ct
          · exact absurd hgkt hkt.1
          have hcall2t := hchain kt hktF ct hgkt
          rcases ct with _ | wt
          · obtain ⟨hsT, hsF⟩ := hR.inv.cand_bot kt hktF hcall2t
            cases b
            · exact spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hsF
            · exact spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hsT
          · have hwt : wt = b := by
              by_contra hne
              have hb : wt = !b := by cases wt <;> cases b <;> simp_all
              subst hb
              exact hkt.2 hgkt
            subst hwt
            obtain ⟨S'', hS'', hh⟩ := hR.inv.cand_heavy kt hktF wt hcall2t
            obtain rfl : S = S'' := by rw [hS] at hS''; exact Option.some.inj hS''
            exact supp_spec_of_core hR.call_eq hR.F_eq hR.inv.val1_prov
              hSval (by omega)
        have hgC : q₂.grade = none ∨ q₂.grade = some false := by
          rcases hgr : q₂.grade with _ | b
          · exact Or.inl rfl
          · cases b
            · exact Or.inr rfl
            · exfalso
              obtain ⟨S₂, v', hS₂, hh⟩ := hR.gradeA_ev hgr
              rw [hC₂] at hS₂
              obtain rfl : C = S₂ := Option.some.inj hS₂
              have := hClight v'
              omega
        by_cases hdne : q₂.excluded = ∅
        · have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
              { q₂ with excluded := insert (!β) q₂.excluded } :=
            GBCA.Step.bindUnset q₂ (!β)
              (quorum_of_core hR.call_eq hR.F_eq hR.inv.val1_prov hSval hScard)
              (by rw [Bool.not_not]; exact hsupp β)
              hdne
          have hret2 : (GBCA.specInst P r).LStep
              { q₂ with excluded := insert (!β) q₂.excluded } (.retG r id .C β)
              { q₂ with
                excluded := insert (!β) q₂.excluded
                grade := some false
                ret := Function.update q₂.ret id true } :=
            GBCA.Step.retC _ id β (Finset.mem_insert_self _ _)
              (hsupp true) (hsupp false) hgC hretflag
          refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, ?_, ?_, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro b hb
            rw [hdne, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · exact hlight
            · simp at hb
          · intro b hb
            rw [hdne, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · exact ⟨β, hβ, rfl⟩
            · simp at hb
          · intro hgr
            exact absurd hgr (by simp)
          · intro _
            exact ⟨C, hC₂, hClight⟩
        · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hdne
          have hbeq := hexcl b hb
          subst hbeq
          refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (GBCA.Step.retC q₂ id β hb (hsupp true) (hsupp false) hgC hretflag)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, hR.excluded_cert,
            hR.excluded_bound, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro hgr
            exact absurd hgr (by simp)
          · intro _
            exact ⟨C, hC₂, hClight⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (GBCA.Step.fail q₂ id)⟩, pairRel_corrupt (r := r) hR id⟩

/-- info: 'PLTS.ABA.GBCA.pairRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairRefines

end GBCA
end ABA
end PLTS
