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

Everything the specification tracks abstractly — the exclusion set `dead`,
the grade lock, the D15 support counts — is discharged from the two gather
specifications' committed entries and frozen core families, by the member
arithmetic of `ABA/Round/Pair.lean`:

* a graded return's value is heavy in a member of the second family
  (`cnt_heavy_of_subMap` on the return's dominated member), and its
  candidate is heavy in a member of the *first* family, recorded by the
  invariant clause `cand_heavy` when the link row computed it;
* values heavy in two members of one family agree (`members_agree` on the
  pairwise `n − f ≥ 2f + 1` shared entries), which pins the surviving bit:
  the exclusion set's kill `bindUnset (!v)` is fired inside the return burst,
  its `DeadEv` certificate — every first-family member counts `!v` below
  `|U| − f` — following from the agreement;
* the A/C grade exclusivity is `members_heavy_light` between the A-side heavy
  member and the C-side everywhere-light member of the second family;
* the D15 support counts are read off members through the committed-entry
  provenance: a member entry is a committed entry, a committed entry of an
  honest process is its call, and the count is `F`-blind.

The bursts are at most two steps — `bindUnset ; ret` through
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
are the gather commit guards, per instance; `cand_heavy`, `cand_bot` and
`cand_cores` record, at the link row, what the computed candidate certifies
about the first instance; the `cores*` clauses re-state the freeze guards,
which the write-once family keeps true. -/
structure PairInv (P : Params) (s : PairState P.n) : Prop where
  /-- The corruption budget. -/
  F_card : s.1.F.card ≤ P.f
  /-- The two corrupted sets are in lockstep. -/
  F_eq12 : s.2.F = s.1.F
  /-- A committed first-instance entry of an honest process is its call. -/
  val1_prov : ∀ k v, s.1.val k = some v → k ∈ s.1.F ∨ s.1.call k = some v
  /-- A committed second-instance entry of an honest process is its call. -/
  val2_prov : ∀ k c, s.2.val k = some c → k ∈ s.1.F ∨ s.2.call k = some c
  /-- An honest bit candidate is heavy in a member of the first family. -/
  cand_heavy : ∀ k ∉ s.1.F, ∀ v, s.2.call k = some (some v) →
    ∃ Cs U, s.1.cores = some Cs ∧ U ∈ Cs ∧ U.card - P.f ≤ APSet.cnt U v
  /-- An honest `⊥` candidate certifies `f + 1` committed-entry support for
  both bits. -/
  cand_bot : ∀ k ∉ s.1.F, s.2.call k = some none →
    P.f + 1 ≤ supp1 s.1 true ∧ P.f + 1 ≤ supp1 s.1 false
  /-- Any candidate at all certifies the first family is frozen. -/
  cand_cores : ∀ k ∉ s.1.F, s.2.call k ≠ none → ∃ Cs, s.1.cores = some Cs
  /-- The first family is nonempty. -/
  cores1_ne : ∀ Cs, s.1.cores = some Cs → Cs.Nonempty
  /-- First-family members are committed entries. -/
  cores1_val : ∀ Cs, s.1.cores = some Cs → ∀ U ∈ Cs, U.subMap s.1.val
  /-- First-family members pairwise share `n − f` entries. -/
  cores1_pair : ∀ Cs, s.1.cores = some Cs →
    ∀ U ∈ Cs, ∀ V ∈ Cs, P.n - P.f ≤ (U ∩ V).card
  /-- The second family is nonempty. -/
  cores2_ne : ∀ Cs, s.2.cores = some Cs → Cs.Nonempty
  /-- Second-family members are committed entries. -/
  cores2_val : ∀ Cs, s.2.cores = some Cs → ∀ U ∈ Cs, U.subMap s.2.val
  /-- Second-family members pairwise share `n − f` entries. -/
  cores2_pair : ∀ Cs, s.2.cores = some Cs →
    ∀ U ∈ Cs, ∀ V ∈ Cs, P.n - P.f ≤ (U ∩ V).card

/-- The invariant holds initially. -/
theorem PairInv.initial : PairInv P (PairState.initial P.n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
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
        hInv.cand_bot, hInv.cand_cores, hInv.cores1_ne, hInv.cores1_val,
        hInv.cores1_pair, hInv.cores2_ne, hInv.cores2_val, hInv.cores2_pair⟩
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
        ?_, hInv.cand_cores, hInv.cores1_ne, ?_, hInv.cores1_pair,
        hInv.cores2_ne, hInv.cores2_val, hInv.cores2_pair⟩
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
      · intro Cs hCs U hU
        have hpre := hInv.cores1_val Cs hCs U hU
        intro p hp
        exact hvmono p.1 p.2 (hpre p hp)
    | bindCores Cs h0 hne hval hpair =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        ?_, hInv.cand_bot, ?_, ?_, ?_, ?_, hInv.cores2_ne, hInv.cores2_val,
        hInv.cores2_pair⟩
      · intro k hk v hc
        obtain ⟨Cs', U', hCs', -, -⟩ := hInv.cand_heavy k hk v hc
        rw [h0] at hCs'
        exact absurd hCs' (by simp)
      · intro k hk hc
        exact ⟨Cs, rfl⟩
      · intro Cs' hCs'
        dsimp only at hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        exact hne
      · intro Cs' hCs' U hU
        dsimp only at hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        exact hval U hU
      · intro Cs' hCs' U hU V hV
        dsimp only at hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        exact hpair U hU V hV
  | ga2Tau t2' h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, ?_, hInv.cand_heavy,
        hInv.cand_bot, hInv.cand_cores, hInv.cores1_ne, hInv.cores1_val,
        hInv.cores1_pair, hInv.cores2_ne, ?_, hInv.cores2_pair⟩
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
      · intro Cs hCs U hU
        have hpre := hInv.cores2_val Cs hCs U hU
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
    | bindCores Cs h0 hne hval hpair =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        hInv.cand_heavy, hInv.cand_bot, hInv.cand_cores, hInv.cores1_ne,
        hInv.cores1_val, hInv.cores1_pair, ?_, ?_, ?_⟩
      · intro Cs' hCs'
        dsimp only at hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        exact hne
      · intro Cs' hCs' U hU
        dsimp only at hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        exact hval U hU
      · intro Cs' hCs' U hU V hV
        dsimp only at hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        exact hpair U hU V hV
  | link id g t1' h h2 =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' Cs hCs hmem hsubv hr =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      obtain ⟨U₀, hU₀Cs, hU₀g⟩ := hmem
      have hUcard : P.n - P.f ≤ U₀.card := by
        have := hInv.cores1_pair Cs hCs U₀ hU₀Cs U₀ hU₀Cs
        rwa [Finset.inter_self] at this
      have hgdom : P.n - P.f ≤ gdom g :=
        le_trans hUcard (APSet.card_le_gdom hU₀g)
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, ?_, ?_, ?_, ?_,
        hInv.cores1_ne, hInv.cores1_val, hInv.cores1_pair, hInv.cores2_ne,
        hInv.cores2_val, hInv.cores2_pair⟩
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
          have hheavy := cand_some hcand
          exact ⟨Cs, U₀, hCs, hU₀Cs, cnt_heavy_of_subMap hU₀g hheavy⟩
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
          · -- `f + 1` entries of `g'` at `true`, each a committed entry
            have hcnt : P.f + 1 ≤ gcount g true := by
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
      · intro k hk hc
        dsimp only at hc
        by_cases hkid : k = id
        · exact ⟨Cs, hCs⟩
        · rw [Function.update_of_ne hkid] at hc
          exact hInv.cand_cores k hk hc
  | retG id g t2' h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' Cs hCs hmem hsubv hr =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      exact ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        hInv.cand_heavy, hInv.cand_bot, hInv.cand_cores, hInv.cores1_ne,
        hInv.cores1_val, hInv.cores1_pair, hInv.cores2_ne, hInv.cores2_val,
        hInv.cores2_pair⟩
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
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
      obtain ⟨Cs, U, hCs, hU, hh⟩ := hInv.cand_heavy k (hF' k hk) v hc
      exact ⟨Cs, U, by rw [Gather.corrupt_cores]; exact hCs, hU, hh⟩
    · intro k hk hc
      rw [Gather.corrupt_call] at hc
      obtain ⟨h1, h2⟩ := hInv.cand_bot k (hF' k hk) hc
      have hmono : supp1 s.1 true ≤ supp1 (s.1.corrupt P id) true ∧
          supp1 s.1 false ≤ supp1 (s.1.corrupt P id) false := by
        constructor <;>
          exact supp1_mono (by intro k' v' hv'; rw [Gather.corrupt_val]; exact hv') hFsub _
      exact ⟨le_trans h1 hmono.1, le_trans h2 hmono.2⟩
    · intro k hk hc
      rw [Gather.corrupt_call] at hc
      obtain ⟨Cs, hCs⟩ := hInv.cand_cores k (hF' k hk) hc
      exact ⟨Cs, by rw [Gather.corrupt_cores]; exact hCs⟩
    · intro Cs hCs
      rw [Gather.corrupt_cores] at hCs
      exact hInv.cores1_ne Cs hCs
    · intro Cs hCs U hU
      rw [Gather.corrupt_cores] at hCs
      have hpre := hInv.cores1_val Cs hCs U hU
      intro p hp
      rw [Gather.corrupt_val]
      exact hpre p hp
    · intro Cs hCs U hU V hV
      rw [Gather.corrupt_cores] at hCs
      exact hInv.cores1_pair Cs hCs U hU V hV
    · intro Cs hCs
      rw [Gather.corrupt_cores] at hCs
      exact hInv.cores2_ne Cs hCs
    · intro Cs hCs U hU
      rw [Gather.corrupt_cores] at hCs
      have hpre := hInv.cores2_val Cs hCs U hU
      intro p hp
      rw [Gather.corrupt_val]
      exact hpre p hp
    · intro Cs hCs U hU V hV
      rw [Gather.corrupt_cores] at hCs
      exact hInv.cores2_pair Cs hCs U hU V hV

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

/-- A member's value entries count into `supp1`. -/
private theorem cnt_le_supp1 {s : PairState P.n} {U : APSet P.n Bool}
    (hUval : U.subMap s.1.val) (v : Bool) :
    APSet.cnt U v ≤ supp1 s.1 v := by
  refine le_trans (APSet.cnt_le_gcount hUval v) (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, Or.inl hid.2⟩

/-- Member-heavy support reads as call support on the specification side. -/
private theorem supp_spec_of_member {s : PairState P.n} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = s.1.call k) (hF : t.F = s.1.F)
    (hprov : ∀ k v, s.1.val k = some v → k ∈ s.1.F ∨ s.1.call k = some v)
    {U : APSet P.n Bool} (hUval : U.subMap s.1.val) {v : Bool}
    (hcnt : P.f + 1 ≤ APSet.cnt U v) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card :=
  spec_supp_of_supp1 hcall hF hprov (le_trans hcnt (cnt_le_supp1 hUval v))

/-- A member of the first family discharges the specification's quorum guard:
its `n − f` distinct processes each carry a committed entry, hence a call or
a corruption. -/
private theorem quorum_of_member {s : PairState P.n} {t : GBCA.SpecState P.n}
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

/-- The exclusion certificate: every first-family member counts `b` below
`|U| − f`, so `b` can never again be a candidate. Frozen — the family and the
members are write-once. -/
def DeadEv (P : Params) (s : PairState P.n) (b : Bool) : Prop :=
  ∃ Cs, s.1.cores = some Cs ∧ ∀ U ∈ Cs, APSet.cnt U b < U.card - P.f

/-- The GBCA core refinement relation. -/
structure PairRel (P : Params) (s : PairState P.n) (t : GBCA.SpecState P.n) : Prop where
  /-- The pair invariant. -/
  inv : PairInv P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = s.1.call k
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = s.2.ret id
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.1.F
  /-- A dead bit is certified excluded. -/
  dead_cert : ∀ b ∈ t.dead, DeadEv P s b
  /-- The A-latch is certified by a heavy second-family member. -/
  gradeA_ev : t.grade = some true → ∃ Cs U v, s.2.cores = some Cs ∧ U ∈ Cs ∧
    U.card - P.f ≤ APSet.cnt U (some v)
  /-- The C-latch is certified by an everywhere-light second-family member. -/
  gradeC_ev : t.grade = some false → ∃ Cs U, s.2.cores = some Cs ∧ U ∈ Cs ∧
    ∀ v, APSet.cnt U (some v) ≤ P.f

/-- The relation holds initially. -/
theorem pairRel_init :
    PairRel P (PairState.initial P.n) (GBCA.SpecState.initial P.n) := by
  refine ⟨PairInv.initial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [PairState.initial, Gather.SpecState.initial, GBCA.SpecState.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem pairRel_corrupt {r : ℕ} {s : PairState P.n} {t : GBCA.SpecState P.n}
    (hR : PairRel P s t) (id : Fin P.n) :
    PairRel P (s.1.corrupt P id, s.2.corrupt P id) (t.corrupt P id) := by
  refine ⟨hR.inv.step (r := r) (PairStep.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [GBCA.corrupt_dead] at hb
    obtain ⟨Cs, hCs, hl⟩ := hR.dead_cert b hb
    exact ⟨Cs, by dsimp only; rw [Gather.corrupt_cores]; exact hCs, hl⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨Cs, U, v, hCs, hU, hh⟩ := hR.gradeA_ev hg
    exact ⟨Cs, U, v, by dsimp only; rw [Gather.corrupt_cores]; exact hCs, hU, hh⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨Cs, U, hCs, hU, hl⟩ := hR.gradeC_ev hg
    exact ⟨Cs, U, by dsimp only; rw [Gather.corrupt_cores]; exact hCs, hU, hl⟩

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
        hInv', ?_, hR.ret_eq, hR.F_eq, hR.dead_cert, hR.gradeA_ev,
        hR.gradeC_ev⟩
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
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.dead_cert, hR.gradeA_ev,
        hR.gradeC_ev⟩
    | bindCores Cs h0 hne hval hpair =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.gradeA_ev, hR.gradeC_ev⟩
      intro b hb
      obtain ⟨Cs', hCs', -⟩ := hR.dead_cert b hb
      rw [h0] at hCs'
      exact absurd hCs' (by simp)
  | ga2Tau t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.dead_cert, hR.gradeA_ev,
        hR.gradeC_ev⟩
    | bindCores Cs h0 hne hval hpair =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.dead_cert, ?_, ?_⟩
      · intro hg
        obtain ⟨Cs', U, v, hCs', -, -⟩ := hR.gradeA_ev hg
        rw [h0] at hCs'
        exact absurd hCs' (by simp)
      · intro hg
        obtain ⟨Cs', U, hCs', -, -⟩ := hR.gradeC_ev hg
        rw [h0] at hCs'
        exact absurd hCs' (by simp)
  | link id g t1' h h2 =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' Cs hCs hmem hsubv hr =>
      have ht1' := PMF.pure_injective hμ
      subst ht1'
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.dead_cert, hR.gradeA_ev,
        hR.gradeC_ev⟩
  | retG id g t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2' : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' Cs₂ hCs₂ hmem₂ hsub₂ hr₂ =>
      have ht2' := PMF.pure_injective hμ
      subst ht2'
      obtain ⟨U₂, hU₂Cs, hU₂g⟩ := hmem₂
      have hU₂card : P.n - P.f ≤ U₂.card := by
        have := hR.inv.cores2_pair Cs₂ hCs₂ U₂ hU₂Cs U₂ hU₂Cs
        rwa [Finset.inter_self] at this
      have hgdom : P.n - P.f ≤ gdom g := le_trans hU₂card (APSet.card_le_gdom hU₂g)
      have hf := P.hf
      have hretflag : q₂.ret id = false := by
        rw [hR.ret_eq id]
        exact hr₂
      have hchain : ∀ k, k ∉ q₁.1.F → ∀ c, g k = some c → q₁.2.call k = some c := by
        intro k hkF c hgc
        have hv2 := hsub₂ k c hgc
        rcases hR.inv.val2_prov k c hv2 with hF | hc
        · exact absurd hF hkF
        · exact hc
      cases hout : gradeOf P g with
      | A v =>
        have hA := gradeOf_A hout
        have hA_ev : U₂.card - P.f ≤ APSet.cnt U₂ (some v) :=
          cnt_heavy_of_subMap hU₂g hA
        have hcnt_v : P.f + 1 ≤ gcount g (some v) := by omega
        obtain ⟨kh, hkhg, hkhF⟩ := exists_honest_filter
          (F := q₁.1.F) hR.inv.F_card
          (p := fun k => g k = some (some v)) hcnt_v
        have hcall2 := hchain kh hkhF (some v) hkhg
        obtain ⟨Cs₁, U₁, hCs₁, hU₁, hheavy₁⟩ := hR.inv.cand_heavy kh hkhF v hcall2
        have hU₁val := hR.inv.cores1_val Cs₁ hCs₁ U₁ hU₁
        have hU₁card : P.n - P.f ≤ U₁.card := by
          have := hR.inv.cores1_pair Cs₁ hCs₁ U₁ hU₁ U₁ hU₁
          rwa [Finset.inter_self] at this
        have hlive : v ∉ q₂.dead := by
          intro hv
          obtain ⟨Cs₁', hCs₁', hlight⟩ := hR.dead_cert v hv
          rw [hCs₁] at hCs₁'
          obtain rfl : Cs₁ = Cs₁' := by injection hCs₁'
          have := hlight U₁ hU₁
          omega
        have hgA : q₂.grade = none ∨ q₂.grade = some true := by
          rcases hgr : q₂.grade with _ | b
          · exact Or.inl rfl
          · cases b
            · exfalso
              obtain ⟨Cs₂', U', hCs₂', hU', hlight⟩ := hR.gradeC_ev hgr
              rw [hCs₂] at hCs₂'
              obtain rfl : Cs₂ = Cs₂' := by injection hCs₂'
              exact members_heavy_light
                (hR.inv.cores2_pair Cs₂ hCs₂ U₂ hU₂Cs U' hU') hA_ev (hlight v)
            · exact Or.inr rfl
        have hDead : ∀ U' ∈ Cs₁, APSet.cnt U' (!v) < U'.card - P.f := by
          intro U' hU'
          by_contra hcon
          rw [not_lt] at hcon
          have h := members_agree
            (hR.inv.cores1_pair Cs₁ hCs₁ U₁ hU₁ U' hU') hheavy₁ hcon
          simp at h
        by_cases hbv : (!v) ∈ q₂.dead
        · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (GBCA.Step.retA q₂ id v hlive hbv hgA hretflag)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, hR.dead_cert, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro _
            exact ⟨Cs₂, U₂, v, hCs₂, hU₂Cs, hA_ev⟩
          · intro hgr
            exact absurd hgr (by simp)
        · have hd0 : q₂.dead = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro b' hb'
            obtain ⟨Cs₁', hCs₁', hlight⟩ := hR.dead_cert b' hb'
            rw [hCs₁] at hCs₁'
            obtain rfl : Cs₁ = Cs₁' := by injection hCs₁'
            have hlU₁ := hlight U₁ hU₁
            have hbv' : b' ≠ v := by
              intro hh
              subst hh
              omega
            have hb'nv : b' = !v := by
              cases b' <;> cases v <;> simp_all
            subst hb'nv
            exact hbv hb'
          have hkill : (GBCA.specInst P r).LStep q₂ Silent.τ
              { q₂ with dead := insert (!v) q₂.dead } :=
            GBCA.Step.bindUnset q₂ (!v)
              (quorum_of_member hR.call_eq hR.F_eq hR.inv.val1_prov hU₁val hU₁card)
              (by
                rw [Bool.not_not]
                exact supp_spec_of_member hR.call_eq hR.F_eq hR.inv.val1_prov
                  hU₁val (by omega))
              hd0
          have hret2 : (GBCA.specInst P r).LStep
              { q₂ with dead := insert (!v) q₂.dead } (.retG r id (.A v))
              { q₂ with
                dead := insert (!v) q₂.dead
                grade := some true
                ret := Function.update q₂.ret id true } :=
            GBCA.Step.retA _ id v (by rw [hd0]; simp) (Finset.mem_insert_self _ _)
              hgA hretflag
          refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hkill hret2 (by simp)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, ?_, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro b hb
            rw [hd0, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · exact ⟨Cs₁, hCs₁, hDead⟩
            · simp at hb
          · intro _
            exact ⟨Cs₂, U₂, v, hCs₂, hU₂Cs, hA_ev⟩
          · intro hgr
            exact absurd hgr (by simp)
      | B v =>
        obtain ⟨hBcnt, hBnotA⟩ := gradeOf_B hout
        obtain ⟨kh, hkhg, hkhF⟩ := exists_honest_filter
          (F := q₁.1.F) hR.inv.F_card
          (p := fun k => g k = some (some v)) hBcnt
        have hcall2 := hchain kh hkhF (some v) hkhg
        obtain ⟨Cs₁, U₁, hCs₁, hU₁, hheavy₁⟩ := hR.inv.cand_heavy kh hkhF v hcall2
        have hU₁val := hR.inv.cores1_val Cs₁ hCs₁ U₁ hU₁
        have hU₁card : P.n - P.f ≤ U₁.card := by
          have := hR.inv.cores1_pair Cs₁ hCs₁ U₁ hU₁ U₁ hU₁
          rwa [Finset.inter_self] at this
        have hlive : v ∉ q₂.dead := by
          intro hv
          obtain ⟨Cs₁', hCs₁', hlight⟩ := hR.dead_cert v hv
          rw [hCs₁] at hCs₁'
          obtain rfl : Cs₁ = Cs₁' := by injection hCs₁'
          have := hlight U₁ hU₁
          omega
        have hDead : ∀ U' ∈ Cs₁, APSet.cnt U' (!v) < U'.card - P.f := by
          intro U' hU'
          by_contra hcon
          rw [not_lt] at hcon
          have h := members_agree
            (hR.inv.cores1_pair Cs₁ hCs₁ U₁ hU₁ U' hU') hheavy₁ hcon
          simp at h
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
          · have hwv : w ≠ v := by
              intro hwv
              subst hwv
              exact hkd.2 hgkd
            obtain ⟨Cs₁', U₁', hCs₁', hU₁', hheavy₁'⟩ :=
              hR.inv.cand_heavy kd hkdF w hcall2d
            rw [hCs₁] at hCs₁'
            obtain rfl : Cs₁ = Cs₁' := by injection hCs₁'
            have h := members_agree
              (hR.inv.cores1_pair Cs₁ hCs₁ U₁ hU₁ U₁' hU₁') hheavy₁ hheavy₁'
            exact absurd h.symm hwv
        by_cases hbv : (!v) ∈ q₂.dead
        · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (GBCA.Step.retB q₂ id v hlive hbv hw hretflag)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, hR.dead_cert, hR.gradeA_ev,
            hR.gradeC_ev⟩
          intro k
          dsimp only
          by_cases hk : k = id
          · subst hk
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hk, Function.update_of_ne hk]
            exact hR.ret_eq k
        · have hd0 : q₂.dead = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro b' hb'
            obtain ⟨Cs₁', hCs₁', hlight⟩ := hR.dead_cert b' hb'
            rw [hCs₁] at hCs₁'
            obtain rfl : Cs₁ = Cs₁' := by injection hCs₁'
            have hlU₁ := hlight U₁ hU₁
            have hbv' : b' ≠ v := by
              intro hh
              subst hh
              omega
            have hb'nv : b' = !v := by
              cases b' <;> cases v <;> simp_all
            subst hb'nv
            exact hbv hb'
          have hkill : (GBCA.specInst P r).LStep q₂ Silent.τ
              { q₂ with dead := insert (!v) q₂.dead } :=
            GBCA.Step.bindUnset q₂ (!v)
              (quorum_of_member hR.call_eq hR.F_eq hR.inv.val1_prov hU₁val hU₁card)
              (by
                rw [Bool.not_not]
                exact supp_spec_of_member hR.call_eq hR.F_eq hR.inv.val1_prov
                  hU₁val (by omega))
              hd0
          have hret2 : (GBCA.specInst P r).LStep
              { q₂ with dead := insert (!v) q₂.dead } (.retG r id (.B v))
              { q₂ with
                dead := insert (!v) q₂.dead
                ret := Function.update q₂.ret id true } :=
            GBCA.Step.retB _ id v (by rw [hd0]; simp) (Finset.mem_insert_self _ _)
              hw hretflag
          refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hkill hret2 (by simp)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, ?_, hR.gradeA_ev, hR.gradeC_ev⟩
          · intro k
            dsimp only
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro b hb
            dsimp only at hb
            rw [hd0, Finset.mem_insert] at hb
            rcases hb with rfl | hb
            · exact ⟨Cs₁, hCs₁, hDead⟩
            · simp at hb
      | C =>
        have hC := gradeOf_C hout
        have hU₂light : ∀ w, APSet.cnt U₂ (some w) ≤ P.f := fun w =>
          le_trans (APSet.cnt_le_gcount hU₂g (some w)) (hC w)
        have hgdom_pos : P.f + 1 ≤ gdom g := by omega
        obtain ⟨k0, hk0, hk0F⟩ := exists_honest_filter
          (F := q₁.1.F) hR.inv.F_card (p := fun k => g k ≠ none) hgdom_pos
        rcases hgk0 : g k0 with _ | c0
        · exact absurd hgk0 hk0
        have hcall20 := hchain k0 hk0F c0 hgk0
        obtain ⟨Cs₁, hCs₁⟩ := hR.inv.cand_cores k0 hk0F (by rw [hcall20]; simp)
        obtain ⟨U₀, hU₀⟩ := hR.inv.cores1_ne Cs₁ hCs₁
        have hU₀val := hR.inv.cores1_val Cs₁ hCs₁ U₀ hU₀
        have hU₀card : P.n - P.f ≤ U₀.card := by
          have := hR.inv.cores1_pair Cs₁ hCs₁ U₀ hU₀ U₀ hU₀
          rwa [Finset.inter_self] at this
        -- both bit supports
        have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
            (fun id' => q₂.call id' = some b ∨ id' ∈ q₂.F)).card := by
          intro b
          have hcard : P.f + 1 ≤ (Finset.univ.filter
              (fun k => g k ≠ none ∧ g k ≠ some (some (!b)))).card := by
            rw [card_ne_gcount]
            have := hC (!b)
            omega
          obtain ⟨kt, hkt, hktF⟩ := exists_honest_filter hR.inv.F_card hcard
          rcases hgkt : g kt with _ | ct
          · exact absurd hgkt hkt.1
          have hcall2t := hchain kt hktF ct hgkt
          rcases ct with _ | wt
          · rcases (hR.inv.cand_bot kt hktF hcall2t) with ⟨hsT, hsF⟩
            cases b
            · exact spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hsF
            · exact spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hsT
          · have hwt : wt = b := by
              by_contra hne
              have : wt = !b := by
                cases wt <;> cases b <;> simp_all
              subst this
              exact hkt.2 hgkt
            subst hwt
            obtain ⟨Cs₁', U', hCs₁', hU', hh⟩ :=
              hR.inv.cand_heavy kt hktF wt hcall2t
            rw [hCs₁] at hCs₁'
            obtain rfl : Cs₁ = Cs₁' := by injection hCs₁'
            have hU'val := hR.inv.cores1_val Cs₁ hCs₁ U' hU'
            have hU'card : P.n - P.f ≤ U'.card := by
              have := hR.inv.cores1_pair Cs₁ hCs₁ U' hU' U' hU'
              rwa [Finset.inter_self] at this
            exact supp_spec_of_member hR.call_eq hR.F_eq hR.inv.val1_prov
              hU'val (by omega)
        have hgC : q₂.grade = none ∨ q₂.grade = some false := by
          rcases hgr : q₂.grade with _ | b
          · exact Or.inl rfl
          · cases b
            · exact Or.inr rfl
            · exfalso
              obtain ⟨Cs₂', U', v', hCs₂', hU', hh⟩ := hR.gradeA_ev hgr
              rw [hCs₂] at hCs₂'
              obtain rfl : Cs₂ = Cs₂' := by injection hCs₂'
              exact members_heavy_light
                (hR.inv.cores2_pair Cs₂ hCs₂ U' hU' U₂ hU₂Cs) hh (hU₂light v')
        by_cases hdne : q₂.dead = ∅
        · -- kill a bit first
          by_cases hex : ∃ U ∈ Cs₁, U.card - P.f ≤ APSet.cnt U true
          · obtain ⟨Ut, hUt, hht⟩ := hex
            have hUtval := hR.inv.cores1_val Cs₁ hCs₁ Ut hUt
            have hUtcard : P.n - P.f ≤ Ut.card := by
              have := hR.inv.cores1_pair Cs₁ hCs₁ Ut hUt Ut hUt
              rwa [Finset.inter_self] at this
            have hDeadF : ∀ U' ∈ Cs₁, APSet.cnt U' false < U'.card - P.f := by
              intro U' hU'
              by_contra hcon
              push_neg at hcon
              have h := members_agree
                (hR.inv.cores1_pair Cs₁ hCs₁ Ut hUt U' hU') hht hcon
              simp at h
            have hkill : (GBCA.specInst P r).LStep q₂ Silent.τ
                { q₂ with dead := insert false q₂.dead } :=
              GBCA.Step.bindUnset q₂ false
                (quorum_of_member hR.call_eq hR.F_eq hR.inv.val1_prov hU₀val hU₀card)
                (by
                  have hnf : (!false) = true := by simp
                  rw [hnf]
                  exact hsupp true)
                hdne
            have hret2 : (GBCA.specInst P r).LStep
                { q₂ with dead := insert false q₂.dead } (.retG r id .C)
                { q₂ with
                  dead := insert false q₂.dead
                  grade := some false
                  ret := Function.update q₂.ret id true } :=
              GBCA.Step.retC _ id (by simp) (hsupp true) (hsupp false) hgC hretflag
            refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hkill hret2 (by simp)⟩,
              hInv', hR.call_eq, ?_, hR.F_eq, ?_, ?_, ?_⟩ <;> dsimp only
            · intro k
              by_cases hk : k = id
              · subst hk
                rw [Function.update_self, Function.update_self]
              · rw [Function.update_of_ne hk, Function.update_of_ne hk]
                exact hR.ret_eq k
            · intro b hb
              rw [hdne, Finset.mem_insert] at hb
              rcases hb with rfl | hb
              · exact ⟨Cs₁, hCs₁, hDeadF⟩
              · simp at hb
            · intro hgr
              exact absurd hgr (by simp)
            · intro _
              exact ⟨Cs₂, U₂, hCs₂, hU₂Cs, hU₂light⟩
          · simp only [not_exists, not_and, not_le] at hex
            have hkill : (GBCA.specInst P r).LStep q₂ Silent.τ
                { q₂ with dead := insert true q₂.dead } :=
              GBCA.Step.bindUnset q₂ true
                (quorum_of_member hR.call_eq hR.F_eq hR.inv.val1_prov hU₀val hU₀card)
                (by
                  have hnf : (!true) = false := by simp
                  rw [hnf]
                  exact hsupp false)
                hdne
            have hret2 : (GBCA.specInst P r).LStep
                { q₂ with dead := insert true q₂.dead } (.retG r id .C)
                { q₂ with
                  dead := insert true q₂.dead
                  grade := some false
                  ret := Function.update q₂.ret id true } :=
              GBCA.Step.retC _ id (by simp) (hsupp true) (hsupp false) hgC hretflag
            refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hkill hret2 (by simp)⟩,
              hInv', hR.call_eq, ?_, hR.F_eq, ?_, ?_, ?_⟩ <;> dsimp only
            · intro k
              by_cases hk : k = id
              · subst hk
                rw [Function.update_self, Function.update_self]
              · rw [Function.update_of_ne hk, Function.update_of_ne hk]
                exact hR.ret_eq k
            · intro b hb
              rw [hdne, Finset.mem_insert] at hb
              rcases hb with rfl | hb
              · exact ⟨Cs₁, hCs₁, hex⟩
              · simp at hb
            · intro hgr
              exact absurd hgr (by simp)
            · intro _
              exact ⟨Cs₂, U₂, hCs₂, hU₂Cs, hU₂light⟩
        · -- some bit is already dead
          have hd : 1 ≤ q₂.dead.card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hdne)
          refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
            (GBCA.Step.retC q₂ id hd (hsupp true) (hsupp false) hgC hretflag)⟩,
            hInv', hR.call_eq, ?_, hR.F_eq, hR.dead_cert, ?_, ?_⟩ <;> dsimp only
          · intro k
            by_cases hk : k = id
            · subst hk
              rw [Function.update_self, Function.update_self]
            · rw [Function.update_of_ne hk, Function.update_of_ne hk]
              exact hR.ret_eq k
          · intro hgr
            exact absurd hgr (by simp)
          · intro _
            exact ⟨Cs₂, U₂, hCs₂, hU₂Cs, hU₂light⟩
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
