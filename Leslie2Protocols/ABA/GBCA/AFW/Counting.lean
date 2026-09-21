/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Specification
import Leslie2Protocols.ABA.Vocabulary.Labels

/-!
# The counting of the graded-agreement round

The local counting the round-`r` GBCA implementation of the modular
construction of Attiya, Flam and Welch runs on — their Algorithm 4 at `R = 2`,
its two-gather branch, with the grade read off the second gather's counts in
place of the approximate-agreement subroutine of its lines 7 and 8 (deviation
D24).

Per process, the construction is

* `S ← Gather₁(b)` — the input bit through the first gather instance;
* the candidate: the bit occurring at least `|S| − f` times in `S`, `⊥` if
  neither does (`GBCA.cand`);
* `T ← Gather₂(candidate)` — the candidate through the second instance;
* the graded return (`GBCA.gradeOf`): `(v, A)` if some bit's entries reach
  `|T| − f`, else `(v, B)` if they reach `f + 1` — at most one bit can —
  else `(⊥, C)`.

## The bound bit

`boundOfCore P S` is the bit heavy in `S` — carried by at least `|S| − f` of
its entries — and `true` when neither bit is. At the sizes the gather
specification's `bindCore` allows (`|S| ≥ n − f > 2f`) at most one bit is
heavy, so the definition is the heavy bit wherever one exists, and its
complement is then light (`cnt_boundOfCore_light`): a return handing out `v`
announces `v`, and a return handing out nothing announces a bit whose
complement no return can hand out.

## The entry counts

The per-process counts of a partial map (`gcount`, `gdom`) and of a payload set
(`APSet.cnt`), the transfer of a heavy value into a payload set below the map
(`cnt_heavy_of_subMap`), and the `F`-blind committed-entry support count
`supp1`, read on a gather specification state.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Gather

/-! ### Entry counting -/

section Counting

variable {n : ℕ} {α : Type} [DecidableEq α]

/-- The number of processes whose entry in `g` is `x`. -/
def gcount (g : Fin n → Option α) (x : α) : ℕ :=
  (Finset.univ.filter (fun k => g k = some x)).card

/-- The number of processes with an entry in `g`. -/
def gdom (g : Fin n → Option α) : ℕ :=
  (Finset.univ.filter (fun k => g k ≠ none)).card

/-- The number of entries of a payload set at value `x`. -/
def APSet.cnt (U : APSet n α) (x : α) : ℕ :=
  (U.filter (fun p => p.2 = x)).card

/-- The entries of a sub-map payload set away from `x` are at most the
map's entries away from `x`: the first components are distinct, and each
carries an entry of `g` other than `x`. -/
theorem APSet.card_sub_cnt_le {U : APSet n α} {g : Fin n → Option α}
    (hg : U.subMap g) (x : α) :
    U.card - APSet.cnt U x ≤ gdom g - gcount g x := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := U) (p := fun p => p.2 = x)
  have himg : (U.filter (fun p => ¬ p.2 = x)).card
      ≤ ((Finset.univ.filter (fun k => g k ≠ none)) \
          (Finset.univ.filter (fun k => g k = some x))).card := by
    have hinj : Set.InjOn Prod.fst
        ((U.filter (fun p => ¬ p.2 = x) : Finset (Fin n × α)) : Set (Fin n × α)) := by
      intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      have h1 := hg p hp.1
      have h2 := hg q hq.1
      rw [hpq] at h1
      rw [h1] at h2
      have h3 : p.2 = q.2 := by injection h2
      exact Prod.ext hpq h3
    rw [← Finset.card_image_of_injOn hinj]
    refine Finset.card_le_card ?_
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    rw [Finset.mem_filter] at hp
    have h1 := hg p hp.1
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, by rw [h1]; simp⟩, ?_⟩
    intro hc
    obtain ⟨-, hc⟩ := hc
    rw [h1] at hc
    have h4 : p.2 = x := by injection hc
    exact hp.2 h4
  have hsub : (Finset.univ.filter (fun k => g k = some x))
      ⊆ (Finset.univ.filter (fun k => g k ≠ none)) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    rw [hk.2]
    simp
  have hsdiff : ((Finset.univ.filter (fun k => g k ≠ none)) \
        (Finset.univ.filter (fun k => g k = some x))).card
      = (Finset.univ.filter (fun k => g k ≠ none)).card
        - ((Finset.univ.filter (fun k => g k = some x))
            ∩ (Finset.univ.filter (fun k => g k ≠ none))).card :=
    Finset.card_sdiff
  rw [Finset.inter_eq_left.mpr hsub] at hsdiff
  unfold APSet.cnt gdom gcount
  omega

/-- A payload set's first components inject into the map's domain. -/
theorem APSet.card_le_gdom {U : APSet n α} {g : Fin n → Option α}
    (hg : U.subMap g) : U.card ≤ gdom g := by
  have hinj : Set.InjOn Prod.fst ((U : Finset (Fin n × α)) : Set (Fin n × α)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    have h1 := hg p hp
    have h2 := hg q hq
    rw [hpq] at h1
    rw [h1] at h2
    have h3 : p.2 = q.2 := by injection h2
    exact Prod.ext hpq h3
  rw [← Finset.card_image_of_injOn hinj]
  refine Finset.card_le_card ?_
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  have h1 := hg p hp
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [h1]
  simp

/-- A payload set's entries at `x` count below the map's. -/
theorem APSet.cnt_le_gcount {U : APSet n α} {g : Fin n → Option α}
    (hg : U.subMap g) (x : α) : APSet.cnt U x ≤ gcount g x := by
  have hinj : Set.InjOn Prod.fst
      ((U.filter (fun p => p.2 = x) : Finset (Fin n × α)) : Set (Fin n × α)) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    have h1 := hg p hp.1
    have h2 := hg q hq.1
    rw [hpq] at h1
    rw [h1] at h2
    have h3 : p.2 = q.2 := by injection h2
    exact Prod.ext hpq h3
  unfold APSet.cnt
  rw [← Finset.card_image_of_injOn hinj]
  refine Finset.card_le_card ?_
  intro k hk
  rw [Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  rw [Finset.mem_filter] at hp
  have h1 := hg p hp.1
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [h1, hp.2]

/-- The entries away from `x` count the domain minus `x`'s count. -/
theorem card_ne_gcount (g : Fin n → Option α) (x : α) :
    (Finset.univ.filter (fun k => g k ≠ none ∧ g k ≠ some x)).card
      = gdom g - gcount g x := by
  have hset : Finset.univ.filter (fun k => g k ≠ none ∧ g k ≠ some x)
      = (Finset.univ.filter (fun k => g k ≠ none))
        \ (Finset.univ.filter (fun k => g k = some x)) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun hc => h3 hc.2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, fun hc => h3 ⟨h1, hc⟩⟩
  have hsub : (Finset.univ.filter (fun k => g k = some x))
      ⊆ (Finset.univ.filter (fun k => g k ≠ none)) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    rw [hk.2]
    simp
  have hsdiff : ((Finset.univ.filter (fun k => g k ≠ none)) \
        (Finset.univ.filter (fun k => g k = some x))).card
      = (Finset.univ.filter (fun k => g k ≠ none)).card
        - ((Finset.univ.filter (fun k => g k = some x))
            ∩ (Finset.univ.filter (fun k => g k ≠ none))).card :=
    Finset.card_sdiff
  rw [Finset.inter_eq_left.mpr hsub] at hsdiff
  rw [hset, hsdiff]
  rfl

/-- For a Boolean map the domain splits into the two value counts. -/
theorem gdom_bool_sum (g : Fin n → Option Bool) :
    gdom g = gcount g true + gcount g false := by
  unfold gdom gcount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨-, hk⟩
      rcases hg : g k with _ | b
      · exact absurd hg hk
      · cases b
        · exact Or.inr ⟨Finset.mem_univ _, rfl⟩
        · exact Or.inl ⟨Finset.mem_univ _, rfl⟩
    · rintro (⟨-, hk⟩ | ⟨-, hk⟩) <;>
        exact ⟨Finset.mem_univ _, by rw [hk]; simp⟩
  · rw [Finset.disjoint_filter]
    intro k _ h1 h2
    rw [h1] at h2
    have : true = false := by injection h2
    exact absurd this (by simp)

/-- **Heavy transfer into a dominated payload set.** A value carried by all
but `f` of a map's entries is carried by all but `f` of the entries of any
payload set below that map. -/
theorem cnt_heavy_of_subMap {P : Params} {U : APSet P.n α} {g : Fin P.n → Option α}
    {x : α} (hg : U.subMap g) (hheavy : gdom g - P.f ≤ gcount g x) :
    U.card - P.f ≤ APSet.cnt U x := by
  have h1 := APSet.card_sub_cnt_le hg x
  omega

end Counting

/-! ### The candidate, the grade and the bound bit -/

/-- The candidate after the first gather: the bit carried by all but `f` of
the returned entries, `⊥` if neither is. At the domains the return rules
allow (`≥ n − f > 2f` entries) at most one bit can be. -/
def cand (P : Params) (g : Fin P.n → Option Bool) : Option Bool :=
  if gdom g - P.f ≤ gcount g true then some true
  else if gdom g - P.f ≤ gcount g false then some false
  else none

theorem cand_some {P : Params} {g : Fin P.n → Option Bool} {v : Bool}
    (h : cand P g = some v) : gdom g - P.f ≤ gcount g v := by
  unfold cand at h
  split_ifs at h with h1 h2
  · obtain rfl : true = v := by injection h
    exact h1
  · obtain rfl : false = v := by injection h
    exact h2

theorem cand_none {P : Params} {g : Fin P.n → Option Bool}
    (h : cand P g = none) (v : Bool) : gcount g v < gdom g - P.f := by
  unfold cand at h
  split_ifs at h with h1 h2
  cases v
  · exact lt_of_not_ge h2
  · exact lt_of_not_ge h1

/-- The graded outcome after the second gather: `A` at `|T| − f` entries of
one bit, `B` at `f + 1`, `C` below both. -/
def gradeOf (P : Params) (g : Fin P.n → Option (Option Bool)) : GbcaOut :=
  if gdom g - P.f ≤ gcount g (some true) then .A true
  else if gdom g - P.f ≤ gcount g (some false) then .A false
  else if P.f + 1 ≤ gcount g (some true) then .B true
  else if P.f + 1 ≤ gcount g (some false) then .B false
  else .C

theorem gradeOf_A {P : Params} {g : Fin P.n → Option (Option Bool)} {v : Bool}
    (h : gradeOf P g = .A v) : gdom g - P.f ≤ gcount g (some v) := by
  unfold gradeOf at h
  split_ifs at h with h1 h2 h3 h4
  · obtain rfl : true = v := by injection h
    exact h1
  · obtain rfl : false = v := by injection h
    exact h2

theorem gradeOf_B {P : Params} {g : Fin P.n → Option (Option Bool)} {v : Bool}
    (h : gradeOf P g = .B v) :
    P.f + 1 ≤ gcount g (some v) ∧ ∀ w, gcount g (some w) < gdom g - P.f := by
  unfold gradeOf at h
  split_ifs at h with h1 h2 h3 h4
  · obtain rfl : true = v := by injection h
    refine ⟨h3, ?_⟩
    intro w
    cases w
    · exact lt_of_not_ge h2
    · exact lt_of_not_ge h1
  · obtain rfl : false = v := by injection h
    refine ⟨h4, ?_⟩
    intro w
    cases w
    · exact lt_of_not_ge h2
    · exact lt_of_not_ge h1

theorem gradeOf_C {P : Params} {g : Fin P.n → Option (Option Bool)}
    (h : gradeOf P g = .C) : ∀ w, gcount g (some w) ≤ P.f := by
  unfold gradeOf at h
  split_ifs at h with h1 h2 h3 h4
  intro w
  cases w
  · exact Nat.lt_succ_iff.mp (lt_of_not_ge h4)
  · exact Nat.lt_succ_iff.mp (lt_of_not_ge h3)

/-- **The round's bound bit**, read off the first gather's core: the bit
heavy in `S` — carried by at least `|S| − f` of its entries — and `true` when
neither bit is. -/
def boundOfCore (P : Params) (S : APSet P.n Bool) : Bool :=
  if S.card - P.f ≤ APSet.cnt S true then true
  else if S.card - P.f ≤ APSet.cnt S false then false
  else true

/-- A heavy bit is the bound bit. Two bits cannot both be heavy at
`|S| ≥ n − f`, so the heavy bit is the one the definition selects. -/
theorem boundOfCore_of_heavy {P : Params} {S : APSet P.n Bool} {v : Bool}
    (hcard : P.n - P.f ≤ S.card) (hv : S.card - P.f ≤ APSet.cnt S v) :
    boundOfCore P S = v := by
  have hf := P.hf
  have hsplit : APSet.cnt S true + APSet.cnt S false ≤ S.card := by
    unfold APSet.cnt
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    · rw [Finset.disjoint_filter]
      intro p _ h1 h2
      rw [h1] at h2
      exact absurd h2 (by simp)
  unfold boundOfCore
  cases v
  · have hT : ¬ S.card - P.f ≤ APSet.cnt S true := by omega
    rw [if_neg hT, if_pos hv]
  · rw [if_pos hv]

/-- The complement of the bound bit is light: no return can hand it out. -/
theorem cnt_boundOfCore_light {P : Params} {S : APSet P.n Bool}
    (hcard : P.n - P.f ≤ S.card) :
    APSet.cnt S (!boundOfCore P S) < S.card - P.f := by
  have hf := P.hf
  have hsplit : APSet.cnt S true + APSet.cnt S false ≤ S.card := by
    unfold APSet.cnt
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    · rw [Finset.disjoint_filter]
      intro p _ h1 h2
      rw [h1] at h2
      exact absurd h2 (by simp)
  unfold boundOfCore
  split_ifs with h1 h2 <;> simp only [Bool.not_true, Bool.not_false] <;> omega

/-! ### The support count -/

/-- The `F`-blind committed-entry support count of a bit. -/
def supp1 {P : Params} (t1 : Gather.SpecState P.n Bool) (v : Bool) : ℕ :=
  (Finset.univ.filter (fun id => t1.val id = some v ∨ id ∈ t1.F)).card

end GBCA
end ABA
end PLTS
