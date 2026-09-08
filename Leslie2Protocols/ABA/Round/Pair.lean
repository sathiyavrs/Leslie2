/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Spec
import Leslie2Protocols.ABA.Vocabulary.Labels

/-!
# The GBCA implementation over the gather specifications

The round-`r` GBCA implementation of the modular construction of Attiya,
Flam and Welch — their Algorithm 4 at `R = 1`, with no approximate-agreement
stage (deviation D24): two gather calls and local counting, read over the
gather specification (`ABA/Gather/Spec.lean`), as an LTS over the shared
alphabet `ABA.Lab n`.

Per process, the construction is

* `S ← Gather₁(b)` — the input bit through the first gather instance;
* the candidate: the bit occurring at least `|S| − f` times in `S`, `⊥` if
  neither does (`GBCA.cand`);
* `T ← Gather₂(candidate)` — the candidate through the second instance;
* the graded return (`GBCA.gradeOf`): `(v, A)` if some bit's entries reach
  `|T| − f`, else `(v, B)` if they reach `f + 1` — at most one bit can —
  else `(⊥, C)`.

The state is exactly the pair of the two gather specification states: the
per-process input is the first instance's call record, the candidate the
second's, the round's return flag the second's return flag. The rule table
embeds the gather specification's rows — a row of the pair either relays one
instance's step, or fuses two: the first gather's return with the second's
call (`link`), and the second gather's return with the graded ABA-level
return (`retG`).

The file also carries the entry-counting kit the refinement consumes: the
per-value counts of a partial map (`gcount`, `gdom`) and of a payload set
(`APSet.cnt`), the transfer of a heavy value into a dominated core-family
member (`cnt_heavy_of_subMap`), and the two member-arithmetic facts — values
heavy in two members of one family agree (`members_agree`), and a heavy
member refutes an everywhere-light one (`members_heavy_light`).
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

theorem APSet.cnt_le_of_subset {U V : APSet n α} (h : U ⊆ V) (x : α) :
    APSet.cnt U x ≤ APSet.cnt V x :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

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

/-- **Heavy transfer into a member.** A value carried by all but `f` of a
map's entries is carried by all but `f` of any dominated payload set's
entries. -/
theorem cnt_heavy_of_subMap {P : Params} {U : APSet P.n α} {g : Fin P.n → Option α}
    {x : α} (hg : U.subMap g) (hheavy : gdom g - P.f ≤ gcount g x) :
    U.card - P.f ≤ APSet.cnt U x := by
  have h1 := APSet.card_sub_cnt_le hg x
  omega

/-- The intersection of two payload sets counts below either. -/
theorem APSet.cnt_inter_le_left (U V : APSet n α) (x : α) :
    APSet.cnt (U ∩ V) x ≤ APSet.cnt U x :=
  APSet.cnt_le_of_subset Finset.inter_subset_left x

theorem APSet.cnt_inter_le_right (U V : APSet n α) (x : α) :
    APSet.cnt (U ∩ V) x ≤ APSet.cnt V x :=
  APSet.cnt_le_of_subset Finset.inter_subset_right x

/-- Heaviness restricts to the intersection: a value heavy in `U` misses at
most `f` entries of any subset of `U`. -/
theorem cnt_heavy_inter {P : Params} {U V : APSet P.n α} {x : α}
    (hheavy : U.card - P.f ≤ APSet.cnt U x) :
    (U ∩ V).card - P.f ≤ APSet.cnt (U ∩ V) x := by
  have hsplitU := Finset.card_filter_add_card_filter_not
    (s := U) (p := fun p => p.2 = x)
  have hsplitD := Finset.card_filter_add_card_filter_not
    (s := U ∩ V) (p := fun p => p.2 = x)
  have hsub : ((U ∩ V).filter (fun p => ¬ p.2 = x)).card
      ≤ (U.filter (fun p => ¬ p.2 = x)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ Finset.inter_subset_left)
  unfold APSet.cnt at hheavy ⊢
  omega

/-- **Two heavy members agree.** In a family whose members pairwise share at
least `n − f ≥ 2f + 1` entries, values heavy in two members coincide. -/
theorem members_agree {P : Params} {U V : APSet P.n α} {x y : α}
    (hpair : P.n - P.f ≤ (U ∩ V).card)
    (hx : U.card - P.f ≤ APSet.cnt U x) (hy : V.card - P.f ≤ APSet.cnt V y) :
    x = y := by
  by_contra hxy
  have hDx := cnt_heavy_inter (V := V) hx
  have hy' : V.card - P.f ≤ APSet.cnt V y := hy
  have hDy : (U ∩ V).card - P.f ≤ APSet.cnt (U ∩ V) y := by
    rw [Finset.inter_comm]
    exact cnt_heavy_inter (V := U) hy'
  -- the two value filters are disjoint
  have hdisj : APSet.cnt (U ∩ V) x + APSet.cnt (U ∩ V) y ≤ (U ∩ V).card := by
    unfold APSet.cnt
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    · rw [Finset.disjoint_filter]
      intro p _ hpx hpy
      exact hxy (hpx ▸ hpy ▸ rfl)
  have hf := P.hf
  omega

/-- **A heavy member refutes an everywhere-light one.** -/
theorem members_heavy_light {P : Params} {U V : APSet P.n α} {x : α}
    (hpair : P.n - P.f ≤ (U ∩ V).card)
    (hx : U.card - P.f ≤ APSet.cnt U x) (hy : APSet.cnt V x ≤ P.f) : False := by
  have hDx := cnt_heavy_inter (V := V) hx
  have hle := APSet.cnt_inter_le_right U V x
  have hf := P.hf
  omega

end Counting

/-! ### The candidate and the grade -/

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

/-! ### The pair instance -/

/-- **The state of the GBCA implementation over the gather specifications**:
the two gather specification states. The per-process input is the first
instance's call record, the candidate the second's, the round's return flag
the second's return flag — the pair carries the whole round. -/
abbrev PairState (n : ℕ) : Type :=
  Gather.SpecState n Bool × Gather.SpecState n (Option Bool)

/-- The initial pair state. -/
def PairState.initial (n : ℕ) : PairState n :=
  (Gather.SpecState.initial n Bool, Gather.SpecState.initial n (Option Bool))

/-- The step relation of the round-`r` GBCA-over-gather instance. Each row
either relays one gather instance's specification step, or fuses two: the
environment call with the first gather's call, the first gather's return
with the second's call (`link`), and the second gather's return with the
graded ABA-level return (`retG`). All transitions are Dirac. -/
inductive PairStep (P : Params) (r : ℕ) :
    PairState P.n → Lab P.n → PMF (PairState P.n) → Prop
  /-- The environment call is the first gather's call (genuine or loop,
  whichever the embedded step is). -/
  | callG (s : PairState P.n) (id : Fin P.n) (b : Bool) (t1' : Gather.SpecState P.n Bool)
      (h : Gather.Step P s.1 (.call id b) (PMF.pure t1')) :
      PairStep P r s (.callG r id b) (PMF.pure (t1', s.2))
  /-- An internal step of the first gather instance. -/
  | ga1Tau (s : PairState P.n) (t1' : Gather.SpecState P.n Bool)
      (h : Gather.Step P s.1 Gather.Lab.tau (PMF.pure t1')) :
      PairStep P r s .tau (PMF.pure (t1', s.2))
  /-- An internal step of the second gather instance. -/
  | ga2Tau (s : PairState P.n) (t2' : Gather.SpecState P.n (Option Bool))
      (h : Gather.Step P s.2 Gather.Lab.tau (PMF.pure t2')) :
      PairStep P r s .tau (PMF.pure (s.1, t2'))
  /-- The first gather returns to `id` and `id` calls the second gather with
  the candidate. -/
  | link (s : PairState P.n) (id : Fin P.n) (g : Fin P.n → Option Bool)
      (t1' : Gather.SpecState P.n Bool)
      (h : Gather.Step P s.1 (.ret id g) (PMF.pure t1'))
      (h2 : s.2.call id = none) :
      PairStep P r s .tau
        (PMF.pure (t1', { s.2 with
          call := Function.update s.2.call id (some (cand P g)) }))
  /-- The second gather returns to `id` and the round returns the graded
  outcome. -/
  | retG (s : PairState P.n) (id : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (t2' : Gather.SpecState P.n (Option Bool))
      (h : Gather.Step P s.2 (.ret id g) (PMF.pure t2')) :
      PairStep P r s (.retG r id (gradeOf P g)) (PMF.pure (s.1, t2'))
  /-- Corruption (deviation D1), in lockstep across both instances. -/
  | fail (s : PairState P.n) (id : Fin P.n) :
      PairStep P r s (.fail id)
        (PMF.pure (s.1.corrupt P id, s.2.corrupt P id))

/-- The round-`r` GBCA-over-gather instance. -/
noncomputable def pairInst (P : Params) (r : ℕ) :
    System (PairState P.n) (Lab P.n) where
  init := PairState.initial P.n
  step := PairStep P r

@[simp] theorem pairInst_init (P : Params) (r : ℕ) :
    (pairInst P r).init = PairState.initial P.n := rfl

@[simp] theorem pairInst_step (P : Params) (r : ℕ) (s : PairState P.n)
    (l : Lab P.n) (μ : PMF (PairState P.n)) :
    (pairInst P r).step s l μ ↔ PairStep P r s l μ := Iff.rfl

/-- Every transition is Dirac: the instance is an LTS. -/
theorem pairInst_isLTS (P : Params) (r : ℕ) : (pairInst P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end GBCA
end ABA
end PLTS
