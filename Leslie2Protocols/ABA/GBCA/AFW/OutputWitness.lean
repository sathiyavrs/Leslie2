/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.AlgorithmOverGatherSpecifications

/-!
# The witnesses of the two-gather round

The counts the refinement of `ABA/GBCA/AFW/RefinesSpecification.lean` consumes, and the two
witnesses its invariant and its relation carry.

The counting lemmas are stated on a gather specification state and on the graded agreement
specification's `call` map. Committed entries and `call` maps only grow
(`firstGatherSupport_mono`, `call_mono`); a call writes the caller's entry alone and leaves the
committed entries, the core and the corrupted set (`call_val`, `call_unchanged`); and a committed
entry of a correct process reads as call support on the specification
(`callSupport_of_firstGatherSupport`, `callSupport_of_core`). `quorum_of_core` discharges the
specification's quorum guard from the first gather's core: the core's `n − f` distinct processes
each carry a committed entry, hence a call or a corruption.

`OutputWitness P s out` is what a recorded graded outcome witnesses. A `grade2 v` outcome
carries `some v` on at least `|S| − f` entries of the second gather's core and `v` on at least
`|S| − f` of the first gather's; a `grade1 v` outcome carries `v` on at least `|S| − f` entries of
the first gather's core and `f + 1` committed-entry support for `!v`; a grade-0 outcome carries
each bit on at most `f` entries of the second gather's core and `f + 1` support for each bit. The
invariant of `ABA/GBCA/AFW/Invariant.lean` states it of every grade a program holds.

`ExclusionWitness P s b` is the exclusion witness: the first gather's core counts `b` below
`|S| − f`, so no later candidate is `b`. The relation of `ABA/GBCA/AFW/SpecificationRelation.lean`
states it of every bit the specification excludes.

Both witnesses read the two cores and the first gather's committed-entry support. The cores are
written once and the support only grows, so each survives every later transition
(`OutputWitness.mono`).
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Parameters}

/-! ### The counting lemmas

The counts the refinement consumes, stated on a gather specification state and
on the graded agreement specification's `call` map. -/

/-- Committed entries only grow: an entry-wise extension preserves `firstGatherSupport`. -/
theorem firstGatherSupport_mono {t t' : Gather.SpecState P.n Bool}
    (hval : ∀ k v, t.val k = some v → t'.val k = some v) (hF : t.F ⊆ t'.F)
    (v : Bool) : firstGatherSupport t v ≤ firstGatherSupport t' v := by
  refine Finset.card_le_card ?_
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  rcases hid.2 with h | h
  · exact ⟨hid.1, Or.inl (hval id v h)⟩
  · exact ⟨hid.1, Or.inr (hF h)⟩

/-- A filter of more than `f` processes contains a correct one. -/
theorem exists_correct_filter {F : Finset (Fin P.n)} (hF : F.card ≤ P.f)
    {p : Fin P.n → Prop} [DecidablePred p]
    (h : P.f + 1 ≤ (Finset.univ.filter p).card) : ∃ k, p k ∧ k ∉ F := by
  have hlt : F.card < (Finset.univ.filter p).card := by
    omega
  obtain ⟨k, hk, hkF⟩ := InstanceState.exists_correct_of_card_lt hlt
  rw [Finset.mem_filter] at hk
  exact ⟨k, hk.2, hkF⟩

/-- Committed-entry support reads as call support on the specification: a committed entry of a
correct process is its call, and the count is `F`-blind. -/
theorem callSupport_of_firstGatherSupport {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v) {v : Bool}
    (h : P.f + 1 ≤ firstGatherSupport t1 v) :
    P.f + 1 ≤ (Finset.univ.filter (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card := by
  refine le_trans h (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  refine ⟨hid.1, ?_⟩
  rcases hid.2 with hval | hFm
  · rcases hprov id v hval with hFm | hc
    · exact Or.inr (by rw [hF]; exact hFm)
    · exact Or.inl (by rw [hcall]; exact hc)
  · exact Or.inr (by rw [hF]; exact hFm)

/-- The core's value entries count into `firstGatherSupport`. -/
theorem count_le_firstGatherSupport {t1 : Gather.SpecState P.n Bool} {U : AcceptedPairs P.n Bool}
    (hUval : U.subMap t1.val) (v : Bool) : AcceptedPairs.count U v ≤ firstGatherSupport t1 v := by
  refine le_trans (AcceptedPairs.count_le_valueCount hUval v) (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, Or.inl hid.2⟩

/-- A count of `f + 1` in the core reads as call support on the specification. -/
theorem callSupport_of_core {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v) {U : AcceptedPairs P.n Bool}
    (hUval : U.subMap t1.val) {v : Bool} (hcnt : P.f + 1 ≤ AcceptedPairs.count U v) :
    P.f + 1 ≤ (Finset.univ.filter (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card :=
  callSupport_of_firstGatherSupport hcall hF hprov (le_trans hcnt (count_le_firstGatherSupport hUval
    v))

/-- The first gather's core discharges the specification's quorum guard: its
`n − f` distinct processes each carry a committed entry, hence a call or a
corruption. -/
theorem quorum_of_core {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v)
    {U : AcceptedPairs P.n Bool} (hUval : U.subMap t1.val)
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
    have h3 : p.2 = q.2 := by
      injection h2
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

/-- A call of the gather specification leaves the committed entries, the core
and the corrupted set alone. -/
theorem call_unchanged {X : Type} [DecidableEq X] {c c' : Gather.SpecState P.n X}
    {id : Fin P.n} {x : X} (h : Gather.Step P c (.call id x) (PMF.pure c')) :
    c'.val = c.val ∧ c'.core = c.core ∧ c'.F = c.F := by
  generalize hμ : (PMF.pure c' : PMF (Gather.SpecState P.n X)) = μ at h
  cases h with
  | call id' x' hc =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact ⟨rfl, rfl, rfl⟩
  | callLoop id' x' =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact ⟨rfl, rfl, rfl⟩

/-- The `call` map of a gather specification only grows. -/
theorem call_mono {X : Type} [DecidableEq X] {c c' : Gather.SpecState P.n X}
    {id : Fin P.n} {x : X} (h : Gather.Step P c (.call id x) (PMF.pure c'))
    (k : Fin P.n) (v : X) (hv : c.call k = some v) : c'.call k = some v := by
  generalize hμ : (PMF.pure c' : PMF (Gather.SpecState P.n X)) = μ at h
  cases h with
  | call id' x' hc =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    dsimp only
    by_cases hk : k = id
    · subst hk
      rw [hc] at hv
      exact absurd hv (by simp)
    · rw [Function.update_of_ne hk]
      exact hv
  | callLoop id' x' =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact hv

/-- A call of the gather specification writes the caller's entry alone: an
entry of the new `call` map is an old entry or the caller's payload. -/
theorem call_val {X : Type} [DecidableEq X] {c c' : Gather.SpecState P.n X}
    {id : Fin P.n} {x : X} (h : Gather.Step P c (.call id x) (PMF.pure c'))
    (k : Fin P.n) (y : X) (hy : c'.call k = some y) :
    c.call k = some y ∨ (k = id ∧ y = x) := by
  generalize hμ : (PMF.pure c' : PMF (Gather.SpecState P.n X)) = μ at h
  cases h with
  | call id' x' hcl =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    dsimp only at hy
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self] at hy
      exact Or.inr ⟨rfl, (Option.some.inj hy).symm⟩
    · rw [Function.update_of_ne hk] at hy
      exact Or.inl hy
  | callLoop id' x' =>
    have hc' := PMF.pure_injective hμ
    subst hc'
    exact Or.inl hy

/-- The committed-entry support count reads the committed entries and the
corrupted set. -/
theorem firstGatherSupport_congr {t t' : Gather.SpecState P.n Bool} (hval : t'.val = t.val)
    (hF : t'.F = t.F) (v : Bool) : firstGatherSupport t' v = firstGatherSupport t v := by
  unfold firstGatherSupport
  rw [hval, hF]

/-! ### The witnesses -/

/-- What a recorded graded outcome witnesses. A `grade2 v` outcome carries
`some v` on at least `|S| − f` entries of the second gather's core and `v` on at
least `|S| − f` of the first gather's; a `grade1 v` outcome carries `v` on at
least `|S| − f` entries of the first gather's core and `f + 1` committed-entry
support for `!v`; a grade-0 outcome carries each bit on at most `f` entries of
the second gather's core and `f + 1` support for each bit. -/
def OutputWitness (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) : GBCAOutput →
  Prop
  | .grade2 v =>
      (∃ S, (secondGather s).core = some S ∧ S.card - P.f ≤ AcceptedPairs.count S (some v)) ∧
      (∃ S, (firstGather s).core = some S ∧ S.card - P.f ≤ AcceptedPairs.count S v)
  | .grade1 v =>
      (∃ S, (firstGather s).core = some S ∧ S.card - P.f ≤ AcceptedPairs.count S v) ∧
      P.f + 1 ≤ firstGatherSupport (firstGather s) (!v)
  | .grade0 =>
      (∃ S, (secondGather s).core = some S ∧ ∀ w, AcceptedPairs.count S (some w) ≤ P.f) ∧
      ∀ b, P.f + 1 ≤ firstGatherSupport (firstGather s) b

/-- The witness reads the two cores and the first gather's committed-entry
support. A state holding the same cores and at least that support carries
it. -/
theorem OutputWitness.mono {s s' : RoundStateOverGatherSpecifications P.n}
    (h1 : (firstGather s').core = (firstGather s).core)
    (h2 : (secondGather s').core = (secondGather s).core)
    (hv : ∀ b, firstGatherSupport (firstGather s) b ≤ firstGatherSupport (firstGather s') b)
    {out : GBCAOutput} (h : OutputWitness P s out) : OutputWitness P s' out := by
  cases out with
  | grade2 v =>
    obtain ⟨⟨S, hS, hh⟩, S', hS', hh'⟩ := h
    exact ⟨⟨S, by rw [h2]; exact hS, hh⟩, S', by rw [h1]; exact hS', hh'⟩
  | grade1 v =>
    obtain ⟨⟨S, hS, hh⟩, hw⟩ := h
    exact ⟨⟨S, by rw [h1]; exact hS, hh⟩, le_trans hw (hv _)⟩
  | grade0 =>
    obtain ⟨⟨S, hS, hl⟩, hw⟩ := h
    exact ⟨⟨S, by rw [h2]; exact hS, hl⟩, fun b => le_trans (hw b) (hv b)⟩

/-- The exclusion witness: the first gather's core counts `b` below
`|S| − f`, so no later candidate is `b`. It survives every later step: the core is written once. -/
def ExclusionWitness (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) (b : Bool) :
  Prop :=
  ∃ S, (firstGather s).core = some S ∧ AcceptedPairs.count S b < S.card - P.f

end GBCA.ByAFW
end ABA
end PLTS
