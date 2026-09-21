/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.StepOverGatherSpecifications
import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY

/-!
# The refinement of the round over the gather specifications

`GBCA.ByAFW.refinesSpecification`: the round over the gather specifications
(`GBCA.ByAFW.roundOverGatherSpecifications`, `GBCA/AFW/Composition.lean`) forward-simulates the
graded agreement specification read over the round's interface
(`GBCA.ByABDY.specificationOverRoundAlphabet`), along `GBCA.ByAFW.SpecificationRelation`.

A transition of the round is one row of `GBCA.ByAFW.StepOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_row`), the row is answered by a weak run of the
specification (`specificationRelation_row`), and that run is lifted to the interface along a
section of `GBCA.ByABDY.gbcaLabelMap`.

## What the program's record carries

The first gather's return, the second gather's call, its return and the
round's graded return are four separate moves, and what carries the round from
one to the next is the program's record. The invariant therefore states the
first gather's certificates on the program's candidate: `candidate_aboveThreshold` and
`candidate_bot` are established at `firstGatherReturn`, where the first gather's return guards
are in scope, and `secondGatherCall_candidate` transfers the candidate to the second gather's
call record at `secondGatherCall`. The graded outcome is recorded at `secondGatherReturn`, and
`out_certificate` is what the second gather's return guards certify about it:

* a `grade2 v` outcome is heavy at `some v` in the second gather's core and heavy
  at `v` in the first gather's;
* a `grade1 v` outcome is heavy at `v` in the first gather's core and carries
  `f + 1` committed-entry support for `!v`;
* a grade-0 outcome is light at both bits in the second gather's core and carries
  `f + 1` committed-entry support for each bit.

Both cores are write-once, so the certificate survives every later row.

## The bound bit on the label

The return label carries the round's bound bit, which the layer's network
holds. The relation clause `excluded_bound` says the specification's
`excluded` holds nothing but that bit's complement, so a return finds either
`(!bnd) ∈ excluded` already — and fires `ret` alone — or `excluded = ∅` — and
fires `bindUnset (!bnd) ; ret`. A value-bearing outcome's value is the bound
bit, by `boundOfCore_of_aboveThreshold` on the first gather's core, so the
specification's guard pair `v ∉ excluded`, `(!v) ∈ excluded` is the same pair.

The runs are at most two steps — `bindUnset ; ret` through
`weakLStep_tauThen` — the long commit chains live one tier down, inside the
gather instances' own internal rows.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Parameters}

/-! ### The counting kit

The counts the refinement consumes, stated on a gather specification state and
on the graded agreement specification's call record. -/

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

/-- A filter of more than `f` processes contains an honest one. -/
theorem exists_correct_filter {F : Finset (Fin P.n)} (hF : F.card ≤ P.f)
    {p : Fin P.n → Prop} [DecidablePred p]
    (h : P.f + 1 ≤ (Finset.univ.filter p).card) : ∃ k, p k ∧ k ∉ F := by
  have hlt : F.card < (Finset.univ.filter p).card := by
    omega
  obtain ⟨k, hk, hkF⟩ := InstanceState.exists_correct_of_card_lt hlt
  rw [Finset.mem_filter] at hk
  exact ⟨k, hk.2, hkF⟩

/-- Committed-entry support reads as call support on the specification side:
a committed entry of an honest process is its call, and the count is
`F`-blind. -/
theorem callSupport_of_firstGatherSupport {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v)
    {v : Bool} (h : P.f + 1 ≤ firstGatherSupport t1 v) :
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

/-- The core's value entries count into `firstGatherSupport`. -/
theorem count_le_firstGatherSupport {t1 : Gather.SpecState P.n Bool} {U : AcceptedPairs P.n Bool}
    (hUval : U.subMap t1.val) (v : Bool) : AcceptedPairs.count U v ≤ firstGatherSupport t1 v := by
  refine le_trans (AcceptedPairs.count_le_valueCount hUval v) (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, Or.inl hid.2⟩

/-- Core-heavy support reads as call support on the specification side. -/
theorem callSupport_of_core {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v)
    {U : AcceptedPairs P.n Bool} (hUval : U.subMap t1.val) {v : Bool}
    (hcnt : P.f + 1 ≤ AcceptedPairs.count U v) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card :=
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

/-- The call record of a gather specification only grows. -/
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
entry of the new call record is an old entry or the caller's payload. -/
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

/-! ### The invariant -/

/-- What a recorded graded outcome certifies. A `grade2 v` outcome is heavy at
`some v` in the second gather's core and heavy at `v` in the first gather's; a
`grade1 v` outcome is heavy at `v` in the first gather's core and carries `f + 1`
committed-entry support for `!v`; a grade-0 outcome is light at both bits in the
second gather's core and carries `f + 1` support for each bit. -/
def OutputCertificate (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) : GBCAOutput →
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

/-- The certificate reads the two cores and the first gather's committed-entry
support. A state holding the same cores and at least that support carries
it. -/
theorem OutputCertificate.mono {s s' : RoundStateOverGatherSpecifications P.n} (h1 : (firstGather
  s').core =
  (firstGather
  s).core)
    (h2 : (secondGather s').core = (secondGather s).core)
    (hv : ∀ b,
      firstGatherSupport (firstGather s) b ≤ firstGatherSupport (firstGather s') b) {out :
        GBCAOutput}
    (h : OutputCertificate P s out) : OutputCertificate P s' out := by
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

/-- The invariant of the round over the gather specifications. The provenance
clauses are the gather commit guards, per gather; `candidate_aboveThreshold` and `candidate_bot`
record what the candidate the first gather's return determines certifies about
that gather, and `secondGatherCall_candidate` carries the candidate into the second gather's
call record; `candidate_bound` and `secondGatherCall_bound` say that the row writing the
candidate writes the bound bit, and `bound_core` that the bit is read off the
first gather's core; `out_certificate` records what the second gather's return
certifies about the grade; the `core*` clauses re-state the freeze guards,
which the write-once cores keep true. -/
structure Invariant (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) : Prop where
  /-- The corruption budget. -/
  F_card : (firstGather s).F.card ≤ P.f
  /-- The two corrupted sets are in lockstep. -/
  F_eq12 : (secondGather s).F = (firstGather s).F
  /-- A committed first-gather entry of an honest process is its call. -/
  firstGatherVal_provenance : ∀ k v,
    (firstGather s).val k = some v → k ∈ (firstGather s).F ∨ (firstGather s).call k = some v
  /-- A committed second-gather entry of an honest process is its call. -/
  secondGatherVal_provenance : ∀ k c,
    (secondGather s).val k = some c → k ∈ (firstGather s).F ∨ (secondGather s).call k = some c
  /-- An honest process's bit candidate is heavy in the first gather's core. -/
  candidate_aboveThreshold : ∀ k ∉ (firstGather s).F, ∀ v,
    (programs s k).candidate = some (some v) → ∃ S,
      (firstGather s).core = some S ∧ S.card - P.f ≤ AcceptedPairs.count S v
  /-- An honest process's `⊥` candidate certifies `f + 1` committed-entry
  support for both bits. -/
  candidate_bot : ∀ k ∉ (firstGather s).F, (programs s k).candidate = some none →
    P.f + 1 ≤ firstGatherSupport (firstGather s) true ∧ P.f + 1 ≤ firstGatherSupport (firstGather s)
      false
  /-- An honest process's second call carries the candidate it holds. -/
  secondGatherCall_candidate : ∀ k ∉ (firstGather s).F, ∀ x,
    (secondGather s).call k = some x → (programs s k).candidate = some x
  /-- A candidate certifies the bound bit is written: the first gather's return
  writes the candidate and the bit together. -/
  candidate_bound : ∀ k, (programs s k).candidate ≠ none → bound s ≠ none
  /-- A second call certifies the bound bit is written: the bit is written at
  the first gather's return, before any second call. -/
  secondGatherCall_bound : ∀ k, (programs s k).called2 = true → bound s ≠ none
  /-- The bound bit is the bound bit of the first gather's frozen core. -/
  bound_core : ∀ β, bound s = some β → ∃ S, (firstGather s).core = some S ∧ β = boundOfCore P S
  /-- A recorded grade comes with the bound bit and its certificate. -/
  out_certificate : ∀ k out,
    (programs s k).output = some out → bound s ≠ none ∧ OutputCertificate P s out
  /-- The first gather's core is committed entries. -/
  firstGatherCore_val : ∀ S, (firstGather s).core = some S → S.subMap (firstGather s).val
  /-- The first gather's core has `n − f` entries. -/
  firstGatherCore_card : ∀ S, (firstGather s).core = some S → P.n - P.f ≤ S.card
  /-- The second gather's core is committed entries. -/
  secondGatherCore_val : ∀ S, (secondGather s).core = some S → S.subMap (secondGather s).val
  /-- The second gather's core has `n − f` entries. -/
  secondGatherCore_card : ∀ S, (secondGather s).core = some S → P.n - P.f ≤ S.card

/-- The invariant holds initially. -/
theorem Invariant.initial (P : Parameters) (r : ℕ) : Invariant P ((roundOverGatherSpecifications P
  r).init)
  := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, programs, bound, firstGather, secondGather,
      Gather.SpecState.initial, ProcessRecord.initial]

/-- The invariant is preserved by every row. -/
theorem Invariant.step {r : ℕ} {s : RoundStateOverGatherSpecifications P.n} {l : Label P.n}
    {μ : PMF (RoundStateOverGatherSpecifications P.n)} (hInv : Invariant P s) (hstep :
      StepOverGatherSpecifications P r s l μ)
    {s' : RoundStateOverGatherSpecifications P.n} (hs' : s' ∈ μ.support) : Invariant P s' := by
  cases hstep with
  | callG id b t1 h0 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain ⟨hval, hcore, hF⟩ := call_unchanged h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [programs_setFirstGather, programs_setPrograms, firstGather_setFirstGather,
        firstGather_setPrograms, secondGather_setFirstGather, secondGather_setPrograms,
          bound_setFirstGather, bound_setPrograms]
    · rw [hF]; exact hInv.F_card
    · rw [hF]; exact hInv.F_eq12
    · rw [hval, hF]
      intro k v hv
      rcases hInv.firstGatherVal_provenance k v hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_mono h k v hc')
    · rw [hF]; exact hInv.secondGatherVal_provenance
    · rw [hF, hcore]
      intro k hk v hcd
      refine hInv.candidate_aboveThreshold k hk v ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · rw [hF, firstGatherSupport_congr hval hF true, firstGatherSupport_congr hval hF false]
      intro k hk hcd
      refine hInv.candidate_bot k hk ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · rw [hF]
      intro k hk x hx
      have hcd := hInv.secondGatherCall_candidate k hk x hx
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self]
      · rwa [Function.update_of_ne hkid]
    · intro k hcd
      refine hInv.candidate_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hcd
      refine hInv.secondGatherCall_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · rw [hcore]; exact hInv.bound_core
    · intro k out hk
      have hk' : (programs s k).output = some out := by
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hk
        · rwa [Function.update_of_ne hkid] at hk
      refine ⟨(hInv.out_certificate k out hk').1,
        OutputCertificate.mono (s := s) ?_ ?_ ?_ (hInv.out_certificate k out hk').2⟩
      · exact hcore
      · rfl
      · exact fun b => le_of_eq (firstGatherSupport_congr hval hF b).symm
    · rw [hval, hcore]; exact hInv.firstGatherCore_val
    · rw [hcore]; exact hInv.firstGatherCore_card
    · exact hInv.secondGatherCore_val
    · exact hInv.secondGatherCore_card
  | callLoop id b t1 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain ⟨hval, hcore, hF⟩ := call_unchanged h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [programs_setFirstGather, firstGather_setFirstGather, secondGather_setFirstGather,
        bound_setFirstGather]
    · rw [hF]; exact hInv.F_card
    · rw [hF]; exact hInv.F_eq12
    · rw [hval, hF]
      intro k v hv
      rcases hInv.firstGatherVal_provenance k v hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_mono h k v hc')
    · rw [hF]; exact hInv.secondGatherVal_provenance
    · rw [hF, hcore]; exact hInv.candidate_aboveThreshold
    · rw [hF, firstGatherSupport_congr hval hF true,
        firstGatherSupport_congr hval hF false]; exact hInv.candidate_bot
    · rw [hF]; exact hInv.secondGatherCall_candidate
    · exact hInv.candidate_bound
    · exact hInv.secondGatherCall_bound
    · rw [hcore]; exact hInv.bound_core
    · intro k out hk
      refine ⟨(hInv.out_certificate k out hk).1,
        OutputCertificate.mono (s := s) ?_ ?_ ?_ (hInv.out_certificate k out hk).2⟩
      · exact hcore
      · rfl
      · exact fun b => le_of_eq (firstGatherSupport_congr hval hF b).symm
    · rw [hval, hcore]; exact hInv.firstGatherCore_val
    · rw [hcore]; exact hInv.firstGatherCore_card
    · exact hInv.secondGatherCore_val
    · exact hInv.secondGatherCore_card
  | firstGatherTau t1 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      have hvmono : ∀ k' v', (firstGather s).val k' = some v' →
          Function.update (firstGather s).val k (some v) k' = some v' := by
        intro k' v' hv'
        by_cases hk : k' = k
        · subst hk
          rw [hv] at hv'
          exact absurd hv' (by simp)
        · rw [Function.update_of_ne hk]
          exact hv'
      refine ⟨hInv.F_card, hInv.F_eq12, ?_, hInv.secondGatherVal_provenance,
        hInv.candidate_aboveThreshold, ?_, hInv.secondGatherCall_candidate, hInv.candidate_bound,
          hInv.secondGatherCall_bound, hInv.bound_core, ?_,
        ?_, hInv.firstGatherCore_card, hInv.secondGatherCore_val, hInv.secondGatherCore_card⟩
      · intro k' v' hv'
        dsimp only [firstGather_setFirstGather] at hv' ⊢
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self] at hv'
          have hveq : v = v' := by
            injection hv'
          subst hveq
          exact hm
        · rw [Function.update_of_ne hk] at hv'
          exact hInv.firstGatherVal_provenance k' v' hv'
      · intro k' hk' hc
        obtain ⟨h1, h2⟩ := hInv.candidate_bot k' hk' hc
        constructor <;> exact le_trans (by assumption) (firstGatherSupport_mono hvmono (by rfl) _)
      · intro k' out hk'
        refine ⟨(hInv.out_certificate k' out hk').1,
          OutputCertificate.mono (s := s) ?_ ?_ ?_ (hInv.out_certificate k' out hk').2⟩
        · rfl
        · rfl
        · exact fun b => firstGatherSupport_mono hvmono (by rfl) b
      · intro S hS
        have hpre := hInv.firstGatherCore_val S hS
        intro p hp
        exact hvmono p.1 p.2 (hpre p hp)
    | bindCore S h0 hval hcard =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.firstGatherVal_provenance,
        hInv.secondGatherVal_provenance, ?_, hInv.candidate_bot, hInv.secondGatherCall_candidate,
          hInv.candidate_bound, hInv.secondGatherCall_bound, ?_, ?_,
        ?_, ?_, hInv.secondGatherCore_val, hInv.secondGatherCore_card⟩
      · intro k hk v hc
        obtain ⟨S', hS', -⟩ := hInv.candidate_aboveThreshold k hk v hc
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro β hβ
        obtain ⟨S', hS', -⟩ := hInv.bound_core β hβ
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro k out hk
        refine ⟨(hInv.out_certificate k out hk).1, ?_⟩
        have hc := (hInv.out_certificate k out hk).2
        cases out with
        | grade2 v =>
          obtain ⟨-, S', hS', -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
        | grade1 v =>
          obtain ⟨⟨S', hS', -⟩, -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
        | grade0 => exact hc
      · intro S' hS'
        dsimp only [firstGather_setFirstGather] at hS'
        obtain rfl : S = S' := by
          injection hS'
        exact hval
      · intro S' hS'
        dsimp only [firstGather_setFirstGather] at hS'
        obtain rfl : S = S' := by
          injection hS'
        exact hcard
  | secondGatherTau t2 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.firstGatherVal_provenance, ?_,
        hInv.candidate_aboveThreshold, hInv.candidate_bot, hInv.secondGatherCall_candidate,
          hInv.candidate_bound, hInv.secondGatherCall_bound,
        hInv.bound_core, hInv.out_certificate, hInv.firstGatherCore_val, hInv.firstGatherCore_card,
          ?_,
        hInv.secondGatherCore_card⟩
      · intro k' c' hc'
        dsimp only [firstGather_setSecondGather, secondGather_setSecondGather] at hc' ⊢
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self] at hc'
          have hceq : c = c' := by
            injection hc'
          subst hceq
          rcases hm with hF | hin
          · exact Or.inl (by rw [← hInv.F_eq12]; exact hF)
          · exact Or.inr hin
        · rw [Function.update_of_ne hk] at hc'
          exact hInv.secondGatherVal_provenance k' c' hc'
      · intro S hS
        have hpre := hInv.secondGatherCore_val S hS
        intro p hp
        dsimp only [secondGather_setSecondGather]
        by_cases hk : p.1 = k
        · rw [hk, Function.update_self]
          have hpk := hpre p hp
          rw [hk] at hpk
          rw [hv] at hpk
          exact absurd hpk (by simp)
        · rw [Function.update_of_ne hk]
          exact hpre p hp
    | bindCore S h0 hval hcard =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.firstGatherVal_provenance,
        hInv.secondGatherVal_provenance, hInv.candidate_aboveThreshold, hInv.candidate_bot,
          hInv.secondGatherCall_candidate, hInv.candidate_bound,
        hInv.secondGatherCall_bound, hInv.bound_core, ?_, hInv.firstGatherCore_val,
          hInv.firstGatherCore_card,
        ?_, ?_⟩
      · intro k out hk
        refine ⟨(hInv.out_certificate k out hk).1, ?_⟩
        have hc := (hInv.out_certificate k out hk).2
        cases out with
        | grade2 v =>
          obtain ⟨⟨S', hS', -⟩, -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
        | grade1 v => exact hc
        | grade0 =>
          obtain ⟨⟨S', hS', -⟩, -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
      · intro S' hS'
        dsimp only [secondGather_setSecondGather] at hS'
        obtain rfl : S = S' := by
          injection hS'
        exact hval
      · intro S' hS'
        dsimp only [secondGather_setSecondGather] at hS'
        obtain rfl : S = S' := by
          injection hS'
        exact hcard
  | firstGatherReturn id g C t1 hin hc h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      have hCcard : P.n - P.f ≤ C.card := hInv.firstGatherCore_card C hC
      have hgdom : P.n - P.f ≤ domainCount g := le_trans hCcard (AcceptedPairs.card_le_domainCount
        hmem)
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.firstGatherVal_provenance,
        hInv.secondGatherVal_provenance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hInv.firstGatherCore_val,
          hInv.firstGatherCore_card, hInv.secondGatherCore_val,
        hInv.secondGatherCore_card⟩
      · intro k hk v hcd
        dsimp only [programs_setBound, programs_setFirstGather, programs_setPrograms] at hcd
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hcd
          have hcand : candidate P g = some v := by
            injection hcd
          exact ⟨C, hC, count_aboveThreshold_of_subMap hmem (candidate_some hcand)⟩
        · rw [Function.update_of_ne hkid] at hcd
          exact hInv.candidate_aboveThreshold k hk v hcd
      · intro k hk hcd
        dsimp only [programs_setBound, programs_setFirstGather, programs_setPrograms] at hcd
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hcd
          have hcand : candidate P g = none := by
            injection hcd
          have hbot := candidate_none hcand
          have hsum := domainCount_bool_sum g
          have hf := P.hResilience
          constructor
          · have hcnt : P.f + 1 ≤ valueCount g true := by
              have := hbot false
              omega
            refine le_trans hcnt (Finset.card_le_card ?_)
            intro k' hk'
            rw [Finset.mem_filter] at hk' ⊢
            exact ⟨hk'.1, Or.inl (hsubv k' true hk'.2)⟩
          · have hcnt : P.f + 1 ≤ valueCount g false := by
              have := hbot true
              omega
            refine le_trans hcnt (Finset.card_le_card ?_)
            intro k' hk'
            rw [Finset.mem_filter] at hk' ⊢
            exact ⟨hk'.1, Or.inl (hsubv k' false hk'.2)⟩
        · rw [Function.update_of_ne hkid] at hcd
          exact hInv.candidate_bot k hk hcd
      · intro k hk x hx
        dsimp only [programs_setBound, programs_setFirstGather, programs_setPrograms]
        by_cases hkid : k = id
        · subst hkid
          exact absurd (hInv.secondGatherCall_candidate k hk x hx) (by rw [hc]; simp)
        · rw [Function.update_of_ne hkid]
          exact hInv.secondGatherCall_candidate k hk x hx
      · intro k _
        dsimp only [bound_setBound]
        exact Option.some_ne_none _
      · intro k _
        dsimp only [bound_setBound]
        exact Option.some_ne_none _
      · intro β hβ
        dsimp only [bound_setBound] at hβ
        obtain rfl : (bound s).getD (boundOfCore P C) = β := by
          injection hβ
        rcases hb : bound s with _ | β₀
        · exact ⟨C, hC, rfl⟩
        · exact hInv.bound_core β₀ hb
      · intro k out hk
        dsimp only [programs_setBound, programs_setFirstGather, programs_setPrograms] at hk
        refine ⟨by dsimp only [bound_setBound]; exact Option.some_ne_none _,
          OutputCertificate.mono rfl rfl (fun _ => le_refl _) (hInv.out_certificate k out ?_).2⟩
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hk
        · rwa [Function.update_of_ne hkid] at hk
  | secondGatherCall id x t2 hc h2 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain ⟨hval2, hcore2, hF2⟩ := call_unchanged h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [programs_setSecondGather, programs_setPrograms, firstGather_setSecondGather,
        firstGather_setPrograms, secondGather_setSecondGather, secondGather_setPrograms,
          bound_setSecondGather, bound_setPrograms]
    · exact hInv.F_card
    · rw [hF2]; exact hInv.F_eq12
    · exact hInv.firstGatherVal_provenance
    · rw [hval2]
      intro k c hv
      rcases hInv.secondGatherVal_provenance k c hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_mono h k c hc')
    · intro k hk v hcd
      refine hInv.candidate_aboveThreshold k hk v ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk hcd
      refine hInv.candidate_bot k hk ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk y hy
      rcases call_val h k y hy with hold | ⟨rfl, rfl⟩
      · have hcd := hInv.secondGatherCall_candidate k hk y hold
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self]
        · rwa [Function.update_of_ne hkid]
      · rw [Function.update_self]
        exact hc
    · intro k hcd
      refine hInv.candidate_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hcd
      by_cases hkid : k = id
      · subst hkid
        exact hInv.candidate_bound k (by rw [hc]; simp)
      · rw [Function.update_of_ne hkid] at hcd
        exact hInv.secondGatherCall_bound k hcd
    · exact hInv.bound_core
    · intro k out hk
      have hk' : (programs s k).output = some out := by
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hk
        · rwa [Function.update_of_ne hkid] at hk
      refine ⟨(hInv.out_certificate k out hk').1,
        OutputCertificate.mono (s := s) ?_ ?_ ?_ (hInv.out_certificate k out hk').2⟩
      · rfl
      · exact hcore2
      · exact fun _ => le_refl _
    · exact hInv.firstGatherCore_val
    · exact hInv.firstGatherCore_card
    · rw [hcore2, hval2]; exact hInv.secondGatherCore_val
    · rw [hcore2]; exact hInv.secondGatherCore_card
  | retG id out ho hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_eq12, hInv.firstGatherVal_provenance,
      hInv.secondGatherVal_provenance, ?_, ?_, ?_, ?_, ?_, hInv.bound_core, ?_,
        hInv.firstGatherCore_val, hInv.firstGatherCore_card,
      hInv.secondGatherCore_val, hInv.secondGatherCore_card⟩ <;> dsimp only [programs_setPrograms]
    · intro k hk v hcd
      refine hInv.candidate_aboveThreshold k hk v ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk hcd
      refine hInv.candidate_bot k hk ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk y hy
      have hcd := hInv.secondGatherCall_candidate k hk y hy
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self]
      · rwa [Function.update_of_ne hkid]
    · intro k hcd
      refine hInv.candidate_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hcd
      refine hInv.secondGatherCall_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k out' hk
      have hk' : (programs s k).output = some out' := by
        by_cases hkid : k = id
        · subst hkid; rw [Function.update_self] at hk; exact absurd hk (by simp)
        · rwa [Function.update_of_ne hkid] at hk
      exact hInv.out_certificate k out' hk'
  | secondGatherReturn id g C t2 h2 ho h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      have hf := P.hResilience
      have hbnd : bound s ≠ none := hInv.secondGatherCall_bound id h2
      have hCcard : P.n - P.f ≤ C.card := hInv.secondGatherCore_card C hC
      have hgdom : P.n - P.f ≤ domainCount g := le_trans hCcard (AcceptedPairs.card_le_domainCount
        hmem)
      have hchain : ∀ k, k ∉ (firstGather s).F → ∀ c,
        g k = some c → (programs s k).candidate = some c:= by
        intro k hkF c hgc
        rcases hInv.secondGatherVal_provenance k c (hsubv k c hgc) with hF | hin
        · exact absurd hF hkF
        · exact hInv.secondGatherCall_candidate k hkF c hin
      have hheavy1 : ∀ v : Bool, P.f + 1 ≤ valueCount g (some v) →
          ∃ S, (firstGather s).core = some S ∧ S.card - P.f ≤ AcceptedPairs.count S v := by
        intro v hcnt
        obtain ⟨kh, hkhg, hkhF⟩ := exists_correct_filter hInv.F_card
          (p := fun k => g k = some (some v)) hcnt
        exact hInv.candidate_aboveThreshold kh hkhF v (hchain kh hkhF (some v) hkhg)
      have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
          (fun k => g k ≠ none ∧ g k ≠ some (some (!b)))).card →
          P.f + 1 ≤ firstGatherSupport (firstGather s) b := by
        intro b hcard
        obtain ⟨kt, hkt, hktF⟩ := exists_correct_filter hInv.F_card hcard
        rcases hgkt : g kt with _ | ct
        · exact absurd hgkt hkt.1
        have hcand := hchain kt hktF ct hgkt
        rcases ct with _ | wt
        · obtain ⟨hsT, hsF⟩ := hInv.candidate_bot kt hktF hcand
          cases b
          · exact hsF
          · exact hsT
        · have hwt : wt = b := by
            by_contra hne
            have hb : wt = !b := by
              cases wt <;> cases b <;> simp_all
            subst hb
            exact hkt.2 hgkt
          subst hwt
          obtain ⟨S, hS, hh⟩ := hInv.candidate_aboveThreshold kt hktF wt hcand
          have hScard := hInv.firstGatherCore_card S hS
          exact le_trans (by omega : P.f + 1 ≤ AcceptedPairs.count S wt)
            (count_le_firstGatherSupport (hInv.firstGatherCore_val S hS) wt)
      have hcert : OutputCertificate P s (gradeOf P g) := by
        cases hout : gradeOf P g with
        | grade2 v =>
          refine ⟨⟨C, hC, count_aboveThreshold_of_subMap hmem (gradeOf_grade2 hout)⟩, hheavy1 v ?_⟩
          have := gradeOf_grade2 hout
          omega
        | grade1 v =>
          obtain ⟨hBcnt, hBnotA⟩ := gradeOf_grade1 hout
          refine ⟨hheavy1 v hBcnt, hsupp (!v) ?_⟩
          simp only [Bool.not_not]
          rw [card_ne_valueCount]
          have := hBnotA v
          omega
        | grade0 =>
          have hCgrade := gradeOf_grade0 hout
          refine ⟨⟨C, hC,
            fun w => le_trans (AcceptedPairs.count_le_valueCount hmem (some w)) (hCgrade w)⟩,
              fun b => hsupp b ?_⟩
          rw [card_ne_valueCount]
          have := hCgrade (!b)
          omega
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.firstGatherVal_provenance,
        hInv.secondGatherVal_provenance, ?_, ?_, ?_, ?_, ?_, hInv.bound_core, ?_,
          hInv.firstGatherCore_val, hInv.firstGatherCore_card,
        hInv.secondGatherCore_val, hInv.secondGatherCore_card⟩
      · intro k hk v hcd
        refine hInv.candidate_aboveThreshold k hk v ?_
        dsimp only [programs_setSecondGather, programs_setPrograms] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k hk hcd
        refine hInv.candidate_bot k hk ?_
        dsimp only [programs_setSecondGather, programs_setPrograms] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k hk x hx
        have hcd := hInv.secondGatherCall_candidate k hk x hx
        dsimp only [programs_setSecondGather, programs_setPrograms]
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self]
        · rwa [Function.update_of_ne hkid]
      · intro k hcd
        refine hInv.candidate_bound k ?_
        dsimp only [programs_setSecondGather, programs_setPrograms] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k hcd
        refine hInv.secondGatherCall_bound k ?_
        dsimp only [programs_setSecondGather, programs_setPrograms] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k out hk
        dsimp only [programs_setSecondGather, programs_setPrograms] at hk
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hk
          obtain rfl : gradeOf P g = out := by
            injection hk
          exact ⟨hbnd, OutputCertificate.mono rfl rfl (fun _ => le_refl _) hcert⟩
        · rw [Function.update_of_ne hkid] at hk
          obtain ⟨hb, hc⟩ := hInv.out_certificate k out hk
          exact ⟨hb, OutputCertificate.mono rfl rfl (fun _ => le_refl _) hc⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hFsub : (firstGather s).F ⊆ ((firstGather s).corrupt P id).F := by
      rw [Gather.SpecState.corrupt_F]
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
    have hF' : ∀ k, k ∉ ((firstGather s).corrupt P id).F → k ∉ (firstGather s).F :=
      fun k hk hkF => hk (hFsub hkF)
    have hsmono : ∀ b,
      firstGatherSupport (firstGather s) b ≤ firstGatherSupport ((firstGather s).corrupt P id) b :=
        fun b => firstGatherSupport_mono (fun k' v' hv' => by rw [Gather.corrupt_val]; exact hv')
          hFsub b
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [programs_corruptAll, bound_corruptAll, firstGather_corruptAll,
        secondGather_corruptAll]
    · rw [Gather.SpecState.corrupt_F]
      split
      · next hcs =>
        have hins := Finset.card_insert_le id (firstGather s).F
        have hlt := hcs.2
        omega
      · exact hInv.F_card
    · rw [Gather.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hInv.F_eq12]
    · intro k v hv
      rw [Gather.corrupt_val] at hv
      rw [Gather.corrupt_call]
      rcases hInv.firstGatherVal_provenance k v hv with hF | hcl
      · exact Or.inl (hFsub hF)
      · exact Or.inr hcl
    · intro k c hcv
      rw [Gather.corrupt_val] at hcv
      rw [Gather.corrupt_call]
      rcases hInv.secondGatherVal_provenance k c hcv with hF | hin
      · exact Or.inl (hFsub hF)
      · exact Or.inr hin
    · intro k hk v hcd
      obtain ⟨S, hS, hh⟩ := hInv.candidate_aboveThreshold k (hF' k hk) v hcd
      exact ⟨S, by rw [Gather.corrupt_core]; exact hS, hh⟩
    · intro k hk hcd
      obtain ⟨h1, h2⟩ := hInv.candidate_bot k (hF' k hk) hcd
      exact ⟨le_trans h1 (hsmono true), le_trans h2 (hsmono false)⟩
    · intro k hk x hx
      rw [Gather.corrupt_call] at hx
      exact hInv.secondGatherCall_candidate k (hF' k hk) x hx
    · exact hInv.candidate_bound
    · exact hInv.secondGatherCall_bound
    · intro β hβ
      obtain ⟨S, hS, hh⟩ := hInv.bound_core β hβ
      exact ⟨S, by rw [Gather.corrupt_core]; exact hS, hh⟩
    · intro k out hk
      refine ⟨(hInv.out_certificate k out hk).1,
        OutputCertificate.mono (s := s) ?_ ?_ ?_ (hInv.out_certificate k out hk).2⟩
      · rw [firstGather_corruptAll, Gather.corrupt_core]
      · rw [secondGather_corruptAll, Gather.corrupt_core]
      · exact fun b => by rw [firstGather_corruptAll]; exact hsmono b
    · intro S hS
      rw [Gather.corrupt_core] at hS
      have hpre := hInv.firstGatherCore_val S hS
      intro p hp
      rw [Gather.corrupt_val]
      exact hpre p hp
    · intro S hS
      rw [Gather.corrupt_core] at hS
      exact hInv.firstGatherCore_card S hS
    · intro S hS
      rw [Gather.corrupt_core] at hS
      have hpre := hInv.secondGatherCore_val S hS
      intro p hp
      rw [Gather.corrupt_val]
      exact hpre p hp
    · intro S hS
      rw [Gather.corrupt_core] at hS
      exact hInv.secondGatherCore_card S hS

/-! ### The relation -/

/-- The exclusion certificate: the first gather's core counts `b` below
`|S| − f`, so no later candidate is `b`. Frozen — the core is write-once. -/
def ExclusionEvidence (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) (b : Bool) :
  Prop :=
  ∃ S, (firstGather s).core = some S ∧ AcceptedPairs.count S b < S.card - P.f

/-- The refinement relation of the round over the gather specifications. -/
structure SpecificationRelation (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) (t :
  GBCA.SpecState
  P.n)
  : Prop where
  /-- The invariant. -/
  invariant : Invariant P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = (firstGather s).call k
  /-- The return flags agree: the specification returns at the graded return,
  which the program marks. -/
  ret_eq : ∀ id, t.ret id = (programs s id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = (firstGather s).F
  /-- An excluded bit is certified excluded. -/
  exclusion_certificate : ∀ b ∈ t.excluded, ExclusionEvidence P s b
  /-- An excluded bit is the complement of the round's bound bit: the
  exclusion is written inside the first return's run, which announces that
  bit. -/
  excluded_bound : ∀ b ∈ t.excluded, ∃ β, bound s = some β ∧ b = !β
  /-- The grade-2 guard is certified by a value heavy in the second gather's
  core. -/
  grade2_evidence : t.grade = some true → ∃ S v, (secondGather s).core = some S ∧
    S.card - P.f ≤ AcceptedPairs.count S (some v)
  /-- The grade-0 guard is certified by the second gather's core being light
  at both bits. -/
  grade0_evidence : t.grade = some false → ∃ S, (secondGather s).core = some S ∧
    ∀ v, AcceptedPairs.count S (some v) ≤ P.f

/-- The relation holds initially. -/
theorem specificationRelation_init (P : Parameters) (r : ℕ) :
    SpecificationRelation P ((roundOverGatherSpecifications P r).init)
      ((GBCA.ByABDY.specificationOverRoundAlphabet P r).init) := by
  refine ⟨Invariant.initial P r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, programs, bound, firstGather, secondGather,
      Gather.SpecState.initial, GBCA.SpecState.initial, ProcessRecord.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem specificationRelation_corrupt {r : ℕ} {s : RoundStateOverGatherSpecifications P.n} {t :
  GBCA.SpecState
  P.n}
    (hR : SpecificationRelation P s t) (id : Fin P.n) :
    SpecificationRelation P (corruptAll P id (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt
      P) s)
      (t.corrupt P id) := by
  refine ⟨hR.invariant.step (r := r) (StepOverGatherSpecifications.fail s id) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp only [firstGather_corruptAll]
    rw [GBCA.corrupt_call, Gather.corrupt_call]
    exact hR.call_eq k
  · intro k
    rw [GBCA.corrupt_ret]
    exact hR.ret_eq k
  · dsimp only [firstGather_corruptAll]
    rw [GBCA.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hR.F_eq]
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    obtain ⟨S, hS, hl⟩ := hR.exclusion_certificate b hb
    exact ⟨S, by rw [firstGather_corruptAll, Gather.corrupt_core]; exact hS, hl⟩
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    exact hR.excluded_bound b hb
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, v, hS, hh⟩ := hR.grade2_evidence hg
    exact ⟨S, v, by rw [secondGather_corruptAll, Gather.corrupt_core]; exact hS, hh⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, hS, hl⟩ := hR.grade0_evidence hg
    exact ⟨S, by rw [secondGather_corruptAll, Gather.corrupt_core]; exact hS, hl⟩

/-! ### The row-wise leg -/

/-- **The row-wise leg**: every row of the round is answered by a weak run of
the graded agreement specification, the relation restored. -/
theorem specificationRelation_row (P : Parameters) (r : ℕ) (q₁ : RoundStateOverGatherSpecifications
  P.n)
    (q₂ : GBCA.SpecState P.n) (hR : SpecificationRelation P q₁ q₂) (l₀ : Label P.n)
    (μ : PMF (RoundStateOverGatherSpecifications P.n)) (hrow : StepOverGatherSpecifications P r q₁
      l₀ μ)
    (q₁' : RoundStateOverGatherSpecifications P.n) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLSilent q₂ q₂') ∨
      (¬ l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLStep q₂ l₀ q₂')) ∧
      SpecificationRelation P q₁' q₂' := by
  have hInv' := hR.invariant.step hrow hq₁'
  cases hrow with
  | callG id b t1 h0 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall))⟩,
        hInv', ?_, ?_, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      · intro k
        dsimp only [firstGather_setFirstGather]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hk, Function.update_of_ne hk]
          exact hR.call_eq k
      · intro k
        dsimp only [programs_setFirstGather, programs_setPrograms]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          exact hR.ret_eq k
        · rw [Function.update_of_ne hk]
          exact hR.ret_eq k
    | callLoop id' b' =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (GBCA.Step.callLoop q₂ id b)⟩, hInv', hR.call_eq, ?_, hR.F_eq,
        hR.exclusion_certificate, hR.excluded_bound, hR.grade2_evidence, hR.grade0_evidence⟩
      intro k
      dsimp only [programs_setFirstGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | callLoop id b t1 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨{ q₂ with call := Function.update q₂.call id (some b) },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.call q₂ id b (by rw [hR.call_eq id]; exact hcall))⟩,
        hInv', ?_, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      intro k
      dsimp only [firstGather_setFirstGather]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.call_eq k
    | callLoop id' b' =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (GBCA.Step.callLoop q₂ id b)⟩, hR⟩
  | firstGatherTau t1 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
    | bindCore S h0 hval hcard =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      intro b hb
      obtain ⟨S', hS', -⟩ := hR.exclusion_certificate b hb
      rw [h0] at hS'
      exact absurd hS' (by simp)
  | secondGatherTau t2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
    | bindCore S h0 hval hcard =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        ?_, ?_⟩
      · intro hg
        obtain ⟨S', v, hS', -⟩ := hR.grade2_evidence hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro hg
        obtain ⟨S', hS', -⟩ := hR.grade0_evidence hg
        rw [h0] at hS'
        exact absurd hS' (by simp)
  | firstGatherReturn id g C t1 hin hc h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.exclusion_certificate, ?_, hR.grade2_evidence,
        hR.grade0_evidence⟩
      · intro k
        dsimp only [programs_setBound, programs_setFirstGather, programs_setPrograms]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          exact hR.ret_eq k
        · rw [Function.update_of_ne hk]
          exact hR.ret_eq k
      · intro b hb
        obtain ⟨β, hβ, hbβ⟩ := hR.excluded_bound b hb
        exact ⟨β, by dsimp only [bound_setBound]; rw [hβ]; rfl, hbβ⟩
  | secondGatherCall id x t2 hc h2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨hval2, hcore2, hF2⟩ := call_unchanged h
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
      hR.call_eq, ?_, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound, ?_, ?_⟩
    · intro k
      dsimp only [programs_setSecondGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
    · intro hg
      obtain ⟨S, v, hS, hh⟩ := hR.grade2_evidence hg
      exact ⟨S, v, by dsimp only [secondGather_setSecondGather,
        secondGather_setPrograms]; rw [hcore2]; exact hS, hh⟩
    · intro hg
      obtain ⟨S, hS, hl⟩ := hR.grade0_evidence hg
      exact ⟨S, by dsimp only [secondGather_setSecondGather,
        secondGather_setPrograms]; rw [hcore2]; exact hS, hl⟩
  | secondGatherReturn id g C t2 h2 ho h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.exclusion_certificate, hR.excluded_bound,
        hR.grade2_evidence, hR.grade0_evidence⟩
      intro k
      dsimp only [programs_setSecondGather, programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | retG id out ho hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hf := P.hResilience
    obtain ⟨hbnd, hcert⟩ := hR.invariant.out_certificate id out ho
    have hretflag : q₂.ret id = false := by
      rw [hR.ret_eq id]
      exact hr
    obtain ⟨β, hβ⟩ : ∃ β, bound q₁ = some β := Option.ne_none_iff_exists'.mp hbnd
    obtain ⟨S, hS, hβS⟩ := hR.invariant.bound_core β hβ
    have hScard : P.n - P.f ≤ S.card := hR.invariant.firstGatherCore_card S hS
    have hSval := hR.invariant.firstGatherCore_val S hS
    have hlight : ExclusionEvidence P q₁ (!β) :=
      ⟨S, hS, by rw [hβS]; exact count_boundOfCore_belowThreshold hScard⟩
    have hexcl : ∀ b ∈ q₂.excluded, b = !β := by
      intro b hb
      obtain ⟨β', hβ', rfl⟩ := hR.excluded_bound b hb
      rw [hβ] at hβ'
      obtain rfl : β = β' := Option.some.inj hβ'
      rfl
    have hret_eq : ∀ k, Function.update q₂.ret id true k =
        (programs (setPrograms q₁ (Function.update (programs q₁) id
          { programs q₁ id with output := none, returned := true })) k).returned := by
      intro k
      dsimp only [programs_setPrograms]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.ret_eq k
    have hbndeq : (bound q₁).getD (boundOfCore P (∅ : AcceptedPairs P.n Bool)) = β := by
      rw [hβ]
      rfl
    rw [hbndeq]
    cases out with
    | grade2 v =>
      obtain ⟨⟨C₂, hC₂, hA_ev⟩, S', hS', hheavy⟩ := hcert
      obtain rfl : S = S' := by
        rw [hS] at hS'; exact Option.some.inj hS'
      have hC₂card : P.n - P.f ≤ C₂.card := hR.invariant.secondGatherCore_card C₂ hC₂
      have hβv : β = v := by
        rw [hβS]
        exact boundOfCore_of_aboveThreshold hScard hheavy
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
            obtain ⟨S₂, hS₂, hlight₂⟩ := hR.grade0_evidence hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hlight₂ v
            omega
          · exact Or.inr rfl
      by_cases hbv : (!v) ∈ q₂.excluded
      · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade2 q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
            hgA hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_certificate,
          hR.excluded_bound, ?_, ?_⟩
        · intro _
          exact ⟨C₂, v, hC₂, hA_ev⟩
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
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance hSval hScard)
            (by
              rw [Bool.not_not]
              exact callSupport_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
                hSval (by omega))
            hd0
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.grade2 v) β)
            { q₂ with
              excluded := insert (!v) q₂.excluded
              grade := some true
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade2 _ id v β (by rw [hd0]; simp)
            (Finset.mem_insert_self _ _)
            (by rw [hβv]; exact Finset.mem_insert_self _ _) hgA hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, ?_⟩
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · rw [← hβv]
            exact hlight
          · simp at hb
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact ⟨β, hβ, by rw [hβv]⟩
          · simp at hb
        · intro _
          exact ⟨C₂, v, hC₂, hA_ev⟩
        · intro hgr
          exact absurd hgr (by simp)
    | grade1 v =>
      obtain ⟨⟨S', hS', hheavy⟩, hw1⟩ := hcert
      obtain rfl : S = S' := by
        rw [hS] at hS'; exact Option.some.inj hS'
      have hβv : β = v := by
        rw [hβS]
        exact boundOfCore_of_aboveThreshold hScard hheavy
      have hlive : v ∉ q₂.excluded := by
        intro hv
        have hb := hexcl v hv
        rw [hβv] at hb
        simp at hb
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some (!v) ∨ id' ∈ q₂.F)).card :=
        callSupport_of_firstGatherSupport hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
          hw1
      by_cases hbv : (!v) ∈ q₂.excluded
      · exact ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade1 q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
            hw hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_certificate,
          hR.excluded_bound, hR.grade2_evidence, hR.grade0_evidence⟩
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
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance hSval hScard)
            (by
              rw [Bool.not_not]
              exact callSupport_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
                hSval (by omega))
            hd0
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!v) q₂.excluded } (.retG r id (.grade1 v) β)
            { q₂ with
              excluded := insert (!v) q₂.excluded
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade1 _ id v β (by rw [hd0]; simp)
            (Finset.mem_insert_self _ _)
            (by rw [hβv]; exact Finset.mem_insert_self _ _) hw hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, hR.grade2_evidence,
          hR.grade0_evidence⟩
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · rw [← hβv]
            exact hlight
          · simp at hb
        · intro b hb
          dsimp only at hb
          rw [hd0, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact ⟨β, hβ, by rw [hβv]⟩
          · simp at hb
    | grade0 =>
      obtain ⟨⟨C₂, hC₂, hClight⟩, hsupp1⟩ := hcert
      have hC₂card : P.n - P.f ≤ C₂.card := hR.invariant.secondGatherCore_card C₂ hC₂
      have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some b ∨ id' ∈ q₂.F)).card := fun b =>
        callSupport_of_firstGatherSupport hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance
          (hsupp1 b)
      have hgC : q₂.grade = none ∨ q₂.grade = some false := by
        rcases hgr : q₂.grade with _ | b
        · exact Or.inl rfl
        · cases b
          · exact Or.inr rfl
          · exfalso
            obtain ⟨S₂, v', hS₂, hh⟩ := hR.grade2_evidence hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hClight v'
            omega
      by_cases hdne : q₂.excluded = ∅
      · have hexclude : (GBCA.specInst P r).LStep q₂ Silent.τ
            { q₂ with excluded := insert (!β) q₂.excluded } :=
          GBCA.Step.bindUnset q₂ (!β)
            (quorum_of_core hR.call_eq hR.F_eq hR.invariant.firstGatherVal_provenance hSval hScard)
            (by rw [Bool.not_not]; exact hsupp β)
            hdne
        have hret2 : (GBCA.specInst P r).LStep
            { q₂ with excluded := insert (!β) q₂.excluded } (.retG r id .grade0 β)
            { q₂ with
              excluded := insert (!β) q₂.excluded
              grade := some false
              ret := Function.update q₂.ret id true } :=
          GBCA.Step.retGrade0 _ id β (Finset.mem_insert_self _ _)
            (hsupp true) (hsupp false) hgC hretflag
        refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hexclude hret2 (by simp)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, ?_, ?_⟩
        · intro b hb
          dsimp only at hb
          rw [hdne, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact hlight
          · simp at hb
        · intro b hb
          dsimp only at hb
          rw [hdne, Finset.mem_insert] at hb
          rcases hb with rfl | hb
          · exact ⟨β, hβ, rfl⟩
          · simp at hb
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hClight⟩
      · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hdne
        have hbeq := hexcl b hb
        subst hbeq
        refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retGrade0 q₂ id β hb (hsupp true) (hsupp false) hgC hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.exclusion_certificate,
          hR.excluded_bound, ?_, ?_⟩
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hClight⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (GBCA.Step.fail q₂ id)⟩, specificationRelation_corrupt (r := r) hR id⟩

/-! ### The refinement -/

/-- **The refinement of the round over the gather specifications**: the round
forward-simulates the graded agreement specification read over the round's
interface. A transition of the round is one row of `GBCA.ByAFW.StepOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_row`), the row is answered by a weak run of the
specification (`specificationRelation_row`), and that run is lifted to the interface along a
section of `GBCA.ByABDY.gbcaLabelMap`. -/
theorem refinesSpecification (P : Parameters) (r : ℕ) :
    ForwardSimulation (roundOverGatherSpecifications P r)
      (GBCA.ByABDY.specificationOverRoundAlphabet P r) (SpecificationRelation P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := roundOverGatherSpecifications_step_row P r q₁ l μ hstep
  obtain ⟨t', hdis, hrel⟩ := specificationRelation_row P r q₁ q₂ hR l₀ μ hrow q₁' hq₁'
  refine ⟨t', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨GBCA.ByABDY.gbcaLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      GBCA.ByABDY.weakLSilent_specificationOverRoundAlphabet P r hweak⟩
  · refine Or.inr ⟨?_, GBCA.ByABDY.weakLStep_specificationOverRoundAlphabet P r hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : GBCA.ByABDY.gbcaLabelMap P.n (Silent.τ : Composition.ExtendedLabel P.n) = some l₀ :=
      by
      rw [← hl]; exact hpull
    rw [GBCA.ByABDY.gbcaLabelMap_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByAFW.refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesSpecification

/-- info: 'PLTS.ABA.GBCA.ByAFW.specificationRelation_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationRelation_corrupt

end GBCA.ByAFW
end ABA
end PLTS
