/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.StepOverGatherSpecifications
import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY

/-!
# The refinement of the round over the gather specifications

`GBCA.ByAFW.pairRefines`: the round over the gather specifications
(`GBCA.ByAFW.roundOverGatherSpecifications`, `GBCA/AFW/Composition.lean`) forward-simulates the
graded agreement specification read over the round's interface
(`GBCA.ByABDY.specificationOverRoundAlphabet`), along `GBCA.ByAFW.PairRel`.

A transition of the round is one row of `GBCA.ByAFW.StepOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_row`), the row is answered by a weak run of the
specification (`pairRel_row`), and that run is lifted to the interface along a
section of `GBCA.ByABDY.gbcaLabelMap`.

## What the program's record carries

The first gather's return, the second gather's call, its return and the
round's graded return are four separate moves, and what carries the round from
one to the next is the program's record. The invariant therefore states the
first gather's certificates on the program's candidate: `cand_heavy` and
`cand_bot` are established at `ret1`, where the first gather's return guards
are in scope, and `call2_cand` transfers the candidate to the second gather's
call record at `call2`. The graded outcome is recorded at `ret2`, and
`out_cert` is what the second gather's return guards certify about it:

* an `A v` outcome is heavy at `some v` in the second gather's core and heavy
  at `v` in the first gather's;
* a `B v` outcome is heavy at `v` in the first gather's core and carries
  `f + 1` committed-entry support for `!v`;
* a `C` outcome is light at both bits in the second gather's core and carries
  `f + 1` committed-entry support for each bit.

Both cores are write-once, so the certificate survives every later row.

## The bound bit on the label

The return label carries the round's bound bit, which the layer's network
holds. The relation clause `excluded_bound` says the specification's
`excluded` holds nothing but that bit's complement, so a return finds either
`(!bnd) ∈ excluded` already — and fires `ret` alone — or `excluded = ∅` — and
fires `bindUnset (!bnd) ; ret`. A value-bearing outcome's value is the bound
bit, by `boundOfCore_of_heavy` on the first gather's core, so the
specification's guard pair `v ∉ excluded`, `(!v) ∈ excluded` is the same pair.

The runs are at most two steps — `bindUnset ; ret` through
`weakLStep_tauThen` — the long commit chains live one tier down, inside the
gather instances' own internal rows.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Params}

/-! ### The counting kit

The counts the refinement consumes, stated on a gather specification state and
on the graded agreement specification's call record. -/

/-- Committed entries only grow: an entry-wise extension preserves `supp1`. -/
theorem supp1_mono {t t' : Gather.SpecState P.n Bool}
    (hval : ∀ k v, t.val k = some v → t'.val k = some v) (hF : t.F ⊆ t'.F)
    (v : Bool) : supp1 t v ≤ supp1 t' v := by
  refine Finset.card_le_card ?_
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  rcases hid.2 with h | h
  · exact ⟨hid.1, Or.inl (hval id v h)⟩
  · exact ⟨hid.1, Or.inr (hF h)⟩

/-- A filter of more than `f` processes contains an honest one. -/
theorem exists_honest_filter {F : Finset (Fin P.n)} (hF : F.card ≤ P.f)
    {p : Fin P.n → Prop} [DecidablePred p]
    (h : P.f + 1 ≤ (Finset.univ.filter p).card) : ∃ k, p k ∧ k ∉ F := by
  have hlt : F.card < (Finset.univ.filter p).card := by omega
  obtain ⟨k, hk, hkF⟩ := SubState.exists_honest_of_card_lt hlt
  rw [Finset.mem_filter] at hk
  exact ⟨k, hk.2, hkF⟩

/-- Committed-entry support reads as call support on the specification side:
a committed entry of an honest process is its call, and the count is
`F`-blind. -/
theorem spec_supp_of_supp1 {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v)
    {v : Bool} (h : P.f + 1 ≤ supp1 t1 v) :
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
theorem cnt_le_supp1 {t1 : Gather.SpecState P.n Bool} {U : APSet P.n Bool}
    (hUval : U.subMap t1.val) (v : Bool) : APSet.cnt U v ≤ supp1 t1 v := by
  refine le_trans (APSet.cnt_le_gcount hUval v) (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, Or.inl hid.2⟩

/-- Core-heavy support reads as call support on the specification side. -/
theorem supp_spec_of_core {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v)
    {U : APSet P.n Bool} (hUval : U.subMap t1.val) {v : Bool}
    (hcnt : P.f + 1 ≤ APSet.cnt U v) :
    P.f + 1 ≤ (Finset.univ.filter
      (fun id' => t.call id' = some v ∨ id' ∈ t.F)).card :=
  spec_supp_of_supp1 hcall hF hprov (le_trans hcnt (cnt_le_supp1 hUval v))

/-- The first gather's core discharges the specification's quorum guard: its
`n − f` distinct processes each carry a committed entry, hence a call or a
corruption. -/
theorem quorum_of_core {t1 : Gather.SpecState P.n Bool} {t : GBCA.SpecState P.n}
    (hcall : ∀ k, t.call k = t1.call k) (hF : t.F = t1.F)
    (hprov : ∀ k v, t1.val k = some v → k ∈ t1.F ∨ t1.call k = some v)
    {U : APSet P.n Bool} (hUval : U.subMap t1.val)
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

/-- A call of the gather specification leaves the committed entries, the core
and the corrupted set alone. -/
theorem call_frame {X : Type} [DecidableEq X] {c c' : Gather.SpecState P.n X}
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
theorem call_prov {X : Type} [DecidableEq X] {c c' : Gather.SpecState P.n X}
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
theorem supp1_congr {t t' : Gather.SpecState P.n Bool} (hval : t'.val = t.val)
    (hF : t'.F = t.F) (v : Bool) : supp1 t' v = supp1 t v := by
  unfold supp1
  rw [hval, hF]

/-! ### The invariant -/

/-- What a recorded graded outcome certifies. An `A v` outcome is heavy at
`some v` in the second gather's core and heavy at `v` in the first gather's; a
`B v` outcome is heavy at `v` in the first gather's core and carries `f + 1`
committed-entry support for `!v`; a `C` outcome is light at both bits in the
second gather's core and carries `f + 1` support for each bit. -/
def OutCert (P : Params) (s : RoundStateOverGatherSpecifications P.n) : GbcaOut → Prop
  | .A v => (∃ S, (ga2 s).core = some S ∧ S.card - P.f ≤ APSet.cnt S (some v)) ∧
      (∃ S, (ga1 s).core = some S ∧ S.card - P.f ≤ APSet.cnt S v)
  | .B v => (∃ S, (ga1 s).core = some S ∧ S.card - P.f ≤ APSet.cnt S v) ∧
      P.f + 1 ≤ supp1 (ga1 s) (!v)
  | .C => (∃ S, (ga2 s).core = some S ∧ ∀ w, APSet.cnt S (some w) ≤ P.f) ∧
      ∀ b, P.f + 1 ≤ supp1 (ga1 s) b

/-- The certificate reads the two cores and the first gather's committed-entry
support. A state holding the same cores and at least that support carries
it. -/
theorem OutCert.mono {s s' : RoundStateOverGatherSpecifications P.n} (h1 : (ga1 s').core = (ga1
  s).core)
    (h2 : (ga2 s').core = (ga2 s).core)
    (hv : ∀ b, supp1 (ga1 s) b ≤ supp1 (ga1 s') b) {out : GbcaOut}
    (h : OutCert P s out) : OutCert P s' out := by
  cases out with
  | A v =>
    obtain ⟨⟨S, hS, hh⟩, S', hS', hh'⟩ := h
    exact ⟨⟨S, by rw [h2]; exact hS, hh⟩, S', by rw [h1]; exact hS', hh'⟩
  | B v =>
    obtain ⟨⟨S, hS, hh⟩, hw⟩ := h
    exact ⟨⟨S, by rw [h1]; exact hS, hh⟩, le_trans hw (hv _)⟩
  | C =>
    obtain ⟨⟨S, hS, hl⟩, hw⟩ := h
    exact ⟨⟨S, by rw [h2]; exact hS, hl⟩, fun b => le_trans (hw b) (hv b)⟩

/-- The invariant of the round over the gather specifications. The provenance
clauses are the gather commit guards, per gather; `cand_heavy` and `cand_bot`
record what the candidate the first gather's return determines certifies about
that gather, and `call2_cand` carries the candidate into the second gather's
call record; `cand_bound` and `call2_bound` say that the row writing the
candidate writes the bound bit, and `bound_core` that the bit is read off the
first gather's core; `out_cert` records what the second gather's return
certifies about the grade; the `core*` clauses re-state the freeze guards,
which the write-once cores keep true. -/
structure PairInv (P : Params) (s : RoundStateOverGatherSpecifications P.n) : Prop where
  /-- The corruption budget. -/
  F_card : (ga1 s).F.card ≤ P.f
  /-- The two corrupted sets are in lockstep. -/
  F_eq12 : (ga2 s).F = (ga1 s).F
  /-- A committed first-gather entry of an honest process is its call. -/
  val1_prov : ∀ k v, (ga1 s).val k = some v → k ∈ (ga1 s).F ∨ (ga1 s).call k = some v
  /-- A committed second-gather entry of an honest process is its call. -/
  val2_prov : ∀ k c, (ga2 s).val k = some c → k ∈ (ga1 s).F ∨ (ga2 s).call k = some c
  /-- An honest process's bit candidate is heavy in the first gather's core. -/
  cand_heavy : ∀ k ∉ (ga1 s).F, ∀ v, (procs s k).cand = some (some v) →
    ∃ S, (ga1 s).core = some S ∧ S.card - P.f ≤ APSet.cnt S v
  /-- An honest process's `⊥` candidate certifies `f + 1` committed-entry
  support for both bits. -/
  cand_bot : ∀ k ∉ (ga1 s).F, (procs s k).cand = some none →
    P.f + 1 ≤ supp1 (ga1 s) true ∧ P.f + 1 ≤ supp1 (ga1 s) false
  /-- An honest process's second call carries the candidate it holds. -/
  call2_cand : ∀ k ∉ (ga1 s).F, ∀ x, (ga2 s).call k = some x → (procs s k).cand = some x
  /-- A candidate certifies the bound bit is written: the first gather's return
  writes the candidate and the bit together. -/
  cand_bound : ∀ k, (procs s k).cand ≠ none → bound s ≠ none
  /-- A second call certifies the bound bit is written: the bit is written at
  the first gather's return, before any second call. -/
  call2_bound : ∀ k, (procs s k).called2 = true → bound s ≠ none
  /-- The bound bit is the bound bit of the first gather's frozen core. -/
  bound_core : ∀ β, bound s = some β → ∃ S, (ga1 s).core = some S ∧ β = boundOfCore P S
  /-- A recorded grade comes with the bound bit and its certificate. -/
  out_cert : ∀ k out, (procs s k).out = some out → bound s ≠ none ∧ OutCert P s out
  /-- The first gather's core is committed entries. -/
  core1_val : ∀ S, (ga1 s).core = some S → S.subMap (ga1 s).val
  /-- The first gather's core has `n − f` entries. -/
  core1_card : ∀ S, (ga1 s).core = some S → P.n - P.f ≤ S.card
  /-- The second gather's core is committed entries. -/
  core2_val : ∀ S, (ga2 s).core = some S → S.subMap (ga2 s).val
  /-- The second gather's core has `n − f` entries. -/
  core2_card : ∀ S, (ga2 s).core = some S → P.n - P.f ≤ S.card

/-- The invariant holds initially. -/
theorem PairInv.initial (P : Params) (r : ℕ) : PairInv P ((roundOverGatherSpecifications P r).init)
  := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, procs, bound, ga1, ga2, Gather.SpecState.initial,
      ProcRec.initial]

/-- The invariant is preserved by every row. -/
theorem PairInv.step {r : ℕ} {s : RoundStateOverGatherSpecifications P.n} {l : Label P.n}
    {μ : PMF (RoundStateOverGatherSpecifications P.n)} (hInv : PairInv P s) (hstep :
      StepOverGatherSpecifications P r s l μ)
    {s' : RoundStateOverGatherSpecifications P.n} (hs' : s' ∈ μ.support) : PairInv P s' := by
  cases hstep with
  | callG id b t1 h0 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain ⟨hval, hcore, hF⟩ := call_frame h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [procs_setGa1, procs_setProcs, ga1_setGa1, ga1_setProcs,
        ga2_setGa1, ga2_setProcs, bound_setGa1, bound_setProcs]
    · rw [hF]; exact hInv.F_card
    · rw [hF]; exact hInv.F_eq12
    · rw [hval, hF]
      intro k v hv
      rcases hInv.val1_prov k v hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_prov h k v hc')
    · rw [hF]; exact hInv.val2_prov
    · rw [hF, hcore]
      intro k hk v hcd
      refine hInv.cand_heavy k hk v ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · rw [hF, supp1_congr hval hF true, supp1_congr hval hF false]
      intro k hk hcd
      refine hInv.cand_bot k hk ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · rw [hF]
      intro k hk x hx
      have hcd := hInv.call2_cand k hk x hx
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self]
      · rwa [Function.update_of_ne hkid]
    · intro k hcd
      refine hInv.cand_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hcd
      refine hInv.call2_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · rw [hcore]; exact hInv.bound_core
    · intro k out hk
      have hk' : (procs s k).out = some out := by
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hk
        · rwa [Function.update_of_ne hkid] at hk
      refine ⟨(hInv.out_cert k out hk').1,
        OutCert.mono (s := s) ?_ ?_ ?_ (hInv.out_cert k out hk').2⟩
      · exact hcore
      · rfl
      · exact fun b => le_of_eq (supp1_congr hval hF b).symm
    · rw [hval, hcore]; exact hInv.core1_val
    · rw [hcore]; exact hInv.core1_card
    · exact hInv.core2_val
    · exact hInv.core2_card
  | callLoop id b t1 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain ⟨hval, hcore, hF⟩ := call_frame h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [procs_setGa1, ga1_setGa1, ga2_setGa1, bound_setGa1]
    · rw [hF]; exact hInv.F_card
    · rw [hF]; exact hInv.F_eq12
    · rw [hval, hF]
      intro k v hv
      rcases hInv.val1_prov k v hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_prov h k v hc')
    · rw [hF]; exact hInv.val2_prov
    · rw [hF, hcore]; exact hInv.cand_heavy
    · rw [hF, supp1_congr hval hF true, supp1_congr hval hF false]; exact hInv.cand_bot
    · rw [hF]; exact hInv.call2_cand
    · exact hInv.cand_bound
    · exact hInv.call2_bound
    · rw [hcore]; exact hInv.bound_core
    · intro k out hk
      refine ⟨(hInv.out_cert k out hk).1,
        OutCert.mono (s := s) ?_ ?_ ?_ (hInv.out_cert k out hk).2⟩
      · exact hcore
      · rfl
      · exact fun b => le_of_eq (supp1_congr hval hF b).symm
    · rw [hval, hcore]; exact hInv.core1_val
    · rw [hcore]; exact hInv.core1_card
    · exact hInv.core2_val
    · exact hInv.core2_card
  | ga1Tau t1 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      have hvmono : ∀ k' v', (ga1 s).val k' = some v' →
          Function.update (ga1 s).val k (some v) k' = some v' := by
        intro k' v' hv'
        by_cases hk : k' = k
        · subst hk
          rw [hv] at hv'
          exact absurd hv' (by simp)
        · rw [Function.update_of_ne hk]
          exact hv'
      refine ⟨hInv.F_card, hInv.F_eq12, ?_, hInv.val2_prov, hInv.cand_heavy, ?_,
        hInv.call2_cand, hInv.cand_bound, hInv.call2_bound, hInv.bound_core, ?_,
        ?_, hInv.core1_card, hInv.core2_val, hInv.core2_card⟩
      · intro k' v' hv'
        dsimp only [ga1_setGa1] at hv' ⊢
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
        constructor <;> exact le_trans (by assumption) (supp1_mono hvmono (by rfl) _)
      · intro k' out hk'
        refine ⟨(hInv.out_cert k' out hk').1,
          OutCert.mono (s := s) ?_ ?_ ?_ (hInv.out_cert k' out hk').2⟩
        · rfl
        · rfl
        · exact fun b => supp1_mono hvmono (by rfl) b
      · intro S hS
        have hpre := hInv.core1_val S hS
        intro p hp
        exact hvmono p.1 p.2 (hpre p hp)
    | bindCore S h0 hval hcard =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov, ?_,
        hInv.cand_bot, hInv.call2_cand, hInv.cand_bound, hInv.call2_bound, ?_, ?_,
        ?_, ?_, hInv.core2_val, hInv.core2_card⟩
      · intro k hk v hc
        obtain ⟨S', hS', -⟩ := hInv.cand_heavy k hk v hc
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro β hβ
        obtain ⟨S', hS', -⟩ := hInv.bound_core β hβ
        rw [h0] at hS'
        exact absurd hS' (by simp)
      · intro k out hk
        refine ⟨(hInv.out_cert k out hk).1, ?_⟩
        have hc := (hInv.out_cert k out hk).2
        cases out with
        | A v =>
          obtain ⟨-, S', hS', -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
        | B v =>
          obtain ⟨⟨S', hS', -⟩, -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
        | C => exact hc
      · intro S' hS'
        dsimp only [ga1_setGa1] at hS'
        obtain rfl : S = S' := by injection hS'
        exact hval
      · intro S' hS'
        dsimp only [ga1_setGa1] at hS'
        obtain rfl : S = S' := by injection hS'
        exact hcard
  | ga2Tau t2 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, ?_, hInv.cand_heavy,
        hInv.cand_bot, hInv.call2_cand, hInv.cand_bound, hInv.call2_bound,
        hInv.bound_core, hInv.out_cert, hInv.core1_val, hInv.core1_card, ?_,
        hInv.core2_card⟩
      · intro k' c' hc'
        dsimp only [ga1_setGa2, ga2_setGa2] at hc' ⊢
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
        dsimp only [ga2_setGa2]
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
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov,
        hInv.cand_heavy, hInv.cand_bot, hInv.call2_cand, hInv.cand_bound,
        hInv.call2_bound, hInv.bound_core, ?_, hInv.core1_val, hInv.core1_card,
        ?_, ?_⟩
      · intro k out hk
        refine ⟨(hInv.out_cert k out hk).1, ?_⟩
        have hc := (hInv.out_cert k out hk).2
        cases out with
        | A v =>
          obtain ⟨⟨S', hS', -⟩, -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
        | B v => exact hc
        | C =>
          obtain ⟨⟨S', hS', -⟩, -⟩ := hc
          rw [h0] at hS'
          exact absurd hS' (by simp)
      · intro S' hS'
        dsimp only [ga2_setGa2] at hS'
        obtain rfl : S = S' := by injection hS'
        exact hval
      · intro S' hS'
        dsimp only [ga2_setGa2] at hS'
        obtain rfl : S = S' := by injection hS'
        exact hcard
  | ret1 id g C t1 hin hc h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      have hCcard : P.n - P.f ≤ C.card := hInv.core1_card C hC
      have hgdom : P.n - P.f ≤ gdom g := le_trans hCcard (APSet.card_le_gdom hmem)
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, hInv.core1_val, hInv.core1_card, hInv.core2_val,
        hInv.core2_card⟩
      · intro k hk v hcd
        dsimp only [procs_setBound, procs_setGa1, procs_setProcs] at hcd
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hcd
          have hcand : cand P g = some v := by injection hcd
          exact ⟨C, hC, cnt_heavy_of_subMap hmem (cand_some hcand)⟩
        · rw [Function.update_of_ne hkid] at hcd
          exact hInv.cand_heavy k hk v hcd
      · intro k hk hcd
        dsimp only [procs_setBound, procs_setGa1, procs_setProcs] at hcd
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hcd
          have hcand : cand P g = none := by injection hcd
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
        · rw [Function.update_of_ne hkid] at hcd
          exact hInv.cand_bot k hk hcd
      · intro k hk x hx
        dsimp only [procs_setBound, procs_setGa1, procs_setProcs]
        by_cases hkid : k = id
        · subst hkid
          exact absurd (hInv.call2_cand k hk x hx) (by rw [hc]; simp)
        · rw [Function.update_of_ne hkid]
          exact hInv.call2_cand k hk x hx
      · intro k _
        dsimp only [bound_setBound]
        exact Option.some_ne_none _
      · intro k _
        dsimp only [bound_setBound]
        exact Option.some_ne_none _
      · intro β hβ
        dsimp only [bound_setBound] at hβ
        obtain rfl : (bound s).getD (boundOfCore P C) = β := by injection hβ
        rcases hb : bound s with _ | β₀
        · exact ⟨C, hC, rfl⟩
        · exact hInv.bound_core β₀ hb
      · intro k out hk
        dsimp only [procs_setBound, procs_setGa1, procs_setProcs] at hk
        refine ⟨by dsimp only [bound_setBound]; exact Option.some_ne_none _,
          OutCert.mono rfl rfl (fun _ => le_refl _) (hInv.out_cert k out ?_).2⟩
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hk
        · rwa [Function.update_of_ne hkid] at hk
  | call2 id x t2 hc h2 h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    obtain ⟨hval2, hcore2, hF2⟩ := call_frame h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [procs_setGa2, procs_setProcs, ga1_setGa2, ga1_setProcs,
        ga2_setGa2, ga2_setProcs, bound_setGa2, bound_setProcs]
    · exact hInv.F_card
    · rw [hF2]; exact hInv.F_eq12
    · exact hInv.val1_prov
    · rw [hval2]
      intro k c hv
      rcases hInv.val2_prov k c hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_prov h k c hc')
    · intro k hk v hcd
      refine hInv.cand_heavy k hk v ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk hcd
      refine hInv.cand_bot k hk ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk y hy
      rcases call_val h k y hy with hold | ⟨rfl, rfl⟩
      · have hcd := hInv.call2_cand k hk y hold
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self]
        · rwa [Function.update_of_ne hkid]
      · rw [Function.update_self]
        exact hc
    · intro k hcd
      refine hInv.cand_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hcd
      by_cases hkid : k = id
      · subst hkid
        exact hInv.cand_bound k (by rw [hc]; simp)
      · rw [Function.update_of_ne hkid] at hcd
        exact hInv.call2_bound k hcd
    · exact hInv.bound_core
    · intro k out hk
      have hk' : (procs s k).out = some out := by
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hk
        · rwa [Function.update_of_ne hkid] at hk
      refine ⟨(hInv.out_cert k out hk').1,
        OutCert.mono (s := s) ?_ ?_ ?_ (hInv.out_cert k out hk').2⟩
      · rfl
      · exact hcore2
      · exact fun _ => le_refl _
    · exact hInv.core1_val
    · exact hInv.core1_card
    · rw [hcore2, hval2]; exact hInv.core2_val
    · rw [hcore2]; exact hInv.core2_card
  | retG id out ho hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov, ?_, ?_, ?_,
      ?_, ?_, hInv.bound_core, ?_, hInv.core1_val, hInv.core1_card,
      hInv.core2_val, hInv.core2_card⟩ <;> dsimp only [procs_setProcs]
    · intro k hk v hcd
      refine hInv.cand_heavy k hk v ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk hcd
      refine hInv.cand_bot k hk ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hk y hy
      have hcd := hInv.call2_cand k hk y hy
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self]
      · rwa [Function.update_of_ne hkid]
    · intro k hcd
      refine hInv.cand_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k hcd
      refine hInv.call2_bound k ?_
      by_cases hkid : k = id
      · subst hkid; rwa [Function.update_self] at hcd
      · rwa [Function.update_of_ne hkid] at hcd
    · intro k out' hk
      have hk' : (procs s k).out = some out' := by
        by_cases hkid : k = id
        · subst hkid; rw [Function.update_self] at hk; exact absurd hk (by simp)
        · rwa [Function.update_of_ne hkid] at hk
      exact hInv.out_cert k out' hk'
  | ret2 id g C t2 h2 ho h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      have hf := P.hf
      have hbnd : bound s ≠ none := hInv.call2_bound id h2
      have hCcard : P.n - P.f ≤ C.card := hInv.core2_card C hC
      have hgdom : P.n - P.f ≤ gdom g := le_trans hCcard (APSet.card_le_gdom hmem)
      have hchain : ∀ k, k ∉ (ga1 s).F → ∀ c, g k = some c → (procs s k).cand = some c := by
        intro k hkF c hgc
        rcases hInv.val2_prov k c (hsubv k c hgc) with hF | hin
        · exact absurd hF hkF
        · exact hInv.call2_cand k hkF c hin
      have hheavy1 : ∀ v : Bool, P.f + 1 ≤ gcount g (some v) →
          ∃ S, (ga1 s).core = some S ∧ S.card - P.f ≤ APSet.cnt S v := by
        intro v hcnt
        obtain ⟨kh, hkhg, hkhF⟩ := exists_honest_filter hInv.F_card
          (p := fun k => g k = some (some v)) hcnt
        exact hInv.cand_heavy kh hkhF v (hchain kh hkhF (some v) hkhg)
      have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
          (fun k => g k ≠ none ∧ g k ≠ some (some (!b)))).card →
          P.f + 1 ≤ supp1 (ga1 s) b := by
        intro b hcard
        obtain ⟨kt, hkt, hktF⟩ := exists_honest_filter hInv.F_card hcard
        rcases hgkt : g kt with _ | ct
        · exact absurd hgkt hkt.1
        have hcand := hchain kt hktF ct hgkt
        rcases ct with _ | wt
        · obtain ⟨hsT, hsF⟩ := hInv.cand_bot kt hktF hcand
          cases b
          · exact hsF
          · exact hsT
        · have hwt : wt = b := by
            by_contra hne
            have hb : wt = !b := by cases wt <;> cases b <;> simp_all
            subst hb
            exact hkt.2 hgkt
          subst hwt
          obtain ⟨S, hS, hh⟩ := hInv.cand_heavy kt hktF wt hcand
          have hScard := hInv.core1_card S hS
          exact le_trans (by omega : P.f + 1 ≤ APSet.cnt S wt)
            (cnt_le_supp1 (hInv.core1_val S hS) wt)
      have hcert : OutCert P s (gradeOf P g) := by
        cases hout : gradeOf P g with
        | A v =>
          refine ⟨⟨C, hC, cnt_heavy_of_subMap hmem (gradeOf_A hout)⟩, hheavy1 v ?_⟩
          have := gradeOf_A hout
          omega
        | B v =>
          obtain ⟨hBcnt, hBnotA⟩ := gradeOf_B hout
          refine ⟨hheavy1 v hBcnt, hsupp (!v) ?_⟩
          simp only [Bool.not_not]
          rw [card_ne_gcount]
          have := hBnotA v
          omega
        | C =>
          have hCgrade := gradeOf_C hout
          refine ⟨⟨C, hC, fun w => le_trans (APSet.cnt_le_gcount hmem (some w)) (hCgrade w)⟩,
            fun b => hsupp b ?_⟩
          rw [card_ne_gcount]
          have := hCgrade (!b)
          omega
      refine ⟨hInv.F_card, hInv.F_eq12, hInv.val1_prov, hInv.val2_prov, ?_, ?_, ?_,
        ?_, ?_, hInv.bound_core, ?_, hInv.core1_val, hInv.core1_card,
        hInv.core2_val, hInv.core2_card⟩
      · intro k hk v hcd
        refine hInv.cand_heavy k hk v ?_
        dsimp only [procs_setGa2, procs_setProcs] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k hk hcd
        refine hInv.cand_bot k hk ?_
        dsimp only [procs_setGa2, procs_setProcs] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k hk x hx
        have hcd := hInv.call2_cand k hk x hx
        dsimp only [procs_setGa2, procs_setProcs]
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self]
        · rwa [Function.update_of_ne hkid]
      · intro k hcd
        refine hInv.cand_bound k ?_
        dsimp only [procs_setGa2, procs_setProcs] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k hcd
        refine hInv.call2_bound k ?_
        dsimp only [procs_setGa2, procs_setProcs] at hcd
        by_cases hkid : k = id
        · subst hkid; rwa [Function.update_self] at hcd
        · rwa [Function.update_of_ne hkid] at hcd
      · intro k out hk
        dsimp only [procs_setGa2, procs_setProcs] at hk
        by_cases hkid : k = id
        · subst hkid
          rw [Function.update_self] at hk
          obtain rfl : gradeOf P g = out := by injection hk
          exact ⟨hbnd, OutCert.mono rfl rfl (fun _ => le_refl _) hcert⟩
        · rw [Function.update_of_ne hkid] at hk
          obtain ⟨hb, hc⟩ := hInv.out_cert k out hk
          exact ⟨hb, OutCert.mono rfl rfl (fun _ => le_refl _) hc⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hFsub : (ga1 s).F ⊆ ((ga1 s).corrupt P id).F := by
      rw [Gather.SpecState.corrupt_F]
      split
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _
    have hF' : ∀ k, k ∉ ((ga1 s).corrupt P id).F → k ∉ (ga1 s).F :=
      fun k hk hkF => hk (hFsub hkF)
    have hsmono : ∀ b, supp1 (ga1 s) b ≤ supp1 ((ga1 s).corrupt P id) b := fun b =>
      supp1_mono (fun k' v' hv' => by rw [Gather.corrupt_val]; exact hv') hFsub b
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [procs_corruptAll, bound_corruptAll, ga1_corruptAll, ga2_corruptAll]
    · rw [Gather.SpecState.corrupt_F]
      split
      · next hcs =>
        have hins := Finset.card_insert_le id (ga1 s).F
        have hlt := hcs.2
        omega
      · exact hInv.F_card
    · rw [Gather.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hInv.F_eq12]
    · intro k v hv
      rw [Gather.corrupt_val] at hv
      rw [Gather.corrupt_call]
      rcases hInv.val1_prov k v hv with hF | hcl
      · exact Or.inl (hFsub hF)
      · exact Or.inr hcl
    · intro k c hcv
      rw [Gather.corrupt_val] at hcv
      rw [Gather.corrupt_call]
      rcases hInv.val2_prov k c hcv with hF | hin
      · exact Or.inl (hFsub hF)
      · exact Or.inr hin
    · intro k hk v hcd
      obtain ⟨S, hS, hh⟩ := hInv.cand_heavy k (hF' k hk) v hcd
      exact ⟨S, by rw [Gather.corrupt_core]; exact hS, hh⟩
    · intro k hk hcd
      obtain ⟨h1, h2⟩ := hInv.cand_bot k (hF' k hk) hcd
      exact ⟨le_trans h1 (hsmono true), le_trans h2 (hsmono false)⟩
    · intro k hk x hx
      rw [Gather.corrupt_call] at hx
      exact hInv.call2_cand k (hF' k hk) x hx
    · exact hInv.cand_bound
    · exact hInv.call2_bound
    · intro β hβ
      obtain ⟨S, hS, hh⟩ := hInv.bound_core β hβ
      exact ⟨S, by rw [Gather.corrupt_core]; exact hS, hh⟩
    · intro k out hk
      refine ⟨(hInv.out_cert k out hk).1,
        OutCert.mono (s := s) ?_ ?_ ?_ (hInv.out_cert k out hk).2⟩
      · rw [ga1_corruptAll, Gather.corrupt_core]
      · rw [ga2_corruptAll, Gather.corrupt_core]
      · exact fun b => by rw [ga1_corruptAll]; exact hsmono b
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

/-! ### The relation -/

/-- The exclusion certificate: the first gather's core counts `b` below
`|S| − f`, so no later candidate is `b`. Frozen — the core is write-once. -/
def ExcludedEv (P : Params) (s : RoundStateOverGatherSpecifications P.n) (b : Bool) : Prop :=
  ∃ S, (ga1 s).core = some S ∧ APSet.cnt S b < S.card - P.f

/-- The refinement relation of the round over the gather specifications. -/
structure PairRel (P : Params) (s : RoundStateOverGatherSpecifications P.n) (t : GBCA.SpecState P.n)
  : Prop where
  /-- The invariant. -/
  inv : PairInv P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = (ga1 s).call k
  /-- The return flags agree: the specification returns at the graded return,
  which the program marks. -/
  ret_eq : ∀ id, t.ret id = (procs s id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = (ga1 s).F
  /-- An excluded bit is certified excluded. -/
  excluded_cert : ∀ b ∈ t.excluded, ExcludedEv P s b
  /-- An excluded bit is the complement of the round's bound bit: the
  exclusion is written inside the first return's run, which announces that
  bit. -/
  excluded_bound : ∀ b ∈ t.excluded, ∃ β, bound s = some β ∧ b = !β
  /-- The `A` grade guard is certified by a value heavy in the second gather's
  core. -/
  gradeA_ev : t.grade = some true → ∃ S v, (ga2 s).core = some S ∧
    S.card - P.f ≤ APSet.cnt S (some v)
  /-- The `C` grade guard is certified by the second gather's core being light
  at both bits. -/
  gradeC_ev : t.grade = some false → ∃ S, (ga2 s).core = some S ∧
    ∀ v, APSet.cnt S (some v) ≤ P.f

/-- The relation holds initially. -/
theorem pairRel_init (P : Params) (r : ℕ) :
    PairRel P ((roundOverGatherSpecifications P r).init)
      ((GBCA.ByABDY.specificationOverRoundAlphabet P r).init) := by
  refine ⟨PairInv.initial P r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, procs, bound, ga1, ga2, Gather.SpecState.initial,
      GBCA.SpecState.initial, ProcRec.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem pairRel_corrupt {r : ℕ} {s : RoundStateOverGatherSpecifications P.n} {t : GBCA.SpecState
  P.n}
    (hR : PairRel P s t) (id : Fin P.n) :
    PairRel P (corruptAll P id (Gather.SpecState.corrupt P) (Gather.SpecState.corrupt P) s)
      (t.corrupt P id) := by
  refine ⟨hR.inv.step (r := r) (StepOverGatherSpecifications.fail s id) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp only [ga1_corruptAll]
    rw [GBCA.corrupt_call, Gather.corrupt_call]
    exact hR.call_eq k
  · intro k
    rw [GBCA.corrupt_ret]
    exact hR.ret_eq k
  · dsimp only [ga1_corruptAll]
    rw [GBCA.SpecState.corrupt_F, Gather.SpecState.corrupt_F, hR.F_eq]
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    obtain ⟨S, hS, hl⟩ := hR.excluded_cert b hb
    exact ⟨S, by rw [ga1_corruptAll, Gather.corrupt_core]; exact hS, hl⟩
  · intro b hb
    rw [GBCA.corrupt_excluded] at hb
    exact hR.excluded_bound b hb
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, v, hS, hh⟩ := hR.gradeA_ev hg
    exact ⟨S, v, by rw [ga2_corruptAll, Gather.corrupt_core]; exact hS, hh⟩
  · intro hg
    rw [GBCA.corrupt_grade] at hg
    obtain ⟨S, hS, hl⟩ := hR.gradeC_ev hg
    exact ⟨S, by rw [ga2_corruptAll, Gather.corrupt_core]; exact hS, hl⟩

/-! ### The row-wise leg -/

/-- **The row-wise leg**: every row of the round is answered by a weak run of
the graded agreement specification, the relation restored. -/
theorem pairRel_row (P : Params) (r : ℕ) (q₁ : RoundStateOverGatherSpecifications P.n)
    (q₂ : GBCA.SpecState P.n) (hR : PairRel P q₁ q₂) (l₀ : Label P.n)
    (μ : PMF (RoundStateOverGatherSpecifications P.n)) (hrow : StepOverGatherSpecifications P r q₁
      l₀ μ)
    (q₁' : RoundStateOverGatherSpecifications P.n) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLSilent q₂ q₂') ∨
      (¬ l₀ = Silent.τ ∧ (GBCA.specInst P r).weakLStep q₂ l₀ q₂')) ∧
      PairRel P q₁' q₂' := by
  have hInv' := hR.inv.step hrow hq₁'
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
        hInv', ?_, ?_, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
      · intro k
        dsimp only [ga1_setGa1]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hk, Function.update_of_ne hk]
          exact hR.call_eq k
      · intro k
        dsimp only [procs_setGa1, procs_setProcs]
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
        hR.excluded_cert, hR.excluded_bound, hR.gradeA_ev, hR.gradeC_ev⟩
      intro k
      dsimp only [procs_setGa1, procs_setProcs]
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
        hInv', ?_, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
      intro k
      dsimp only [ga1_setGa1]
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
  | ga1Tau t1 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | commit k v hv hm =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
    | bindCore S h0 hval hcard =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
      intro b hb
      obtain ⟨S', hS', -⟩ := hR.excluded_cert b hb
      rw [h0] at hS'
      exact absurd hS' (by simp)
  | ga2Tau t2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | commit k c hv hm =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, hR.ret_eq, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
    | bindCore S h0 hval hcard =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
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
  | ret1 id g C t1 hin hc h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1 : PMF (Gather.SpecState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht1 := PMF.pure_injective hμ
      subst ht1
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.excluded_cert, ?_, hR.gradeA_ev,
        hR.gradeC_ev⟩
      · intro k
        dsimp only [procs_setBound, procs_setGa1, procs_setProcs]
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self]
          exact hR.ret_eq k
        · rw [Function.update_of_ne hk]
          exact hR.ret_eq k
      · intro b hb
        obtain ⟨β, hβ, hbβ⟩ := hR.excluded_bound b hb
        exact ⟨β, by dsimp only [bound_setBound]; rw [hβ]; rfl, hbβ⟩
  | call2 id x t2 hc h2 h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨hval2, hcore2, hF2⟩ := call_frame h
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
      hR.call_eq, ?_, hR.F_eq, hR.excluded_cert, hR.excluded_bound, ?_, ?_⟩
    · intro k
      dsimp only [procs_setGa2, procs_setProcs]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
    · intro hg
      obtain ⟨S, v, hS, hh⟩ := hR.gradeA_ev hg
      exact ⟨S, v, by dsimp only [ga2_setGa2, ga2_setProcs]; rw [hcore2]; exact hS, hh⟩
    · intro hg
      obtain ⟨S, hS, hl⟩ := hR.gradeC_ev hg
      exact ⟨S, by dsimp only [ga2_setGa2, ga2_setProcs]; rw [hcore2]; exact hS, hl⟩
  | ret2 id g C t2 h2 ho h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2 : PMF (Gather.SpecState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' C' hC hmem hsubv hr =>
      have ht2 := PMF.pure_injective hμ
      subst ht2
      refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hInv',
        hR.call_eq, ?_, hR.F_eq, hR.excluded_cert, hR.excluded_bound,
        hR.gradeA_ev, hR.gradeC_ev⟩
      intro k
      dsimp only [procs_setGa2, procs_setProcs]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.ret_eq k
      · rw [Function.update_of_ne hk]
        exact hR.ret_eq k
  | retG id out ho hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hf := P.hf
    obtain ⟨hbnd, hcert⟩ := hR.inv.out_cert id out ho
    have hretflag : q₂.ret id = false := by
      rw [hR.ret_eq id]
      exact hr
    obtain ⟨β, hβ⟩ : ∃ β, bound q₁ = some β := Option.ne_none_iff_exists'.mp hbnd
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
    have hret_eq : ∀ k, Function.update q₂.ret id true k =
        (procs (setProcs q₁ (Function.update (procs q₁) id
          { procs q₁ id with out := none, returned := true })) k).returned := by
      intro k
      dsimp only [procs_setProcs]
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.ret_eq k
    have hbndeq : (bound q₁).getD (boundOfCore P (∅ : APSet P.n Bool)) = β := by
      rw [hβ]
      rfl
    rw [hbndeq]
    cases out with
    | A v =>
      obtain ⟨⟨C₂, hC₂, hA_ev⟩, S', hS', hheavy⟩ := hcert
      obtain rfl : S = S' := by rw [hS] at hS'; exact Option.some.inj hS'
      have hC₂card : P.n - P.f ≤ C₂.card := hR.inv.core2_card C₂ hC₂
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
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hlight₂ v
            omega
          · exact Or.inr rfl
      by_cases hbv : (!v) ∈ q₂.excluded
      · refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retA q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
            hgA hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.excluded_cert,
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
    | B v =>
      obtain ⟨⟨S', hS', hheavy⟩, hw1⟩ := hcert
      obtain rfl : S = S' := by rw [hS] at hS'; exact Option.some.inj hS'
      have hβv : β = v := by
        rw [hβS]
        exact boundOfCore_of_heavy hScard hheavy
      have hlive : v ∉ q₂.excluded := by
        intro hv
        have hb := hexcl v hv
        rw [hβv] at hb
        simp at hb
      have hw : P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some (!v) ∨ id' ∈ q₂.F)).card :=
        spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov hw1
      by_cases hbv : (!v) ∈ q₂.excluded
      · exact ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (GBCA.Step.retB q₂ id v β hlive hbv (by rw [hβv]; exact hbv)
            hw hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.excluded_cert,
          hR.excluded_bound, hR.gradeA_ev, hR.gradeC_ev⟩
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
          hInv', hR.call_eq, hret_eq, hR.F_eq, ?_, ?_, hR.gradeA_ev,
          hR.gradeC_ev⟩
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
    | C =>
      obtain ⟨⟨C₂, hC₂, hClight⟩, hsupp1⟩ := hcert
      have hC₂card : P.n - P.f ≤ C₂.card := hR.inv.core2_card C₂ hC₂
      have hsupp : ∀ b : Bool, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => q₂.call id' = some b ∨ id' ∈ q₂.F)).card := fun b =>
        spec_supp_of_supp1 hR.call_eq hR.F_eq hR.inv.val1_prov (hsupp1 b)
      have hgC : q₂.grade = none ∨ q₂.grade = some false := by
        rcases hgr : q₂.grade with _ | b
        · exact Or.inl rfl
        · cases b
          · exact Or.inr rfl
          · exfalso
            obtain ⟨S₂, v', hS₂, hh⟩ := hR.gradeA_ev hgr
            rw [hC₂] at hS₂
            obtain rfl : C₂ = S₂ := Option.some.inj hS₂
            have hlv := hClight v'
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
          (GBCA.Step.retC q₂ id β hb (hsupp true) (hsupp false) hgC hretflag)⟩,
          hInv', hR.call_eq, hret_eq, hR.F_eq, hR.excluded_cert,
          hR.excluded_bound, ?_, ?_⟩
        · intro hgr
          exact absurd hgr (by simp)
        · intro _
          exact ⟨C₂, hC₂, hClight⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (GBCA.Step.fail q₂ id)⟩, pairRel_corrupt (r := r) hR id⟩

/-! ### The refinement -/

/-- **The refinement of the round over the gather specifications**: the round
forward-simulates the graded agreement specification read over the round's
interface. A transition of the round is one row of `GBCA.ByAFW.StepOverGatherSpecifications`
(`GBCA.ByAFW.roundOverGatherSpecifications_step_row`), the row is answered by a weak run of the
specification (`pairRel_row`), and that run is lifted to the interface along a
section of `GBCA.ByABDY.gbcaLabelMap`. -/
theorem pairRefines (P : Params) (r : ℕ) :
    ForwardSimulation (roundOverGatherSpecifications P r)
      (GBCA.ByABDY.specificationOverRoundAlphabet P r) (PairRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := roundOverGatherSpecifications_step_row P r q₁ l μ hstep
  obtain ⟨t', hdis, hrel⟩ := pairRel_row P r q₁ q₂ hR l₀ μ hrow q₁' hq₁'
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

/-- info: 'PLTS.ABA.GBCA.ByAFW.pairRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairRefines

/-- info: 'PLTS.ABA.GBCA.ByAFW.pairRel_corrupt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairRel_corrupt

end GBCA.ByAFW
end ABA
end PLTS
