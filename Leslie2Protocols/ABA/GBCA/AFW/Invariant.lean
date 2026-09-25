/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.OutputWitness

/-!
# The inductive invariant of the round over the gather specifications

`GBCA.ByAFW.Invariant P s` is the inductive invariant of the round over the gather specifications
(`GBCA.ByAFW.roundOverGatherSpecifications`, `ABA/GBCA/AFW/Composition.lean`). `Invariant.initial`
holds it at the initial state, and `Invariant.step` carries it along every transition of
`GBCA.ByAFW.AlgorithmOverGatherSpecifications`.

The invariant carries

* the corruption budget (`F_card`) and the agreement of the two corrupted sets
  (`secondGatherF_eq_firstGatherF`);
* a committed entry of a correct process is that process's call, per gather
  (`firstGatherVal_of_call`, `secondGatherVal_of_call`);
* what a correct process's candidate witnesses about the first gather's core
  (`candidate_aboveThreshold`, `candidate_bot`), and its transfer to the second gather's call
  (`secondGatherCall_candidate`);
* the round's bound bit (D29): a candidate or a second call witnesses that the bit is written
  (`candidate_bound`, `secondGatherCall_bound`), and the bit is `GBCA.boundOfCore` of the first
  gather's recorded core (`bound_core`);
* what a recorded grade witnesses (`out_witness`, through `OutputWitness`);
* the core-write guards, which the write-once cores keep true (`firstGatherCore_val`,
  `firstGatherCore_card`, `secondGatherCore_val`, `secondGatherCore_card`).

## What the program's variables carry

The first gather's return, the second gather's call, its return and the round's graded return are
four separate moves, and what carries the round from one to the next is the program's variables. The
invariant therefore states the first gather's witnesses on the program's candidate:
`candidate_aboveThreshold` and `candidate_bot` are established at `firstGatherReturn`, where the
first gather's return guards are in scope, and `secondGatherCall_candidate` transfers the candidate
to the second gather's call at `secondGatherCall`. The graded outcome is recorded at
`secondGatherReturn`, and `out_witness` is what the second gather's return guards witness about
it. Both cores are write-once, so a witness survives every later transition.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Gather

variable {P : Parameters}

/-! ### The invariant -/

/-- The invariant of the round over the gather specifications. The clauses naming a committed entry
are the gather commit guards, per gather; `candidate_aboveThreshold` and `candidate_bot`
record what the candidate the first gather's return determines witnesses about
that gather, and `secondGatherCall_candidate` carries the candidate into the second gather's
call; `candidate_bound` and `secondGatherCall_bound` say that the transition writing the
candidate writes the bound bit, and `bound_core` that the bit is read off the
first gather's core; `out_witness` records what the second gather's return
witnesses about the grade; the `core*` clauses re-state the core-write guards,
which the write-once cores keep true. -/
structure Invariant (P : Parameters) (s : RoundStateOverGatherSpecifications P.n) : Prop where
  /-- The corruption budget. -/
  F_card : (firstGather s).F.card ≤ P.f
  /-- The two corrupted sets are equal. -/
  secondGatherF_eq_firstGatherF : (secondGather s).F = (firstGather s).F
  /-- A committed first-gather entry of a correct process is its call. -/
  firstGatherVal_of_call : ∀ k v,
    (firstGather s).val k = some v → k ∈ (firstGather s).F ∨ (firstGather s).call k = some v
  /-- A committed second-gather entry of a correct process is its call. -/
  secondGatherVal_of_call : ∀ k c,
    (secondGather s).val k = some c → k ∈ (firstGather s).F ∨ (secondGather s).call k = some c
  /-- A correct process's bit candidate is on at least `|S| − f` entries of the
  first gather's core. -/
  candidate_aboveThreshold : ∀ k ∉ (firstGather s).F, ∀ v,
    (programs s k).candidate = some (some v) → ∃ S,
      (firstGather s).core = some S ∧ S.card - P.f ≤ AcceptedPairs.count S v
  /-- A correct process's `⊥` candidate witnesses `f + 1` committed-entry
  support for both bits. -/
  candidate_bot : ∀ k ∉ (firstGather s).F, (programs s k).candidate = some none →
    P.f + 1 ≤ firstGatherSupport (firstGather s) true ∧ P.f + 1 ≤ firstGatherSupport (firstGather s)
      false
  /-- A correct process's second call carries the candidate it holds. -/
  secondGatherCall_candidate : ∀ k ∉ (firstGather s).F, ∀ x,
    (secondGather s).call k = some x → (programs s k).candidate = some x
  /-- A candidate witnesses that the bound bit is written: the first gather's return
  writes the candidate and the bit together. -/
  candidate_bound : ∀ k, (programs s k).candidate ≠ none → bound s ≠ none
  /-- A second call witnesses that the bound bit is written: the bit is written at
  the first gather's return, before any second call. -/
  secondGatherCall_bound : ∀ k, (programs s k).secondGatherCalled = true → bound s ≠ none
  /-- The bound bit is the bound bit of the first gather's recorded core. -/
  bound_core : ∀ β, bound s = some β → ∃ S, (firstGather s).core = some S ∧ β = boundOfCore P S
  /-- A recorded grade comes with the bound bit and its witness. -/
  out_witness : ∀ k out,
    (programs s k).output = some out → bound s ≠ none ∧ OutputWitness P s out
  /-- The first gather's core is committed entries. -/
  firstGatherCore_val : ∀ S, (firstGather s).core = some S → S.subMap (firstGather s).val
  /-- The first gather's core has `n − f` entries. -/
  firstGatherCore_card : ∀ S, (firstGather s).core = some S → P.n - P.f ≤ S.card
  /-- The second gather's core is committed entries. -/
  secondGatherCore_val : ∀ S, (secondGather s).core = some S → S.subMap (secondGather s).val
  /-- The second gather's core has `n − f` entries. -/
  secondGatherCore_card : ∀ S, (secondGather s).core = some S → P.n - P.f ≤ S.card

/-- The invariant holds initially. -/
theorem Invariant.initial (P : Parameters) (r : ℕ) :
    Invariant P ((roundOverGatherSpecifications P r).init) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [roundOverGatherSpecifications_init, programs, bound, firstGather, secondGather,
      Gather.SpecState.initial, ProcessVariables.initial]

/-- The invariant is preserved by every transition. -/
theorem Invariant.step {r : ℕ} {s : RoundStateOverGatherSpecifications P.n} {l : Label P.n}
    {μ : PMF (RoundStateOverGatherSpecifications P.n)} (hInv : Invariant P s)
    (hstep : AlgorithmOverGatherSpecifications P r s l μ)
    {s' : RoundStateOverGatherSpecifications P.n}
    (hs' : s' ∈ μ.support) : Invariant P s' := by
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
    · rw [hF]; exact hInv.secondGatherF_eq_firstGatherF
    · rw [hval, hF]
      intro k v hv
      rcases hInv.firstGatherVal_of_call k v hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_mono h k v hc')
    · rw [hF]; exact hInv.secondGatherVal_of_call
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
      refine ⟨(hInv.out_witness k out hk').1,
        OutputWitness.mono (s := s) ?_ ?_ ?_ (hInv.out_witness k out hk').2⟩
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
    · rw [hF]; exact hInv.secondGatherF_eq_firstGatherF
    · rw [hval, hF]
      intro k v hv
      rcases hInv.firstGatherVal_of_call k v hv with hf' | hc'
      · exact Or.inl hf'
      · exact Or.inr (call_mono h k v hc')
    · rw [hF]; exact hInv.secondGatherVal_of_call
    · rw [hF, hcore]; exact hInv.candidate_aboveThreshold
    · rw [hF, firstGatherSupport_congr hval hF true,
        firstGatherSupport_congr hval hF false]; exact hInv.candidate_bot
    · rw [hF]; exact hInv.secondGatherCall_candidate
    · exact hInv.candidate_bound
    · exact hInv.secondGatherCall_bound
    · rw [hcore]; exact hInv.bound_core
    · intro k out hk
      refine ⟨(hInv.out_witness k out hk).1,
        OutputWitness.mono (s := s) ?_ ?_ ?_ (hInv.out_witness k out hk).2⟩
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
      refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, ?_, hInv.secondGatherVal_of_call,
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
          exact hInv.firstGatherVal_of_call k' v' hv'
      · intro k' hk' hc
        obtain ⟨h1, h2⟩ := hInv.candidate_bot k' hk' hc
        constructor <;> exact le_trans (by assumption) (firstGatherSupport_mono hvmono (by rfl) _)
      · intro k' out hk'
        refine ⟨(hInv.out_witness k' out hk').1,
          OutputWitness.mono (s := s) ?_ ?_ ?_ (hInv.out_witness k' out hk').2⟩
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
      refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, hInv.firstGatherVal_of_call,
        hInv.secondGatherVal_of_call, ?_, hInv.candidate_bot, hInv.secondGatherCall_candidate,
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
        refine ⟨(hInv.out_witness k out hk).1, ?_⟩
        have hc := (hInv.out_witness k out hk).2
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
      refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, hInv.firstGatherVal_of_call, ?_,
        hInv.candidate_aboveThreshold, hInv.candidate_bot, hInv.secondGatherCall_candidate,
          hInv.candidate_bound, hInv.secondGatherCall_bound,
        hInv.bound_core, hInv.out_witness, hInv.firstGatherCore_val, hInv.firstGatherCore_card,
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
          · exact Or.inl (by rw [← hInv.secondGatherF_eq_firstGatherF]; exact hF)
          · exact Or.inr hin
        · rw [Function.update_of_ne hk] at hc'
          exact hInv.secondGatherVal_of_call k' c' hc'
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
      refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, hInv.firstGatherVal_of_call,
        hInv.secondGatherVal_of_call, hInv.candidate_aboveThreshold, hInv.candidate_bot,
          hInv.secondGatherCall_candidate, hInv.candidate_bound,
        hInv.secondGatherCall_bound, hInv.bound_core, ?_, hInv.firstGatherCore_val,
          hInv.firstGatherCore_card,
        ?_, ?_⟩
      · intro k out hk
        refine ⟨(hInv.out_witness k out hk).1, ?_⟩
        have hc := (hInv.out_witness k out hk).2
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
      refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, hInv.firstGatherVal_of_call,
        hInv.secondGatherVal_of_call, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hInv.firstGatherCore_val,
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
          OutputWitness.mono rfl rfl (fun _ => le_refl _) (hInv.out_witness k out ?_).2⟩
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
    · rw [hF2]; exact hInv.secondGatherF_eq_firstGatherF
    · exact hInv.firstGatherVal_of_call
    · rw [hval2]
      intro k c hv
      rcases hInv.secondGatherVal_of_call k c hv with hf' | hc'
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
      refine ⟨(hInv.out_witness k out hk').1,
        OutputWitness.mono (s := s) ?_ ?_ ?_ (hInv.out_witness k out hk').2⟩
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
    refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, hInv.firstGatherVal_of_call,
      hInv.secondGatherVal_of_call, ?_, ?_, ?_, ?_, ?_, hInv.bound_core, ?_,
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
      exact hInv.out_witness k out' hk'
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
        rcases hInv.secondGatherVal_of_call k c (hsubv k c hgc) with hF | hin
        · exact absurd hF hkF
        · exact hInv.secondGatherCall_candidate k hkF c hin
      have hFirstGatherCoreAboveThreshold : ∀ v : Bool, P.f + 1 ≤ valueCount g (some v) →
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
      have hcert : OutputWitness P s (gradeOf P g) := by
        cases hout : gradeOf P g with
        | grade2 v =>
          refine ⟨⟨C, hC, count_aboveThreshold_of_subMap hmem (gradeOf_grade2 hout)⟩,
            hFirstGatherCoreAboveThreshold v ?_⟩
          have := gradeOf_grade2 hout
          omega
        | grade1 v =>
          obtain ⟨hBcnt, hBnotA⟩ := gradeOf_grade1 hout
          refine ⟨hFirstGatherCoreAboveThreshold v hBcnt, hsupp (!v) ?_⟩
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
      refine ⟨hInv.F_card, hInv.secondGatherF_eq_firstGatherF, hInv.firstGatherVal_of_call,
        hInv.secondGatherVal_of_call, ?_, ?_, ?_, ?_, ?_, hInv.bound_core, ?_,
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
          exact ⟨hbnd, OutputWitness.mono rfl rfl (fun _ => le_refl _) hcert⟩
        · rw [Function.update_of_ne hkid] at hk
          obtain ⟨hb, hc⟩ := hInv.out_witness k out hk
          exact ⟨hb, OutputWitness.mono rfl rfl (fun _ => le_refl _) hc⟩
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
    · rw [Gather.SpecState.corrupt_F, Gather.SpecState.corrupt_F,
        hInv.secondGatherF_eq_firstGatherF]
    · intro k v hv
      rw [Gather.corrupt_val] at hv
      rw [Gather.corrupt_call]
      rcases hInv.firstGatherVal_of_call k v hv with hF | hcl
      · exact Or.inl (hFsub hF)
      · exact Or.inr hcl
    · intro k c hcv
      rw [Gather.corrupt_val] at hcv
      rw [Gather.corrupt_call]
      rcases hInv.secondGatherVal_of_call k c hcv with hF | hin
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
      refine ⟨(hInv.out_witness k out hk).1,
        OutputWitness.mono (s := s) ?_ ?_ ?_ (hInv.out_witness k out hk).2⟩
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

end GBCA.ByAFW
end ABA
end PLTS
