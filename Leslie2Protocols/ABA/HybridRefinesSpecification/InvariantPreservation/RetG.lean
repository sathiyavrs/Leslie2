/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# `Invariant` across the `retG` transitions of `hybrid`

`Invariant.step_retG`, preservation of `Invariant` at a return of the graded-agreement
specification. The round's instance writes `.grade` and `.ret` alone, never `.F`, `.excluded` or
`.call`, and `Invariant` reads no `.ret`. The round loop of `id` takes the return on `retG` at the
phase and round it waits for, and writes `.estimate`, `.lastGrade` and `.phase` alone, never
`.round`, `.input` or its record of its DECIDED sends. At a process of `F`, and at a round loop that
does not wait for round `r`'s return, the round loop stays where it stands. At such a return no
clause on a round loop's round or phase changes, and the instance records the return, its grade
included, as at a return the round loop takes.

The proof uses two lemmas of this file that relate rounds: `Invariant.commit_to_later_rounds`
carries the guard pair `(!b) ∈ excluded ∧ b ∉ excluded` and the absence of grade 0 from a round to
every later round, and `Invariant.grade0_chain_to_earlier_rounds` carries grade 0 to every earlier
round. The round-`r` commitment of `grade2Bound_commit` comes from
`Invariant.commit_to_later_rounds`, and `agree_bound` at `id` from `Invariant.no_grade0_succ` and
`Invariant.no_grade0_succ_of_support`.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- Let round `r` be not graded 0, with `!b` excluded and `b` not excluded. Then every round
`r' ≥ r` has an empty exclusion set or the same guard pair `(!b) ∈ excluded ∧ b ∉ excluded`, and is
not graded 0. The induction step uses `bind_succ`: a bit excluded at round `r' + 1` is excluded at
round `r'`, and is therefore `!b` by the pair at `r'`, unless round `r'` is graded 0, which the
induction hypothesis rules out. `grade0_chain` carries grade 0 downward, so its contrapositive
carries the absence of grade 0 upward. -/
theorem Invariant.commit_to_later_rounds {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) :
    ∀ r b, (g r).grade ≠ some false → (!b) ∈ (g r).excluded → b ∉ (g r).excluded →
      ∀ r', r ≤ r' →
        ((g r').excluded = ∅ ∨ ((!b) ∈ (g r').excluded ∧ b ∉ (g r').excluded)) ∧
          (g r').grade ≠ some false := by
  intro r b hg hres hlive r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact ⟨Or.inr ⟨hres, hlive⟩, hg⟩
  | succ r' hrr' ih =>
    refine ⟨?_, fun h => ih.2 (hI.grade0_chain r' h)⟩
    rcases Finset.eq_empty_or_nonempty ((g (r' + 1)).excluded) with hemp | ⟨w', hw'⟩
    · exact Or.inl hemp
    · right
      have hwmem : ∀ x, x ∈ (g (r' + 1)).excluded → x = !b := by
        intro x hx
        have hxres : (!(!x)) ∈ (g (r' + 1)).excluded := by
          simpa using hx
        rcases hI.bind_succ r' (!x) hxres with hd | ⟨hgf, -⟩
        · rcases ih.1 with hn | ⟨hpr, hpl⟩
          · rw [hn] at hd; simp at hd
          · have hx' : x ∈ (g r').excluded := by simpa using hd
            have hxb : x ≠ b := fun hh => hpl (hh ▸ hx')
            revert hxb; cases x <;> cases b <;> simp
        · exact absurd hgf ih.2
      refine ⟨?_, fun hb0 => ?_⟩
      · have hwb := hwmem w' hw'
        rw [← hwb]; exact hw'
      · have hbb := hwmem b hb0
        exact absurd hbb (by cases b <;> simp)

/-- Grade 0 propagates downward to every earlier round, by iterating `grade0_chain`. -/
theorem Invariant.grade0_chain_to_earlier_rounds {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) :
    ∀ r r', r ≤ r' → (g r').grade = some false → (g r).grade = some false := by
  intro r r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact id
  | succ r' hrr' ih => intro h; exact ih (hI.grade0_chain r' h)

/-- `retG`: `Invariant` is preserved and the abstract state is unchanged at a return of the
graded-agreement specification. The first disjunct of `hstepC` is the round loop's `retG` at the
phase and round it waits for; the second is a return at which the round loop stays, at a process of
`F` or at a round loop that does not wait for round `r`'s return. -/
theorem Invariant.step_retG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitG ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcessVariables id { c.processes id with
            estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
        ((id ∈ c.F ∨ ¬((c.processes id).phase = .awaitG ∧ (c.processes id).round = r)) ∧
          μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P (Function.update g r gr') c' w ∧
      AbstractStateUnchanged P g (Function.update g r gr') c c' := by
  have hGUnchanged : gr'.F = (g r).F ∧ gr'.excluded = (g r).excluded ∧ gr'.call = (g r).call := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retGrade2 _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retGrade0 _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
  have hGgradeTrue : (g r).grade = some true → gr'.grade = some true := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h =>
      h
    | retGrade2 _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ =>
      rfl
    | retGrade0 _ _ _ _ hg _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
  have hGgradeFalse : (g r).grade = some false → gr'.grade = some false := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h =>
      h
    | retGrade2 _ _ _ _ hg _ => intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
    | retGrade0 _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ =>
      rfl
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGUnchanged.1
    · rw [hGeq r' h]
  have hExcludedEq : ∀ r', (Function.update g r gr' r').excluded = (g r').excluded := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGUnchanged.2.1
    · rw [hGeq r' h]
  have hCalleq : ∀ r', (Function.update g r gr' r').call = (g r').call := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGUnchanged.2.2
    · rw [hGeq r' h]
  have hGself : Function.update g r gr' r = gr' := by
    rw [Function.update_self]
  have hClosedEq : ∀ r', r' ≠ r → (RoundSettled (Function.update g r gr') r' ↔ RoundSettled g r') :=
    fun r' h => RoundSettled.congr (hExcludedEq r') (by rw [hGeq r' h])
  have hClosedTo : ∀ r', RoundSettled g r' → RoundSettled (Function.update g r gr') r' := by
    intro r' h
    refine RoundSettled.of_unchanged (hExcludedEq r') (fun hh => ?_) h
    by_cases h2 : r' = r
    · rw [h2, hGself]; exact hGgradeFalse (by rw [← h2]; exact hh)
    · rw [hGeq r' h2]; exact hh
  have hCUnchanged : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedReceived =
    c.decidedReceived ∧
      ∀ id', (c'.processes id').input = (c.processes id').input ∧
        (c'.processes id').round = (c.processes id').round := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨-, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProcessVariables_F _ _ _, ABAState.setProcessVariables_decidedSent _ _ _,
        ABAState.setProcessVariables_decidedReceived _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · rw [h, ABAState.setProcessVariables_processes_self]; exact ⟨rfl, rfl⟩
      · rw [ABAState.setProcessVariables_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCUnchanged
  have hCstepG : ((c.processes id).phase = .awaitG ∧ (c.processes id).round = r ∧
      c' = c.setProcessVariables id { c.processes id with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW }) ∨
      c' = c := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨-, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr hc'
  -- The return writes neither record of the DECIDED sends.
  have hRecordEq : ∀ j, (c'.1 j).decidedSent = (c.1 j).decidedSent := by
    intro j
    rcases hCstepG with ⟨-, -, rfl⟩ | rfl
    · by_cases hj : j = id
      · subst hj; simp [ABAState.setProcessVariables]
      · simp [ABAState.setProcessVariables, Function.update_of_ne hj]
    · rfl
  -- The return either returns the bit round `r` leaves not excluded (`retGrade2`/`retGrade1`, with
  -- the guard pair `v ∉ excluded ∧ (!v) ∈ excluded`) or returns no bit and sets the round's grade
  -- to 0 (`retGrade0`).
  have hRetInfo : (∃ v, out.estimate = some v ∧ v ∉ (g r).excluded ∧ (!v) ∈ (g r).excluded) ∨
      (out.estimate = none ∧ gr'.grade = some false) := by
    cases hstepG with
    | retGrade1 _ v hlive hexcluded _ _ => exact Or.inl ⟨v, rfl, hlive, hexcluded⟩
    | retGrade2 _ v hlive hexcluded _ _ => exact Or.inl ⟨v, rfl, hlive, hexcluded⟩
    | retGrade0 _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      exact Or.inr ⟨rfl, by rw [hgr']⟩
  -- A round graded 0 after the return has the `retGrade0` guards at `g r`: `grade0_support`
  -- gives them at a round graded 0 before the return (`retGrade1` writes no grade, `retGrade2`
  -- writes grade 2), and a `retGrade0` return has them as its guards.
  have hGrade0Support : gr'.grade = some false → ∀ b, P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g r).call id' = some b ∨ id' ∈ (g r).F)).card := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf b; rw [hgr'] at hgf; exact hI.grade0_support r b hgf
    | retGrade2 _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf; rw [hgr'] at hgf; simp at hgf
    | retGrade0 _ _ hwT hwF _ _ =>
      intro _ b; cases b
      · exact hwF
      · exact hwT
  have hGradeTrueOfGrade2 : ∀ b, out = .grade2 b → gr'.grade = some true := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ => intro b h; simp at h
    | retGrade2 _ _ _ _ _ _ => intro b h; rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']
    | retGrade0 _ _ _ _ _ _ => intro b h; simp at h
  have hGradeNoneTrans : (g r).grade ≠ none → gr'.grade ≠ none := by
    intro hgne hcontra
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hgne
    cases b' with
    | true => rw [hGgradeTrue hb'] at hcontra; simp at hcontra
    | false => rw [hGgradeFalse hb'] at hcontra; simp at hcontra
  have hGradedOrDissent : ∀ r', (g r').grade ≠ none ∨ DissentWitness P g c r' →
      (Function.update g r gr' r').grade ≠ none ∨
        DissentWitness P (Function.update g r gr') c' r' := by
    intro r' hres
    rcases hres with hg | hd
    · left
      by_cases h2 : r' = r
      · rw [h2, Function.update_self]; exact hGradeNoneTrans (h2 ▸ hg)
      · rwa [hGeq r' h2]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentWitness.preserved (hExcludedEq r') (hExcludedEq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentWitness.preserved (hExcludedEq r') (hExcludedEq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  -- A grade-0 return at round `r` admits no round graded 2 below `r`: its supports of both bits
  -- give grade 0 at round `r - 1` (`grade0_chain_of_both_supports`), and
  -- `grade0_chain_to_earlier_rounds` carries grade 0 to every earlier round.
  have hNoGrade2Below : ∀ r0, r0 < r → (g r0).grade = some true → gr'.grade = some false →
      False := by
    intro r0 hlt hg0 hgf
    have hr1 : r - 1 + 1 = r := by
      omega
    have hgf' := hI.grade0_chain_of_both_supports (r - 1)
      (by rw [hr1]; exact hGrade0Support hgf true) (by rw [hr1]; exact hGrade0Support hgf false)
    have hgf0 := hI.grade0_chain_to_earlier_rounds r0 (r - 1) (by omega) hgf'
    rw [hg0] at hgf0; simp at hgf0
  -- A holder after the return is a holder before it, or `id` holding the returned value.
  have hOutcomeHolderCases : ∀ r₀ i1 v1, OutcomeHolder P (Function.update g r gr') c' r₀ i1 v1 →
      OutcomeHolder P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.estimate = some v1) := by
    intro r₀ i1 v1 hc1
    rcases hc1 with hcall | ⟨he, hk⟩
    · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, ABAState.setProcessVariables_processes_self] at he hk
          right
          refine ⟨rfl, ?_, he⟩
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · rw [← hr0]; exact hr
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
      · rw [hc'eq] at he hk
        exact Or.inl (Or.inr ⟨he, hk⟩)
  -- Where an existing round-`r` holder comes from: the permanent fact `!v1 ∈ excluded` or grade 0.
  have hHolderSource : ∀ j1 v1, j1 ∉ c.F → OutcomeHolder P g c r j1 v1 →
      (!v1) ∈ (g r).excluded ∨ (g r).grade = some false := by
    intro j1 v1 hj hcar
    rcases hcar with hcall | ⟨he, hk⟩
    · rcases hI.call_of_previousRound r j1 v1 hj hcall with hd | ⟨hgf, -⟩
      · exact Or.inl hd
      · exact Or.inr hgf
    · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
      · obtain ⟨-, hsome⟩ := hI.estimate_ret r j1 hj hr0 hph
        exact Or.inl (hsome v1 he)
      · rcases hI.estimate_previous r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
  have hCommitTrans : ∀ r0 b0, (g r0).grade = some true → Grade2Commitment P g c r0 b0 →
      Grade2Commitment P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r' b'' hrr' hb' => h1 r' b'' hrr' (by rw [← hExcludedEq r']; exact hb'),
      fun r' id' b'' hrr' hmem hcall =>
        h2 r' id' b'' hrr' (hCF ▸ hmem) (by rw [← hCalleq r']; exact hcall),
      fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
    · rw [(hCprocs id').2] at hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
      · by_cases hid : id' = id
        · rw [hid, hc'eq, ABAState.setProcessVariables_processes_self]
          have hround' : r0 < r := by
            rw [hid, hr] at hround; exact hround
          rcases hRetInfo with ⟨v, hoev, hlive, hexcluded⟩ | ⟨-, hgf⟩
          · change out.estimate = some b0
            rw [hoev, h1 r v (le_of_lt hround') ⟨hexcluded, hlive⟩]
          · exact absurd hgf (fun hgf => hNoGrade2Below r0 hround' hg0 hgf)
        · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid]
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq]
        exact h3 id' (hCF ▸ hmem) hround
    · rcases hOutcomeHolderCases r0 id0 v hcar with hold | ⟨-, hreq, hev⟩
      · exact h4 id0 v (hCF ▸ hmem) hold
      · subst hreq
        rcases hRetInfo with ⟨u, hoev, hulive, huexcluded⟩ | ⟨-, hgf⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          exact h1 r0 u le_rfl ⟨huexcluded, hulive⟩
        · have hgt := hGgradeTrue hg0
          rw [hgf] at hgt
          simp at hgt
  have hWitnessTrans : ∀ r0 b0, Grade2Witness P g c r0 b0 →
      Grade2Witness P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg0, hres0, hcm⟩
    refine ⟨?_, by rw [hExcludedEq]; exact hres0, hCommitTrans r0 b0 hg0 hcm⟩
    by_cases h2 : r0 = r
    · rw [h2, hGself]; exact hGgradeTrue (h2 ▸ hg0)
    · rw [hGeq r0 h2]; exact hg0
  -- The round-`r` commitment after the return: when round `r` is not graded 0, the guard pair
  -- `(!b0) ∈ excluded ∧ b0 ∉ excluded` at it commits every round at and above it, through
  -- `commit_to_later_rounds`.
  have hFreshCommit : ∀ b0, (g r).grade ≠ some false →
      (!b0) ∈ (g r).excluded → b0 ∉ (g r).excluded →
      Grade2Commitment P (Function.update g r gr') c' r b0 := by
    intro b0 hgne hres0 hlive0
    have hCommitLater := hI.commit_to_later_rounds r b0 hgne hres0 hlive0
    have hThirdConjunct : ∀ id', id' ∉ c.F → r < (c.processes id').round →
        (c.processes id').estimate = some b0 := by
      intro id' hmem2 hround2
      by_cases hgroup : (c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW
      · obtain ⟨hnone, hsome⟩ := hI.estimate_ret (c.processes id').round id' hmem2 rfl hgroup
        rcases Option.eq_none_or_eq_some ((c.processes id').estimate) with he | ⟨v, he⟩
        · exfalso
          obtain ⟨hgf, -⟩ := hnone he
          exact (hCommitLater (c.processes id').round (by omega)).2 hgf
        · have hveq := hsome v he
          rw [he]
          rcases (hCommitLater (c.processes id').round (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hveq; simp at hveq
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by
                revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hveq)
            rw [hvb]
      · have hphase3 : (c.processes id').phase = .idle ∨ (c.processes id').phase = .toCallG ∨
            (c.processes id').phase = .awaitG ∨ (c.processes id').phase = .toSendDecided := by
          rcases hph2 : (c.processes id').phase with _ | _ | _ | _ | _ | _
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact absurd (Or.inl hph2) hgroup
          · exact absurd (Or.inr hph2) hgroup
          · exact Or.inr (Or.inr (Or.inr rfl))
        have hround1 : (c.processes id').round ≠ 0 := by
          omega
        have hne := hI.estimate_previous_ne id' hmem2 hround1 hphase3
        obtain ⟨v, he⟩ := Option.ne_none_iff_exists'.mp hne
        have hr'eq2 : (c.processes id').round = (c.processes id').round - 1 + 1 := by
          omega
        have hep := hI.estimate_previous ((c.processes id').round - 1) id' hmem2 hr'eq2 hphase3 v he
        rw [he]
        rcases hep with hbv | ⟨hgf, -⟩
        · rcases (hCommitLater ((c.processes id').round - 1) (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hbv; simp at hbv
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by
                revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hbv)
            rw [hvb]
        · exact absurd hgf (hCommitLater ((c.processes id').round - 1) (by omega)).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' b'' hrr' hb'
      rw [hExcludedEq r'] at hb'
      rcases (hCommitLater r' hrr').1 with hn | ⟨hres', hlive'⟩
      · rw [hn] at hb'; exact absurd hb'.1 (by simp)
      · by_contra hne
        have hv' : (!b'') = b0 := by
          revert hne; cases b'' <;> cases b0 <;> simp
        exact hlive' (hv' ▸ hb'.1)
    · intro r' id' b'' hrr' hmem hcall
      have hr'eq : r' = (r' - 1) + 1 := by
        omega
      rw [hCalleq] at hcall
      rw [hr'eq] at hcall
      have hcp := hI.call_of_previousRound (r' - 1) id' b'' (hCF ▸ hmem) hcall
      have hCommitPrevious := hCommitLater (r' - 1) (by omega)
      rcases hcp with hbv | ⟨hgf, -⟩
      · rcases hCommitPrevious.1 with hn | ⟨hres', hlive'⟩
        · rw [hn] at hbv; simp at hbv
        · by_contra hne
          have hv' : (!b'') = b0 := by
            revert hne; cases b'' <;> cases b0 <;> simp
          exact hlive' (hv' ▸ hbv)
      · exact absurd hgf hCommitPrevious.2
    · intro id' hmem hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
      · by_cases hid : id' = id
        · exfalso
          have hround' : r < (c.processes id).round := by
            simpa [hid, hc'eq, ABAState.setProcessVariables_processes_self] using hround
          omega
        · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hround ⊢
          exact hThirdConjunct id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact hThirdConjunct id' (hCF ▸ hmem) hround
    · intro id0 v hmem hcar
      rcases hOutcomeHolderCases r id0 v hcar with hold | ⟨-, -, hev⟩
      · rcases hHolderSource id0 v (hCF ▸ hmem) hold with hres | hgf
        · by_contra hne
          have hv' : (!v) = b0 := by
            revert hne; cases v <;> cases b0 <;> simp
          exact hlive0 (hv' ▸ hres)
        · exact absurd hgf hgne
      · rcases hRetInfo with ⟨u, hoev, hulive, -⟩ | ⟨hoe, -⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          by_contra hne
          have hv' : u = !b0 := by
            revert hne; cases u <;> cases b0 <;> simp
          exact hulive (hv' ▸ hres0)
        · rw [hoe] at hev; simp at hev
  have hGrade2HolderCases : ∀ i1 b1,
      Grade2Holder P c' i1 b1 → Grade2Holder P c i1 b1 ∨ (i1 = id ∧ out = .grade2 b1) := by
    intro i1 b1 h1
    rcases h1 with h1 | h1
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, ABAState.setProcessVariables_processes_self] at h1
          exact Or.inr ⟨rfl, Option.some_inj.mp h1⟩
        · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid1] at h1
          exact Or.inl (Or.inl h1)
      · rw [hc'eq] at h1
        exact Or.inl (Or.inl h1)
    · rw [hCDS] at h1
      exact Or.inl (Or.inr h1)
  -- The value of a grade-2 return against every existing witness: at the same round by the
  -- return's guard pair, at a witness below by the witness's commitment, at a witness above by
  -- the round-`r` commitment and the derived caller of the bit the witness leaves not excluded.
  have hWitnessAgree : ∀ b1, out = .grade2 b1 → ∀ r1 b1', Grade2Witness P g c r1 b1' →
      b1' = b1 := by
    intro b1 hout r1 b1' hWitness
    rcases hRetInfo with ⟨u, hoev, hulive, huexcluded⟩ | ⟨hoe, -⟩
    · have hu : u = b1 := by
        rw [hout] at hoev
        simpa using hoev.symm
      have hulive' : b1 ∉ (g r).excluded := hu ▸ hulive
      have huexcluded' : (!b1) ∈ (g r).excluded := hu ▸ huexcluded
      obtain ⟨hg1, hres1, hcm1⟩ := hWitness
      rcases lt_trichotomy r1 r with hlt | heq | hgt
      · exact (hcm1.1 r b1 (le_of_lt hlt) ⟨huexcluded', hulive'⟩).symm
      · subst heq
        by_contra hne
        have hv' : (!b1') = b1 := by
          revert hne; cases b1 <;> cases b1' <;> simp
        exact hulive' (hv' ▸ hres1)
      · have hgne : (g r).grade ≠ some false := fun hf => by
          have h1 := hGgradeFalse hf
          rw [hGradeTrueOfGrade2 b1 hout] at h1
          simp at h1
        have hRoundCommit := hFreshCommit b1 hgne huexcluded' hulive'
        obtain ⟨id0, hid0F, hcall0⟩ := GBCA.exists_correct_caller
          (hI.excluded_support r1 (!b1') hres1) (by rw [hI.F_gbca r1]; exact hI.F_card)
        have hcall0' : (g r1).call id0 = some b1' := by
          simpa using hcall0
        have hid0c' : id0 ∉ c'.F := by
          rw [hCF, ← hI.F_gbca r1]; exact hid0F
        exact hRoundCommit.2.1 r1 id0 b1' hgt hid0c' (by rw [hCalleq r1]; exact hcall0')
    · rw [hout] at hoe; simp at hoe
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hWitnessTrans r0 b0 hc⟩,
    fun v hcv hHolderAgree j b' hj hh => ?_⟩
  case refine_2 =>
    rcases hGrade2HolderCases j b' hh with hold | ⟨-, hout⟩
    · exact hHolderAgree j b' (hCF ▸ hj) hold
    · obtain ⟨r1, hcv1⟩ := hcv
      exact (hWitnessAgree b' hout r1 v hcv1).symm
  have hCcorr : c'.corrupted = c.corrupted := by
    rcases hCstepG with ⟨-, -, hc'eq⟩ | hc'eq
    · rw [hc'eq]; exact ABAState.setProcessVariables_corrupted _ _ _
    · rw [hc'eq]
  refine ⟨fun id' => by rw [hCcorr, hCF]; exact hI.corrupted_F id',
    fun r' => (hFgeq r').trans (hCF ▸ hI.F_gbca r'), fun r' => hCF ▸ hI.F_wcc r',
    hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id' b' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall
    exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.processes id').phase ≠ .idle := by
          rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- `down_settled`: at every other round nothing changes; at `r' + 1 = r` the supports of both
    -- bits of a grade-0 return give grade 0 at round `r'` (`grade0_chain_of_both_supports`).
    intro r' h
    by_cases h2 : r' = r
    · exact hClosedTo r' (hI.down_settled r' ((hClosedEq (r' + 1) (by omega)).mp h))
    · rw [hClosedEq r' h2]
      by_cases h1 : r' + 1 = r
      · rcases h with hb | hgf
        · refine hI.down_settled r' (Or.inl ?_)
          rw [← hExcludedEq (r' + 1)]; exact hb
        · have hgself : Function.update g r gr' (r' + 1) = gr' := by rw [h1]; exact hGself
          rw [hgself] at hgf
          exact Or.inr (hI.grade0_chain_of_both_supports r'
            (by rw [h1]; exact hGrade0Support hgf true)
            (by rw [h1]; exact hGrade0Support hgf false))
      · exact hI.down_settled r' ((hClosedEq (r' + 1) h1).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨max R (r + 1), fun r' hr' h =>
      hR r' (by omega) ((hClosedEq r' (by omega)).mp h)⟩
  · intro r' h; exact hClosedTo r' (hI.wcc_bound r' h)
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.received_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_source id' b' (hCF ▸ hmem) h).imp (fun r0 => hWitnessTrans r0 b')
  · intro j hj
    rw [hCDS, hRecordEq j]
    exact hI.decidedSent_recorded j (hCF ▸ hj)
  · intro r0 b0 hgr hbr
    by_cases hr0r : r0 = r
    · rw [hr0r, Function.update_self] at hgr hbr
      have hgne : (g r).grade ≠ some false := fun hf => by
        rw [hGgradeFalse hf] at hgr; simp at hgr
      have hb0eq : (!b0) ∈ (g r).excluded ∧ b0 ∉ (g r).excluded := by
        rw [← hGUnchanged.2.1]; exact hbr
      rw [hr0r]
      exact hFreshCommit b0 hgne hb0eq.1 hb0eq.2
    · rw [hGeq r0 hr0r] at hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Bound_commit r0 b0 hgr hbr
      refine ⟨fun r' b'' hrr' hb' => by rw [hExcludedEq] at hb'; exact h1 r' b'' hrr' hb',
        fun r' id' b'' hrr' hmem hcall => by
          rw [hCalleq] at hcall; exact h2 r' id' b'' hrr' (hCF ▸ hmem) hcall,
        fun id' hmem hround => ?_,
        fun id0 v hmem hcar => by
          rcases hOutcomeHolderCases r0 id0 v hcar with hold | ⟨-, hreq, -⟩
          · exact h4 id0 v (hCF ▸ hmem) hold
          · exact absurd hreq hr0r⟩
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
      · by_cases hid : id' = id
        · rw [hid] at hround hmem
          have hround' : r0 < (c.processes id).round := by
            simpa [hc'eq, ABAState.setProcessVariables_processes_self] using hround
          rw [hid, hc'eq, ABAState.setProcessVariables_processes_self]
          by_cases hr0lt : r0 < r
          · rcases hRetInfo with ⟨v, hoev, hlive, hexcluded⟩ | ⟨-, hgf⟩
            · rw [hoev, h1 r v (le_of_lt hr0lt) ⟨hexcluded, hlive⟩]
            · exact (hNoGrade2Below r0 hr0lt hgr hgf).elim
          · exfalso; omega
        · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hround ⊢
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2] at hround
    exact hClosedTo r' (hI.round_bound id' (hCF ▸ hmem) r' hround)
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hExcludedEq]; exact h),
      by rw [← hExcludedEq (r' + 1)]; exact hlast.2⟩
    rw [hExcludedEq] at hbr
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · -- `id` is at round `r` with `r' < r` and an agreeing coin at `r'`: round `r' + 1`
        -- neither excludes a bit (`hlast'`) nor is graded 0 (`no_grade0_succ`).
        exfalso
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        have hround' : r' < r := by
          rw [hid, hr] at hround; exact hround
        have hvNotExcluded : v ∉ (g r').excluded := hbr.2
        by_cases heq : r' + 1 = r
        · rcases hRetInfo with ⟨u, -, -, huexcluded⟩ | ⟨-, hgf⟩
          · rw [← heq] at huexcluded
            rw [hlast'.2] at huexcluded
            simp at huexcluded
          · exact hI.no_grade0_succ_of_support r' v hcoin hvNotExcluded
              (by rw [heq]; exact hGrade0Support hgf (!v))
        · rcases hI.round_bound id hmem' (r' + 1) (by omega) with hh | hh
          · exact hh hlast'.2
          · exact hI.no_grade0_succ r' v hcoin hvNotExcluded hh
      · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid]
        exact hI.agree_bound r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
    · rw [hc'eq]
      exact hI.agree_bound r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2, hExcludedEq]
      rcases hRetInfo with ⟨v, -, -, hexcluded⟩ | ⟨-, hgf⟩
      · exact fun hemp => by rw [hemp] at hexcluded; simp at hexcluded
      · exfalso; rw [h2, hGself, hgf] at h; simp at h
    · rw [hGeq r' h2] at h; rw [hExcludedEq]; exact hI.grade2_needs_bind r' h
  · intro r' id' hmem hcall
    rw [hCalleq] at hcall
    rw [(hCprocs id').2]
    exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    exact hClosedTo r' (hI.wcc_called r' id' (hCF ▸ hmem) hcalled)
  · intro r' id' hmem hround
    rw [(hCprocs id').2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcessVariables_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hphase
        rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid]
        exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
    · rw [(hCprocs id').2] at hround
      rw [hc'eq] at hphase
      rw [hc'eq]
      exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · -- the grade-2 return is its own witness: its guard pair and `hFreshCommit`
        rw [hid, hc'eq, ABAState.setProcessVariables_processes_self] at hlg
        rw [Option.some_inj] at hlg
        refine ⟨r, by rw [Function.update_self]; exact hGradeTrueOfGrade2 b' hlg, ?_, ?_⟩
        · rw [hExcludedEq]
          rcases hRetInfo with ⟨v, hoev, -, hexcluded⟩ | ⟨hoe, -⟩
          · have hb'eq : out.estimate = some b' := by simp [hlg]
            rw [hb'eq] at hoev
            rw [Option.some_inj.mp hoev]
            exact hexcluded
          · exfalso; rw [hlg] at hoe; simp at hoe
        · rcases hRetInfo with ⟨v, hoev, hlive, hexcluded⟩ | ⟨hoe, -⟩
          · have hb'eq : out.estimate = some b' := by simp [hlg]
            rw [hb'eq] at hoev
            have hveq := Option.some_inj.mp hoev
            have hgne : (g r).grade ≠ some false := fun hf => by
              have h1 := hGgradeFalse hf
              rw [hGradeTrueOfGrade2 b' hlg] at h1
              simp at h1
            exact hFreshCommit b' hgne (hveq ▸ hexcluded) (hveq ▸ hlive)
          · exfalso; rw [hlg] at hoe; simp at hoe
      · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hlg
        exact (hI.grade2_source id' b' hlg).imp (fun r0 => hWitnessTrans r0 b')
    · rw [hc'eq] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r0 => hWitnessTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · have hround' : (c.processes id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, ABAState.setProcessVariables_processes_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        simp only [hid, hreq, hc'eq, ABAState.setProcessVariables_processes_self]
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · rcases hRetInfo with ⟨v, hoev, -⟩ | ⟨-, hgf⟩
          · exfalso; rw [hoev] at he; simp at he
          · refine ⟨by rw [Function.update_self]; exact hgf, fun r₀ hr0 hgr0 => ?_⟩
            by_cases hr0eq : r₀ = r
            · rw [hr0eq, Function.update_self] at hgr0
              exact absurd (hgr0.symm.trans hgf) (by simp)
            · rw [hGeq r₀ hr0eq] at hgr0
              exact hNoGrade2Below r₀ (by omega) hgr0 hgf
        · rw [hExcludedEq]
          rcases hRetInfo with ⟨v, hoev, -, hexcluded⟩ | ⟨hoe, -⟩
          · rw [hoev] at hb
            rw [← Option.some_inj.mp hb]
            exact hexcluded
          · exfalso; rw [hoe] at hb; exact absurd hb (by simp)
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hphase
        obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
        rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid]
        refine ⟨fun he => ?_, fun b hb => by rw [hExcludedEq]; exact hsome b hb⟩
        obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
        · by_cases hrr : r' = r
          · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
          · rw [hGeq r' hrr]; exact hg0
        · by_cases hr0eq : r₀ = r
          · rw [hr0eq, Function.update_self] at hgr0
            by_cases hrr : r' = r
            · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
            · have hgrfalse : (g r).grade = some false :=
                hI.grade0_chain_to_earlier_rounds r r' (by omega) hg0
              rw [hGgradeFalse hgrfalse] at hgr0
              simp at hgr0
          · rw [hGeq r₀ hr0eq] at hgr0
            exact hno r₀ hr0 hgr0
    · rw [hc'eq] at hround hphase
      obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
      rw [hc'eq]
      refine ⟨fun he => ?_, fun b hb => by rw [hExcludedEq]; exact hsome b hb⟩
      obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
      · by_cases hrr : r' = r
        · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
        · rw [hGeq r' hrr]; exact hg0
      · by_cases hr0eq : r₀ = r
        · rw [hr0eq, Function.update_self] at hgr0
          by_cases hrr : r' = r
          · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
          · have hgrfalse : (g r).grade = some false :=
              hI.grade0_chain_to_earlier_rounds r r' (by omega) hg0
            rw [hGgradeFalse hgrfalse] at hgr0
            simp at hgr0
        · rw [hGeq r₀ hr0eq] at hgr0
          exact hno r₀ hr0 hgr0
  · intro r' v h
    rw [hExcludedEq (r' + 1)] at h
    rcases hI.bind_succ r' v h with hbv | ⟨hgf, hw0⟩
    · rw [hExcludedEq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' v hmem hcall
    rw [hCalleq] at hcall
    rcases hI.call_of_previousRound r' id' v (hCF ▸ hmem) hcall with hbv | ⟨hgf, hw0⟩
    · rw [hExcludedEq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcessVariables_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hphase hest
        rcases hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
        · rw [hExcludedEq r']; exact Or.inl hbv
        · by_cases h2 : r' = r
          · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
            exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
          · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
    · rw [hc'eq] at hphase hest
      rcases hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
      · rw [hExcludedEq r']; exact Or.inl hbv
      · by_cases h2 : r' = r
        · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
          exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
        · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2] at h ⊢
      rw [hGeq (r + 1) (by omega)] at h
      rw [Function.update_self]
      exact hGgradeFalse (hI.grade0_chain r h)
    · by_cases h1 : r' + 1 = r
      · rw [h1, Function.update_self] at h
        rw [hGeq r' h2]
        exact hI.grade0_chain_of_both_supports r' (by rw [h1]; exact hGrade0Support h true)
          (by rw [h1]; exact hGrade0Support h false)
      · rw [hGeq (r' + 1) h1] at h
        rw [hGeq r' h2]
        exact hI.grade0_chain r' h
  · intro id' hmem hround hphase
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcessVariables_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hphase ⊢
        exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase ⊢
      exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
  · intro id' b' h
    rw [hCalleq] at h
    rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2]; exact hI.wcc_callRound r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_witness r' h with hg | hd
    · left
      by_cases hrr : r' = r
      · rw [hrr, Function.update_self]; exact hGradeNoneTrans (hrr ▸ hg)
      · rwa [hGeq r' hrr]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentWitness.preserved (hExcludedEq r') (hExcludedEq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentWitness.preserved (hExcludedEq r') (hExcludedEq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin
    exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r'
  · -- `retG_witness` at `id`, which moves from `awaitG` to `toCallW` at round `r`: `retGrade2`
    -- and `retGrade0` grade the round, and the guards of `retGrade1` give a `DissentWitness`
    -- through `input_gbcaRound0` or `call_of_previousRound`. At every other process, and at a
    -- return at which the round loop stays, `hGradedOrDissent` carries the clause over.
    intro r' id' hmem hp
    rcases hp with ⟨hround, hphase⟩ | hlt
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
      · by_cases hid : id' = id
        · have hround' : (c.processes id).round = r' := by
            rw [hid] at hround
            simpa [hc'eq, ABAState.setProcessVariables_processes_self] using hround
          have hreq : r' = r := hround'.symm.trans hr
          rw [hreq, Function.update_self]
          cases hstepG with
          | retGrade2 _ _ _ _ _ _ =>
            rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retGrade0 _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retGrade1 _ v hlive hexcluded hw _ =>
            rw [PMF.mem_support_pure_iff] at hgr'
            by_cases hgn : (g r).grade = none
            · right
              obtain ⟨id0, hid0F, hcall0⟩ :=
                GBCA.exists_correct_caller hw (by rw [hI.F_gbca r]; exact hI.F_card)
              have hcF0 : id0 ∉ c.F := by
                rw [← hI.F_gbca r]; exact hid0F
              refine ⟨v, by rw [hExcludedEq r]; exact hexcluded, ?_⟩
              by_cases hr0 : r = 0
              · rw [if_pos hr0]
                refine ⟨id0, ?_⟩
                rw [(hCprocs id0).1]
                exact hI.input_gbcaRound0 id0 (!v) hcF0 (by rw [← hr0]; exact hcall0)
              · rw [if_neg hr0]
                have heqr : r - 1 + 1 = r := by
                  omega
                have hcp := hI.call_of_previousRound (r - 1) id0 (!v) hcF0 (by rw [heqr]; exact
                  hcall0)
                rcases hcp with hbv | ⟨hgf, -⟩
                · left; rw [hGeq (r - 1) (by omega)]; simpa using hbv
                · right; rw [hGeq (r - 1) (by omega)]; exact hgf
            · left; rw [hgr']; exact hgn
        · rw [(hCprocs id').2] at hround
          rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid] at hphase
          exact hGradedOrDissent r' (hI.retG_witness r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
      · rw [(hCprocs id').2] at hround
        rw [hc'eq] at hphase
        exact hGradedOrDissent r' (hI.retG_witness r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
    · rw [(hCprocs id').2] at hlt
      exact hGradedOrDissent r' (hI.retG_witness r' id' (hCF ▸ hmem) (Or.inr hlt))
  · intro r' id' hmem hcalled
    exact hGradedOrDissent r' (hI.wccCalled_witness r' id' (hCF ▸ hmem) hcalled)
  · intro r' h
    rw [hExcludedEq] at h
    exact GBCA.SpecState.quorum_of_eq (hFgeq r') (hCalleq r') (hI.bound_quorum r' h)
  · -- I26: the return writes no exclusion set and no input
    intro r' v hb
    rw [hExcludedEq r'] at hb
    exact (hI.bind_support r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx)
  · -- I27: the return writes no call entry and no `F`; at every other round it writes no grade,
    -- and at round `r` `hGrade0Support` gives the guards.
    intro r' b' hgf
    refine GBCA.callSupport_mono (s := g r') (fun id' h => by rw [hCalleq r']; exact h)
      (hFgeq r').ge ?_
    by_cases hrr : r' = r
    · rw [hrr, hGself] at hgf
      rw [hrr]
      exact hGrade0Support hgf b'
    · rw [hGeq r' hrr] at hgf
      exact hI.grade0_support r' b' hgf
  · -- I28: the return writes no exclusion set, no call entry and no `F`
    intro r' b0 hbd
    rw [hExcludedEq r'] at hbd
    exact GBCA.callSupport_mono (fun id' h => by rw [hCalleq r']; exact h) (hFgeq r').ge
      (hI.excluded_support r' b0 hbd)
  · -- I29: at a return of grade 1 or 2, every existing holder of the opposite bit has
    -- `v ∈ excluded`, which contradicts the guard `v ∉ excluded`; a grade-0 return sets the
    -- round's grade to 0.
    intro r₀ i0 j0 v v' hm hm' h h'
    have hOutcomeHolderCasesAt : ∀ i1 v1, OutcomeHolder P (Function.update g r gr') c' r₀ i1 v1 →
        OutcomeHolder P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.estimate = some v1) := by
      intro i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
      · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | hc'eq
        · by_cases hid1 : i1 = id
          · subst hid1
            rw [hc'eq, ABAState.setProcessVariables_processes_self] at he hk
            right
            refine ⟨rfl, ?_, he⟩
            rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
            · rw [← hr0]; exact hr
            · exfalso; rcases hp with hp | hp | hp <;> simp at hp
          · rw [hc'eq, ABAState.setProcessVariables_processes_ne _ _ _ hid1] at he hk
            exact Or.inl (Or.inr ⟨he, hk⟩)
        · rw [hc'eq] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hHolderSourceAt : ∀ j1 v1, j1 ∉ c.F → OutcomeHolder P g c r j1 v1 →
        (!v1) ∈ (g r).excluded ∨ (g r).grade = some false := by
      intro j1 v1 hj hcar
      rcases hcar with hcall | ⟨he, hk⟩
      · rcases hI.call_of_previousRound r j1 v1 hj hcall with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
      · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
        · obtain ⟨-, hsome⟩ := hI.estimate_ret r j1 hj hr0 hph
          exact Or.inl (hsome v1 he)
        · rcases hI.estimate_previous r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
          · exact Or.inl hd
          · exact Or.inr hgf
    have hReturnAgree : ∀ vnew j1 v1, j1 ∉ c.F → out.estimate = some vnew →
        OutcomeHolder P g c r j1 v1 → v1 = vnew ∨ (g r).grade = some false := by
      intro vnew j1 v1 hj hoev hcar
      rcases hHolderSourceAt j1 v1 hj hcar with hres | hgf
      · rcases hRetInfo with ⟨u, hoev', hulive, -⟩ | ⟨hoe, -⟩
        · have hu : u = vnew := Option.some_inj.mp (hoev'.symm.trans hoev)
          rw [hu] at hulive
          left
          by_contra hne
          have hv' : (!v1) = vnew := by
            revert hne; cases vnew <;> cases v1 <;> simp
          exact hulive (hv' ▸ hres)
        · rw [hoe] at hoev; simp at hoev
      · exact Or.inr hgf
    have hGradeTo : ∀ r₁, (g r₁).grade = some false →
        (Function.update g r gr' r₁).grade = some false := by
      intro r₁ hgf
      by_cases h2 : r₁ = r
      · rw [h2, hGself]; exact hGgradeFalse (h2 ▸ hgf)
      · rwa [hGeq r₁ h2]
    rcases hOutcomeHolderCasesAt i0 v h with hold0 | ⟨-, hreq0, hev0⟩
    · rcases hOutcomeHolderCasesAt j0 v' h' with hold1 | ⟨-, hreq1, hev1⟩
      · exact (hI.outcomeHolder_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1).imp
          (fun x => x) (hGradeTo r₀)
      · rcases hReturnAgree v' i0 v (hCF ▸ hm) hev1 (hreq1 ▸ hold0) with hvv | hgf
        · exact Or.inl hvv
        · exact Or.inr (by rw [hreq1]; exact hGradeTo r hgf)
    · rcases hOutcomeHolderCasesAt j0 v' h' with hold1 | ⟨-, -, hev1⟩
      · rcases hReturnAgree v j0 v' (hCF ▸ hm') hev0 (hreq0 ▸ hold1) with hvv | hgf
        · exact Or.inl hvv.symm
        · exact Or.inr (by rw [hreq0]; exact hGradeTo r hgf)
      · exact Or.inl (Option.some_inj.mp (hev0.symm.trans hev1))
  · -- I30: a grade-2 return is compared with the witness of every existing correct holder
    -- through `hWitnessAgree`.
    intro i0 j0 b0 b0' hm hm' h h'
    have hHolderAgree : ∀ b1, out = .grade2 b1 → ∀ j1 b1',
        j1 ∉ c.F → Grade2Holder P c j1 b1' → b1' = b1 := by
      intro b1 hout j1 b1' hj hold
      have hWitness : ∃ r1, Grade2Witness P g c r1 b1' := by
        rcases hold with h1 | h1
        · exact hI.grade2_source j1 b1' h1
        · exact hI.decided_source j1 b1' hj h1
      obtain ⟨r1, hcv1⟩ := hWitness
      exact hWitnessAgree b1 hout r1 b1' hcv1
    rcases hGrade2HolderCases i0 b0 h with hold0 | ⟨-, hout0⟩
    · rcases hGrade2HolderCases j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact hI.grade2Bound_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1
      · exact hHolderAgree b0' hout1 i0 b0 (hCF ▸ hm) hold0
    · rcases hGrade2HolderCases j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact (hHolderAgree b0 hout0 j0 b0' (hCF ▸ hm') hold1).symm
      · rw [hout0] at hout1
        simpa using hout1

end ABA
end PLTS
