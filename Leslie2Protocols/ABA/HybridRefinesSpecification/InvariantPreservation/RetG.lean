/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# `Invariant` across the `retG` rows of `hybrid`

`Invariant.step_retG`, preservation of `Invariant` at a return of the graded-agreement
specification. The GBCA instance only ever touches `.grade` and `.ret`, never `.F`, `.excluded` or
`.call`, and `.ret` is not inspected by `Invariant`; the core only ever touches `.estimate`,
`.lastGrade` and `.phase` at `id`, never `.round` or `.input`. The two round-chaining lemmas the
proof runs on stand beside it: `Invariant.commit_to_later_rounds` carries a live pair and the
absence of a grade-0 lock from a round to every later round, and
`Invariant.grade0Lock_chain_to_earlier_rounds` carries a grade-0 lock to every earlier round. The
hard obligations, `grade2Lock_commit`'s round-`r` commitment and `agree_locked`'s estimate transfer
at `id`, need GBCA's own graded-agreement safety and are handed off.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- Once a round `r` is not (yet) grade-0-locked and its surviving bit `b` is still alive, every
round `r' ≥ r` either has an empty exclusion set or the same live pair, and is never
grade-0-locked either: `bind_succ` forces every bit excluded at a freshly-bound round `r' + 1` to
be a bit already excluded at `r'` — hence `!b`, by the inductive pair — unless `r'` itself just
closed grade-0-locked (ruled out by the IH), and `grade0Lock_chain` propagates the absence of a
grade-0 lock downward, so its contrapositive propagates it upward along the induction. -/
theorem Invariant.commit_to_later_rounds {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) :
    ∀ r b, (g r).grade ≠ some false → (!b) ∈ (g r).excluded → b ∉ (g r).excluded →
      ∀ r', r ≤ r' →
        ((g r').excluded = ∅ ∨ ((!b) ∈ (g r').excluded ∧ b ∉ (g r').excluded)) ∧
          (g r').grade ≠ some false := by
  intro r b hg hres hlive r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact ⟨Or.inr ⟨hres, hlive⟩, hg⟩
  | succ r' hrr' ih =>
    refine ⟨?_, fun h => ih.2 (hI.grade0Lock_chain r' h)⟩
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

/-- Grade-0 locks propagate downward to every earlier round, by iterating `grade0Lock_chain`. -/
theorem Invariant.grade0Lock_chain_to_earlier_rounds {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P} {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) :
    ∀ r r', r ≤ r' → (g r').grade = some false → (g r).grade = some false := by
  intro r r' hrr'
  induction r', hrr' using Nat.le_induction with
  | base => exact id
  | succ r' hrr' ih => intro h; exact ih (hI.grade0Lock_chain r' h)

/-- `retG`: `Invariant` is preserved and the abstract state is unchanged at a return of the
graded-agreement specification. -/
theorem Invariant.step_retG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
    (bnd : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.retG r id out bnd) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitG ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcess id { c.processes id with
            estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P (Function.update g r gr') c' w ∧
      AbstractStateUnchanged P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.excluded = (g r).excluded ∧ gr'.call = (g r).call := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retGrade2 _ _ _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
    | retGrade0 _ _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact ⟨rfl, rfl, rfl⟩
  have hGgradeTrue : (g r).grade = some true → gr'.grade = some true := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h =>
      h
    | retGrade2 _ _ _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ =>
      rfl
    | retGrade0 _ _ _ _ _ hg _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
  have hGgradeFalse : (g r).grade = some false → gr'.grade = some false := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun h =>
      h
    | retGrade2 _ _ _ _ _ _ hg _ => intro hgt; rw [hgt] at hg; rcases hg with hg | hg <;> simp at hg
    | retGrade0 _ _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']; exact fun _ =>
      rfl
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').excluded = (g r').excluded := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hCalleq : ∀ r', (Function.update g r gr' r').call = (g r').call := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hGself : Function.update g r gr' r = gr' := by
    rw [Function.update_self]
  have hClosedEq : ∀ r', r' ≠ r → (RoundSettled (Function.update g r gr') r' ↔ RoundSettled g r') :=
    fun r' h => RoundSettled.congr (hBindeq r') (by rw [hGeq r' h])
  have hClosedTo : ∀ r', RoundSettled g r' → RoundSettled (Function.update g r gr') r' := by
    intro r' h
    refine RoundSettled.of_unchanged (hBindeq r') (fun hh => ?_) h
    by_cases h2 : r' = r
    · rw [h2, hGself]; exact hGgradeFalse (by rw [← h2]; exact hh)
    · rw [hGeq r' h2]; exact hh
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedReceived =
    c.decidedReceived ∧
      ∀ id', (c'.processes id').input = (c.processes id').input ∧
        (c'.processes id').round = (c.processes id').round := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProcess_F _ _ _, ABAState.setProcess_decidedSent _ _ _,
        ABAState.setProcess_decidedReceived _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · rw [h, ABAState.setProcess_processes_self]; exact ⟨rfl, rfl⟩
      · rw [ABAState.setProcess_processes_ne _ _ _ h]; exact ⟨rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hCstepG : ((c.processes id).phase = .awaitG ∧ (c.processes id).round = r ∧
      c' = c.setProcess id { c.processes id with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW }) ∨
      (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- The return either hands out round `r`'s surviving bit (`retGrade2`/`retGrade1`, with its live
  -- pair as fire-time guards) or hands out nothing and locks the round at 0 (`retGrade0`).
  have hRetInfo : (∃ v, out.estimate = some v ∧ v ∉ (g r).excluded ∧ (!v) ∈ (g r).excluded) ∨
      (out.estimate = none ∧ gr'.grade = some false) := by
    cases hstepG with
    | retGrade1 _ v _ hlive hexcluded _ _ _ => exact Or.inl ⟨v, rfl, hlive, hexcluded⟩
    | retGrade2 _ v _ hlive hexcluded _ _ _ => exact Or.inl ⟨v, rfl, hlive, hexcluded⟩
    | retGrade0 _ _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      exact Or.inr ⟨rfl, by rw [hgr']⟩
  -- A round that is grade-0-locked after the return carries the `retGrade0` guards at `g r`: either
  -- they were already there (`retGrade1` leaves the grade alone; `retGrade2` locks grade 2) or this
  -- very return supplied them.
  have hCsupp : gr'.grade = some false → ∀ b, P.f + 1 ≤ (Finset.univ.filter
      (fun id' => (g r).call id' = some b ∨ id' ∈ (g r).F)).card := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf b; rw [hgr'] at hgf; exact hI.grade0Lock_support r b hgf
    | retGrade2 _ _ _ _ _ _ _ _ =>
      rw [PMF.mem_support_pure_iff] at hgr'
      intro hgf; rw [hgr'] at hgf; simp at hgf
    | retGrade0 _ _ _ hwT hwF _ _ =>
      intro _ b; cases b
      · exact hwF
      · exact hwT
  have hGradeTrueOfGrade2 : ∀ b, out = .grade2 b → gr'.grade = some true := by
    cases hstepG with
    | retGrade1 _ _ _ _ _ _ _ _ => intro b h; simp at h
    | retGrade2 _ _ _ _ _ _ _ _ => intro b h; rw [PMF.mem_support_pure_iff] at hgr'; rw [hgr']
    | retGrade0 _ _ _ _ _ _ _ => intro b h; simp at h
  have hGradeNoneTrans : (g r).grade ≠ none → gr'.grade ≠ none := by
    intro hgne hcontra
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hgne
    cases b' with
    | true => rw [hGgradeTrue hb'] at hcontra; simp at hcontra
    | false => rw [hGgradeFalse hb'] at hcontra; simp at hcontra
  have hTransport : ∀ r', (g r').grade ≠ none ∨ DissentWitness P g c r' →
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
      · refine DissentWitness.transport (hBindeq r') (hBindeq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  -- A grade-0-locking return at round `r` pulls a grade-0 lock below every
  -- grade-2-locked round under `r` (its own both-bit supports via
  -- `grade0Lock_chain_of_both_supports`, then `grade0Lock_chain_to_earlier_rounds`) — contradiction.
  have hNoCAbove : ∀ r0, r0 < r → (g r0).grade = some true → gr'.grade = some false →
      False := by
    intro r0 hlt hg0 hgf
    have hr1 : r - 1 + 1 = r := by
      omega
    have hgf' := hI.grade0Lock_chain_of_both_supports (r - 1)
      (by rw [hr1]; exact hCsupp hgf true) (by rw [hr1]; exact hCsupp hgf false)
    have hgf0 := hI.grade0Lock_chain_to_earlier_rounds r0 (r - 1) (by omega) hgf'
    rw [hg0] at hgf0; simp at hgf0
  -- OutcomeHolder reduction: a carrier of the post-state is an old carrier or the freshly
  -- returned `id` itself, holding the return's own output.
  have hRedC : ∀ r₀ i1 v1, OutcomeHolder P (Function.update g r gr') c' r₀ i1 v1 →
      OutcomeHolder P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.estimate = some v1) := by
    intro r₀ i1 v1 hc1
    rcases hc1 with hcall | ⟨he, hk⟩
    · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, ABAState.setProcess_processes_self] at he hk
          right
          refine ⟨rfl, ?_, he⟩
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · rw [← hr0]; exact hr
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
      · rw [hc'eq] at he hk
        exact Or.inl (Or.inr ⟨he, hk⟩)
  -- Provenance of a standing round-`r` carrier: the permanent residue or the grade-0 lock.
  have hProvC : ∀ j1 v1, j1 ∉ c.F → OutcomeHolder P g c r j1 v1 →
      (!v1) ∈ (g r).excluded ∨ (g r).grade = some false := by
    intro j1 v1 hj hcar
    rcases hcar with hcall | ⟨he, hk⟩
    · rcases hI.call_provenance r j1 v1 hj hcall with hd | ⟨hgf, -⟩
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
    refine ⟨fun r' b'' hrr' hb' => h1 r' b'' hrr' (by rw [← hBindeq r']; exact hb'),
      fun r' id' b'' hrr' hmem hcall =>
        h2 r' id' b'' hrr' (hCF ▸ hmem) (by rw [← hCalleq r']; exact hcall),
      fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
    · rw [(hCprocs id').2] at hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · rw [hid, hc'eq, ABAState.setProcess_processes_self]
          have hround' : r0 < r := by
            rw [hid, hr] at hround; exact hround
          rcases hRetInfo with ⟨v, hoev, hlive, hexcluded⟩ | ⟨-, hgf⟩
          · show out.estimate = some b0
            rw [hoev, h1 r v (le_of_lt hround') ⟨hexcluded, hlive⟩]
          · exact absurd hgf (fun hgf => hNoCAbove r0 hround' hg0 hgf)
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid]
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq]
        exact h3 id' (hCF ▸ hmem) hround
    · rcases hRedC r0 id0 v hcar with hold | ⟨-, hreq, hev⟩
      · exact h4 id0 v (hCF ▸ hmem) hold
      · subst hreq
        rcases hRetInfo with ⟨u, hoev, hulive, huexcluded⟩ | ⟨-, hgf⟩
        · have hu : u = v := Option.some_inj.mp (hoev.symm.trans hev)
          rw [← hu]
          exact h1 r0 u le_rfl ⟨huexcluded, hulive⟩
        · have hgt := hGgradeTrue hg0
          rw [hgf] at hgt
          simp at hgt
  have hCertTrans : ∀ r0 b0, Grade2Certificate P g c r0 b0 →
      Grade2Certificate P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg0, hres0, hcm⟩
    refine ⟨?_, by rw [hBindeq]; exact hres0, hCommitTrans r0 b0 hg0 hcm⟩
    by_cases h2 : r0 = r
    · rw [h2, hGself]; exact hGgradeTrue (h2 ▸ hg0)
    · rw [hGeq r0 h2]; exact hg0
  -- The *fresh* round-`r` commitment: a live pair at the returning round that is not (yet)
  -- A grade-0-locked round commits everything at and above it, through `commit_to_later_rounds`'s
  -- pair invariant.
  have hFreshCommit : ∀ b0, (g r).grade ≠ some false →
      (!b0) ∈ (g r).excluded → b0 ∉ (g r).excluded →
      Grade2Commitment P (Function.update g r gr') c' r b0 := by
    intro b0 hgne hres0 hlive0
    have hCU := hI.commit_to_later_rounds r b0 hgne hres0 hlive0
    have hconj3 : ∀ id', id' ∉ c.F → r < (c.processes id').round →
        (c.processes id').estimate = some b0 := by
      intro id' hmem2 hround2
      by_cases hgroup : (c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW
      · obtain ⟨hnone, hsome⟩ := hI.estimate_ret (c.processes id').round id' hmem2 rfl hgroup
        rcases Option.eq_none_or_eq_some ((c.processes id').estimate) with he | ⟨v, he⟩
        · exfalso
          obtain ⟨hgf, -⟩ := hnone he
          exact (hCU (c.processes id').round (by omega)).2 hgf
        · have hveq := hsome v he
          rw [he]
          rcases (hCU (c.processes id').round (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hveq; simp at hveq
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by
                revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hveq)
            rw [hvb]
      · have hphase3 : (c.processes id').phase = .idle ∨ (c.processes id').phase = .toCallG ∨
            (c.processes id').phase = .awaitG := by
          rcases hph2 : (c.processes id').phase with _ | _ | _ | _ | _
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact absurd (Or.inl hph2) hgroup
          · exact absurd (Or.inr hph2) hgroup
        have hround1 : (c.processes id').round ≠ 0 := by
          omega
        have hne := hI.estimate_previous_ne id' hmem2 hround1 hphase3
        obtain ⟨v, he⟩ := Option.ne_none_iff_exists'.mp hne
        have hr'eq2 : (c.processes id').round = (c.processes id').round - 1 + 1 := by
          omega
        have hep := hI.estimate_previous ((c.processes id').round - 1) id' hmem2 hr'eq2 hphase3 v he
        rw [he]
        rcases hep with hbv | ⟨hgf, -⟩
        · rcases (hCU ((c.processes id').round - 1) (by omega)).1 with hn | ⟨hres', hlive'⟩
          · rw [hn] at hbv; simp at hbv
          · have hvb : v = b0 := by
              by_contra hne
              have hv' : (!v) = b0 := by
                revert hne; cases v <;> cases b0 <;> simp
              exact hlive' (hv' ▸ hbv)
            rw [hvb]
        · exact absurd hgf (hCU ((c.processes id').round - 1) (by omega)).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' b'' hrr' hb'
      rw [hBindeq r'] at hb'
      rcases (hCU r' hrr').1 with hn | ⟨hres', hlive'⟩
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
      have hcp := hI.call_provenance (r' - 1) id' b'' (hCF ▸ hmem) hcall
      have hcu2 := hCU (r' - 1) (by omega)
      rcases hcp with hbv | ⟨hgf, -⟩
      · rcases hcu2.1 with hn | ⟨hres', hlive'⟩
        · rw [hn] at hbv; simp at hbv
        · by_contra hne
          have hv' : (!b'') = b0 := by
            revert hne; cases b'' <;> cases b0 <;> simp
          exact hlive' (hv' ▸ hbv)
      · exact absurd hgf hcu2.2
    · intro id' hmem hround
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · exfalso
          have hround' : r < (c.processes id).round := by
            simpa [hid, hc'eq, ABAState.setProcess_processes_self] using hround
          omega
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hround ⊢
          exact hconj3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact hconj3 id' (hCF ▸ hmem) hround
    · intro id0 v hmem hcar
      rcases hRedC r id0 v hcar with hold | ⟨-, -, hev⟩
      · rcases hProvC id0 v (hCF ▸ hmem) hold with hres | hgf
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
  have hRedH : ∀ i1 b1,
      Grade2Holder P c' i1 b1 → Grade2Holder P c i1 b1 ∨ (i1 = id ∧ out = .grade2 b1) := by
    intro i1 b1 h1
    rcases h1 with h1 | h1
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid1 : i1 = id
        · subst hid1
          rw [hc'eq, ABAState.setProcess_processes_self] at h1
          exact Or.inr ⟨rfl, Option.some_inj.mp h1⟩
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid1] at h1
          exact Or.inl (Or.inl h1)
      · rw [hc'eq] at h1
        exact Or.inl (Or.inl h1)
    · rw [hCDS] at h1
      exact Or.inl (Or.inr h1)
  -- A fresh grade-2 return's value against any standing certificate: same round via the
  -- fire-time pair, below via the certificate's commitment, above via the fresh
  -- commitment and the derived caller of the certificate's spared bit.
  have hpinCert : ∀ b1, out = .grade2 b1 → ∀ r1 b1', Grade2Certificate P g c r1 b1' → b1' = b1 := by
    intro b1 hout r1 b1' hcert
    rcases hRetInfo with ⟨u, hoev, hulive, huexcluded⟩ | ⟨hoe, -⟩
    · have hu : u = b1 := by
        rw [hout] at hoev
        simpa using hoev.symm
      have hulive' : b1 ∉ (g r).excluded := hu ▸ hulive
      have huexcluded' : (!b1) ∈ (g r).excluded := hu ▸ huexcluded
      obtain ⟨hg1, hres1, hcm1⟩ := hcert
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
        have hFC := hFreshCommit b1 hgne huexcluded' hulive'
        obtain ⟨id0, hid0F, hcall0⟩ := GBCA.exists_correct_caller
          (hI.excluded_support r1 (!b1') hres1) (by rw [hI.F_gbca r1]; exact hI.F_card)
        have hcall0' : (g r1).call id0 = some b1' := by
          simpa using hcall0
        have hid0c' : id0 ∉ c'.F := by
          rw [hCF, ← hI.F_gbca r1]; exact hid0F
        exact hFC.2.1 r1 id0 b1' hgt hid0c' (by rw [hCalleq r1]; exact hcall0')
    · rw [hout] at hoe; simp at hoe
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v hcv hpin j b' hj hh => ?_⟩
  case refine_2 =>
    rcases hRedH j b' hh with hold | ⟨-, hout⟩
    · exact hpin j b' (hCF ▸ hj) hold
    · obtain ⟨r1, hcv1⟩ := hcv
      exact (hpinCert b' hout r1 v hcv1).symm
  have hCcorr : c'.corrupted = c.corrupted := by
    rcases hCstepG with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · rw [hc'eq]; exact ABAState.setProcess_corrupted _ _ _
    · rw [hc'eq]
  refine ⟨fun id' => by rw [hCcorr, hCF]; exact hI.corrupted_F id',
    fun r' => (hFgeq r').trans (hCF ▸ hI.F_gbca r'), fun r' => hCF ▸ hI.F_wcc r',
    hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro id' b' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall
    exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; rw [hCalleq] at hcall; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        have hne' : (c.processes id').phase ≠ .idle := by
          rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hne; exact hne
        exact hI.phase_input id' (hCF ▸ hmem) hne'
    · rw [hc'eq] at hne; rw [(hCprocs id').1]; exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- `down_settled`: off the returning round nothing moved; at `r' + 1 = r` a grade-0
    -- return's both-bit support pushes the grade-0 lock down one round
    -- (`grade0Lock_chain_of_both_supports`).
    intro r' h
    by_cases h2 : r' = r
    · exact hClosedTo r' (hI.down_settled r' ((hClosedEq (r' + 1) (by omega)).mp h))
    · rw [hClosedEq r' h2]
      by_cases h1 : r' + 1 = r
      · rcases h with hb | hgf
        · refine hI.down_settled r' (Or.inl ?_)
          rw [← hBindeq (r' + 1)]; exact hb
        · have hgself : Function.update g r gr' (r' + 1) = gr' := by rw [h1]; exact hGself
          rw [hgself] at hgf
          exact Or.inr (hI.grade0Lock_chain_of_both_supports r' (by rw [h1]; exact hCsupp hgf true)
            (by rw [h1]; exact hCsupp hgf false))
      · exact hI.down_settled r' ((hClosedEq (r' + 1) h1).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨max R (r + 1), fun r' hr' h =>
      hR r' (by omega) ((hClosedEq r' (by omega)).mp h)⟩
  · intro r' h; exact hClosedTo r' (hI.wcc_bound r' h)
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.received_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_source id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    by_cases hr0r : r0 = r
    · rw [hr0r, Function.update_self] at hgr hbr
      have hgne : (g r).grade ≠ some false := fun hf => by
        rw [hGgradeFalse hf] at hgr; simp at hgr
      have hb0eq : (!b0) ∈ (g r).excluded ∧ b0 ∉ (g r).excluded := by
        rw [← hGframe.2.1]; exact hbr
      rw [hr0r]
      exact hFreshCommit b0 hgne hb0eq.1 hb0eq.2
    · rw [hGeq r0 hr0r] at hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r0 b0 hgr hbr
      refine ⟨fun r' b'' hrr' hb' => by rw [hBindeq] at hb'; exact h1 r' b'' hrr' hb',
        fun r' id' b'' hrr' hmem hcall => by
          rw [hCalleq] at hcall; exact h2 r' id' b'' hrr' (hCF ▸ hmem) hcall,
        fun id' hmem hround => ?_,
        fun id0 v hmem hcar => by
          rcases hRedC r0 id0 v hcar with hold | ⟨-, hreq, -⟩
          · exact h4 id0 v (hCF ▸ hmem) hold
          · exact absurd hreq hr0r⟩
      rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · rw [hid] at hround hmem
          have hround' : r0 < (c.processes id).round := by
            simpa [hc'eq, ABAState.setProcess_processes_self] using hround
          rw [hid, hc'eq, ABAState.setProcess_processes_self]
          by_cases hr0lt : r0 < r
          · rcases hRetInfo with ⟨v, hoev, hlive, hexcluded⟩ | ⟨-, hgf⟩
            · rw [hoev, h1 r v (le_of_lt hr0lt) ⟨hexcluded, hlive⟩]
            · exact (hNoCAbove r0 hr0lt hgr hgf).elim
          · exfalso; omega
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hround ⊢
          exact h3 id' (hCF ▸ hmem) hround
      · rw [hc'eq] at hround ⊢
        exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2] at hround
    exact hClosedTo r' (hI.round_bound id' (hCF ▸ hmem) r' hround)
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · -- `id` sits at round `r` with `r' < r` and an agreeing coin at `r'`: round `r' + 1`
        -- can neither have bound (`hlast'`) nor be grade-0-locked (`no_grade0Lock_succ`).
        exfalso
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        have hround' : r' < r := by
          rw [hid, hr] at hround; exact hround
        have hbnd : v ∉ (g r').excluded := hbr.2
        by_cases heq : r' + 1 = r
        · rcases hRetInfo with ⟨u, -, -, huexcluded⟩ | ⟨-, hgf⟩
          · rw [← heq] at huexcluded
            rw [hlast'.2] at huexcluded
            simp at huexcluded
          · exact hI.no_grade0Lock_succ_of_support r' v hcoin hbnd
              (by rw [heq]; exact hCsupp hgf (!v))
        · rcases hI.round_bound id hmem' (r' + 1) (by omega) with hh | hh
          · exact hh hlast'.2
          · exact hI.no_grade0Lock_succ r' v hcoin hbnd hh
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid]
        exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
    · rw [hc'eq]
      exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2, hBindeq]
      rcases hRetInfo with ⟨v, -, -, hexcluded⟩ | ⟨-, hgf⟩
      · exact fun hemp => by rw [hemp] at hexcluded; simp at hexcluded
      · exfalso; rw [h2, hGself, hgf] at h; simp at h
    · rw [hGeq r' h2] at h; rw [hBindeq]; exact hI.grade2_needs_bind r' h
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
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid]
        exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
    · rw [(hCprocs id').2] at hround
      rw [hc'eq] at hphase
      rw [hc'eq]
      exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · -- the fresh grade-2 return certifies itself: its fire-time pair plus `hFreshCommit`
        rw [hid, hc'eq, ABAState.setProcess_processes_self] at hlg
        rw [Option.some_inj] at hlg
        refine ⟨r, by rw [Function.update_self]; exact hGradeTrueOfGrade2 b' hlg, ?_, ?_⟩
        · rw [hBindeq]
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
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hlg
        exact (hI.grade2_source id' b' hlg).imp (fun r0 => hCertTrans r0 b')
    · rw [hc'eq] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.processes id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, ABAState.setProcess_processes_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        simp only [hid, hreq, hc'eq, ABAState.setProcess_processes_self]
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · rcases hRetInfo with ⟨v, hoev, -⟩ | ⟨-, hgf⟩
          · exfalso; rw [hoev] at he; simp at he
          · refine ⟨by rw [Function.update_self]; exact hgf, fun r₀ hr0 hgr0 => ?_⟩
            by_cases hr0eq : r₀ = r
            · rw [hr0eq, Function.update_self] at hgr0
              exact absurd (hgr0.symm.trans hgf) (by simp)
            · rw [hGeq r₀ hr0eq] at hgr0
              exact hNoCAbove r₀ (by omega) hgr0 hgf
        · rw [hBindeq]
          rcases hRetInfo with ⟨v, hoev, -, hexcluded⟩ | ⟨hoe, -⟩
          · rw [hoev] at hb
            rw [← Option.some_inj.mp hb]
            exact hexcluded
          · exfalso; rw [hoe] at hb; exact absurd hb (by simp)
      · rw [(hCprocs id').2] at hround
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid]
        refine ⟨fun he => ?_, fun b hb => by rw [hBindeq]; exact hsome b hb⟩
        obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
        · by_cases hrr : r' = r
          · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
          · rw [hGeq r' hrr]; exact hg0
        · by_cases hr0eq : r₀ = r
          · rw [hr0eq, Function.update_self] at hgr0
            by_cases hrr : r' = r
            · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
            · have hgrfalse : (g r).grade = some false := hI.grade0Lock_chain_to_earlier_rounds r r' (by omega)
                hg0
              rw [hGgradeFalse hgrfalse] at hgr0
              simp at hgr0
          · rw [hGeq r₀ hr0eq] at hgr0
            exact hno r₀ hr0 hgr0
    · rw [hc'eq] at hround hphase
      obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
      rw [hc'eq]
      refine ⟨fun he => ?_, fun b hb => by rw [hBindeq]; exact hsome b hb⟩
      obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨?_, fun r₀ hr0 hgr0 => ?_⟩
      · by_cases hrr : r' = r
        · rw [hrr, Function.update_self]; exact hGgradeFalse (by rw [← hrr]; exact hg0)
        · rw [hGeq r' hrr]; exact hg0
      · by_cases hr0eq : r₀ = r
        · rw [hr0eq, Function.update_self] at hgr0
          by_cases hrr : r' = r
          · exact absurd hgr0 (by rw [hGgradeFalse (by rw [← hrr]; exact hg0)]; simp)
          · have hgrfalse : (g r).grade = some false := hI.grade0Lock_chain_to_earlier_rounds r r' (by omega) hg0
            rw [hGgradeFalse hgrfalse] at hgr0
            simp at hgr0
        · rw [hGeq r₀ hr0eq] at hgr0
          exact hno r₀ hr0 hgr0
  · intro r' v h
    rw [hBindeq (r' + 1)] at h
    rcases hI.bind_succ r' v h with hbv | ⟨hgf, hw0⟩
    · rw [hBindeq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' v hmem hcall
    rw [hCalleq] at hcall
    rcases hI.call_provenance r' id' v (hCF ▸ hmem) hcall with hbv | ⟨hgf, hw0⟩
    · rw [hBindeq r']; exact Or.inl hbv
    · by_cases h2 : r' = r
      · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
        exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
      · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase hest
        rcases hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
        · rw [hBindeq r']; exact Or.inl hbv
        · by_cases h2 : r' = r
          · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
            exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
          · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
    · rw [hc'eq] at hphase hest
      rcases hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest with hbv | ⟨hgf, hw0⟩
      · rw [hBindeq r']; exact Or.inl hbv
      · by_cases h2 : r' = r
        · rw [h2] at hgf hw0 ⊢; rw [Function.update_self]
          exact Or.inr ⟨hGgradeFalse hgf, hw0⟩
        · rw [hGeq r' h2]; exact Or.inr ⟨hgf, hw0⟩
  · intro r' h
    by_cases h2 : r' = r
    · rw [h2] at h ⊢
      rw [hGeq (r + 1) (by omega)] at h
      rw [Function.update_self]
      exact hGgradeFalse (hI.grade0Lock_chain r h)
    · by_cases h1 : r' + 1 = r
      · rw [h1, Function.update_self] at h
        rw [hGeq r' h2]
        exact hI.grade0Lock_chain_of_both_supports r' (by rw [h1]; exact hCsupp h true)
          (by rw [h1]; exact hCsupp h false)
      · rw [hGeq (r' + 1) h1] at h
        rw [hGeq r' h2]
        exact hI.grade0Lock_chain r' h
  · intro id' hmem hround hphase
    rw [(hCprocs id').2] at hround
    rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase ⊢
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
    rcases hI.flip_grade2Lock r' h with hg | hd
    · left
      by_cases hrr : r' = r
      · rw [hrr, Function.update_self]; exact hGradeNoneTrans (hrr ▸ hg)
      · rwa [hGeq r' hrr]
    · right
      by_cases hrr1 : r' - 1 = r
      · refine DissentWitness.transport (hBindeq r') (hBindeq (r' - 1)) (fun hgf => ?_)
          (fun id' => (hCprocs id').1) hd
        rw [hrr1, Function.update_self]; exact hGgradeFalse (hrr1 ▸ hgf)
      · exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
          (fun hgf => by rwa [hGeq (r' - 1) hrr1]) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin
    exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r'
  · -- `retG_witness`'s establishment: the freshly-`retG`'d `id` at round `r` (`awaitG →
    -- toCallW`) gets a fresh grade/dissent fact from the genuine GBCA return guards
    -- (`retGrade2`/`retGrade0` grade the round outright; `retGrade1`'s dissent converts
    -- to `DissentWitness` via `input_gbcaRound0`/`call_provenance`, mirroring
    -- `DissentWitness`'s own provenance argument);
    -- everywhere else is `hTransport`-routed pass-through of the pre-state fact.
    intro r' id' hmem hp
    rcases hp with ⟨hround, hphase⟩ | hlt
    · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
      · by_cases hid : id' = id
        · have hround' : (c.processes id).round = r' := by
            rw [hid] at hround
            simpa [hc'eq, ABAState.setProcess_processes_self] using hround
          have hreq : r' = r := hround'.symm.trans hr
          rw [hreq, Function.update_self]
          cases hstepG with
          | retGrade2 _ _ _ _ _ _ _ _ =>
            rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retGrade0 _ _ _ _ _ _ _ => rw [PMF.mem_support_pure_iff] at hgr'; left; rw [hgr']; simp
          | retGrade1 _ v _ hlive hexcluded _ hw _ =>
            rw [PMF.mem_support_pure_iff] at hgr'
            by_cases hgn : (g r).grade = none
            · right
              obtain ⟨id0, hid0F, hcall0⟩ :=
                GBCA.exists_correct_caller hw (by rw [hI.F_gbca r]; exact hI.F_card)
              have hcF0 : id0 ∉ c.F := by
                rw [← hI.F_gbca r]; exact hid0F
              refine ⟨v, by rw [hBindeq r]; exact hexcluded, ?_⟩
              by_cases hr0 : r = 0
              · rw [if_pos hr0]
                refine ⟨id0, ?_⟩
                rw [(hCprocs id0).1]
                exact hI.input_gbcaRound0 id0 (!v) hcF0 (by rw [← hr0]; exact hcall0)
              · rw [if_neg hr0]
                have heqr : r - 1 + 1 = r := by
                  omega
                have hcp := hI.call_provenance (r - 1) id0 (!v) hcF0 (by rw [heqr]; exact hcall0)
                rcases hcp with hbv | ⟨hgf, -⟩
                · left; rw [hGeq (r - 1) (by omega)]; simpa using hbv
                · right; rw [hGeq (r - 1) (by omega)]; exact hgf
            · left; rw [hgr']; exact hgn
        · rw [(hCprocs id').2] at hround
          rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
          exact hTransport r' (hI.retG_witness r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
      · rw [(hCprocs id').2] at hround
        rw [hc'eq] at hphase
        exact hTransport r' (hI.retG_witness r' id' (hCF ▸ hmem) (Or.inl ⟨hround, hphase⟩))
    · rw [(hCprocs id').2] at hlt
      exact hTransport r' (hI.retG_witness r' id' (hCF ▸ hmem) (Or.inr hlt))
  · intro r' id' hmem hcalled
    exact hTransport r' (hI.wccCalled_witness r' id' (hCF ▸ hmem) hcalled)
  · intro r' h
    rw [hBindeq] at h
    exact GBCA.SpecState.quorum_of_eq (hFgeq r') (hCalleq r') (hI.bound_quorum r' h)
  · -- I26: `retG` never touches `excluded`, sent sets pass through the `c`-frame
    intro r' v hb
    rw [hBindeq r'] at hb
    exact (hI.bind_support r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx)
  · -- I27: `retG` never touches `call`/`F`; off the returning round the grade is untouched
    -- too, and on it `hCsupp` reads the guards straight off the return.
    intro r' b' hgf
    refine GBCA.callSupport_mono (s := g r') (fun id' h => by rw [hCalleq r']; exact h)
      (hFgeq r').ge ?_
    by_cases hrr : r' = r
    · rw [hrr, hGself] at hgf
      rw [hrr]
      exact hCsupp hgf b'
    · rw [hGeq r' hrr] at hgf
      exact hI.grade0Lock_support r' b' hgf
  · -- I28: `retG` never touches `excluded`/`call`/`F`
    intro r' b0 hbd
    rw [hBindeq r'] at hbd
    exact GBCA.callSupport_mono (fun id' h => by rw [hCalleq r']; exact h) (hFgeq r').ge
      (hI.excluded_support r' b0 hbd)
  · -- I29 establishment: a fresh value-bearing return's carrier meets every standing
    -- opposite carrier's permanent residue head-on — the return's own liveness guard
    -- refutes it; a grade-0 return locks the round's grade instead.
    intro r₀ i0 j0 v v' hm hm' h h'
    have hred : ∀ i1 v1, OutcomeHolder P (Function.update g r gr') c' r₀ i1 v1 →
        OutcomeHolder P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ out.estimate = some v1) := by
      intro i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl (by rw [← hCalleq (r₀ + 1)]; exact hcall))
      · rcases hCstepG with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · by_cases hid1 : i1 = id
          · subst hid1
            rw [hc'eq, ABAState.setProcess_processes_self] at he hk
            right
            refine ⟨rfl, ?_, he⟩
            rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
            · rw [← hr0]; exact hr
            · exfalso; rcases hp with hp | hp | hp <;> simp at hp
          · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid1] at he hk
            exact Or.inl (Or.inr ⟨he, hk⟩)
        · rw [hc'eq] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hprov : ∀ j1 v1, j1 ∉ c.F → OutcomeHolder P g c r j1 v1 →
        (!v1) ∈ (g r).excluded ∨ (g r).grade = some false := by
      intro j1 v1 hj hcar
      rcases hcar with hcall | ⟨he, hk⟩
      · rcases hI.call_provenance r j1 v1 hj hcall with hd | ⟨hgf, -⟩
        · exact Or.inl hd
        · exact Or.inr hgf
      · rcases hk with ⟨hr0, hph⟩ | ⟨hr0, hph⟩
        · obtain ⟨-, hsome⟩ := hI.estimate_ret r j1 hj hr0 hph
          exact Or.inl (hsome v1 he)
        · rcases hI.estimate_previous r j1 hj hr0 hph v1 he with hd | ⟨hgf, -⟩
          · exact Or.inl hd
          · exact Or.inr hgf
    have hnewpin : ∀ vnew j1 v1, j1 ∉ c.F → out.estimate = some vnew → OutcomeHolder P g c r j1 v1 →
        v1 = vnew ∨ (g r).grade = some false := by
      intro vnew j1 v1 hj hoev hcar
      rcases hprov j1 v1 hj hcar with hres | hgf
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
    rcases hred i0 v h with hold0 | ⟨-, hreq0, hev0⟩
    · rcases hred j0 v' h' with hold1 | ⟨-, hreq1, hev1⟩
      · exact (hI.outcomeHolder_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1).imp
          (fun x => x) (hGradeTo r₀)
      · rcases hnewpin v' i0 v (hCF ▸ hm) hev1 (hreq1 ▸ hold0) with hvv | hgf
        · exact Or.inl hvv
        · exact Or.inr (by rw [hreq1]; exact hGradeTo r hgf)
    · rcases hred j0 v' h' with hold1 | ⟨-, -, hev1⟩
      · rcases hnewpin v j0 v' (hCF ▸ hm') hev0 (hreq0 ▸ hold1) with hvv | hgf
        · exact Or.inl hvv.symm
        · exact Or.inr (by rw [hreq0]; exact hGradeTo r hgf)
      · exact Or.inl (Option.some_inj.mp (hev0.symm.trans hev1))
  · -- I30 establishment: a fresh grade-2 return is compared against every standing correct
    -- holder's certificate through `hpinCert`.
    intro i0 j0 b0 b0' hm hm' h h'
    have hpin : ∀ b1, out = .grade2 b1 → ∀ j1 b1',
        j1 ∉ c.F → Grade2Holder P c j1 b1' → b1' = b1 := by
      intro b1 hout j1 b1' hj hold
      have hcert : ∃ r1, Grade2Certificate P g c r1 b1' := by
        rcases hold with h1 | h1
        · exact hI.grade2_source j1 b1' h1
        · exact hI.decided_source j1 b1' hj h1
      obtain ⟨r1, hcv1⟩ := hcert
      exact hpinCert b1 hout r1 b1' hcv1
    rcases hRedH i0 b0 h with hold0 | ⟨-, hout0⟩
    · rcases hRedH j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact hI.grade2Lock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm') hold0 hold1
      · exact hpin b0' hout1 i0 b0 (hCF ▸ hm) hold0
    · rcases hRedH j0 b0' h' with hold1 | ⟨-, hout1⟩
      · exact (hpin b0 hout0 j0 b0' (hCF ▸ hm') hold1).symm
      · rw [hout0] at hout1
        simpa using hout1

end ABA
end PLTS
