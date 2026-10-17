/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.Hybrid

/-!
# The step cases of `hybrid`

One lemma per visible label class (`callABA`, `retABA`, `fail`) and one for `τ`, each reading a
transition of the protocol-shaped specification back into the transitions of its four components.
The round loops and the ABA network are read as the pair `(C, A)` through `ABAState`'s accessors,
and the two families through their accessors: a round's write is `setInstanceState`, and the
corruption is the broadcast `applyBroadcast`. `hybrid_step_tau` is the nine-way disjunction the τ
case of the simulation dispatches on. Its τ has more sources than the visible labels do, every
synchronisation label and every sub-protocol API label being hidden. The nine are the silent
transitions of the round specifications and of the coin, a call or a return of a round or of the
coin with the round loop's half, a DECIDED message, and the transitions that leave the state as it
stands: the announcement, and the DECIDED delivery of a payload already held.

Every lemma takes I0 as a hypothesis, and the `retABA` and `τ` lemmas also take I4'. A round
loop's transition is guarded by its own replacement flag and the ABA network's by the corrupted
set, and I0 identifies the two, so that the statement is on `F` alone (D23);
`corrupted_eq_false_iff` is the one-line form of that translation. A correct round loop's return
and relay read its own record of its DECIDED sends, and I4' identifies that record with the
network's, so that the statement is on the network's record (D12′).
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]

/-- The round loop's correctness guard read on the corrupted set: under I0 the
replacement flag is not set exactly at the processes outside `F`. -/
theorem corrupted_eq_false_iff {P : Parameters} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {A : ABANetworkState P.n}
    (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (id : Fin P.n) : (C id).corrupted = false ↔ id ∉ ABAState.F (C, A) := by
  have h := hcorr id
  rw [ABAState.corrupted_apply] at h
  cases hb : (C id).corrupted <;> rw [hb] at h <;> simp_all

/-- `hybrid` step cases, `callABA`: the round specifications and the common coin idle on a label
outside their own API and the ABA network idles, so the whole transition is the addressed round
loop's: the input of a correct process, guarded by `input = ⊥`, or a self-loop, which is the
input-enabledness transition of an unreplaced program holding an input, and the replaced
program's own transition otherwise (D23, D36). -/
theorem hybrid_step_callABA (P : Parameters) (G : GBCASpecificationFamilyState P M)
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) (id : Fin P.n)
    (b : Bool) (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (μ : PMF (HybridState P M)) :
    (hybrid P M).step (G, C, A, o) (.callABA id b) μ ↔
      ∃ μc : PMF (ABAState P),
        ((id ∉ ABAState.F (C, A) ∧ (ABAState.processes (C, A) id).input = none ∧
            μc = PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with
                input := some b, estimate := some b, round := 0, phase := .toCallG })) ∨
          ((ABAState.corrupted (C, A) id = true ∨
              (ABAState.processes (C, A) id).input ≠ none) ∧
            μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o)) := by
  have hWlift : (coinOverRoundAlphabet P M).step o (Sum.inl (Label.callABA id b)) (PMF.pure o) :=
    (System.mapIdle_step_some (coinLabelMap_inl (Label.callABA id b)) (PMF.pure o)).mpr
      (wccFamily_idle P o (by simp) rfl (by simp [Label.isFail]))
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridHidden_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_cases P (by simp) hpre
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_callABA hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_cases P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.callABA id b)) _).mp hW)
        rcases roundLoopStep_callABA_own (hall id) with ⟨hh, hin, hx0⟩ | ⟨hloop, hx0⟩
        · obtain rfl : C' = Function.update C id ((C id).setProcessVariables
              { (C id).processVariables with
                input := some b, estimate := some b, round := 0, phase := .toCallG }) :=
            roundLoopVariables_update hx0 (fun i hi => roundLoopStep_callABA_notOwn (Ne.symm hi)
              (hall i))
          exact ⟨PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with
                input := some b, estimate := some b, round := 0, phase := .toCallG }),
            Or.inl ⟨(corrupted_eq_false_iff hcorr id).mp hh, hin, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩
        · obtain rfl : C = C' := (roundLoopVariables_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_callABA_notOwn (Ne.symm hi) (hall i)).symm
          exact ⟨PMF.pure (C, A), Or.inr ⟨hloop, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩
  · rintro ⟨μc, hdisj, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridHidden_step_iff]
    refine Or.inr ?_
    rcases hdisj with ⟨hnF, hin, rfl⟩ | ⟨hloop, rfl⟩
    · have h := hybridExtended_visible_step (M := M) P (L := Sum.inl (Label.callABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (roundLoopVariables_family id ((C id).setProcessVariables { (C id).processVariables with
            input := some b, estimate := some b, round := 0, phase := .toCallG })
          (RoundLoopStep.input (C id) b ((corrupted_eq_false_iff hcorr id).mpr hnF) hin)
          (fun i hi => RoundLoopStep.callABAIdle (C i) id b (Ne.symm hi)))
        (ABANetworkStep.callABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h
    · have h := hybridExtended_visible_step (M := M) P (L := Sum.inl (Label.callABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (fun i => by
          by_cases hi : i = id
          · subst hi
            simp only [ABAState.corrupted_apply, ABAState.processes_apply] at hloop
            cases hb : (C i).corrupted
            · exact RoundLoopStep.inputLoop (C i) b hb
                (hloop.resolve_left (by rw [hb]; simp))
            · exact RoundLoopStep.corruptedIdle (C i) _ hb (by simp) (by simp [roundLoopActsAt])
          · exact RoundLoopStep.callABAIdle (C i) id b (Ne.symm hi))
        (ABANetworkStep.callABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h

/-- `hybrid` step cases, `retABA`: a correct process returns on an `n − f` DECIDED quorum, having
sent `⟨DECIDED, b⟩` itself. Both guards are the round loop's; the second reads the round loop's own
record, which I4' identifies with the network's. A corrupted process returns any bit at any time
and the state does not move: the replaced program's half is its self-loop, and the ABA network
takes the return on one unguarded transition (D23). -/
theorem hybrid_step_retABA (P : Parameters) (G : GBCASpecificationFamilyState P M)
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) (id : Fin P.n)
    (b : Bool) (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (hrecorded : ∀ k, k ∉ ABAState.F (C, A) → (C k).decidedSent = ABAState.decidedSent (C, A) k)
    (μ : PMF (HybridState P M)) :
    (hybrid P M).step (G, C, A, o) (.retABA id b) μ ↔
      ∃ μc : PMF (ABAState P),
        ((id ∉ ABAState.F (C, A) ∧
            P.n - P.f ≤ ABAState.decidedCount (C, A) id b ∧
            b ∈ ABAState.decidedSent (C, A) id ∧
            (ABAState.processes (C, A) id).returned = false ∧
            μc = PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with returned := true })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o)) := by
  have hWlift : (coinOverRoundAlphabet P M).step o (Sum.inl (Label.retABA id b)) (PMF.pure o) :=
    (System.mapIdle_step_some (coinLabelMap_inl (Label.retABA id b)) (PMF.pure o)).mpr
      (wccFamily_idle P o (by simp) rfl (by simp [Label.isFail]))
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridHidden_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_cases P (by simp) hpre
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_retABA hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_cases P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.retABA id b)) _).mp hW)
        rcases roundLoopStep_retABA_own (hall id) with ⟨hh, hcnt, hsent, hret, hx0⟩ | ⟨hh, hx0⟩
        · have hnF : id ∉ ABAState.F (C, A) := (corrupted_eq_false_iff hcorr id).mp hh
          obtain rfl : C' = Function.update C id
              ((C id).setProcessVariables { (C id).processVariables with returned := true }) :=
            roundLoopVariables_update hx0 (fun i hi => roundLoopStep_retABA_notOwn (Ne.symm hi)
              (hall i))
          exact ⟨PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with returned := true }),
            Or.inl ⟨hnF, hcnt, hrecorded id hnF ▸ hsent, hret, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩
        · obtain rfl : C = C' := (roundLoopVariables_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_retABA_notOwn (Ne.symm hi) (hall i)).symm
          exact ⟨PMF.pure (C, A), Or.inr ⟨(hcorr id).mp hh, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩
  · rintro ⟨μc, hdisj, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridHidden_step_iff]
    refine Or.inr ?_
    rcases hdisj with ⟨hnF, hcnt, hsent, hret, rfl⟩ | ⟨hF, rfl⟩
    · have hsent' : b ∈ (C id).decidedSent := (hrecorded id hnF).symm ▸ hsent
      have h := hybridExtended_visible_step (M := M) P (L := Sum.inl (Label.retABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (roundLoopVariables_family id ((C id).setProcessVariables { (C id).processVariables with
          returned := true })
          (RoundLoopStep.ret (C id) b ((corrupted_eq_false_iff hcorr id).mpr hnF) hcnt hsent' hret)
          (fun i hi => RoundLoopStep.retABAIdle (C i) id b (Ne.symm hi)))
        (ABANetworkStep.retABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h
    · have h := hybridExtended_visible_step (M := M) P (L := Sum.inl (Label.retABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (fun i => by
          by_cases hi : i = id
          · subst hi
            exact RoundLoopStep.corruptedIdle (C i) _ ((hcorr i).mpr hF) (by simp)
              (by simp [roundLoopActsAt])
          · exact RoundLoopStep.retABAIdle (C i) id b (Ne.symm hi))
        (ABANetworkStep.retABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h

/-- `hybrid` step cases, `fail`: a synchronisation of all four components, under the two guards
the ABA network's transition carries: the named process is not corrupted yet and the budget has
room. The two families apply the corruption to every round by their broadcast, and the ABA network
corrupts the projection's `F`; the named round loop replaces its own program by writing the flag
(D23), and every other round loop is unchanged (D1). -/
theorem hybrid_step_fail (P : Parameters) (G : GBCASpecificationFamilyState P M)
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
    (id : Fin P.n) (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (μ : PMF (HybridState P M)) :
    (hybrid P M).step (G, C, A, o) (.fail id) μ ↔
      id ∉ ABAState.F (C, A) ∧ (ABAState.F (C, A)).card < P.f ∧
      μ = prodPMF (PMF.pure (G.applyBroadcast (Sum.inl (Label.fail id))))
        ((PMF.pure (ABAState.corrupt P id (C, A))).map
          fun c => (c.1, c.2, o.applyBroadcast (Label.fail id))) := by
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridHidden_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_cases P (by simp) hpre
        obtain rfl : G' = G.applyBroadcast (Sum.inl (Label.fail id)) :=
          pure_inj (gbcaSpecificationFamily_fail_cases P id hG)
        obtain ⟨hnew, hbud, hA'⟩ := abaNetworkStep_fail hA
        obtain rfl : A' = ABANetworkState.corrupt P id A := pure_inj hA'
        obtain rfl : ω = PMF.pure (o.applyBroadcast (Label.fail id)) := wccFamily_fail_cases P id
          ((System.mapIdle_step_some (coinLabelMap_inl (Label.fail id)) _).mp hW)
        have hh : (C id).corrupted = false := (corrupted_eq_false_iff hcorr id).mpr hnew
        obtain rfl : C' = Function.update C id { C id with corrupted := true } := by
          refine roundLoopVariables_update ?_ (fun i hi => roundLoopStep_fail_notOwn (Ne.symm hi)
            (hall i))
          rcases roundLoopStep_fail_own (hall id) with ⟨-, hx0⟩ | ⟨habs, -⟩
          · exact hx0
          · rw [hh] at habs; exact absurd habs (by simp)
        refine ⟨hnew, hbud, ?_⟩
        simp only [PMF.pure_map, prodPMF_pure_pure]
        rfl
  · rintro ⟨hnew, hbud, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridHidden_step_iff]
    refine Or.inr ?_
    have h := hybridExtended_visible_step (M := M) P (L := Sum.inl (Label.fail id)) (by simp)
      (gbcaSpecificationFamily_fail P G id)
      (roundLoopVariables_family id { C id with corrupted := true }
        (RoundLoopStep.failSelf (C id) ((corrupted_eq_false_iff hcorr id).mpr hnew))
        (fun i hi => RoundLoopStep.failIdle (C i) id (Ne.symm hi)))
      (ABANetworkStep.fail A id hnew hbud)
      ((System.mapIdle_step_some (coinLabelMap_inl (Label.fail id)) _).mpr (wccFamily_fail P o id))
    simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
    exact h

/-- `hybrid` step cases, `τ` (`mp` only: the preservation needs the forward direction alone).
A silent transition of `hybrid` has one of nine sources:

1. the binding exclusion of one round of the specification family's map;
2. a DECIDED message of the projection: a delivery of a payload not held, the `f + 1` relay of a
   correct process, writing both records, or the injection or relay of a corrupted process,
   writing the network's record alone;
3. a graded-agreement call, which the round's specification takes on its call or its loop: the
   call of a correct round loop, at which the ABA network records the round's start, or the
   network's call for a corrupted process at a started round (D11, D37), at which
   `recordStartedRound` is the identity, the process lying in `F`;
4. the graded-agreement return, the round loop taking it on `retG` at the phase and round it waits
   for, and on its loop or its self-loop elsewhere;
5. a coin call, which the coin takes on its call or its loop: the call of a correct round loop,
   or the network's call for a corrupted process at a started round;
6. the coin return, taken as the graded-agreement return is;
7. the DECIDED send of a grade-2 round, after the coin return;
8. the resolution of one round of the coin's map;
9. a transition that leaves the state as it stands: the announcement of a round's bound bit, and
   the DECIDED delivery of a payload already held from its sender or to a replaced round loop.

The round loop has no silent transition, and a replaced program contributes no source of its own:
its self-loop on `retG`, `retW` and `decidedRelay` is the corrupted disjunct of those sources,
`id ∈ F` being supplied by I0 (D23). -/
theorem hybrid_step_tau (P : Parameters) (G : GBCASpecificationFamilyState P M)
    (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
    (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (hrecorded : ∀ k, k ∉ ABAState.F (C, A) → (C k).decidedSent = ABAState.decidedSent (C, A) k)
    (μ : PMF (HybridState P M))
    (hstep : (hybrid P M).step (G, C, A, o) .tau μ) :
    (∃ r μr, GBCA.Step P r (G r) .tau μr ∧
        μ = prodPMF (μr.map (G.setInstanceState r)) (PMF.pure (C, A, o))) ∨
      (∃ μc : PMF (ABAState P),
        ((∃ i j b, b ∈ ABAState.decidedSent (C, A) j ∧
              b ∉ ABAState.decidedReceived (C, A) i j ∧
              μc = PMF.pure (ABAState.deliverDecided (C, A) i j b)) ∨
          (∃ k b, P.f + 1 ≤ ABAState.decidedCount (C, A) k b ∧
              b ∉ ABAState.decidedSent (C, A) k ∧
              μc = PMF.pure (ABAState.relayDecided (C, A) k b)) ∨
          (∃ k b, k ∈ ABAState.F (C, A) ∧
              μc = PMF.pure (ABAState.recordDecided (C, A) k b))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (b : Bool) (μr : PMF (GBCA.SpecState P.n))
          (μc : PMF (ABAState P)), GBCA.Step P r (G r) (.callG r id b) μr ∧
        (((ABAState.processes (C, A) id).phase = .toCallG ∧
            (ABAState.processes (C, A) id).round = r ∧
            (ABAState.processes (C, A) id).estimate = some b ∧
            μc = PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with phase := .awaitG })) ∨
          (id ∈ ABAState.F (C, A) ∧ r ∈ ABAState.startedRounds (C, A) ∧
            μc = PMF.pure (C, A))) ∧
        μ = prodPMF (μr.map (G.setInstanceState r))
          (μc.map fun c => (c.1, c.2.recordStartedRound r id, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (μr : PMF (GBCA.SpecState P.n))
          (μc : PMF (ABAState P)), GBCA.Step P r (G r) (.retG r id out) μr ∧
        (((ABAState.processes (C, A) id).phase = .awaitG ∧
            (ABAState.processes (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with
                estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
          ((id ∈ ABAState.F (C, A) ∨ ¬((ABAState.processes (C, A) id).phase = .awaitG ∧
              (ABAState.processes (C, A) id).round = r)) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (μr.map (G.setInstanceState r)) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (μw' : PMF (WCC.SpecState P.n))
          (μc : PMF (ABAState P)), WCC.Step P r (o r) (.callW r id) μw' ∧
        (((ABAState.processes (C, A) id).phase = .toCallW ∧
            (ABAState.processes (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with phase := .awaitW })) ∨
          (id ∈ ABAState.F (C, A) ∧ r ∈ ABAState.startedRounds (C, A) ∧
            μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.bind fun c => prodPMF (PMF.pure c.1)
              (prodPMF (PMF.pure c.2) (μw'.map (o.setInstanceState r))))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (b : Bool) (μw' : PMF (WCC.SpecState P.n))
          (μc : PMF (ABAState P)), WCC.Step P r (o r) (.retW r id b) μw' ∧
        (((ABAState.processes (C, A) id).phase = .awaitW ∧
            (ABAState.processes (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.stepRound (C, A) id b)) ∨
          ((id ∈ ABAState.F (C, A) ∨ ¬((ABAState.processes (C, A) id).phase = .awaitW ∧
              (ABAState.processes (C, A) id).round = r)) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.bind fun c => prodPMF (PMF.pure c.1)
              (prodPMF (PMF.pure c.2) (μw'.map (o.setInstanceState r))))) ∨
      (∃ (id : Fin P.n) (b : Bool) (μc : PMF (ABAState P)),
        (id ∉ ABAState.F (C, A) ∧ (ABAState.processes (C, A) id).phase = .toSendDecided ∧
            (ABAState.processes (C, A) id).lastGrade = some (.grade2 b) ∧
            μc = PMF.pure (ABAState.sendDecidedOnGrade2 (C, A) id b)) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (μw : PMF (WCC.SpecState P.n)), WCC.Step P r (o r) .tau μw ∧
        μ = prodPMF (PMF.pure G) (prodPMF (PMF.pure C)
          (prodPMF (PMF.pure A) (μw.map (o.setInstanceState r))))) ∨
      μ = PMF.pure (G, C, A, o) := by
  rw [hybrid_step_iff] at hstep
  rcases hstep with ⟨-, l', hl', hg⟩ | ⟨-, hg⟩
  · rw [hybridHidden_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact absurd hl' (by simp)
    · -- a sub-protocol API label, sent to `τ` by the outer hiding
      obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
        hybridExtended_visible_cases P (by rintro ⟨⟩; exact absurd hl' (by simp)) hpre
      cases l' with
      | tau => exact absurd hl' (by simp)
      | callABA id b => exact absurd hl' (by simp)
      | retABA id b => exact absurd hl' (by simp)
      | fail k => exact absurd hl' (by simp)
      | callG r id b =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : A' = A.recordStartedRound r id := pure_inj (abaNetworkStep_callG hA)
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_cases P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.callG r id b)) _).mp hW)
        obtain ⟨-, hph, hr, hest, hx0⟩ := roundLoopStep_callG_own (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProcessVariables { (C id).processVariables with phase := .awaitG }) :=
          roundLoopVariables_update hx0 (fun i hi => roundLoopStep_callG_notOwn (Ne.symm hi)
            (hall i))
        exact Or.inr (Or.inr (Or.inl ⟨r, id, b, PMF.pure X,
          PMF.pure (ABAState.setProcessVariables (C, A) id
            { ABAState.processes (C, A) id with phase := .awaitG }),
          hstepG, Or.inl ⟨hph, hr, hest, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩))
      | retG r id out =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_retG hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_cases P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.retG r id out)) _).mp hW)
        rcases roundLoopStep_retG_own (hall id) with ⟨-, hph, hr, hx0⟩ | ⟨hloop, hx0⟩
        · obtain rfl : C' = Function.update C id ((C id).setProcessVariables
              { (C id).processVariables with
                estimate := out.estimate, lastGrade := some out, phase := .toCallW }) :=
            roundLoopVariables_update hx0 (fun i hi => roundLoopStep_retG_notOwn (Ne.symm hi)
              (hall i))
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, out, PMF.pure X,
            PMF.pure (ABAState.setProcessVariables (C, A) id
              { ABAState.processes (C, A) id with
                estimate := out.estimate, lastGrade := some out, phase := .toCallW }),
            hstepG, Or.inl ⟨hph, hr, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)))
        · obtain rfl : C = C' := (roundLoopVariables_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_retG_notOwn (Ne.symm hi) (hall i)).symm
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, out, PMF.pure X, PMF.pure (C, A),
            hstepG, Or.inr ⟨hloop.imp_left (hcorr id).mp, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]⟩)))
      | boundG r b =>
        obtain ⟨-, hG'⟩ := gbcaSpecificationFamily_boundG_cases P hG
        obtain rfl : G = G' := (pure_inj hG').symm
        obtain rfl : C = C' :=
          (roundLoopVariables_id fun i => roundLoopStep_boundG (hall i)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_boundG hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_cases P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.boundG r b)) _).mp hW)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]))))))))
      | callW r id =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_callW hA)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_cases P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW r id)) _).mp hW)
        obtain ⟨-, hph, hr, hx0⟩ := roundLoopStep_callW_own (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProcessVariables { (C id).processVariables with phase := .awaitW }) :=
          roundLoopVariables_update hx0 (fun i hi => roundLoopStep_callW_notOwn (Ne.symm hi)
            (hall i))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, μw',
          PMF.pure (ABAState.setProcessVariables (C, A) id
            { ABAState.processes (C, A) id with phase := .awaitW }),
          hstepW, Or.inl ⟨hph, hr, rfl⟩, by rw [PMF.pure_bind]; rfl⟩))))
      | retW r id c =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_retW hA)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_cases P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW r id c)) _).mp hW)
        rcases roundLoopStep_retW_own (hall id) with ⟨-, hph, hr, hx0⟩ | ⟨hloop, hx0⟩
        · obtain rfl : C' = Function.update C id ((C id).stepRound c) :=
            roundLoopVariables_update hx0 (fun i hi => roundLoopStep_retW_notOwn (Ne.symm hi)
              (hall i))
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, c, μw',
            PMF.pure (ABAState.stepRound (C, A) id c), hstepW,
            Or.inl ⟨hph, hr, rfl⟩, ?_⟩)))))
          rw [PMF.pure_bind, ABAState.stepRound_apply C A id c]
        · obtain rfl : C = C' := (roundLoopVariables_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_retW_notOwn (Ne.symm hi) (hall i)).symm
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, c, μw',
            PMF.pure (C, A), hstepW, Or.inr ⟨hloop.imp_left (hcorr id).mp, rfl⟩,
            by rw [PMF.pure_bind]⟩)))))
  · rw [hybridHidden_step_iff] at hg
    rcases hg with ⟨-, e, hpre⟩ | hpre
    · -- a synchronisation label of the hidden alphabet
      obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
        hybridExtended_visible_cases P (by simp) hpre
      cases e with
      | gbcaRoundEvent r j ev => exact ev.elim
      | gbcaSend r j m => exact (abaNetworkStep_gbcaSend_noStep hA).elim
      | gbcaDeliver r i j m => exact (abaNetworkStep_gbcaDeliver_noStep hA).elim
      | decidedRelay j b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain rfl : A' = A.recordDecided j b := pure_inj (abaNetworkStep_decidedRelay hA)
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_decidedRelay j b) ω).mp hW
        rcases roundLoopStep_decidedRelay_self (hall j) with ⟨hh, hcnt, hnot, hx0⟩ | ⟨hh, hx0⟩
        · have hnF : j ∉ ABAState.F (C, A) := (corrupted_eq_false_iff hcorr j).mp hh
          obtain rfl : C' = Function.update C j ((C j).recordDecided b) :=
            roundLoopVariables_update hx0 (fun i hi => roundLoopStep_decidedRelay_notOwn
              (Ne.symm hi) (hall i))
          exact Or.inr (Or.inl ⟨PMF.pure (ABAState.relayDecided (C, A) j b),
            Or.inr (Or.inl ⟨j, b, hcnt, hrecorded j hnF ▸ hnot, rfl⟩), by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
        · obtain rfl : C = C' := (roundLoopVariables_id fun i => by
            by_cases hi : i = j
            · subst hi; exact hx0
            · exact roundLoopStep_decidedRelay_notOwn (Ne.symm hi) (hall i)).symm
          exact Or.inr (Or.inl ⟨PMF.pure (ABAState.recordDecided (C, A) j b),
            Or.inr (Or.inr ⟨j, b, (hcorr j).mp hh, rfl⟩), by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
      | decidedDeliver i j b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain ⟨hmem, hA'⟩ := abaNetworkStep_decidedDeliver hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_decidedDeliver i j b) ω).mp hW
        rcases roundLoopStep_decidedDeliver_self (hall i) with ⟨-, hnr, hx0⟩ | ⟨-, hx0⟩
        · obtain rfl : C' = Function.update C i ((C i).receiveDecided j b) :=
            roundLoopVariables_update hx0 (fun k hk => roundLoopStep_decidedDeliver_notOwn
              (Ne.symm hk) (hall k))
          exact Or.inr (Or.inl ⟨PMF.pure (ABAState.deliverDecided (C, A) i j b),
            Or.inl ⟨i, j, b, hmem, hnr, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
        · obtain rfl : C = C' := (roundLoopVariables_id fun k => by
            by_cases hk : k = i
            · subst hk; exact hx0
            · exact roundLoopStep_decidedDeliver_notOwn (Ne.symm hk) (hall k)).symm
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]))))))))
      | decidedSend j b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain ⟨hh, hph, hgA, hx0⟩ := roundLoopStep_decidedSend_self (hall j)
        obtain rfl : C' = Function.update C j (((C j).setProcessVariables
            { (C j).processVariables with lastGrade := none, phase := .toCallG }).recordDecided
              b) :=
          roundLoopVariables_update hx0 (fun k hk => roundLoopStep_decidedSend_notOwn (Ne.symm hk)
            (hall k))
        obtain rfl : A' = A.recordDecided j b := pure_inj (abaNetworkStep_decidedSend hA)
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_decidedSend j b) ω).mp hW
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, b,
          PMF.pure (ABAState.sendDecidedOnGrade2 (C, A) j b),
          ⟨(corrupted_eq_false_iff hcorr j).mp hh, hph, hgA, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩))))))
      | byzantineCallG r k b =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' :=
          (roundLoopVariables_id fun i => roundLoopStep_byzantineCallG (hall i)).symm
        obtain ⟨hF, hr, hA'⟩ := abaNetworkStep_byzantineCallG hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_byzantineCallG r k b) ω).mp hW
        have hA : A.recordStartedRound r k = A := by
          unfold ABANetworkState.recordStartedRound
          rw [if_neg (not_not_intro hF)]
        exact Or.inr (Or.inr (Or.inl ⟨r, k, b, PMF.pure X, PMF.pure (C, A),
          hstepG, Or.inr ⟨hF, hr, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure, hA]⟩))
      | byzantineCallW r k =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_cases P hG (by simp) rfl not_false)).symm
        obtain rfl : C = C' :=
          (roundLoopVariables_id fun i => roundLoopStep_byzantineCallW (hall i)).symm
        obtain ⟨hF, hr, hA'⟩ := abaNetworkStep_byzantineCallW hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_cases P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_byzantineCallW r k) ω).mp hW)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, μw',
          PMF.pure (C, A), hstepW, Or.inr ⟨hF, hr, rfl⟩, by rw [PMF.pure_bind]⟩))))
    · -- a silent transition of a component: the binding exclusion, the network's DECIDED
      -- injection or the coin's resolution
      rcases hybridExtended_tau_cases P hpre with ⟨G', hspec, rfl⟩ | ⟨A', hnet, rfl⟩ |
        ⟨r, -, μw, hstepW, rfl⟩
      · obtain ⟨r, -, X, hstepG, hGeq⟩ := gbcaSpecificationFamily_tau_cases P hspec
        obtain rfl : G' = G.setInstanceState r X := pure_inj hGeq
        exact Or.inl ⟨r, PMF.pure X, hstepG, by rw [PMF.pure_map, prodPMF_pure_pure]⟩
      · obtain ⟨k, b, hF, hA'⟩ := abaNetworkStep_tau hnet
        obtain rfl : A' = A.recordDecided k b := pure_inj hA'
        exact Or.inr (Or.inl ⟨PMF.pure (ABAState.recordDecided (C, A) k b),
          Or.inr (Or.inr ⟨k, b, hF, rfl⟩), by rw [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨r, μw, hstepW, rfl⟩)))))))

end ABA
end PLTS
