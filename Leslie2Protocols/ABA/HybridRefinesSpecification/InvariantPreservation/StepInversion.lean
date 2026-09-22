/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# Step inversion for `hybrid`

One lemma per visible label class (`callABA`, `retABA`, `fail`) and one for `τ`, each reading a
transition of the protocol-shaped specification back into the rows of its four components, in the
view's own coordinates: the pair `(C, A)` of the round loops beside the ABA network, read through
`ABAState`'s accessors. `hybrid_step_tau` is the six-way disjunction the τ case of the simulation
dispatches on; its τ has more sources than the visible labels do, the whole rendezvous alphabet
being hidden, and each of those sources collapses into one of the six. Three of the four lemmas
take the invariant's I0 conjunct as a hypothesis: a round loop's row is guarded by its own
replacement flag and the ABA network's row by the corrupted set, and I0 identifies the two, so that
the statement speaks of `F` alone (D23). `corrupted_eq_false_iff` is the one-line form of that
translation.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- The round loop's correctness guard read on the corrupted set: under I0 the
replacement flag is down exactly at the processes outside `F`. -/
theorem corrupted_eq_false_iff {P : Parameters} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n}
    (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (id : Fin P.n) : (C id).corrupted = false ↔ id ∉ ABAState.F (C, A) := by
  have h := hcorr id
  rw [ABAState.corrupted_apply] at h
  cases hb : (C id).corrupted <;> rw [hb] at h <;> simp_all

/-- `hybrid` inversion, `callABA`: the round specifications and the coin oracle idle on a label
outside their own API and the ABA network has no row of its own, so the whole transition is the
addressed round loop's — the genuine input of a never-corrupted process, guarded by `input = ⊥`, or
a self-loop, which is the input-enabledness row of a process whose program stands and holds an
input, and the replaced program's own row otherwise (D23, D36). -/
theorem hybrid_step_callABA (P : Parameters) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool)
    (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (μ : PMF (HybridState P)) :
    (hybrid P).step (G, C, A, o) (.callABA id b) μ ↔
      ∃ μc : PMF (ABAState P),
        ((id ∉ ABAState.F (C, A) ∧ (ABAState.processes (C, A) id).input = none ∧
            μc = PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with
                input := some b, estimate := some b, round := 0, phase := .toCallG })) ∨
          ((ABAState.corrupted (C, A) id = true ∨
              (ABAState.processes (C, A) id).input ≠ none) ∧
            μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o)) := by
  have hWlift : (coinOverRoundAlphabet P).step o (Sum.inl (Label.callABA id b)) (PMF.pure o) :=
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
          hybridExtended_visible_inversion P (by simp) hpre
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_callABA hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_inversion P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.callABA id b)) _).mp hW)
        rcases roundLoopStep_callABA_own (hall id) with ⟨hh, hin, hx0⟩ | ⟨hloop, hx0⟩
        · obtain rfl : C' = Function.update C id ((C id).setProcess { (C id).process with
              input := some b, estimate := some b, round := 0, phase := .toCallG }) :=
            roundLoopRecords_update hx0 (fun i hi => roundLoopStep_callABA_foreign (Ne.symm hi)
              (hall i))
          exact ⟨PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with
                input := some b, estimate := some b, round := 0, phase := .toCallG }),
            Or.inl ⟨(corrupted_eq_false_iff hcorr id).mp hh, hin, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩
        · obtain rfl : C = C' := (roundLoopRecords_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_callABA_foreign (Ne.symm hi) (hall i)).symm
          exact ⟨PMF.pure (C, A), Or.inr ⟨hloop, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩
  · rintro ⟨μc, hdisj, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridHidden_step_iff]
    refine Or.inr ?_
    rcases hdisj with ⟨hnF, hin, rfl⟩ | ⟨hloop, rfl⟩
    · have h := hybridExtended_visible_step P (L := Sum.inl (Label.callABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (roundLoopRecords_family id ((C id).setProcess { (C id).process with
            input := some b, estimate := some b, round := 0, phase := .toCallG })
          (RoundLoopStep.input (C id) b ((corrupted_eq_false_iff hcorr id).mpr hnF) hin)
          (fun i hi => RoundLoopStep.callABAIdle (C i) id b (Ne.symm hi)))
        (ABANetworkStep.callABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h
    · have h := hybridExtended_visible_step P (L := Sum.inl (Label.callABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (fun i => by
          by_cases hi : i = id
          · subst hi
            simp only [ABAState.corrupted_apply, ABAState.processes_apply] at hloop
            cases hb : (C i).corrupted
            · exact RoundLoopStep.inputLoop (C i) b hb
                (hloop.resolve_left (by rw [hb]; simp))
            · exact RoundLoopStep.corruptedIdle (C i) _ hb (by simp) (by simp [actsAt])
          · exact RoundLoopStep.callABAIdle (C i) id b (Ne.symm hi))
        (ABANetworkStep.callABAIdle A id b) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h

/-- `hybrid` inversion, `retABA`: a never-corrupted process's return has its
two guards split across two components — the `n − f` quorum is the round
loop's, having multicast `⟨DECIDED, b⟩` oneself is the network's — and they
rejoin on `ABAState`. A corrupted process returns any bit at any time and the
state does not move: the network's visible-return row asks for nothing beyond
`id ∈ F`, and the replaced program's half is its self-loop (D23). -/
theorem hybrid_step_retABA (P : Parameters) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o : ℕ → WCC.SpecState P.n) (id : Fin P.n) (b : Bool)
    (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (μ : PMF (HybridState P)) :
    (hybrid P).step (G, C, A, o) (.retABA id b) μ ↔
      ∃ μc : PMF (ABAState P),
        ((id ∉ ABAState.F (C, A) ∧
            P.n - P.f ≤ ABAState.decidedCount (C, A) id b ∧
            b ∈ ABAState.decidedSent (C, A) id ∧
            (ABAState.processes (C, A) id).returned = false ∧
            μc = PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with returned := true })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o)) := by
  have hWlift : (coinOverRoundAlphabet P).step o (Sum.inl (Label.retABA id b)) (PMF.pure o) :=
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
          hybridExtended_visible_inversion P (by simp) hpre
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain ⟨hsent, hA'⟩ := abaNetworkStep_retABA hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_inversion P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.retABA id b)) _).mp hW)
        rcases roundLoopStep_retABA_own (hall id) with ⟨hh, hcnt, hret, hx0⟩ | ⟨hh, hx0⟩
        · have hnF : id ∉ ABAState.F (C, A) := (corrupted_eq_false_iff hcorr id).mp hh
          obtain rfl : C' = Function.update C id
              ((C id).setProcess { (C id).process with returned := true }) :=
            roundLoopRecords_update hx0 (fun i hi => roundLoopStep_retABA_foreign (Ne.symm hi) (hall
              i))
          exact ⟨PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with returned := true }),
            Or.inl ⟨hnF, hcnt, hsent.resolve_right hnF, hret, rfl⟩, by
              simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩
        · obtain rfl : C = C' := (roundLoopRecords_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_retABA_foreign (Ne.symm hi) (hall i)).symm
          exact ⟨PMF.pure (C, A), Or.inr ⟨(hcorr id).mp hh, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩
  · rintro ⟨μc, hdisj, rfl⟩
    rw [hybrid_step_iff]
    refine Or.inr ⟨by simp, ?_⟩
    rw [hybridHidden_step_iff]
    refine Or.inr ?_
    rcases hdisj with ⟨hnF, hcnt, hsent, hret, rfl⟩ | ⟨hF, rfl⟩
    · have h := hybridExtended_visible_step P (L := Sum.inl (Label.retABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (roundLoopRecords_family id ((C id).setProcess { (C id).process with returned := true })
          (RoundLoopStep.ret (C id) b ((corrupted_eq_false_iff hcorr id).mpr hnF) hcnt hret)
          (fun i hi => RoundLoopStep.retABAIdle (C i) id b (Ne.symm hi)))
        (ABANetworkStep.retABA A id b hsent) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h
    · have h := hybridExtended_visible_step P (L := Sum.inl (Label.retABA id b)) (by simp)
        (gbcaSpecificationFamily_idle P G (by simp) rfl not_false)
        (fun i => by
          by_cases hi : i = id
          · subst hi
            exact RoundLoopStep.corruptedIdle (C i) _ ((hcorr i).mpr hF) (by simp)
              (by simp [actsAt])
          · exact RoundLoopStep.retABAIdle (C i) id b (Ne.symm hi))
        (ABANetworkStep.retByzantine A id b hF) hWlift
      simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
      exact h

/-- `hybrid` inversion, `fail`: a genuine synchronisation of all four components, under the two
guards the ABA network's row carries — the named process is not corrupted yet and the budget has
room. The round specifications and the coin oracle each corrupt their own copy of `F` and the ABA
network corrupts the view's; the named round loop replaces its own program by writing the flag
(D23), and every other round loop is unchanged (D1). -/
theorem hybrid_step_fail (P : Parameters) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n) (o : ℕ → WCC.SpecState P.n)
    (id : Fin P.n) (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (μ : PMF (HybridState P)) :
    (hybrid P).step (G, C, A, o) (.fail id) μ ↔
      id ∉ ABAState.F (C, A) ∧ (ABAState.F (C, A)).card < P.f ∧
      μ = prodPMF (PMF.pure fun r => (G r).corrupt P id)
        ((PMF.pure (ABAState.corrupt P id (C, A))).map
          fun c => (c.1, c.2, fun r => (o r).corrupt P id)) := by
  constructor
  · intro hstep
    rw [hybrid_step_iff] at hstep
    rcases hstep with ⟨habs, -⟩ | ⟨-, hg⟩
    · exact absurd habs (by simp)
    · rw [hybridHidden_step_iff] at hg
      rcases hg with ⟨habs, -⟩ | hpre
      · exact absurd habs (by simp)
      · obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_inversion P (by simp) hpre
        obtain rfl : G' = fun r => (G r).corrupt P id :=
          pure_inj (gbcaSpecificationFamily_fail_inversion P id hG)
        obtain ⟨hnew, hbud, hA'⟩ := abaNetworkStep_fail hA
        obtain rfl : A' = ABANetworkState.corrupt P id A := pure_inj hA'
        obtain rfl : ω = PMF.pure (fun r => (o r).corrupt P id) := wccFamily_fail_inversion P id
          ((System.mapIdle_step_some (coinLabelMap_inl (Label.fail id)) _).mp hW)
        have hh : (C id).corrupted = false := (corrupted_eq_false_iff hcorr id).mpr hnew
        obtain rfl : C' = Function.update C id { C id with corrupted := true } := by
          refine roundLoopRecords_update ?_ (fun i hi => roundLoopStep_fail_foreign (Ne.symm hi)
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
    have h := hybridExtended_visible_step P (L := Sum.inl (Label.fail id)) (by simp)
      (gbcaSpecificationFamily_fail P G id)
      (roundLoopRecords_family id { C id with corrupted := true }
        (RoundLoopStep.failSelf (C id) ((corrupted_eq_false_iff hcorr id).mpr hnew))
        (fun i hi => RoundLoopStep.failIdle (C i) id (Ne.symm hi)))
      (ABANetworkStep.fail A id hnew hbud)
      ((System.mapIdle_step_some (coinLabelMap_inl (Label.fail id)) _).mpr (wccFamily_fail P o id))
    simp only [PMF.pure_map, prodPMF_pure_pure] at h ⊢
    exact h

/-- `hybrid` inversion, `τ` (`mp`-only: preservation only needs the forward
direction). Six sources, and the whole rendezvous alphabet folds into them:
the specification family's binding exclusion, the view's own DECIDED messages
(delivery, echo, Byzantine injection), and the four handshakes — `callG`/`retG`
against a round specification, `callW`/`retW` against the coin oracle — each
reached either by the shared label under the sub-protocol hiding or by the
rendezvous that stands for it (`gbcaCallLoop`, the Byzantine handshake rows, and
the fused coin return `retWPublish`). The coin resolves inside the `callW`
handshake (D31), so the coin oracle's draw arrives under that handshake's
source. A replaced program contributes no source of its own: its self-loop on `callG`, `retG`,
`callW`, `retW` and `decidedSend` reads as the corrupted branch already present at those rows,
`id ∈ F` being supplied by I0 (D23). -/
theorem hybrid_step_tau (P : Parameters) (G : ℕ → GBCA.SpecState P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o : ℕ → WCC.SpecState P.n)
    (hcorr : ∀ k, ABAState.corrupted (C, A) k = true ↔ k ∈ ABAState.F (C, A))
    (μ : PMF (HybridState P))
    (hstep : (hybrid P).step (G, C, A, o) .tau μ) :
    (∃ r μr, GBCA.Step P r (G r) .tau μr ∧
        μ = prodPMF (μr.map (Function.update G r)) (PMF.pure (C, A, o))) ∨
      (∃ μc : PMF (ABAState P),
        ((∃ i j b, b ∈ ABAState.decidedSent (C, A) j ∧
              b ∉ ABAState.decidedReceived (C, A) i j ∧
              μc = PMF.pure (ABAState.deliverDecided (C, A) i j b)) ∨
          (∃ k b, P.f + 1 ≤ ABAState.decidedCount (C, A) k b ∧
              b ∉ ABAState.decidedSent (C, A) k ∧
              μc = PMF.pure (ABAState.sendDecided (C, A) k b)) ∨
          (∃ k b, k ∈ ABAState.F (C, A) ∧
              μc = PMF.pure (ABAState.sendDecided (C, A) k b))) ∧
        μ = prodPMF (PMF.pure G) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (b : Bool) (μr : PMF (GBCA.SpecState P.n))
          (μc : PMF (ABAState P)), GBCA.Step P r (G r) (.callG r id b) μr ∧
        (((ABAState.processes (C, A) id).phase = .toCallG ∧
            (ABAState.processes (C, A) id).round = r ∧
            (ABAState.processes (C, A) id).estimate = some b ∧
            μc = PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with phase := .awaitG })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (μr.map (Function.update G r)) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
          (μr : PMF (GBCA.SpecState P.n))
          (μc : PMF (ABAState P)), GBCA.Step P r (G r) (.retG r id out bnd) μr ∧
        (((ABAState.processes (C, A) id).phase = .awaitG ∧
            (ABAState.processes (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with
                estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (μr.map (Function.update G r)) (μc.map fun c => (c.1, c.2, o))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (μw' : PMF (WCC.SpecState P.n))
          (μc : PMF (ABAState P)), WCC.Step P r (o r) (.callW r id) μw' ∧
        (((ABAState.processes (C, A) id).phase = .toCallW ∧
            (ABAState.processes (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with phase := .awaitW })) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.bind fun c => prodPMF (PMF.pure c.1)
              (prodPMF (PMF.pure c.2) (μw'.map (Function.update o r))))) ∨
      (∃ (r : ℕ) (id : Fin P.n) (b : Bool) (μw' : PMF (WCC.SpecState P.n))
          (μc : PMF (ABAState P)), WCC.Step P r (o r) (.retW r id b) μw' ∧
        (((ABAState.processes (C, A) id).phase = .awaitW ∧
            (ABAState.processes (C, A) id).round = r ∧
            μc = PMF.pure (ABAState.stepRound (C, A) id b)) ∨
          (id ∈ ABAState.F (C, A) ∧ μc = PMF.pure (C, A))) ∧
        μ = prodPMF (PMF.pure G) (μc.bind fun c => prodPMF (PMF.pure c.1)
              (prodPMF (PMF.pure c.2) (μw'.map (Function.update o r))))) := by
  rw [hybrid_step_iff] at hstep
  rcases hstep with ⟨-, l', hl', hg⟩ | ⟨-, hg⟩
  · rw [hybridHidden_step_iff] at hg
    rcases hg with ⟨rfl, e, hpre⟩ | hpre
    · exact absurd hl' (by simp)
    · -- a sub-protocol API label, sent to `τ` by the outer hiding
      cases l' with
      | tau => exact absurd hl' (by simp)
      | callABA id b => exact absurd hl' (by simp)
      | retABA id b => exact absurd hl' (by simp)
      | fail k => exact absurd hl' (by simp)
      | callG r id b =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_inversion P (by simp) hpre
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_callG hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_inversion P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.callG r id b)) _).mp hW)
        obtain ⟨-, hph, hr, hest, hx0⟩ := roundLoopStep_callG_own (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProcess { (C id).process with phase := .awaitG }) :=
          roundLoopRecords_update hx0 (fun i hi => roundLoopStep_callG_foreign (Ne.symm hi) (hall
            i))
        exact Or.inr (Or.inr (Or.inl ⟨r, id, b, PMF.pure X,
          PMF.pure (ABAState.setProcess (C, A) id
            { ABAState.processes (C, A) id with phase := .awaitG }),
          hstepG, Or.inl ⟨hph, hr, hest, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩))
      | retG r id out bnd =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_inversion P (by simp) hpre
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_retG hA)).symm
        obtain rfl : ω = PMF.pure o :=
          wccFamily_idle_inversion P (by simp) rfl (by simp [Label.isFail])
            ((System.mapIdle_step_some (coinLabelMap_inl (Label.retG r id out bnd)) _).mp hW)
        obtain ⟨-, hph, hr, hx0⟩ := roundLoopStep_retG_own (hall id)
        obtain rfl : C' = Function.update C id ((C id).setProcess
            { (C id).process with
              estimate := out.estimate, lastGrade := some out,
              phase := .toCallW }) :=
          roundLoopRecords_update hx0 (fun i hi => roundLoopStep_retG_foreign (Ne.symm hi) (hall i))
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, out, bnd, PMF.pure X,
          PMF.pure (ABAState.setProcess (C, A) id
            { ABAState.processes (C, A) id with
              estimate := out.estimate, lastGrade := some out, phase := .toCallW }),
          hstepG, Or.inl ⟨hph, hr, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)))
      | callW r id =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_inversion P (by simp) hpre
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_callW hA)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inversion P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW r id)) _).mp hW)
        rcases roundLoopStep_callW_own (hall id) with ⟨-, hph, hr, hx0⟩ | ⟨hh, hx0⟩
        · obtain rfl : C' = Function.update C id
              ((C id).setProcess { (C id).process with phase := .awaitW }) :=
            roundLoopRecords_update hx0 (fun i hi => roundLoopStep_callW_foreign (Ne.symm hi) (hall
              i))
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, μw',
            PMF.pure (ABAState.setProcess (C, A) id
              { ABAState.processes (C, A) id with phase := .awaitW }),
            hstepW, Or.inl ⟨hph, hr, rfl⟩, by rw [PMF.pure_bind]; rfl⟩))))
        · obtain rfl : C = C' := (roundLoopRecords_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_callW_foreign (Ne.symm hi) (hall i)).symm
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, id, μw',
            PMF.pure (C, A), hstepW, Or.inr ⟨(hcorr id).mp hh, rfl⟩,
            by rw [PMF.pure_bind]⟩))))
      | retW r id c =>
        obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
          hybridExtended_visible_inversion P (by simp) hpre
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_retW hA)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inversion P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW r id c)) _).mp hW)
        rcases roundLoopStep_retW_own (hall id) with ⟨-, hph, hr, hgr, hx0⟩ | ⟨hh, hx0⟩
        · obtain rfl : C' = Function.update C id ((C id).stepRound c) :=
            roundLoopRecords_update hx0 (fun i hi => roundLoopStep_retW_foreign (Ne.symm hi) (hall
              i))
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, id, c, μw',
            PMF.pure (ABAState.stepRound (C, A) id c), hstepW,
            Or.inl ⟨hph, hr, rfl⟩, ?_⟩))))
          rw [PMF.pure_bind, ABAState.stepRound_of_not_grade2 C A id c hgr]
        · obtain rfl : C = C' := (roundLoopRecords_id fun i => by
            by_cases hi : i = id
            · subst hi; exact hx0
            · exact roundLoopStep_retW_foreign (Ne.symm hi) (hall i)).symm
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, id, c, μw',
            PMF.pure (C, A), hstepW, Or.inr ⟨(hcorr id).mp hh, rfl⟩,
            by rw [PMF.pure_bind]⟩))))
  · rw [hybridHidden_step_iff] at hg
    rcases hg with ⟨-, e, hpre⟩ | hpre
    · -- a rendezvous of the hidden alphabet
      obtain ⟨G', C', A', ω, hG, hall, hA, hW, rfl⟩ :=
        hybridExtended_visible_inversion P (by simp) hpre
      cases e with
      | gbcaSend r j m => exact (abaNetworkStep_gbcaSend_noStep hA).elim
      | gbcaDeliver r i j m => exact (abaNetworkStep_gbcaDeliver_noStep hA).elim
      | decidedSend j b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        have hx0 : (PMF.pure (C' j) : PMF (RoundLoopRecord P.n)) = PMF.pure (C j) := by
          rcases roundLoopStep_decidedSend_self (hall j) with ⟨-, -, h⟩ | ⟨-, h⟩ <;> exact h
        obtain rfl : C = C' := (roundLoopRecords_id fun i => by
          by_cases hi : i = j
          · subst hi; exact hx0
          · exact roundLoopStep_decidedSend_foreign (Ne.symm hi) (hall i)).symm
        obtain ⟨hsent, hA'⟩ := abaNetworkStep_decidedSend hA
        obtain rfl : A' = A.recordDecided j b := pure_inj hA'
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_decidedSend j b) ω).mp hW
        refine Or.inr (Or.inl ⟨PMF.pure (ABAState.sendDecided (C, A) j b), ?_, by
          simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
        rcases roundLoopStep_decidedSend_self (hall j) with ⟨-, hcnt, -⟩ | ⟨hh, -⟩
        · exact Or.inr (Or.inl ⟨j, b, hcnt, hsent, rfl⟩)
        · exact Or.inr (Or.inr ⟨j, b, (hcorr j).mp hh, rfl⟩)
      | decidedDeliver i j b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain ⟨-, hnr, hx0⟩ := roundLoopStep_decidedDeliver_self (hall i)
        obtain rfl : C' = Function.update C i ((C i).receiveDecided j b) :=
          roundLoopRecords_update hx0 (fun k hk => roundLoopStep_decidedDeliver_foreign (Ne.symm hk)
            (hall k))
        obtain ⟨hmem, hA'⟩ := abaNetworkStep_decidedDeliver hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_decidedDeliver i j b) ω).mp hW
        exact Or.inr (Or.inl ⟨PMF.pure (ABAState.deliverDecided (C, A) i j b),
          Or.inl ⟨i, j, b, hmem, hnr, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)
      | retWPublish r id c b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inversion P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_retWPublish r id c b) ω).mp hW)
        obtain ⟨-, hph, hr, hgA, hx0⟩ := roundLoopStep_retWPublish_self (hall id)
        obtain rfl : C' = Function.update C id ((C id).stepRound c) :=
          roundLoopRecords_update hx0 (fun k hk => roundLoopStep_retWPublish_foreign (Ne.symm hk)
            (hall k))
        obtain rfl : A' = A.recordDecided id b := pure_inj (abaNetworkStep_retWPublish hA)
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, id, c, μw',
          PMF.pure (ABAState.stepRound (C, A) id c), hstepW,
          Or.inl ⟨hph, hr, rfl⟩, ?_⟩))))
        rw [PMF.pure_bind, ABAState.stepRound_publish C A id c b hgA]
      | gbcaCallLoop r id b =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain ⟨-, hph, hr, hest, hx0⟩ := roundLoopStep_gbcaCallLoop_self (hall id)
        obtain rfl : C' = Function.update C id
            ((C id).setProcess { (C id).process with phase := .awaitG }) :=
          roundLoopRecords_update hx0 (fun k hk => roundLoopStep_gbcaCallLoop_foreign (Ne.symm hk)
            (hall k))
        obtain rfl : A = A' := (pure_inj (abaNetworkStep_gbcaCallLoop hA)).symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_gbcaCallLoop r id b) ω).mp hW
        exact Or.inr (Or.inr (Or.inl ⟨r, id, b, PMF.pure X,
          PMF.pure (ABAState.setProcess (C, A) id
            { ABAState.processes (C, A) id with phase := .awaitG }),
          hstepG, Or.inl ⟨hph, hr, hest, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]; rfl⟩))
      | byzantineCallG r k b =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' := (roundLoopRecords_id fun i => roundLoopStep_byzantineCallG (hall
          i)).symm
        obtain ⟨hF, hA'⟩ := abaNetworkStep_byzantineCallG hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_byzantineCallG r k b) ω).mp hW
        exact Or.inr (Or.inr (Or.inl ⟨r, k, b, PMF.pure X, PMF.pure (C, A),
          hstepG, Or.inr ⟨hF, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩))
      | byzantineCallGLoop r k b =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' := (roundLoopRecords_id fun i => roundLoopStep_byzantineCallGLoop (hall
          i)).symm
        obtain ⟨hF, hA'⟩ := abaNetworkStep_byzantineCallGLoop hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_byzantineCallGLoop r k b) ω).mp hW
        exact Or.inr (Or.inr (Or.inl ⟨r, k, b, PMF.pure X, PMF.pure (C, A),
          hstepG, Or.inr ⟨hF, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩))
      | byzantineRetG r k out bnd =>
        obtain ⟨X, hstepG, rfl⟩ := gbcaSpecificationFamily_owned_step P rfl (by simp) rfl hG
        obtain rfl : C = C' := (roundLoopRecords_id fun i => roundLoopStep_byzantineRetG (hall
          i)).symm
        obtain ⟨hF, hA'⟩ := abaNetworkStep_byzantineRetG hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain rfl : ω = PMF.pure o :=
          (System.mapIdle_step_none (coinLabelMap_byzantineRetG r k out bnd) ω).mp hW
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, out, bnd, PMF.pure X,
          PMF.pure (C, A), hstepG, Or.inr ⟨hF, rfl⟩, by
            simp only [PMF.pure_map, prodPMF_pure_pure]⟩)))
      | byzantineCallW r k =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain rfl : C = C' := (roundLoopRecords_id fun i => roundLoopStep_byzantineCallW (hall
          i)).symm
        obtain ⟨hF, hA'⟩ := abaNetworkStep_byzantineCallW hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inversion P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_byzantineCallW r k) ω).mp hW)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, μw',
          PMF.pure (C, A), hstepW, Or.inr ⟨hF, rfl⟩, by rw [PMF.pure_bind]⟩))))
      | byzantineRetW r k b =>
        obtain rfl : G = G' :=
          (pure_inj (gbcaSpecificationFamily_idle_inversion P hG (by simp) rfl not_false)).symm
        obtain rfl : C = C' := (roundLoopRecords_id fun i => roundLoopStep_byzantineRetW (hall
          i)).symm
        obtain ⟨hF, hA'⟩ := abaNetworkStep_byzantineRetW hA
        obtain rfl : A = A' := (pure_inj hA').symm
        obtain ⟨μw', hstepW, rfl⟩ := wccFamily_owned_inversion P (by simp) rfl
          ((System.mapIdle_step_some (coinLabelMap_byzantineRetW r k b) ω).mp hW)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, k, b, μw',
          PMF.pure (C, A), hstepW, Or.inr ⟨hF, rfl⟩, by rw [PMF.pure_bind]⟩))))
    · -- genuine `τ`: the binding exclusion or the network's Byzantine injection
      rcases hybridExtended_tau_inversion P hpre with ⟨G', hspec, rfl⟩ | ⟨A', hnet, rfl⟩
      · obtain ⟨r, X, hstepG, hGeq⟩ := gbcaSpecificationFamily_tau_inversion P hspec
        obtain rfl : G' = Function.update G r X := pure_inj hGeq
        rw [GBCA.ByABDY.specificationOverRoundAlphabet,
          System.mapIdle_step_some (GBCA.ByABDY.gbcaLabelMap_inl (Label.tau : Label P.n))] at hstepG
        exact Or.inl ⟨r, PMF.pure X, hstepG, by rw [PMF.pure_map, prodPMF_pure_pure]⟩
      · obtain ⟨k, b, hF, hA'⟩ := abaNetworkStep_tau hnet
        obtain rfl : A' = A.recordDecided k b := pure_inj hA'
        exact Or.inr (Or.inl ⟨PMF.pure (ABAState.sendDecided (C, A) k b),
          Or.inr (Or.inr ⟨k, b, hF, rfl⟩), by rw [PMF.pure_map, prodPMF_pure_pure]; rfl⟩)

end ABA
end PLTS
