/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# The core-simulation invariant: step inversion and preservation

Stages A and B of the proof that `hybridSpecificationStateRelation` is a simulation relation
(`DESIGN-HybridRefinesSpecification.md`), on top of the relation and invariant of
`HybridRefinesSpecification/Relation.lean`.

* **Stage A** — step inversion for `hybrid`: one lemma per visible label class (`callABA`, `retABA`,
  `fail`) and one for `τ`, each reading a composite transition back into the component rows that
  produced it. `hybrid_step_tau` is the six-way disjunction the τ case of the simulation dispatches
  on; its τ has more sources than the visible labels do, the whole rendezvous alphabet being hidden,
  and each of those sources collapses into one of the six.
* **Stage B** — preservation of `Invariant`: one `Invariant.step_*` lemma per row of Stage
  A's inversion, each carrying all forty invariant fields across that
  row.

The assembly of the two into `Invariant.step` is in
`HybridRefinesSpecification/AbstractStatePreservation.lean`, beside the `AbstractState` stutter
lemmas it is stated with. -/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-! ### Stage A: step inversion for `hybrid`

Each lemma reads a transition of the protocol-shaped specification back into the rows of its four
components, delivering the ABA content in the view's own coordinates: the pair `(C, A)` of the round
loops beside the ABA network, read through `ABAState`'s accessors.

Three of the four take the invariant's I0 conjunct as a hypothesis. The correctness guard a round
loop's row carries reads its own replacement flag, and the guard the ABA network's row carries reads
the corrupted set; I0 is what identifies the two, so that the statement speaks of `F` alone
(D23). -/

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

/-! ### Stage B: preservation of `Invariant` -/

/-- WCC corruption changes only `F`. -/
theorem WCC.corrupt_val {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold WCC.SpecState.corrupt; split <;> rfl

theorem WCC.corrupt_called {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n) :
    (s.corrupt P id).called = s.called := by unfold WCC.SpecState.corrupt; split <;> rfl

/-- The GBCA corruption of a state agreeing with the core on `F` agrees with the core's corruption
on `F` (keeps `F_gbca` together across a `fail` broadcast). -/
theorem GBCA.corrupt_F_eq {P : Parameters} (id : Fin P.n) (s : GBCA.SpecState P.n)
    (c : ABAState P) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold GBCA.SpecState.corrupt
  rw [ABAState.corrupt_F, h]; split_ifs <;> simp [h]

/-- The WCC corruption of a state agreeing with the core on `F` agrees with the core's corruption on
`F` (keeps `F_wcc` together across a `fail` broadcast). -/
theorem WCC.corrupt_F_eq {P : Parameters} (id : Fin P.n) (s : WCC.SpecState P.n)
    (c : ABAState P) (h : s.F = c.F) :
    (s.corrupt P id).F = (c.corrupt P id).F := by
  unfold WCC.SpecState.corrupt
  rw [ABAState.corrupt_F, h]; split_ifs <;> simp [h]

/-- `retABA`: a never-corrupted process's return only sets `returned`, a field `Invariant` never
inspects, so `Invariant` transfers verbatim modulo the pointwise-unchanged projections of
`processes`. A corrupted process's return is a state identity, and `Invariant` transfers outright.
-/
theorem Invariant.step_retABA {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (ABAState P)}
    (hstep : (id ∉ c.F ∧ P.n - P.f ≤ c.decidedCount id b ∧ b ∈ c.decidedSent id ∧
        (c.processes id).returned = false ∧
        μc = PMF.pure (c.setProcess id { c.processes id with returned := true })) ∨
      (id ∈ c.F ∧ μc = PMF.pure c))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' w ∧ AbstractStateUnchanged P g g c c' := by
  rcases hstep with hstep | ⟨-, rfl⟩
  · obtain ⟨-, -, -, -, rfl⟩ := hstep
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    set c' := c.setProcess id { c.processes id with returned := true } with hc'def
    have hF : c'.F = c.F := ABAState.setProcess_F _ _ _
    have hCorr : c'.corrupted = c.corrupted := ABAState.setProcess_corrupted _ _ _
    have hDS : c'.decidedSent = c.decidedSent := ABAState.setProcess_decidedSent _ _ _
    have hDR : c'.decidedReceived = c.decidedReceived := ABAState.setProcess_decidedReceived _ _ _
    have hDC : ∀ i b', c'.decidedCount i b' = c.decidedCount i b' :=
      fun i b' => ABAState.setProcess_decidedCount _ _ _ _ _
    have hInput : ∀ id', (c'.processes id').input = (c.processes id').input := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hEst : ∀ id', (c'.processes id').estimate = (c.processes id').estimate := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hRound : ∀ id', (c'.processes id').round = (c.processes id').round := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hPhase : ∀ id', (c'.processes id').phase = (c.processes id').phase := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hLastGrade : ∀ id', (c'.processes id').lastGrade = (c.processes id').lastGrade := by
      intro id'; by_cases h : id' = id
      · subst h; rw [hc'def, ABAState.setProcess_processes_self]
      · rw [hc'def, ABAState.setProcess_processes_ne _ _ _ h]
    have hCarr : ∀ r' id' v, OutcomeHolder P g c' r' id' v → OutcomeHolder P g c r' id' v := by
      intro r' id' v hc
      unfold OutcomeHolder at hc ⊢
      rwa [hEst, hRound, hPhase] at hc
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g c' r' b' := fun r' b' =>
        Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hF] : c.F ⊆ c'.F) hRound hEst (fun id0 v => hCarr r' id0 v)
    have hHold : ∀ id' b', Grade2Holder P c' id' b' → Grade2Holder P c id' b' := by
      intro id' b' h
      unfold Grade2Holder at h ⊢
      rwa [hLastGrade, hDS] at h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
    refine ⟨fun id' => by rw [hCorr, hF]; exact hI.corrupted_F id',
      fun r => (hI.F_gbca r).trans hF.symm, fun r => ?_, ?_, ?_, ?_, ?_,
      hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hInput]; exact h) (fun x hx => by rw [hF]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i j v v' hm hm' h h' => hI.outcomeHolder_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
        (hCarr _ _ _ h) (hCarr _ _ _ h'),
      fun i j b₀ b₀' hm hm' h h' => hI.grade2Lock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
        (hHold _ _ h) (hHold _ _ h')⟩
    · rw [hF]; exact hI.F_wcc r
    · rw [hF]; exact hI.F_card
    · intro id' b' hmem hcall; rw [hInput]; exact hI.input_gbcaRound0 id' b' (hF ▸ hmem) hcall
    · intro r id' hmem hcall; rw [hInput]; exact hI.input_called r id' (hF ▸ hmem) hcall
    · intro id' hmem hne; rw [hPhase] at hne; rw [hInput]; exact hI.phase_input id' (hF ▸ hmem) hne
    · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.received_sound i j b' h
    · intro id' b' hmem h; rw [hDS] at h
      exact (hI.decided_source id' b' (hF ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hg hb
      exact Grade2Commitment.of_unchanged (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hF]) hRound hEst (fun id0 v => hCarr r id0 v) (hI.grade2Lock_commit r b' hg hb)
    · intro id' hmem r hr; exact hI.round_bound id' (hF ▸ hmem) r (hRound id' ▸ hr)
    · intro r v hlast hb hcoin id' hmem hr
      rw [hEst]; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) (hRound id' ▸ hr)
    · intro r id' hmem hcall; rw [hRound]; exact hI.call_round r id' (hF ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hF ▸ hmem) hcalled
    · intro r id' hmem hr; rw [hRound] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
    · intro id' hmem hround hphase
      rw [hRound] at hround; rw [hPhase] at hphase
      rw [hEst, hInput]; exact hI.estimate0 id' (hF ▸ hmem) hround hphase
    · intro id' b' hlg; rw [hLastGrade] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hRound] at hround; rw [hPhase] at hphase
      rw [hEst]; exact hI.estimate_ret r id' (hF ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hF ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst] at hest
      exact hI.estimate_previous r id' (hF ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hRound] at hround; rw [hPhase] at hphase; rw [hEst]
      exact hI.estimate_previous_ne id' (hF ▸ hmem) hround hphase
    · intro id' b' h
      rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
      · left; rw [hInput]; exact hin
      · right; rw [hF]; exact hf
    · intro r id' hmem hcalled; rw [hRound]; exact hI.wcc_callRound r id' (hF ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun hh => hh) (fun id' => hInput id') hd
    · intro id' hmem hin r'; rw [hInput] at hin; exact hI.idle_no_wccCall id' (hF ▸ hmem) hin r'
    · intro r id' hmem h
      rw [hRound] at h; rw [hPhase] at h
      rcases hI.retG_witness r id' (hF ▸ hmem) h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun hh => hh) (fun id'' => hInput id'') hd
  · rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact ⟨hI, AbstractStateUnchanged.refl P g _⟩

/-- `callABA`: either a never-corrupted process's genuine external input (guarded by
`input = none`, so `input_called` rules out the "already called GBCA" corner) or the idle
self-loop. -/
theorem Invariant.step_callABA {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n) (b : Bool)
    {μc : PMF (ABAState P)}
    (hstep :
      (id ∉ c.F ∧ (c.processes id).input = none ∧
          μc = PMF.pure (c.setProcess id { c.processes id with
            input := some b, estimate := some b, round := 0, phase := .toCallG })) ∨
        ((c.corrupted id = true ∨ (c.processes id).input ≠ none) ∧ μc = PMF.pure c))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' w ∧ AbstractStateUnchanged P g g c c' := by
  rcases hstep with ⟨-, hin, rfl⟩ | ⟨-, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    set c' := c.setProcess id { c.processes id with
      input := some b, estimate := some b, round := 0, phase := .toCallG } with hc'def
    have hF : c'.F = c.F := ABAState.setProcess_F _ _ _
    have hCorr : c'.corrupted = c.corrupted := ABAState.setProcess_corrupted _ _ _
    have hDS : c'.decidedSent = c.decidedSent := ABAState.setProcess_decidedSent _ _ _
    have hDR : c'.decidedReceived = c.decidedReceived := ABAState.setProcess_decidedReceived _ _ _
    have hSelf : c'.processes id = { c.processes id with
        input := some b, estimate := some b, round := 0, phase := .toCallG } := by
      rw [hc'def]; exact ABAState.setProcess_processes_self _ _ _
    have hNe : ∀ id', id' ≠ id → c'.processes id' = c.processes id' := by
      intro id' h; rw [hc'def]; exact ABAState.setProcess_processes_ne _ _ _ h
    have hDissTrans : ∀ r, DissentWitness P g c r → DissentWitness P g c' r := by
      intro r hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hbv, ?_⟩
      by_cases h0 : r = 0
      · rw [if_pos h0] at hif ⊢
        obtain ⟨id', hid'⟩ := hif
        by_cases hidmatch : id' = id
        · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
        · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
      · rw [if_neg h0] at hif ⊢; exact hif
    have hInMono : ∀ id' b',
      (c.processes id').input = some b' → (c'.processes id').input = some b' := by
      intro id' b' h
      by_cases hid : id' = id
      · exact absurd (hid ▸ h) (by rw [hin]; simp)
      · rw [hNe id' hid]; exact h
    have hCarrTrans : ∀ r' id₀ v, OutcomeHolder P g c' r' id₀ v → OutcomeHolder P g c r' id₀ v := by
      intro r' id₀ v hc
      rcases hc with h | ⟨he, hk⟩
      · exact Or.inl h
      · by_cases hid : id₀ = id
        · subst hid; exfalso; simp [hSelf] at hk
        · rw [hNe id₀ hid] at he hk
          exact Or.inr ⟨he, hk⟩
    have hCertTrans : ∀ r' b', Grade2Certificate P g c r' b' → Grade2Certificate P g c' r' b' := by
      rintro r' b' ⟨hg1, hd1, h1, h2, h3, h4⟩
      refine ⟨hg1, hd1, h1,
        fun r'' id'' b'' hrr hmem hcall => h2 r'' id'' b'' hrr (hF ▸ hmem) hcall,
        fun id'' hmem hr => ?_,
        fun id'' v hmem hcar => h4 id'' v (hF ▸ hmem) (hCarrTrans r' id'' v hcar)⟩
      by_cases h : id'' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id'' h] at hr ⊢; exact h3 id'' (hF ▸ hmem) hr
    have hLG : ∀ id₀, (c'.processes id₀).lastGrade = (c.processes id₀).lastGrade := by
      intro id₀; by_cases h : id₀ = id
      · subst h; simp [hSelf]
      · rw [hNe id₀ h]
    have hHold : ∀ id₀ b₀, Grade2Holder P c' id₀ b₀ → Grade2Holder P c id₀ b₀ := by
      intro id₀ b₀ h
      unfold Grade2Holder at h ⊢
      rwa [hLG, hDS] at h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hF ▸ hj) (hHold j b' hh)⟩
    refine ⟨fun id' => by rw [hCorr, hF]; exact hI.corrupted_F id',
      fun r => (hI.F_gbca r).trans hF.symm, fun r => hF ▸ hI.F_wcc r, hF ▸ hI.F_card,
      ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono hInMono (fun x hx => by rw [hF]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i j v v' hm hm' h h' => hI.outcomeHolder_agree r' i j v v' (hF ▸ hm) (hF ▸ hm')
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h'),
      fun i j b₀ b₀' hm hm' h h' => hI.grade2Lock_agree i j b₀ b₀' (hF ▸ hm) (hF ▸ hm')
        (hHold _ _ h) (hHold _ _ h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem
        have hne : (g 0).call id ≠ none := by
          rw [hcall]; simp
        exact absurd hin (hI.input_called 0 id (hF ▸ hmem) hne)
      · rw [hNe id' h]; exact hI.input_gbcaRound0 id' b' (hF ▸ hmem) hcall
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h]; exact hI.input_called r id' (hF ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h]; simp [hSelf]
      · rw [hNe id' h] at hne ⊢; exact hI.phase_input id' (hF ▸ hmem) hne
    · intro i j b' h; rw [hDR] at h; rw [hDS]; exact hI.received_sound i j b' h
    · intro id' b' hmem h; rw [hDS] at h
      exact (hI.decided_source id' b' (hF ▸ hmem) h).imp (fun r => hCertTrans r b')
    · intro r b' hg hb
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hg hb
      refine ⟨h1, h2, fun id' hmem hr => ?_,
        fun id0 v hmem hcar => h4 id0 v (hF ▸ hmem) (hCarrTrans r id0 v hcar)⟩
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact h3 id' (hF ▸ hmem) hr
    · intro id' hmem r hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_bound id' (hF ▸ hmem) r hr
    · intro r v hlast hb hcoin id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr ⊢; exact hI.agree_locked r v hlast hb hcoin id' (hF ▸ hmem) hr
    · intro r id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hcall hmem; exact absurd hin (hI.input_called r id (hF ▸ hmem) hcall)
      · rw [hNe id' h]; exact hI.call_round r id' (hF ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hF ▸ hmem) hcalled
    · intro r id' hmem hr
      by_cases h : id' = id
      · subst h; simp [hSelf] at hr
      · rw [hNe id' h] at hr; exact hI.round_flip r id' (hF ▸ hmem) hr
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf]
      · rw [hNe id' h] at hround hphase ⊢; exact hI.estimate0 id' (hF ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · rw [h] at hlg; rw [hSelf] at hlg
        exact (hI.grade2_source id b' hlg).imp (fun r => hCertTrans r b')
      · rw [hNe id' h] at hlg
        exact (hI.grade2_source id' b' hlg).imp (fun r => hCertTrans r b')
    · intro r id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hphase
      · rw [hNe id' h] at hround hphase ⊢; exact hI.estimate_ret r id' (hF ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hF ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase hest
        exact hI.estimate_previous r id' (hF ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · subst h; simp [hSelf] at hround
      · rw [hNe id' h] at hround hphase ⊢
        exact hI.estimate_previous_ne id' (hF ▸ hmem) hround hphase
    · intro id' b' h
      rcases hI.input_gbcaRound0_permanent id' b' h with hpre | hf
      · by_cases hid : id' = id
        · rw [hid, hin] at hpre; exact absurd hpre (by simp)
        · left; rw [hNe id' hid]; exact hpre
      · right; rw [hF]; exact hf
    · -- `wcc_callRound`'s `id' = id` corner: `id` was just idle (`hin`), so `idle_no_wccCall`
      -- rules out `id` having ever called any `WCC` instance.
      intro r id' hmem hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem hcalled
        have := hI.idle_no_wccCall id (hF ▸ hmem) hin r
        rw [this] at hcalled
        exact absurd hcalled (by simp)
      · rw [hNe id' hid]; exact hI.wcc_callRound r id' (hF ▸ hmem) hcalled
    · -- `flip_grade2Lock`: `g` is untouched entirely; the only wrinkle is the `r = 0` dissent
      -- witness possibly naming `id` itself, ruled out by `hin : input = none` (the fresh
      -- the input of a correct process cannot have been the opposing dissenter).
      intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right
        obtain ⟨v, hbv, hif⟩ := hd
        refine ⟨v, hbv, ?_⟩
        by_cases h0 : r = 0
        · rw [if_pos h0] at hif ⊢
          obtain ⟨id', hid'⟩ := hif
          by_cases hidmatch : id' = id
          · exfalso; rw [hidmatch, hin] at hid'; exact absurd hid' (by simp)
          · exact ⟨id', by rw [hNe id' hidmatch]; exact hid'⟩
        · rw [if_neg h0] at hif ⊢; exact hif
    · intro id' hmem hin' r'
      by_cases h : id' = id
      · subst h; simp [hSelf] at hin'
      · rw [hNe id' h] at hin'; exact hI.idle_no_wccCall id' (hF ▸ hmem) hin' r'
    · intro r id' hmem hp
      by_cases h : id' = id
      · subst h; simp [hSelf] at hp
      · rw [hNe id' h] at hp
        rcases hI.retG_witness r id' (hF ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDissTrans r hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDissTrans r hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    exact ⟨hI, AbstractStateUnchanged.refl P g _⟩

/-- `fail`: a genuine synchronised corruption of all three components, under the row's own guards —
the named process is not corrupted yet and the budget has room. `F` only grows, and every other
projection is untouched, so correctness hypotheses transfer via `F`-monotonicity. The two guards are
what puts the replacement flag and the corrupted set together (I0, D23): the flag goes up at `id`
and `F` gains exactly `id`. -/
theorem Invariant.step_fail {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (id : Fin P.n)
    (hnew : id ∉ c.F) (hbud : c.F.card < P.f) :
    Invariant P (fun r => (g r).corrupt P id) (c.corrupt P id) (fun r => (w r).corrupt P id) ∧
      AbstractStateUnchanged P g (fun r => (g r).corrupt P id) c (c.corrupt P id) := by
  set g' := fun r => (g r).corrupt P id with hg'def
  set c' := c.corrupt P id with hc'def
  set w' := fun r => (w r).corrupt P id with hw'def
  have hcall : ∀ r, (g' r).call = (g r).call := fun r => GBCA.corrupt_call P (g r) id
  have hbind : ∀ r, (g' r).excluded = (g r).excluded := fun r => GBCA.corrupt_excluded P (g r) id
  have hgrade : ∀ r, (g' r).grade = (g r).grade := fun r => GBCA.corrupt_grade P (g r) id
  have hval : ∀ r, (w' r).val = (w r).val := fun r => WCC.corrupt_val id (w r)
  have hcalled : ∀ r, (w' r).called = (w r).called := fun r => WCC.corrupt_called id (w r)
  have hprocs : c'.processes = c.processes := ABAState.corrupt_processes c id
  have hDS : c'.decidedSent = c.decidedSent := ABAState.corrupt_decidedSent c id
  have hDR : c'.decidedReceived = c.decidedReceived := ABAState.corrupt_decidedReceived c id
  have hFg : ∀ r, (g' r).F = c'.F := fun r => GBCA.corrupt_F_eq id (g r) c (hI.F_gbca r)
  have hFw : ∀ r, (w' r).F = c'.F := fun r => WCC.corrupt_F_eq id (w r) c (hI.F_wcc r)
  have hFsub : c.F ⊆ c'.F := by
    rw [hc'def, ABAState.corrupt_F]; split_ifs with hcond
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  have hFcard : c'.F.card ≤ P.f := by
    rw [hc'def, ABAState.corrupt_F]; split_ifs with hcond
    · obtain ⟨-, hlt⟩ := hcond
      show (insert id c.F).card ≤ P.f
      have hcard := Finset.card_insert_le id c.F
      omega
    · exact hI.F_card
  have hLastBound : ∀ r, IsLastBound g' r ↔ IsLastBound g r := by
    intro r; unfold IsLastBound; rw [hbind r, hbind (r + 1)]
  have hCarrTrans : ∀ r' id₀ v, OutcomeHolder P g' c' r' id₀ v → OutcomeHolder P g c r' id₀ v := by
    intro r' id₀ v hc
    unfold OutcomeHolder at hc ⊢
    rwa [hprocs, hcall (r' + 1)] at hc
  have hCertTrans : ∀ r' b',
    Grade2Certificate P g c r' b' → Grade2Certificate P g' c' r' b' := fun r' b' =>
      Grade2Certificate.of_unchanged (hgrade r') hbind (fun r'' id' => congrFun (hcall r'') id')
        hFsub
      (fun id' => by rw [hprocs]) (fun id' => by rw [hprocs])
      (fun id0 v => hCarrTrans r' id0 v)
  have hHold : ∀ id₀ b₀, Grade2Holder P c' id₀ b₀ → Grade2Holder P c id₀ b₀ := by
    intro id₀ b₀ h
    unfold Grade2Holder at h ⊢
    rwa [hprocs, hDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (fun h0 => hj (hFsub h0)) (hHold j b' hh)⟩
  have hFins : c'.F = insert id c.F := by
    rw [hc'def, ABAState.corrupt_F, if_pos ⟨hnew, hbud⟩]
  have hCorr : ∀ id', c'.corrupted id' = true ↔ id' ∈ c'.F := by
    intro id'
    rw [hFins, Finset.mem_insert]
    by_cases h : id' = id
    · subst h; rw [hc'def, ABAState.corrupt_corrupted_self]; simp
    · rw [hc'def, ABAState.corrupt_corrupted_ne c id h, hI.corrupted_F id']; simp [h]
  refine ⟨hCorr, fun r => hFg r, fun r => hFw r, hFcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r v hb => (hI.bind_support r v (by rw [← hbind r]; exact hb)).mono
      (fun id' b' h => by rw [hprocs]; exact h) hFsub,
    fun r b hgf => GBCA.callSupport_mono (fun id' h => by rw [hcall r]; exact h)
      (by rw [hFg r, hI.F_gbca r]; exact hFsub)
      (hI.grade0Lock_support r b (by rw [← hgrade r]; exact hgf)),
    fun r b h => GBCA.callSupport_mono (fun id' h' => by rw [hcall r]; exact h')
      (by rw [hFg r, hI.F_gbca r]; exact hFsub)
      (hI.excluded_support r b (by rw [← hbind r]; exact h)),
    fun r' i j v v' hm hm' h h' => hI.outcomeHolder_agree r' i j v v'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h') |>.imp (fun hh => hh) (fun hh => by
        rw [hgrade r']; exact hh),
    fun i j b₀ b₀' hm hm' h h' => hI.grade2Lock_agree i j b₀ b₀'
      (fun hh => hm (hFsub hh)) (fun hh => hm' (hFsub hh))
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall0
    rw [hprocs]; rw [hcall 0] at hcall0
    exact hI.input_gbcaRound0 id' b' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.input_called r id' (fun h => hmem (hFsub h)) hcall0
  · intro id' hmem hne
    rw [hprocs] at hne ⊢; exact hI.phase_input id' (fun h => hmem (hFsub h)) hne
  · intro r h
    rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.down_settled r ((RoundSettled.congr (hbind (r + 1)) (hgrade (r + 1))).mp h)
  · obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r hr h => hR r hr ((RoundSettled.congr (hbind r) (hgrade r)).mp h)⟩
  · intro r h
    rw [hval r] at h; rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.wcc_bound r h
  · intro i j b' h
    rw [hDR] at h; rw [hDS]
    exact hI.received_sound i j b' h
  · intro id' b' hmem h
    rw [hDS] at h
    exact (hI.decided_source id' b' (fun h' => hmem (hFsub h')) h).imp (fun r => hCertTrans r b')
  · intro r b' hgr hbr
    rw [hgrade r] at hgr; rw [hbind r] at hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
    refine ⟨fun r' b'' hrr' hb' => ?_, fun r' id' b'' hrr' hmem hcall0 => ?_,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (fun h => hmem (hFsub h)) (hCarrTrans r id0 v hcar)⟩
    · rw [hbind r'] at hb'; exact h1 r' b'' hrr' hb'
    · rw [hcall r'] at hcall0; exact h2 r' id' b'' hrr' (fun h => hmem (hFsub h)) hcall0
    · rw [hprocs] at hround ⊢; exact h3 id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem r hround
    rw [hprocs] at hround; rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.round_bound id' (fun h => hmem (hFsub h)) r hround
  · intro r v hlast hbr hcoin id' hmem hround
    rw [hLastBound r] at hlast; rw [hbind r] at hbr; rw [hval r] at hcoin
    rw [hprocs] at hround ⊢
    exact hI.agree_locked r v hlast hbr hcoin id' (fun h => hmem (hFsub h)) hround
  · intro r h; rw [hgrade r] at h; rw [hbind r]; exact hI.grade2_needs_bind r h
  · intro r id' hmem hcall0
    rw [hprocs]; rw [hcall r] at hcall0
    exact hI.call_round r id' (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [RoundSettled.congr (hbind r) (hgrade r)]
    exact hI.wcc_called r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r id' hmem hround
    rw [hprocs] at hround; rw [hval r]
    exact hI.round_flip r id' (fun h => hmem (hFsub h)) hround
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.estimate0 id' (fun h => hmem (hFsub h)) hround hphase
  · intro id' b' hlg
    rw [hprocs] at hlg
    exact (hI.grade2_source id' b' hlg).imp (fun r => hCertTrans r b')
  · intro r id' hmem hround hphase
    rw [hprocs] at hround hphase
    obtain ⟨hnone, hsome⟩ := hI.estimate_ret r id' (fun h => hmem (hFsub h)) hround hphase
    rw [hprocs]
    refine ⟨fun he => ?_, fun b' hb' => ?_⟩
    · obtain ⟨hg0, hno⟩ := hnone he
      refine ⟨by rw [hgrade]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
      rw [hgrade] at hgr0
      exact hno r₀ hr0 hgr0
    · rw [hbind]; exact hsome b' hb'
  · intro r v h
    rw [hbind (r + 1)] at h; rw [hbind r, hgrade r, hval r]
    exact hI.bind_succ r v h
  · intro r id' v hmem hcall0
    rw [hcall (r + 1)] at hcall0; rw [hbind r, hgrade r, hval r]
    exact hI.call_provenance r id' v (fun h => hmem (hFsub h)) hcall0
  · intro r id' hmem hround hphase v hest
    rw [hprocs] at hround hphase hest; rw [hbind r, hgrade r, hval r]
    exact hI.estimate_previous r id' (fun h => hmem (hFsub h)) hround hphase v hest
  · intro r h; rw [hgrade (r + 1)] at h; rw [hgrade r]; exact hI.grade0Lock_chain r h
  · intro id' hmem hround hphase
    rw [hprocs] at hround hphase ⊢
    exact hI.estimate_previous_ne id' (fun h => hmem (hFsub h)) hround hphase
  · intro r h; rw [hval] at h ⊢; exact hI.wcc_order r h
  · intro id' b' h
    rw [hcall 0] at h; rw [hprocs]
    rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
    · left; exact hin
    · right; exact hFsub hf
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0; rw [hprocs]
    exact hI.wcc_callRound r id' (fun h => hmem (hFsub h)) hcalled0
  · intro r h
    rw [hval] at h
    rcases hI.flip_grade2Lock r h with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentWitness.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro id' hmem hin r
    rw [hprocs] at hin; rw [hcalled r]
    exact hI.idle_no_wccCall id' (fun h => hmem (hFsub h)) hin r
  · intro r id' hmem hp
    rw [hprocs] at hp
    rcases hI.retG_witness r id' (fun h => hmem (hFsub h)) hp with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentWitness.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r id' hmem hcalled0
    rw [hcalled r] at hcalled0
    rcases hI.wccCalled_witness r id' (fun h => hmem (hFsub h)) hcalled0 with hg | hd
    · left; rw [hgrade]; exact hg
    · right
      exact DissentWitness.transport (hbind r) (hbind (r - 1)) (fun hh => (hgrade (r - 1)) ▸ hh)
        (fun id' => by rw [hprocs]) hd
  · intro r h
    rw [hbind r] at h
    exact GBCA.SpecState.quorum_mono (by rw [hFg r, hI.F_gbca r]; exact hFsub)
      (fun id' hne => by rw [hcall r]; exact hne) (hI.bound_quorum r h)

/-- `bindUnset` (the GBCA family's only genuine `τ`-step): excludes one bit of round `r`'s
exclusion set. `down_settled`'s round-`r` corner needs "a call at round `r` implies current
round `≥ r`", a fact `Invariant` doesn't carry explicitly — handed off. The value-transport
corners lean on the exclusion's own D15 guard: the spared bit `!b` keeps `f + 1` F-blind call
support at round `r`, whose derived correct caller determines `!b` at every standing
commitment. -/
theorem Invariant.step_gbcaTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ)
    {μr : PMF (GBCA.SpecState P.n)} (hstep : GBCA.Step P r (g r) .tau μr)
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support) :
    Invariant P (Function.update g r gr') c w ∧
      AbstractStateUnchanged P g (Function.update g r gr') c c := by
  cases hstep
  case bindUnset b _hq _hw hd0 =>
    rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
    have hb : b ∉ (g r).excluded := by
      rw [hd0]; simp
    set g' := Function.update g r { g r with excluded := insert b (g r).excluded } with hg'def
    have hFeq : ∀ r', (g' r').F = (g r').F := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hCalleq : ∀ r', (g' r').call = (g r').call := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hGradeeq : ∀ r', (g' r').grade = (g r').grade := by
      intro r'; by_cases h : r' = r
      · subst h; rw [hg'def, Function.update_self]
      · rw [hg'def, Function.update_of_ne h]
    have hExcludedSelf : (g' r).excluded = insert b (g r).excluded := by
      rw [hg'def, Function.update_self]
    have hExcludedNe : ∀ r', r' ≠ r → (g' r').excluded = (g r').excluded := by
      intro r' h; rw [hg'def, Function.update_of_ne h]
    have hExcludedMono : ∀ r' x, x ∈ (g r').excluded → x ∈ (g' r').excluded := by
      intro r' x hx
      by_cases h : r' = r
      · subst h; rw [hExcludedSelf]; exact Finset.mem_insert_of_mem hx
      · rw [hExcludedNe r' h]; exact hx
    obtain ⟨id0, hid0F, hcall0⟩ :=
      GBCA.exists_correct_caller _hw (by rw [hI.F_gbca r]; exact hI.F_card)
    have hFid0 : id0 ∉ c.F := by
      rw [← hI.F_gbca r]; exact hid0F
    have hClosedNe : ∀ r', r' ≠ r → (RoundSettled g' r' ↔ RoundSettled g r') :=
      fun r' h => RoundSettled.congr (hExcludedNe r' h) (hGradeeq r')
    have hClosedSelf : RoundSettled g' r := Or.inl (by rw [hExcludedSelf]; simp)
    have hDissTrans : ∀ r₀, DissentWitness P g c r₀ → DissentWitness P g' c r₀ := by
      intro r₀ hd
      obtain ⟨v, hbv, hif⟩ := hd
      refine ⟨v, hExcludedMono r₀ _ hbv, ?_⟩
      by_cases h0 : r₀ = 0
      · rw [if_pos h0] at hif ⊢; exact hif
      · rw [if_neg h0] at hif ⊢
        rcases hif with hh | hh
        · exact Or.inl (hExcludedMono (r₀ - 1) _ hh)
        · exact Or.inr ((hGradeeq (r₀ - 1)).trans hh)
    have hCarrTrans : ∀ r₀ id₀ v, OutcomeHolder P g' c r₀ id₀ v → OutcomeHolder P g c r₀ id₀ v := by
      intro r₀ id₀ v hc
      unfold OutcomeHolder at hc ⊢
      rwa [hCalleq (r₀ + 1)] at hc
    have hCommitTrans : ∀ r'' b'', (!b'') ∈ (g r'').excluded → Grade2Commitment P g c r'' b'' →
        Grade2Commitment P g' c r'' b'' := by
      rintro r'' b'' hres ⟨h1, h2, h3, h4⟩
      refine ⟨fun r₀ b₀ hrr hb' => ?_,
        fun r₀ id₀ b₀ hrr hmem hcall =>
          h2 r₀ id₀ b₀ hrr hmem (by rw [← hCalleq r₀]; exact hcall), h3,
        fun id₀ v hmem hcar => h4 id₀ v hmem (hCarrTrans r'' id₀ v hcar)⟩
      by_cases h3' : r₀ = r
      · subst h3'
        rw [hExcludedSelf] at hb'
        have hb₀nd : b₀ ∉ (g r₀).excluded := fun hh => hb'.2 (Finset.mem_insert_of_mem hh)
        rcases Finset.mem_insert.mp hb'.1 with hnew | hold
        · rcases eq_or_lt_of_le hrr with heq | hlt
          · have hne : b₀ ≠ !b'' := fun hh => hb₀nd (hh ▸ (heq ▸ hres))
            revert hne; cases b₀ <;> cases b'' <;> simp
          · have hb₀ : b₀ = !b := by revert hnew; cases b₀ <;> cases b <;> simp
            rw [hb₀]; exact h2 r₀ id0 (!b) hlt hFid0 hcall0
        · exact h1 r₀ b₀ hrr ⟨hold, hb₀nd⟩
      · rw [hExcludedNe r₀ h3'] at hb'; exact h1 r₀ b₀ hrr hb'
    have hCertTrans : ∀ r'' b'',
        Grade2Certificate P g c r'' b'' → Grade2Certificate P g' c r'' b'' := by
      rintro r'' b'' ⟨hg1, hd1, hcm⟩
      exact ⟨(hGradeeq r'').trans hg1, hExcludedMono r'' _ hd1, hCommitTrans r'' b'' hd1 hcm⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
      fun v _ hpin => hpin⟩
    refine ⟨hI.corrupted_F, fun r' => (hFeq r').trans (hI.F_gbca r'), hI.F_wcc, hI.F_card,
      ?_, ?_, hI.phase_input,
      ?_, ?_, ?_,
      hI.received_sound, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.round_flip, hI.estimate0, ?_, ?_,
      ?_, ?_, ?_, ?_, hI.estimate_previous_ne, hI.wcc_order, ?_, hI.wcc_callRound, ?_,
      hI.idle_no_wccCall, ?_, ?_, ?_, ?_, ?_, ?_,
      fun r₀ i j v v' hm hm' h h' => (hI.outcomeHolder_agree r₀ i j v v' hm hm'
        (hCarrTrans _ _ _ h) (hCarrTrans _ _ _ h')).imp (fun x => x)
        (fun hh => (hGradeeq r₀).trans hh),
      hI.grade2Lock_agree⟩
    · intro id b' hmem hcall; rw [hCalleq] at hcall; exact hI.input_gbcaRound0 id b' hmem hcall
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.input_called r' id hmem hcall
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · by_cases h1 : r' + 1 = r
        · -- the fresh exclusion at `r' + 1` had a correct caller of the spared bit, whose
          -- round progress closes `r'`
          obtain ⟨id0, hid0F, hcall0⟩ :=
            GBCA.exists_correct_caller _hw (by rw [hI.F_gbca r]; exact hI.F_card)
          have hFid0 : id0 ∉ c.F := by
            rw [← hI.F_gbca r]; exact hid0F
          have hcr : r ≤ (c.processes id0).round :=
            hI.call_round r id0 hFid0 (by rw [hcall0]; simp)
          rw [hClosedNe r' h2]
          exact hI.round_bound id0 hFid0 r' (by omega)
        · rw [hClosedNe r' h2]
          exact hI.down_settled r' ((hClosedNe (r' + 1) h1).mp h)
    · obtain ⟨R, hR⟩ := hI.quiescent
      exact ⟨max R (r + 1), fun r' hr' h =>
        hR r' (by omega) ((hClosedNe r' (by omega)).mp h)⟩
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.wcc_bound r' h
    · intro id b' hmem h
      exact (hI.decided_source id b' hmem h).imp (fun r'' => hCertTrans r'' b')
    · intro r' b' hgr hbr
      rw [hGradeeq] at hgr
      have hpair : (!b') ∈ (g r').excluded ∧ b' ∉ (g r').excluded := by
        by_cases h2 : r' = r
        · subst h2
          rw [hExcludedSelf] at hbr
          refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
          rcases Finset.mem_insert.mp hbr.1 with hnew | hold
          · -- the fresh exclusion is `!b'`: the grade-2-locked round already had an excluded bit,
            -- which can be neither `b` (`hb`) nor `b'` (still alive), so it is `!b'`
            obtain ⟨wd, hwd⟩ :=
              Finset.nonempty_iff_ne_empty.mpr (hI.grade2_needs_bind r' hgr)
            have hwb : wd ≠ b := fun hh => hb (hh ▸ hwd)
            have hwb' : wd ≠ b' := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
            have hwd' : wd = !b' := by
              revert hwb hwb' hnew; cases wd <;> cases b' <;> cases b <;> simp
            exact hwd' ▸ hwd
          · exact hold
        · rw [hExcludedNe r' h2] at hbr; exact hbr
      exact hCommitTrans r' b' hpair.1 (hI.grade2Lock_commit r' b' hgr hpair)
    · intro id hmem r' hround
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.round_bound id hmem r' hround
    · intro r' v hlast hbr hcoin id hmem hround
      by_cases h1 : r' + 1 = r
      · exfalso
        have hemp : (g' (r' + 1)).excluded = ∅ := hlast.2
        rw [h1, hExcludedSelf] at hemp; exact absurd hemp (by simp)
      · by_cases h2 : r' = r
        · have hExcludedSelf' : (g' r').excluded = insert b (g r').excluded := by
            rw [h2]; exact hExcludedSelf
          have hbAt : b ∉ (g r').excluded := by
            rw [h2]; exact hb
          have hemp1 : (g (r' + 1)).excluded = ∅ := by
            rw [← hExcludedNe (r' + 1) h1]; exact hlast.2
          by_cases hexcluded0 : (g r').excluded = ∅
          · -- round `r'` was fresh before this exclusion, hence already grade-0-blocked upward;
            -- `estimate_previous` fixes `id`'s estimate at the agreeing coin's bit.
            have hnoC : (g (r' + 1)).grade ≠ some false :=
              fun hh => hI.no_grade0Lock_succ r' v hcoin (by rw [hexcluded0]; simp) hh
            have hround1 : (c.processes id).round = r' + 1 := by
              by_contra hne
              rcases hI.round_bound id hmem (r' + 1) (by omega) with hh | hh
              · exact hh hemp1
              · exact hnoC hh
            by_cases hgroup : (c.processes id).phase = .toCallW ∨ (c.processes id).phase = .awaitW
            · exfalso
              obtain ⟨hnone, hsome⟩ := hI.estimate_ret (r' + 1) id hmem hround1 hgroup
              rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with he | ⟨u, he⟩
              · exact hnoC (hnone he).1
              · have hu := hsome u he
                rw [hemp1] at hu; exact absurd hu (by simp)
            · have hphase3 : (c.processes id).phase = .idle ∨ (c.processes id).phase = .toCallG ∨
                  (c.processes id).phase = .awaitG := by
                rcases hph2 : (c.processes id).phase with _ | _ | _ | _ | _
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr rfl)
                · exact absurd (Or.inl hph2) hgroup
                · exact absurd (Or.inr hph2) hgroup
              obtain ⟨u, he⟩ :=
                Option.ne_none_iff_exists'.mp (hI.estimate_previous_ne id hmem (by omega) hphase3)
              rw [he]
              rcases hI.estimate_previous r' id hmem hround1 hphase3 u he with hbu | ⟨-, hw0⟩
              · rw [hexcluded0] at hbu; simp at hbu
              · rcases hw0 with hh | hh
                · rw [hcoin] at hh; simp only [CoinValue.bit.injEq] at hh; rw [hh]
                · rw [hcoin] at hh; simp at hh
          · -- round `r'` already had an excluded bit, which the live pair fixes at `!v`:
            -- the pre-exclude pair holds and the old `agree_locked` applies
            have hpairold : (!v) ∈ (g r').excluded ∧ v ∉ (g r').excluded := by
              rw [hExcludedSelf'] at hbr
              refine ⟨?_, fun hh => hbr.2 (Finset.mem_insert_of_mem hh)⟩
              rcases Finset.mem_insert.mp hbr.1 with hnew | hold
              · obtain ⟨wd, hwd⟩ := Finset.nonempty_iff_ne_empty.mpr hexcluded0
                have hwb : wd ≠ b := fun hh => hbAt (hh ▸ hwd)
                have hwv : wd ≠ v := fun hh => hbr.2 (Finset.mem_insert_of_mem (hh ▸ hwd))
                have hwd' : wd = !v := by
                  revert hwb hwv hnew; cases wd <;> cases v <;> cases b <;> simp
                exact hwd' ▸ hwd
              · exact hold
            have hlast' : IsLastBound g r' :=
              ⟨Finset.nonempty_iff_ne_empty.mp ⟨_, hpairold.1⟩, hemp1⟩
            exact hI.agree_locked r' v hlast' hpairold hcoin id hmem hround
        · have hlast' : IsLastBound g r' := ⟨by rw [← hExcludedNe r' h2]; exact hlast.1,
            by rw [← hExcludedNe (r' + 1) h1]; exact hlast.2⟩
          rw [hExcludedNe r' h2] at hbr
          exact hI.agree_locked r' v hlast' hbr hcoin id hmem hround
    · intro r' h
      by_cases h2 : r' = r
      · subst h2; rw [hExcludedSelf]; simp
      · rw [hGradeeq] at h
        rw [hExcludedNe r' h2]; exact hI.grade2_needs_bind r' h
    · intro r' id hmem hcall; rw [hCalleq] at hcall; exact hI.call_round r' id hmem hcall
    · intro r' id hmem hcalled
      by_cases h2 : r' = r
      · subst h2; exact hClosedSelf
      · rw [hClosedNe r' h2]; exact hI.wcc_called r' id hmem hcalled
    · intro id b hlg
      exact (hI.grade2_source id b hlg).imp (fun r'' => hCertTrans r'' b)
    · intro r' id hmem hround hphase
      obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id hmem hround hphase
      refine ⟨fun he => ?_, fun b' hb' => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨(hGradeeq r').trans hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · exact hExcludedMono r' _ (hsome b' hb')
    · intro r' v h
      by_cases h1 : r' + 1 = r
      · rw [h1, hExcludedSelf] at h
        rcases Finset.mem_insert.mp h with hnew | hold
        · -- the fresh exclusion: the spared bit `!b = v` was carried by the derived
          -- correct caller, whose `call_provenance` provenance is the conclusion verbatim
          have hveq : v = !b := by
            revert hnew; cases v <;> cases b <;> simp
          have hcp := hI.call_provenance r' id0 (!b) hFid0 (by rw [h1]; exact hcall0)
          rw [← hveq] at hcp
          rcases hcp with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hExcludedMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
        · rcases hI.bind_succ r' v (by rw [h1]; exact hold) with hd | ⟨hg0, hw0⟩
          · exact Or.inl (hExcludedMono r' _ hd)
          · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
      · rw [hExcludedNe (r' + 1) h1] at h
        rcases hI.bind_succ r' v h with hd | ⟨hg0, hw0⟩
        · exact Or.inl (hExcludedMono r' _ hd)
        · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id v hmem hcall
      rw [hCalleq] at hcall
      rcases hI.call_provenance r' id v hmem hcall with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hExcludedMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' id hmem hround hphase v hest
      rcases hI.estimate_previous r' id hmem hround hphase v hest with hd | ⟨hg0, hw0⟩
      · exact Or.inl (hExcludedMono r' _ hd)
      · exact Or.inr ⟨(hGradeeq r').trans hg0, hw0⟩
    · intro r' h
      rw [hGradeeq] at h ⊢
      exact hI.grade0Lock_chain r' h
    · intro id b' h; rw [hCalleq] at h; exact hI.input_gbcaRound0_permanent id b' h
    · -- `flip_grade2Lock`: `grade` and every residue component are monotone-transported
      intro r' h
      rcases hI.flip_grade2Lock r' h with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hp
      rcases hI.retG_witness r' id hmem hp with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' id hmem hcalled
      rcases hI.wccCalled_witness r' id hmem hcalled with hg | hd
      · left; rw [hGradeeq]; exact hg
      · right; exact hDissTrans r' hd
    · intro r' h
      by_cases h2 : r' = r
      · rw [h2]
        exact GBCA.SpecState.quorum_of_eq (hFeq r) (hCalleq r) _hq
      · rw [hExcludedNe r' h2] at h
        exact GBCA.SpecState.quorum_of_eq (hFeq r') (hCalleq r') (hI.bound_quorum r' h)
    · -- I26 establishment: the fresh exclusion's D15 count is the spared bit's sent source
      intro r' v hb'
      by_cases h2 : r' = r
      · rw [h2, hExcludedSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · have hveq : v = !b := by revert hnew; cases v <;> cases b <;> simp
          rw [hveq]
          exact hI.support_of_call_count r (!b) _hw
        · exact hI.bind_support r v hold
      · rw [hExcludedNe r' h2] at hb'; exact hI.bind_support r' v hb'
    · intro r' b' hgf
      rw [hGradeeq] at hgf
      exact GBCA.callSupport_mono (fun id' h => by rw [hCalleq r']; exact h) (hFeq r').ge
        (hI.grade0Lock_support r' b' hgf)
    · -- I28 establishment: the fresh exclusion records its own guard; old exclusions keep theirs
      intro r' b' hb'
      have hcnt : ∀ r₀ b₀, P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g r₀).call id' = some (!b₀) ∨ id' ∈ (g r₀).F)).card →
          P.f + 1 ≤ (Finset.univ.filter
          (fun id' => (g' r₀).call id' = some (!b₀) ∨ id' ∈ (g' r₀).F)).card :=
        fun r₀ b₀ hh => GBCA.callSupport_mono (fun id' h => by rw [hCalleq r₀]; exact h)
          (hFeq r₀).ge hh
      by_cases h2 : r' = r
      · rw [h2] at hb' ⊢
        rw [hExcludedSelf] at hb'
        rcases Finset.mem_insert.mp hb' with hnew | hold
        · rw [hnew]; exact hcnt r b _hw
        · exact hcnt r b' (hI.excluded_support r b' hold)
      · rw [hExcludedNe r' h2] at hb'
        exact hcnt r' b' (hI.excluded_support r' b' hb')

/-- Core `τ`: DECIDED delivery, echo, or byzantine injection. All three leave `processes`/`F`
untouched, so only `received_sound`/`decided_source` need real work; the `echo` case's correct
sender comes from an `f + 1`-vs-`≤ f` pigeonhole on the delivered senders. -/
theorem Invariant.step_roundLoopTau {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w)
    {μc : PMF (ABAState P)}
    (hstep :
      (∃ i j b, b ∈ c.decidedSent j ∧ b ∉ c.decidedReceived i j ∧
          μc = PMF.pure (c.deliverDecided i j b)) ∨
        (∃ id b, P.f + 1 ≤ c.decidedCount id b ∧ b ∉ c.decidedSent id ∧
          μc = PMF.pure (c.sendDecided id b)) ∨
        (∃ id b, id ∈ c.F ∧ μc = PMF.pure (c.sendDecided id b)))
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' w ∧ AbstractStateUnchanged P g g c c' := by
  rcases hstep with ⟨i, j, b, hs, hr, rfl⟩ | ⟨id, b, hcnt, hs, rfl⟩ | ⟨id, b, hF, rfl⟩
  · -- deliver
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.deliverDecided i j b).processes = c.processes :=
      ABAState.deliverDecided_processes _ _ _ _
    have hFeq : (c.deliverDecided i j b).F = c.F := ABAState.deliverDecided_F _ _ _ _
    have hDS : (c.deliverDecided i j b).decidedSent = c.decidedSent :=
      ABAState.deliverDecided_decidedSent _ _ _ _
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g (c.deliverDecided i j b) r' b' := fun r'
        b' => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj)
        (by unfold Grade2Holder at hh ⊢; rwa [hProcs, hDS] at hh)⟩
    refine ⟨fun id' => by
        rw [ABAState.deliverDecided_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r => by rw [hFeq]; exact hI.F_gbca r, fun r => by rw [hFeq]; exact hI.F_wcc r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold OutcomeHolder at h ⊢; rwa [hProcs] at h)
        (by unfold OutcomeHolder at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold Grade2Holder at h ⊢; rwa [hProcs, hDS] at h)
        (by unfold Grade2Holder at h' ⊢; rwa [hProcs, hDS] at h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDS]
      by_cases hij : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := hij
        rw [ABAState.deliverDecided_decidedReceived_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact hs
        · exact hI.received_sound i' j' b' h
      · rw [ABAState.deliverDecided_decidedReceived_of_ne _ _ _ _ (by tauto)] at h
        exact hI.received_sound i' j' b' h
    · intro id' b' hmem h
      rw [hDS] at h
      exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.estimate_previous r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_gbcaRound0_permanent id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.wcc_callRound r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retG_witness r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- echo: a correct sender among the `f + 1` counted deliveries
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).processes = c.processes := ABAState.sendDecided_processes _ _
      _
    have hFeq : (c.sendDecided id b).F = c.F := ABAState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedReceived = c.decidedReceived :=
      ABAState.sendDecided_decidedReceived _ _ _
    have hcnt' : P.f + 1 ≤ (Finset.univ.filter (fun j => b ∈ c.decidedReceived id j)).card :=
      hcnt
    have hcard : c.F.card < (Finset.univ.filter (fun j => b ∈ c.decidedReceived id j)).card := by
      have := hI.F_card
      omega
    obtain ⟨j, hjmem, hjF⟩ :=
      (Finset.not_subset (s := Finset.univ.filter (fun j => b ∈ c.decidedReceived id j))
        (t := c.F)).mp (fun hsub => absurd (Finset.card_le_card hsub) (by omega))
    rw [Finset.mem_filter] at hjmem
    have hjsent : b ∈ c.decidedSent j := hI.received_sound id j b hjmem.2
    obtain ⟨r0, hcert0⟩ := hI.decided_source j b hjF hjsent
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g (c.sendDecided id b) r' b' := fun r' b'
        => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → Grade2Holder P (c.sendDecided id b) i0 b0 →
        ∃ j0, j0 ∉ c.F ∧ Grade2Holder P c j0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact ⟨i0, hm, Or.inl h⟩
      · rcases (ABAState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨-, rfl⟩ | h
        · exact ⟨j, hjF, Or.inr hjsent⟩
        · exact ⟨i0, hm, Or.inr h⟩
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => by
        obtain ⟨j0, hj0, hh0⟩ := hHold j b' (hFeq ▸ hj) hh
        exact hpin j0 b' hj0 hh0⟩
    refine ⟨fun id' => by
        rw [ABAState.sendDecided_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r => by rw [hFeq]; exact hI.F_gbca r, fun r => by rw [hFeq]; exact hI.F_wcc r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold OutcomeHolder at h ⊢; rwa [hProcs] at h)
        (by unfold OutcomeHolder at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => by
        obtain ⟨ja, hjaF, hja⟩ := hHold i0 b0 (hFeq ▸ hm) h
        obtain ⟨jb, hjbF, hjb⟩ := hHold j0 b0' (hFeq ▸ hm') h'
        exact hI.grade2Lock_agree ja jb b0 b0' hjaF hjbF hja hjb⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact ABAState.sendDecided_decidedSent_mono _ _ _ (hI.received_sound i' j' b' h)
    · intro id' b' hmem h
      rw [ABAState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid
        rw [Function.update_self, Finset.mem_insert] at h
        rcases h with rfl | h
        · exact ⟨r0, hCert r0 b' hcert0⟩
        · exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg; exact hI.grade2_source id' b' hlg
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.estimate_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.estimate_previous r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_gbcaRound0_permanent id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.wcc_callRound r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retG_witness r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
  · -- byzantine DECIDED injection: `id ∈ F`, so correct `decided_source` at `id` is vacuous
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    have hProcs : (c.sendDecided id b).processes = c.processes := ABAState.sendDecided_processes _ _
      _
    have hFeq : (c.sendDecided id b).F = c.F := ABAState.sendDecided_F _ _ _
    have hDR : (c.sendDecided id b).decidedReceived = c.decidedReceived :=
      ABAState.sendDecided_decidedReceived _ _ _
    have hCert : ∀ r' b',
      Grade2Certificate P g c r' b' → Grade2Certificate P g (c.sendDecided id b) r' b' := fun r' b'
        => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
        (by rw [hFeq] : c.F ⊆ _) (fun id' => by rw [hProcs]) (fun id' => by rw [hProcs])
        (fun id0 v hcar => by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)
    have hHold : ∀ i0 b0, i0 ∉ c.F → Grade2Holder P (c.sendDecided id b) i0 b0 →
        Grade2Holder P c i0 b0 := by
      intro i0 b0 hm h
      rcases h with h | h
      · rw [hProcs] at h; exact Or.inl h
      · rcases (ABAState.mem_sendDecided_decidedSent_iff _ _ _ _ _).mp h with ⟨rfl, rfl⟩ | h
        · exact absurd hF hm
        · exact Or.inr h
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hHold j b' (hFeq ▸ hj) hh)⟩
    refine ⟨fun id' => by
        rw [ABAState.sendDecided_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r => by rw [hFeq]; exact hI.F_gbca r, fun r => by rw [hFeq]; exact hI.F_wcc r,
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent, hI.wcc_bound, ?_, ?_, ?_, ?_, ?_,
      hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, hI.bind_succ, ?_, ?_, hI.grade0Lock_chain, ?_,
      hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r v hb => (hI.bind_support r v hb).mono
        (fun id' b' h => by rw [hProcs]; exact h) (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r' i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r' i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm')
        (by unfold OutcomeHolder at h ⊢; rwa [hProcs] at h)
        (by unfold OutcomeHolder at h' ⊢; rwa [hProcs] at h'),
      fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hHold i0 b0 (hFeq ▸ hm) h) (hHold j0 b0' (hFeq ▸ hm') h')⟩
    · intro id' b' hmem hcall
      rw [hProcs]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcall
      rw [hProcs]; exact hI.input_called r id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      rw [hProcs] at hne ⊢; exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i' j' b' h
      rw [hDR] at h
      exact ABAState.sendDecided_decidedSent_mono _ _ _ (hI.received_sound i' j' b' h)
    · intro id' b' hmem h
      rw [ABAState.sendDecided_decidedSent] at h
      by_cases hid : id' = id
      · subst hid; exact absurd (hFeq ▸ hmem) (not_not.mpr hF)
      · rw [Function.update_of_ne hid] at h
        exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r => hCert r b')
    · intro r b' hgr hbr
      obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r b' hgr hbr
      refine ⟨h1, h2, fun id' hmem hround => ?_,
        fun id0 v hmem hcar => h4 id0 v (hFeq ▸ hmem)
          (by unfold OutcomeHolder at hcar ⊢; rwa [hProcs] at hcar)⟩
      rw [hProcs] at hround ⊢; exact h3 id' (hFeq ▸ hmem) hround
    · intro id' hmem r hround
      rw [hProcs] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r hround
    · intro r v hlast hbr hcoin id' hmem hround
      rw [hProcs] at hround ⊢; exact hI.agree_locked r v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · intro r id' hmem hcall; rw [hProcs]; exact hI.call_round r id' (hFeq ▸ hmem) hcall
    · intro r id' hmem hcalled; exact hI.wcc_called r id' (hFeq ▸ hmem) hcalled
    · intro r id' hmem hround
      rw [hProcs] at hround; exact hI.round_flip r id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢; exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      rw [hProcs] at hlg
      exact (hI.grade2_source id' b' hlg).imp (fun r => hCert r b')
    · intro r id' hmem hround hphase
      rw [hProcs] at hround hphase; exact hI.estimate_ret r id' (hFeq ▸ hmem) hround hphase
    · intro r id' v hmem hcall; exact hI.call_provenance r id' v (hFeq ▸ hmem) hcall
    · intro r id' hmem hround hphase v hest
      rw [hProcs] at hround hphase hest
      exact hI.estimate_previous r id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      rw [hProcs] at hround hphase ⊢
      exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro id' b' h; rw [hProcs]; exact hI.input_gbcaRound0_permanent id' b' h
    · intro r id' hmem hcalled; rw [hProcs]; exact hI.wcc_callRound r id' (hFeq ▸ hmem) hcalled
    · intro r h
      rcases hI.flip_grade2Lock r h with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro id' hmem hin r; rw [hProcs] at hin; exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r
    · intro r id' hmem hp
      rw [hProcs] at hp
      rcases hI.retG_witness r id' (hFeq ▸ hmem) hp with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd
    · intro r id' hmem hcalled
      rcases hI.wccCalled_witness r id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => by rw [hProcs]) hd

/-- A round whose caller count has passed `f` has a never-corrupted caller: the callers
outnumber the corrupted set, which `F_card` bounds by `f`. -/
theorem Invariant.exists_correct_wccCaller {P : Parameters} {g : ℕ → GBCA.SpecState P.n}
    {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) {r : ℕ}
    (hq : (w r).threshold P) : ∃ id, id ∉ c.F ∧ (w r).called id = true := by
  by_contra hcon
  have hsub : (Finset.univ.filter (fun id => (w r).called id)) ⊆ c.F := by
    intro id hid
    rw [Finset.mem_filter] at hid
    by_contra hF
    exact hcon ⟨id, hF, hid.2⟩
  have hcard := Finset.card_le_card hsub
  have hFcard := hI.F_card
  rw [WCC.SpecState.threshold] at hq
  omega

/-- The coin resolution the resolving call carries: round `r`'s caller count has passed `f`
at an unresolved `val`, and the drawn outcome is written to `val`. The clauses that read
`(w r).val` are re-established from the threshold, which supplies a never-corrupted caller of
round `r` (`Invariant.exists_correct_wccCaller`); that caller's `wcc_called`, `wcc_callRound` and
`wccCalled_witness` carry `wcc_bound`, `wcc_order` and `flip_grade2Lock` respectively.
`agree_locked`'s round-`r` corner is vacuous, since `round_flip` at a correct process past round `r`
contradicts `val = ⊥`. -/
theorem Invariant.step_callW_resolve {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ)
    (hq : (w r).threshold P) (hv : (w r).val = .bot) (o : CoinOutcome) :
    Invariant P g c (Function.update w r { w r with val := o.toCoinValue }) := by
  set w' := Function.update w r { w r with val := o.toCoinValue } with hw'def
  have hFeq : ∀ r', (w' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [hw'def, Function.update_self]
    · rw [hw'def, Function.update_of_ne h]
  have hValNe : ∀ r', r' ≠ r → (w' r').val = (w r').val := by
    intro r' h; rw [hw'def, Function.update_of_ne h]
  have hValSelf : (w' r).val = o.toCoinValue := by
    rw [hw'def, Function.update_self]
  have hCalledEq : ∀ r', (w' r').called = (w r').called := by
    intro r'; by_cases h : r' = r
    · subst h; rw [hw'def, Function.update_self]
    · rw [hw'def, Function.update_of_ne h]
  refine ⟨hI.corrupted_F, hI.F_gbca, fun r' => (hFeq r').trans (hI.F_wcc r'), hI.F_card,
    hI.input_gbcaRound0,
    hI.input_called, hI.phase_input, hI.down_settled, hI.quiescent, ?_, hI.received_sound,
    hI.decided_source, hI.grade2Lock_commit, hI.round_bound, ?_, hI.grade2_needs_bind,
      hI.call_round, ?_, ?_,
    hI.estimate0, hI.grade2_source, hI.estimate_ret, ?_, ?_, ?_, hI.grade0Lock_chain,
      hI.estimate_previous_ne,
    ?_, hI.input_gbcaRound0_permanent, ?_, ?_, ?_, hI.retG_witness, ?_, hI.bound_quorum,
    hI.bind_support, hI.grade0Lock_support, hI.excluded_support, hI.outcomeHolder_agree,
      hI.grade2Lock_agree⟩
  · intro r' h
    by_cases h2 : r' = r
    · obtain ⟨id0, hid0cF, hid0called⟩ :=
        hI.exists_correct_wccCaller (r := r') (by rw [h2]; exact hq)
      exact hI.wcc_called r' id0 hid0cF hid0called
    · rw [hValNe r' h2] at h; exact hI.wcc_bound r' h
  · intro r' v hlast hbr hcoin id hmem hround
    by_cases h2 : r' = r
    · have hround' : r < (c.processes id).round := by rw [← h2]; exact hround
      exact absurd hv (hI.round_flip r id hmem hround')
    · rw [hValNe r' h2] at hcoin
      exact hI.agree_locked r' v hlast hbr hcoin id hmem hround
  · intro r' id hmem hcalled
    rw [hCalledEq] at hcalled; exact hI.wcc_called r' id hmem hcalled
  · intro r' id hmem hround
    by_cases h2 : r' = r
    · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toCoinValue]
    · rw [hValNe r' h2]; exact hI.round_flip r' id hmem hround
  · intro r' v h
    have hb := hI.bind_succ r' v h
    by_cases h2 : r' = r
    · rw [h2] at hb ⊢
      rcases hb with hbv | ⟨hg0, hw0⟩
      · exact Or.inl hbv
      · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
    · rw [hValNe r' h2]; exact hb
  · intro r' id v hmem hcall
    have hcp := hI.call_provenance r' id v hmem hcall
    by_cases h2 : r' = r
    · rw [h2] at hcp ⊢
      rcases hcp with hbv | ⟨hg0, hw0⟩
      · exact Or.inl hbv
      · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
    · rw [hValNe r' h2]; exact hcp
  · intro r' id hmem hround hphase v hest
    have hep := hI.estimate_previous r' id hmem hround hphase v hest
    by_cases h2 : r' = r
    · rw [h2] at hep ⊢
      rcases hep with hbv | ⟨hg0, hw0⟩
      · exact Or.inl hbv
      · rcases hw0 with hh | hh <;> rw [hv] at hh <;> simp at hh
    · rw [hValNe r' h2]; exact hep
  · -- `wcc_order`: pass-through, except at round `r`'s predecessor, where the correct caller
    -- of round `r` has already passed round `r - 1`, so `round_flip` applies to it.
    intro r' h
    by_cases h2 : r' = r
    · subst h2; rw [hValSelf]; cases o <;> simp [CoinOutcome.toCoinValue]
    · by_cases h1 : r' + 1 = r
      · obtain ⟨id0, hid0cF, hid0called⟩ := hI.exists_correct_wccCaller (r := r) hq
        have hcr := hI.wcc_callRound r id0 hid0cF hid0called
        rw [hValNe r' h2]
        exact hI.round_flip r' id0 hid0cF (by omega)
      · rw [hValNe (r' + 1) h1] at h; rw [hValNe r' h2]; exact hI.wcc_order r' h
  · intro r' id hmem hcalled; rw [hCalledEq] at hcalled; exact hI.wcc_callRound r' id hmem hcalled
  · -- `flip_grade2Lock`'s establishment: round `r`'s correct caller feeds `wccCalled_witness`
    -- directly.
    intro r' h
    by_cases h2 : r' = r
    · obtain ⟨id0, hid0cF, hid0called⟩ :=
        hI.exists_correct_wccCaller (r := r') (by rw [h2]; exact hq)
      exact hI.wccCalled_witness r' id0 hid0cF hid0called
    · rw [hValNe r' h2] at h; exact hI.flip_grade2Lock r' h
  · intro id hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wccCall id hmem hin r'
  · intro r' id hmem hcalled
    rw [hCalledEq] at hcalled; exact hI.wccCalled_witness r' id hmem hcalled

/-- The Dirac rows of `callW` — the input-enabledness loop and the recording call. The WCC
instance touches only `.called`, and only at `id`; the core touches only `.phase`, and only at
`id`. `Invariant` inspects neither, so this is pure bookkeeping. -/
theorem Invariant.step_callW_dirac {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    {wr' : WCC.SpecState P.n} (hWF : wr'.F = (w r).F) (hWval : wr'.val = (w r).val)
    (hWcalled : ∀ j, j ≠ id → wr'.called j = (w r).called j)
    {c' : ABAState P}
    (hCstep : ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
        c' = c.setProcess id { c.processes id with phase := .awaitW }) ∨ (id ∈ c.F ∧ c' = c)) :
    Invariant P g c' (Function.update w r wr') ∧ AbstractStateUnchanged P g g c c' := by
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hWF
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hWval
    · rw [hWNe r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedReceived =
    c.decidedReceived ∧
      ∀ id',
        (c'.processes id').input = (c.processes id').input ∧ (c'.processes id').estimate =
          (c.processes id').estimate ∧ (c'.processes id').round = (c.processes id').round := by
    rcases hCstep with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · refine ⟨ABAState.setProcess_F _ _ _, ABAState.setProcess_decidedSent _ _ _,
        ABAState.setProcess_decidedReceived _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [ABAState.setProcess_processes_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  have hLastGrade : ∀ id', (c'.processes id').lastGrade = (c.processes id').lastGrade := by
    rcases hCstep with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]
      · rw [ABAState.setProcess_processes_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarr : ∀ r₀ id₀ v, OutcomeHolder P g c' r₀ id₀ v → OutcomeHolder P g c r₀ id₀ v := by
    intro r₀ id₀ v hc0
    rcases hc0 with h | ⟨he, hk⟩
    · exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCstep with ⟨hph, hrid, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, ABAState.setProcess_processes_self] at hk
          rcases hk with ⟨hr0, -⟩ | ⟨-, hp⟩
          · exact Or.inl ⟨hr0, Or.inl hph⟩
          · exfalso; rcases hp with hp | hp | hp <;> simp at hp
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCert : ∀ r' b', Grade2Certificate P g c r' b' → Grade2Certificate P g c' r' b' :=
    fun r' b' => Grade2Certificate.of_unchanged rfl (fun _ => rfl) (fun _ _ => rfl)
      (by rw [hCF] : c.F ⊆ _) (fun id' => (hCprocs id').2.2) (fun id' => (hCprocs id').2.1)
      (fun id0 v => hCarr r' id0 v)
  have hHold : ∀ i0 b0, Grade2Holder P c' i0 b0 → Grade2Holder P c i0 b0 := by
    intro i0 b0 h
    unfold Grade2Holder at h ⊢
    rwa [hLastGrade, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCert r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  have hCcorr : c'.corrupted = c.corrupted := by
    rcases hCstep with ⟨-, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · rw [hc'eq]; exact ABAState.setProcess_corrupted _ _ _
    · rw [hc'eq]
  refine ⟨fun id' => by rw [hCcorr, hCF]; exact hI.corrupted_F id',
    fun r' => hCF ▸ hI.F_gbca r', fun r' => (hFweq r').trans (hCF ▸ hI.F_wcc r'),
    hCF ▸ hI.F_card,
    ?_, ?_, ?_, hI.down_settled, hI.quiescent, ?_, ?_, ?_, ?_, ?_, ?_,
    hI.grade2_needs_bind, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.grade0Lock_chain, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
    fun r' v hb => (hI.bind_support r' v hb).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    hI.grade0Lock_support, hI.excluded_support,
    fun r₀ i0 j0 v v' hm hm' h h' => hI.outcomeHolder_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarr _ _ _ h) (hCarr _ _ _ h'),
    fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · intro id' b' hmem hcall; rw [(hCprocs id').1]; exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem)
      hcall
  · intro r' id' hmem hcall
    rw [(hCprocs id').1]; exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · intro id' hmem hne
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
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
  · intro r' h; rw [hValeq] at h; exact hI.wcc_bound r' h
  · intro i j b h; rw [hCDR] at h; rw [hCDS]; exact hI.received_sound i j b h
  · intro id' b' hmem h; rw [hCDS] at h
    exact (hI.decided_source id' b' (hCF ▸ hmem) h).imp (fun r' => hCert r' b')
  · intro r' b' hgr hbr
    obtain ⟨h1, h2, h3, h4⟩ := hI.grade2Lock_commit r' b' hgr hbr
    refine ⟨h1, fun r'' id' b'' hr hmem hcall => h2 r'' id' b'' hr (hCF ▸ hmem) hcall,
      fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem) (hCarr r' id0 v hcar)⟩
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround; exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    rw [hValeq] at hcoin; rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' id' hmem hcall
    rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · obtain ⟨hnone, hsome⟩ := hI.estimate_ret r id (hCF ▸ hmem) hr (Or.inl hph)
          by_cases hE : (c.processes id).estimate = none
          · exact Or.inr (hnone hE).1
          · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hE
            exact Or.inl (fun hemp => by
              have hm := hsome b hb
              rw [hemp] at hm
              simp at hm)
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [hWcalled id' hid] at hcalled
        exact hI.wcc_called r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled; exact hI.wcc_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [hValeq]; rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1, (hCprocs id').1]; exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGrade] at hlg
    exact (hI.grade2_source id' b' hlg).imp (fun r' => hCert r' b')
  · intro r' id' hmem hround hphase
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · have hround' : (c.processes id).round = r' := by
          rw [hid] at hround
          simpa [hc'eq, ABAState.setProcess_processes_self] using hround
        have hreq : r' = r := hround'.symm.trans hr
        rw [hid, hreq, (hCprocs id).2.1]
        exact hI.estimate_ret r id (hCF ▸ (hid ▸ hmem)) hr (Or.inl hph)
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        exact hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      exact hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
  · intro r' v h; rw [hValeq]; exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall; rw [hValeq]; exact hI.call_provenance r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest; rw [hValeq]
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid] at hphase
        simp only [hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h | h <;> simp at h
      · simp only [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [(hCprocs id').2.1]
        exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.1]
      exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
  · intro r' h; rw [hValeq] at h ⊢; exact hI.wcc_order r' h
  · intro id' b' h
    rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
    · left; rw [(hCprocs id').1]; exact hin
    · right; rw [hCF]; exact hf
  · -- `wcc_callRound`'s establishment: a correct caller of `WCC_r` just finished `GBCA_r`
    -- (`r ≤ round` from `hr : (c.processes id).round = r`, unaffected by `callW`).
    intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [hWcalled id' hid] at hcalled
        rw [(hCprocs id').2.2]; exact hI.wcc_callRound r id' (hCF ▸ hmem) hcalled
    · rw [hWNe r' h2] at hcalled
      rw [(hCprocs id').2.2]; exact hI.wcc_callRound r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rw [hValeq] at h
    rcases hI.flip_grade2Lock r' h with hg | hd
    · left; exact hg
    · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    by_cases h2 : r' = r
    · rw [h2, Function.update_self]
      rw [(hCprocs id').1] at hin
      by_cases hid : id' = id
      · exfalso
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rw [hid] at hin
          have hmem' : id ∉ c.F := by
            rw [← hCF, ← hid]; exact hmem
          exact absurd hin (hI.phase_input id hmem' (by rw [hph]; simp))
        · rw [hid] at hmem; exact hmem (hCF ▸ hF)
      · rw [hWcalled id' hid]
        exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r
    · rw [hWNe r' h2]
      rw [(hCprocs id').1] at hin
      exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hphaseImp : ((c'.processes id').phase = .toCallW ∨ (c'.processes id').phase = .awaitW) →
        ((c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW) := by
      intro hph2
      rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id' = id
        · exact Or.inl (hid ▸ hph)
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hph2; exact hph2
      · rw [hc'eq] at hph2; exact hph2
    have hp' : ((c.processes id').round = r' ∧
        ((c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW)) ∨
        r' < (c.processes id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · exact Or.inl ⟨hround, hphaseImp hphase⟩
      · exact Or.inr hlt
    rcases hI.retG_witness r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    by_cases h2 : r' = r
    · rw [h2] at hcalled ⊢
      simp only [Function.update_self] at hcalled
      by_cases hid : id' = id
      · rw [hid] at hmem
        rcases hCstep with ⟨hph, hr, hc'eq⟩ | ⟨hF, hc'eq⟩
        · rcases hI.retG_witness r id (hCF ▸ hmem) (Or.inl ⟨hr, Or.inl hph⟩) with hg | hd
          · left; exact hg
          · right
            exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
        · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [hWcalled id' hid] at hcalled
        rcases hI.wccCalled_witness r id' (hCF ▸ hmem) hcalled with hg | hd
        · left; exact hg
        · right
          exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd
    · rw [hWNe r' h2] at hcalled
      rcases hI.wccCalled_witness r' id' (hCF ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact DissentWitness.transport rfl rfl (fun h => h) (fun id' => (hCprocs id').1) hd

/-- `callW`, assembled from the three rows of `WCC.step_callW_inversion`. The loop and the
recording call leave `val` and `F` alone, so both are `Invariant.step_callW_dirac`. The resolving
call records `id` by that same bookkeeping and then writes the drawn outcome to `val`
(`Invariant.step_callW_resolve`); the two updates compose into one because `Function.update` is
idempotent at the round it writes. -/
theorem Invariant.step_callW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.callW r id) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.setProcess id { c.processes id with phase := .awaitW })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' (Function.update w r wr') ∧ AbstractStateUnchanged P g g c c' := by
  have hCstep : ((c.processes id).phase = .toCallW ∧ (c.processes id).round = r ∧
      c' = c.setProcess id { c.processes id with phase := .awaitW }) ∨ (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  rcases WCC.step_callW_inversion hstepW with rfl | ⟨-, -, rfl⟩ | ⟨-, hv, ht, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'
    exact hI.step_callW_dirac r id rfl rfl (fun _ _ => rfl) hCstep
  · rw [PMF.mem_support_pure_iff] at hwr'; subst hwr'
    exact hI.step_callW_dirac (wr' := (w r).record id) r id rfl rfl
      (fun j hj => WCC.SpecState.record_called_ne _ hj) hCstep
  · rw [PMF.mem_support_map_iff] at hwr'
    obtain ⟨o, -, rfl⟩ := hwr'
    obtain ⟨hI₁, hAF⟩ := hI.step_callW_dirac (wr' := (w r).record id) r id rfl rfl
      (fun j hj => WCC.SpecState.record_called_ne _ hj) hCstep
    refine ⟨?_, hAF⟩
    have hw₁ : Function.update w r ((w r).record id) r = (w r).record id := by
      rw [Function.update_self]
    have hres := hI₁.step_callW_resolve r (by rw [hw₁]; exact ht) (by rw [hw₁]; simpa using hv) o
    rw [hw₁, Function.update_idem] at hres
    exact hres
/-- `callG`: the GBCA instance only ever touches `.call` (never `.F`/`.excluded`/`.grade`), the
core only ever touches `.phase` at `id` (never `.input`/`.estimate`/`.round`). `input_gbcaRound0`/
`input_called`'s correct-fresh-call corner needs "`estimate = input` before any round-`0` return"
(phase/input coherence, not an explicit `Invariant` conjunct) — handed off; `grade2Lock_commit`'s
second conjunct is derived cleanly from its own third conjunct plus the correct call guard
`estimate = b`. -/
theorem Invariant.step_callG {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μr : PMF (GBCA.SpecState P.n)} (hstepG : GBCA.Step P r (g r) (.callG r id b) μr)
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .toCallG ∧ (c.processes id).round = r ∧
          (c.processes id).estimate = some b ∧
          μc = PMF.pure (c.setProcess id { c.processes id with phase := .awaitG })) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {gr' : GBCA.SpecState P.n} (hgr' : gr' ∈ μr.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P (Function.update g r gr') c' w ∧
      AbstractStateUnchanged P g (Function.update g r gr') c c' := by
  have hGframe : gr'.F = (g r).F ∧ gr'.excluded = (g r).excluded ∧ gr'.grade = (g r).grade := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact ⟨rfl, rfl, rfl⟩
  have hGeq : ∀ r', r' ≠ r → Function.update g r gr' r' = g r' := fun r' h =>
    Function.update_of_ne h gr' g
  have hFgeq : ∀ r', (Function.update g r gr' r').F = (g r').F := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.1
    · rw [hGeq r' h]
  have hBindeq : ∀ r', (Function.update g r gr' r').excluded = (g r').excluded := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.1
    · rw [hGeq r' h]
  have hGradeeq : ∀ r', (Function.update g r gr' r').grade = (g r').grade := by
    intro r'; by_cases h : r' = r
    · subst h; rw [Function.update_self]; exact hGframe.2.2
    · rw [hGeq r' h]
  have hCframe : c'.F = c.F ∧ c'.decidedSent = c.decidedSent ∧ c'.decidedReceived =
    c.decidedReceived ∧
      ∀ id',
        (c'.processes id').input = (c.processes id').input ∧ (c'.processes id').estimate =
          (c.processes id').estimate ∧ (c'.processes id').round = (c.processes id').round := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      refine ⟨ABAState.setProcess_F _ _ _, ABAState.setProcess_decidedSent _ _ _,
        ABAState.setProcess_decidedReceived _ _ _, fun id' => ?_⟩
      by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]; exact ⟨rfl, rfl, rfl⟩
      · rw [ABAState.setProcess_processes_ne _ _ _ h]; exact ⟨rfl, rfl, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
      exact ⟨rfl, rfl, rfl, fun id' => ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨hCF, hCDS, hCDR, hCprocs⟩ := hCframe
  -- The one fact needing case analysis: `gr'.call`, as an unconditional description
  -- (`Or.inl`: a fresh correct/byzantine `call` at `id`; `Or.inr`: `callLoop`, unaffected).
  have hGcall : (gr' = { g r with call := Function.update (g r).call id (some b) }) ∨
      gr' = g r := by
    cases hstepG with
    | call h => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inl hgr'
    | callLoop => rw [PMF.mem_support_pure_iff] at hgr'; exact Or.inr hgr'
  have hCcall : ((c.processes id).phase = .toCallG ∧ (c.processes id).round = r ∧
      (c.processes id).estimate = some b ∧
      c' = c.setProcess id { c.processes id with phase := .awaitG }) ∨ (id ∈ c.F ∧ c' = c) := by
    rcases hstepC with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inl ⟨hph, hr, hest, hc'⟩
    · rw [PMF.mem_support_pure_iff] at hc'; exact Or.inr ⟨hF, hc'⟩
  -- Every fresh call of a correct process, at any `id'` and any round `r'`, agrees with
  -- `estimate` at that `id'`.
  have hGcallval : ∀ id' b', gr'.call id' = some b' → id' ≠ id → (g r).call id' = some b' := by
    rcases hGcall with rfl | rfl
    · intro id' b' h hne; simpa [Function.update_of_ne hne] using h
    · intro id' b' h _; exact h
  -- `call` entries are write-once (`Step.call` fires only on an empty entry), so a fresh call
  -- only ever adds to a support count.
  have hCallMono : ∀ id' b', (g r).call id' = some b' → gr'.call id' = some b' := by
    cases hstepG with
    | call _ _ hfresh =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'
      intro id' b' h'
      show Function.update (g r).call id (some b) id' = some b'
      by_cases hid : id' = id
      · rw [hid] at h'; rw [hfresh] at h'; simp at h'
      · rw [Function.update_of_ne hid]; exact h'
    | callLoop =>
      rw [PMF.mem_support_pure_iff] at hgr'; subst hgr'; exact fun _ _ h => h
  have hGcallSelf : gr'.call id = some b ∨ gr' = g r := by
    rcases hGcall with rfl | rfl
    · left; simp
    · right; rfl
  have hPhaseNe : ∀ id', id' ≠ id → (c'.processes id').phase = (c.processes id').phase := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id' hne; rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hne]
    · intro id' _; rw [hc'eq]
  have hLastGradeG : ∀ id', (c'.processes id').lastGrade = (c.processes id').lastGrade := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · intro id'; rw [hc'eq]; by_cases h : id' = id
      · subst h; rw [ABAState.setProcess_processes_self]
      · rw [ABAState.setProcess_processes_ne _ _ _ h]
    · intro id'; rw [hc'eq]
  have hCarrTrans : ∀ r₀ id₀ v, id₀ ∉ c.F →
      OutcomeHolder P (Function.update g r gr') c' r₀ id₀ v → OutcomeHolder P g c r₀ id₀ v := by
    intro r₀ id₀ v hmem0 hc0
    rcases hc0 with h | ⟨he, hk⟩
    · by_cases h1 : r₀ + 1 = r
      · rw [h1, Function.update_self] at h
        by_cases hid : id₀ = id
        · subst hid
          rcases hGcallSelf with hself | hself
          · rw [hself, Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
            · exact Or.inr ⟨by rw [hest, h], Or.inr ⟨by rw [hr, h1], Or.inr (Or.inl hph)⟩⟩
            · exact absurd hF hmem0
          · rw [hself] at h
            exact Or.inl (by rw [h1]; exact h)
        · have := hGcallval id₀ v h hid
          exact Or.inl (by rw [h1]; exact this)
      · rw [hGeq (r₀ + 1) h1] at h; exact Or.inl h
    · refine Or.inr ⟨(hCprocs id₀).2.1 ▸ he, ?_⟩
      rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨-, hc'eq⟩
      · by_cases hid : id₀ = id
        · subst hid
          rw [hc'eq, ABAState.setProcess_processes_self] at hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · exact Or.inr ⟨hr0, Or.inr (Or.inl hph)⟩
        · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hk
          exact hk
      · rw [hc'eq] at hk; exact hk
  have hCommitTrans : ∀ r0 b0, Grade2Commitment P g c r0 b0 →
      Grade2Commitment P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨h1, h2, h3, h4⟩
    refine ⟨fun r'' b'' hrr' hbind =>
        h1 r'' b'' hrr' (by rw [← hBindeq r'']; exact hbind),
      fun r'' id' b'' hrr' hmem hcall => ?_, fun id' hmem hround => ?_,
      fun id0 v hmem hcar => h4 id0 v (hCF ▸ hmem)
        (hCarrTrans r0 id0 v (hCF ▸ hmem) hcar)⟩
    · by_cases hrr : r'' = r
      · rw [hrr, Function.update_self] at hcall
        by_cases hid : id' = id
        · rw [hid] at hcall hmem
          rcases hGcallSelf with hself | hself
          · rw [hself] at hcall; rw [Option.some_inj] at hcall
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · have hh3 := h3 id (hCF ▸ hmem) (by rw [hr, ← hrr]; exact hrr')
              rw [hest] at hh3; rw [Option.some_inj] at hh3
              rw [← hcall, hh3]
            · exact absurd (hCF ▸ hmem) (not_not.mpr hF)
          · rw [hself] at hcall
            exact h2 r'' id b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact hcall)
        · have := hGcallval id' b'' hcall hid
          exact h2 r'' id' b'' hrr' (hCF ▸ hmem) (by rw [hrr]; exact this)
      · rw [hGeq r'' hrr] at hcall
        exact h2 r'' id' b'' hrr' (hCF ▸ hmem) hcall
    · rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]; exact h3 id' (hCF ▸ hmem) hround
  have hCertTrans : ∀ r0 b0, Grade2Certificate P g c r0 b0 →
      Grade2Certificate P (Function.update g r gr') c' r0 b0 := by
    rintro r0 b0 ⟨hg1, hd1, hcm⟩
    exact ⟨by rw [hGradeeq]; exact hg1, by rw [hBindeq]; exact hd1, hCommitTrans r0 b0 hcm⟩
  have hHold : ∀ i0 b0, Grade2Holder P c' i0 b0 → Grade2Holder P c i0 b0 := by
    intro i0 b0 h
    unfold Grade2Holder at h ⊢
    rwa [hLastGradeG, hCDS] at h
  refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertTrans r0 b0 hc⟩,
    fun v _ hpin j b' hj hh => hpin j b' (hCF ▸ hj) (hHold j b' hh)⟩
  have hCcorr : c'.corrupted = c.corrupted := by
    rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · rw [hc'eq]; exact ABAState.setProcess_corrupted _ _ _
    · rw [hc'eq]
  refine ⟨fun id' => by rw [hCcorr, hCF]; exact hI.corrupted_F id',
    fun r' => (hFgeq r').trans (hCF ▸ hI.F_gbca r'), fun r' => hCF ▸ hI.F_wcc r',
    hCF ▸ hI.F_card,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun r' h => by rw [hGradeeq] at h ⊢; exact hI.grade0Lock_chain r' h, ?_,
    hI.wcc_order, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r' v hb => (hI.bind_support r' v (by rw [← hBindeq r']; exact hb)).mono
      (fun id' b' h => by rw [(hCprocs id').1]; exact h) (fun x hx => by rw [hCF]; exact hx),
    fun r' b' hgf => GBCA.callSupport_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' b' h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.grade0Lock_support r' b' ((hGradeeq r').symm.trans hgf)),
    fun r' b0 hbd => GBCA.callSupport_mono
      (fun id' h => by
        by_cases hrr : r' = r
        · subst hrr; rw [Function.update_self]; exact hCallMono id' (!b0) h
        · rw [hGeq r' hrr]; exact h)
      (hFgeq r').ge (hI.excluded_support r' b0 (by rw [← hBindeq r']; exact hbd)),
    fun r₀ i0 j0 v v' hm hm' h h' => (hI.outcomeHolder_agree r₀ i0 j0 v v' (hCF ▸ hm) (hCF ▸ hm')
      (hCarrTrans r₀ i0 v (hCF ▸ hm) h) (hCarrTrans r₀ j0 v' (hCF ▸ hm') h')).imp
      (fun x => x) (fun hh => (hGradeeq r₀).trans hh),
    fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hCF ▸ hm) (hCF ▸ hm')
      (hHold _ _ h) (hHold _ _ h')⟩
  · -- input_gbcaRound0
    intro id' b' hmem hcall
    rw [(hCprocs id').1]
    by_cases hr0 : r = 0
    · rw [hr0, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself] at hcall; rw [Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · rw [hid]
            have hmem' : id ∉ c.F := by
              rw [← hCF, ← hid]; exact hmem
            have he0 := hI.estimate0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
            rw [← he0, hest, hcall]
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself, hr0] at hcall
          rw [hid] at hmem ⊢
          exact hI.input_gbcaRound0 id b' (hCF ▸ hmem) hcall
      · have := hGcallval id' b' hcall hid
        rw [hr0] at this
        exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem) this
    · rw [hGeq 0 (Ne.symm hr0)] at hcall
      exact hI.input_gbcaRound0 id' b' (hCF ▸ hmem) hcall
  · -- input_called
    intro r' id' hmem hcall
    rw [(hCprocs id').1]
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid] at hcall ⊢
        rcases hGcallSelf with hself | hself
        · rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
          · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
            exact hI.phase_input id hmem' (by rw [hph]; simp)
          · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
        · rw [hself] at hcall; rw [hid] at hmem; exact hI.input_called r id (hCF ▸ hmem) hcall
      · rcases hGcall with hgeq | hgeq
        · rw [hgeq] at hcall; simp only [Function.update_of_ne hid] at hcall
          exact hI.input_called r id' (hCF ▸ hmem) hcall
        · rw [hgeq] at hcall; exact hI.input_called r id' (hCF ▸ hmem) hcall
    · rw [hGeq r' hrr] at hcall
      exact hI.input_called r' id' (hCF ▸ hmem) hcall
  · -- phase_input
    intro id' hmem hne
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid, (hCprocs id).1]
        have hmem' : id ∉ c.F := by
          rw [← hCF, ← hid]; exact hmem
        exact hI.phase_input id hmem' (by rw [hph]; simp)
      · rw [(hCprocs id').1]
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hne
        exact hI.phase_input id' (hCF ▸ hmem) hne
    · rw [hc'eq] at hne
      rw [(hCprocs id').1]
      exact hI.phase_input id' (hCF ▸ hmem) hne
  · -- down_settled
    intro r' h
    rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]
    exact hI.down_settled r' ((RoundSettled.congr (hBindeq (r' + 1)) (hGradeeq (r' + 1))).mp h)
  · -- quiescent
    obtain ⟨R, hR⟩ := hI.quiescent
    exact ⟨R, fun r' hr' h => hR r' hr' ((RoundSettled.congr (hBindeq r') (hGradeeq r')).mp h)⟩
  · -- wcc_bound
    intro r' h; rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]; exact hI.wcc_bound r' h
  · intro i j b' h; rw [hCDR] at h; rw [hCDS]; exact hI.received_sound i j b' h
  · intro id' b' hmem h
    rw [hCDS] at h
    exact (hI.decided_source id' b' (hCF ▸ hmem) h).imp (fun r0 => hCertTrans r0 b')
  · intro r0 b0 hgr hbr
    rw [hGradeeq] at hgr; rw [hBindeq] at hbr
    exact hCommitTrans r0 b0 (hI.grade2Lock_commit r0 b0 hgr hbr)
  · intro id' hmem r' hround
    rw [(hCprocs id').2.2] at hround
    rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]
    exact hI.round_bound id' (hCF ▸ hmem) r' hround
  · intro r' v hlast hbr hcoin id' hmem hround
    have hlast' : IsLastBound g r' := ⟨fun h => hlast.1 (by rw [hBindeq]; exact h),
      by rw [← hBindeq (r' + 1)]; exact hlast.2⟩
    rw [hBindeq] at hbr
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1]
    exact hI.agree_locked r' v hlast' hbr hcoin id' (hCF ▸ hmem) hround
  · intro r' h; rw [hGradeeq] at h; rw [hBindeq]; exact hI.grade2_needs_bind r' h
  · intro r' id' hmem hcall
    by_cases hrr : r' = r
    · rw [hrr, Function.update_self] at hcall
      by_cases hid : id' = id
      · rw [hid, (hCprocs id).2.2]
        rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
        · omega
        · rw [hid] at hmem; exact absurd (hCF ▸ hmem) (not_not.mpr hF)
      · rw [(hCprocs id').2.2]
        obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hcall
        have hcv := hGcallval id' b' hb' hid
        rw [hrr]
        exact hI.call_round r id' (hCF ▸ hmem) (by rw [hcv]; simp)
    · rw [hGeq r' hrr] at hcall
      rw [(hCprocs id').2.2]; exact hI.call_round r' id' (hCF ▸ hmem) hcall
  · intro r' id' hmem hcalled
    rw [RoundSettled.congr (hBindeq r') (hGradeeq r')]
    exact hI.wcc_called r' id' (hCF ▸ hmem) hcalled
  · intro r' id' hmem hround
    rw [(hCprocs id').2.2] at hround
    exact hI.round_flip r' id' (hCF ▸ hmem) hround
  · intro id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · have hmem' : id ∉ c.F := by rw [← hCF, ← hid]; exact hmem
        rw [hid, (hCprocs id).2.2] at hround
        rw [hid, (hCprocs id).1, (hCprocs id).2.1]
        exact hI.estimate0 id hmem' hround (Or.inr (Or.inl hph))
      · rw [(hCprocs id').2.2] at hround
        rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        rw [(hCprocs id').1, (hCprocs id').2.1]
        exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      rw [(hCprocs id').2.2] at hround
      rw [(hCprocs id').1, (hCprocs id').2.1]
      exact hI.estimate0 id' (hCF ▸ hmem) hround hphase
  · intro id' b' hlg
    rw [hLastGradeG] at hlg
    exact (hI.grade2_source id' b' hlg).imp (fun r0 => hCertTrans r0 b')
  · intro r' id' hmem hround hphase
    rcases hCcall with ⟨hph, hr, hest, hc'eq⟩ | ⟨hF, hc'eq⟩
    · by_cases hid : id' = id
      · exfalso
        rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
        rcases hphase with h | h <;> simp at h
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hround hphase
        rw [(hCprocs id').2.1]
        obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
        refine ⟨fun he => ?_, fun b hb => ?_⟩
        · obtain ⟨hg0, hno⟩ := hnone he
          refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
          rw [hGradeeq] at hgr0
          exact hno r₀ hr0 hgr0
        · rw [hBindeq]; exact hsome b hb
    · rw [hc'eq] at hround hphase
      rw [(hCprocs id').2.1]
      obtain ⟨hnone, hsome⟩ := hI.estimate_ret r' id' (hCF ▸ hmem) hround hphase
      refine ⟨fun he => ?_, fun b hb => ?_⟩
      · obtain ⟨hg0, hno⟩ := hnone he
        refine ⟨by rw [hGradeeq]; exact hg0, fun r₀ hr0 hgr0 => ?_⟩
        rw [hGradeeq] at hgr0
        exact hno r₀ hr0 hgr0
      · rw [hBindeq]; exact hsome b hb
  · intro r' v h
    rw [hBindeq] at h; rw [hBindeq r', hGradeeq r']
    exact hI.bind_succ r' v h
  · intro r' id' v hmem hcall
    by_cases h1 : r' + 1 = r
    · by_cases hid : id' = id
      · rw [hid] at hcall hmem
        rw [h1, Function.update_self] at hcall
        rcases hGcallSelf with hself | hself
        · rw [hself, Option.some_inj] at hcall
          rcases hCcall with ⟨hph, hr, hest, -⟩ | ⟨hF, -⟩
          · have hround : (c.processes id).round = r' + 1 := by rw [hr, h1]
            have hep := hI.estimate_previous r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) b hest
            rw [hBindeq r', hGradeeq r']
            rwa [hcall] at hep
          · exact absurd hF (hCF ▸ hmem)
        · rw [hself] at hcall
          rw [hBindeq r', hGradeeq r']
          exact hI.call_provenance r' id v (hCF ▸ hmem) (by rw [h1]; exact hcall)
      · rw [h1, Function.update_self] at hcall
        have hcv := hGcallval id' v hcall hid
        rw [hBindeq r', hGradeeq r']
        exact hI.call_provenance r' id' v (hCF ▸ hmem) (by rw [h1]; exact hcv)
    · rw [hGeq (r' + 1) h1] at hcall
      rw [hBindeq r', hGradeeq r']
      exact hI.call_provenance r' id' v (hCF ▸ hmem) hcall
  · intro r' id' hmem hround hphase v hest
    rw [(hCprocs id').2.2] at hround; rw [(hCprocs id').2.1] at hest
    rw [hBindeq r', hGradeeq r']
    rcases hCcall with ⟨hph, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround hest
        exact hI.estimate_previous r' id (hCF ▸ hmem) hround (Or.inr (Or.inl hph)) v hest
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
    · rw [hc'eq] at hphase
      exact hI.estimate_previous r' id' (hCF ▸ hmem) hround hphase v hest
  · intro id' hmem hround hphase
    rw [(hCprocs id').2.2] at hround
    rw [(hCprocs id').2.1]
    rcases hCcall with ⟨hph, hr, -, hc'eq⟩ | ⟨-, hc'eq⟩
    · by_cases hid : id' = id
      · rw [hid] at hmem hround ⊢
        exact hI.estimate_previous_ne id (hCF ▸ hmem) hround (Or.inr (Or.inl hph))
      · rw [hc'eq, ABAState.setProcess_processes_ne _ _ _ hid] at hphase
        exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
    · rw [hc'eq] at hphase
      exact hI.estimate_previous_ne id' (hCF ▸ hmem) hround hphase
  · -- `input_gbcaRound0_permanent`: mirrors `input_gbcaRound0`'s establishment
    -- above, with an `id' ∈ F` escape hatch replacing the correctness hypothesis.
    intro id' b' h
    by_cases hmem : id' ∈ c.F
    · right; rw [hCF]; exact hmem
    · left
      rw [(hCprocs id').1]
      by_cases hr0 : r = 0
      · rw [hr0, Function.update_self] at h
        by_cases hid : id' = id
        · rw [hid] at h
          rcases hGcallSelf with hself | hself
          · rw [hself] at h; rw [Option.some_inj] at h
            rcases hCcall with ⟨hph, hr, hest, rfl⟩ | ⟨hF, rfl⟩
            · rw [hid]
              have hmem' : id ∉ c.F := by
                rw [hid] at hmem; exact hmem
              have he0 := hI.estimate0 id hmem' (hr.trans hr0) (Or.inr (Or.inl hph))
              rw [← he0, hest, h]
            · rw [hid] at hmem; exact absurd hF hmem
          · rw [hself, hr0] at h
            rw [hid] at hmem ⊢
            rcases hI.input_gbcaRound0_permanent id b' h with hin | hf
            · exact hin
            · exact absurd hf hmem
        · have hcv := hGcallval id' b' h hid
          rw [hr0] at hcv
          rcases hI.input_gbcaRound0_permanent id' b' hcv with hin | hf
          · exact hin
          · exact absurd hf hmem
      · rw [hGeq 0 (Ne.symm hr0)] at h
        rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
        · exact hin
        · exact absurd hf hmem
  · intro r' id' hmem hcalled
    rw [(hCprocs id').2.2]; exact hI.wcc_callRound r' id' (hCF ▸ hmem) hcalled
  · intro r' h
    rcases hI.flip_grade2Lock r' h with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro id' hmem hin r'
    rw [(hCprocs id').1] at hin; exact hI.idle_no_wccCall id' (hCF ▸ hmem) hin r'
  · intro r' id' hmem hp
    rw [(hCprocs id').2.2] at hp
    have hp' : ((c.processes id').round = r' ∧
        ((c.processes id').phase = .toCallW ∨ (c.processes id').phase = .awaitW)) ∨
        r' < (c.processes id').round := by
      rcases hp with ⟨hround, hphase⟩ | hlt
      · refine Or.inl ⟨hround, ?_⟩
        by_cases hid : id' = id
        · rcases hCcall with ⟨-, -, -, hc'eq⟩ | ⟨-, hc'eq⟩
          · exfalso
            rw [hid, hc'eq, ABAState.setProcess_processes_self] at hphase
            rcases hphase with h | h <;> simp at h
          · rw [hid]
            rw [hid, hc'eq] at hphase
            exact hphase
        · rwa [hPhaseNe id' hid] at hphase
      · exact Or.inr hlt
    rw [hGradeeq]
    rcases hI.retG_witness r' id' (hCF ▸ hmem) hp' with hg | hd
    · left; exact hg
    · right; exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' id' hmem hcalled
    rcases hI.wccCalled_witness r' id' (hCF ▸ hmem) hcalled with hg | hd
    · left; rw [hGradeeq]; exact hg
    · right
      exact DissentWitness.transport (hBindeq r') (hBindeq (r' - 1))
        (fun h => (hGradeeq (r' - 1)) ▸ h) (fun id' => (hCprocs id').1) hd
  · intro r' h
    rw [hBindeq] at h
    refine GBCA.SpecState.quorum_mono (hFgeq r').ge (fun id' hne => ?_) (hI.bound_quorum r' h)
    by_cases hrr : r' = r
    · rw [hrr] at hne ⊢
      rw [Function.update_self]
      rcases hGcall with hg | hg
      · rw [hg]
        show Function.update (g r).call id (some b) id' ≠ none
        by_cases hid : id' = id
        · rw [hid, Function.update_self]; simp
        · rw [Function.update_of_ne hid]; exact hne
      · rw [hg]; exact hne
    · rw [hGeq r' hrr]; exact hne

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

/-- `retG`: the GBCA instance only ever touches `.grade`/`.ret` (never `.F`/`.excluded`/`.call`;
`.ret` isn't inspected by `Invariant`), the core only ever touches `.estimate`/`.lastGrade`/`.phase`
at `id` (never `.round`/`.input`). The genuinely hard obligations — `grade2Lock_commit`'s *new*
round-`r` commitment and `agree_locked`'s est-transfer at `id` — are handed off; they need
GBCA's own Graded-Agreement safety property, not local bookkeeping. -/
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

/-- `retW`: `g` is untouched entirely; the WCC instance only touches `.ret` (not inspected by
`Invariant`); the core's `stepRound` touches `estimate`/`lastGrade`/`round`/`phase` at `id` and
conditionally `decidedSent id` (on a grade-2). `round_bound`'s freshly-included round is
covered by `wcc_bound` (the coin having resolved closes the round); the DECIDED-on-grade-2
witness for `decided_source`, and the `grade2Lock_commit`/`agree_locked` extension to `id`'s new
round, need the cross-round `lastGrade`-to-`(g r).grade/.excluded` correlation (GBCA Graded
Agreement) that isn't a local `Invariant` consequence — handed off. -/
theorem Invariant.step_retW {P : Parameters} {g : ℕ → GBCA.SpecState P.n} {c : ABAState P}
    {w : ℕ → WCC.SpecState P.n} (hI : Invariant P g c w) (r : ℕ) (id : Fin P.n) (b : Bool)
    {μw' : PMF (WCC.SpecState P.n)} (hstepW : WCC.Step P r (w r) (.retW r id b) μw')
    {μc : PMF (ABAState P)}
    (hstepC :
      ((c.processes id).phase = .awaitW ∧ (c.processes id).round = r ∧
          μc = PMF.pure (c.stepRound id b)) ∨
        (id ∈ c.F ∧ μc = PMF.pure c))
    {wr' : WCC.SpecState P.n} (hwr' : wr' ∈ μw'.support)
    {c' : ABAState P} (hc' : c' ∈ μc.support) :
    Invariant P g c' (Function.update w r wr') ∧ AbstractStateUnchanged P g g c c' := by
  have hWeq : (Function.update w r wr' r).F = (w r).F ∧
      (Function.update w r wr' r).val = (w r).val := by
    rw [Function.update_self]; cases hstepW with
    | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']; exact ⟨rfl, rfl⟩
  have hWNe : ∀ r', r' ≠ r → Function.update w r wr' r' = w r' := fun r' h =>
    Function.update_of_ne h wr' w
  have hFweq : ∀ r', (Function.update w r wr' r').F = (w r').F := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.1
    · rw [hWNe r' h]
  have hValeq : ∀ r', (Function.update w r wr' r').val = (w r').val := by
    intro r'; by_cases h : r' = r
    · rw [h]; exact hWeq.2
    · rw [hWNe r' h]
  have hWval : (w r).val ≠ .bot := by
    cases hstepW with
    | ret _ _ h1 _ => rcases h1 with h1 | h1 <;> rw [h1] <;> simp
  have hCoinEq : ∀ v', (w r).val = .bit v' → b = v' := by
    cases hstepW with
    | ret _ _ h1 _ =>
      intro v' hv'
      rcases h1 with h1 | h1
      · rw [h1] at hv'; simp at hv'
      · rw [h1] at hv'; simpa using hv'
  have hCalledEq : ∀ r', (Function.update w r wr' r').called = (w r').called := by
    intro r'; by_cases h : r' = r
    · rw [h, Function.update_self]
      cases hstepW with
      | ret _ _ _ _ => rw [PMF.mem_support_pure_iff] at hwr'; rw [hwr']
    · rw [hWNe r' h]
  rcases hstepC with ⟨hph, hr, rfl⟩ | ⟨hF, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hc'
    have hFeq : (c.stepRound id b).F = c.F := ABAState.stepRound_F _ _ _
    have hDReq : (c.stepRound id b).decidedReceived = c.decidedReceived :=
      ABAState.stepRound_decidedReceived _ _ _
    have hProcNe : ∀ id', id' ≠ id → (c.stepRound id b).processes id' = c.processes id' := by
      intro id' h; exact ABAState.stepRound_processes_ne _ _ _ h
    have hProcSelf : (c.stepRound id b).processes id = { c.processes id with
        estimate := some ((c.processes id).estimate.getD b), lastGrade := none,
        round := (c.processes id).round + 1,
          phase := .toCallG } := ABAState.stepRound_processes_self _ _ _
    have hInputEq : ((c.stepRound id b).processes id).input = (c.processes id).input := by
      rw [hProcSelf]
    have hRoundEq : ((c.stepRound id b).processes id).round = (c.processes id).round + 1 := by
      rw [hProcSelf]
    have hDSeq : (c.stepRound id b).decidedSent = c.decidedSent ∨
        ∃ b0, (c.processes id).lastGrade = some (.grade2 b0) ∧
          (c.stepRound id b).decidedSent =
            Function.update c.decidedSent id (insert b0 (c.decidedSent id)) := by
      by_cases hA : ∃ b0, (c.processes id).lastGrade = some (.grade2 b0)
      · obtain ⟨b0, hlg⟩ := hA
        exact Or.inr ⟨b0, hlg, ABAState.stepRound_decidedSent_of_grade2 c id b b0 hlg⟩
      · exact Or.inl (ABAState.stepRound_decidedSent_of_not_grade2 c id b (fun b1 heq => hA ⟨b1,
          heq⟩))
    have hDR2 : ∀ r', DissentWitness P g c r' → DissentWitness P g (c.stepRound id b) r' := by
      intro r' hd
      refine DissentWitness.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
      by_cases hid2 : id2 = id
      · rw [hid2]; exact hInputEq
      · rw [hProcNe id2 hid2]
    -- OutcomeHolder reduction: a post-`stepRound` carrier is an old one or `id`, now holding the
    -- adopted estimate at the finished round `r`.
    have hRedW : ∀ r₀ i1 v1, OutcomeHolder P g (c.stepRound id b) r₀ i1 v1 →
        OutcomeHolder P g c r₀ i1 v1 ∨ (i1 = id ∧ r₀ = r ∧ (c.processes id).estimate.getD b = v1) :=
          by
      intro r₀ i1 v1 hc1
      rcases hc1 with hcall | ⟨he, hk⟩
      · exact Or.inl (Or.inl hcall)
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at he hk
          rcases hk with ⟨-, hp | hp⟩ | ⟨hr0, -⟩
          · exact absurd hp (by simp)
          · exact absurd hp (by simp)
          · have hr0' : (c.processes id).round + 1 = r₀ + 1 := by simpa using hr0
            exact Or.inr ⟨hid1, by omega, Option.some_inj.mp he⟩
        · rw [hProcNe i1 hid1] at he hk
          exact Or.inl (Or.inr ⟨he, hk⟩)
    have hIdCarr : ∀ bv, (c.processes id).estimate = some bv → OutcomeHolder P g c r id bv :=
      fun bv hoe => Or.inr ⟨hoe, Or.inl ⟨hr, Or.inr hph⟩⟩
    have hCommitW : ∀ r0 b0, (g r0).grade = some true → Grade2Commitment P g c r0 b0 →
        Grade2Commitment P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 hg0 ⟨h1, h2, h3, h4⟩
      refine ⟨h1, fun r' id' b'' hrr' hmem hcall => h2 r' id' b'' hrr' (hFeq ▸ hmem) hcall,
        fun id' hmem hround => ?_, fun id0 v hmem hcar => ?_⟩
      · by_cases hid : id' = id
        · rw [hid, hRoundEq] at hround
          by_cases hle : r0 < (c.processes id).round
          · have hold := h3 id (hFeq ▸ (hid ▸ hmem)) hle
            rw [hid]; simp [hold]
          · have hr0r : r0 = r := (by omega : r0 = (c.processes id).round).trans hr
            rw [hid]; simp only [hProcSelf]
            rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
            · exfalso
              obtain ⟨hg0', -⟩ :=
                (hI.estimate_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)).1 hoe
              rw [hr0r] at hg0
              exact absurd (hg0.symm.trans hg0') (by simp)
            · have hbv0 : bv = b0 :=
                h4 id bv (hFeq ▸ (hid ▸ hmem)) (hr0r ▸ hIdCarr bv hoe)
              simp [hoe, hbv0]
        · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
          exact h3 id' (hFeq ▸ hmem) hround
      · rcases hRedW r0 id0 v hcar with hold | ⟨heq0, hreq, hev⟩
        · exact h4 id0 v (hFeq ▸ hmem) hold
        · rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
          · obtain ⟨hg0', -⟩ :=
              (hI.estimate_ret r id (hFeq ▸ (heq0 ▸ hmem)) hr (Or.inr hph)).1 hoe
            rw [hreq] at hg0
            exact absurd (hg0.symm.trans hg0') (by simp)
          · have hv : v = bv := by rw [hoe] at hev; simpa using hev.symm
            rw [hv]
            exact h4 id bv (hFeq ▸ (heq0 ▸ hmem)) (hreq ▸ hIdCarr bv hoe)
    have hCertW : ∀ r0 b0,
        Grade2Certificate P g c r0 b0 → Grade2Certificate P g (c.stepRound id b) r0 b0 := by
      rintro r0 b0 ⟨hg0, hres0, hcm⟩
      exact ⟨hg0, hres0, hCommitW r0 b0 hg0 hcm⟩
    have hRedHW : ∀ i1 b1, Grade2Holder P (c.stepRound id b) i1 b1 → Grade2Holder P c i1 b1 := by
      intro i1 b1 h1
      rcases h1 with h1 | h1
      · by_cases hid1 : i1 = id
        · rw [hid1, hProcSelf] at h1; simp at h1
        · rw [hProcNe i1 hid1] at h1; exact Or.inl h1
      · rcases hDSeq with heq | ⟨b2, hlg, heq⟩
        · rw [heq] at h1; exact Or.inr h1
        · rw [heq] at h1
          by_cases hid1 : i1 = id
          · subst hid1
            rw [Function.update_self, Finset.mem_insert] at h1
            rcases h1 with rfl | h1
            · exact Or.inl hlg
            · exact Or.inr h1
          · rw [Function.update_of_ne hid1] at h1
            exact Or.inr h1
    rw [hc']
    refine And.intro ?_ ⟨fun r0 b0 hc => ⟨r0, hCertW r0 b0 hc⟩,
      fun v _ hpin j b' hj hh => hpin j b' (hFeq ▸ hj) (hRedHW j b' hh)⟩
    refine ⟨fun id' => by
        rw [ABAState.stepRound_corrupted, hFeq]; exact hI.corrupted_F id',
      fun r' => hFeq ▸ hI.F_gbca r', fun r' => (hFweq r').trans (hFeq ▸ hI.F_wcc r'),
      hFeq ▸ hI.F_card, ?_, ?_, ?_, hI.down_settled, hI.quiescent,
      fun r' h => hI.wcc_bound r' (by rw [← hValeq r']; exact h),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.grade0Lock_chain, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.bound_quorum,
      fun r' v hb2 => (hI.bind_support r' v hb2).mono
        (fun id2 b2 h => by
          by_cases hid2 : id2 = id
          · rw [hid2, hInputEq]; exact hid2 ▸ h
          · rw [hProcNe id2 hid2]; exact h)
        (fun x hx => by rw [hFeq]; exact hx),
      hI.grade0Lock_support, hI.excluded_support,
      fun r₀ i0 j0 v v' hm hm' h h' => by
        rcases hRedW r₀ i0 v h with hold0 | ⟨heq0, hreq0, hev0⟩
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · exact hI.outcomeHolder_agree r₀ i0 j0 v v' (hFeq ▸ hm) (hFeq ▸ hm') hold0 hold1
          · rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.estimate_ret r id (hFeq ▸ (heq1 ▸ hm')) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq1]; exact hg0)
            · have hv' : v' = bv := by rw [hoe] at hev1; simpa using hev1.symm
              rw [hv']
              exact hI.outcomeHolder_agree r₀ i0 id v bv (hFeq ▸ hm) (hFeq ▸ (heq1 ▸ hm')) hold0
                (hreq1 ▸ hIdCarr bv hoe)
        · rcases hRedW r₀ j0 v' h' with hold1 | ⟨heq1, hreq1, hev1⟩
          · rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
            · obtain ⟨hg0, -⟩ :=
                (hI.estimate_ret r id (hFeq ▸ (heq0 ▸ hm)) hr (Or.inr hph)).1 hoe
              exact Or.inr (by rw [hreq0]; exact hg0)
            · have hv0 : v = bv := by rw [hoe] at hev0; simpa using hev0.symm
              rw [hv0]
              exact hI.outcomeHolder_agree r₀ id j0 bv v' (hFeq ▸ (heq0 ▸ hm)) (hFeq ▸ hm')
                (hreq0 ▸ hIdCarr bv hoe) hold1
          · exact Or.inl (hev0.symm.trans hev1),
      fun i0 j0 b0 b0' hm hm' h h' => hI.grade2Lock_agree i0 j0 b0 b0' (hFeq ▸ hm) (hFeq ▸ hm')
        (hRedHW i0 b0 h) (hRedHW j0 b0' h')⟩
    · intro id' b' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_gbcaRound0 id b' (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_gbcaRound0 id' b' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h] at hmem hcall; rw [h, hInputEq]
        exact hI.input_called r' id (hFeq ▸ hmem) hcall
      · rw [hProcNe id' h]; exact hI.input_called r' id' (hFeq ▸ hmem) hcall
    · intro id' hmem hne
      by_cases h : id' = id
      · rw [h, hInputEq]; rw [h] at hmem
        exact hI.phase_input id (hFeq ▸ hmem) (by rw [hph]; simp)
      · rw [hProcNe id' h] at hne ⊢
        exact hI.phase_input id' (hFeq ▸ hmem) hne
    · intro i j b' h
      rw [hDReq] at h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq]; exact hI.received_sound i j b' h
      · rw [heq]
        by_cases hji : j = id
        -- the sent set only grows (D12′): the old receipt stays covered
        · rw [hji] at h ⊢
          rw [Function.update_self]
          exact Finset.mem_insert_of_mem (hI.received_sound i id b' h)
        · rw [Function.update_of_ne hji]; exact hI.received_sound i j b' h
    · intro id' b' hmem h
      rcases hDSeq with heq | ⟨b0, hlg, heq⟩
      · rw [heq] at h
        exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
      · rw [heq] at h
        by_cases hid : id' = id
        · rw [hid, Function.update_self, Finset.mem_insert] at h
          rcases h with rfl | h
          · exact (hI.grade2_source id b' hlg).imp (fun r0 => hCertW r0 b')
          · exact (hI.decided_source id b' (hFeq ▸ hid ▸ hmem) h).imp (fun r0 => hCertW r0 b')
        · rw [Function.update_of_ne hid] at h
          exact (hI.decided_source id' b' (hFeq ▸ hmem) h).imp (fun r0 => hCertW r0 b')
    · intro r0 b0 hgr hbr
      exact hCommitW r0 b0 hgr (hI.grade2Lock_commit r0 b0 hgr hbr)
    · intro id' hmem r' hround
      by_cases h : id' = id
      · rw [h] at hmem; rw [h, hRoundEq] at hround
        by_cases hr' : r' = (c.processes id).round
        · rw [hr', hr]; exact hI.wcc_bound r hWval
        · exact hI.round_bound id (hFeq ▸ hmem) r' (by omega)
      · rw [hProcNe id' h] at hround; exact hI.round_bound id' (hFeq ▸ hmem) r' hround
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        by_cases hle : r' < (c.processes id).round
        · have hold := hI.agree_locked r' v hlast hbr hcoin id (hFeq ▸ (hid ▸ hmem)) hle
          rw [hid]; simp [hold]
        · have hr'eq : r' = (c.processes id).round := by omega
          have hr'r : r' = r := hr'eq.trans hr
          rw [hid]; simp only [hProcSelf]
          obtain ⟨hnone, hsome⟩ := hI.estimate_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
          by_cases holdE : (c.processes id).estimate = none
          · obtain ⟨hg0, -⟩ := hnone holdE
            have hbeqv : b = v := hCoinEq v (by rw [← hr'r]; exact hcoin)
            simp [holdE, hbeqv]
          · obtain ⟨bv, hbv⟩ := Option.ne_none_iff_exists'.mp holdE
            have hbveq := hsome bv hbv
            rw [hr'r] at hbr
            have hbv0 : bv = v := by
              by_contra hne
              have hv' : (!bv) = v := by
                revert hne; cases bv <;> cases v <;> simp
              exact hbr.2 (hv' ▸ hbveq)
            simp [hbv, hbv0]
      · rw [hProcNe id' hid] at hround; rw [hProcNe id' hid]
        exact hI.agree_locked r' v hlast hbr hcoin id' (hFeq ▸ hmem) hround
    · exact hI.grade2_needs_bind
    · intro r' id' hmem hcall
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcall
        exact le_trans (hI.call_round r' id (hFeq ▸ hmem) hcall) (by omega)
      · rw [hProcNe id' h]
        exact hI.call_round r' id' (hFeq ▸ hmem) hcall
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcc_called r' id' (hFeq ▸ hmem) hcalled
    · intro r' id' hmem hround
      by_cases h : id' = id
      · rw [h, hRoundEq] at hround
        rw [hValeq]
        by_cases hlt : r' < (c.processes id).round
        · exact hI.round_flip r' id (hFeq ▸ (h ▸ hmem)) hlt
        · have hreq : r' = (c.processes id).round := by omega
          rw [hreq, hr]; exact hWval
      · rw [hProcNe id' h] at hround
        rw [hValeq]; exact hI.round_flip r' id' (hFeq ▸ hmem) hround
    · intro id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hRoundEq] at hround
        omega
      · rw [hProcNe id' h] at hround hphase ⊢
        exact hI.estimate0 id' (hFeq ▸ hmem) hround hphase
    · intro id' b' hlg
      by_cases h : id' = id
      · exfalso; rw [h, hProcSelf] at hlg; simp at hlg
      · rw [hProcNe id' h] at hlg
        exact (hI.grade2_source id' b' hlg).imp (fun r0 => hCertW r0 b')
    · intro r' id' hmem hround hphase
      by_cases h : id' = id
      · exfalso
        rw [h, hProcSelf] at hphase
        rcases hphase with hp | hp <;> simp at hp
      · rw [hProcNe id' h] at hround hphase
        rw [hProcNe id' h]
        exact hI.estimate_ret r' id' (hFeq ▸ hmem) hround hphase
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall
      rw [hValeq r']; exact hI.call_provenance r' id' v (hFeq ▸ hmem) hcall
    · intro r' id' hmem hround hphase v hest
      by_cases hid : id' = id
      · rw [hid, hRoundEq] at hround
        have hreq : r' = r := by
          omega
        rw [hreq, hValeq r]
        have hveq : (c.processes id).estimate.getD b = v := by
          have hcopy := hest
          rw [hid, hProcSelf] at hcopy
          exact Option.some_inj.mp hcopy
        have hep := hI.estimate_ret r id (hFeq ▸ (hid ▸ hmem)) hr (Or.inr hph)
        rcases Option.eq_none_or_eq_some ((c.processes id).estimate) with hoe | ⟨bv, hoe⟩
        · rw [hoe] at hveq; simp at hveq
          obtain ⟨hg0, -⟩ := hep.1 hoe
          have hWtb : (w r).val = .top ∨ (w r).val = .bit b := by
            cases hstepW with | ret _ _ h1 _ => exact h1
          rw [← hveq]; exact Or.inr ⟨hg0, hWtb.symm⟩
        · rw [hoe] at hveq; simp at hveq
          have hbveq := hep.2 bv hoe
          rw [← hveq]; exact Or.inl hbveq
      · rw [hProcNe id' hid] at hround hphase hest
        rw [hValeq r']
        exact hI.estimate_previous r' id' (hFeq ▸ hmem) hround hphase v hest
    · intro id' hmem hround hphase
      by_cases hid : id' = id
      · rw [hid, hProcSelf]; simp
      · rw [hProcNe id' hid] at hround hphase ⊢
        exact hI.estimate_previous_ne id' (hFeq ▸ hmem) hround hphase
    · intro r' h; rw [hValeq] at h ⊢; exact hI.wcc_order r' h
    · intro id' b' h
      by_cases hid : id' = id
      · rw [hid] at h ⊢
        rcases hI.input_gbcaRound0_permanent id b' h with hin | hf
        · left; rw [hInputEq]; exact hin
        · right; rw [hFeq]; exact hf
      · rw [hProcNe id' hid]
        rcases hI.input_gbcaRound0_permanent id' b' h with hin | hf
        · left; exact hin
        · right; rw [hFeq]; exact hf
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      by_cases h : id' = id
      · rw [h, hRoundEq]; rw [h] at hmem hcalled
        exact le_trans (hI.wcc_callRound r' id (hFeq ▸ hmem) hcalled) (by omega)
      · rw [hProcNe id' h]
        exact hI.wcc_callRound r' id' (hFeq ▸ hmem) hcalled
    · intro r' h
      rw [hValeq] at h
      rcases hI.flip_grade2Lock r' h with hg | hd
      · left; exact hg
      · right
        refine DissentWitness.transport rfl rfl (fun hh => hh) (fun id2 => ?_) hd
        by_cases hid2 : id2 = id
        · rw [hid2]; exact hInputEq
        · rw [hProcNe id2 hid2]
    · intro id' hmem hin r'
      rw [hCalledEq]
      by_cases h : id' = id
      · rw [h] at hmem hin
        rw [h]; rw [hInputEq] at hin
        exact hI.idle_no_wccCall id (hFeq ▸ hmem) hin r'
      · rw [hProcNe id' h] at hin
        exact hI.idle_no_wccCall id' (hFeq ▸ hmem) hin r'
    · intro r' id' hmem hp
      by_cases hid : id' = id
      · rw [hid] at hmem hp
        rcases hp with ⟨hround, hphase⟩ | hlt0
        · exfalso
          rw [hProcSelf] at hphase
          rcases hphase with h | h <;> simp at h
        · rw [hRoundEq] at hlt0
          by_cases hlt : r' < (c.processes id).round
          · rcases hI.retG_witness r' id (hFeq ▸ hmem) (Or.inr hlt) with hg | hd
            · left; exact hg
            · right; exact hDR2 r' hd
          · have hreq : r' = r := by omega
            rcases hI.retG_witness r id (hFeq ▸ hmem) (Or.inl ⟨hr, Or.inr hph⟩) with hg | hd
            · left; rw [hreq]; exact hg
            · right; rw [hreq]; exact hDR2 r hd
      · rw [hProcNe id' hid] at hp
        rcases hI.retG_witness r' id' (hFeq ▸ hmem) hp with hg | hd
        · left; exact hg
        · right; exact hDR2 r' hd
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled
      rcases hI.wccCalled_witness r' id' (hFeq ▸ hmem) hcalled with hg | hd
      · left; exact hg
      · right; exact hDR2 r' hd
  · rw [PMF.mem_support_pure_iff] at hc'; subst hc'
    refine And.intro ?_ (AbstractStateUnchanged.refl P g _)
    refine ⟨hI.corrupted_F, hI.F_gbca, fun r' => (hFweq r').trans (hI.F_wcc r'), hI.F_card,
      hI.input_gbcaRound0, hI.input_called, hI.phase_input, hI.down_settled, hI.quiescent,
      fun r' h => hI.wcc_bound r' (by rw [← hValeq r']; exact h),
      hI.received_sound, hI.decided_source, hI.grade2Lock_commit, hI.round_bound, ?_,
      hI.grade2_needs_bind, hI.call_round, ?_, ?_, hI.estimate0, hI.grade2_source, hI.estimate_ret,
      ?_, ?_, ?_, hI.grade0Lock_chain, hI.estimate_previous_ne,
      ?_, hI.input_gbcaRound0_permanent, ?_, ?_, ?_, hI.retG_witness, ?_, hI.bound_quorum,
      hI.bind_support, hI.grade0Lock_support, hI.excluded_support, hI.outcomeHolder_agree,
        hI.grade2Lock_agree⟩
    · intro r' v hlast hbr hcoin id' hmem hround
      rw [hValeq] at hcoin
      exact hI.agree_locked r' v hlast hbr hcoin id' hmem hround
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcc_called r' id' hmem hcalled
    · intro r' id' hmem hround
      rw [hValeq]; exact hI.round_flip r' id' hmem hround
    · intro r' v h; rw [hValeq r']; exact hI.bind_succ r' v h
    · intro r' id' v hmem hcall; rw [hValeq r']; exact hI.call_provenance r' id' v hmem hcall
    · intro r' id' hmem hround hphase v hest
      rw [hValeq r']; exact hI.estimate_previous r' id' hmem hround hphase v hest
    · intro r' h; rw [hValeq] at h ⊢; exact hI.wcc_order r' h
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wcc_callRound r' id' hmem hcalled
    · intro r' h; rw [hValeq] at h; exact hI.flip_grade2Lock r' h
    · intro id' hmem hin r'; rw [hCalledEq]; exact hI.idle_no_wccCall id' hmem hin r'
    · intro r' id' hmem hcalled
      rw [hCalledEq] at hcalled; exact hI.wccCalled_witness r' id' hmem hcalled

end ABA
end PLTS
