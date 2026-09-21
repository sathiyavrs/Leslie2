/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.AbstractStatePreservation
import Leslie2Protocols.ABA.HybridRefinesSpecification.WeakTransitions

/-!
# The core simulation `hybrid ⊑ ABA.spec`

Assembles the invariant and relation of the `CoreSimRel`/`CoreSimInv`/`CoreSimAbs`
chain and `CoreSimRun`'s run kit into `coreSim`, the probabilistic forward
simulation `hybrid P ⊑ spec P` along `coreRel P`.

The rows dispatch as follows. A visible `callABA` is answered by
`SpecStep.callSet` at a never-corrupted process holding no input, by
`SpecStep.callLoop` at a never-corrupted process holding one, and by
`SpecStep.callByz` at a corrupted process. A never-corrupted process's visible
`retABA` is answered by `SpecStep.decide` followed by `SpecStep.ret` on the
first such row, and by `SpecStep.ret` alone on every later one. Every hidden
row, the coin's resolving call included, is answered by a stutter: the
abstract state's mode stays `Mode.idle`, so it never fires
`SpecStep.coinFlip` and `SpecStep.decide` remains enabled when the first
return arrives. A `fail` is answered by `SpecStep.fail`, whose two guards are
the concrete row's own, read across `Abs.F_eq`.

A corruption replaces the program of the process it names (D23), and the
replacement is answered on both sides of the interface. The corrupted
process's `retABA` is answered by `SpecStep.retByz`: neither the concrete
state nor the abstract state moves. On every other label the replaced program
self-loops, and the concrete row it contributes is the corrupted branch the
inversion already carries.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Params}

/-- The core simulation relation, `Dirac`-lifted: every concrete state relates to the point
mass on its (unique) abstract state. -/
def coreRel (P : Params) : HybridState P → PMF (SpecState P.n) → Prop :=
  diracRel (coreR P)

/-- **Stutter-row packaging.** If every post-state `s'` in the support of a concrete τ-step's
outcome `μ_C` relates to the *same* abstract state `a` (via `coreR`), the abstract state can
answer with the trivial `weakTau_refl` stutter: the coupling `Ω := μ_C.map (fun s' => (s', pure
a))` has first marginal `μ_C` and second marginal the constant `pure (pure a)` (`PMF.map_const`),
so `ω := pure (pure a)` and `ω.bind id = pure a` (`PMF.pure_bind`). Reused by every hidden
row, the coin's resolving call included. -/
private theorem stutter_step {P : Params} (μ_C : PMF (HybridState P)) (a : SpecState P.n)
    (hA : ∀ s' ∈ μ_C.support, coreR P s' a) :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (coreRel P) μ_C ω ∧ weakTau (spec P) (PMF.pure a) (ω.bind id) := by
  set Ω : PMF (HybridState P × PMF (SpecState P.n)) := μ_C.map (fun s' => (s', PMF.pure a)) with hΩdef
  have hFst : Ω.map Prod.fst = μ_C := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun s' => (s', PMF.pure a)) = (id : HybridState P → HybridState P) := rfl
    rw [hcomp, PMF.map_id]
  have hSnd : Ω.map Prod.snd = PMF.pure (PMF.pure a) := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.snd ∘ fun s' => (s', PMF.pure a)) =
        (Function.const (HybridState P) (PMF.pure a)) := rfl
    rw [hcomp, PMF.map_const]
  refine ⟨PMF.pure (PMF.pure a), ⟨Ω, hFst, hSnd, ?_⟩, ?_⟩
  · intro p hp
    rw [hΩdef, PMF.mem_support_map_iff] at hp
    obtain ⟨s', hs', hp'⟩ := hp
    rw [← hp']
    exact ⟨a, rfl, hA s' hs'⟩
  · rw [PMF.pure_bind]
    exact weakTau_refl _ _

/-- Corruption of `F` is monotone (`fail`'s guard only ever inserts). -/
theorem ABAState.corrupt_F_subset {P : Params} (c : ABAState P) (id : Fin P.n) :
    c.F ⊆ (c.corrupt P id).F := by
  rw [ABAState.corrupt_F]; split_ifs with hcond
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- The outcome of a visible row collapses to a single Dirac: the specification
side stands, the ABA-side pair lands on one state and the coin oracle stands,
so the four components' joint outcome is the point mass `dirac_step`
expects. -/
private theorem prodPMF_pure_abaRow {P : Params} (G : ℕ → GBCA.SpecState P.n)
    (c : ABAState P) (o : ℕ → WCC.SpecState P.n) :
    prodPMF (PMF.pure G) ((PMF.pure c).map fun x => (x.1, x.2, o))
      = PMF.pure (G, c.1, c.2, o) := by
  rw [PMF.pure_map, prodPMF_pure_pure]

/-- **Visible-row packaging.** A single concrete Dirac outcome `s_C'` matched by a single
abstract state `a'` (`coreR`-related) closes the `weakStep` disjunct of the simulation clause:
the coupling is the Dirac-of-Dirac `ω := pure (pure a')`, whose `bind id` collapses back to
`pure a'` (`PMF.pure_bind`), so any `weakStep (spec P) (pure a) l (pure a')` transfers directly. -/
private theorem dirac_step {P : Params} (s_C' : HybridState P) (a' : SpecState P.n)
    (hcoreR : coreR P s_C' a') :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (coreRel P) (PMF.pure s_C') ω ∧ ω.bind id = PMF.pure a' := by
  refine ⟨PMF.pure (PMF.pure a'), ⟨PMF.pure (s_C', PMF.pure a'), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp; rw [PMF.mem_support_pure_iff] at hp; subst hp; exact ⟨a', rfl, hcoreR⟩
  · rw [PMF.pure_bind]; rfl

/-- A hidden-API label can never be visible at the `hybrid` level (it is always relabeled
to `τ` by the outer hiding), so any purported `hybrid`-step carrying one is vacuous. -/
private theorem hidden_label_impossible {P : Params} {s_C : HybridState P} {l : Lab P.n}
    {μ_C : PMF (HybridState P)} (hmem : l ∈ Lab.hiddenAPI P.n) (hne : l ≠ Silent.τ)
    (hstep : (hybrid P).step s_C l μ_C) : False := by
  rw [hybrid_step_iff] at hstep
  rcases hstep with ⟨h, -⟩ | ⟨h, -⟩
  · exact hne h
  · exact h hmem

/-- **The core simulation.** `hybrid P` is a probabilistic forward simulation of `spec P`
along `coreRel P` (the never-flipping abstract state). -/
theorem coreSim (P : Params) :
    ProbabilisticForwardSimulation (hybrid P) (spec P) (coreRel P) := by
  refine ⟨⟨PMF.pure (SpecState.initial P.n), ?_, SpecState.initial P.n, rfl, Inv.initial P,
    Abs.initial P⟩, ?_⟩
  · intro s_A hs_A; rw [PMF.mem_support_pure_iff] at hs_A; exact hs_A
  · intro s_C μ_A hR l μ_C hstep
    obtain ⟨g, C, A, w⟩ := s_C
    obtain ⟨a, rfl, hI, hAbs⟩ := hR
    dsimp only [HybridState.aba, HybridState.wcc] at hI hAbs
    cases l with
    | tau =>
      rcases hybrid_step_tau P g C A w hI.corrupted_F μ_C hstep with
        ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ |
        ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
        ⟨r, id, out, bnd, μr, μc, hstepG, hstepC, rfl⟩ |
        ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ | ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩
      · -- row 3: `bindUnset` (`gbcaTau`) — the abstract state stutters
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', C', A', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_map_iff, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hs'
          obtain ⟨⟨gr', hgr', heq⟩, rfl, rfl, rfl⟩ := hs'
          exact ⟨hI', by rw [← heq]; exact hAbs.step_gbcaTau hI r hstepG hgr'⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- rows 2/8: the view's own τ (DECIDED delivery/echo/byz)
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', C', A', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨rfl, hs2⟩ := hs'
          obtain ⟨hc2, rfl⟩ := mem_support_abaRow hs2
          exact ⟨hI', hAbs.step_coreTau hI hstepC hc2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: callG handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', C', A', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF] at hs'
          obtain ⟨h1, h2⟩ := hs'
          rw [PMF.mem_support_map_iff] at h1
          obtain ⟨gr', hgr', heq⟩ := h1
          obtain ⟨hc2, rfl⟩ := mem_support_abaRow h2
          exact ⟨hI', by rw [← heq]; exact hAbs.step_callG hI r id b hstepG hstepC hgr' hc2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: retG handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', C', A', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF] at hs'
          obtain ⟨h1, h2⟩ := hs'
          rw [PMF.mem_support_map_iff] at h1
          obtain ⟨gr', hgr', heq⟩ := h1
          obtain ⟨hc2, rfl⟩ := mem_support_abaRow h2
          exact ⟨hI', by
            rw [← heq]; exact hAbs.step_retG hI r id out bnd hstepG hstepC hgr' hc2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: callW handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', C', A', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨rfl, h2⟩ := hs'
          obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinRow h2
          exact ⟨hI', hAbs.step_callW hI r id hstepW hstepC hwr' hc2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: retW handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', C', A', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨rfl, h2⟩ := hs'
          obtain ⟨hc2, wr', hwr', rfl⟩ := mem_support_coinRow h2
          exact ⟨hI', hAbs.step_retW hI r id b hstepW hstepC hwr' hc2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
    | callABA id b =>
      rw [hybrid_step_callABA P g C A w id b hI.corrupted_F] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      have hdisj := hstepC
      rcases hdisj with ⟨hidF, hin, rfl⟩ | ⟨hloop, rfl⟩
      · -- the commit row at a never-corrupted process holding no input: `SpecStep.callSet`,
        -- whose empty-entry guard is `input_sync` read at `id`
        set c' := ABAState.setProc (C, A) id { ABAState.procs (C, A) id with
          input := some b, est := some b, round := 0, phase := .toCallG } with hc'def
        have hc'mem : c' ∈ (PMF.pure c').support := by rw [PMF.mem_support_pure_iff]
        have hIAF := Inv.step_callABA hI id b hstepC hc'mem
        have hIA' : Inv P g c' w := hIAF.1
        have hCF : c'.F = ABAState.F (C, A) := ABAState.setProc_F _ _ _
        have hSelf : c'.procs id = { ABAState.procs (C, A) id with
            input := some b, est := some b, round := 0, phase := .toCallG } := by
          rw [hc'def]; exact ABAState.setProc_procs_self _ _ _
        have hNe : ∀ id', id' ≠ id → c'.procs id' = ABAState.procs (C, A) id' := by
          intro id' h; rw [hc'def]; exact ABAState.setProc_procs_ne _ _ _ h
        have hempty : a.input id = none := by rw [hAbs.input_sync id hidF]; exact hin
        set a' : SpecState P.n :=
          { a with input := Function.update a.input id (some b) } with ha'def
        have hAbs' : Abs P g c' w a' := by
          refine ⟨by rw [hCF]; exact hAbs.F_eq, fun id' => ?_, hAbs.mode_idle,
            fun id' hid' => ?_, ?_⟩
          · show a.ret id' = (c'.procs id').returned
            by_cases h : id' = id
            · rw [h, hSelf]; exact hAbs.ret_eq id
            · rw [hNe id' h]; exact hAbs.ret_eq id'
          · rw [hCF] at hid'
            show Function.update a.input id (some b) id' = (c'.procs id').input
            by_cases h : id' = id
            · rw [h, Function.update_self, hSelf]
            · rw [Function.update_of_ne h, hNe id' h]
              exact hAbs.input_sync id' hid'
          · rcases hAbs.phase with hv | ⟨v, hv2, ⟨r0, hcv0⟩, hpin⟩
            · exact Or.inl hv
            · exact Or.inr ⟨v, hv2, hIAF.2.1 r0 v hcv0, hIAF.2.2 v ⟨r0, hcv0⟩ hpin⟩
        simp only [prodPMF_pure_abaRow]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c'.1, c'.2, w) a' ⟨hIA', hAbs'⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_strong (SpecStep.callSet a id b hempty)
      · by_cases hidF : id ∈ ABAState.F (C, A)
        · -- the replaced program's self-loop: `SpecStep.callByz`, whose write lands at a
          -- corrupted process, where `input_sync` is vacuous
          set a' : SpecState P.n :=
            { a with input := Function.update a.input id (some b) } with ha'def
          have hAbs' : Abs P g (C, A) w a' := by
            refine ⟨hAbs.F_eq, hAbs.ret_eq, hAbs.mode_idle, fun id' hid' => ?_, hAbs.phase⟩
            have hne : id' ≠ id := by intro h; rw [h] at hid'; exact hid' hidF
            show Function.update a.input id (some b) id' = (ABAState.procs (C, A) id').input
            rw [Function.update_of_ne hne]
            exact hAbs.input_sync id' hid'
          simp only [prodPMF_pure_abaRow]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, C, A, w) a' ⟨hI, hAbs'⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_strong (SpecStep.callByz a id b b (hAbs.F_eq ▸ hidF))
        · -- the input-enabledness loop at a never-corrupted process holding an input:
          -- `SpecStep.callLoop`, whose filled-entry guard is `input_sync` read at `id`
          have hcorr : ABAState.corrupted (C, A) id = false := by
            cases hb : ABAState.corrupted (C, A) id
            · rfl
            · exact absurd ((hI.corrupted_F id).mp hb) hidF
          have hfilled : a.input id ≠ none := by
            rw [hAbs.input_sync id hidF]
            exact hloop.resolve_left (by rw [hcorr]; simp)
          simp only [prodPMF_pure_abaRow]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, C, A, w) a ⟨hI, hAbs⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_strong (SpecStep.callLoop a id b hfilled)
    | retABA id b =>
      rw [hybrid_step_retABA P g C A w id b hI.corrupted_F] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      have hdisj := hstepC
      rcases hdisj with ⟨-, hcnt, hs, hret, rfl⟩ | ⟨hFbyz, rfl⟩
      · -- a never-corrupted process's return: the abstract state decides and returns
        set c' := ABAState.setProc (C, A) id { ABAState.procs (C, A) id with returned := true }
          with hc'def
        have hc'mem : c' ∈ (PMF.pure c').support := by rw [PMF.mem_support_pure_iff]
        have hIAF := Inv.step_retABA hI id b hstepC hc'mem
        have hIA' : Inv P g c' w := hIAF.1
        -- Honest DECIDED-sender pigeonhole: `n − f` distinct senders of `b` delivered to `id`,
        -- only `f` corrupted — equivocating byzantine senders may count toward the tally, but
        -- at least one counted sender is never-corrupted (D12′).
        have hex : ∃ j, j ∉ ABAState.F (C, A) ∧ b ∈ ABAState.decidedRecv (C, A) id j := by
          by_contra hcon; push Not at hcon
          have hsub : (Finset.univ.filter (fun j => b ∈ ABAState.decidedRecv (C, A) id j))
              ⊆ ABAState.F (C, A) := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            by_contra hnf; exact hcon j hnf hj
          have hcard := Finset.card_le_card hsub
          have hfc := hI.F_card
          have hf3 := P.hf
          unfold ABAState.decidedCount at hcnt
          omega
        obtain ⟨j, hjF, hjrecv⟩ := hex
        have hjsent : b ∈ ABAState.decidedSent (C, A) j := hI.recv_sound id j b hjrecv
        obtain ⟨rA, hrA_cert⟩ := hI.decided_src j b hjF hjsent
        -- the abstract-side holder pin for `b`: every honest `A`-decision holder agrees with the
        -- derived sender's sent bit (I30)
        have hpinb : ∀ j0 b0', j0 ∉ ABAState.F (C, A) → AHolder P (C, A) j0 b0' → b0' = b :=
          fun j0 b0' hj0 hh0 => hI.alock_agree j0 j b0' b hj0 hjF hh0 (Or.inr hjsent)
        have hretfalse : a.ret id = false := by rw [hAbs.ret_eq id]; exact hret
        have hCF : c'.F = ABAState.F (C, A) := ABAState.setProc_F _ _ _
        have hInputEq : ∀ id', (c'.procs id').input = (ABAState.procs (C, A) id').input := by
          intro id'
          by_cases h : id' = id
          · rw [h, hc'def, ABAState.setProc_procs_self]
          · rw [hc'def, ABAState.setProc_procs_ne _ _ _ h]
        have hSync : ∀ id', id' ∉ c'.F → a.input id' = (c'.procs id').input := by
          intro id' hid'
          rw [hCF] at hid'
          rw [hInputEq id']
          exact hAbs.input_sync id' hid'
        rcases hAbs.phase with hv | ⟨v, hv2, ⟨r0, hcv0⟩, hpin⟩
        · -- phase 1: the `decide` τ-step, then `SpecStep.ret`
          have hsup : SuppOK P a b :=
            suppOK_of_inputSupp hAbs.F_eq hAbs.input_sync (hI.bind_supp rA b hrA_cert.2.1)
          have hmode : a.mode ≠ .terminal := by rw [hAbs.mode_idle]; exact fun h => by cases h
          set a1 : SpecState P.n := { a with val := some b, mode := .idle } with ha1def
          have hrun : weakTau (spec P) (PMF.pure a) (PMF.pure a1) :=
            decide_step hv hsup hmode
          have hval1 : a1.val = some b := rfl
          have hretid : a1.ret id = false := hretfalse
          set a'' : SpecState P.n := { a1 with ret := Function.update a1.ret id true } with ha''def
          have hAbs'' : Abs P g c' w a'' := by
            refine ⟨?_, ?_, rfl, hSync, Or.inr ⟨b, rfl, hIAF.2.1 rA b hrA_cert,
              hIAF.2.2 b ⟨rA, hrA_cert⟩ hpinb⟩⟩
            · show a.F = c'.F
              rw [hAbs.F_eq, hCF]
            · intro id'
              show Function.update a1.ret id true id' = (c'.procs id').returned
              by_cases h : id' = id
              · rw [h, Function.update_self, hc'def, ABAState.setProc_procs_self]
              · rw [Function.update_of_ne h, hc'def, ABAState.setProc_procs_ne _ _ _ h]
                exact hAbs.ret_eq id'
          simp only [prodPMF_pure_abaRow]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c'.1, c'.2, w) a'' ⟨hIA', hAbs''⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_of_run_then_step hrun (SpecStep.ret a1 id b hval1 hretid)
        · -- phase 2: `b` agrees with the certified value through the abstract state's holder pin
          -- (I30 pins the derived sender's sent `b` against every honest holder, and the
          -- abstract state's pin names `v`; `SpecStep.ret` fires alone)
          have hD3 : v = b := (hpin j b hjF (Or.inr hjsent)).symm
          have hvalb : a.val = some b := by rw [hv2, hD3]
          set a'' : SpecState P.n := { a with ret := Function.update a.ret id true } with ha''def
          have hAbs'' : Abs P g c' w a'' := by
            refine ⟨?_, ?_, hAbs.mode_idle, hSync, Or.inr ⟨v, hv2, hIAF.2.1 r0 v hcv0,
              hIAF.2.2 v ⟨r0, hcv0⟩ hpin⟩⟩
            · show a.F = c'.F
              rw [hAbs.F_eq, hCF]
            · intro id'
              show Function.update a.ret id true id' = (c'.procs id').returned
              by_cases h : id' = id
              · rw [h, Function.update_self, hc'def, ABAState.setProc_procs_self]
              · rw [Function.update_of_ne h, hc'def, ABAState.setProc_procs_ne _ _ _ h]
                exact hAbs.ret_eq id'
          simp only [prodPMF_pure_abaRow]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c'.1, c'.2, w) a'' ⟨hIA', hAbs''⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_strong (SpecStep.ret a id b hvalb hretfalse)
      · -- a corrupted process's return (D23): neither side moves, and the abstract state answers
        -- with its own corrupted-return rule
        simp only [prodPMF_pure_abaRow]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, C, A, w) a ⟨hI, hAbs⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_strong (SpecStep.retByz a id b (hAbs.F_eq ▸ hFbyz))
    | callG r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retG r id out bnd => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | callW r id => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retW r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | fail id =>
      rw [hybrid_step_fail P g C A w id hI.corrupted_F] at hstep
      obtain ⟨hnew, hbud, rfl⟩ := hstep
      set c' : ABAState P := ABAState.corrupt P id (C, A) with hc'def
      simp only [prodPMF_pure_abaRow]
      have hFsub := ABAState.corrupt_F_subset (C, A) id
      have hAbs' : Abs P (fun r => (g r).corrupt P id) c'
          (fun r => (w r).corrupt P id) (a.corrupt P id) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show (a.corrupt P id).F = c'.F
          rw [hc'def, ABAState.corrupt_F]
          unfold SpecState.corrupt
          rw [hAbs.F_eq]
          split_ifs <;> simp [hAbs.F_eq]
        · intro id'
          rw [corrupt_ret, hc'def, ABAState.corrupt_procs]; exact hAbs.ret_eq id'
        · rw [corrupt_mode]; exact hAbs.mode_idle
        · intro id' hid'
          rw [corrupt_input, hc'def, ABAState.corrupt_procs]
          exact hAbs.input_sync id' (fun hh => hid' (hFsub hh))
        · rcases hAbs.phase with hv | ⟨v, hv, ⟨r0, hcv0⟩, hpin⟩
          · exact Or.inl (by rw [corrupt_val]; exact hv)
          · exact Or.inr ⟨v, by rw [corrupt_val]; exact hv,
              (hI.step_fail id hnew hbud).2.1 r0 v hcv0,
              (hI.step_fail id hnew hbud).2.2 v ⟨r0, hcv0⟩ hpin⟩
      have hIA' : Inv P (fun r => (g r).corrupt P id) c'
          (fun r => (w r).corrupt P id) := (hI.step_fail id hnew hbud).1
      refine ⟨PMF.pure (PMF.pure (a.corrupt P id)), ⟨PMF.pure
        ((fun r => (g r).corrupt P id, c'.1, c'.2, fun r => (w r).corrupt P id),
          PMF.pure (a.corrupt P id)), ?_, ?_, ?_⟩, Or.inr ⟨by simp, ?_⟩⟩
      · rw [PMF.pure_map]
      · rw [PMF.pure_map]
      · intro p hp
        rw [PMF.mem_support_pure_iff] at hp
        subst hp
        exact ⟨a.corrupt P id, rfl, hIA', hAbs'⟩
      · rw [PMF.pure_bind]
        exact weakStep_strong (SpecStep.fail a id (hAbs.F_eq ▸ hnew)
          (by rw [hAbs.F_eq]; exact hbud))

end ABA
end PLTS
