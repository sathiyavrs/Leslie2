/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.AbstractStatePreservation
import Leslie2Protocols.ABA.HybridRefinesSpecification.WeakTransitions

/-!
# The simulation `hybrid ⊑ ABA.spec`

This file assembles the relation and the invariant of `HybridRefinesSpecification/Relation.lean`,
their preservation in `HybridRefinesSpecification/InvariantPreservation/` and
`HybridRefinesSpecification/AbstractStatePreservation.lean`, and the weak transitions of
`HybridRefinesSpecification/WeakTransitions.lean` into `hybridRefinesSpecification`, the
probabilistic forward simulation `hybrid P M ⊑ spec P` along `hybridSpecificationRelation P`.
It holds for every type `M` of round messages: no step of the simulation reads a round message.
`hybrid_spec` is the trace-distribution inclusion it yields. Both chains of the case study reach
the ABA specification along it, ABDY22's at `GBCA.ByABDY.Message` and the gather-based one at
`Empty`.

The transitions of `hybrid` are matched label class by label class.

* A silent transition is matched by the stutter `weakTau_refl`. The abstract state does not move,
  and its mode is `ControlMode.flipEnabled`, so it never fires `SpecStep.coinFlip` and
  `SpecStep.decide` is enabled when the first return occurs. The silent transitions include the
  coin's resolution, the round loop's `retGLoop`, `retWLoop` and `decidedDeliverLoop`, and the
  announcement `boundG`, which leaves the state of `hybrid` unchanged.
* A `callABA` is matched by `SpecStep.callSet` at a never-corrupted process holding no input, by
  `SpecStep.callLoop` at a never-corrupted process holding one, and by `SpecStep.callByzantine`
  at a corrupted process.
* A never-corrupted process's `retABA` is matched by `SpecStep.decide` followed by
  `SpecStep.ret` at the first such transition, and by `SpecStep.ret` alone at every later one.
  The guard `b ∈ c.decidedSent` of the round loop's return reads the round loop's own record of
  its DECIDED sends. I4' (`Invariant.decidedSent_recorded`) identifies that record with the ABA
  network's, so `hybrid_step_retABA` states the transition on the network's record, which the
  invariant reads.
* A corrupted process's `retABA` is the replaced round loop's self-loop beside the ABA network's
  `retABAIdle`. Neither the state of `hybrid` nor the abstract state moves, and
  `SpecStep.retByzantine` matches the transition (D23).
* A `fail` is matched by `SpecStep.fail`, whose two guards follow from the concrete transition's
  two guards and `AbstractState.F_eq`. The two families apply the corruption to every round, as
  `GBCA.instanceState_applyBroadcast_fail` and `WCC.instanceState_applyBroadcast_fail` state.
* The labels of the sub-protocol interface, `callG`, `retG`, `boundG`, `callW` and `retW`, are
  hidden, so no transition of `hybrid` carries one of them. -/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]

omit [DecidableEq M] in
/-- The simulation relation: a state of `hybrid` relates to the point mass at every abstract state
it relates to under `hybridSpecificationStateRelation`. -/
def hybridSpecificationRelation (P : Parameters) :
    HybridState P M → PMF (SpecState P.n) → Prop :=
  diracRel (hybridSpecificationStateRelation P)

omit [DecidableEq M] in
/-- **The stutter.** Let every state in the support of the outcome `μ_C` of a silent transition
relate to the abstract state `a` under `hybridSpecificationStateRelation`. Then the stutter
`weakTau_refl` at `a` matches the transition. The coupling is
`Ω := μ_C.map (fun s' => (s', pure a))`. Its first marginal is `μ_C` and its second marginal is
the constant `pure (pure a)` (`PMF.map_const`), so `ω := pure (pure a)` and `ω.bind id = pure a`
(`PMF.pure_bind`). -/
private theorem stutter_step {P : Parameters} (μ_C : PMF (HybridState P M)) (a : SpecState P.n)
    (hA : ∀ s' ∈ μ_C.support, hybridSpecificationStateRelation P s' a) :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (hybridSpecificationRelation P) μ_C ω ∧ weakTau (spec P) (PMF.pure a) (ω.bind id) := by
  set Ω : PMF (HybridState P M × PMF (SpecState P.n)) := μ_C.map (fun s' => (s',
    PMF.pure a)) with hΩdef
  have hFst : Ω.map Prod.fst = μ_C := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun s' => (s',
      PMF.pure a)) = (id : HybridState P M → HybridState P M) := rfl
    rw [hcomp, PMF.map_id]
  have hSnd : Ω.map Prod.snd = PMF.pure (PMF.pure a) := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.snd ∘ fun s' => (s', PMF.pure a)) =
        (Function.const (HybridState P M) (PMF.pure a)) := rfl
    rw [hcomp, PMF.map_const]
  refine ⟨PMF.pure (PMF.pure a), ⟨Ω, hFst, hSnd, ?_⟩, ?_⟩
  · intro p hp
    rw [hΩdef, PMF.mem_support_map_iff] at hp
    obtain ⟨s', hs', hp'⟩ := hp
    rw [← hp']
    exact ⟨a, rfl, hA s' hs'⟩
  · rw [PMF.pure_bind]
    exact weakTau_refl _ _

/-- The corruption of a process enlarges the corrupted set or leaves it as it is. -/
theorem ABAState.corrupt_F_subset {P : Parameters} (c : ABAState P) (id : Fin P.n) :
    c.F ⊆ (c.corrupt P id).F := by
  rw [ABAState.corrupt_F]; split_ifs with hcond
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- A transition at which the specification family reaches the state `G`, the round loops and the
ABA network reach the state `c`, and the coin family reaches the state `o` has the point mass at
`(G, c.1, c.2, o)` as its outcome. -/
private theorem prodPMF_pure_abaTransition {P : Parameters} {α σ : Type} (G : α)
    (c : ABAState P) (o : σ) :
    prodPMF (PMF.pure G) ((PMF.pure c).map fun x => (x.1, x.2, o))
      = PMF.pure (G, c.1, c.2, o) := by
  rw [PMF.pure_map, prodPMF_pure_pure]

omit [DecidableEq M] in
/-- **A visible step.** Let the outcome of a transition be the point mass at `s_C'`, and let
`s_C'` relate to the abstract state `a'` under `hybridSpecificationStateRelation`. The coupling is
the point mass `ω := pure (pure a')`, and `ω.bind id = pure a'` (`PMF.pure_bind`), so a weak step
of `spec P` from `pure a` to `pure a'` matches the transition. -/
private theorem dirac_step {P : Parameters} (s_C' : HybridState P M) (a' : SpecState P.n)
    (hrelated : hybridSpecificationStateRelation P s_C' a') :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (hybridSpecificationRelation P) (PMF.pure s_C') ω ∧ ω.bind id = PMF.pure a' := by
  refine ⟨PMF.pure (PMF.pure a'), ⟨PMF.pure (s_C', PMF.pure a'), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp; rw [PMF.mem_support_pure_iff] at hp; subst hp; exact ⟨a', rfl, hrelated⟩
  · rw [PMF.pure_bind]; rfl

/-- A label of `Label.hiddenAPI` other than `τ` is hidden by the second hiding of `hybrid`, so no
transition of `hybrid` carries it. -/
private theorem hidden_label_impossible {P : Parameters} {s_C : HybridState P M} {l : Label P.n}
    {μ_C : PMF (HybridState P M)} (hmem : l ∈ Label.hiddenAPI P.n) (hne : l ≠ Silent.τ)
    (hstep : (hybrid P M).step s_C l μ_C) : False := by
  rw [hybrid_step_iff] at hstep
  rcases hstep with ⟨h, -⟩ | ⟨h, -⟩
  · exact hne h
  · exact h hmem

/-- **The simulation.** `hybrid P M` is a probabilistic forward simulation of `spec P` along
`hybridSpecificationRelation P`, at an abstract state that never fires `SpecStep.coinFlip`. -/
theorem hybridRefinesSpecification (P : Parameters) (M : Type) [DecidableEq M] :
    ProbabilisticForwardSimulation (hybrid P M) (spec P) (hybridSpecificationRelation P) := by
  refine ⟨⟨PMF.pure (SpecState.initial P.n), ?_, SpecState.initial P.n, rfl,
    hybridSpecificationStateRelation_init P M⟩, ?_⟩
  · intro s_A hs_A; rw [PMF.mem_support_pure_iff] at hs_A; exact hs_A
  · intro s_C μ_A hR l μ_C hstep
    obtain ⟨G, C, A, o⟩ := s_C
    obtain ⟨a, rfl, hI, hAbstract⟩ := hR
    dsimp only [HybridState.aba, HybridState.wcc] at hI hAbstract
    cases l with
    | tau =>
      -- every silent transition, the loops and the announcement included: the abstract state
      -- stutters
      obtain ⟨ω, hcoupling, hweakTau⟩ := stutter_step μ_C a (fun s' hs' => by
        obtain ⟨G', C', A', o'⟩ := s'
        exact ⟨hI.step hstep hs', hAbstract.step_tau hI hstep hs'⟩)
      exact ⟨ω, hcoupling, Or.inl ⟨rfl, hweakTau⟩⟩
    | callABA id b =>
      rw [hybrid_step_callABA P G C A o id b hI.corrupted_F] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      have hcases := hstepC
      rcases hcases with ⟨hidF, hin, rfl⟩ | ⟨hloop, rfl⟩
      · -- the input of a never-corrupted process holding no input: `SpecStep.callSet`, whose
        -- empty-entry guard is `input_sync` at `id`
        set c' := ABAState.setProcessVariables (C, A) id { ABAState.processes (C, A) id with
          input := some b, estimate := some b, round := 0, phase := .toCallG } with hc'def
        have hc'mem : c' ∈ (PMF.pure c').support := by
          rw [PMF.mem_support_pure_iff]
        have hstepInvariant := Invariant.step_callABA hI id b hstepC hc'mem
        have hInvariant' : Invariant P G c' o := hstepInvariant.1
        have hF' : c'.F = ABAState.F (C, A) := ABAState.setProcessVariables_F _ _ _
        have hSelf : c'.processes id = { ABAState.processes (C, A) id with
            input := some b, estimate := some b, round := 0, phase := .toCallG } := by
          rw [hc'def]; exact ABAState.setProcessVariables_processes_self _ _ _
        have hOthers : ∀ id', id' ≠ id → c'.processes id' = ABAState.processes (C, A) id' := by
          intro id' h; rw [hc'def]; exact ABAState.setProcessVariables_processes_ne _ _ _ h
        have hempty : a.input id = none := by
          rw [hAbstract.input_sync id hidF]; exact hin
        set a' : SpecState P.n :=
          { a with input := Function.update a.input id (some b) } with ha'def
        have hAbstract' : AbstractState P G c' o a' := by
          refine ⟨by rw [hF']; exact hAbstract.F_eq, fun id' => ?_, hAbstract.mode_flipEnabled,
            fun id' hid' => ?_, ?_⟩
          · change a.ret id' = (c'.processes id').returned
            by_cases h : id' = id
            · rw [h, hSelf]; exact hAbstract.ret_eq id
            · rw [hOthers id' h]; exact hAbstract.ret_eq id'
          · rw [hF'] at hid'
            change Function.update a.input id (some b) id' = (c'.processes id').input
            by_cases h : id' = id
            · rw [h, Function.update_self, hSelf]
            · rw [Function.update_of_ne h, hOthers id' h]
              exact hAbstract.input_sync id' hid'
          · rcases hAbstract.phase with hv | ⟨v, hval, ⟨r₀, hwitness⟩, hholders⟩
            · exact Or.inl hv
            · exact Or.inr ⟨v, hval, hstepInvariant.2.1 r₀ v hwitness,
                hstepInvariant.2.2 v ⟨r₀, hwitness⟩ hholders⟩
        simp only [prodPMF_pure_abaTransition]
        obtain ⟨ω, hcoupling, hbind⟩ := dirac_step (G, c'.1, c'.2, o) a' ⟨hInvariant', hAbstract'⟩
        refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbind]
        exact weakStep_strong (SpecStep.callSet a id b hempty)
      · by_cases hidF : id ∈ ABAState.F (C, A)
        · -- the replaced round loop's self-loop: `SpecStep.callByzantine`, whose write is at a
          -- corrupted process, where `input_sync` is vacuous
          set a' : SpecState P.n :=
            { a with input := Function.update a.input id (some b) } with ha'def
          have hAbstract' : AbstractState P G (C, A) o a' := by
            refine ⟨hAbstract.F_eq, hAbstract.ret_eq, hAbstract.mode_flipEnabled,
              fun id' hid' => ?_, hAbstract.phase⟩
            have hne : id' ≠ id := by
              intro h; rw [h] at hid'; exact hid' hidF
            change Function.update a.input id (some b) id' = (ABAState.processes (C, A) id').input
            rw [Function.update_of_ne hne]
            exact hAbstract.input_sync id' hid'
          simp only [prodPMF_pure_abaTransition]
          obtain ⟨ω, hcoupling, hbind⟩ := dirac_step (G, C, A, o) a' ⟨hI, hAbstract'⟩
          refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbind]
          exact weakStep_strong (SpecStep.callByzantine a id b b (hAbstract.F_eq ▸ hidF))
        · -- the input-enabledness loop at a never-corrupted process holding an input:
          -- `SpecStep.callLoop`, whose filled-entry guard is `input_sync` at `id`
          have hcorrupted : ABAState.corrupted (C, A) id = false := by
            cases hflag : ABAState.corrupted (C, A) id
            · rfl
            · exact absurd ((hI.corrupted_F id).mp hflag) hidF
          have hfilled : a.input id ≠ none := by
            rw [hAbstract.input_sync id hidF]
            exact hloop.resolve_left (by rw [hcorrupted]; simp)
          simp only [prodPMF_pure_abaTransition]
          obtain ⟨ω, hcoupling, hbind⟩ := dirac_step (G, C, A, o) a ⟨hI, hAbstract⟩
          refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbind]
          exact weakStep_strong (SpecStep.callLoop a id b hfilled)
    | retABA id b =>
      rw [hybrid_step_retABA P G C A o id b hI.corrupted_F hI.decidedSent_recorded] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      have hcases := hstepC
      rcases hcases with ⟨-, hcount, -, hret, rfl⟩ | ⟨hidF, rfl⟩
      · -- a never-corrupted process's return: the abstract state decides and returns
        set c' := ABAState.setProcessVariables (C, A) id { ABAState.processes (C,
          A) id with returned := true } with hc'def
        have hc'mem : c' ∈ (PMF.pure c').support := by
          rw [PMF.mem_support_pure_iff]
        have hstepInvariant := Invariant.step_retABA hI id b hstepC hc'mem
        have hInvariant' : Invariant P G c' o := hstepInvariant.1
        -- the pigeonhole on the DECIDED senders: `id` holds `⟨DECIDED, b⟩` from `n − f` distinct
        -- senders, at most `f` of them corrupted. A corrupted sender may send both bits, and its
        -- message counts toward the tally, but `f < n − f` gives a counted sender outside `F`
        -- (D12′).
        have hcorrectSender :
            ∃ j, j ∉ ABAState.F (C, A) ∧ b ∈ ABAState.decidedReceived (C, A) id j := by
          by_contra hnone; push Not at hnone
          have hsubset :
              (Finset.univ.filter (fun j => b ∈ ABAState.decidedReceived (C, A) id j))
                ⊆ ABAState.F (C, A) := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            by_contra hnotF; exact hnone j hnotF hj
          have hcard := Finset.card_le_card hsubset
          have hFcard := hI.F_card
          have hResilience := P.hResilience
          unfold ABAState.decidedCount at hcount
          omega
        obtain ⟨j, hjF, hjreceived⟩ := hcorrectSender
        have hjsent : b ∈ ABAState.decidedSent (C, A) j := hI.received_sound id j b hjreceived
        obtain ⟨rWitness, hwitness⟩ := hI.decided_source j b hjF hjsent
        -- every correct holder of a grade-2 decision names the bit `b` the sender `j` sent (I30)
        have hholdersB :
            ∀ j₀ b₀, j₀ ∉ ABAState.F (C, A) → Grade2Holder P (C, A) j₀ b₀ → b₀ = b :=
          fun j₀ b₀ hj₀ hholder₀ =>
            hI.grade2Bound_agree j₀ j b₀ b hj₀ hjF hholder₀ (Or.inr hjsent)
        have hretfalse : a.ret id = false := by
          rw [hAbstract.ret_eq id]; exact hret
        have hF' : c'.F = ABAState.F (C, A) := ABAState.setProcessVariables_F _ _ _
        have hInputEq : ∀ id', (c'.processes id').input = (ABAState.processes (C,
          A) id').input := by
          intro id'
          by_cases h : id' = id
          · rw [h, hc'def, ABAState.setProcessVariables_processes_self]
          · rw [hc'def, ABAState.setProcessVariables_processes_ne _ _ _ h]
        have hSync : ∀ id', id' ∉ c'.F → a.input id' = (c'.processes id').input := by
          intro id' hid'
          rw [hF'] at hid'
          rw [hInputEq id']
          exact hAbstract.input_sync id' hid'
        rcases hAbstract.phase with hv | ⟨v, hval, ⟨r₀, hwitness₀⟩, hholders⟩
        · -- phase 1: the silent step `SpecStep.decide`, then `SpecStep.ret`
          have hsupport : InputSupport P a b :=
            inputSupport_of_roundLoopInputSupport hAbstract.F_eq hAbstract.input_sync
              (hI.bind_support rWitness b hwitness.2.1)
          have hmode : a.mode ≠ .noTransitionEnabled := by
            rw [hAbstract.mode_flipEnabled]; exact fun h => by cases h
          set a₁ : SpecState P.n := { a with val := some b, mode := .flipEnabled } with ha₁def
          have hrun : weakTau (spec P) (PMF.pure a) (PMF.pure a₁) :=
            decide_step hv hsupport hmode
          have hval₁ : a₁.val = some b := rfl
          have hretid : a₁.ret id = false := hretfalse
          set a'' : SpecState P.n := { a₁ with ret := Function.update a₁.ret id true }
            with ha''def
          have hAbstract'' : AbstractState P G c' o a'' := by
            refine ⟨?_, ?_, rfl, hSync, Or.inr ⟨b, rfl, hstepInvariant.2.1 rWitness b hwitness,
              hstepInvariant.2.2 b ⟨rWitness, hwitness⟩ hholdersB⟩⟩
            · change a.F = c'.F
              rw [hAbstract.F_eq, hF']
            · intro id'
              change Function.update a₁.ret id true id' = (c'.processes id').returned
              by_cases h : id' = id
              · rw [h, Function.update_self, hc'def, ABAState.setProcessVariables_processes_self]
              · rw [Function.update_of_ne h, hc'def,
                  ABAState.setProcessVariables_processes_ne _ _ _ h]
                exact hAbstract.ret_eq id'
          simp only [prodPMF_pure_abaTransition]
          obtain ⟨ω, hcoupling, hbind⟩ :=
            dirac_step (G, c'.1, c'.2, o) a'' ⟨hInvariant', hAbstract''⟩
          refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbind]
          exact weakStep_of_run_then_step hrun (SpecStep.ret a₁ id b hval₁ hretid)
        · -- phase 2: `b` is the decided value `v`, since every correct holder of a grade-2
          -- decision names `v` and the sender `j` sent `b` (I30). `SpecStep.ret` matches the
          -- return alone.
          have hvb : v = b := (hholders j b hjF (Or.inr hjsent)).symm
          have hvalb : a.val = some b := by
            rw [hval, hvb]
          set a'' : SpecState P.n := { a with ret := Function.update a.ret id true } with ha''def
          have hAbstract'' : AbstractState P G c' o a'' := by
            refine ⟨?_, ?_, hAbstract.mode_flipEnabled, hSync, Or.inr ⟨v, hval,
              hstepInvariant.2.1 r₀ v hwitness₀, hstepInvariant.2.2 v ⟨r₀, hwitness₀⟩ hholders⟩⟩
            · change a.F = c'.F
              rw [hAbstract.F_eq, hF']
            · intro id'
              change Function.update a.ret id true id' = (c'.processes id').returned
              by_cases h : id' = id
              · rw [h, Function.update_self, hc'def, ABAState.setProcessVariables_processes_self]
              · rw [Function.update_of_ne h, hc'def,
                  ABAState.setProcessVariables_processes_ne _ _ _ h]
                exact hAbstract.ret_eq id'
          simp only [prodPMF_pure_abaTransition]
          obtain ⟨ω, hcoupling, hbind⟩ :=
            dirac_step (G, c'.1, c'.2, o) a'' ⟨hInvariant', hAbstract''⟩
          refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbind]
          exact weakStep_strong (SpecStep.ret a id b hvalb hretfalse)
      · -- a corrupted process's return, the replaced round loop's self-loop beside the ABA
        -- network's `retABAIdle`: neither system moves, and `SpecStep.retByzantine` matches it
        -- (D23)
        simp only [prodPMF_pure_abaTransition]
        obtain ⟨ω, hcoupling, hbind⟩ := dirac_step (G, C, A, o) a ⟨hI, hAbstract⟩
        refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbind]
        exact weakStep_strong (SpecStep.retByzantine a id b (hAbstract.F_eq ▸ hidF))
    | callG r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retG r id out => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | boundG r b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | callW r id => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retW r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | fail id =>
      rw [hybrid_step_fail P G C A o id hI.corrupted_F] at hstep
      obtain ⟨hcorrect, hbudget, rfl⟩ := hstep
      set c' : ABAState P := ABAState.corrupt P id (C, A) with hc'def
      simp only [prodPMF_pure_abaTransition]
      have hFsubset := ABAState.corrupt_F_subset (C, A) id
      have hAbstract' : AbstractState P (fun r => (G r).corrupt P id) c'
          (fun r => (o r).corrupt P id) (a.corrupt P id) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show (a.corrupt P id).F = c'.F
          rw [hc'def, ABAState.corrupt_F]
          unfold SpecState.corrupt
          rw [hAbstract.F_eq]
          split_ifs <;> simp [hAbstract.F_eq]
        · intro id'
          rw [corrupt_ret, hc'def, ABAState.corrupt_processes]; exact hAbstract.ret_eq id'
        · rw [corrupt_mode]; exact hAbstract.mode_flipEnabled
        · intro id' hid'
          rw [corrupt_input, hc'def, ABAState.corrupt_processes]
          exact hAbstract.input_sync id' (fun hmemF => hid' (hFsubset hmemF))
        · rcases hAbstract.phase with hv | ⟨v, hv, ⟨r₀, hwitness⟩, hholders⟩
          · exact Or.inl (by rw [corrupt_val]; exact hv)
          · exact Or.inr ⟨v, by rw [corrupt_val]; exact hv,
              (hI.step_fail id hcorrect hbudget).2.1 r₀ v hwitness,
              (hI.step_fail id hcorrect hbudget).2.2 v ⟨r₀, hwitness⟩ hholders⟩
      have hInvariant' : Invariant P (fun r => (G r).corrupt P id) c'
          (fun r => (o r).corrupt P id) := (hI.step_fail id hcorrect hbudget).1
      -- the two families read through their accessors: the broadcast corrupts every round
      have hrelated : hybridSpecificationStateRelation P
          (G.applyBroadcast (Sum.inl (Label.fail id)), c'.1, c'.2,
            o.applyBroadcast (Label.fail id)) (a.corrupt P id) := by
        refine ⟨?_, ?_⟩ <;> dsimp only [HybridState.aba, HybridState.wcc] <;>
          rw [GBCA.instanceState_applyBroadcast_fail, WCC.instanceState_applyBroadcast_fail]
        · exact hInvariant'
        · exact hAbstract'
      obtain ⟨ω, hcoupling, hbind⟩ := dirac_step _ (a.corrupt P id) hrelated
      refine ⟨ω, hcoupling, Or.inr ⟨by simp, ?_⟩⟩
      rw [hbind]
      exact weakStep_strong (SpecStep.fail a id (hAbstract.F_eq ▸ hcorrect)
        (by rw [hAbstract.F_eq]; exact hbudget))

/-- **Every achievable trace distribution of `hybrid` is one of Transition System 1**, by
`ProbabilisticForwardSimulation.achievableTraceDists_subset` at `hybridRefinesSpecification`. -/
theorem hybrid_spec (P : Parameters) (M : Type) [DecidableEq M] :
    achievableTraceDists (hybrid P M) ⊆ achievableTraceDists (spec P) :=
  (hybridRefinesSpecification P M).achievableTraceDists_subset

/-! ### The axioms -/

/-- info: 'PLTS.ABA.hybrid_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hybrid_spec

end ABA
end PLTS
