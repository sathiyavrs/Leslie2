/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GatherLow
import Leslie2Protocols.ABA.BRBSim
import Leslie2Protocols.Framework.WeakBurst

/-!
# The broadcast substitution inside the gather instance

`Gather.gatherLow`: the gather-over-Bracha instance (`ABA/GatherLow.lean`)
forward-simulates the gather-over-BRB-specification instance
(`ABA/GatherMid.lean`), along `Gather.LowRel` — the gather boxes and fabric
held *equal*, and each Bracha coordinate related to its specification
coordinate by the BRB refinement relation (`ABA/BRBSim.lean`).

The abstraction gap is delivery: the implementation's rows read the derived
predicates `apIn` / `apBind` — a `VOTE` receipt quorum in the coordinate —
where the specification's rows read the committed values. Each row that
consumes a derived delivery is answered through a chain of the
specification's `commitIn` / `commitBind` rows, one per uncommitted entry,
licensed by `BRB.commitReach`: the receipt quorum certifies the value, an
honest coordinate's committed value is its input, and a corrupted one may
commit anything. The exported answers are chain data
(`lowTau_reach`, `lowRetBurst`), replayable by any system embedding the
specification tier's rows.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Params}

/-- `PMF.pure` is injective (via its singleton support). -/
private theorem pure_inj {α : Type*} {a b : α} (h : PMF.pure a = PMF.pure b) :
    a = b := by
  have ha : a ∈ (PMF.pure a).support := by rw [PMF.mem_support_pure_iff]
  rw [h, PMF.mem_support_pure_iff] at ha
  exact ha

/-! ### The relation -/

/-- The broadcast substitution relation: the gather boxes and fabric equal,
the Bracha coordinates related by the BRB refinement relation, and the
corrupted sets in lockstep across every component. -/
structure LowRel (P : Params) (s : LowState P.n X) (t : MidState P.n X) : Prop where
  /-- The gather boxes and fabric are untouched by the substitution. -/
  ga_eq : t.ga = s.ga
  /-- The input-BRB corrupted sets are in lockstep with the fabric's. -/
  F_in_ga : ∀ k, (s.brbIn k).F = s.ga.F
  /-- The bind-BRB corrupted sets are in lockstep with the fabric's. -/
  F_bind_ga : ∀ k, (s.brbBind k).F = s.ga.F
  /-- Each input coordinate is BRB-refined. -/
  inRel : ∀ k, BRB.InstRel P k (s.brbIn k) (t.brbIn k)
  /-- Each bind coordinate is BRB-refined. -/
  bindRel : ∀ k, BRB.InstRel P k (s.brbBind k) (t.brbBind k)

/-- The relation holds initially. -/
theorem lowRel_init : LowRel P (LowState.initial P.n X) (MidState.initial P.n X) := by
  refine ⟨rfl, ?_, ?_, fun _ => BRB.instRel_init, fun _ => BRB.instRel_init⟩
  · intro k
    simp [LowState.initial, BRB.ImplState.initial]
  · intro k
    simp [LowState.initial, BRB.ImplState.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem lowRel_corrupt {s : LowState P.n X} {t : MidState P.n X}
    (hR : LowRel P s t) (id : Fin P.n) :
    LowRel P (s.corruptAll P id) (t.corruptAll P id) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (t.corruptAll P id).ga = s.ga.corrupt P id
    show t.ga.corrupt P id = s.ga.corrupt P id
    rw [hR.ga_eq]
  · intro k
    show ((s.brbIn k).corrupt P id).F = (s.ga.corrupt P id).F
    rw [SubState.corrupt_F, SubState.corrupt_F, hR.F_in_ga k]
  · intro k
    show ((s.brbBind k).corrupt P id).F = (s.ga.corrupt P id).F
    rw [SubState.corrupt_F, SubState.corrupt_F, hR.F_bind_ga k]
  · intro k
    exact BRB.instRel_corrupt (hR.inRel k) id
  · intro k
    exact BRB.instRel_corrupt (hR.bindRel k) id

/-! ### The commit chains -/

/-- A chain of `commitIn` rows covering a list of held entries. -/
private theorem commitsIn_reach {s : LowState P.n X} {j : Fin P.n} :
    ∀ (l : List (Fin P.n × X)) (t : MidState P.n X),
      LowRel P s t →
      (∀ p ∈ l, apIn P s j p.1 p.2) →
      ∃ ts : List (MidState P.n X),
        List.IsChain (fun a b => MidStep P a Gather.Lab.tau (PMF.pure b)) (t :: ts) ∧
        (ts.getLastD t).ga = t.ga ∧
        (ts.getLastD t).brbBind = t.brbBind ∧
        (∀ k v, (t.brbIn k).val = some v → ((ts.getLastD t).brbIn k).val = some v) ∧
        (∀ p ∈ l, ((ts.getLastD t).brbIn p.1).val = some p.2) ∧
        LowRel P s (ts.getLastD t)
  | [], t, hR, _ =>
    ⟨[], List.isChain_singleton t, rfl, rfl, fun _ _ h => h, by simp, hR⟩
  | p :: l, t, hR, hap => by
    rcases BRB.commitReach (hR.inRel p.1) (hap p (by simp)) with
      ⟨hval, -⟩ | ⟨hval, hm, hRel'⟩
    · obtain ⟨ts, hchain, hga, hbind, hmono, hcov, hR'⟩ :=
        commitsIn_reach l t hR (fun q hq => hap q (List.mem_cons_of_mem p hq))
      refine ⟨ts, hchain, hga, hbind, hmono, ?_, hR'⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hmono q.1 q.2 hval
      · exact hcov q hq'
    · have hm' : p.1 ∈ t.ga.F ∨ (t.brbIn p.1).input = some p.2 := by
        rcases hm with hF | hin
        · left
          have h1 : (t.brbIn p.1).F = s.ga.F := by
            rw [(hR.inRel p.1).F_eq, hR.F_in_ga p.1]
          rw [show t.ga.F = s.ga.F from by rw [hR.ga_eq], ← h1]
          exact hF
        · exact Or.inr hin
      have hstep : MidStep P t Gather.Lab.tau (PMF.pure
          { t with
            brbIn := Function.update t.brbIn p.1 { t.brbIn p.1 with val := some p.2 } }) :=
        MidStep.commitIn t p.1 p.2 hval hm'
      have hR1 : LowRel P s
          { t with
            brbIn := Function.update t.brbIn p.1 { t.brbIn p.1 with val := some p.2 } } := by
        refine ⟨hR.ga_eq, hR.F_in_ga, hR.F_bind_ga, ?_, hR.bindRel⟩
        intro k
        dsimp only
        by_cases hk : k = p.1
        · subst hk
          rw [Function.update_self]
          exact hRel'
        · rw [Function.update_of_ne hk]
          exact hR.inRel k
      obtain ⟨ts, hchain, hga, hbind, hmono, hcov, hR''⟩ :=
        commitsIn_reach l _ hR1 (fun q hq => hap q (List.mem_cons_of_mem p hq))
      refine ⟨({ t with
          brbIn := Function.update t.brbIn p.1 { t.brbIn p.1 with val := some p.2 } } :: ts),
        List.isChain_cons_cons.mpr ⟨hstep, hchain⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.getLastD_cons, hga]
      · rw [List.getLastD_cons, hbind]
      · intro k v hv
        rw [List.getLastD_cons]
        refine hmono k v ?_
        dsimp only
        by_cases hk : k = p.1
        · subst hk
          rw [hval] at hv
          exact absurd hv (by simp)
        · rw [Function.update_of_ne hk]
          exact hv
      · intro q hq
        rw [List.getLastD_cons]
        rcases List.mem_cons.mp hq with rfl | hq'
        · refine hmono q.1 q.2 ?_
          dsimp only
          rw [Function.update_self]
        · exact hcov q hq'
      · rw [List.getLastD_cons]
        exact hR''

/-- A chain of `commitBind` rows covering a list of held payloads. -/
private theorem commitsBind_reach {s : LowState P.n X} {j : Fin P.n} :
    ∀ (l : List (Fin P.n × APSet P.n X)) (t : MidState P.n X),
      LowRel P s t →
      (∀ p ∈ l, apBind P s j p.1 p.2) →
      ∃ ts : List (MidState P.n X),
        List.IsChain (fun a b => MidStep P a Gather.Lab.tau (PMF.pure b)) (t :: ts) ∧
        (ts.getLastD t).ga = t.ga ∧
        (ts.getLastD t).brbIn = t.brbIn ∧
        (∀ k v, (t.brbBind k).val = some v → ((ts.getLastD t).brbBind k).val = some v) ∧
        (∀ p ∈ l, ((ts.getLastD t).brbBind p.1).val = some p.2) ∧
        LowRel P s (ts.getLastD t)
  | [], t, hR, _ =>
    ⟨[], List.isChain_singleton t, rfl, rfl, fun _ _ h => h, by simp, hR⟩
  | p :: l, t, hR, hap => by
    rcases BRB.commitReach (hR.bindRel p.1) (hap p (by simp)) with
      ⟨hval, -⟩ | ⟨hval, hm, hRel'⟩
    · obtain ⟨ts, hchain, hga, hbin, hmono, hcov, hR'⟩ :=
        commitsBind_reach l t hR (fun q hq => hap q (List.mem_cons_of_mem p hq))
      refine ⟨ts, hchain, hga, hbin, hmono, ?_, hR'⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hmono q.1 q.2 hval
      · exact hcov q hq'
    · have hm' : p.1 ∈ t.ga.F ∨ (t.brbBind p.1).input = some p.2 := by
        rcases hm with hF | hin
        · left
          have h1 : (t.brbBind p.1).F = s.ga.F := by
            rw [(hR.bindRel p.1).F_eq, hR.F_bind_ga p.1]
          rw [show t.ga.F = s.ga.F from by rw [hR.ga_eq], ← h1]
          exact hF
        · exact Or.inr hin
      have hstep : MidStep P t Gather.Lab.tau (PMF.pure
          { t with
            brbBind := Function.update t.brbBind p.1 { t.brbBind p.1 with val := some p.2 } }) :=
        MidStep.commitBind t p.1 p.2 hval hm'
      have hR1 : LowRel P s
          { t with
            brbBind := Function.update t.brbBind p.1 { t.brbBind p.1 with val := some p.2 } } := by
        refine ⟨hR.ga_eq, hR.F_in_ga, hR.F_bind_ga, hR.inRel, ?_⟩
        intro k
        dsimp only
        by_cases hk : k = p.1
        · subst hk
          rw [Function.update_self]
          exact hRel'
        · rw [Function.update_of_ne hk]
          exact hR.bindRel k
      obtain ⟨ts, hchain, hga, hbin, hmono, hcov, hR''⟩ :=
        commitsBind_reach l _ hR1 (fun q hq => hap q (List.mem_cons_of_mem p hq))
      refine ⟨({ t with
          brbBind := Function.update t.brbBind p.1 { t.brbBind p.1 with val := some p.2 } } :: ts),
        List.isChain_cons_cons.mpr ⟨hstep, hchain⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.getLastD_cons, hga]
      · rw [List.getLastD_cons, hbin]
      · intro k v hv
        rw [List.getLastD_cons]
        refine hmono k v ?_
        dsimp only
        by_cases hk : k = p.1
        · subst hk
          rw [hval] at hv
          exact absurd hv (by simp)
        · rw [Function.update_of_ne hk]
          exact hv
      · intro q hq
        rw [List.getLastD_cons]
        rcases List.mem_cons.mp hq with rfl | hq'
        · refine hmono q.1 q.2 ?_
          dsimp only
          rw [Function.update_self]
        · exact hcov q hq'
      · rw [List.getLastD_cons]
        exact hR''

/-! ### The row transports -/

/-- The relation across the fused call. -/
theorem lowRel_call {s : LowState P.n X} {t : MidState P.n X}
    (hR : LowRel P s t) {id : Fin P.n} {x : X}
    (h : (s.ga.proc id).input = none)
    (hb : ((s.brbIn id).proc id).input = none) :
    LowRel P
      { s with
        ga := s.ga.setProc id { s.ga.proc id with input := some x }
        brbIn := Function.update s.brbIn id
          (((s.brbIn id).setProc id
            { (s.brbIn id).proc id with input := some x }).mcast id (.init x)) }
      { t with
        ga := t.ga.setProc id { t.ga.proc id with input := some x }
        brbIn := Function.update t.brbIn id
          { t.brbIn id with input := some x } } := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [hR.ga_eq]
  · intro k
    rw [show (s.ga.setProc id { s.ga.proc id with input := some x }).F
      = s.ga.F from rfl]
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self]
      rw [show ((((s.brbIn k).setProc k
        { (s.brbIn k).proc k with input := some x }).mcast k (.init x))).F
        = (s.brbIn k).F from rfl]
      exact hR.F_in_ga k
    · rw [Function.update_of_ne hk]
      exact hR.F_in_ga k
  · intro k
    exact hR.F_bind_ga k
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self, Function.update_self]
      exact BRB.instRel_call (hR.inRel k) hb
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      exact hR.inRel k
  · intro k
    exact hR.bindRel k

/-- The relation across any internal row, as a chain of the specification
tier's own internal rows. -/
theorem lowTau_reach {s s' : LowState P.n X} {t : MidState P.n X}
    (hR : LowRel P s t) (hstep : LowStep P s Gather.Lab.tau (PMF.pure s')) :
    ∃ ts : List (MidState P.n X),
      List.IsChain (fun a b => MidStep P a Gather.Lab.tau (PMF.pure b)) (t :: ts) ∧
      LowRel P s' (ts.getLastD t) := by
  generalize hμ : (PMF.pure s' : PMF (LowState P.n X)) = μ at hstep
  cases hstep with
  | brbInTau k b' h =>
    have hs' := pure_inj hμ
    subst hs'
    refine ⟨[], List.isChain_singleton t, ?_, ?_, hR.F_bind_ga, ?_, hR.bindRel⟩
    · exact hR.ga_eq
    · intro k'
      dsimp only
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self, BRB.implStep_tau_F h]
        exact hR.F_in_ga k'
      · rw [Function.update_of_ne hk]
        exact hR.F_in_ga k'
    · intro k'
      dsimp only
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact BRB.instRel_tau (hR.inRel k') h
      · rw [Function.update_of_ne hk]
        exact hR.inRel k'
  | brbBindTau k b' h =>
    have hs' := pure_inj hμ
    subst hs'
    refine ⟨[], List.isChain_singleton t, hR.ga_eq, hR.F_in_ga, ?_, hR.inRel, ?_⟩
    · intro k'
      dsimp only
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self, BRB.implStep_tau_F h]
        exact hR.F_bind_ga k'
      · rw [Function.update_of_ne hk]
        exact hR.F_bind_ga k'
    · intro k'
      dsimp only
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact BRB.instRel_tau (hR.bindRel k') h
      · rw [Function.update_of_ne hk]
        exact hR.bindRel k'
  | deliver i j m h =>
    have hs' := pure_inj hμ
    subst hs'
    refine ⟨[{ t with ga := t.ga.recvMsg i j m }],
      List.isChain_cons_cons.mpr ⟨MidStep.deliver t i j m
        (by rw [hR.ga_eq]; exact h), List.isChain_singleton _⟩, ?_⟩
    simp only [List.getLastD_cons, List.getLastD_nil]
    refine ⟨?_, ?_, ?_, hR.inRel, hR.bindRel⟩ <;> dsimp only
    · rw [hR.ga_eq]
    · intro k
      exact hR.F_in_ga k
    · intro k
      exact hR.F_bind_ga k
  | byz j m hj =>
    have hs' := pure_inj hμ
    subst hs'
    refine ⟨[{ t with ga := t.ga.mcast j m }],
      List.isChain_cons_cons.mpr ⟨MidStep.byz t j m
        (by rw [hR.ga_eq]; exact hj), List.isChain_singleton _⟩, ?_⟩
    simp only [List.getLastD_cons, List.getLastD_nil]
    refine ⟨?_, ?_, ?_, hR.inRel, hR.bindRel⟩ <;> dsimp only
    · rw [hR.ga_eq]
    · intro k
      rw [SubState.mcast_F]
      exact hR.F_in_ga k
    · intro k
      rw [SubState.mcast_F]
      exact hR.F_bind_ga k
  | echo j A hin happ hcard hsend =>
    have hs' := pure_inj hμ
    subst hs'
    obtain ⟨ts, hchain, hga, hbind, hmono, hcov, hR1⟩ :=
      commitsIn_reach A.toList t hR
        (fun p hp => happ p (Finset.mem_toList.mp hp))
    have hga1 : (ts.getLastD t).ga = s.ga := by
      rw [hga, hR.ga_eq]
    have hechostep : MidStep P (ts.getLastD t) Gather.Lab.tau
        (PMF.pure { ts.getLastD t with
          ga := ((ts.getLastD t).ga.setProc j
            { (ts.getLastD t).ga.proc j with sentEcho := some A }).mcast j
            (.echo A) }) := by
      refine MidStep.echo _ j A ?_ ?_ hcard ?_
      · rw [hga1]
        exact hin
      · intro p hp
        exact hcov p (Finset.mem_toList.mpr hp)
      · rw [hga1]
        exact hsend
    refine ⟨ts ++ [_], isChain_snoc hchain hechostep, ?_⟩
    rw [List.getLastD_concat]
    refine ⟨?_, ?_, ?_, hR1.inRel, hR1.bindRel⟩ <;> dsimp only
    · rw [hga1]
    · intro k
      rw [SubState.mcast_F]
      exact hR1.F_in_ga k
    · intro k
      rw [SubState.mcast_F]
      exact hR1.F_bind_ga k
  | vote j U hin happ hQ hsend =>
    have hs' := pure_inj hμ
    subst hs'
    obtain ⟨ts, hchain, hga, hbind, hmono, hcov, hR1⟩ :=
      commitsIn_reach U.toList t hR
        (fun p hp => happ p (Finset.mem_toList.mp hp))
    have hga1 : (ts.getLastD t).ga = s.ga := by
      rw [hga, hR.ga_eq]
    have hvotestep : MidStep P (ts.getLastD t) Gather.Lab.tau
        (PMF.pure { ts.getLastD t with
          ga := ((ts.getLastD t).ga.setProc j
            { (ts.getLastD t).ga.proc j with sentVote := some U }).mcast j
            (.vote U) }) := by
      refine MidStep.vote _ j U ?_ ?_ ?_ ?_
      · rw [hga1]
        exact hin
      · intro p hp
        exact hcov p (Finset.mem_toList.mpr hp)
      · obtain ⟨Q, hQc, hQm⟩ := hQ
        refine ⟨Q, hQc, ?_⟩
        intro q hq
        obtain ⟨A, hA, hAap, hAU⟩ := hQm q hq
        refine ⟨A, by rw [hga1]; exact hA, ?_, hAU⟩
        intro p hp
        exact hcov p (Finset.mem_toList.mpr (hAU hp))
      · rw [hga1]
        exact hsend
    refine ⟨ts ++ [_], isChain_snoc hchain hvotestep, ?_⟩
    rw [List.getLastD_concat]
    refine ⟨?_, ?_, ?_, hR1.inRel, hR1.bindRel⟩ <;> dsimp only
    · rw [hga1]
    · intro k
      rw [SubState.mcast_F]
      exact hR1.F_in_ga k
    · intro k
      rw [SubState.mcast_F]
      exact hR1.F_bind_ga k
  | bindCall j U hin hbc happ hQ =>
    have hs' := pure_inj hμ
    subst hs'
    obtain ⟨ts, hchain, hga, hbind, hmono, hcov, hR1⟩ :=
      commitsIn_reach U.toList t hR
        (fun p hp => happ p (Finset.mem_toList.mp hp))
    have hga1 : (ts.getLastD t).ga = s.ga := by
      rw [hga, hR.ga_eq]
    have hbindstep : MidStep P (ts.getLastD t) Gather.Lab.tau
        (PMF.pure { ts.getLastD t with
          brbBind := Function.update (ts.getLastD t).brbBind j
            { (ts.getLastD t).brbBind j with input := some U } }) := by
      refine MidStep.bindCall _ j U ?_ ?_ ?_ ?_
      · rw [hga1]
        exact hin
      · rw [hbind, (hR.bindRel j).input_eq]
        exact hbc
      · intro p hp
        exact hcov p (Finset.mem_toList.mpr hp)
      · obtain ⟨Q, hQc, hQm⟩ := hQ
        refine ⟨Q, hQc, ?_⟩
        intro q hq
        obtain ⟨W, hW, hWap, hWU⟩ := hQm q hq
        refine ⟨W, by rw [hga1]; exact hW, ?_, hWU⟩
        intro p hp
        exact hcov p (Finset.mem_toList.mpr (hWU hp))
    refine ⟨ts ++ [_], isChain_snoc hchain hbindstep, ?_⟩
    rw [List.getLastD_concat]
    refine ⟨?_, hR1.F_in_ga, ?_, hR1.inRel, ?_⟩ <;> dsimp only
    · rw [hga1]
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        exact hR1.F_bind_ga k
      · rw [Function.update_of_ne hk]
        exact hR1.F_bind_ga k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        exact BRB.instRel_call (hR1.bindRel k) hbc
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR1.bindRel k

private theorem getLastD_append {α : Type*} (d : α) :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).getLastD d = l₂.getLastD (l₁.getLastD d)
  | [], _ => rfl
  | a :: l₁, l₂ => by
    rw [List.cons_append, List.getLastD_cons, List.getLastD_cons,
      getLastD_append a l₁ l₂]

/-! ### The return burst -/

/-- The return answer, as chain data: from a related pair and the
implementation's return guards, a chain of the specification tier's internal
rows reaches a state where its return guards hold, the relation restored
across the pair of return effects. -/
theorem lowRetBurst {s : LowState P.n X} {t : MidState P.n X}
    (hR : LowRel P s t) {id : Fin P.n} {g : Fin P.n → Option X}
    (hin : (s.ga.proc id).input ≠ none)
    (hsubap : ∀ k x, g k = some x → apIn P s id k x)
    (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ U, apBind P s id q U ∧ APSet.subMap U g)
    (hr : (s.ga.proc id).returned = false) :
    ∃ ts : List (MidState P.n X),
      List.IsChain (fun a b => MidStep P a Gather.Lab.tau (PMF.pure b)) (t :: ts) ∧
      ((ts.getLastD t).ga.proc id).input ≠ none ∧
      (∀ k x, g k = some x → ((ts.getLastD t).brbIn k).val = some x) ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, ((ts.getLastD t).brbBind q).val = some U ∧ APSet.subMap U g) ∧
      ((ts.getLastD t).ga.proc id).returned = false ∧
      LowRel P
        { s with ga := s.ga.setProc id { s.ga.proc id with returned := true } }
        { ts.getLastD t with
          ga := (ts.getLastD t).ga.setProc id
            { (ts.getLastD t).ga.proc id with returned := true } } := by
  classical
  obtain ⟨Q, hQc, hQm⟩ := hQ
  -- the input-entry chain
  set lg : List (Fin P.n × X) := (List.finRange P.n).filterMap
    (fun k => (g k).map (fun x => (k, x))) with hlg
  have hlg_mem : ∀ k x, g k = some x → (k, x) ∈ lg := by
    intro k x hx
    rw [hlg, List.mem_filterMap]
    exact ⟨k, List.mem_finRange k, by rw [hx]; rfl⟩
  have hlg_ap : ∀ p ∈ lg, apIn P s id p.1 p.2 := by
    intro p hp
    rw [hlg, List.mem_filterMap] at hp
    obtain ⟨k, -, hk⟩ := hp
    rcases hgk : g k with _ | x
    · rw [hgk] at hk
      exact absurd hk (by simp)
    · rw [hgk] at hk
      simp only [Option.map_some] at hk
      obtain rfl : (k, x) = p := by injection hk
      exact hsubap k x hgk
  obtain ⟨ts₁, hchain₁, hga₁, hbind₁, hmono₁, hcov₁, hR₁⟩ :=
    commitsIn_reach lg t hR hlg_ap
  -- the bind-payload chain
  set u : Fin P.n → APSet P.n X := fun q =>
    if h : ∃ U, apBind P s id q U ∧ APSet.subMap U g then h.choose else ∅
    with hu_def
  have hu : ∀ q ∈ Q, apBind P s id q (u q) ∧ APSet.subMap (u q) g := by
    intro q hq
    have hex := hQm q hq
    rw [hu_def]
    dsimp only
    rw [dif_pos hex]
    exact hex.choose_spec
  set lb : List (Fin P.n × APSet P.n X) := Q.toList.map (fun q => (q, u q))
    with hlb
  have hlb_ap : ∀ p ∈ lb, apBind P s id p.1 p.2 := by
    intro p hp
    rw [hlb, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (hu q (Finset.mem_toList.mp hq)).1
  obtain ⟨ts₂, hchain₂, hga₂, hbin₂, hmono₂, hcov₂, hR₂⟩ :=
    commitsBind_reach lb (ts₁.getLastD t) hR₁ hlb_ap
  have hga : (ts₂.getLastD (ts₁.getLastD t)).ga = s.ga := by
    rw [hga₂, hga₁, hR.ga_eq]
  refine ⟨ts₁ ++ ts₂, isChain_trans hchain₁ hchain₂, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [getLastD_append]
  · rw [hga]
    exact hin
  · intro k x hx
    rw [hbin₂]
    exact hcov₁ (k, x) (hlg_mem k x hx)
  · refine ⟨Q, hQc, ?_⟩
    intro q hq
    refine ⟨u q, hcov₂ (q, u q) ?_, (hu q hq).2⟩
    rw [hlb, List.mem_map]
    exact ⟨q, Finset.mem_toList.mpr hq, rfl⟩
  · rw [hga]
    exact hr
  · refine ⟨?_, hR₂.F_in_ga, hR₂.F_bind_ga, hR₂.inRel, hR₂.bindRel⟩
    dsimp only
    rw [hga]

/-! ### The refinement -/

/-- **The broadcast substitution**: the gather-over-Bracha instance
forward-simulates the gather-over-BRB-specification instance. -/
theorem gatherLow (P : Params) (X : Type) [DecidableEq X] :
    ForwardSimulation (lowInst P X) (midInst P X) (LowRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  rw [lowInst_step] at hstep
  cases hstep with
  | call id x h hb =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (MidStep.call q₂ id x (by rw [hR.ga_eq]; exact h))⟩,
      lowRel_call hR h hb⟩
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (MidStep.callLoop q₂ id x)⟩, hR⟩
  | brbInTau k b' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ := lowTau_reach hR (LowStep.brbInTau q₁ k b' h)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | brbBindTau k b' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ := lowTau_reach hR (LowStep.brbBindTau q₁ k b' h)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ := lowTau_reach hR (LowStep.deliver q₁ i j m h)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | echo j A hin happ hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ :=
      lowTau_reach hR (LowStep.echo q₁ j A hin happ hcard hsend)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | vote j U hin happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ :=
      lowTau_reach hR (LowStep.vote q₁ j U hin happ hQ hsend)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | bindCall j U hin hbc happ hQ =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ :=
      lowTau_reach hR (LowStep.bindCall q₁ j U hin hbc happ hQ)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | byz j m hj =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ := lowTau_reach hR (LowStep.byz q₁ j m hj)
    exact ⟨_, Or.inl ⟨rfl, System.weakLSilent_ofChain hchain⟩, hR'⟩
  | ret id g hin hsubap hQ hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hin', hcov, hQ', hr', hRel⟩ :=
      lowRetBurst hR hin hsubap hQ hr
    have hretstep : MidStep P (ts.getLastD q₂) (Gather.Lab.ret id g)
        (PMF.pure { ts.getLastD q₂ with
          ga := (ts.getLastD q₂).ga.setProc id
            { (ts.getLastD q₂).ga.proc id with returned := true } }) :=
      MidStep.ret _ id g hin' hcov hQ' hr'
    exact ⟨_, Or.inr ⟨by simp,
      System.weakLStep_tausThen hchain hretstep (by simp)⟩, hRel⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corruptAll P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (MidStep.fail q₂ id)⟩, lowRel_corrupt hR id⟩

/-- info: 'PLTS.ABA.Gather.gatherLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherLow

end Gather
end ABA
end PLTS
