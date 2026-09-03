/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCALow
import Leslie2Protocols.ABA.GatherLowSim
import Leslie2Protocols.Framework.WeakBurst

/-!
# The broadcast substitution inside the round

`GBCA.lowRefines`: the GBCA implementation (`ABA/GBCALow.lean`)
forward-simulates the GBCA instance over the gather-over-BRB components
(`ABA/GBCAIdeal.lean`), along the componentwise pairing of the broadcast
substitution relation. Everything is inherited from the gather-level
substitution (`ABA/GatherLowSim.lean`): the internal rows replay
`Gather.lowTau_reach`, the fused calls `Gather.lowRel_call`, and the fused
returns `Gather.lowRetBurst`, the chains mapping into the pair's embedded
rows coordinate by coordinate.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Gather

variable {P : Params}

/-- `PMF.pure` is injective (via its singleton support). -/
private theorem pure_inj {α : Type*} {a b : α} (h : PMF.pure a = PMF.pure b) :
    a = b := by
  have ha : a ∈ (PMF.pure a).support := by rw [PMF.mem_support_pure_iff]
  rw [h, PMF.mem_support_pure_iff] at ha
  exact ha

/-- The broadcast substitution relation, per coordinate. -/
def LowPairRel (P : Params) (s : LowPairState P.n) (t : IdealState P.n) : Prop :=
  Gather.LowRel P s.1 t.1 ∧ Gather.LowRel P s.2 t.2

/-- The relation holds initially. -/
theorem lowPairRel_init :
    LowPairRel P (LowPairState.initial P.n) (IdealState.initial P.n) :=
  ⟨Gather.lowRel_init, Gather.lowRel_init⟩

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem lowPairRel_corrupt {s : LowPairState P.n} {t : IdealState P.n}
    (hR : LowPairRel P s t) (id : Fin P.n) :
    LowPairRel P (s.1.corruptAll P id, s.2.corruptAll P id)
      (t.1.corruptAll P id, t.2.corruptAll P id) :=
  ⟨Gather.lowRel_corrupt hR.1 id, Gather.lowRel_corrupt hR.2 id⟩

/-- Mapping a first-coordinate τ-chain of gather-over-BRB steps into the
pair. -/
private theorem chain_map_ga1 {r : ℕ} (t2 : Gather.MidState P.n (Option Bool))
    {t : Gather.MidState P.n Bool} {ts : List (Gather.MidState P.n Bool)}
    (h : List.IsChain (fun a b => Gather.MidStep P a Gather.Lab.tau (PMF.pure b))
      (t :: ts)) :
    List.IsChain (fun A B => (idealInst P r).LStep A Silent.τ B)
      ((t, t2) :: ts.map (fun x => (x, t2))) := by
  induction ts generalizing t with
  | nil => exact List.isChain_singleton _
  | cons b l ih =>
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨IdealStep.ga1Tau (t, t2) b hab, ih hbl⟩

/-- Mapping a second-coordinate τ-chain of gather-over-BRB steps into the
pair. -/
private theorem chain_map_ga2 {r : ℕ} (t1 : Gather.MidState P.n Bool)
    {t : Gather.MidState P.n (Option Bool)}
    {ts : List (Gather.MidState P.n (Option Bool))}
    (h : List.IsChain (fun a b => Gather.MidStep P a Gather.Lab.tau (PMF.pure b))
      (t :: ts)) :
    List.IsChain (fun A B => (idealInst P r).LStep A Silent.τ B)
      ((t1, t) :: ts.map (fun x => (t1, x))) := by
  induction ts generalizing t with
  | nil => exact List.isChain_singleton _
  | cons b l ih =>
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨IdealStep.ga2Tau (t1, t) b hab, ih hbl⟩

private theorem getLastD_map {α β : Type*} (f : α → β) (d : α) :
    ∀ l : List α, (l.map f).getLastD (f d) = f (l.getLastD d)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.getLastD_cons, List.getLastD_cons, getLastD_map f a l]

/-- **The broadcast substitution**: the GBCA implementation forward-simulates
the GBCA instance over the gather-over-BRB components. -/
theorem lowRefines (P : Params) (r : ℕ) :
    ForwardSimulation (lowPairInst P r) (idealInst P r) (LowPairRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  rw [lowPairInst_step] at hstep
  cases hstep with
  | callG id b t1' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.LowState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall hbcall =>
      have ht1' := pure_inj hμ
      subst ht1'
      refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (IdealStep.callG q₂ id b _
          (Gather.MidStep.call q₂.1 id b (by rw [hR.1.ga_eq]; exact hcall)))⟩,
        Gather.lowRel_call hR.1 hcall hbcall, hR.2⟩
    | callLoop id' b' =>
      have ht1' := pure_inj hμ
      subst ht1'
      exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (IdealStep.callG q₂ id b q₂.1 (Gather.MidStep.callLoop q₂.1 id b))⟩, hR⟩
  | ga1Tau t1' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ := Gather.lowTau_reach hR.1 h
    refine ⟨(ts.getLastD q₂.1, q₂.2), Or.inl ⟨rfl, ?_⟩, hR', hR.2⟩
    have hrun := System.weakLSilent_ofChain (chain_map_ga1 (r := r) q₂.2 hchain)
    rwa [getLastD_map] at hrun
  | ga2Tau t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hR'⟩ := Gather.lowTau_reach hR.2 h
    refine ⟨(q₂.1, ts.getLastD q₂.2), Or.inl ⟨rfl, ?_⟩, hR.1, hR'⟩
    have hrun := System.weakLSilent_ofChain (chain_map_ga2 (r := r) q₂.1 hchain)
    rwa [getLastD_map] at hrun
  | link id g t1' h h2 hb2 =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.LowState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' hin hsubap hQ hr =>
      have ht1' := pure_inj hμ
      subst ht1'
      obtain ⟨ts, hchain, hin', hcov, hQ', hr', hRel1⟩ :=
        Gather.lowRetBurst hR.1 hin hsubap hQ hr
      have hguard2 : (q₂.2.ga.proc id).input = none := by
        rw [hR.2.ga_eq]
        exact h2
      have hchain' := chain_map_ga1 (r := r) q₂.2 hchain
      have hlinkstep : (idealInst P r).LStep
          ((ts.map (fun x => (x, q₂.2))).getLastD (q₂.1, q₂.2)) Silent.τ
          ({ ts.getLastD q₂.1 with
            ga := (ts.getLastD q₂.1).ga.setProc id
              { (ts.getLastD q₂.1).ga.proc id with returned := true } },
           { q₂.2 with
            ga := q₂.2.ga.setProc id
              { q₂.2.ga.proc id with input := some (cand P g) }
            brbIn := Function.update q₂.2.brbIn id
              { q₂.2.brbIn id with input := some (cand P g) } }) := by
        rw [show ((q₂.1, q₂.2) : IdealState P.n)
            = (fun x => (x, q₂.2)) q₂.1 from rfl, getLastD_map]
        exact IdealStep.link ((ts.getLastD q₂.1), q₂.2) id g _
          (Gather.MidStep.ret _ id g hin' hcov hQ' hr') hguard2
      refine ⟨({ ts.getLastD q₂.1 with
          ga := (ts.getLastD q₂.1).ga.setProc id
            { (ts.getLastD q₂.1).ga.proc id with returned := true } },
        { q₂.2 with
          ga := q₂.2.ga.setProc id
            { q₂.2.ga.proc id with input := some (cand P g) }
          brbIn := Function.update q₂.2.brbIn id
            { q₂.2.brbIn id with input := some (cand P g) } }),
        Or.inl ⟨rfl, ?_⟩, hRel1,
        Gather.lowRel_call (x := cand P g) hR.2 h2 hb2⟩
      have hfull := isChain_snoc hchain' hlinkstep
      have hrun := System.weakLSilent_ofChain hfull
      rwa [List.getLastD_concat] at hrun
  | retG id g t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2' : PMF (Gather.LowState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' hin hsubap hQ hr =>
      have ht2' := pure_inj hμ
      subst ht2'
      obtain ⟨ts, hchain, hin', hcov, hQ', hr', hRel2⟩ :=
        Gather.lowRetBurst hR.2 hin hsubap hQ hr
      have hchain' := chain_map_ga2 (r := r) q₂.1 hchain
      have hlaststep : (idealInst P r).LStep
          ((ts.map (fun x => (q₂.1, x))).getLastD (q₂.1, q₂.2))
          (Lab.retG r id (gradeOf P g))
          (q₂.1, { ts.getLastD q₂.2 with
            ga := (ts.getLastD q₂.2).ga.setProc id
              { (ts.getLastD q₂.2).ga.proc id with returned := true } }) := by
        rw [show ((q₂.1, q₂.2) : IdealState P.n)
            = (fun x => (q₂.1, x)) q₂.2 from rfl, getLastD_map]
        exact IdealStep.retG (q₂.1, ts.getLastD q₂.2) id g _
          (Gather.MidStep.ret _ id g hin' hcov hQ' hr')
      exact ⟨_, Or.inr ⟨by simp,
        System.weakLStep_tausThen hchain' hlaststep (by simp)⟩, hR.1, hRel2⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨(q₂.1.corruptAll P id, q₂.2.corruptAll P id),
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (IdealStep.fail q₂ id)⟩, lowPairRel_corrupt hR id⟩

/-- info: 'PLTS.ABA.GBCA.lowRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowRefines

end GBCA
end ABA
end PLTS
