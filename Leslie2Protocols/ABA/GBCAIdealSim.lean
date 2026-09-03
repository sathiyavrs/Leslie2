/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCAIdeal
import Leslie2Protocols.ABA.GatherSim
import Leslie2Protocols.Framework.WeakBurst

/-!
# The gather substitution inside the round

`GBCA.idealRefines`: the GBCA instance over the gather-over-BRB components
(`ABA/GBCAIdeal.lean`) forward-simulates the GBCA instance over the gather
specifications (`ABA/GBCAPair.lean`), along the componentwise pairing of the
gather refinement relation.

Everything is inherited from the gather refinement (`ABA/GatherSim.lean`):
internal gather rows transport by `Gather.coreRel_tau` under a stutter, the
fused calls by `Gather.coreRel_call`, and the two fused returns replay
`Gather.retBurst` — its τ-chain of gather specification steps maps into the
pair's own embedded rows coordinate by coordinate, and its final return
guards feed the pair's fused row.
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

/-- The gather substitution relation: the gather refinement relation, per
coordinate. -/
def IdealRel (P : Params) (s : IdealState P.n) (t : PairState P.n) : Prop :=
  Gather.CoreRel P s.1 t.1 ∧ Gather.CoreRel P s.2 t.2

/-- The relation holds initially. -/
theorem idealRel_init :
    IdealRel P (IdealState.initial P.n) (PairState.initial P.n) :=
  ⟨Gather.coreRel_init, Gather.coreRel_init⟩

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem idealRel_corrupt {s : IdealState P.n} {t : PairState P.n}
    (hR : IdealRel P s t) (id : Fin P.n) :
    IdealRel P (s.1.corruptAll P id, s.2.corruptAll P id)
      (t.1.corrupt P id, t.2.corrupt P id) :=
  ⟨Gather.coreRel_corrupt hR.1 id, Gather.coreRel_corrupt hR.2 id⟩

/-- Mapping a first-coordinate τ-chain of gather specification steps into the
pair. -/
private theorem chain_map_ga1 {r : ℕ} (t2 : Gather.SpecState P.n (Option Bool))
    {t : Gather.SpecState P.n Bool} {ts : List (Gather.SpecState P.n Bool)}
    (h : List.IsChain (fun a b => Gather.Step P a Gather.Lab.tau (PMF.pure b))
      (t :: ts)) :
    List.IsChain (fun A B => (pairInst P r).LStep A Silent.τ B)
      ((t, t2) :: ts.map (fun x => (x, t2))) := by
  induction ts generalizing t with
  | nil => exact List.isChain_singleton _
  | cons b l ih =>
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨PairStep.ga1Tau (t, t2) b hab, ih hbl⟩

/-- Mapping a second-coordinate τ-chain of gather specification steps into
the pair. -/
private theorem chain_map_ga2 {r : ℕ} (t1 : Gather.SpecState P.n Bool)
    {t : Gather.SpecState P.n (Option Bool)}
    {ts : List (Gather.SpecState P.n (Option Bool))}
    (h : List.IsChain (fun a b => Gather.Step P a Gather.Lab.tau (PMF.pure b))
      (t :: ts)) :
    List.IsChain (fun A B => (pairInst P r).LStep A Silent.τ B)
      ((t1, t) :: ts.map (fun x => (t1, x))) := by
  induction ts generalizing t with
  | nil => exact List.isChain_singleton _
  | cons b l ih =>
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨PairStep.ga2Tau (t1, t) b hab, ih hbl⟩

private theorem getLastD_map {α β : Type*} (f : α → β) (d : α) :
    ∀ l : List α, (l.map f).getLastD (f d) = f (l.getLastD d)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.getLastD_cons, List.getLastD_cons, getLastD_map f a l]

/-- **The gather substitution**: the GBCA instance over the gather
implementations forward-simulates the GBCA instance over the gather
specifications. -/
theorem idealRefines (P : Params) (r : ℕ) :
    ForwardSimulation (idealInst P r) (pairInst P r) (IdealRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  rw [idealInst_step] at hstep
  cases hstep with
  | callG id b t1' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.MidState P.n Bool)) = μ1 at h
    cases h with
    | call id' b' hcall =>
      have ht1' := pure_inj hμ
      subst ht1'
      refine ⟨_, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (PairStep.callG q₂ id b _
          (Gather.Step.call q₂.1 id b (by rw [hR.1.call_eq id]; exact hcall)))⟩,
        Gather.coreRel_call hR.1 hcall, hR.2⟩
    | callLoop id' b' =>
      have ht1' := pure_inj hμ
      subst ht1'
      exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (PairStep.callG q₂ id b q₂.1 (Gather.Step.callLoop q₂.1 id b))⟩, hR⟩
  | ga1Tau t1' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      Gather.coreRel_tau hR.1 h, hR.2⟩
  | ga2Tau t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hR.1, Gather.coreRel_tau hR.2 h⟩
  | link id g t1' h h2 =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t1' : PMF (Gather.MidState P.n Bool)) = μ1 at h
    cases h with
    | ret id' g' hin hsub hQ hr =>
      have ht1' := pure_inj hμ
      subst ht1'
      obtain ⟨ts, Cs, hchain, hCs, hmem, hcov, hret1, hRel1⟩ :=
        Gather.retBurst hR.1 hin hsub hQ hr
      have hguard2 : q₂.2.call id = none := by
        rw [hR.2.call_eq id]
        exact h2
      have hchain' := chain_map_ga1 (r := r) q₂.2 hchain
      have hlinkstep : (pairInst P r).LStep
          ((ts.map (fun x => (x, q₂.2))).getLastD (q₂.1, q₂.2)) Silent.τ
          ({ ts.getLastD q₂.1 with
            ret := Function.update (ts.getLastD q₂.1).ret id true },
           { q₂.2 with
            call := Function.update q₂.2.call id (some (cand P g)) }) := by
        rw [show ((q₂.1, q₂.2) : PairState P.n)
            = (fun x => (x, q₂.2)) q₂.1 from rfl, getLastD_map]
        exact PairStep.link ((ts.getLastD q₂.1), q₂.2) id g _
          (Gather.Step.ret _ id g Cs hCs hmem hcov hret1) hguard2
      refine ⟨({ ts.getLastD q₂.1 with
          ret := Function.update (ts.getLastD q₂.1).ret id true },
        { q₂.2 with call := Function.update q₂.2.call id (some (cand P g)) }),
        Or.inl ⟨rfl, ?_⟩, hRel1, Gather.coreRel_call (x := cand P g) hR.2 h2⟩
      have hfull := isChain_snoc hchain' hlinkstep
      have hrun := System.weakLSilent_ofChain hfull
      rwa [List.getLastD_concat] at hrun
  | retG id g t2' h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    generalize hμ : (PMF.pure t2' : PMF (Gather.MidState P.n (Option Bool))) = μ2 at h
    cases h with
    | ret id' g' hin hsub hQ hr =>
      have ht2' := pure_inj hμ
      subst ht2'
      obtain ⟨ts, Cs, hchain, hCs, hmem, hcov, hret1, hRel2⟩ :=
        Gather.retBurst hR.2 hin hsub hQ hr
      have hchain' := chain_map_ga2 (r := r) q₂.1 hchain
      have hlaststep : (pairInst P r).LStep
          ((ts.map (fun x => (q₂.1, x))).getLastD (q₂.1, q₂.2))
          (Lab.retG r id (gradeOf P g))
          (q₂.1, { ts.getLastD q₂.2 with
            ret := Function.update (ts.getLastD q₂.2).ret id true }) := by
        rw [show ((q₂.1, q₂.2) : PairState P.n)
            = (fun x => (q₂.1, x)) q₂.2 from rfl, getLastD_map]
        exact PairStep.retG (q₂.1, ts.getLastD q₂.2) id g _
          (Gather.Step.ret _ id g Cs hCs hmem hcov hret1)
      exact ⟨_, Or.inr ⟨by simp,
        System.weakLStep_tausThen hchain' hlaststep (by simp)⟩, hR.1, hRel2⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨(q₂.1.corrupt P id, q₂.2.corrupt P id),
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (PairStep.fail q₂ id)⟩, idealRel_corrupt hR id⟩

/-- info: 'PLTS.ABA.GBCA.idealRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idealRefines

end GBCA
end ABA
end PLTS
