/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.Flat
import Leslie2Protocols.ABA.AFW.Chain

/-!
# The gather-based protocol into its composed reading

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed P`
reads the same protocol as a composition of components. This file carries the
first into the second, which is where the gather-based chain passes from
implementation to specification, as `ABA/ABDY/ProtocolSim.lean` does for the
ladder. Everything here is read in the namespace `AFW`, where each name is
that of its ladder-chain counterpart, and the qualifier is dropped below.

## The composed state is a view of the flat one

The relation is a function, not a correspondence: a state of `composed P` is
computed from a state of `protocol P`. The round loops and the coin oracle
are shared objects, the ABA-side network is the DECIDED pools beside the
corrupted set, and the round-`r` instance is assembled by `toPair`. Assembling
it undoes the two rearrangements the flat reading performs. The boxes are
transposed back: the instance's box vector at round `r` is read off the round
records the `n` processes hold. And the pools are sliced: the instance's
fabric carries the messages of one tag, recovered from the adversary's single
tagged pool family by `slice`.

Slicing commutes with the adversary's pool write in the only two ways a step
needs (`slice_post_some`, `slice_post_none`): a message of the tag being
sliced arrives in that slice, and a message of any other tag leaves the slice
alone. Together with the two lemmas that read a written round record
(`stage_update_self`, `stage_update_ne`) these are what every row of the
simulation is discharged by.
-/

namespace PLTS
namespace ABA
namespace AFW

open Net Gather

/-! ### Two extensionality helpers -/

/-- A fabric is its pool family beside its corrupted set. -/
theorem fabric_ext {n : ℕ} {M : Type} {a b : Fabric n M}
    (hp : a.pool = b.pool) (hF : a.F = b.F) : a = b := by
  cases a; cases b; simp_all

/-- A gather-over-Bracha state is its gather instance beside its two
broadcast families. -/
theorem lowState_ext {n : ℕ} {X : Type} {a b : Gather.LowState n X}
    (h1 : a.ga = b.ga) (h2 : a.brbIn = b.brbIn) (h3 : a.brbBind = b.brbBind) :
    a = b := by
  cases a; cases b; simp_all

/-! ### Slicing a tagged pool -/

variable {n : ℕ} {β : Type}

/-- The messages of one tag, recovered from a tagged pool family along a
partial untagging. -/
def slice (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (pool : Fin n → Finset (Msg n)) : Fin n → Finset β :=
  fun q => (pool q).filterMap f hf

theorem mem_slice {f : Msg n → Option β}
    {hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'}
    {pool : Fin n → Finset (Msg n)} {q : Fin n} {b : β} :
    b ∈ slice f hf pool q ↔ ∃ m ∈ pool q, f m = some b :=
  Finset.mem_filterMap f

/-- A pooled message of another tag leaves the slice alone. -/
theorem slice_post_none (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (pool : Fin n → Finset (Msg n)) (j : Fin n) (m : Msg n) (hm : f m = none) :
    slice f hf (Function.update pool j (insert m (pool j))) = slice f hf pool := by
  funext q
  ext b
  rw [mem_slice, mem_slice]
  constructor
  · rintro ⟨a, ha, hab⟩
    by_cases hq : q = j
    · subst hq
      rw [Function.update_self, Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · rw [hm] at hab; exact absurd hab (by simp)
      · exact ⟨a, ha, hab⟩
    · rw [Function.update_of_ne hq] at ha
      exact ⟨a, ha, hab⟩
  · rintro ⟨a, ha, hab⟩
    refine ⟨a, ?_, hab⟩
    by_cases hq : q = j
    · subst hq
      rw [Function.update_self, Finset.mem_insert]
      exact Or.inr ha
    · rwa [Function.update_of_ne hq]

/-- A pooled message of the tag being sliced arrives in that slice. -/
theorem slice_post_some [DecidableEq β] (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (pool : Fin n → Finset (Msg n)) (j : Fin n) (m : Msg n) (b : β)
    (hm : f m = some b) :
    slice f hf (Function.update pool j (insert m (pool j)))
      = Function.update (slice f hf pool) j (insert b (slice f hf pool j)) := by
  funext q
  by_cases hq : q = j
  · subst hq
    rw [Function.update_self]
    ext c
    rw [mem_slice, Finset.mem_insert, mem_slice]
    constructor
    · rintro ⟨a, ha, hac⟩
      rw [Function.update_self, Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · rw [hm] at hac
        exact Or.inl (Option.some.inj hac).symm
      · exact Or.inr ⟨a, ha, hac⟩
    · rintro (rfl | ⟨a, ha, hac⟩)
      · exact ⟨m, by rw [Function.update_self]; exact Finset.mem_insert_self _ _, hm⟩
      · refine ⟨a, ?_, hac⟩
        rw [Function.update_self, Finset.mem_insert]
        exact Or.inr ha
  · rw [Function.update_of_ne hq]
    ext c
    rw [mem_slice, mem_slice]
    constructor
    · rintro ⟨a, ha, hac⟩
      rw [Function.update_of_ne hq] at ha
      exact ⟨a, ha, hac⟩
    · rintro ⟨a, ha, hac⟩
      exact ⟨a, by rw [Function.update_of_ne hq]; exact ha, hac⟩

/-! ### The six untaggings -/

/-- The first gather's fabric messages. -/
def unGa1 : Msg n → Option (GaMsg n Bool)
  | .ga1 m => some m
  | _ => none

/-- The second gather's fabric messages. -/
def unGa2 : Msg n → Option (GaMsg n (Option Bool))
  | .ga2 m => some m
  | _ => none

/-- The messages of input-broadcast instance `i` of the first gather. -/
def unIn1 (i : Fin n) : Msg n → Option (BRB.BMsg Bool)
  | .brbIn1 i' m => if i' = i then some m else none
  | _ => none

/-- The messages of bind-broadcast instance `i` of the first gather. -/
def unBind1 (i : Fin n) : Msg n → Option (BRB.BMsg (APSet n Bool))
  | .brbBind1 i' m => if i' = i then some m else none
  | _ => none

/-- The messages of input-broadcast instance `i` of the second gather. -/
def unIn2 (i : Fin n) : Msg n → Option (BRB.BMsg (Option Bool))
  | .brbIn2 i' m => if i' = i then some m else none
  | _ => none

/-- The messages of bind-broadcast instance `i` of the second gather. -/
def unBind2 (i : Fin n) : Msg n → Option (BRB.BMsg (APSet n (Option Bool)))
  | .brbBind2 i' m => if i' = i then some m else none
  | _ => none

theorem unGa1_inj : ∀ a a' (b : GaMsg n Bool),
    b ∈ unGa1 a → b ∈ unGa1 a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unGa1]

theorem unGa2_inj : ∀ a a' (b : GaMsg n (Option Bool)),
    b ∈ unGa2 a → b ∈ unGa2 a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unGa2]

theorem unIn1_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg Bool),
    b ∈ unIn1 i a → b ∈ unIn1 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unIn1]

theorem unBind1_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg (APSet n Bool)),
    b ∈ unBind1 i a → b ∈ unBind1 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unBind1]

theorem unIn2_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg (Option Bool)),
    b ∈ unIn2 i a → b ∈ unIn2 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unIn2]

theorem unBind2_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg (APSet n (Option Bool))),
    b ∈ unBind2 i a → b ∈ unBind2 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unBind2]

/-! ### The composed round instance, assembled -/

variable {P : Params}

/-- The round-`r` state of the first gather instance, read off the flat
state: the box vector transposed out of the round records the processes hold,
and the fabrics sliced out of the adversary's tagged pools. -/
def toLow1 (P : Params) (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (r : ℕ) : Gather.LowState P.n Bool where
  ga := (fun i => ((u i).2.stage r).ga1, ⟨slice unGa1 unGa1_inj (w.pool r), w.F⟩)
  brbIn := fun k =>
    (fun i => ((u i).2.stage r).brbIn1 k, ⟨slice (unIn1 k) (unIn1_inj k) (w.pool r), w.F⟩)
  brbBind := fun k =>
    (fun i => ((u i).2.stage r).brbBind1 k,
      ⟨slice (unBind1 k) (unBind1_inj k) (w.pool r), w.F⟩)

/-- The round-`r` state of the second gather instance, read off the flat
state. -/
def toLow2 (P : Params) (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (r : ℕ) : Gather.LowState P.n (Option Bool) where
  ga := (fun i => ((u i).2.stage r).ga2, ⟨slice unGa2 unGa2_inj (w.pool r), w.F⟩)
  brbIn := fun k =>
    (fun i => ((u i).2.stage r).brbIn2 k, ⟨slice (unIn2 k) (unIn2_inj k) (w.pool r), w.F⟩)
  brbBind := fun k =>
    (fun i => ((u i).2.stage r).brbBind2 k,
      ⟨slice (unBind2 k) (unBind2_inj k) (w.pool r), w.F⟩)

/-- The round-`r` instance of the composed reading, read off the flat
state. -/
def toPair (P : Params) (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (r : ℕ) : GBCA.LowPairState P.n :=
  (toLow1 P u w r, toLow2 P u w r)

/-! ### Reading a written round record -/

/-- The round record a process holds at the round it has just written. -/
theorem stage_update_self {u : ∀ _ : Fin P.n, ProcRec P.n} {j : Fin P.n}
    {c : CoreRec P.n} {p : StageSideRec P.n} (hu : (u j).2 = p) (r : ℕ)
    (sr : StageRec P.n) (i : Fin P.n) :
    ((Function.update u j (c, p.setStage r sr) i).2.stage r)
      = if i = j then sr else ((u i).2.stage r) := by
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    simp
  · rw [Function.update_of_ne hi, if_neg hi]

/-- The round records a process holds at every other round. -/
theorem stage_update_ne {u : ∀ _ : Fin P.n, ProcRec P.n} {j : Fin P.n}
    {c : CoreRec P.n} {p : StageSideRec P.n} (hu : (u j).2 = p) {r r' : ℕ}
    (hr : r' ≠ r) (sr : StageRec P.n) (i : Fin P.n) :
    ((Function.update u j (c, p.setStage r sr) i).2.stage r') = ((u i).2.stage r') := by
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    change ((p.setStage r sr).stage r') = _
    rw [StageSideRecP.stage_setStage_ne _ _ _ hr, hu]
  · rw [Function.update_of_ne hi]

/-- The round loop a process holds is untouched by a round-record write. -/
@[simp] theorem core_update {u : ∀ _ : Fin P.n, ProcRec P.n} {j : Fin P.n}
    (x : ProcRec P.n) (i : Fin P.n) :
    (Function.update u j x i).1 = if i = j then x.1 else (u i).1 := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hi, if_neg hi]

/-! ### The relation -/

/-- **The composition relation**: the round loops and the coin oracle are
shared, the ABA-side network is the DECIDED pools beside the corrupted set,
and every round's instance is the view `toPair` of the flat state. Nothing is
guarded, so the composed state is determined by the flat one. -/
def ProtocolRel (P : Params) (s : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (s.1 j).1 = t.2.1 j) ∧
    s.2.2 = t.2.2.2 ∧
    t.2.2.1 = ⟨s.2.1.dpool, s.2.1.F⟩ ∧
    t.1 = fun r => toPair P s.1 s.2.1 r

theorem protocolRel_mk (P : Params) (u : ∀ _ : Fin P.n, ProcRec P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (G : ℕ → GBCA.LowPairState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : Comp.ANetState P.n)
    (o' : ℕ → WCC.SpecState P.n) :
    ProtocolRel P (u, w, o) (G, C, A, o') ↔
      ((∀ j, (u j).1 = C j) ∧ o = o' ∧ A = ⟨w.dpool, w.F⟩ ∧
        G = fun r => toPair P u w r) := Iff.rfl

/-- The initial states are related: every round of the view is the initial
instance state, an untouched round reading as the initial record on the flat
side and the empty pool slicing to the empty pool. -/
theorem protocolRel_init (P : Params) :
    ProtocolRel P (protocol P).init (composed P).init := by
  have hslice : ∀ {β : Type} (f : Msg P.n → Option β)
      (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'),
      slice f hf (fun _ => (∅ : Finset (Msg P.n))) = fun _ => (∅ : Finset β) := by
    intro β f hf
    funext q
    simp [slice]
  refine ⟨fun _ => rfl, rfl, rfl, ?_⟩
  funext r
  have hlow : (composed P).init.1 r = GBCA.LowPairState.initial P.n := rfl
  have hproc : (protocol P).init.1
      = fun _ => (CoreRec.initial P.n, StageSideRecP.initial (StageRec P.n)) := rfl
  have hpool : ((protocol P).init.2.1).pool
      = fun _ _ => (∅ : Finset (Msg P.n)) := rfl
  have hF : ((protocol P).init.2.1).F = (∅ : Finset (Fin P.n)) := rfl
  rw [hlow, toPair, toLow1, toLow2, hproc, hpool, hF]
  refine Prod.ext ?_ ?_ <;>
    simp [GBCA.LowPairState.initial, Gather.LowState.initial, SubState.initial,
      Fabric.initial, StageRec.initial, BRB.ImplState.initial, hslice]

/-! ### Building a transition of the composed reading

The composed reading's pipeline, read once so that every row of the
simulation can be assembled from its components' rows: the family of round
instances beside the round loops, the ABA-side network and the lifted
oracle. -/

/-- The four components of the gather-based composed reading, side by side. -/
noncomputable def composedPre (P : Params) :
    System (ComposedState P) (NLab P.n) :=
  (lowSide P).parallel
    ((System.syncProduct (Comp.coreProcN P)).parallel
      ((Comp.aNet P).parallel (wccLift P)))

/-- The composed group: the rendezvous alphabet hidden, read back over
`Lab n`. -/
noncomputable def composedGroup (P : Params) :
    System (ComposedState P) (Lab P.n) :=
  ((composedPre P).abstract (netEvtLabels P.n)).relabel

theorem composed_eq (P : Params) :
    composed P = (composedGroup P).abstract (Lab.hiddenAPI P.n) := rfl

/-- A row of the round instance, read over the extended alphabet. -/
theorem liftedLow_step (P : Params) (r : ℕ) {q q' : GBCA.LowPairState P.n}
    {L : NLab P.n} {l₀ : Lab P.n} (hpull : GSub.gPull P.n L = some l₀)
    (h : GBCA.LowPairStep P r q l₀ (PMF.pure q')) :
    (liftedLow P r).step q L (PMF.pure q') := by
  rw [liftedLow, System.mapIdle_step_some hpull]
  exact h

/-- The round-`r` instance moves on a label it owns. -/
theorem lowSide_owned (P : Params) (G : ℕ → GBCA.LowPairState P.n) (r : ℕ)
    {L : NLab P.n} (hL : GSub.gOwns L = some r) {X : GBCA.LowPairState P.n}
    (h : (liftedLow P r).step (G r) L (PMF.pure X)) :
    (lowSide P).step G L (PMF.pure (Function.update G r X)) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure X, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose instance stands still. -/
theorem lowSide_owned_id (P : Params) (G : ℕ → GBCA.LowPairState P.n) (r : ℕ)
    {L : NLab P.n} (hL : GSub.gOwns L = some r)
    (h : (liftedLow P r).step (G r) L (PMF.pure (G r))) :
    (lowSide P).step G L (PMF.pure G) := by
  have hstep := lowSide_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` instance takes one of its own silent rules. -/
theorem lowSide_tau (P : Params) (G : ℕ → GBCA.LowPairState P.n) (r : ℕ)
    {X : GBCA.LowPairState P.n}
    (h : (liftedLow P r).step (G r) (Sum.inl Lab.tau) (PMF.pure X)) :
    (lowSide P).step G (Sum.inl Lab.tau) (PMF.pure (Function.update G r X)) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure X, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem lowSide_idle (P : Params) (G : ℕ → GBCA.LowPairState P.n) {L : NLab P.n}
    (hτ : L ≠ Silent.τ) (hown : GSub.gOwns L = none) (hf : ¬ GSub.isFailN L) :
    (lowSide P).step G L (PMF.pure G) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's coordinates. -/
theorem lowSide_fail (P : Params) (G : ℕ → GBCA.LowPairState P.n) (k : Fin P.n) :
    (lowSide P).step G (Sum.inl (Lab.fail k))
      (PMF.pure (fun r => gActLow P (Sum.inl (Lab.fail k)) (G r))) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- Build a joint transition of the four components on a visible label, the
oracle's successor left arbitrary. -/
theorem composedPre_vis_step (P : Params) {G G' : ℕ → GBCA.LowPairState P.n}
    {C C' : ∀ _ : Fin P.n, CoreRec P.n} {A A' : Comp.ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n}
    (hL : L ≠ Silent.τ)
    (hG : (lowSide P).step G L (PMF.pure G'))
    (hC : ∀ i, Comp.CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : Comp.ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ω) :
    (composedPre P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω))) := by
  rw [composedPre, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ω),
    hG, ?_, rfl⟩
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ω,
    Comp.syncCore_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ω, hA, hW, rfl⟩

/-- Build a silent transition of the four components from a round-instance
one. -/
theorem composedPre_tau_low (P : Params) {G G' : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : Comp.ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (lowSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (PMF.pure (G', C, A, o)) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA-side network
injection. -/
theorem composedPre_tau_aNet (P : Params) {G : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A A' : Comp.ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hA : Comp.ANetStep P A (Sum.inl Lab.tau) (PMF.pure A')) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (PMF.pure (G, C, A', o)) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-- Build a silent transition of the four components from the coin
resolution. -/
theorem composedPre_tau_wcc (P : Params) {G : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : Comp.ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ω : PMF (ℕ → WCC.SpecState P.n)}
    (hW : (WCC.specFamily P).step o Lab.tau ω) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau)
      (prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ω))) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, _, ?_, rfl⟩)
  rw [System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A) ω, ?_, rfl⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, ω, (System.mapIdle_step_some (by simp) ω).mpr hW, rfl⟩)

/-! ### The two hiding frames -/

theorem composedGroup_step_iff (P : Params) (q : ComposedState P) (l : Lab P.n)
    (μ : PMF (ComposedState P)) :
    (composedGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (composedPre P).step q (Sum.inr e) μ) ∨
      (composedPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

theorem composedGroup_of_event (P : Params) {q : ComposedState P}
    (e : NetEvt P.n) {μ : PMF (ComposedState P)}
    (h : (composedPre P).step q (Sum.inr e) μ) :
    (composedGroup P).step q Lab.tau μ :=
  (composedGroup_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedGroup_of_tau (P : Params) {q : ComposedState P}
    {μ : PMF (ComposedState P)}
    (h : (composedPre P).step q (Sum.inl Lab.tau) μ) :
    (composedGroup P).step q Lab.tau μ :=
  (composedGroup_step_iff P _ _ _).mpr (Or.inr h)

/-! ### Transposing one written record

A row writes the acting process's round record, so the box vector the view
reads becomes a one-point update of the old one. Each lemma below is that
observation at one component, stated over the `ite` that reading a written
record produces. -/

section Boxes

variable {n : ℕ} {j : Fin n} (X : Fin n → StageRec n) (sr : StageRec n)

theorem boxes_ga1_if :
    (fun i => (if i = j then sr else X i).ga1)
      = Function.update (fun i => (X i).ga1) j sr.ga1 := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem boxes_ga2_if :
    (fun i => (if i = j then sr else X i).ga2)
      = Function.update (fun i => (X i).ga2) j sr.ga2 := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem boxes_brbIn1_if (k : Fin n) :
    (fun i => (if i = j then sr else X i).brbIn1 k)
      = Function.update (fun i => (X i).brbIn1 k) j (sr.brbIn1 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem boxes_brbBind1_if (k : Fin n) :
    (fun i => (if i = j then sr else X i).brbBind1 k)
      = Function.update (fun i => (X i).brbBind1 k) j (sr.brbBind1 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem boxes_brbIn2_if (k : Fin n) :
    (fun i => (if i = j then sr else X i).brbIn2 k)
      = Function.update (fun i => (X i).brbIn2 k) j (sr.brbIn2 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem boxes_brbBind2_if (k : Fin n) :
    (fun i => (if i = j then sr else X i).brbBind2 k)
      = Function.update (fun i => (X i).brbBind2 k) j (sr.brbBind2 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

end Boxes

/-! ### The view after one row

A row of the flat reading writes one component of the acting process's round
record and pools one tagged message. The lemma below is that write read
through the view, and it is the shape every row of the simulation is
discharged by: the round the row names moves as the composed reading's own row
moves it. -/

section Frame

variable {u : ∀ _ : Fin P.n, ProcRec P.n} {w : NetState P.n} {j : Fin P.n}
    {c : CoreRec P.n} {p : StageSideRec P.n}

/-- The view after a write, with the one-point update pushed inside every
coordinate: the acting process's box replaced in each box vector, and each
fabric sliced out of the written pool. -/
def toPairUpd (P : Params) (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (j : Fin P.n) (sr : StageRec P.n)
    (pool : Fin P.n → Finset (Msg P.n)) : GBCA.LowPairState P.n :=
  ({ ga := (Function.update (fun i => ((u i).2.stage r).ga1) j sr.ga1,
            ⟨slice unGa1 unGa1_inj pool, w.F⟩)
     brbIn := fun k =>
       (Function.update (fun i => ((u i).2.stage r).brbIn1 k) j (sr.brbIn1 k),
        ⟨slice (unIn1 k) (unIn1_inj k) pool, w.F⟩)
     brbBind := fun k =>
       (Function.update (fun i => ((u i).2.stage r).brbBind1 k) j (sr.brbBind1 k),
        ⟨slice (unBind1 k) (unBind1_inj k) pool, w.F⟩) },
   { ga := (Function.update (fun i => ((u i).2.stage r).ga2) j sr.ga2,
            ⟨slice unGa2 unGa2_inj pool, w.F⟩)
     brbIn := fun k =>
       (Function.update (fun i => ((u i).2.stage r).brbIn2 k) j (sr.brbIn2 k),
        ⟨slice (unIn2 k) (unIn2_inj k) pool, w.F⟩)
     brbBind := fun k =>
       (Function.update (fun i => ((u i).2.stage r).brbBind2 k) j (sr.brbBind2 k),
        ⟨slice (unBind2 k) (unBind2_inj k) pool, w.F⟩) })

/-- **A write, read through the view.** A row writes the acting process's
round record and pools one tagged message; the round it names then reads as
the one-point update of every coordinate. This is the transposition, done
once, so that the six slice computations each row still owes are pool algebra
alone. -/
theorem toPair_write (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) (m : Msg P.n) :
    toPair P (Function.update u j (c, (u j).2.setStage r sr)) (w.gpool r j m) r
      = toPairUpd P u w r j sr
          (Function.update (w.pool r) j (insert m (w.pool r j))) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow1, stage_update_self rfl, boxes_ga1_if]
    · simp only [toPair, toPairUpd, toLow1, gpool_pool_self]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow1, stage_update_self rfl, boxes_brbIn1_if]
    · simp only [toPair, toPairUpd, toLow1, gpool_pool_self]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow1, stage_update_self rfl, boxes_brbBind1_if]
    · simp only [toPair, toPairUpd, toLow1, gpool_pool_self]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow2, stage_update_self rfl, boxes_ga2_if]
    · simp only [toPair, toPairUpd, toLow2, gpool_pool_self]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow2, stage_update_self rfl, boxes_brbIn2_if]
    · simp only [toPair, toPairUpd, toLow2, gpool_pool_self]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow2, stage_update_self rfl, boxes_brbBind2_if]
    · simp only [toPair, toPairUpd, toLow2, gpool_pool_self]

/-- A write that pools nothing — a delivery, or a return — read through the
view. -/
theorem toPair_writeNoPool (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) :
    toPair P (Function.update u j (c, (u j).2.setStage r sr)) w r
      = toPairUpd P u w r j sr (w.pool r) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow1, stage_update_self rfl, boxes_ga1_if]
    · simp only [toPair, toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow1, stage_update_self rfl, boxes_brbIn1_if]
    · simp only [toPair, toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow1, stage_update_self rfl, boxes_brbBind1_if]
    · simp only [toPair, toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow2, stage_update_self rfl, boxes_ga2_if]
    · simp only [toPair, toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow2, stage_update_self rfl, boxes_brbIn2_if]
    · simp only [toPair, toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPair, toPairUpd, toLow2, stage_update_self rfl, boxes_brbBind2_if]
    · simp only [toPair, toPairUpd, toLow2]

/-- A send of the first gather, read through the view: the sender's box takes
the send, the first gather's fabric pools it, and every other coordinate of
the round stands still. Both ladder sends of the first gather are this row,
and so is any other row that writes the first gather's box and pools on its
fabric. -/
theorem toPair_ga1Send (hu : (u j).2 = p) (r : ℕ) (pr : PRec P.n Bool)
    (m : GaMsg P.n Bool) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with ga1 := (p.stage r).ga1.setP pr }))
      (w.gpool r j (.ga1 m)) r
      = ({ toLow1 P u w r with
            ga := ((toLow1 P u w r).ga.setProc j pr).mcast j m },
         toLow2 P u w r) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1, SubState.mcast, SubState.setProc]
    · simp only [toPairUpd, toLow1, SubState.mcast, Fabric.post]
      exact slice_post_some unGa1 unGa1_inj (w.pool r) j (.ga1 m) m rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j (.ga1 m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j (.ga1 m) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.ga1 m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j (.ga1 m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j (.ga1 m) rfl

/-- A send in an input-broadcast instance of the first gather, read through
the view: the sender's box in that instance takes the send, that instance's
fabric pools it, and every other coordinate stands still. The three Bracha
rows of the family are this row, and so is the graded-agreement call's
broadcast half. -/
theorem toPair_in1Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState Bool) (m : BRB.BMsg Bool) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn1 := Function.update (p.stage r).brbIn1 i
            (((p.stage r).brbIn1 i).setP pr) }))
      (w.gpool r j (.brbIn1 i m)) r
      = ({ toLow1 P u w r with
            brbIn := Function.update (toLow1 P u w r).brbIn i
              ((((toLow1 P u w r).brbIn i).setProc j pr).mcast j m) },
         toLow2 P u w r) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.brbIn1 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast,
          SubState.setProc]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast,
          Fabric.post]
        exact slice_post_some (unIn1 k) (unIn1_inj k) (w.pool r) j
          (.brbIn1 k m) m (by simp [unIn1])
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast,
          SubState.setProc, Fabric.post]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j (.brbIn1 i m)
          (by simp [unIn1, Ne.symm hk])
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j (.brbIn1 i m) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.brbIn1 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j (.brbIn1 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j (.brbIn1 i m) rfl

/-- A send of the second gather, read through the view. -/
theorem toPair_ga2Send (hu : (u j).2 = p) (r : ℕ) (pr : PRec P.n (Option Bool))
    (m : GaMsg P.n (Option Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with ga2 := (p.stage r).ga2.setP pr }))
      (w.gpool r j (.ga2 m)) r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            ga := ((toLow2 P u w r).ga.setProc j pr).mcast j m }) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.ga2 m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j (.ga2 m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j (.ga2 m) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2, SubState.mcast, SubState.setProc]
    · simp only [toPairUpd, toLow2, SubState.mcast, Fabric.post]
      exact slice_post_some unGa2 unGa2_inj (w.pool r) j (.ga2 m) m rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j (.ga2 m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j (.ga2 m) rfl

/-- A send in a bind-broadcast instance of the first gather, read through the view. -/
theorem toPair_bind1Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState (APSet P.n Bool)) (m : BRB.BMsg (APSet P.n Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind1 := Function.update (p.stage r).brbBind1 i
            (((p.stage r).brbBind1 i).setP pr) }))
      (w.gpool r j (.brbBind1 i m)) r
      = ({ toLow1 P u w r with
            brbBind := Function.update (toLow1 P u w r).brbBind i
              ((((toLow1 P u w r).brbBind i).setProc j pr).mcast j m) },
         toLow2 P u w r) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.brbBind1 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j (.brbBind1 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast, SubState.setProc]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast, Fabric.post]
        exact slice_post_some (unBind1 k) (unBind1_inj k) (w.pool r) j
          (.brbBind1 k m) m (by simp [unBind1])
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast, SubState.setProc,
        Fabric.post]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j (.brbBind1 i m)
          (by simp [unBind1, Ne.symm hk])
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.brbBind1 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j (.brbBind1 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j (.brbBind1 i m) rfl

/-- A send in an input-broadcast instance of the second gather, read through the view. -/
theorem toPair_in2Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState (Option Bool)) (m : BRB.BMsg (Option Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn2 := Function.update (p.stage r).brbIn2 i
            (((p.stage r).brbIn2 i).setP pr) }))
      (w.gpool r j (.brbIn2 i m)) r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            brbIn := Function.update (toLow2 P u w r).brbIn i
              ((((toLow2 P u w r).brbIn i).setProc j pr).mcast j m) }) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.brbIn2 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j (.brbIn2 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j (.brbIn2 i m) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.brbIn2 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast, SubState.setProc]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast, Fabric.post]
        exact slice_post_some (unIn2 k) (unIn2_inj k) (w.pool r) j
          (.brbIn2 k m) m (by simp [unIn2])
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast, SubState.setProc,
        Fabric.post]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j (.brbIn2 i m)
          (by simp [unIn2, Ne.symm hk])
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j (.brbIn2 i m) rfl

/-- A send in a bind-broadcast instance of the second gather, read through the view. -/
theorem toPair_bind2Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState (APSet P.n (Option Bool))) (m : BRB.BMsg (APSet P.n (Option Bool))) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind2 := Function.update (p.stage r).brbBind2 i
            (((p.stage r).brbBind2 i).setP pr) }))
      (w.gpool r j (.brbBind2 i m)) r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            brbBind := Function.update (toLow2 P u w r).brbBind i
              ((((toLow2 P u w r).brbBind i).setProc j pr).mcast j m) }) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.brbBind2 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j (.brbBind2 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j (.brbBind2 i m) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.brbBind2 i m) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j (.brbBind2 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast, SubState.setProc]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast, Fabric.post]
        exact slice_post_some (unBind2 k) (unBind2_inj k) (w.pool r) j
          (.brbBind2 k m) m (by simp [unBind2])
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast, SubState.setProc,
        Fabric.post]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j (.brbBind2 i m)
          (by simp [unBind2, Ne.symm hk])
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]

/-- A delivery on the first gather's fabric, read through the view. -/
theorem toPair_dlvGa1 (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n) (mm : GaMsg P.n Bool) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with ga1 := (p.stage r).ga1.deliverTo k mm })) w r
      = ({ toLow1 P u w r with ga := (toLow1 P u w r).ga.recvMsg j k mm },
         toLow2 P u w r) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1, SubState.recvMsg]
    · simp only [toPairUpd, toLow1, SubState.recvMsg]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]

/-- A delivery on the second gather's fabric, read through the view. -/
theorem toPair_dlvGa2 (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n) (mm : GaMsg P.n (Option Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with ga2 := (p.stage r).ga2.deliverTo k mm })) w r
      = (toLow1 P u w r,
         { toLow2 P u w r with ga := (toLow2 P u w r).ga.recvMsg j k mm }) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2, SubState.recvMsg]
    · simp only [toPairUpd, toLow2, SubState.recvMsg]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]

/-- A delivery in an input-broadcast instance of the first gather, read through the view. -/
theorem toPair_dlvIn1 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n) (mm : BRB.BMsg Bool) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn1 := Function.update (p.stage r).brbIn1 i
            (((p.stage r).brbIn1 i).deliverTo k mm) })) w r
      = ({ toLow1 P u w r with
            brbIn := Function.update (toLow1 P u w r).brbIn i
              (((toLow1 P u w r).brbIn i).recvMsg j k mm) },
         toLow2 P u w r) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.recvMsg]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]

/-- A delivery in a bind-broadcast instance of the first gather, read through the view. -/
theorem toPair_dlvBind1 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (APSet P.n Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind1 := Function.update (p.stage r).brbBind1 i
            (((p.stage r).brbBind1 i).deliverTo k mm) })) w r
      = ({ toLow1 P u w r with
            brbBind := Function.update (toLow1 P u w r).brbBind i
              (((toLow1 P u w r).brbBind i).recvMsg j k mm) },
         toLow2 P u w r) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.recvMsg]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]

/-- A delivery in an input-broadcast instance of the second gather, read through the view. -/
theorem toPair_dlvIn2 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n) (mm : BRB.BMsg (Option Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn2 := Function.update (p.stage r).brbIn2 i
            (((p.stage r).brbIn2 i).deliverTo k mm) })) w r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            brbIn := Function.update (toLow2 P u w r).brbIn i
              (((toLow2 P u w r).brbIn i).recvMsg j k mm) }) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.recvMsg]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]

/-- A delivery in a bind-broadcast instance of the second gather, read through the view. -/
theorem toPair_dlvBind2 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (APSet P.n (Option Bool))) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind2 := Function.update (p.stage r).brbBind2 i
            (((p.stage r).brbBind2 i).deliverTo k mm) })) w r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            brbBind := Function.update (toLow2 P u w r).brbBind i
              (((toLow2 P u w r).brbBind i).recvMsg j k mm) }) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.recvMsg]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.recvMsg]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]


/-- The second gather's return, read through the view: the returner's box
takes the flag and nothing is pooled. -/
theorem toPair_retG (hu : (u j).2 = p) (r : ℕ) (pr : PRec P.n (Option Bool)) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with ga2 := (p.stage r).ga2.setP pr })) w r
      = (toLow1 P u w r,
         { toLow2 P u w r with ga := (toLow2 P u w r).ga.setProc j pr }) := by
  rw [← hu, toPair_writeNoPool]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2, SubState.setProc]
    · simp only [toPairUpd, toLow2, SubState.setProc]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]

/-- The graded-agreement call, read through the view: the first gather records
the input and the caller's own input-broadcast instance takes it and pools its
`⟨INIT, b⟩`. -/
theorem toPair_callG (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga1 := (p.stage r).ga1.setP
            { ((p.stage r).ga1.proc) with input := some b }
          brbIn1 := Function.update (p.stage r).brbIn1 j
            (((p.stage r).brbIn1 j).setP
              { (((p.stage r).brbIn1 j).proc) with input := some b }) }))
      (w.gpool r j (.brbIn1 j (.init b))) r
      = ({ toLow1 P u w r with
            ga := (toLow1 P u w r).ga.setProc j
              { ((toLow1 P u w r).ga.proc j) with input := some b }
            brbIn := Function.update (toLow1 P u w r).brbIn j
              ((((toLow1 P u w r).brbIn j).setProc j
                { (((toLow1 P u w r).brbIn j).proc j) with input := some b }).mcast
                  j (.init b)) },
         toLow2 P u w r) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1, SubState.setProc, SubState.proc]
    · simp only [toPairUpd, toLow1]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.brbIn1 j (.init b)) rfl
  · funext k
    by_cases hk : k = j
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast,
          SubState.setProc, SubState.proc]
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast,
          Fabric.post]
        exact slice_post_some (unIn1 k) (unIn1_inj k) (w.pool r) k
          (.brbIn1 k (.init b)) (.init b) (by simp [unIn1])
      · simp only [toPairUpd, toLow1, Function.update_self, SubState.mcast,
          SubState.setProc, Fabric.post]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
        exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j
          (.brbIn1 j (.init b)) (by simp [unIn1, Ne.symm hk])
      · simp only [toPairUpd, toLow1, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j
        (.brbIn1 j (.init b)) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.brbIn1 j (.init b)) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j
        (.brbIn1 j (.init b)) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j
        (.brbIn1 j (.init b)) rfl

/-- The link, read through the view: the first gather records the return, the
second records the candidate, and the caller's own input-broadcast instance of
the second gather takes it and pools its `⟨INIT, ·⟩` (D28). -/
theorem toPair_link (hu : (u j).2 = p) (r : ℕ) (pr1 : PRec P.n Bool)
    (pr2 : PRec P.n (Option Bool)) (prb : BRB.PState (Option Bool))
    (x : Option Bool) :
    toPair P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga1 := (p.stage r).ga1.setP pr1
          ga2 := (p.stage r).ga2.setP pr2
          brbIn2 := Function.update (p.stage r).brbIn2 j
            (((p.stage r).brbIn2 j).setP prb) }))
      (w.gpool r j (.brbIn2 j (.init x))) r
      = ({ toLow1 P u w r with ga := (toLow1 P u w r).ga.setProc j pr1 },
         { toLow2 P u w r with
            ga := (toLow2 P u w r).ga.setProc j pr2
            brbIn := Function.update (toLow2 P u w r).brbIn j
              ((((toLow2 P u w r).brbIn j).setProc j prb).mcast j (.init x)) }) := by
  rw [← hu, toPair_write]
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1, SubState.setProc]
    · simp only [toPairUpd, toLow1, SubState.setProc]
      exact slice_post_none unGa1 unGa1_inj (w.pool r) j (.brbIn2 j (.init x)) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.pool r) j
        (.brbIn2 j (.init x)) rfl
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow1]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.pool r) j
        (.brbIn2 j (.init x)) rfl
  · refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2, SubState.setProc]
    · simp only [toPairUpd, toLow2, SubState.setProc]
      exact slice_post_none unGa2 unGa2_inj (w.pool r) j (.brbIn2 j (.init x)) rfl
  · funext k
    by_cases hk : k = j
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast,
          SubState.setProc]
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast,
          Fabric.post]
        exact slice_post_some (unIn2 k) (unIn2_inj k) (w.pool r) k
          (.brbIn2 k (.init x)) (.init x) (by simp [unIn2])
      · simp only [toPairUpd, toLow2, Function.update_self, SubState.mcast,
          SubState.setProc, Fabric.post]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
        exact slice_post_none (unIn2 k) (unIn2_inj k) (w.pool r) j
          (.brbIn2 j (.init x)) (by simp [unIn2, Ne.symm hk])
      · simp only [toPairUpd, toLow2, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (fabric_ext ?_ rfl)
    · simp only [toPairUpd, toLow2]
      exact Function.update_eq_self _ _
    · simp only [toPairUpd, toLow2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.pool r) j
        (.brbIn2 j (.init x)) rfl

/-! ### Every other round stands still

A row names one round. The rounds it does not name read exactly as they did:
the process's other round records are untouched, and the adversary's pool
family is written at one round only. -/

theorem toPair_other (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : StageRec P.n) (m : Msg P.n) :
    toPair P (Function.update u j (c, p.setStage r sr)) (w.gpool r j m) r'
      = toPair P u w r' := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_) <;>
    first
      | (refine Prod.ext ?_ (fabric_ext ?_ rfl)
         · simp only [toPair, toLow1, toLow2, stage_update_ne hu hr]
         · simp only [toPair, toLow1, toLow2, gpool_pool_ne _ _ _ _ hr])
      | (funext k
         refine Prod.ext ?_ (fabric_ext ?_ rfl)
         · simp only [toPair, toLow1, toLow2, stage_update_ne hu hr]
         · simp only [toPair, toLow1, toLow2, gpool_pool_ne _ _ _ _ hr])

theorem toPair_otherNoPool (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : StageRec P.n) :
    toPair P (Function.update u j (c, p.setStage r sr)) w r' = toPair P u w r' := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_) <;>
    first
      | (refine Prod.ext ?_ (fabric_ext rfl rfl)
         simp only [toPair, toLow1, toLow2, stage_update_ne hu hr])
      | (funext k
         refine Prod.ext ?_ (fabric_ext rfl rfl)
         simp only [toPair, toLow1, toLow2, stage_update_ne hu hr])

/-- The whole family of rounds after a row: the round it names moves, the rest
stand still. -/
theorem toPairFam (hu : (u j).2 = p) (r : ℕ) (sr : StageRec P.n) (m : Msg P.n)
    (X : GBCA.LowPairState P.n)
    (hX : toPair P (Function.update u j (c, p.setStage r sr)) (w.gpool r j m) r = X) :
    (fun r' => toPair P (Function.update u j (c, p.setStage r sr))
        (w.gpool r j m) r')
      = Function.update (fun r' => toPair P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, toPair_other hu hr]

/-- The same, for a row that pools nothing. -/
theorem toPairFamNoPool (hu : (u j).2 = p) (r : ℕ) (sr : StageRec P.n)
    (X : GBCA.LowPairState P.n)
    (hX : toPair P (Function.update u j (c, p.setStage r sr)) w r = X) :
    (fun r' => toPair P (Function.update u j (c, p.setStage r sr)) w r')
      = Function.update (fun r' => toPair P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, toPair_otherNoPool hu hr]

end Frame

/-! ### The coupling

The relation is a function, so a Dirac outcome of the flat reading is matched
by the single composed state it is read as, and an outcome whose only free
coordinate is the oracle's is matched outcome by outcome. -/

/-- A Dirac outcome matched by the single composed state it is read as. -/
private theorem match_pure (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRel P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (PMF.pure s) Ω ∧ Ω.bind id = PMF.pure t := by
  refine ⟨PMF.pure (PMF.pure t), ⟨PMF.pure (s, PMF.pure t), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro q hq
    rw [PMF.mem_support_pure_iff] at hq
    subst hq
    exact ⟨t, rfl, h⟩
  · rw [PMF.pure_bind]
    rfl

/-- An outcome whose only free coordinate is the oracle's, matched outcome by
outcome. -/
private theorem match_prod (P : Params) {x : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {G : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : Comp.ANetState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)}
    (h : ∀ o ∈ ν.support, ProtocolRel P (x, w, o) (G, C, A, o)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) ν)) Ω ∧
      Ω.bind id =
        prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ν)) := by
  refine ⟨ν.map (fun o => PMF.pure ((G, C, A, o) : ComposedState P)),
    ⟨ν.map (fun o => (((x, w, o) : ProtocolState P),
      PMF.pure ((G, C, A, o) : ComposedState P))), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.map_comp, prodPMF_pure₂]
    rfl
  · rw [PMF.map_comp]
    rfl
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    exact ⟨(G, C, A, o), rfl, h o ho⟩
  · rw [PMF.bind_map, prodPMF_pure₃]
    rfl



/-! ### Rows the view does not see

A row that writes only the round loop leaves every round record where it
stands, so the view does not move. Corruption moves it in one respect only:
the corrupted set the adversary holds is the corrupted set of every fabric,
and the two guards are the same. -/

theorem toPair_congr {x u : ∀ _ : Fin P.n, ProcRec P.n} {r : ℕ}
    (h : ∀ i, (x i).2.stage r = (u i).2.stage r) (w : NetState P.n) :
    toPair P x w r = toPair P u w r := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun q => q.ga1) (h i)
  · funext k
    refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun q => q.brbIn1 k) (h i)
  · funext k
    refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun q => q.brbBind1 k) (h i)
  · refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun q => q.ga2) (h i)
  · funext k
    refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun q => q.brbIn2 k) (h i)
  · funext k
    refine Prod.ext ?_ rfl
    funext i
    exact congrArg (fun q => q.brbBind2 k) (h i)

theorem toPair_fail (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) :
    toPair P u (NetStateP.corrupt P k w) r
      = gActLow P (Sum.inl (Lab.fail k)) (toPair P u w r) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl ?_
    simp only [toPair, toLow1, gActLow, Gather.LowState.corruptAll,
      SubState.corrupt, NetStateP.corrupt, Fabric.corrupt]
    split_ifs <;> rfl
  · funext k
    refine Prod.ext rfl ?_
    simp only [toPair, toLow1, gActLow, Gather.LowState.corruptAll,
      SubState.corrupt, NetStateP.corrupt, Fabric.corrupt]
    split_ifs <;> rfl
  · funext k
    refine Prod.ext rfl ?_
    simp only [toPair, toLow1, gActLow, Gather.LowState.corruptAll,
      SubState.corrupt, NetStateP.corrupt, Fabric.corrupt]
    split_ifs <;> rfl
  · refine Prod.ext rfl ?_
    simp only [toPair, toLow2, gActLow, Gather.LowState.corruptAll,
      SubState.corrupt, NetStateP.corrupt, Fabric.corrupt]
    split_ifs <;> rfl
  · funext k
    refine Prod.ext rfl ?_
    simp only [toPair, toLow2, gActLow, Gather.LowState.corruptAll,
      SubState.corrupt, NetStateP.corrupt, Fabric.corrupt]
    split_ifs <;> rfl
  · funext k
    refine Prod.ext rfl ?_
    simp only [toPair, toLow2, gActLow, Gather.LowState.corruptAll,
      SubState.corrupt, NetStateP.corrupt, Fabric.corrupt]
    split_ifs <;> rfl

/-- A pool write at one round leaves every other round's view alone. -/
theorem toPair_otherPool (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    {r r' : ℕ} (hr : r' ≠ r) (k : Fin P.n) (m : Msg P.n) :
    toPair P u (w.gpool r k m) r' = toPair P u w r' := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_ne _ _ _ _ hr]
  · funext k'
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_ne _ _ _ _ hr]
  · funext k'
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_ne _ _ _ _ hr]
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_ne _ _ _ _ hr]
  · funext k'
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_ne _ _ _ _ hr]
  · funext k'
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_ne _ _ _ _ hr]

/-- The family of rounds after a Byzantine injection at one round. -/
theorem toPairFamPool (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (m : Msg P.n) (X : GBCA.LowPairState P.n)
    (hX : toPair P u (w.gpool r k m) r = X) :
    (fun r' => toPair P u (w.gpool r k m) r')
      = Function.update (fun r' => toPair P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, toPair_otherPool u w hr]

/-! ### Assembling a matched transition -/

/-- A visible label: the four components move together, the oracle's successor
free. -/
private theorem match_vis (P : Params) {x : ∀ _ : Fin P.n, ProcRec P.n}
    {w' : NetState P.n} {G' : ℕ → GBCA.LowPairState P.n}
    {C' : ∀ _ : Fin P.n, CoreRec P.n} {A' : Comp.ANetState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {G : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : Comp.ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {L : NLab P.n} (hL : L ≠ Silent.τ)
    (hrel : ∀ o' ∈ ν.support, ProtocolRel P (x, w', o') (G', C', A', o'))
    (hG : (lowSide P).step G L (PMF.pure G'))
    (hC : ∀ i, Comp.CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : Comp.ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ν) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      (composedPre P).step (G, C, A, o) L (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := match_prod P hrel
  exact ⟨Ω, hr, hb ▸ composedPre_vis_step P hL hG hC hA hW⟩

/-- A rendezvous of the flat reading: the round instance takes one of its own
silent rules and nothing else moves. -/
private theorem match_round (P : Params) {x : ∀ _ : Fin P.n, ProcRec P.n}
    {w' : NetState P.n} {G' G : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : Comp.ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hrel : ProtocolRel P (x, w', o) (G', C, A, o))
    (hG : (lowSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (PMF.pure ((x, w', o) : ProtocolState P)) Ω ∧
      (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau) (Ω.bind id) := by
  obtain ⟨Ω, hr, hb⟩ := match_pure P hrel
  exact ⟨Ω, hr, hb ▸ composedPre_tau_low P hG⟩



/-! ### Reading a row off a label the process owns

A program's row on a label of `stageOwn j` is a row of the implementation:
every other row of the flat reading either carries a label of another class,
or carries one of these at another process, or is the replaced program's
self-loop, which has no row on a label the process acts on. -/

theorem stageRow_of_own {j : Fin P.n} {q : ProcRec P.n} {L : NLabP P.n (Msg P.n)}
    {y : ProcRec P.n} (hown : stageOwn j L)
    (h : ProcStep P j q L (PMF.pure y)) : StageStep P j q L (PMF.pure y) := by
  generalize hμ : (PMF.pure y : PMF (ProcRec P.n)) = ν at h
  cases h
  case stageRow h' => exact hμ ▸ h'
  case corruptedIdle hh hτ hown' => exact absurd (actsAt_of_stageOwn hown) hown'
  all_goals first
    | exact hown.elim
    | (rename_i hid; exact absurd hown hid)

/-! ### Answering a send

A send of the flat reading is a silent row of the round instance: the sender
writes its own record, the network pools the message, and the round the label
tags moves as one of the instance's own rules moves it. -/

theorem stage_answer_gsnd (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) {r : ℕ} {m : Msg P.n} {μ : PMF (ProcRec P.n)}
    (h : StageStep P j (c, p) (Sum.inr (.gsnd r j m)) μ) :
    ∃ x : ProcRec P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      GBCA.LowPairStep P r (toPair P u w r) Lab.tau
        (PMF.pure (toPair P (Function.update u j x) (w.gpool r j m) r)) := by
  subst hu
  cases h with
  | ga1Echo _ _ _ A hh hterm hin happ hcard hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_ga1Send rfl]
    exact GBCA.LowPairStep.ga1Tau
      (toPair P u w r) _ (Gather.LowStep.echo (toPair P u w r).1 j A hin happ hcard hsend)
  | ga1Vote _ _ _ U hh hterm hin happ hQ hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_ga1Send rfl]
    exact GBCA.LowPairStep.ga1Tau
      (toPair P u w r) _ (Gather.LowStep.vote (toPair P u w r).1 j U hin happ hQ hsend)
  | ga1Bind _ _ _ U hh hterm hin hbc happ hQ =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind1Send rfl]
    exact GBCA.LowPairStep.ga1Tau
      (toPair P u w r) _ (Gather.LowStep.bindCall (toPair P u w r).1 j U hin hbc happ hQ)
  | ga2Echo _ _ _ A hh hterm hin happ hcard hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_ga2Send rfl]
    exact GBCA.LowPairStep.ga2Tau
      (toPair P u w r) _ (Gather.LowStep.echo (toPair P u w r).2 j A hin happ hcard hsend)
  | ga2Vote _ _ _ U hh hterm hin happ hQ hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_ga2Send rfl]
    exact GBCA.LowPairStep.ga2Tau
      (toPair P u w r) _ (Gather.LowStep.vote (toPair P u w r).2 j U hin happ hQ hsend)
  | ga2Bind _ _ _ U hh hterm hin hbc happ hQ =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind2Send rfl]
    exact GBCA.LowPairStep.ga2Tau
      (toPair P u w r) _ (Gather.LowStep.bindCall (toPair P u w r).2 j U hin hbc happ hQ)
  | link _ _ _ g hh hterm hin hsubap hQ hr1 hin2 hbin2 =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_link rfl]
    exact GBCA.LowPairStep.link (toPair P u w r) j g _
      (Gather.LowStep.ret (toPair P u w r).1 j g hin hsubap hQ hr1) hin2 hbin2
  | in1Echo _ _ _ i mm hh hterm hrecv hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_in1Send rfl]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).1 i _
        (BRB.ImplStep.echo ((toPair P u w r).1.brbIn i) j mm hrecv hsend))
  | in1VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_in1Send rfl]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).1 i _
        (BRB.ImplStep.voteQuorum ((toPair P u w r).1.brbIn i) j mm hcnt hsend))
  | in1VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_in1Send rfl]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).1 i _
        (BRB.ImplStep.voteAmp ((toPair P u w r).1.brbIn i) j mm hcnt hsend))
  | bind1Echo _ _ _ i mm hh hterm hrecv hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind1Send rfl]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).1 i _
        (BRB.ImplStep.echo ((toPair P u w r).1.brbBind i) j mm hrecv hsend))
  | bind1VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind1Send rfl]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).1 i _
        (BRB.ImplStep.voteQuorum ((toPair P u w r).1.brbBind i) j mm hcnt hsend))
  | bind1VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind1Send rfl]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).1 i _
        (BRB.ImplStep.voteAmp ((toPair P u w r).1.brbBind i) j mm hcnt hsend))
  | in2Echo _ _ _ i mm hh hterm hrecv hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_in2Send rfl]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).2 i _
        (BRB.ImplStep.echo ((toPair P u w r).2.brbIn i) j mm hrecv hsend))
  | in2VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_in2Send rfl]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).2 i _
        (BRB.ImplStep.voteQuorum ((toPair P u w r).2.brbIn i) j mm hcnt hsend))
  | in2VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_in2Send rfl]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).2 i _
        (BRB.ImplStep.voteAmp ((toPair P u w r).2.brbIn i) j mm hcnt hsend))
  | bind2Echo _ _ _ i mm hh hterm hrecv hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind2Send rfl]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).2 i _
        (BRB.ImplStep.echo ((toPair P u w r).2.brbBind i) j mm hrecv hsend))
  | bind2VoteQuorum _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind2Send rfl]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).2 i _
        (BRB.ImplStep.voteQuorum ((toPair P u w r).2.brbBind i) j mm hcnt hsend))
  | bind2VoteAmp _ _ _ i mm hh hterm hcnt hsend =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_bind2Send rfl]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).2 i _
        (BRB.ImplStep.voteAmp ((toPair P u w r).2.brbBind i) j mm hcnt hsend))


/-! ### Answering a delivery, a call, a return and a call loop -/

/-- A delivery of the flat reading is a silent row of the round instance: the
message the adversary holds under its sender is filed in the receiver's own
box of the fabric its tag names. -/
theorem stage_answer_gdlv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) {r : ℕ} {k : Fin P.n} {m : Msg P.n}
    {μ : PMF (ProcRec P.n)} (hpool : m ∈ w.pool r k)
    (h : StageStep P j (c, p) (Sum.inr (.gdlv r j k m)) μ) :
    ∃ x : ProcRec P.n, μ = PMF.pure x ∧ x.1 = c ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      GBCA.LowPairStep P r (toPair P u w r) Lab.tau
        (PMF.pure (toPair P (Function.update u j x) w r)) := by
  subst hu
  cases h with
  | gdlvRecv _ _ _ _ _ hh hterm =>
    refine ⟨_, rfl, rfl, fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
    cases m with
    | ga1 mm =>
      rw [toPair_dlvGa1 rfl]
      exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
        (Gather.LowStep.deliver (toPair P u w r).1 j k mm
          ((mem_slice (hf := unGa1_inj)).mpr ⟨_, hpool, rfl⟩))
    | ga2 mm =>
      rw [toPair_dlvGa2 rfl]
      exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
        (Gather.LowStep.deliver (toPair P u w r).2 j k mm
          ((mem_slice (hf := unGa2_inj)).mpr ⟨_, hpool, rfl⟩))
    | brbIn1 i mm =>
      rw [toPair_dlvIn1 rfl]
      exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
        (Gather.LowStep.brbInTau (toPair P u w r).1 i _
          (BRB.ImplStep.deliver ((toPair P u w r).1.brbIn i) j k mm
            ((mem_slice (hf := unIn1_inj i)).mpr ⟨_, hpool, by simp [unIn1]⟩)))
    | brbBind1 i mm =>
      rw [toPair_dlvBind1 rfl]
      exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
        (Gather.LowStep.brbBindTau (toPair P u w r).1 i _
          (BRB.ImplStep.deliver ((toPair P u w r).1.brbBind i) j k mm
            ((mem_slice (hf := unBind1_inj i)).mpr ⟨_, hpool, by simp [unBind1]⟩)))
    | brbIn2 i mm =>
      rw [toPair_dlvIn2 rfl]
      exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
        (Gather.LowStep.brbInTau (toPair P u w r).2 i _
          (BRB.ImplStep.deliver ((toPair P u w r).2.brbIn i) j k mm
            ((mem_slice (hf := unIn2_inj i)).mpr ⟨_, hpool, by simp [unIn2]⟩)))
    | brbBind2 i mm =>
      rw [toPair_dlvBind2 rfl]
      exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
        (Gather.LowStep.brbBindTau (toPair P u w r).2 i _
          (BRB.ImplStep.deliver ((toPair P u w r).2.brbBind i) j k mm
            ((mem_slice (hf := unBind2_inj i)).mpr ⟨_, hpool, by simp [unBind2]⟩)))

/-- The graded-agreement call of the flat reading is the round instance's own
call. -/
theorem stage_answer_callG (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) {r : ℕ} {b : Bool} {μ : PMF (ProcRec P.n)}
    (h : StageStep P j (c, p) (Sum.inl (.callG r j b)) μ) :
    ∃ x : ProcRec P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.proc.phase = .toCallG ∧ c.proc.round = r ∧
      c.proc.est = some b ∧
      x.1 = c.setProc { c.proc with phase := .awaitG } ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      GBCA.LowPairStep P r (toPair P u w r) (.callG r j b)
        (PMF.pure (toPair P (Function.update u j x)
          (w.gpool r j (gCallPayload P j b)) r)) := by
  subst hu
  cases h with
  | callG _ _ _ _ hh hph hr hterm hest hin hbin =>
    refine ⟨_, rfl, hh, hph, hr, hest, rfl,
      fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [gCallPayload, toPair_callG rfl]
    exact GBCA.LowPairStep.callG (toPair P u w r) j b _
      (Gather.LowStep.call (toPair P u w r).1 j b hin hbin)

/-- The graded-agreement return of the flat reading is the round instance's
own return, the grade read off the second gather's output. -/
theorem stage_answer_retG (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) {r : ℕ} {out : GbcaOut} {μ : PMF (ProcRec P.n)}
    (h : StageStep P j (c, p) (Sum.inl (.retG r j out)) μ) :
    ∃ x : ProcRec P.n, μ = PMF.pure x ∧
      c.corrupted = false ∧ c.proc.phase = .awaitG ∧ c.proc.round = r ∧
      x.1 = c.setProc { c.proc with
        est := out.est, lastGrade := some out, phase := .toCallW } ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      GBCA.LowPairStep P r (toPair P u w r) (.retG r j out)
        (PMF.pure (toPair P (Function.update u j x) w r)) := by
  subst hu
  cases h with
  | retG _ _ _ g hh hph hr hterm hin hsubap hQ hr2 =>
    refine ⟨_, rfl, hh, hph, hr, rfl,
      fun r' hr' => StageSideRecP.stage_setStage_ne _ _ _ hr', ?_⟩
    rw [toPair_retG rfl]
    exact GBCA.LowPairStep.retG (toPair P u w r) j g _
      (Gather.LowStep.ret (toPair P u w r).2 j g hin hsubap hQ hr2)

/-- The call against an already-called record: the round loop moves and the
round instance takes its input-enabledness loop. -/
theorem stage_answer_gcallLoop (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    (w : NetState P.n) {j : Fin P.n} {c : CoreRec P.n} {p : StageSideRec P.n}
    (hu : (u j).2 = p) {r : ℕ} {b : Bool} {μ : PMF (ProcRec P.n)}
    (h : StageStep P j (c, p) (Sum.inr (.gcallLoop r j b)) μ) :
    ∃ x : ProcRec P.n, μ = PMF.pure x ∧ x.2 = p ∧
      c.corrupted = false ∧ c.proc.phase = .toCallG ∧ c.proc.round = r ∧
      c.proc.est = some b ∧
      x.1 = c.setProc { c.proc with phase := .awaitG } ∧
      (∀ r', r' ≠ r → x.2.stage r' = p.stage r') ∧
      GBCA.LowPairStep P r (toPair P u w r) (.callG r j b)
        (PMF.pure (toPair P u w r)) := by
  subst hu
  cases h with
  | gcallLoop _ _ _ _ hh hph hr hest hin =>
    exact ⟨_, rfl, rfl, hh, hph, hr, hest, rfl, fun r' _ => rfl,
      GBCA.LowPairStep.callG (toPair P u w r) j b _
        (Gather.LowStep.callLoop (toPair P u w r).1 j b)⟩


/-! ### Answering a Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the fabric its tag names and no record moves. -/

/-- A Byzantine injection on the first gather's fabric, read through the view. -/
theorem toPair_byzGa1 (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (mm : GaMsg P.n Bool) :
    toPair P u (w.gpool r k (.ga1 mm)) r
      = ({ toLow1 P u w r with ga := (toLow1 P u w r).ga.mcast k mm },
         toLow2 P u w r) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, SubState.mcast, Fabric.post, gpool_pool_self]
    exact slice_post_some unGa1 unGa1_inj (w.pool r) k (.ga1 mm) mm rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unIn1 kk) (unIn1_inj kk) (w.pool r) k (.ga1 mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unBind1 kk) (unBind1_inj kk) (w.pool r) k (.ga1 mm) rfl
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none unGa2 unGa2_inj (w.pool r) k (.ga1 mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unIn2 kk) (unIn2_inj kk) (w.pool r) k (.ga1 mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unBind2 kk) (unBind2_inj kk) (w.pool r) k (.ga1 mm) rfl

/-- A Byzantine injection on the second gather's fabric, read through the view. -/
theorem toPair_byzGa2 (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (mm : GaMsg P.n (Option Bool)) :
    toPair P u (w.gpool r k (.ga2 mm)) r
      = (toLow1 P u w r,
         { toLow2 P u w r with ga := (toLow2 P u w r).ga.mcast k mm }) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none unGa1 unGa1_inj (w.pool r) k (.ga2 mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unIn1 kk) (unIn1_inj kk) (w.pool r) k (.ga2 mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unBind1 kk) (unBind1_inj kk) (w.pool r) k (.ga2 mm) rfl
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, SubState.mcast, Fabric.post, gpool_pool_self]
    exact slice_post_some unGa2 unGa2_inj (w.pool r) k (.ga2 mm) mm rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unIn2 kk) (unIn2_inj kk) (w.pool r) k (.ga2 mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unBind2 kk) (unBind2_inj kk) (w.pool r) k (.ga2 mm) rfl

/-- A Byzantine injection in an input-broadcast instance of the first gather. -/
theorem toPair_byzIn1 (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg Bool) :
    toPair P u (w.gpool r k (.brbIn1 i mm)) r
      = ({ toLow1 P u w r with
            brbIn := Function.update (toLow1 P u w r).brbIn i
              (((toLow1 P u w r).brbIn i).mcast k mm) },
         toLow2 P u w r) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none unGa1 unGa1_inj (w.pool r) k (.brbIn1 i mm) rfl
  · funext kk
    by_cases hk : kk = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_self, SubState.mcast]
      · simp only [toPair, toLow1, Function.update_self, SubState.mcast,
          Fabric.post, gpool_pool_self]
        exact slice_post_some (unIn1 kk) (unIn1_inj kk) (w.pool r) k
          (.brbIn1 kk mm) mm (by simp [unIn1])
      · simp only [toPair, toLow1, Function.update_self, SubState.mcast,
          Fabric.post, gpool_F]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_of_ne hk]
      · simp only [toPair, toLow1, Function.update_of_ne hk, gpool_pool_self]
        exact slice_post_none (unIn1 kk) (unIn1_inj kk) (w.pool r) k (.brbIn1 i mm)
          (by simp [unIn1, Ne.symm hk])
      · simp only [toPair, toLow1, Function.update_of_ne hk, gpool_F]
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unBind1 kk) (unBind1_inj kk) (w.pool r) k (.brbIn1 i mm) rfl
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none unGa2 unGa2_inj (w.pool r) k (.brbIn1 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unIn2 kk) (unIn2_inj kk) (w.pool r) k (.brbIn1 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unBind2 kk) (unBind2_inj kk) (w.pool r) k (.brbIn1 i mm) rfl

/-- A Byzantine injection in a bind-broadcast instance of the first gather. -/
theorem toPair_byzBind1 (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg (APSet P.n Bool)) :
    toPair P u (w.gpool r k (.brbBind1 i mm)) r
      = ({ toLow1 P u w r with
            brbBind := Function.update (toLow1 P u w r).brbBind i
              (((toLow1 P u w r).brbBind i).mcast k mm) },
         toLow2 P u w r) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none unGa1 unGa1_inj (w.pool r) k (.brbBind1 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unIn1 kk) (unIn1_inj kk) (w.pool r) k (.brbBind1 i mm) rfl
  · funext kk
    by_cases hk : kk = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_self, SubState.mcast]
      · simp only [toPair, toLow1, Function.update_self, SubState.mcast,
          Fabric.post, gpool_pool_self]
        exact slice_post_some (unBind1 kk) (unBind1_inj kk) (w.pool r) k
          (.brbBind1 kk mm) mm (by simp [unBind1])
      · simp only [toPair, toLow1, Function.update_self, SubState.mcast,
          Fabric.post, gpool_F]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_of_ne hk]
      · simp only [toPair, toLow1, Function.update_of_ne hk, gpool_pool_self]
        exact slice_post_none (unBind1 kk) (unBind1_inj kk) (w.pool r) k (.brbBind1 i mm)
          (by simp [unBind1, Ne.symm hk])
      · simp only [toPair, toLow1, Function.update_of_ne hk, gpool_F]
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none unGa2 unGa2_inj (w.pool r) k (.brbBind1 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unIn2 kk) (unIn2_inj kk) (w.pool r) k (.brbBind1 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unBind2 kk) (unBind2_inj kk) (w.pool r) k (.brbBind1 i mm) rfl

/-- A Byzantine injection in an input-broadcast instance of the second gather. -/
theorem toPair_byzIn2 (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg (Option Bool)) :
    toPair P u (w.gpool r k (.brbIn2 i mm)) r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            brbIn := Function.update (toLow2 P u w r).brbIn i
              (((toLow2 P u w r).brbIn i).mcast k mm) }) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none unGa1 unGa1_inj (w.pool r) k (.brbIn2 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unIn1 kk) (unIn1_inj kk) (w.pool r) k (.brbIn2 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unBind1 kk) (unBind1_inj kk) (w.pool r) k (.brbIn2 i mm) rfl
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none unGa2 unGa2_inj (w.pool r) k (.brbIn2 i mm) rfl
  · funext kk
    by_cases hk : kk = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_self, SubState.mcast]
      · simp only [toPair, toLow2, Function.update_self, SubState.mcast,
          Fabric.post, gpool_pool_self]
        exact slice_post_some (unIn2 kk) (unIn2_inj kk) (w.pool r) k
          (.brbIn2 kk mm) mm (by simp [unIn2])
      · simp only [toPair, toLow2, Function.update_self, SubState.mcast,
          Fabric.post, gpool_F]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_of_ne hk]
      · simp only [toPair, toLow2, Function.update_of_ne hk, gpool_pool_self]
        exact slice_post_none (unIn2 kk) (unIn2_inj kk) (w.pool r) k (.brbIn2 i mm)
          (by simp [unIn2, Ne.symm hk])
      · simp only [toPair, toLow2, Function.update_of_ne hk, gpool_F]
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unBind2 kk) (unBind2_inj kk) (w.pool r) k (.brbIn2 i mm) rfl

/-- A Byzantine injection in a bind-broadcast instance of the second gather. -/
theorem toPair_byzBind2 (u : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg (APSet P.n (Option Bool))) :
    toPair P u (w.gpool r k (.brbBind2 i mm)) r
      = (toLow1 P u w r,
         { toLow2 P u w r with
            brbBind := Function.update (toLow2 P u w r).brbBind i
              (((toLow2 P u w r).brbBind i).mcast k mm) }) := by
  refine Prod.ext (lowState_ext ?_ ?_ ?_) (lowState_ext ?_ ?_ ?_)
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none unGa1 unGa1_inj (w.pool r) k (.brbBind2 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unIn1 kk) (unIn1_inj kk) (w.pool r) k (.brbBind2 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow1, gpool_pool_self]
    exact slice_post_none (unBind1 kk) (unBind1_inj kk) (w.pool r) k (.brbBind2 i mm) rfl
  · refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none unGa2 unGa2_inj (w.pool r) k (.brbBind2 i mm) rfl
  · funext kk
    refine Prod.ext rfl (fabric_ext ?_ rfl)
    simp only [toPair, toLow2, gpool_pool_self]
    exact slice_post_none (unIn2 kk) (unIn2_inj kk) (w.pool r) k (.brbBind2 i mm) rfl
  · funext kk
    by_cases hk : kk = i
    · subst hk
      refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_self, SubState.mcast]
      · simp only [toPair, toLow2, Function.update_self, SubState.mcast,
          Fabric.post, gpool_pool_self]
        exact slice_post_some (unBind2 kk) (unBind2_inj kk) (w.pool r) k
          (.brbBind2 kk mm) mm (by simp [unBind2])
      · simp only [toPair, toLow2, Function.update_self, SubState.mcast,
          Fabric.post, gpool_F]
    · refine Prod.ext ?_ (fabric_ext ?_ ?_)
      · simp only [toPair, toLow1, toLow2, Function.update_of_ne hk]
      · simp only [toPair, toLow2, Function.update_of_ne hk, gpool_pool_self]
        exact slice_post_none (unBind2 kk) (unBind2_inj kk) (w.pool r) k (.brbBind2 i mm)
          (by simp [unBind2, Ne.symm hk])
      · simp only [toPair, toLow2, Function.update_of_ne hk, gpool_F]



/-- A Byzantine injection is answered by the round instance's own injection on
the fabric the message's tag names. -/
theorem byz_answer (P : Params) (u : ∀ _ : Fin P.n, ProcRec P.n)
    (w : NetState P.n) (r : ℕ) {k : Fin P.n} (m : Msg P.n) (hF : k ∈ w.F) :
    GBCA.LowPairStep P r (toPair P u w r) Lab.tau
      (PMF.pure (toPair P u (w.gpool r k m) r)) := by
  cases m with
  | ga1 mm =>
    rw [toPair_byzGa1]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.byz (toPair P u w r).1 k mm hF)
  | ga2 mm =>
    rw [toPair_byzGa2]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.byz (toPair P u w r).2 k mm hF)
  | brbIn1 i mm =>
    rw [toPair_byzIn1]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).1 i _
        (BRB.ImplStep.byz ((toPair P u w r).1.brbIn i) k mm hF))
  | brbBind1 i mm =>
    rw [toPair_byzBind1]
    exact GBCA.LowPairStep.ga1Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).1 i _
        (BRB.ImplStep.byz ((toPair P u w r).1.brbBind i) k mm hF))
  | brbIn2 i mm =>
    rw [toPair_byzIn2]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbInTau (toPair P u w r).2 i _
        (BRB.ImplStep.byz ((toPair P u w r).2.brbIn i) k mm hF))
  | brbBind2 i mm =>
    rw [toPair_byzBind2]
    exact GBCA.LowPairStep.ga2Tau (toPair P u w r) _
      (Gather.LowStep.brbBindTau (toPair P u w r).2 i _
        (BRB.ImplStep.byz ((toPair P u w r).2.brbBind i) k mm hF))

/-- The matching on the silent label. The flat reading's own `terminate` row
writes no coordinate the relation reads, so the composed answer to it is to
stand still; the adversary's two injections and the coin resolution are
answered by a transition. -/
theorem match_tau (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.LowPairState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : Comp.ANetState P.n} (hR : ProtocolRel P (u, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolPre P).step (u, w, o) (Sum.inl Lab.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      ((composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) ∨
        Ω.bind id = PMF.pure (G, C, A, o)) := by
  obtain ⟨hC, -, hA, hGv⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  rcases flatPre_tau_inv h with ⟨i, y, hstep, rfl⟩ | ⟨w', hn, rfl⟩ | ⟨ω, hW, rfl⟩
  · obtain ⟨b, hh, hret, hcnt, hterm, hy⟩ := stepN_tau_terminate hstep
    obtain rfl : y = ((u i).1, { (u i).2 with terminated := true }) := pureN_inj hy
    have hrel : ProtocolRel P
        (Function.update u i ((u i).1, { (u i).2 with terminated := true }), w, o)
        (G, C, A, o) := by
      refine (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨fun j => ?_, rfl, hA, ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact hC j
        · rw [Function.update_of_ne hj]; exact hC j
      · rw [hGv]
        funext r
        refine (toPair_congr (fun j => ?_) w).symm
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; rfl
        · rw [Function.update_of_ne hj]
    obtain ⟨Ω, hrelΩ, hb⟩ := match_pure P hrel
    exact ⟨Ω, hrelΩ, Or.inr hb⟩
  · rcases netStep_tau hn with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.gpool r k m := pureN_inj hw
      have hrel : ProtocolRel P (u, w.gpool r k m, o)
          (Function.update G r (toPair P u (w.gpool r k m) r), C, A, o) :=
        (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, by simpa using hA, by
          rw [hGv]; exact (toPairFamPool u w r k m _ rfl).symm⟩
      obtain ⟨Ω, hrelΩ, hb⟩ := match_pure P hrel
      refine ⟨Ω, hrelΩ, Or.inl (composedGroup_of_tau P ?_)⟩
      rw [hb]
      refine composedPre_tau_low P (lowSide_tau P G r ?_)
      refine liftedLow_step P r (l₀ := Lab.tau) (by simp) ?_
      rw [hGv]
      exact byz_answer P u w r m hF
    · obtain rfl : w' = w.dput k b := pureN_inj hw
      have hrel : ProtocolRel P (u, w.dput k b, o)
          (G, C, ⟨(w.dput k b).dpool, (w.dput k b).F⟩, o) :=
        (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, rfl, by rw [hGv]; funext r; rfl⟩
      obtain ⟨Ω, hrelΩ, hb⟩ := match_pure P hrel
      refine ⟨Ω, hrelΩ, Or.inl (composedGroup_of_tau P ?_)⟩
      rw [hb]
      refine composedPre_tau_aNet P ?_
      rw [hA]
      exact Comp.ANetStep.byzD ⟨w.dpool, w.F⟩ k b hF
  · obtain ⟨Ω, hrel, hb⟩ := match_prod P (x := u) (w := w) (G := G) (C := C) (A := A)
      (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hGv⟩)
    refine ⟨Ω, hrel, Or.inl (composedGroup_of_tau P ?_)⟩
    rw [hb]
    exact composedPre_tau_wcc P hW


/-- A row that leaves every round record where it stands leaves the whole
family of rounds where it stands. -/
theorem view_unchanged {x u : ∀ _ : Fin P.n, ProcRec P.n}
    (h : ∀ i, (x i).2 = (u i).2) (w : NetState P.n) :
    (fun r => toPair P u w r) = fun r => toPair P x w r := by
  funext r
  exact (toPair_congr (fun i => by rw [h i]) w).symm


/-- The matching on a visible shared label. -/
theorem match_lab (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.LowPairState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : Comp.ANetState P.n} (hR : ProtocolRel P (u, w, o) (G, C, A, o))
    {l : Lab P.n} (hl : l ≠ Lab.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolPre P).step (u, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      (composedGroup P).step (G, C, A, o) l (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := flatPre_lab_inv hl h
  have hWl : (Net.wccLift P).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (wccPull_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : NLab P.n) ≠ Silent.τ := by simpa using hl
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  suffices hsuf : ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedPre P).step (G, C, A, o) (Sum.inl l) (Ω.bind id) by
    obtain ⟨Ω, hr, hs⟩ := hsuf
    exact ⟨Ω, hr, (composedGroup_step_iff P _ _ _).mpr (Or.inr hs)⟩
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pureN_inj (netStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_callABA_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_callABA_own (hall i) with ⟨-, -, hx⟩ | hx <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w'⟩)
      (lowSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (Comp.ANetStep.callABAIdle A id b) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_callABA_own (hall i) with ⟨hh, hin, hx⟩ | hx
      · rw [pureN_inj hx]; exact Comp.CoreProcStepN.input _ b hh hin
      · rw [pureN_inj hx]
        by_cases hc : (u i).1.corrupted = true
        · exact Comp.CoreProcStepN.corruptedIdle _ _ hc (by simp) not_false
        · exact Comp.CoreProcStepN.inputLoop _ b (by simpa using hc)
    · rw [hfor i hi]; exact Comp.CoreProcStepN.callABAIdle _ id b (Ne.symm hi)
  | retABA id b =>
    obtain ⟨hdp, hw⟩ := netStep_retABA hn
    obtain rfl : w' = w := pureN_inj hw
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retABA_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_retABA_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;>
          rw [pureN_inj hx]
      · rw [hfor i hi]
    have hAn : Comp.ANetStep P A (Sum.inl (Lab.retABA id b)) (PMF.pure A) := by
      rw [hA]
      rcases hdp with hd | hf
      · exact Comp.ANetStep.retABA ⟨w'.dpool, w'.F⟩ id b hd
      · exact Comp.ANetStep.retByz ⟨w'.dpool, w'.F⟩ id b hf
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w'⟩)
      (lowSide_idle P G hLne (by simp) not_false) (fun i => ?_) hAn hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_retABA_own (hall i) with ⟨hh, hin, hcnt, hret, hx⟩ | ⟨hc, hx⟩
      · rw [pureN_inj hx]; exact Comp.CoreProcStepN.ret _ b hh hcnt hret
      · rw [pureN_inj hx]
        exact Comp.CoreProcStepN.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact Comp.CoreProcStepN.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w' = w := pureN_inj (netStep_callW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_callW_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_callW_own (hall i) with ⟨-, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w'⟩)
      (lowSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (Comp.ANetStep.callWIdle A r id) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_callW_own (hall i) with ⟨hh, hph, hr, hx⟩ | ⟨hc, hx⟩
      · rw [pureN_inj hx]; exact Comp.CoreProcStepN.callW _ r hh hph hr
      · rw [pureN_inj hx]
        exact Comp.CoreProcStepN.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact Comp.CoreProcStepN.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w' = w := pureN_inj (netStep_retW hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retW_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi
        rcases stepN_retW_own (hall i) with ⟨-, -, -, -, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w'⟩)
      (lowSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (Comp.ANetStep.retWIdle A r id co) hWl
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi
      rcases stepN_retW_own (hall i) with ⟨hh, hph, hr, hgr, hx⟩ | ⟨hc, hx⟩
      · rw [pureN_inj hx]; exact Comp.CoreProcStepN.retW _ r co hh hph hr hgr
      · rw [pureN_inj hx]
        exact Comp.CoreProcStepN.corruptedIdle _ _ hc (by simp) not_false
    · rw [hfor i hi]; exact Comp.CoreProcStepN.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain ⟨hnew, hbud, hw⟩ := netStep_fail hn
    obtain rfl : w' = NetStateP.corrupt P k w := pureN_inj hw
    have hfor : ∀ i, i ≠ k → x i = u i := fun i hi =>
      pureN_inj (stepN_fail_foreign (Ne.symm hi) (hall i))
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = k
      · subst hi
        rcases stepN_fail_own (hall i) with ⟨-, hx⟩ | ⟨-, hx⟩ <;> rw [pureN_inj hx]
      · rw [hfor i hi]
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, ?_, ?_⟩)
      (lowSide_fail P G k) (fun i => ?_)
      (Comp.ANetStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    · rw [hA]
      unfold Comp.ANetState.corrupt NetStateP.corrupt
      split_ifs <;> rfl
    · funext r
      rw [hGv]
      simp only []
      exact ((toPair_fail u w r k).symm).trans
        ((toPair_congr (r := r) (fun i => by rw [hsame i])
          (NetStateP.corrupt P k w)).symm)
    · by_cases hi : i = k
      · subst hi
        rcases stepN_fail_own (hall i) with ⟨hh, hx⟩ | ⟨hh, hx⟩
        · rw [hCeq i, pureN_inj hx]; exact Comp.CoreProcStepN.failSelf _ hh
        · rw [hCeq i, pureN_inj hx]
          exact Comp.CoreProcStepN.corruptedIdle _ _ hh (by simp) not_false
      · rw [hCeq i, hfor i hi]; exact Comp.CoreProcStepN.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = w.gpool r id (gCallPayload P id b) :=
      pureN_inj (netStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_callG_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hest, hx1, hoff, hlow⟩ :=
      stage_answer_callG P w (u := u) (j := id) rfl (stageRow_of_own rfl (hall id))
    obtain rfl : x id = y := pureN_inj hy
    have hxeq : x = Function.update u id (x id) := by
      funext i
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; simp, ?_⟩)
      (lowSide_owned P G r (by simp)
        (liftedLow_step P r (l₀ := Lab.callG r id b) (by simp)
          (by rw [hGv]; exact hlow)))
      (fun i => ?_) (Comp.ANetStep.callGIdle A r id b) hWl
    · funext r'
      have hxc : ∀ i, (x i).2.stage r'
          = ((Function.update u id (x id)) i).2.stage r' := by
        intro i
        by_cases hi : i = id
        · subst hi; rw [Function.update_self]
        · rw [Function.update_of_ne hi, hfor i hi]
      rw [hGv]
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact (toPair_congr hxc _).symm
      · rw [Function.update_of_ne hr']
        refine ((toPair_congr (r := r') (fun i => ?_) _).trans
          (toPair_otherPool u w hr' id _)).symm
        by_cases hi : i = id
        · subst hi; exact hoff r' hr'
        · rw [hfor i hi]
    · rw [hCeq i]
      by_cases hi : i = id
      · subst hi
        rw [hx1]
        exact Comp.CoreProcStepN.callG _ r b hh hph hrr hest
      · rw [hfor i hi]; exact Comp.CoreProcStepN.callGIdle _ r id b (Ne.symm hi)
  | retG r id out =>
    obtain rfl : w' = w := pureN_inj (netStep_retG hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retG_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hh, hph, hrr, hx1, hoff, hlow⟩ :=
      stage_answer_retG P w' (u := u) (j := id) rfl (stageRow_of_own rfl (hall id))
    obtain rfl : x id = y := pureN_inj hy
    have hxeq : x = Function.update u id (x id) := by
      funext i
      by_cases hi : i = id
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, ?_⟩)
      (lowSide_owned P G r (by simp)
        (liftedLow_step P r (l₀ := Lab.retG r id out) (by simp)
          (by rw [hGv]; exact hlow)))
      (fun i => ?_) (Comp.ANetStep.retGIdle A r id out) hWl
    · funext r'
      have hxc : ∀ i, (x i).2.stage r'
          = ((Function.update u id (x id)) i).2.stage r' := by
        intro i
        by_cases hi : i = id
        · subst hi; rw [Function.update_self]
        · rw [Function.update_of_ne hi, hfor i hi]
      rw [hGv]
      by_cases hr' : r' = r
      · subst hr'
        rw [Function.update_self]
        exact (toPair_congr hxc _).symm
      · rw [Function.update_of_ne hr']
        refine (toPair_congr (r := r') (fun i => ?_) _).symm
        by_cases hi : i = id
        · subst hi; exact hoff r' hr'
        · rw [hfor i hi]
    · rw [hCeq i]
      by_cases hi : i = id
      · subst hi
        rw [hx1]
        exact Comp.CoreProcStepN.retG _ r out hh hph hrr
      · rw [hfor i hi]; exact Comp.CoreProcStepN.retGIdle _ r id out (Ne.symm hi)


/-- The matching on a rendezvous of the flat reading. A send and a delivery
are internal to the round instance, so the composed reading answers them with
one of its own silent rules; the DECIDED rows, the fused coin return and the
drives are answered by the same rendezvous. -/
theorem match_event (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.LowPairState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : Comp.ANetState P.n} (hR : ProtocolRel P (u, w, o) (G, C, A, o))
    (e : NetEvtP P.n (Msg P.n)) {μ : PMF (ProtocolState P)}
    (h : (protocolPre P).step (u, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
  obtain ⟨hC, -, hA, hGv⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (u i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := flatPre_event_inv h
  have htau : ∀ {G' : ℕ → GBCA.LowPairState P.n}, ν = PMF.pure o →
      ProtocolRel P (x, w', o) (G', C, A, o) →
      (lowSide P).step G (Sum.inl Lab.tau) (PMF.pure G') →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRel P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
    intro G' hν hrel hGs
    subst hν
    obtain ⟨Ω, hr, hs⟩ := match_round P hrel hGs
    refine ⟨Ω, ?_, composedGroup_of_tau P hs⟩
    rwa [prodPMF_pure_pure, prodPMF_pure_pure]
  have hvis : ∀ {G' : ℕ → GBCA.LowPairState P.n} {A' : Comp.ANetState P.n}
      (e' : NetEvt P.n), (Sum.inr e' : NLab P.n) ≠ Silent.τ →
      (∀ o' ∈ ν.support, ProtocolRel P (x, w', o') (G', fun i => (x i).1, A', o')) →
      (lowSide P).step G (Sum.inr e') (PMF.pure G') →
      (∀ i, Comp.CoreProcStepN P i (C i) (Sum.inr e') (PMF.pure ((x i).1))) →
      Comp.ANetStep P A (Sum.inr e') (PMF.pure A') →
      (Net.wccLift P).step o (Sum.inr e') ν →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRel P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
    intro G' A' e' hne hrel hGs hCs hAs hWs'
    obtain ⟨Ω, hr, hs⟩ := match_vis P hne hrel hGs hCs hAs hWs'
    exact ⟨Ω, hr, composedGroup_of_event P e' hs⟩
  cases e with
  | gsnd r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gsnd r j m) ν).mp hWs
    obtain rfl : w' = w.gpool r j m := pureN_inj (netStep_gsnd hn)
    have hfor : ∀ i, i ≠ j → x i = u i := fun i hi =>
      pureN_inj (stepN_gsnd_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hcore, hoff, hlow⟩ :=
      stage_answer_gsnd P w (u := u) (j := j) rfl (stageRow_of_own rfl (hall j))
    obtain rfl : x j = y := pureN_inj hy
    have hxeq : ∀ i, x i = (Function.update u j (x j)) i := by
      intro i
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i hi]
    refine htau rfl ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i => by
        rw [hCeq i]
        by_cases hi : i = j
        · subst hi; rw [hcore]
        · rw [hfor i hi], rfl, by rw [hA]; simp, ?_⟩)
      (lowSide_tau P G r (liftedLow_step P r (l₀ := Lab.tau) (by simp)
        (by rw [hGv]; exact hlow)))
    funext r'
    rw [hGv]
    by_cases hr' : r' = r
    · subst hr'
      rw [Function.update_self]
      exact (toPair_congr (r := r') (fun i => by rw [hxeq i]) _).symm
    · rw [Function.update_of_ne hr']
      refine ((toPair_congr (r := r') (fun i => ?_) _).trans
        (toPair_otherPool u w hr' j m)).symm
      by_cases hi : i = j
      · subst hi; exact hoff r' hr'
      · rw [hfor i hi]
  | gdlv r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gdlv r i k m) ν).mp hWs
    obtain ⟨hpool, hw⟩ := netStep_gdlv hn
    obtain rfl : w' = w := pureN_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pureN_inj (stepN_gdlv_foreign (Ne.symm hi) (hall i'))
    obtain ⟨y, hy, hcore, hoff, hlow⟩ :=
      stage_answer_gdlv P w' (u := u) (j := i) rfl hpool
        (stageRow_of_own rfl (hall i))
    obtain rfl : x i = y := pureN_inj hy
    have hxeq : ∀ i', x i' = (Function.update u i (x i)) i' := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [Function.update_self]
      · rw [Function.update_of_ne hi, hfor i' hi]
    refine htau rfl ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun i' => by
        rw [hCeq i']
        by_cases hi : i' = i
        · subst hi; rw [hcore]
        · rw [hfor i' hi], rfl, hA, ?_⟩)
      (lowSide_tau P G r (liftedLow_step P r (l₀ := Lab.tau) (by simp)
        (by rw [hGv]; exact hlow)))
    funext r'
    rw [hGv]
    by_cases hr' : r' = r
    · subst hr'
      rw [Function.update_self]
      exact (toPair_congr (r := r') (fun i' => by rw [hxeq i']) _).symm
    · rw [Function.update_of_ne hr']
      refine (toPair_congr (r := r') (fun i' => ?_) _).symm
      by_cases hi : i' = i
      · subst hi; exact hoff r' hr'
      · rw [hfor i' hi]
  | dsnd j b =>
    obtain ⟨hd, hw⟩ := netStep_dsnd hn
    obtain rfl : w' = w.dput j b := pureN_inj hw
    have hx : ∀ i, x i = u i := by
      intro i
      by_cases hi : i = j
      · subst hi
        rcases stepN_dsnd_self (hall i) with ⟨-, -, -, hxi⟩ | ⟨-, hxi⟩ <;>
          exact pureN_inj hxi
      · exact pureN_inj (stepN_dsnd_foreign (Ne.symm hi) (hall i))
    refine hvis (.dsnd j b) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, by rw [hA]; rfl, by
          rw [hGv]; funext r; exact (toPair_congr (fun i => by rw [hx i]) _).symm⟩)
      (lowSide_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ Comp.ANetStep.dsnd ⟨w.dpool, w.F⟩ j b hd) hWs
    rw [hCeq i, hx i]
    by_cases hi : i = j
    · subst hi
      rcases stepN_dsnd_self (hall i) with ⟨hh, hin, hcnt, -⟩ | ⟨hc, -⟩
      · exact Comp.CoreProcStepN.dsndRelay _ b hh hcnt
      · exact Comp.CoreProcStepN.corruptedIdle _ _ hc (by simp) not_false
    · exact Comp.CoreProcStepN.dsndIdle _ j b (Ne.symm hi)
  | ddlv i k b =>
    obtain ⟨hd, hw⟩ := netStep_ddlv hn
    obtain rfl : w' = w := pureN_inj hw
    have hfor : ∀ i', i' ≠ i → x i' = u i' := fun i' hi =>
      pureN_inj (stepN_ddlv_foreign (Ne.symm hi) (hall i'))
    obtain ⟨hh, hr, hxi⟩ := stepN_ddlv_self (hall i)
    have hsame : ∀ i', (x i').2 = (u i').2 := by
      intro i'
      by_cases hi : i' = i
      · subst hi; rw [pureN_inj hxi]
      · rw [hfor i' hi]
    refine hvis (.ddlv i k b) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by
          rw [hGv]; exact view_unchanged hsame w'⟩)
      (lowSide_idle P G (by simp) (by simp) not_false) (fun i' => ?_)
      (hA ▸ Comp.ANetStep.ddlv ⟨w'.dpool, w'.F⟩ i k b hd) hWs
    rw [hCeq i']
    by_cases hi : i' = i
    · subst hi; rw [pureN_inj hxi]; exact Comp.CoreProcStepN.ddlvRecv _ k b hh hr
    · rw [hfor i' hi]; exact Comp.CoreProcStepN.ddlvIdle _ i k b (Ne.symm hi)
  | retWPub r id c b =>
    obtain rfl : w' = w.dput id b := pureN_inj (netStep_retWPub hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_retWPub_foreign (Ne.symm hi) (hall i))
    obtain ⟨hh, hph, hr, hgr, hxi⟩ := stepN_retWPub_self (hall id)
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; rw [pureN_inj hxi]
      · rw [hfor i hi]
    refine hvis (.retWPub r id c b) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, by rw [hA]; rfl, by
          rw [hGv]; funext r'; exact (toPair_congr (fun i => by rw [hsame i]) _).symm⟩)
      (lowSide_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ Comp.ANetStep.retWPub ⟨w.dpool, w.F⟩ r id c b) hWs
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [pureN_inj hxi]
      exact Comp.CoreProcStepN.retWPub _ r c b hh hph hr hgr
    · rw [hfor i hi]; exact Comp.CoreProcStepN.retWPubIdle _ r id c b (Ne.symm hi)
  | gcallLoop r id b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gcallLoop r id b) ν).mp hWs
    obtain rfl : w' = w := pureN_inj (netStep_gcallLoop hn)
    have hfor : ∀ i, i ≠ id → x i = u i := fun i hi =>
      pureN_inj (stepN_gcallLoop_foreign (Ne.symm hi) (hall i))
    obtain ⟨y, hy, hy2, hh, hph, hrr, hest, hx1, -, hlow⟩ :=
      stage_answer_gcallLoop P w' (u := u) (j := id) rfl
        (stageRow_of_own rfl (hall id))
    obtain rfl : x id = y := pureN_inj hy
    have hsame : ∀ i, (x i).2 = (u i).2 := by
      intro i
      by_cases hi : i = id
      · subst hi; exact hy2
      · rw [hfor i hi]
    refine hvis (.gcallLoop r id b) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, by rw [hGv]; exact view_unchanged hsame w'⟩)
      (lowSide_owned_id P G r (by simp)
        (liftedLow_step P r (l₀ := Lab.callG r id b) (by simp)
          (by rw [hGv]; exact hlow)))
      (fun i => ?_) (Comp.ANetStep.gcallLoop A r id b) hWs
    rw [hCeq i]
    by_cases hi : i = id
    · subst hi; rw [hx1]; exact Comp.CoreProcStepN.gcallLoop _ r b hh hph hrr hest
    · rw [hfor i hi]; exact Comp.CoreProcStepN.gcallLoopIdle _ r id b (Ne.symm hi)
  | byzCallGLoop r k b =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_byzCallGLoop r k b) ν).mp hWs
    obtain ⟨hF, hw⟩ := netStep_byzCallGLoop hn
    obtain rfl : w' = w := pureN_inj hw
    have hx : ∀ i, x i = u i := fun i => pureN_inj (stepN_byzCallGLoop (hall i))
    refine hvis (.byzCallGLoop r k b) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by
          rw [hGv]; funext r'; exact (toPair_congr (fun i => by rw [hx i]) _).symm⟩)
      (lowSide_owned_id P G r (by simp)
        (liftedLow_step P r (l₀ := Lab.callG r k b) (by simp)
          (by rw [hGv]
              exact GBCA.LowPairStep.callG (toPair P u w' r) k b _
                (Gather.LowStep.callLoop (toPair P u w' r).1 k b))))
      (fun i => ?_) (hA ▸ Comp.ANetStep.byzCallGLoop ⟨w'.dpool, w'.F⟩ r k b hF) hWs
    rw [hCeq i, hx i]
    exact Comp.CoreProcStepN.byzCallGLoopIdle _ r k b
  | byzCallW r k =>
    obtain ⟨hF, hw⟩ := netStep_byzCallW hn
    obtain rfl : w' = w := pureN_inj hw
    have hx : ∀ i, x i = u i := fun i => pureN_inj (stepN_byzCallW (hall i))
    refine hvis (.byzCallW r k) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by
          rw [hGv]; funext r'; exact (toPair_congr (fun i => by rw [hx i]) _).symm⟩)
      (lowSide_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ Comp.ANetStep.byzCallW ⟨w'.dpool, w'.F⟩ r k hF) hWs
    rw [hCeq i, hx i]
    exact Comp.CoreProcStepN.byzCallWIdle _ r k
  | byzRetW r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzRetW hn
    obtain rfl : w' = w := pureN_inj hw
    have hx : ∀ i, x i = u i := fun i => pureN_inj (stepN_byzRetW (hall i))
    refine hvis (.byzRetW r k b) (by simp) (fun o' _ =>
      (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun i => by rw [hx i], rfl, hA, by
          rw [hGv]; funext r'; exact (toPair_congr (fun i => by rw [hx i]) _).symm⟩)
      (lowSide_idle P G (by simp) (by simp) not_false) (fun i => ?_)
      (hA ▸ Comp.ANetStep.byzRetW ⟨w'.dpool, w'.F⟩ r k b hF) hWs
    rw [hCeq i, hx i]
    exact Comp.CoreProcStepN.byzRetWIdle _ r k b
  | byzCallG r k b => exact (stepN_byzCallG_dead (hall k)).elim
  | byzRetG r k out => exact (stepN_byzRetG_dead (hall k)).elim


/-- The matching at the group level: the rendezvous alphabet is hidden on both
sides, so a hidden rendezvous of the flat reading is answered by a silent
transition of the composed group. The second disjunct is the composed answer
to `terminate`: the state stands still under a silent label. -/
theorem match_group (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRel P s t) {l : Lab P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolGroup P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
        ((composedGroup P).step t l (Ω.bind id) ∨
          (l = Lab.tau ∧ Ω.bind id = PMF.pure t)) := by
  obtain ⟨u, w, o⟩ := s
  obtain ⟨G, C, A, o'⟩ := t
  obtain ⟨hC, ho, hA, hGv⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  have hR' : ProtocolRel P (u, w, o) (G, C, A, o) :=
    (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hGv⟩
  rcases (flatGroup_step_iff _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := match_event P hR' e hstep
    exact ⟨Ω, hrel, Or.inl hs⟩
  · by_cases hl : l = Lab.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := match_tau P hR' hstep
      exact ⟨Ω, hrel, hs.imp id (fun hp => ⟨rfl, hp⟩)⟩
    · obtain ⟨Ω, hrel, hs⟩ := match_lab P hR' hl hstep
      exact ⟨Ω, hrel, Or.inl hs⟩

/-- The matching at the system level: a hidden sub-protocol label is silent on
both sides, and every other label is answered on the nose or by standing
still. -/
theorem match_step (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRel P s t) {l : Lab P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step s l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (flat_step_iff s l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_group P hR hg
    rcases hlay with hlay | ⟨rfl, -⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl, weakTau_of_step rfl
        ((System.abstract_step _ _ _ _ _).mpr (Or.inl ⟨rfl, l', hmem, hlay⟩))⟩⟩
    · exact absurd hmem Lab.tau_not_mem_hiddenAPI
  · obtain ⟨Ω, hrel, hlay⟩ := match_group P hR hg
    rcases hlay with hlay | ⟨rfl, hpure⟩
    · have hstep : (composed P).step t l (Ω.bind id) :=
        (System.abstract_step _ _ _ _ _).mpr (Or.inr ⟨hnm, hlay⟩)
      by_cases hτ : l = Silent.τ
      · exact ⟨Ω, hrel, Or.inl ⟨hτ, weakTau_of_step hτ hstep⟩⟩
      · exact ⟨Ω, hrel, Or.inr ⟨hτ, weakStep_strong hstep⟩⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl, hpure ▸ weakTau_refl (composed P) (PMF.pure t)⟩⟩


/-- **The gather-based protocol forward-simulates into its composed reading**,
along the Dirac lift of the view. -/
theorem protocolSim (P : Params) :
    ProbabilisticForwardSimulation (protocol P) (composed P)
      (diracRel (ProtocolRel P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRel_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact match_step P hR hstep

/-- **The composition inclusion**: every trace distribution the gather-based
protocol achieves is achieved by its composed reading. -/
theorem protocol_composed (P : Params) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (composed P) :=
  (protocolSim P).achievableTraceDists_subset


/-! ### The headlines

The gather-based protocol reaches the ABA specification along the composed
reading it was cut into, and safety transfers to it. -/

/-- **Trace-distribution refinement of the gather-based protocol**: every
trace distribution achievable by the protocol as it runs is achievable by the
ABA specification. The composition inclusion gives the first step, the
substitution and the core simulation the rest. -/
theorem refines (P : Params) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (spec P) :=
  Set.Subset.trans (protocol_composed P) (composed_refines P)

/-- **Correctness of the gather-based protocol**: every positive-probability
trace of the protocol as it runs satisfies Validity and Agreement. No side
condition on the trace: the corruption budget is a guard of the network
adversary's own `fail` row, so every execution is in budget by construction. -/
theorem main (P : Params) :
    ∀ D ∈ achievableTraceDists (protocol P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t :=
  safety_transfer (refines P) (spec_safe P)

/-- **The composed gather-based simulation** `protocol ⊑ ABA.spec`: the
composition simulation joined with the chain from the composed reading by
Result 2. -/
noncomputable def chainSim (P : Params) :
    ProbabilisticForwardSimulation (protocol P) (spec P)
      (compRel (diracRel (ProtocolRel P))
        (compRel
          (compRel (parallelRel (diracRel (RlowAll P)))
            (compRel (parallelRel (diracRel (RidealAll P)))
              (parallelRel (diracRel (RpairAll P)))))
          (coreRel P))) :=
  (protocolSim P).trans (chainSimComposed P)

/-! ### Mechanical axiom firewall -/

/-- info: 'PLTS.ABA.AFW.protocolSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolSim

/-- info: 'PLTS.ABA.AFW.protocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_composed

/-- info: 'PLTS.ABA.AFW.refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refines

/-- info: 'PLTS.ABA.AFW.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main

/-- info: 'PLTS.ABA.AFW.chainSim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chainSim

end AFW

end ABA
end PLTS
