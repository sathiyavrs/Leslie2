/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.View

/-!
# The view of the composed round after one flat row

`AFW.toRound` (`ABA/AFW/View.lean`) computes the round-`r` state of the
composed reading from a state of `AFW.protocol P`. This file says where that
state stands after one row of the flat reading: for each row, the view after
the row is the view before the row with the composed round's own effect
applied, written through the updaters `GBCA.setProcs`, `GBCA.setBound`,
`GBCA.setGa1`, `GBCA.setGa2`, `Gather.setGa`, `Gather.setBrbIn`,
`Gather.setBrbBind` and `Gather.setCore` exactly as the composed rows write
them.

## One written record, transposed

A row writes the acting process's round record and records at most one tagged
message. `toRound_write` and `toRound_writeNoSent` do that write once, through
`toRoundUpd`: each local state vector becomes a one-point update of the old
one, and each network state is sliced out of the written sent family. What each
row still owes is then sent algebra alone, which `slice_post_some` and
`slice_post_none` supply.

## Three rows against two events

Three rows of the flat reading are answered by two events of the composed
round. The link is `ret1` and `call2`: `toRound_ret1_call2` states the view
after it as `afterCall2` of `afterRet1`, and `afterRet1` is the round after the
first event alone. The graded return is `ret2` and `retG`, with `afterRet2` the
intermediate state. A delivery that completes an `n − f` `VOTE` quorum is the
broadcast instance's `dlv` and then the gather's `inRet` (or `bindRet`), with
`afterDlvIn1` and its three companions the intermediate states.

## The store and the return flag

`storeIn` reads the delivered sets, so a broadcast delivery moves two
coordinates of the view at once. The instance's local state takes the message.
And where the delivery completes the receiver's `n − f` `VOTE` quorum, the
receiver's return flag in that instance goes on and the receiver's gather store
records the value. The quorum lemmas (`toRound_dlvIn1_ret` and its three
companions) carry the hypothesis that the store holds `v` after the delivery;
the plain lemmas (`toRound_dlvIn1` and its companions) carry the hypothesis
that the store does not move. `AFW.storeIn_eq_of_quorum` identifies the
store with the value a flat receipt quorum carries, which is what supplies
those hypotheses under `AFW.StoreInv`.

## The two clauses that are not readings

`StoreInv` and `BoundInv` are the conjuncts of `AFW.ProtocolRel` that no
frame lemma supplies. `storeInv_of` carries the first across a row from the
moves of the round's `4n` broadcast instances, each an application of
`BRB.Inv.step`, and `storeInv_congr` covers a row that leaves every round's
view where it stands. `boundInv_writeGhost` carries the second.
-/

namespace PLTS
namespace ABA
namespace AFW

open Net Comp GSub

/-! ### Two extensionality helpers -/

/-- A network state is its sent family beside its corrupted set. -/
theorem networkState_ext {n : ℕ} {M : Type} {a b : NetworkState n M}
    (hp : a.sent = b.sent) (hF : a.F = b.F) : a = b := by
  cases a; cases b; simp_all

/-- A gather-over-Bracha state is its gather tier beside its two broadcast
families and its core. -/
theorem subStateAt_ext {n : ℕ} {X B B' : Type} {a b : Gather.SubStateAt n X B B'}
    (h1 : Gather.ga a = Gather.ga b) (h2 : Gather.brbIn a = Gather.brbIn b)
    (h3 : Gather.brbBind a = Gather.brbBind b) (h4 : Gather.core a = Gather.core b) :
    a = b := by
  obtain ⟨⟨ua, ⟨wa, ca⟩⟩, ia, ba⟩ := a
  obtain ⟨⟨ub, ⟨wb, cb⟩⟩, ib, bb⟩ := b
  have hu : ua = ub := congrArg Prod.fst h1
  have hw : wa = wb := congrArg Prod.snd h1
  subst hu; subst hw
  change ia = ib at h2
  change ba = bb at h3
  change ca = cb at h4
  subst h2; subst h3; subst h4
  rfl

/-- A round state is its programs and its bound bit beside its two gather
instances. -/
theorem roundStateAt_ext {n : ℕ} {G₁ G₂ : Type} {a b : GBCA.RoundStateAt n G₁ G₂}
    (h1 : GBCA.procs a = GBCA.procs b) (h2 : GBCA.bound a = GBCA.bound b)
    (h3 : GBCA.ga1 a = GBCA.ga1 b) (h4 : GBCA.ga2 a = GBCA.ga2 b) : a = b := by
  obtain ⟨⟨ua, va⟩, ca, da⟩ := a
  obtain ⟨⟨ub, vb⟩, cb, db⟩ := b
  change ua = ub at h1
  change va = vb at h2
  change ca = cb at h3
  change da = db at h4
  subst h1; subst h2; subst h3; subst h4
  rfl

/-! ### Slicing a tagged sent -/

variable {n : ℕ} {β : Type}

/-- A sent message of another tag leaves the slice alone. -/
theorem slice_post_none (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (sent : Fin n → Finset (Msg n)) (j : Fin n) (m : Msg n) (hm : f m = none) :
    slice f hf (Function.update sent j (insert m (sent j))) = slice f hf sent := by
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

/-- A sent message of the tag being sliced arrives in that slice. -/
theorem slice_post_some [DecidableEq β] (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (sent : Fin n → Finset (Msg n)) (j : Fin n) (m : Msg n) (b : β)
    (hm : f m = some b) :
    slice f hf (Function.update sent j (insert m (sent j)))
      = Function.update (slice f hf sent) j (insert b (slice f hf sent j)) := by
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

/-! ### Reading a written record -/

variable {P : Params}

/-- The round record a process holds at the round it has just written. -/
theorem stage_update_self {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {j : Fin P.n}
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
theorem stage_update_ne {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {j : Fin P.n}
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
@[simp] theorem core_update {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {j : Fin P.n}
    (x : AFW.ProcRec P.n) (i : Fin P.n) :
    (Function.update u j x i).1 = if i = j then x.1 else (u i).1 := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hi, if_neg hi]

/-- The view reads a process family through its round records alone. -/
theorem toRound_congr {x u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w : NetState P.n} {r : ℕ}
    (h : ∀ i, (x i).2.stage r = (u i).2.stage r) :
    toRound P x w r = toRound P u w r := by
  simp only [toRound, toGa1, toGa2, h]

/-! ### Transposing one written record

A row writes the acting process's round record, so each local state vector the
view reads becomes a one-point update of the old one. Each lemma below is that
observation at one component of the view, stated over the `ite` that reading a
written record produces. -/

section Locals

variable {j : Fin P.n} (Y : Fin P.n → StageRec P.n) (sr : StageRec P.n)

theorem locals_toProc_if :
    (fun i => toProc (if i = j then sr else Y i))
      = Function.update (fun i => toProc (Y i)) j (toProc sr) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_view1_if :
    (fun i => gaProcView P Bool (if i = j then sr else Y i).ga1
        (if i = j then sr else Y i).brbIn1 (if i = j then sr else Y i).brbBind1)
      = Function.update
          (fun i => gaProcView P Bool (Y i).ga1 (Y i).brbIn1 (Y i).brbBind1) j
          (gaProcView P Bool sr.ga1 sr.brbIn1 sr.brbBind1) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_view2_if :
    (fun i => gaProcView P (Option Bool) (if i = j then sr else Y i).ga2
        (if i = j then sr else Y i).brbIn2 (if i = j then sr else Y i).brbBind2)
      = Function.update
          (fun i => gaProcView P (Option Bool) (Y i).ga2 (Y i).brbIn2 (Y i).brbBind2) j
          (gaProcView P (Option Bool) sr.ga2 sr.brbIn2 sr.brbBind2) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_in1_if (k : Fin P.n) :
    (fun i => brbLocal P ((if i = j then sr else Y i).brbIn1 k))
      = Function.update (fun i => brbLocal P ((Y i).brbIn1 k)) j
          (brbLocal P (sr.brbIn1 k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_bind1_if (k : Fin P.n) :
    (fun i => brbLocal P ((if i = j then sr else Y i).brbBind1 k))
      = Function.update (fun i => brbLocal P ((Y i).brbBind1 k)) j
          (brbLocal P (sr.brbBind1 k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_in2_if (k : Fin P.n) :
    (fun i => brbLocal P ((if i = j then sr else Y i).brbIn2 k))
      = Function.update (fun i => brbLocal P ((Y i).brbIn2 k)) j
          (brbLocal P (sr.brbIn2 k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_bind2_if (k : Fin P.n) :
    (fun i => brbLocal P ((if i = j then sr else Y i).brbBind2 k))
      = Function.update (fun i => brbLocal P ((Y i).brbBind2 k)) j
          (brbLocal P (sr.brbBind2 k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

end Locals

/-! ### The view after one write

A row of the flat reading writes one component of the acting process's round
record and records at most one tagged message. The two lemmas below are that
write read through the view: each local state vector becomes a one-point
update, and each network state is sliced out of the written sent family. What
every row still owes is then sent algebra alone. -/

section Frame

variable {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w : NetState P.n} {j : Fin P.n}
    {c : CoreRec P.n} {p : StageSideRec P.n}

/-- The view after a write, with the one-point update pushed inside every
coordinate: the acting process's local state replaced in each local state
vector, and each network state sliced out of the written sent. The two cores
and the bound bit are the adversary's ghost record of the round, which a write
leaves alone. -/
noncomputable def toRoundUpd (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (r : ℕ) (j : Fin P.n) (sr : StageRec P.n)
    (sent : Fin P.n → Finset (Msg P.n)) : GBCA.LowPairState P.n :=
  ((Function.update (fun i => toProc ((u i).2.stage r)) j (toProc sr),
      (w.ghostRec r).2.2),
    (((Function.update
            (fun i => gaProcView P Bool ((u i).2.stage r).ga1 ((u i).2.stage r).brbIn1
              ((u i).2.stage r).brbBind1) j
            (gaProcView P Bool sr.ga1 sr.brbIn1 sr.brbBind1),
          ⟨⟨slice unGa1 unGa1_inj sent, w.F⟩, (w.ghostRec r).1⟩),
        fun k => (Function.update (fun i => brbLocal P (((u i).2.stage r).brbIn1 k)) j
            (brbLocal P (sr.brbIn1 k)),
          ⟨slice (unIn1 k) (unIn1_inj k) sent, w.F⟩),
        fun q => (Function.update (fun i => brbLocal P (((u i).2.stage r).brbBind1 q)) j
            (brbLocal P (sr.brbBind1 q)),
          ⟨slice (unBind1 q) (unBind1_inj q) sent, w.F⟩)),
      ((Function.update
            (fun i => gaProcView P (Option Bool) ((u i).2.stage r).ga2
              ((u i).2.stage r).brbIn2 ((u i).2.stage r).brbBind2) j
            (gaProcView P (Option Bool) sr.ga2 sr.brbIn2 sr.brbBind2),
          ⟨⟨slice unGa2 unGa2_inj sent, w.F⟩, (w.ghostRec r).2.1⟩),
        fun k => (Function.update (fun i => brbLocal P (((u i).2.stage r).brbIn2 k)) j
            (brbLocal P (sr.brbIn2 k)),
          ⟨slice (unIn2 k) (unIn2_inj k) sent, w.F⟩),
        fun q => (Function.update (fun i => brbLocal P (((u i).2.stage r).brbBind2 q)) j
            (brbLocal P (sr.brbBind2 q)),
          ⟨slice (unBind2 q) (unBind2_inj q) sent, w.F⟩))))

/-- **A write, read through the view.** A row writes the acting process's round
record and records one tagged message; the round it names then reads as the
one-point update of every coordinate. -/
theorem toRound_write (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) (m : Msg P.n) :
    toRound P (Function.update u j (c, (u j).2.setStage r sr)) (w.gsent r j m) r
      = toRoundUpd P u w r j sr
          (Function.update (w.sent r) j (insert m (w.sent r j))) := by
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, toRound, toRoundUpd, stage_update_self rfl, locals_toProc_if]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga1, toRound, toRoundUpd, toGa1, stage_update_self rfl,
      locals_view1_if]
    · simp only [Gather.ga, GBCA.ga1, toRound, toRoundUpd, toGa1, gsent_sent_self]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga1, toRound, toRoundUpd, toGa1, stage_update_self rfl,
      locals_in1_if]
    · simp only [Gather.brbIn, GBCA.ga1, toRound, toRoundUpd, toGa1, gsent_sent_self]
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga1, toRound, toRoundUpd, toGa1,
      stage_update_self rfl, locals_bind1_if]
    · simp only [Gather.brbBind, GBCA.ga1, toRound, toRoundUpd, toGa1, gsent_sent_self]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga2, toRound, toRoundUpd, toGa2, stage_update_self rfl,
      locals_view2_if]
    · simp only [Gather.ga, GBCA.ga2, toRound, toRoundUpd, toGa2, gsent_sent_self]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga2, toRound, toRoundUpd, toGa2, stage_update_self rfl,
      locals_in2_if]
    · simp only [Gather.brbIn, GBCA.ga2, toRound, toRoundUpd, toGa2, gsent_sent_self]
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga2, toRound, toRoundUpd, toGa2,
      stage_update_self rfl, locals_bind2_if]
    · simp only [Gather.brbBind, GBCA.ga2, toRound, toRoundUpd, toGa2, gsent_sent_self]

/-- A write that records nothing — a delivery, or a return — read through the
view. -/
theorem toRound_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) :
    toRound P (Function.update u j (c, (u j).2.setStage r sr)) w r
      = toRoundUpd P u w r j sr (w.sent r) := by
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, toRound, toRoundUpd, stage_update_self rfl, locals_toProc_if]
  · refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.ga, GBCA.ga1, toRound, toRoundUpd, toGa1, stage_update_self rfl,
      locals_view1_if]
  · funext k
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.brbIn, GBCA.ga1, toRound, toRoundUpd, toGa1, stage_update_self rfl,
      locals_in1_if]
  · funext q
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.brbBind, GBCA.ga1, toRound, toRoundUpd, toGa1, stage_update_self rfl,
      locals_bind1_if]
  · refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.ga, GBCA.ga2, toRound, toRoundUpd, toGa2, stage_update_self rfl,
      locals_view2_if]
  · funext k
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.brbIn, GBCA.ga2, toRound, toRoundUpd, toGa2, stage_update_self rfl,
      locals_in2_if]
  · funext q
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.brbBind, GBCA.ga2, toRound, toRoundUpd, toGa2, stage_update_self rfl,
      locals_bind2_if]

end Frame

/-! ### The store under a local write

`storeIn` counts `VOTE` receipts, so a write of a local record leaves it where
it stands and a delivery is the only row that moves it. -/

section Store

variable {X : Type} [DecidableEq X]

/-- A local record write leaves the store where it stands. -/
theorem storeIn_setP (q : LocalState P.n (BRB.PState X) (BRB.BMsg X))
    (pr : BRB.PState X) : storeIn P (q.setP pr) = storeIn P q := rfl

/-- The local record of a written local state. -/
theorem localState_setP_proc {Pr M : Type} (q : LocalState P.n Pr M) (pr : Pr) :
    (q.setP pr).proc = pr := rfl

/-- The delivered sets of a written local state. -/
theorem localState_setP_recv {Pr M : Type} (q : LocalState P.n Pr M) (pr : Pr) :
    (q.setP pr).recv = q.recv := rfl

/-- The store reads the delivered sets alone. -/
theorem storeIn_mk_eq (pr : BRB.PState X)
    (q : LocalState P.n (BRB.PState X) (BRB.BMsg X)) :
    storeIn P ({ proc := pr, recv := q.recv } : LocalState P.n (BRB.PState X) (BRB.BMsg X))
      = storeIn P q := rfl

/-- A local record write in one instance leaves the whole store family where it
stands. -/
theorem storeIn_update_setP (b : Fin P.n → LocalState P.n (BRB.PState X) (BRB.BMsg X))
    (i : Fin P.n) (pr : BRB.PState X) :
    (fun k => storeIn P (Function.update b i ((b i).setP pr) k))
      = fun k => storeIn P (b k) := by
  funext k
  by_cases hk : k = i
  · subst hk; rw [Function.update_self, storeIn_setP]
  · rw [Function.update_of_ne hk]

/-- A delivery in one instance, read through the store family. -/
theorem storeIn_update_deliverTo (b : Fin P.n → LocalState P.n (BRB.PState X) (BRB.BMsg X))
    (i k : Fin P.n) (m : BRB.BMsg X) :
    (fun k' => storeIn P (Function.update b i ((b i).deliverTo k m) k'))
      = Function.update (fun k' => storeIn P (b k')) i (storeIn P ((b i).deliverTo k m)) := by
  funext k'
  by_cases hk : k' = i
  · subst hk; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

/-- A delivery that leaves the store where it stands, read through the return
flag. -/
theorem brbLocal_deliverTo (q : LocalState P.n (BRB.PState X) (BRB.BMsg X)) (k : Fin P.n)
    (m : BRB.BMsg X) (h : storeIn P (q.deliverTo k m) = storeIn P q) :
    brbLocal P (q.deliverTo k m) = (brbLocal P q).deliverTo k m := by
  unfold brbLocal
  rw [h]
  rfl

/-- A delivery that completes a receipt quorum, read through the return flag:
the flag goes on. -/
theorem brbLocal_deliverTo_ret (q : LocalState P.n (BRB.PState X) (BRB.BMsg X))
    (k : Fin P.n) (m : BRB.BMsg X) {v : X} (h : storeIn P (q.deliverTo k m) = some v) :
    brbLocal P (q.deliverTo k m)
      = ((brbLocal P q).deliverTo k m).setP
          { ((brbLocal P q).deliverTo k m).proc with returned := true } := by
  unfold brbLocal LocalState.setP
  rw [h]
  rfl

end Store

/-! ### Reading the written view

The written view is read coordinate by coordinate, so that a row's remaining
obligations are stated over one local state vector or one network state at a
time. -/

section UpdReaders

variable (v : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n) (r : ℕ) (j : Fin P.n)
    (sr : StageRec P.n) (sent : Fin P.n → Finset (Msg P.n))

@[simp] theorem procs_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ProcRec P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.procs (((a, bnd), (x, y)) : GBCA.RoundStateAt P.n G₁ G₂) = a := rfl

@[simp] theorem bound_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ProcRec P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.bound (((a, bnd), (x, y)) : GBCA.RoundStateAt P.n G₁ G₂) = bnd := rfl

@[simp] theorem ga1_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ProcRec P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ga1 (((a, bnd), (x, y)) : GBCA.RoundStateAt P.n G₁ G₂) = x := rfl

@[simp] theorem ga2_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ProcRec P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ga2 (((a, bnd), (x, y)) : GBCA.RoundStateAt P.n G₁ G₂) = y := rfl

@[simp] theorem ga_toGa1_fst :
    (Gather.ga (toGa1 P v w r)).1
      = fun i => gaProcView P Bool ((v i).2.stage r).ga1 ((v i).2.stage r).brbIn1
          ((v i).2.stage r).brbBind1 := rfl

@[simp] theorem ga_toGa2_fst :
    (Gather.ga (toGa2 P v w r)).1
      = fun i => gaProcView P (Option Bool) ((v i).2.stage r).ga2 ((v i).2.stage r).brbIn2
          ((v i).2.stage r).brbBind2 := rfl

@[simp] theorem procs_toRound_eq :
    GBCA.procs (toRound P v w r) = fun i => toProc ((v i).2.stage r) := rfl

@[simp] theorem procs_toRoundUpd :
    GBCA.procs (toRoundUpd P v w r j sr sent)
      = Function.update (fun i => toProc ((v i).2.stage r)) j (toProc sr) := rfl

@[simp] theorem bound_toRoundUpd :
    GBCA.bound (toRoundUpd P v w r j sr sent) = (w.ghostRec r).2.2 := rfl

@[simp] theorem core_ga1_toRoundUpd :
    Gather.core (GBCA.ga1 (toRoundUpd P v w r j sr sent)) = (w.ghostRec r).1 := rfl

@[simp] theorem core_ga2_toRoundUpd :
    Gather.core (GBCA.ga2 (toRoundUpd P v w r j sr sent)) = (w.ghostRec r).2.1 := rfl

@[simp] theorem ga_ga1_toRoundUpd :
    Gather.ga (GBCA.ga1 (toRoundUpd P v w r j sr sent))
      = (Function.update (fun i => gaProcView P Bool ((v i).2.stage r).ga1
            ((v i).2.stage r).brbIn1 ((v i).2.stage r).brbBind1) j
          (gaProcView P Bool sr.ga1 sr.brbIn1 sr.brbBind1),
        ⟨slice unGa1 unGa1_inj sent, w.F⟩) := rfl

@[simp] theorem ga_ga2_toRoundUpd :
    Gather.ga (GBCA.ga2 (toRoundUpd P v w r j sr sent))
      = (Function.update (fun i => gaProcView P (Option Bool) ((v i).2.stage r).ga2
            ((v i).2.stage r).brbIn2 ((v i).2.stage r).brbBind2) j
          (gaProcView P (Option Bool) sr.ga2 sr.brbIn2 sr.brbBind2),
        ⟨slice unGa2 unGa2_inj sent, w.F⟩) := rfl

@[simp] theorem brbIn_ga1_toRoundUpd (k : Fin P.n) :
    Gather.brbIn (GBCA.ga1 (toRoundUpd P v w r j sr sent)) k
      = (Function.update (fun i => brbLocal P (((v i).2.stage r).brbIn1 k)) j
          (brbLocal P (sr.brbIn1 k)), ⟨slice (unIn1 k) (unIn1_inj k) sent, w.F⟩) := rfl

@[simp] theorem brbBind_ga1_toRoundUpd (q : Fin P.n) :
    Gather.brbBind (GBCA.ga1 (toRoundUpd P v w r j sr sent)) q
      = (Function.update (fun i => brbLocal P (((v i).2.stage r).brbBind1 q)) j
          (brbLocal P (sr.brbBind1 q)), ⟨slice (unBind1 q) (unBind1_inj q) sent, w.F⟩) := rfl

@[simp] theorem brbIn_ga2_toRoundUpd (k : Fin P.n) :
    Gather.brbIn (GBCA.ga2 (toRoundUpd P v w r j sr sent)) k
      = (Function.update (fun i => brbLocal P (((v i).2.stage r).brbIn2 k)) j
          (brbLocal P (sr.brbIn2 k)), ⟨slice (unIn2 k) (unIn2_inj k) sent, w.F⟩) := rfl

@[simp] theorem brbBind_ga2_toRoundUpd (q : Fin P.n) :
    Gather.brbBind (GBCA.ga2 (toRoundUpd P v w r j sr sent)) q
      = (Function.update (fun i => brbLocal P (((v i).2.stage r).brbBind2 q)) j
          (brbLocal P (sr.brbBind2 q)), ⟨slice (unBind2 q) (unBind2_inj q) sent, w.F⟩) := rfl

end UpdReaders

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w : NetState P.n} {j : Fin P.n}
    {c : CoreRec P.n} {p : StageSideRec P.n}

/-! ### A send of a gather instance

A gather's `ECHO` and `VOTE` write the sender's gather record and record on the
gather's network state. Each is the gather's `snd` event, which
`Gather.LowStep.echo` and `Gather.LowStep.vote` write through
`Gather.setGa`. -/

/-- A send of the first gather, read through the view. -/
theorem toRound_ga1Send (hu : (u j).2 = p) (r : ℕ) (pr : Gather.PRec P.n Bool)
    (m : Gather.GaMsg P.n Bool) (hin : pr.input = ((p.stage r).ga1.proc).input) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with ga1 := (p.stage r).ga1.setP pr }))
      (w.gsent r j (.ga1 m)) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setGa (toGa1 P u w r)
            (((Gather.ga (toGa1 P u w r)).setProc j
                { pr with
                  delivIn := fun k => storeIn P ((p.stage r).brbIn1 k)
                  delivBind := fun q => storeIn P ((p.stage r).brbBind1 q) }).mcast j m)) := by
  rw [← hu] at hin ⊢
  rw [toRound_write]
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, GBCA.setGa1, toRound, toRoundUpd, toProc, LocalState.setP, hin]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, Gather.setGa, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd, toGa1,
      gaProcView, SubState.mcast, SubState.setProc, LocalState.setP]
    · simp only [Gather.ga, Gather.setGa, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd, toGa1,
      SubState.mcast, NetworkState.post]
      exact slice_post_some unGa1 unGa1_inj (w.sent r) j (.ga1 m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, Gather.setGa, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, Gather.setGa, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.ga1 m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, Gather.setGa, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd,
      toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, Gather.setGa, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd,
      toGa1]
      exact slice_post_none (unBind1 q) (unBind1_inj q) (w.sent r) j (.ga1 m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) j (.ga1 m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.ga1 m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unBind2 q) (unBind2_inj q) (w.sent r) j (.ga1 m) rfl

/-- A send of the second gather, read through the view. -/
theorem toRound_ga2Send (hu : (u j).2 = p) (r : ℕ) (pr : Gather.PRec P.n (Option Bool))
    (m : Gather.GaMsg P.n (Option Bool))
    (hin : pr.input = ((p.stage r).ga2.proc).input)
    (hret : pr.returned = ((p.stage r).ga2.proc).returned) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with ga2 := (p.stage r).ga2.setP pr }))
      (w.gsent r j (.ga2 m)) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setGa (toGa2 P u w r)
            (((Gather.ga (toGa2 P u w r)).setProc j
                { pr with
                  delivIn := fun k => storeIn P ((p.stage r).brbIn2 k)
                  delivBind := fun q => storeIn P ((p.stage r).brbBind2 q) }).mcast j m)) := by
  rw [← hu] at hin hret ⊢
  rw [toRound_write]
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, GBCA.setGa2, toRound, toRoundUpd, toProc, LocalState.setP, hin, hret]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) j (.ga2 m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.ga2 m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unBind1 q) (unBind1_inj q) (w.sent r) j (.ga2 m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, Gather.setGa, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd, toGa2,
      gaProcView, SubState.mcast, SubState.setProc, LocalState.setP]
    · simp only [Gather.ga, Gather.setGa, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd, toGa2,
      SubState.mcast, NetworkState.post]
      exact slice_post_some unGa2 unGa2_inj (w.sent r) j (.ga2 m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, Gather.setGa, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, Gather.setGa, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.ga2 m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, Gather.setGa, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd,
      toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, Gather.setGa, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd,
      toGa2]
      exact slice_post_none (unBind2 q) (unBind2_inj q) (w.sent r) j (.ga2 m) rfl

/-! ### A send in a broadcast instance

A Bracha row writes the sender's local state in one broadcast instance and
records on that instance's network state. Each is the instance's `snd` event,
which `BRB.ImplStep.echo`, `BRB.ImplStep.voteQuorum` and `BRB.ImplStep.voteAmp`
write, and the composed round reaches it through `Gather.setBrbIn` or
`Gather.setBrbBind`. The return flag the view supplies is the store's, which a
local write does not move.
-/

/-- A send in an input-broadcast instance of the first gather, read through the
view. -/
theorem toRound_in1Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState Bool) (m : BRB.BMsg Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn1 := Function.update (p.stage r).brbIn1 i
            (((p.stage r).brbIn1 i).setP pr) }))
      (w.gsent r j (.brbIn1 i m)) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbIn (toGa1 P u w r)
            (Function.update (Gather.brbIn (toGa1 P u w r)) i
              (((Gather.brbIn (toGa1 P u w r) i).setProc j
                  { pr with returned := (storeIn P ((p.stage r).brbIn1 i)).isSome }).mcast
                j m))) := by
  rw [← hu, toRound_write]
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, GBCA.setGa1, toRound, toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd,
      toGa1, gaProcView, storeIn_update_setP]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd, toGa1]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) j (.brbIn1 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_self, SubState.mcast, SubState.setProc, brbLocal,
        LocalState.setP, storeIn_mk_eq]
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_self, SubState.mcast, NetworkState.post]
        exact slice_post_some (unIn1 k) (unIn1_inj k) (w.sent r) j
          (.brbIn1 k m) m (by simp [unIn1])
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_self, SubState.mcast, SubState.setProc,
        NetworkState.post]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_of_ne hk]
        exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.brbIn1 i m)
          (by simp [unIn1, Ne.symm hk])
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
      toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, Gather.setBrbIn, GBCA.ga1, GBCA.setGa1, toRound,
      toRoundUpd, toGa1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.sent r) j (.brbIn1 i m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) j (.brbIn1 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.brbIn1 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.sent r) j (.brbIn1 i m) rfl

/-- A send in a bind-broadcast instance of the first gather, read through the
view. -/
theorem toRound_bind1Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState (Gather.APSet P.n Bool)) (m : BRB.BMsg (Gather.APSet P.n Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind1 := Function.update (p.stage r).brbBind1 i
            (((p.stage r).brbBind1 i).setP pr) }))
      (w.gsent r j (.brbBind1 i m)) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbBind (toGa1 P u w r)
            (Function.update (Gather.brbBind (toGa1 P u w r)) i
              (((Gather.brbBind (toGa1 P u w r) i).setProc j
                  { pr with returned := (storeIn P ((p.stage r).brbBind1 i)).isSome }).mcast
                j m))) := by
  rw [← hu, toRound_write]
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, GBCA.setGa1, toRound, toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd,
      toGa1, gaProcView, storeIn_update_setP]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound, toRoundUpd,
      toGa1]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) j (.brbBind1 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
      toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
      toRoundUpd, toGa1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.brbBind1 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_self, SubState.mcast, SubState.setProc, brbLocal,
        LocalState.setP, storeIn_mk_eq]
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_self, SubState.mcast, NetworkState.post]
        exact slice_post_some (unBind1 k) (unBind1_inj k) (w.sent r) j
          (.brbBind1 k m) m (by simp [unBind1])
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_self, SubState.mcast, SubState.setProc,
        NetworkState.post]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_of_ne hk]
        exact slice_post_none (unBind1 k) (unBind1_inj k) (w.sent r) j (.brbBind1 i m)
          (by simp [unBind1, Ne.symm hk])
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga1, GBCA.setGa1, toRound,
        toRoundUpd, toGa1, Function.update_of_ne hk]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) j (.brbBind1 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.brbBind1 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, GBCA.ga2, GBCA.setGa1, toRound, toRoundUpd, toGa2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.sent r) j (.brbBind1 i m) rfl

/-- A send in an input-broadcast instance of the second gather, read through
the view. -/
theorem toRound_in2Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState (Option Bool)) (m : BRB.BMsg (Option Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn2 := Function.update (p.stage r).brbIn2 i
            (((p.stage r).brbIn2 i).setP pr) }))
      (w.gsent r j (.brbIn2 i m)) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbIn (toGa2 P u w r)
            (Function.update (Gather.brbIn (toGa2 P u w r)) i
              (((Gather.brbIn (toGa2 P u w r) i).setProc j
                  { pr with returned := (storeIn P ((p.stage r).brbIn2 i)).isSome }).mcast
                j m))) := by
  rw [← hu, toRound_write]
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, GBCA.setGa2, toRound, toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) j (.brbIn2 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.brbIn2 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.sent r) j (.brbIn2 i m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd,
      toGa2, gaProcView, storeIn_update_setP]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd, toGa2]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) j (.brbIn2 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_self, SubState.mcast, SubState.setProc, brbLocal,
        LocalState.setP, storeIn_mk_eq]
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_self, SubState.mcast, NetworkState.post]
        exact slice_post_some (unIn2 k) (unIn2_inj k) (w.sent r) j
          (.brbIn2 k m) m (by simp [unIn2])
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_self, SubState.mcast, SubState.setProc,
        NetworkState.post]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_of_ne hk]
        exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.brbIn2 i m)
          (by simp [unIn2, Ne.symm hk])
      · simp only [Gather.brbIn, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
      toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, Gather.setBrbIn, GBCA.ga2, GBCA.setGa2, toRound,
      toRoundUpd, toGa2]
      exact slice_post_none (unBind2 k) (unBind2_inj k) (w.sent r) j (.brbIn2 i m) rfl

/-- A send in a bind-broadcast instance of the second gather, read through the
view. -/
theorem toRound_bind2Send (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.PState (Gather.APSet P.n (Option Bool)))
    (m : BRB.BMsg (Gather.APSet P.n (Option Bool))) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind2 := Function.update (p.stage r).brbBind2 i
            (((p.stage r).brbBind2 i).setP pr) }))
      (w.gsent r j (.brbBind2 i m)) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbBind (toGa2 P u w r)
            (Function.update (Gather.brbBind (toGa2 P u w r)) i
              (((Gather.brbBind (toGa2 P u w r) i).setProc j
                  { pr with returned := (storeIn P ((p.stage r).brbBind2 i)).isSome }).mcast
                j m))) := by
  rw [← hu, toRound_write]
  refine roundStateAt_ext ?_ rfl (subStateAt_ext ?_ ?_ ?_ rfl) (subStateAt_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.procs, GBCA.setGa2, toRound, toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) j (.brbBind2 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.brbBind2 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbBind, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbBind, GBCA.ga1, GBCA.setGa2, toRound, toRoundUpd, toGa1]
      exact slice_post_none (unBind1 k) (unBind1_inj k) (w.sent r) j (.brbBind2 i m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.ga, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd,
      toGa2, gaProcView, storeIn_update_setP]
      exact Function.update_eq_self _ _
    · simp only [Gather.ga, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound, toRoundUpd,
      toGa2]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) j (.brbBind2 i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.brbIn, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
      toRoundUpd, toGa2]
      exact Function.update_eq_self _ _
    · simp only [Gather.brbIn, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
      toRoundUpd, toGa2]
      exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.brbBind2 i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_self, SubState.mcast, SubState.setProc, brbLocal,
        LocalState.setP, storeIn_mk_eq]
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_self, SubState.mcast, NetworkState.post]
        exact slice_post_some (unBind2 k) (unBind2_inj k) (w.sent r) j
          (.brbBind2 k m) m (by simp [unBind2])
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_self, SubState.mcast, SubState.setProc,
        NetworkState.post]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_of_ne hk]
        exact slice_post_none (unBind2 k) (unBind2_inj k) (w.sent r) j (.brbBind2 i m)
          (by simp [unBind2, Ne.symm hk])
      · simp only [Gather.brbBind, Gather.setBrbBind, GBCA.ga2, GBCA.setGa2, toRound,
        toRoundUpd, toGa2, Function.update_of_ne hk]

/-! ### The rows of the two gathers and of the broadcast instances

Each row below is one flat row, read through the view over the effect the
composed round's own row writes. -/

/-- The first gather's `ECHO`, read through the view. -/
theorem toRound_ga1Echo (hu : (u j).2 = p) (r : ℕ) (A : Gather.APSet P.n Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga1 := (p.stage r).ga1.setP
            { ((p.stage r).ga1.proc) with sentEcho := some A } }))
      ((w.gsent r j (.ga1 (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.ga1 (.echo A))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setGa (toGa1 P u w r)
            (((Gather.ga (toGa1 P u w r)).setProc j
                { (Gather.ga (toGa1 P u w r)).proc j with sentEcho := some A }).mcast
              j (.echo A))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.ga1 (.echo A)))) (fun _ _ => rfl)]
  exact toRound_ga1Send rfl r _ (.echo A) rfl

/-- The first gather's `VOTE`, read through the view. -/
theorem toRound_ga1Vote (hu : (u j).2 = p) (r : ℕ) (U : Gather.APSet P.n Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga1 := (p.stage r).ga1.setP
            { ((p.stage r).ga1.proc) with sentVote := some U } }))
      ((w.gsent r j (.ga1 (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.ga1 (.vote U))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setGa (toGa1 P u w r)
            (((Gather.ga (toGa1 P u w r)).setProc j
                { (Gather.ga (toGa1 P u w r)).proc j with sentVote := some U }).mcast
              j (.vote U))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.ga1 (.vote U)))) (fun _ _ => rfl)]
  exact toRound_ga1Send rfl r _ (.vote U) rfl

/-- The second gather's `ECHO`, read through the view. -/
theorem toRound_ga2Echo (hu : (u j).2 = p) (r : ℕ) (A : Gather.APSet P.n (Option Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga2 := (p.stage r).ga2.setP
            { ((p.stage r).ga2.proc) with sentEcho := some A } }))
      ((w.gsent r j (.ga2 (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.ga2 (.echo A))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setGa (toGa2 P u w r)
            (((Gather.ga (toGa2 P u w r)).setProc j
                { (Gather.ga (toGa2 P u w r)).proc j with sentEcho := some A }).mcast
              j (.echo A))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.ga2 (.echo A)))) (fun _ _ => rfl)]
  exact toRound_ga2Send rfl r _ (.echo A) rfl rfl

/-- The second gather's `VOTE`, read through the view. -/
theorem toRound_ga2Vote (hu : (u j).2 = p) (r : ℕ) (U : Gather.APSet P.n (Option Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga2 := (p.stage r).ga2.setP
            { ((p.stage r).ga2.proc) with sentVote := some U } }))
      ((w.gsent r j (.ga2 (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.ga2 (.vote U))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setGa (toGa2 P u w r)
            (((Gather.ga (toGa2 P u w r)).setProc j
                { (Gather.ga (toGa2 P u w r)).proc j with sentVote := some U }).mcast
              j (.vote U))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.ga2 (.vote U)))) (fun _ _ => rfl)]
  exact toRound_ga2Send rfl r _ (.vote U) rfl rfl

/-- The first gather's `BIND`, read through the view: the payload is the input
of the sender's own bind-broadcast instance, which broadcasts it. -/
theorem toRound_ga1Bind (hu : (u j).2 = p) (r : ℕ) (U : Gather.APSet P.n Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind1 := Function.update (p.stage r).brbBind1 j
            (((p.stage r).brbBind1 j).setP
              { (((p.stage r).brbBind1 j).proc) with input := some U }) }))
      ((w.gsent r j (.brbBind1 j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbBind1 j (.init U))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbBind (toGa1 P u w r)
            (Function.update (Gather.brbBind (toGa1 P u w r)) j
              (((Gather.brbBind (toGa1 P u w r) j).setProc j
                  { (Gather.brbBind (toGa1 P u w r) j).proc j with input := some U }).mcast
                j (.init U)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbBind1 j (.init U)))) (fun _ _ => rfl)]
  exact toRound_bind1Send rfl r j _ (.init U)

/-- The second gather's `BIND`, read through the view. -/
theorem toRound_ga2Bind (hu : (u j).2 = p) (r : ℕ) (U : Gather.APSet P.n (Option Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind2 := Function.update (p.stage r).brbBind2 j
            (((p.stage r).brbBind2 j).setP
              { (((p.stage r).brbBind2 j).proc) with input := some U }) }))
      ((w.gsent r j (.brbBind2 j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbBind2 j (.init U))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbBind (toGa2 P u w r)
            (Function.update (Gather.brbBind (toGa2 P u w r)) j
              (((Gather.brbBind (toGa2 P u w r) j).setProc j
                  { (Gather.brbBind (toGa2 P u w r) j).proc j with input := some U }).mcast
                j (.init U)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbBind2 j (.init U)))) (fun _ _ => rfl)]
  exact toRound_bind2Send rfl r j _ (.init U)

/-- `ECHO` in an input-broadcast instance of the first gather, read through the
view. -/
theorem toRound_in1Echo (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n) (m : Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn1 := Function.update (p.stage r).brbIn1 i
            (((p.stage r).brbIn1 i).setP
              { (((p.stage r).brbIn1 i).proc) with sentEcho := some m }) }))
      ((w.gsent r j (.brbIn1 i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbIn1 i (.echo m))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbIn (toGa1 P u w r)
            (Function.update (Gather.brbIn (toGa1 P u w r)) i
              (((Gather.brbIn (toGa1 P u w r) i).setProc j
                  { (Gather.brbIn (toGa1 P u w r) i).proc j with sentEcho := some m }).mcast
                j (.echo m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbIn1 i (.echo m)))) (fun _ _ => rfl)]
  exact toRound_in1Send rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the first gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem toRound_in1Vote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n) (m : Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn1 := Function.update (p.stage r).brbIn1 i
            (((p.stage r).brbIn1 i).setP
              { (((p.stage r).brbIn1 i).proc) with sentVote := some m }) }))
      ((w.gsent r j (.brbIn1 i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbIn1 i (.vote m))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbIn (toGa1 P u w r)
            (Function.update (Gather.brbIn (toGa1 P u w r)) i
              (((Gather.brbIn (toGa1 P u w r) i).setProc j
                  { (Gather.brbIn (toGa1 P u w r) i).proc j with sentVote := some m }).mcast
                j (.vote m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbIn1 i (.vote m)))) (fun _ _ => rfl)]
  exact toRound_in1Send rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the first gather, read through the
view. -/
theorem toRound_bind1Echo (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n) (m : Gather.APSet P.n Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind1 := Function.update (p.stage r).brbBind1 i
            (((p.stage r).brbBind1 i).setP
              { (((p.stage r).brbBind1 i).proc) with sentEcho := some m }) }))
      ((w.gsent r j (.brbBind1 i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbBind1 i (.echo m))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbBind (toGa1 P u w r)
            (Function.update (Gather.brbBind (toGa1 P u w r)) i
              (((Gather.brbBind (toGa1 P u w r) i).setProc j
                  { (Gather.brbBind (toGa1 P u w r) i).proc j with sentEcho := some m }).mcast
                j (.echo m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbBind1 i (.echo m)))) (fun _ _ => rfl)]
  exact toRound_bind1Send rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the first gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem toRound_bind1Vote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n) (m : Gather.APSet P.n Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind1 := Function.update (p.stage r).brbBind1 i
            (((p.stage r).brbBind1 i).setP
              { (((p.stage r).brbBind1 i).proc) with sentVote := some m }) }))
      ((w.gsent r j (.brbBind1 i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbBind1 i (.vote m))))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbBind (toGa1 P u w r)
            (Function.update (Gather.brbBind (toGa1 P u w r)) i
              (((Gather.brbBind (toGa1 P u w r) i).setProc j
                  { (Gather.brbBind (toGa1 P u w r) i).proc j with sentVote := some m }).mcast
                j (.vote m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbBind1 i (.vote m)))) (fun _ _ => rfl)]
  exact toRound_bind1Send rfl r i _ (.vote m)

/-- `ECHO` in an input-broadcast instance of the second gather, read through
the view. -/
theorem toRound_in2Echo (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n) (m : Option Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn2 := Function.update (p.stage r).brbIn2 i
            (((p.stage r).brbIn2 i).setP
              { (((p.stage r).brbIn2 i).proc) with sentEcho := some m }) }))
      ((w.gsent r j (.brbIn2 i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbIn2 i (.echo m))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbIn (toGa2 P u w r)
            (Function.update (Gather.brbIn (toGa2 P u w r)) i
              (((Gather.brbIn (toGa2 P u w r) i).setProc j
                  { (Gather.brbIn (toGa2 P u w r) i).proc j with sentEcho := some m }).mcast
                j (.echo m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbIn2 i (.echo m)))) (fun _ _ => rfl)]
  exact toRound_in2Send rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the second gather, read through
the view. The quorum row and the amplification row write this record. -/
theorem toRound_in2Vote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n) (m : Option Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbIn2 := Function.update (p.stage r).brbIn2 i
            (((p.stage r).brbIn2 i).setP
              { (((p.stage r).brbIn2 i).proc) with sentVote := some m }) }))
      ((w.gsent r j (.brbIn2 i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbIn2 i (.vote m))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbIn (toGa2 P u w r)
            (Function.update (Gather.brbIn (toGa2 P u w r)) i
              (((Gather.brbIn (toGa2 P u w r) i).setProc j
                  { (Gather.brbIn (toGa2 P u w r) i).proc j with sentVote := some m }).mcast
                j (.vote m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbIn2 i (.vote m)))) (fun _ _ => rfl)]
  exact toRound_in2Send rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the second gather, read through the
view. -/
theorem toRound_bind2Echo (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.APSet P.n (Option Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind2 := Function.update (p.stage r).brbBind2 i
            (((p.stage r).brbBind2 i).setP
              { (((p.stage r).brbBind2 i).proc) with sentEcho := some m }) }))
      ((w.gsent r j (.brbBind2 i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbBind2 i (.echo m))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbBind (toGa2 P u w r)
            (Function.update (Gather.brbBind (toGa2 P u w r)) i
              (((Gather.brbBind (toGa2 P u w r) i).setProc j
                  { (Gather.brbBind (toGa2 P u w r) i).proc j with sentEcho := some m }).mcast
                j (.echo m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbBind2 i (.echo m)))) (fun _ _ => rfl)]
  exact toRound_bind2Send rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the second gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem toRound_bind2Vote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.APSet P.n (Option Bool)) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          brbBind2 := Function.update (p.stage r).brbBind2 i
            (((p.stage r).brbBind2 i).setP
              { (((p.stage r).brbBind2 i).proc) with sentVote := some m }) }))
      ((w.gsent r j (.brbBind2 i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbBind2 i (.vote m))))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbBind (toGa2 P u w r)
            (Function.update (Gather.brbBind (toGa2 P u w r)) i
              (((Gather.brbBind (toGa2 P u w r) i).setProc j
                  { (Gather.brbBind (toGa2 P u w r) i).proc j with sentVote := some m }).mcast
                j (.vote m)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gsnd r j (.brbBind2 i (.vote m)))) (fun _ _ => rfl)]
  exact toRound_bind2Send rfl r i _ (.vote m)

/-! ### The graded-agreement call and its loop

The call is fused (D28): the round's first gather records the input and the
caller's own input-broadcast instance of that gather is called with it. The
composed round answers on one label, whose program row records the input and
whose first gather takes `Gather.LowStep.call`. The call against an
already-called record moves the round loop alone, which the view does not
read. -/

/-- The graded-agreement call, read through the view. -/
theorem toRound_callG (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga1 := (p.stage r).ga1.setP
            { ((p.stage r).ga1.proc) with input := some b }
          brbIn1 := Function.update (p.stage r).brbIn1 j
            (((p.stage r).brbIn1 j).setP
              { (((p.stage r).brbIn1 j).proc) with input := some b }) }))
      ((w.gsent r j (.brbIn1 j (.init b))).writeGhost (ghostStep P)
        (Sum.inl (.callG r j b))) r
      = GBCA.setGa1 (GBCA.setProcs (toRound P u w r)
            (Function.update (GBCA.procs (toRound P u w r)) j
              { GBCA.procs (toRound P u w r) j with input := some b }))
          (Gather.setBrbIn (Gather.setGa (toGa1 P u w r)
              ((Gather.ga (toGa1 P u w r)).setProc j
                { (Gather.ga (toGa1 P u w r)).proc j with input := some b }))
            (Function.update (Gather.brbIn (toGa1 P u w r)) j
              (((Gather.brbIn (toGa1 P u w r) j).setProc j
                  { (Gather.brbIn (toGa1 P u w r) j).proc j with
                    input := some b }).mcast j (.init b)))) := by
  subst hu
  rw [toRound_ghostId (Sum.inl (.callG r j b)) (fun _ _ => rfl), toRound_write]
  refine roundStateAt_ext ?_ ?_ (subStateAt_ext ?_ ?_ ?_ ?_) (subStateAt_ext ?_ ?_ ?_ ?_)
  · simp only [procs_toRoundUpd, GBCA.procs_setGa1, GBCA.procs_setProcs, procs_toRound_eq]
    refine congrArg (Function.update (fun i => toProc ((u i).2.stage r)) j) ?_
    simp only [toProc, LocalState.setP]
  · simp
  · simp only [ga_ga1_toRoundUpd, GBCA.ga1_setGa1, Gather.ga_setBrbIn, Gather.ga_setGa]
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [SubState.setProc]
      refine congrArg (Function.update
        (fun i => gaProcView P Bool ((u i).2.stage r).ga1 ((u i).2.stage r).brbIn1
          ((u i).2.stage r).brbBind1) j) ?_
      simp only [gaProcView, storeIn_update_setP, SubState.proc, ga_toGa1_proc,
        localState_setP_proc, localState_setP_recv]
      simp only [LocalState.setP]
    · exact slice_post_none unGa1 unGa1_inj (w.sent r) j (.brbIn1 j (.init b)) rfl
  · funext k
    simp only [brbIn_ga1_toRoundUpd, GBCA.ga1_setGa1, Gather.brbIn_setBrbIn, brbIn_toGa1]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [SubState.mcast, SubState.setProc]
        refine congrArg (Function.update
          (fun i => brbLocal P (((u i).2.stage r).brbIn1 k)) k) ?_
        simp only [SubState.proc, brbLocal, LocalState.setP, storeIn_mk_eq]
      · simp only [SubState.mcast, NetworkState.post]
        exact slice_post_some (unIn1 k) (unIn1_inj k) (w.sent r) k
          (.brbIn1 k (.init b)) (.init b) (by simp [unIn1])
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j (.brbIn1 j (.init b))
        (by simp [unIn1, Ne.symm hk])
  · funext q
    simp only [brbBind_ga1_toRoundUpd, GBCA.ga1_setGa1, Gather.brbBind_setBrbIn,
      Gather.brbBind_setGa, brbBind_toGa1]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact slice_post_none (unBind1 q) (unBind1_inj q) (w.sent r) j (.brbIn1 j (.init b)) rfl
  · simp
  · simp only [ga_ga2_toRoundUpd, GBCA.ga2_setGa1, GBCA.ga2_setProcs, ga2_toRound]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact slice_post_none unGa2 unGa2_inj (w.sent r) j (.brbIn1 j (.init b)) rfl
  · funext k
    simp only [brbIn_ga2_toRoundUpd, GBCA.ga2_setGa1, GBCA.ga2_setProcs, ga2_toRound,
      brbIn_toGa2]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j (.brbIn1 j (.init b)) rfl
  · funext q
    simp only [brbBind_ga2_toRoundUpd, GBCA.ga2_setGa1, GBCA.ga2_setProcs, ga2_toRound,
      brbBind_toGa2]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact slice_post_none (unBind2 q) (unBind2_inj q) (w.sent r) j (.brbIn1 j (.init b)) rfl
  · simp

/-- The graded-agreement call against an already-called record, read through
the view: the round loop moves and the view stands still. -/
theorem toRound_gcallLoop (hu : (u j).2 = p) (r r' : ℕ) (b : Bool) (c' : CoreRec P.n) :
    toRound P (Function.update u j (c', p))
        (w.writeGhost (ghostStep P) (Sum.inr (.gcallLoop r j b))) r'
      = toRound P u w r' := by
  rw [toRound_ghostId (Sum.inr (.gcallLoop r j b)) (fun _ _ => rfl)]
  refine toRound_congr (fun i => ?_)
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, ← hu]
  · rw [Function.update_of_ne hi]

/-! ### The link and the graded return

The link is answered by two events, `ret1` and `call2`; the graded return by
`ret2` and `retG`. Each pair is stated as one equation with the two effects
composed, and the state between them is named so that a run can be built
through it. -/

/-- The view of one gather instance after a write. -/
theorem toGa1_write (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) (m : Msg P.n) :
    toGa1 P (Function.update u j (c, (u j).2.setStage r sr)) (w.gsent r j m) r
      = GBCA.ga1 (toRoundUpd P u w r j sr
          (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ga1 (toRound_write u w j c r sr m)

/-- The same at the second gather instance. -/
theorem toGa2_write (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) (m : Msg P.n) :
    toGa2 P (Function.update u j (c, (u j).2.setStage r sr)) (w.gsent r j m) r
      = GBCA.ga2 (toRoundUpd P u w r j sr
          (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ga2 (toRound_write u w j c r sr m)

/-- The core the first gather's return carries: the one on record, and the core
of the gather's network state where none is on record. -/
noncomputable def ret1Core (P : Params) (s : GBCA.LowPairState P.n) :
    Gather.APSet P.n Bool :=
  (Gather.core (GBCA.ga1 s)).getD (Gather.coreOfNet P (Gather.ga (GBCA.ga1 s)).2)

/-- The core the second gather's return carries. -/
noncomputable def ret2Core (P : Params) (s : GBCA.LowPairState P.n) :
    Gather.APSet P.n (Option Bool) :=
  (Gather.core (GBCA.ga2 s)).getD (Gather.coreOfNet P (Gather.ga (GBCA.ga2 s)).2)

/-- **The round after the first gather's return to `j` over `g`**: the program
records the candidate, the round's bound bit is written from the core the
return carries, and the first gather takes `Gather.LowStep.ret`. -/
noncomputable def afterRet1 (P : Params) (s : GBCA.LowPairState P.n) (j : Fin P.n)
    (g : Fin P.n → Option Bool) : GBCA.LowPairState P.n :=
  GBCA.setGa1
    (GBCA.setBound
      (GBCA.setProcs s (Function.update (GBCA.procs s) j
        { GBCA.procs s j with cand := some (GBCA.cand P g) }))
      (some ((GBCA.bound s).getD (GBCA.boundOfCore P (ret1Core P s)))))
    (Gather.setCore
      (Gather.setGa (GBCA.ga1 s)
        ((Gather.ga (GBCA.ga1 s)).setProc j
          { (Gather.ga (GBCA.ga1 s)).proc j with returned := true }))
      (some (ret1Core P s)))

/-- **The round after `j`'s call of the second gather with `x`**: the program
marks the call and the second gather takes `Gather.LowStep.call`. -/
noncomputable def afterCall2 (P : Params) (s : GBCA.LowPairState P.n) (j : Fin P.n)
    (x : Option Bool) : GBCA.LowPairState P.n :=
  GBCA.setGa2
    (GBCA.setProcs s (Function.update (GBCA.procs s) j
      { GBCA.procs s j with called2 := true }))
    (Gather.setBrbIn
      (Gather.setGa (GBCA.ga2 s)
        ((Gather.ga (GBCA.ga2 s)).setProc j
          { (Gather.ga (GBCA.ga2 s)).proc j with input := some x }))
      (Function.update (Gather.brbIn (GBCA.ga2 s)) j
        (((Gather.brbIn (GBCA.ga2 s) j).setProc j
            { (Gather.brbIn (GBCA.ga2 s) j).proc j with input := some x }).mcast
          j (.init x))))

/-- **The round after the second gather's return to `j` over `g`**: the program
records the grade and the second gather takes `Gather.LowStep.ret`. -/
noncomputable def afterRet2 (P : Params) (s : GBCA.LowPairState P.n) (j : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) : GBCA.LowPairState P.n :=
  GBCA.setGa2
    (GBCA.setProcs s (Function.update (GBCA.procs s) j
      { GBCA.procs s j with out := some (GBCA.gradeOf P g) }))
    (Gather.setCore
      (Gather.setGa (GBCA.ga2 s)
        ((Gather.ga (GBCA.ga2 s)).setProc j
          { (Gather.ga (GBCA.ga2 s)).proc j with returned := true }))
      (some (ret2Core P s)))

/-- **The round after its graded return to `j`**: the program announces the
grade and marks the record returned. -/
def afterRetG (P : Params) (s : GBCA.LowPairState P.n) (j : Fin P.n) :
    GBCA.LowPairState P.n :=
  GBCA.setProcs s (Function.update (GBCA.procs s) j
    { GBCA.procs s j with out := none, returned := true })

/-- **The link, read through the view.** The first gather returns to `j`, which
records the candidate and calls the second gather with it; the round's
bound bit is written from the core the return carries. -/
theorem toRound_ret1_call2 (hu : (u j).2 = p) (r : ℕ) (g : Fin P.n → Option Bool) :
    toRound P (Function.update u j (c, p.setStage r
        { p.stage r with
          ga1 := (p.stage r).ga1.setP
            { ((p.stage r).ga1.proc) with returned := true }
          ga2 := (p.stage r).ga2.setP
            { ((p.stage r).ga2.proc) with input := some (GBCA.cand P g) }
          brbIn2 := Function.update (p.stage r).brbIn2 j
            (((p.stage r).brbIn2 j).setP
              { (((p.stage r).brbIn2 j).proc) with
                input := some (GBCA.cand P g) }) }))
      ((w.gsent r j (.brbIn2 j (.init (GBCA.cand P g)))).writeGhost (ghostStep P)
        (Sum.inr (.gsnd r j (.brbIn2 j (.init (GBCA.cand P g)))))) r
      = afterCall2 P (afterRet1 P (toRound P u w r) j g) j (GBCA.cand P g) := by
  subst hu
  have hcore : Gather.coreOf P
      (ga1Of P (w.gsent r j (.brbIn2 j (.init (GBCA.cand P g)))) r)
      = Gather.coreOfNet P (Gather.ga (toGa1 P u w r)).2 := by
    rw [coreOfNet_toGa1]
    refine Gather.coreOf_networkState_only _ _ (networkState_ext ?_ rfl)
    simp only [ga1Of, gsent_sent_self]
    exact slice_post_none unGa1 unGa1_inj (w.sent r) j
      (.brbIn2 j (.init (GBCA.cand P g))) rfl
  rw [toRound_gsndGhost, toGa1_write, toGa2_write]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterCall2, afterRet1, GBCA.procs_setGa2, GBCA.procs_setProcs,
    GBCA.procs_setGa1, GBCA.procs_setBound, procs_toRound_eq, Function.update_idem,
    stage_update_self rfl, locals_toProc_if, Function.update_self]
    simp only [procs_mk, toProc, LocalState.setP, Option.isSome_some]
  · simp only [afterCall2, afterRet1, GBCA.bound_setGa2, GBCA.bound_setProcs,
    GBCA.bound_setGa1, GBCA.bound_setBound, bound_toRound, ret1Core, ga1_toRound, core_toGa1]
    simp only [bound_mk, ghostStep, hcore]
  · simp only [afterCall2, afterRet1, GBCA.ga1_setGa2, GBCA.ga1_setProcs, GBCA.ga1_setGa1,
    ga1_toRound]
    simp only [ga1_mk]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [Gather.ga_setCore, ga_ga1_toRoundUpd, Gather.ga_setGa]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [SubState.setProc]
        refine congrArg (Function.update
          (fun i => gaProcView P Bool ((u i).2.stage r).ga1 ((u i).2.stage r).brbIn1
            ((u i).2.stage r).brbBind1) j) ?_
        simp only [gaProcView, SubState.proc, ga_toGa1_proc, localState_setP_proc,
          localState_setP_recv]
        simp only [LocalState.setP]
      · exact slice_post_none unGa1 unGa1_inj (w.sent r) j
          (.brbIn2 j (.init (GBCA.cand P g))) rfl
    · funext k
      simp only [Gather.brbIn_setCore, brbIn_ga1_toRoundUpd, Gather.brbIn_setGa, brbIn_toGa1]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k) (unIn1_inj k) (w.sent r) j
        (.brbIn2 j (.init (GBCA.cand P g))) rfl
    · funext q
      simp only [Gather.brbBind_setCore, brbBind_ga1_toRoundUpd, Gather.brbBind_setGa,
        brbBind_toGa1]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact slice_post_none (unBind1 q) (unBind1_inj q) (w.sent r) j
        (.brbIn2 j (.init (GBCA.cand P g))) rfl
    · simp only [Gather.core_setCore, ret1Core, ga1_toRound, core_toGa1]
      simp only [ghostStep, hcore]
  · simp only [afterCall2, afterRet1, GBCA.ga2_setGa2, GBCA.ga2_setProcs, GBCA.ga2_setBound,
    GBCA.ga2_setGa1, ga2_toRound]
    simp only [ga2_mk]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [Gather.ga_setCore, Gather.ga_setBrbIn, Gather.ga_setGa]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [SubState.setProc]
        refine congrArg (Function.update
          (fun i => gaProcView P (Option Bool) ((u i).2.stage r).ga2 ((u i).2.stage r).brbIn2
            ((u i).2.stage r).brbBind2) j) ?_
        simp only [gaProcView, storeIn_update_setP, SubState.proc, ga_toGa2_proc,
          localState_setP_proc, localState_setP_recv]
        simp only [LocalState.setP]
      · exact slice_post_none unGa2 unGa2_inj (w.sent r) j
          (.brbIn2 j (.init (GBCA.cand P g))) rfl
    · funext k
      simp only [Gather.brbIn_setCore, Gather.brbIn_setBrbIn, brbIn_ga2_toRoundUpd, brbIn_toGa2]
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        refine Prod.ext ?_ (networkState_ext ?_ rfl)
        · simp only [SubState.mcast, SubState.setProc]
          refine congrArg (Function.update
            (fun i => brbLocal P (((u i).2.stage r).brbIn2 k)) k) ?_
          simp only [SubState.proc, brbLocal, LocalState.setP, storeIn_mk_eq]
        · simp only [SubState.mcast, NetworkState.post]
          exact slice_post_some (unIn2 k) (unIn2_inj k) (w.sent r) k
            (.brbIn2 k (.init (GBCA.cand P g))) (.init (GBCA.cand P g)) (by simp [unIn2])
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
        exact slice_post_none (unIn2 k) (unIn2_inj k) (w.sent r) j
          (.brbIn2 j (.init (GBCA.cand P g))) (by simp [unIn2, Ne.symm hk])
    · funext q
      simp only [Gather.brbBind_setCore, Gather.brbBind_setBrbIn, Gather.brbBind_setGa,
        brbBind_ga2_toRoundUpd, brbBind_toGa2]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact slice_post_none (unBind2 q) (unBind2_inj q) (w.sent r) j
        (.brbIn2 j (.init (GBCA.cand P g))) rfl
    · simp only [Gather.core_setCore, Gather.core_setBrbIn, Gather.core_setGa, core_toGa2]
      simp only [ghostStep]

/-- The view of the first gather instance after a write that records
nothing. -/
theorem toGa1_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) :
    toGa1 P (Function.update u j (c, (u j).2.setStage r sr)) w r
      = GBCA.ga1 (toRoundUpd P u w r j sr (w.sent r)) :=
  congrArg GBCA.ga1 (toRound_writeNoSent u w j c r sr)

/-- The same at the second gather instance. -/
theorem toGa2_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (j : Fin P.n) (c : CoreRec P.n) (r : ℕ) (sr : StageRec P.n) :
    toGa2 P (Function.update u j (c, (u j).2.setStage r sr)) w r
      = GBCA.ga2 (toRoundUpd P u w r j sr (w.sent r)) :=
  congrArg GBCA.ga2 (toRound_writeNoSent u w j c r sr)

/-- **The graded return, read through the view.** The second gather returns to
`j`, which records the grade and announces it; the round's return clears the
record and marks it returned. -/
theorem toRound_ret2_retG (hu : (u j).2 = p) (r : ℕ)
    (g : Fin P.n → Option (Option Bool)) (c' : CoreRec P.n) (bnd : Bool) :
    toRound P (Function.update u j (c', p.setStage r
        { p.stage r with
          ga2 := (p.stage r).ga2.setP
            { ((p.stage r).ga2.proc) with returned := true } }))
      (w.writeGhost (ghostStep P) (Sum.inl (.retG r j (GBCA.gradeOf P g) bnd))) r
      = afterRetG P (afterRet2 P (toRound P u w r) j g) j := by
  subst hu
  rw [toRound_writeGhost _ _ (rfl : roundOf (Sum.inl
      (Lab.retG r j (GBCA.gradeOf P g) bnd)) = some r),
    toGa1_writeNoSent, toGa2_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterRetG, afterRet2, GBCA.procs_setProcs, GBCA.procs_setGa2,
    procs_toRound_eq, Function.update_idem, Function.update_self, stage_update_self rfl,
    locals_toProc_if]
    simp only [procs_mk, toProc, LocalState.setP]
  · simp only [afterRetG, afterRet2, GBCA.bound_setProcs, GBCA.bound_setGa2, bound_toRound]
    simp only [bound_mk, ghostStep]
  · simp only [afterRetG, afterRet2, GBCA.ga1_setProcs, GBCA.ga1_setGa2, ga1_toRound]
    simp only [ga1_mk, ghostStep]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [Gather.ga_setCore, ga_ga1_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [Gather.brbIn_setCore, brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.brbBind_setCore, brbBind_ga1_toRoundUpd, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, core_toGa1]
  · simp only [afterRetG, afterRet2, GBCA.ga2_setProcs, GBCA.ga2_setGa2, ga2_toRound]
    simp only [ga2_mk, ghostStep]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [Gather.ga_setCore, Gather.ga_setGa, ga_ga2_toRoundUpd]
      refine Prod.ext ?_ rfl
      simp only [SubState.setProc]
      refine congrArg (Function.update
        (fun i => gaProcView P (Option Bool) ((u i).2.stage r).ga2 ((u i).2.stage r).brbIn2
          ((u i).2.stage r).brbBind2) j) ?_
      simp only [gaProcView, SubState.proc, ga_toGa2_proc, localState_setP_proc,
        localState_setP_recv]
      simp only [LocalState.setP]
    · funext k
      simp only [Gather.brbIn_setCore, Gather.brbIn_setGa, brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.brbBind_setCore, Gather.brbBind_setGa, brbBind_ga2_toRoundUpd,
        brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, ret2Core, ga2_toRound, core_toGa2, coreOfNet_toGa2]

/-! ### A delivery

A delivery of the flat reading files the message in the receiver's own local
state of the network state the message's tag names. A gather message moves the
gather instance alone. A broadcast message moves the broadcast instance, and,
where it completes an `n − f` `VOTE` quorum at the receiver, the instance
returns to the receiver as well: the return flag goes on and the receiver's
gather store records the value. -/

/-- A delivery on the first gather's network, read through the view. -/
theorem toRound_dlvGa1 (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.GaMsg P.n Bool) :
    toRound P (Function.update u j (c, p.deliverTo r k (.ga1 mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.ga1 mm)))) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setGa (toGa1 P u w r) ((Gather.ga (toGa1 P u w r)).recvMsg j k mm)) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.ga1 mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.procs_setGa1, procs_toRound_eq, procs_toRoundUpd, toProc,
    LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ga1_setGa1]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd, Gather.ga_setGa, SubState.recvMsg, ga_toGa1_net]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => gaProcView P Bool ((u i).2.stage r).ga1 ((u i).2.stage r).brbIn1
          ((u i).2.stage r).brbBind1) j) ?_
      simp only [gaProcView, ga_toGa1_proc, LocalState.deliverTo]
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, Gather.brbIn_setGa, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, Gather.brbBind_setGa, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery on the second gather's network, read through the view. -/
theorem toRound_dlvGa2 (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.GaMsg P.n (Option Bool)) :
    toRound P (Function.update u j (c, p.deliverTo r k (.ga2 mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.ga2 mm)))) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setGa (toGa2 P u w r) ((Gather.ga (toGa2 P u w r)).recvMsg j k mm)) := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.ga2 mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.procs_setGa2, procs_toRound_eq, procs_toRoundUpd, toProc,
    LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ga2_setGa2]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd, Gather.ga_setGa, SubState.recvMsg, ga_toGa2_net]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => gaProcView P (Option Bool) ((u i).2.stage r).ga2 ((u i).2.stage r).brbIn2
          ((u i).2.stage r).brbBind2) j) ?_
      simp only [gaProcView, ga_toGa2_proc, LocalState.deliverTo]
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, Gather.brbIn_setGa, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, Gather.brbBind_setGa, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in an input-broadcast instance of the first
gather.** -/
noncomputable def afterDlvIn1 (P : Params) (s : GBCA.LowPairState P.n)
    (i j k : Fin P.n) (m : BRB.BMsg Bool) : GBCA.LowPairState P.n :=
  GBCA.setGa1 s
    (Gather.setBrbIn (GBCA.ga1 s)
      (Function.update (Gather.brbIn (GBCA.ga1 s)) i
        ((Gather.brbIn (GBCA.ga1 s) i).recvMsg j k m)))

/-- **The round after an input-broadcast instance of the first gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
store records the value. -/
noncomputable def afterInRet1 (P : Params) (s : GBCA.LowPairState P.n)
    (i j : Fin P.n) (v : Bool) : GBCA.LowPairState P.n :=
  GBCA.setGa1 s
    (Gather.setBrbIn
      (Gather.setGa (GBCA.ga1 s)
        ((Gather.ga (GBCA.ga1 s)).setProc j
          { (Gather.ga (GBCA.ga1 s)).proc j with
            delivIn :=
              Function.update ((Gather.ga (GBCA.ga1 s)).proc j).delivIn i (some v) }))
      (Function.update (Gather.brbIn (GBCA.ga1 s)) i
        ((Gather.brbIn (GBCA.ga1 s) i).setProc j
          { (Gather.brbIn (GBCA.ga1 s) i).proc j with returned := true })))

/-- A delivery in an input-broadcast instance of the first gather that leaves
the store where it stands, read through the view. -/
theorem toRound_dlvIn1 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg Bool)
    (hst : storeIn P (((p.stage r).brbIn1 i).deliverTo k mm)
      = storeIn P ((p.stage r).brbIn1 i)) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbIn1 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbIn1 i mm)))) r
      = afterDlvIn1 P (toRound P u w r) i j k mm := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbIn1 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterDlvIn1, GBCA.procs_setGa1, procs_toRound_eq, procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterDlvIn1]
  · simp only [afterDlvIn1, GBCA.ga1_setGa1, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd, Gather.ga_setBrbIn]
      refine Prod.ext ?_ rfl
      simp only [ga_toGa1_fst]
      have hv : gaProcView P Bool ((u j).2.stage r).ga1
          (Function.update ((u j).2.stage r).brbIn1 i
            ((((u j).2.stage r).brbIn1 i).deliverTo k mm)) ((u j).2.stage r).brbBind1
          = gaProcView P Bool ((u j).2.stage r).ga1 ((u j).2.stage r).brbIn1
              ((u j).2.stage r).brbBind1 := by
        simp only [gaProcView, storeIn_update_deliverTo, hst, Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, Gather.brbIn_setBrbIn, brbIn_toGa1]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbIn1 i)) j) ?_
        exact brbLocal_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, Gather.brbBind_setBrbIn, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterDlvIn1, GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in an input-broadcast instance of the first gather that
completes an `n − f` `VOTE` quorum, read through the view. -/
theorem toRound_dlvIn1_ret (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg Bool) (v : Bool)
    (hst : storeIn P (((p.stage r).brbIn1 i).deliverTo k mm) = some v) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbIn1 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbIn1 i mm)))) r
      = afterInRet1 P (afterDlvIn1 P (toRound P u w r) i j k mm) i j v := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbIn1 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterInRet1, afterDlvIn1, GBCA.procs_setGa1, procs_toRound_eq,
    procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterInRet1, afterDlvIn1]
  · simp only [afterInRet1, afterDlvIn1, GBCA.ga1_setGa1, ga1_toRound, Gather.ga_setBrbIn,
    Gather.brbIn_setBrbIn]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd, Gather.ga_setBrbIn, Gather.ga_setGa]
      refine Prod.ext ?_ rfl
      simp only [SubState.setProc, ga_toGa1_fst]
      refine congrArg (Function.update
        (fun i' => gaProcView P Bool ((u i').2.stage r).ga1
          ((u i').2.stage r).brbIn1 ((u i').2.stage r).brbBind1) j) ?_
      simp only [gaProcView, storeIn_update_deliverTo, hst, SubState.proc, ga_toGa1_proc,
        LocalState.setP]
    · funext k'
      simp only [Gather.brbIn_setBrbIn, brbIn_ga1_toRoundUpd, brbIn_toGa1]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [SubState.setProc, SubState.recvMsg, SubState.proc, Function.update_self,
          Function.update_idem]
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbIn1 i)) j) ?_
        exact brbLocal_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.brbBind_setBrbIn, Gather.brbBind_setGa, brbBind_ga1_toRoundUpd,
        brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterInRet1, afterDlvIn1, GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in a bind-broadcast instance of the first
gather.** -/
noncomputable def afterDlvBind1 (P : Params) (s : GBCA.LowPairState P.n)
    (i j k : Fin P.n) (m : BRB.BMsg (Gather.APSet P.n Bool)) : GBCA.LowPairState P.n :=
  GBCA.setGa1 s
    (Gather.setBrbBind (GBCA.ga1 s)
      (Function.update (Gather.brbBind (GBCA.ga1 s)) i
        ((Gather.brbBind (GBCA.ga1 s) i).recvMsg j k m)))

/-- **The round after a bind-broadcast instance of the first gather returns `v`
to `j`**: the instance's return flag goes on at `j` and `j`'s gather store
records the value. -/
noncomputable def afterBindRet1 (P : Params) (s : GBCA.LowPairState P.n)
    (i j : Fin P.n) (v : Gather.APSet P.n Bool) : GBCA.LowPairState P.n :=
  GBCA.setGa1 s
    (Gather.setBrbBind
      (Gather.setGa (GBCA.ga1 s)
        ((Gather.ga (GBCA.ga1 s)).setProc j
          { (Gather.ga (GBCA.ga1 s)).proc j with
            delivBind :=
              Function.update ((Gather.ga (GBCA.ga1 s)).proc j).delivBind i (some v) }))
      (Function.update (Gather.brbBind (GBCA.ga1 s)) i
        ((Gather.brbBind (GBCA.ga1 s) i).setProc j
          { (Gather.brbBind (GBCA.ga1 s) i).proc j with returned := true })))

/-- A delivery in a bind-broadcast instance of the first gather that leaves the
store where it stands, read through the view. -/
theorem toRound_dlvBind1 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Gather.APSet P.n Bool))
    (hst : storeIn P (((p.stage r).brbBind1 i).deliverTo k mm)
      = storeIn P ((p.stage r).brbBind1 i)) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbBind1 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbBind1 i mm)))) r
      = afterDlvBind1 P (toRound P u w r) i j k mm := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbBind1 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterDlvBind1, GBCA.procs_setGa1, procs_toRound_eq, procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterDlvBind1]
  · simp only [afterDlvBind1, GBCA.ga1_setGa1, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd, Gather.ga_setBrbBind]
      refine Prod.ext ?_ rfl
      simp only [ga_toGa1_fst]
      have hv : gaProcView P Bool ((u j).2.stage r).ga1
          ((u j).2.stage r).brbIn1 (Function.update ((u j).2.stage r).brbBind1 i
            ((((u j).2.stage r).brbBind1 i).deliverTo k mm))
          = gaProcView P Bool ((u j).2.stage r).ga1 ((u j).2.stage r).brbIn1
              ((u j).2.stage r).brbBind1 := by
        simp only [gaProcView, storeIn_update_deliverTo, hst, Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext q
      simp only [brbIn_ga1_toRoundUpd, Gather.brbIn_setBrbBind, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbBind_ga1_toRoundUpd, Gather.brbBind_setBrbBind, brbBind_toGa1]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbBind1 i)) j) ?_
        exact brbLocal_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterDlvBind1, GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in a bind-broadcast instance of the first gather that completes
an `n − f` `VOTE` quorum, read through the view. -/
theorem toRound_dlvBind1_ret (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Gather.APSet P.n Bool)) (v : Gather.APSet P.n Bool)
    (hst : storeIn P (((p.stage r).brbBind1 i).deliverTo k mm) = some v) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbBind1 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbBind1 i mm)))) r
      = afterBindRet1 P (afterDlvBind1 P (toRound P u w r) i j k mm) i j v := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbBind1 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterBindRet1, afterDlvBind1, GBCA.procs_setGa1, procs_toRound_eq,
    procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterBindRet1, afterDlvBind1]
  · simp only [afterBindRet1, afterDlvBind1, GBCA.ga1_setGa1, ga1_toRound,
    Gather.ga_setBrbBind, Gather.brbBind_setBrbBind]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd, Gather.ga_setBrbBind, Gather.ga_setGa]
      refine Prod.ext ?_ rfl
      simp only [SubState.setProc, ga_toGa1_fst]
      refine congrArg (Function.update
        (fun i' => gaProcView P Bool ((u i').2.stage r).ga1
          ((u i').2.stage r).brbIn1 ((u i').2.stage r).brbBind1) j) ?_
      simp only [gaProcView, storeIn_update_deliverTo, hst, SubState.proc, ga_toGa1_proc,
        LocalState.setP]
    · funext q
      simp only [Gather.brbIn_setBrbBind, Gather.brbIn_setGa, brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [Gather.brbBind_setBrbBind, brbBind_ga1_toRoundUpd, brbBind_toGa1]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [SubState.setProc, SubState.recvMsg, SubState.proc, Function.update_self,
          Function.update_idem]
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbBind1 i)) j) ?_
        exact brbLocal_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterBindRet1, afterDlvBind1, GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in an input-broadcast instance of the second
gather.** -/
noncomputable def afterDlvIn2 (P : Params) (s : GBCA.LowPairState P.n)
    (i j k : Fin P.n) (m : BRB.BMsg (Option Bool)) : GBCA.LowPairState P.n :=
  GBCA.setGa2 s
    (Gather.setBrbIn (GBCA.ga2 s)
      (Function.update (Gather.brbIn (GBCA.ga2 s)) i
        ((Gather.brbIn (GBCA.ga2 s) i).recvMsg j k m)))

/-- **The round after an input-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
store records the value. -/
noncomputable def afterInRet2 (P : Params) (s : GBCA.LowPairState P.n)
    (i j : Fin P.n) (v : Option Bool) : GBCA.LowPairState P.n :=
  GBCA.setGa2 s
    (Gather.setBrbIn
      (Gather.setGa (GBCA.ga2 s)
        ((Gather.ga (GBCA.ga2 s)).setProc j
          { (Gather.ga (GBCA.ga2 s)).proc j with
            delivIn :=
              Function.update ((Gather.ga (GBCA.ga2 s)).proc j).delivIn i (some v) }))
      (Function.update (Gather.brbIn (GBCA.ga2 s)) i
        ((Gather.brbIn (GBCA.ga2 s) i).setProc j
          { (Gather.brbIn (GBCA.ga2 s) i).proc j with returned := true })))

/-- A delivery in an input-broadcast instance of the second gather that leaves
the store where it stands, read through the view. -/
theorem toRound_dlvIn2 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Option Bool))
    (hst : storeIn P (((p.stage r).brbIn2 i).deliverTo k mm)
      = storeIn P ((p.stage r).brbIn2 i)) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbIn2 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbIn2 i mm)))) r
      = afterDlvIn2 P (toRound P u w r) i j k mm := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbIn2 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterDlvIn2, GBCA.procs_setGa2, procs_toRound_eq, procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterDlvIn2]
  · simp only [afterDlvIn2, GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterDlvIn2, GBCA.ga2_setGa2, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd, Gather.ga_setBrbIn]
      refine Prod.ext ?_ rfl
      simp only [ga_toGa2_fst]
      have hv : gaProcView P (Option Bool) ((u j).2.stage r).ga2
          (Function.update ((u j).2.stage r).brbIn2 i
            ((((u j).2.stage r).brbIn2 i).deliverTo k mm)) ((u j).2.stage r).brbBind2
          = gaProcView P (Option Bool) ((u j).2.stage r).ga2 ((u j).2.stage r).brbIn2
              ((u j).2.stage r).brbBind2 := by
        simp only [gaProcView, storeIn_update_deliverTo, hst, Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [brbIn_ga2_toRoundUpd, Gather.brbIn_setBrbIn, brbIn_toGa2]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbIn2 i)) j) ?_
        exact brbLocal_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga2_toRoundUpd, Gather.brbBind_setBrbIn, brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in an input-broadcast instance of the second gather that
completes an `n − f` `VOTE` quorum, read through the view. -/
theorem toRound_dlvIn2_ret (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Option Bool)) (v : Option Bool)
    (hst : storeIn P (((p.stage r).brbIn2 i).deliverTo k mm) = some v) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbIn2 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbIn2 i mm)))) r
      = afterInRet2 P (afterDlvIn2 P (toRound P u w r) i j k mm) i j v := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbIn2 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterInRet2, afterDlvIn2, GBCA.procs_setGa2, procs_toRound_eq,
    procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterInRet2, afterDlvIn2]
  · simp only [afterInRet2, afterDlvIn2, GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterInRet2, afterDlvIn2, GBCA.ga2_setGa2, ga2_toRound, Gather.ga_setBrbIn,
    Gather.brbIn_setBrbIn]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd, Gather.ga_setBrbIn, Gather.ga_setGa]
      refine Prod.ext ?_ rfl
      simp only [SubState.setProc, ga_toGa2_fst]
      refine congrArg (Function.update
        (fun i' => gaProcView P (Option Bool) ((u i').2.stage r).ga2
          ((u i').2.stage r).brbIn2 ((u i').2.stage r).brbBind2) j) ?_
      simp only [gaProcView, storeIn_update_deliverTo, hst, SubState.proc, ga_toGa2_proc,
        LocalState.setP]
    · funext k'
      simp only [Gather.brbIn_setBrbIn, brbIn_ga2_toRoundUpd, brbIn_toGa2]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [SubState.setProc, SubState.recvMsg, SubState.proc, Function.update_self,
          Function.update_idem]
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbIn2 i)) j) ?_
        exact brbLocal_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.brbBind_setBrbIn, Gather.brbBind_setGa, brbBind_ga2_toRoundUpd,
        brbBind_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in a bind-broadcast instance of the second
gather.** -/
noncomputable def afterDlvBind2 (P : Params) (s : GBCA.LowPairState P.n)
    (i j k : Fin P.n) (m : BRB.BMsg (Gather.APSet P.n (Option Bool))) : GBCA.LowPairState P.n :=
  GBCA.setGa2 s
    (Gather.setBrbBind (GBCA.ga2 s)
      (Function.update (Gather.brbBind (GBCA.ga2 s)) i
        ((Gather.brbBind (GBCA.ga2 s) i).recvMsg j k m)))

/-- **The round after a bind-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
store records the value. -/
noncomputable def afterBindRet2 (P : Params) (s : GBCA.LowPairState P.n)
    (i j : Fin P.n) (v : Gather.APSet P.n (Option Bool)) : GBCA.LowPairState P.n :=
  GBCA.setGa2 s
    (Gather.setBrbBind
      (Gather.setGa (GBCA.ga2 s)
        ((Gather.ga (GBCA.ga2 s)).setProc j
          { (Gather.ga (GBCA.ga2 s)).proc j with
            delivBind :=
              Function.update ((Gather.ga (GBCA.ga2 s)).proc j).delivBind i (some v) }))
      (Function.update (Gather.brbBind (GBCA.ga2 s)) i
        ((Gather.brbBind (GBCA.ga2 s) i).setProc j
          { (Gather.brbBind (GBCA.ga2 s) i).proc j with returned := true })))

/-- A delivery in a bind-broadcast instance of the second gather that leaves
the store where it stands, read through the view. -/
theorem toRound_dlvBind2 (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Gather.APSet P.n (Option Bool)))
    (hst : storeIn P (((p.stage r).brbBind2 i).deliverTo k mm)
      = storeIn P ((p.stage r).brbBind2 i)) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbBind2 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbBind2 i mm)))) r
      = afterDlvBind2 P (toRound P u w r) i j k mm := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbBind2 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterDlvBind2, GBCA.procs_setGa2, procs_toRound_eq, procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterDlvBind2]
  · simp only [afterDlvBind2, GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterDlvBind2, GBCA.ga2_setGa2, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd, Gather.ga_setBrbBind]
      refine Prod.ext ?_ rfl
      simp only [ga_toGa2_fst]
      have hv : gaProcView P (Option Bool) ((u j).2.stage r).ga2
          ((u j).2.stage r).brbIn2 (Function.update ((u j).2.stage r).brbBind2 i
            ((((u j).2.stage r).brbBind2 i).deliverTo k mm))
          = gaProcView P (Option Bool) ((u j).2.stage r).ga2 ((u j).2.stage r).brbIn2
              ((u j).2.stage r).brbBind2 := by
        simp only [gaProcView, storeIn_update_deliverTo, hst, Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext q
      simp only [brbIn_ga2_toRoundUpd, Gather.brbIn_setBrbBind, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbBind_ga2_toRoundUpd, Gather.brbBind_setBrbBind, brbBind_toGa2]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbBind2 i)) j) ?_
        exact brbLocal_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in a bind-broadcast instance of the second gather that completes
an `n − f` `VOTE` quorum, read through the view. -/
theorem toRound_dlvBind2_ret (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.BMsg (Gather.APSet P.n (Option Bool))) (v : Gather.APSet P.n (Option Bool))
    (hst : storeIn P (((p.stage r).brbBind2 i).deliverTo k mm) = some v) :
    toRound P (Function.update u j (c, p.deliverTo r k (.brbBind2 i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gdlv r j k (.brbBind2 i mm)))) r
      = afterBindRet2 P (afterDlvBind2 P (toRound P u w r) i j k mm) i j v := by
  subst hu
  rw [toRound_ghostId (Sum.inr (.gdlv r j k (.brbBind2 i mm))) (fun _ _ => rfl)]
  simp only [StageSideRecP.deliverTo, stageRecord_deliverTo, StageRec.deliverTo]
  rw [toRound_writeNoSent]
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp only [afterBindRet2, afterDlvBind2, GBCA.procs_setGa2, procs_toRound_eq,
    procs_toRoundUpd, toProc]
    exact Function.update_eq_self _ _
  · simp [afterBindRet2, afterDlvBind2]
  · simp only [afterBindRet2, afterDlvBind2, GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga1_toRoundUpd]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [brbIn_ga1_toRoundUpd, brbIn_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [brbBind_ga1_toRoundUpd, brbBind_toGa1]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterBindRet2, afterDlvBind2, GBCA.ga2_setGa2, ga2_toRound,
    Gather.ga_setBrbBind, Gather.brbBind_setBrbBind]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · simp only [ga_ga2_toRoundUpd, Gather.ga_setBrbBind, Gather.ga_setGa]
      refine Prod.ext ?_ rfl
      simp only [SubState.setProc, ga_toGa2_fst]
      refine congrArg (Function.update
        (fun i' => gaProcView P (Option Bool) ((u i').2.stage r).ga2
          ((u i').2.stage r).brbIn2 ((u i').2.stage r).brbBind2) j) ?_
      simp only [gaProcView, storeIn_update_deliverTo, hst, SubState.proc, ga_toGa2_proc,
        LocalState.setP]
    · funext q
      simp only [Gather.brbIn_setBrbBind, Gather.brbIn_setGa, brbIn_ga2_toRoundUpd, brbIn_toGa2]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [Gather.brbBind_setBrbBind, brbBind_ga2_toRoundUpd, brbBind_toGa2]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [SubState.setProc, SubState.recvMsg, SubState.proc, Function.update_self,
          Function.update_idem]
        refine congrArg (Function.update
          (fun i' => brbLocal P (((u i').2.stage r).brbBind2 i)) j) ?_
        exact brbLocal_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-! ### A Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the network state its tag names and no record moves. -/

/-- A Byzantine injection on the first gather's network state, read through the
view. -/
theorem toRound_byzGa1 (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (k : Fin P.n) (mm : Gather.GaMsg P.n Bool) :
    toRound P u (w.gsent r k (.ga1 mm)) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setGa (toGa1 P u w r) ((Gather.ga (toGa1 P u w r)).mcast k mm)) := by
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ga1_setGa1, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.ga_setGa, SubState.mcast, NetworkState.post, ga_toGa1_net,
        gsent_sent_self]
      exact slice_post_some unGa1 unGa1_inj (w.sent r) k (.ga1 mm) mm rfl
    · funext k'
      simp only [Gather.brbIn_setGa, brbIn_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k') (unIn1_inj k') (w.sent r) k (.ga1 mm) rfl
    · funext k'
      simp only [Gather.brbBind_setGa, brbBind_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind1 k') (unBind1_inj k') (w.sent r) k (.ga1 mm) rfl
    · simp
  · simp only [GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [ga_toGa2_net, gsent_sent_self]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) k (.ga1 mm) rfl
    · funext k'
      simp only [brbIn_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn2 k') (unIn2_inj k') (w.sent r) k (.ga1 mm) rfl
    · funext k'
      simp only [brbBind_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind2 k') (unBind2_inj k') (w.sent r) k (.ga1 mm) rfl
    · simp

/-- A Byzantine injection on the second gather's network state, read through
the view. -/
theorem toRound_byzGa2 (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (k : Fin P.n) (mm : Gather.GaMsg P.n (Option Bool)) :
    toRound P u (w.gsent r k (.ga2 mm)) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setGa (toGa2 P u w r) ((Gather.ga (toGa2 P u w r)).mcast k mm)) := by
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [ga_toGa1_net, gsent_sent_self]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) k (.ga2 mm) rfl
    · funext k'
      simp only [brbIn_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k') (unIn1_inj k') (w.sent r) k (.ga2 mm) rfl
    · funext k'
      simp only [brbBind_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind1 k') (unBind1_inj k') (w.sent r) k (.ga2 mm) rfl
    · simp
  · simp only [GBCA.ga2_setGa2, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.ga_setGa, SubState.mcast, NetworkState.post, ga_toGa2_net,
        gsent_sent_self]
      exact slice_post_some unGa2 unGa2_inj (w.sent r) k (.ga2 mm) mm rfl
    · funext k'
      simp only [Gather.brbIn_setGa, brbIn_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn2 k') (unIn2_inj k') (w.sent r) k (.ga2 mm) rfl
    · funext k'
      simp only [Gather.brbBind_setGa, brbBind_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind2 k') (unBind2_inj k') (w.sent r) k (.ga2 mm) rfl
    · simp

/-- A Byzantine injection on an input-broadcast instance of the first gather,
read through the view. -/
theorem toRound_byzIn1 (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg Bool) :
    toRound P u (w.gsent r k (.brbIn1 i mm)) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbIn (toGa1 P u w r)
            (Function.update (Gather.brbIn (toGa1 P u w r)) i
              ((Gather.brbIn (toGa1 P u w r) i).mcast k mm))) := by
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ga1_setGa1, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.ga_setBrbIn, ga_toGa1_net, gsent_sent_self]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) k (.brbIn1 i mm) rfl
    · funext k'
      simp only [Gather.brbIn_setBrbIn, brbIn_toGa1, gsent_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [SubState.mcast, NetworkState.post]
        exact slice_post_some (unIn1 i) (unIn1_inj i) (w.sent r) k
          (.brbIn1 i mm) mm (by simp [unIn1])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [brbIn_toGa1]
        exact slice_post_none (unIn1 k') (unIn1_inj k') (w.sent r) k
          (.brbIn1 i mm) (by simp [unIn1, Ne.symm hk])
    · funext k'
      simp only [Gather.brbBind_setBrbIn, brbBind_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind1 k') (unBind1_inj k') (w.sent r) k (.brbIn1 i mm) rfl
    · simp
  · simp only [GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [ga_toGa2_net, gsent_sent_self]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) k (.brbIn1 i mm) rfl
    · funext k'
      simp only [brbIn_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn2 k') (unIn2_inj k') (w.sent r) k (.brbIn1 i mm) rfl
    · funext k'
      simp only [brbBind_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind2 k') (unBind2_inj k') (w.sent r) k (.brbIn1 i mm) rfl
    · simp

/-- A Byzantine injection on a bind-broadcast instance of the first gather,
read through the view. -/
theorem toRound_byzBind1 (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg (Gather.APSet P.n Bool)) :
    toRound P u (w.gsent r k (.brbBind1 i mm)) r
      = GBCA.setGa1 (toRound P u w r)
          (Gather.setBrbBind (toGa1 P u w r)
            (Function.update (Gather.brbBind (toGa1 P u w r)) i
              ((Gather.brbBind (toGa1 P u w r) i).mcast k mm))) := by
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ga1_setGa1, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.ga_setBrbBind, ga_toGa1_net, gsent_sent_self]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) k (.brbBind1 i mm) rfl
    · funext k'
      simp only [Gather.brbIn_setBrbBind, brbIn_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k') (unIn1_inj k') (w.sent r) k (.brbBind1 i mm) rfl
    · funext k'
      simp only [Gather.brbBind_setBrbBind, brbBind_toGa1, gsent_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [SubState.mcast, NetworkState.post]
        exact slice_post_some (unBind1 i) (unBind1_inj i) (w.sent r) k
          (.brbBind1 i mm) mm (by simp [unBind1])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [brbBind_toGa1]
        exact slice_post_none (unBind1 k') (unBind1_inj k') (w.sent r) k
          (.brbBind1 i mm) (by simp [unBind1, Ne.symm hk])
    · simp
  · simp only [GBCA.ga2_setGa1, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [ga_toGa2_net, gsent_sent_self]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) k (.brbBind1 i mm) rfl
    · funext k'
      simp only [brbIn_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn2 k') (unIn2_inj k') (w.sent r) k (.brbBind1 i mm) rfl
    · funext k'
      simp only [brbBind_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind2 k') (unBind2_inj k') (w.sent r) k (.brbBind1 i mm) rfl
    · simp

/-- A Byzantine injection on an input-broadcast instance of the second gather,
read through the view. -/
theorem toRound_byzIn2 (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg (Option Bool)) :
    toRound P u (w.gsent r k (.brbIn2 i mm)) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbIn (toGa2 P u w r)
            (Function.update (Gather.brbIn (toGa2 P u w r)) i
              ((Gather.brbIn (toGa2 P u w r) i).mcast k mm))) := by
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [ga_toGa1_net, gsent_sent_self]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) k (.brbIn2 i mm) rfl
    · funext k'
      simp only [brbIn_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k') (unIn1_inj k') (w.sent r) k (.brbIn2 i mm) rfl
    · funext k'
      simp only [brbBind_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind1 k') (unBind1_inj k') (w.sent r) k (.brbIn2 i mm) rfl
    · simp
  · simp only [GBCA.ga2_setGa2, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.ga_setBrbIn, ga_toGa2_net, gsent_sent_self]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) k (.brbIn2 i mm) rfl
    · funext k'
      simp only [Gather.brbIn_setBrbIn, brbIn_toGa2, gsent_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [SubState.mcast, NetworkState.post]
        exact slice_post_some (unIn2 i) (unIn2_inj i) (w.sent r) k
          (.brbIn2 i mm) mm (by simp [unIn2])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [brbIn_toGa2]
        exact slice_post_none (unIn2 k') (unIn2_inj k') (w.sent r) k
          (.brbIn2 i mm) (by simp [unIn2, Ne.symm hk])
    · funext k'
      simp only [Gather.brbBind_setBrbIn, brbBind_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind2 k') (unBind2_inj k') (w.sent r) k (.brbIn2 i mm) rfl
    · simp

/-- A Byzantine injection on a bind-broadcast instance of the second gather,
read through the view. -/
theorem toRound_byzBind2 (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (k : Fin P.n) (i : Fin P.n) (mm : BRB.BMsg (Gather.APSet P.n (Option Bool))) :
    toRound P u (w.gsent r k (.brbBind2 i mm)) r
      = GBCA.setGa2 (toRound P u w r)
          (Gather.setBrbBind (toGa2 P u w r)
            (Function.update (Gather.brbBind (toGa2 P u w r)) i
              ((Gather.brbBind (toGa2 P u w r) i).mcast k mm))) := by
  refine roundStateAt_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ga1_setGa2, ga1_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [ga_toGa1_net, gsent_sent_self]
      exact slice_post_none unGa1 unGa1_inj (w.sent r) k (.brbBind2 i mm) rfl
    · funext k'
      simp only [brbIn_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn1 k') (unIn1_inj k') (w.sent r) k (.brbBind2 i mm) rfl
    · funext k'
      simp only [brbBind_toGa1, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unBind1 k') (unBind1_inj k') (w.sent r) k (.brbBind2 i mm) rfl
    · simp
  · simp only [GBCA.ga2_setGa2, ga2_toRound]
    refine subStateAt_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.ga_setBrbBind, ga_toGa2_net, gsent_sent_self]
      exact slice_post_none unGa2 unGa2_inj (w.sent r) k (.brbBind2 i mm) rfl
    · funext k'
      simp only [Gather.brbIn_setBrbBind, brbIn_toGa2, gsent_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact slice_post_none (unIn2 k') (unIn2_inj k') (w.sent r) k (.brbBind2 i mm) rfl
    · funext k'
      simp only [Gather.brbBind_setBrbBind, brbBind_toGa2, gsent_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [SubState.mcast, NetworkState.post]
        exact slice_post_some (unBind2 i) (unBind2_inj i) (w.sent r) k
          (.brbBind2 i mm) mm (by simp [unBind2])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [brbBind_toGa2]
        exact slice_post_none (unBind2 k') (unBind2_inj k') (w.sent r) k
          (.brbBind2 i mm) (by simp [unBind2, Ne.symm hk])
    · simp

/-! ### Every other round stands still

A row names one round. The rounds it does not name read exactly as they did:
the acting process's other round records are untouched, the adversary's sent
family is written at one round only, and so is its ghost record. -/

/-- The view of a round the row does not name. -/
theorem toRound_otherRow (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : StageRec P.n) (v : NetState P.n) (hsent : v.sent r' = w.sent r')
    (hF : v.F = w.F) (hghost : v.ghostRec r' = w.ghostRec r') :
    toRound P (Function.update u j (c, p.setStage r sr)) v r' = toRound P u w r' := by
  simp only [toRound, toGa1, toGa2, stage_update_ne hu hr, hsent, hF, hghost]

/-- A send of round `r`, read at another round. -/
theorem toRound_other (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr : StageRec P.n)
    (m : Msg P.n) {L : NLabP P.n (Msg P.n)} (hL : roundOf L = some r) :
    toRound P (Function.update u j (c, p.setStage r sr))
        ((w.gsent r j m).writeGhost (ghostStep P) L) r' = toRound P u w r' := by
  rw [toRound_writeGhost_ne _ _ hL hr]
  exact toRound_otherRow hu hr sr _ (gsent_sent_ne w r j m hr) rfl rfl

/-- A row of round `r` that records nothing, read at another round. -/
theorem toRound_otherNoSent (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : StageRec P.n) {L : NLabP P.n (Msg P.n)} (hL : roundOf L = some r) :
    toRound P (Function.update u j (c, p.setStage r sr))
        (w.writeGhost (ghostStep P) L) r' = toRound P u w r' := by
  rw [toRound_writeGhost_ne _ _ hL hr]
  exact toRound_otherRow hu hr sr w rfl rfl rfl

/-- A Byzantine injection of round `r`, read at another round. -/
theorem toRound_otherSent (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    {r r' : ℕ} (hr : r' ≠ r) (k : Fin P.n) (m : Msg P.n)
    {L : NLabP P.n (Msg P.n)} (hL : roundOf L = some r) :
    toRound P u ((w.gsent r k m).writeGhost (ghostStep P) L) r' = toRound P u w r' := by
  rw [toRound_writeGhost_ne _ _ hL hr]
  simp only [toRound, toGa1, toGa2, gsent_sent_ne w r k m hr, gsent_F, gsent_ghostRec]

/-- **The whole family of rounds after a send**: the round the row names moves,
the rest stand still. -/
theorem toRoundFam (hu : (u j).2 = p) (r : ℕ) (sr : StageRec P.n) (m : Msg P.n)
    {L : NLabP P.n (Msg P.n)} (hL : roundOf L = some r) (X : GBCA.LowPairState P.n)
    (hX : toRound P (Function.update u j (c, p.setStage r sr))
      ((w.gsent r j m).writeGhost (ghostStep P) L) r = X) :
    (fun r' => toRound P (Function.update u j (c, p.setStage r sr))
        ((w.gsent r j m).writeGhost (ghostStep P) L) r')
      = Function.update (fun r' => toRound P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, toRound_other hu hr sr m hL]

/-- The same, for a row that records nothing. -/
theorem toRoundFamNoSent (hu : (u j).2 = p) (r : ℕ) (sr : StageRec P.n)
    {L : NLabP P.n (Msg P.n)} (hL : roundOf L = some r) (X : GBCA.LowPairState P.n)
    (hX : toRound P (Function.update u j (c, p.setStage r sr))
      (w.writeGhost (ghostStep P) L) r = X) :
    (fun r' => toRound P (Function.update u j (c, p.setStage r sr))
        (w.writeGhost (ghostStep P) L) r')
      = Function.update (fun r' => toRound P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, toRound_otherNoSent hu hr sr hL]

/-- The same, for a Byzantine injection. -/
theorem toRoundFamSent (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n) (r : ℕ)
    (k : Fin P.n) (m : Msg P.n) {L : NLabP P.n (Msg P.n)} (hL : roundOf L = some r)
    (X : GBCA.LowPairState P.n)
    (hX : toRound P u ((w.gsent r k m).writeGhost (ghostStep P) L) r = X) :
    (fun r' => toRound P u ((w.gsent r k m).writeGhost (ghostStep P) L) r')
      = Function.update (fun r' => toRound P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, toRound_otherSent u w hr k m hL]

end Rows

/-! ### The two clauses that are not readings

`StoreInv` and `BoundInv` are the conjuncts of `AFW.ProtocolRel` that no
frame lemma supplies. Each survives a row instance by instance: a broadcast
instance either stands still or takes a row of `BRB.ImplStep`, which
`BRB.Inv.step` carries, and a process's second-gather local input is written at
the link alone. -/

section Invariants

/-- One broadcast instance's move across a row: it stands still, or it takes a
row of `BRB.ImplStep`. -/
def InvStep (P : Params) {M : Type} [DecidableEq M] (ldr : Fin P.n)
    (s s' : BRB.ImplState P.n M) : Prop :=
  s' = s ∨ ∃ l, BRB.ImplStep P ldr s l (PMF.pure s')

/-- An instance that stands still. -/
theorem InvStep.stand {M : Type} [DecidableEq M] (P : Params) (ldr : Fin P.n)
    (s : BRB.ImplState P.n M) : InvStep P ldr s s := Or.inl rfl

/-- An instance that takes a row. -/
theorem InvStep.row {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s s' : BRB.ImplState P.n M} {l : BRB.Lab P.n M}
    (h : BRB.ImplStep P ldr s l (PMF.pure s')) : InvStep P ldr s s' := Or.inr ⟨l, h⟩

/-- **The broadcast invariant survives one instance's move.** -/
theorem InvStep.inv {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s s' : BRB.ImplState P.n M} (h : InvStep P ldr s s') (hInv : BRB.Inv P ldr s) :
    BRB.Inv P ldr s' := by
  rcases h with rfl | ⟨l, hl⟩
  · exact hInv
  · exact hInv.step hl (by simp)

/-- A row that moves one instance of a family: that instance takes its row and
every other instance stands still. -/
theorem invStep_update {M : Type} [DecidableEq M] {P : Params}
    (b : Fin P.n → BRB.ImplState P.n M) (i : Fin P.n) (s' : BRB.ImplState P.n M)
    {l : BRB.Lab P.n M} (h : BRB.ImplStep P i (b i) l (PMF.pure s')) (k : Fin P.n) :
    InvStep P k (b k) (Function.update b i s' k) := by
  by_cases hk : k = i
  · subst hk; rw [Function.update_self]; exact InvStep.row h
  · rw [Function.update_of_ne hk]; exact InvStep.stand P k (b k)

variable {u x : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w v : NetState P.n}

/-- **The broadcast invariant survives a row**: at each of a round's `4n`
instances the state after the row is the state before it or a `BRB.ImplStep`
successor of it. -/
theorem storeInv_of (hI : StoreInv P u w)
    (h1 : ∀ r k, InvStep P k (Gather.brbIn (GBCA.ga1 (toRound P u w r)) k)
      (Gather.brbIn (GBCA.ga1 (toRound P x v r)) k))
    (h2 : ∀ r k, InvStep P k (Gather.brbBind (GBCA.ga1 (toRound P u w r)) k)
      (Gather.brbBind (GBCA.ga1 (toRound P x v r)) k))
    (h3 : ∀ r k, InvStep P k (Gather.brbIn (GBCA.ga2 (toRound P u w r)) k)
      (Gather.brbIn (GBCA.ga2 (toRound P x v r)) k))
    (h4 : ∀ r k, InvStep P k (Gather.brbBind (GBCA.ga2 (toRound P u w r)) k)
      (Gather.brbBind (GBCA.ga2 (toRound P x v r)) k)) :
    StoreInv P x v :=
  fun r k => ⟨(h1 r k).inv (hI r k).1, (h2 r k).inv (hI r k).2.1,
    (h3 r k).inv (hI r k).2.2.1, (h4 r k).inv (hI r k).2.2.2⟩

/-- A row that leaves every round's view where it stands keeps the broadcast
invariant. -/
theorem storeInv_congr (hI : StoreInv P u w) (h : ∀ r, toRound P x v r = toRound P u w r) :
    StoreInv P x v := fun r k => by rw [h r]; exact hI r k

/-- The bound invariant survives a row that leaves every process's
second-gather local input where it stands and writes the ghost through
`AFW.ghostStep`. -/
theorem boundInv_writeGhost (hI : BoundInv P u w)
    (hx : ∀ i r, (((x i).2.stage r).ga2.proc).input = (((u i).2.stage r).ga2.proc).input)
    (hv : ∀ r, v.ghostRec r = w.ghostRec r) (L : NLabP P.n (Msg P.n)) :
    BoundInv P x (v.writeGhost (ghostStep P) L) :=
  boundInv_of hI hx (fun r h => writeGhost_bound L (by rw [hv r]; exact h))

end Invariants

end AFW

end ABA
end PLTS
