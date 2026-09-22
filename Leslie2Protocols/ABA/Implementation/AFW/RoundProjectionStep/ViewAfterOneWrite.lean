/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndErasures
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjection

/-!
# The view of the composed round after one write

A row of the implementation writes the acting process's round record and records at most one
tagged message. `roundProjection_write` and `roundProjection_writeNoSent` do that write once,
through `roundProjectionUpdate`: each local state vector of the view becomes a one-point update of
the old one, and each network state is recovered from the written sent family by its own tag
(`messagesOf`).
`messagesOf_recordSent_some` and `messagesOf_recordSent_none` are the sent algebra a row still
owes, and one simp lemma per coordinate reads the written view off `roundProjectionUpdate`.
`broadcastReturnsFor_update_setProcess` and `broadcastReturnsFor_update_deliverTo` read the family
of returned values under a local write and under a delivery. `networkState_ext`,
`stateOverBroadcasts_ext` and `roundStateOverGathers_ext` identify a network state, a
gather-over-Bracha state and a round state with their components. Every row class of
`Implementation/AFW/RoundProjectionStep/` rests on this file.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

/-! ### Two extensionality helpers -/

/-- A network state is its sent family beside its corrupted set. -/
theorem networkState_ext {n : ℕ} {M : Type} {a b : ABA.NetworkState n M}
    (hp : a.sent = b.sent) (hF : a.F = b.F) : a = b := by
  cases a; cases b; simp_all

/-- A gather-over-Bracha state is its gather tier beside its two broadcast
families and its core. -/
theorem stateOverBroadcasts_ext {n : ℕ} {X B B' : Type} {a b : Gather.StateOverBroadcasts n X B B'}
    (h1 : Gather.gatherTier a = Gather.gatherTier b)
    (h2 : Gather.inputBroadcasts a = Gather.inputBroadcasts b)
    (h3 : Gather.bindBroadcasts a = Gather.bindBroadcasts b) (h4 : Gather.core a = Gather.core b) :
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
theorem roundStateOverGathers_ext {n : ℕ} {G₁ G₂ : Type}
    {a b : GBCA.ByAFW.RoundStateOverGathers n G₁ G₂}
    (h1 : GBCA.ByAFW.programs a = GBCA.ByAFW.programs b)
    (h2 : GBCA.ByAFW.bound a = GBCA.ByAFW.bound b)
    (h3 : GBCA.ByAFW.firstGather a = GBCA.ByAFW.firstGather b)
    (h4 : GBCA.ByAFW.secondGather a = GBCA.ByAFW.secondGather b) : a = b := by
  obtain ⟨⟨ua, va⟩, ca, da⟩ := a
  obtain ⟨⟨ub, vb⟩, cb, db⟩ := b
  change ua = ub at h1
  change va = vb at h2
  change ca = cb at h3
  change da = db at h4
  subst h1; subst h2; subst h3; subst h4
  rfl

/-! ### The messages of one tag under a recorded send -/

variable {n : ℕ} {β : Type}

/-- A sent message of another tag leaves the messagesOf alone. -/
theorem messagesOf_recordSent_none (f : Message n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (sent : Fin n → Finset (Message n)) (j : Fin n) (m : Message n) (hm : f m = none) :
    messagesOf f hf (Function.update sent j (insert m (sent j))) = messagesOf f hf sent := by
  funext q
  ext b
  rw [mem_messagesOf, mem_messagesOf]
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

/-- A sent message of the tag being recovered arrives in that messagesOf. -/
theorem messagesOf_recordSent_some [DecidableEq β] (f : Message n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (sent : Fin n → Finset (Message n)) (j : Fin n) (m : Message n) (b : β)
    (hm : f m = some b) :
    messagesOf f hf (Function.update sent j (insert m (sent j)))
      = Function.update (messagesOf f hf sent) j (insert b (messagesOf f hf sent j)) := by
  funext q
  by_cases hq : q = j
  · subst hq
    rw [Function.update_self]
    ext c
    rw [mem_messagesOf, Finset.mem_insert, mem_messagesOf]
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
    rw [mem_messagesOf, mem_messagesOf]
    constructor
    · rintro ⟨a, ha, hac⟩
      rw [Function.update_of_ne hq] at ha
      exact ⟨a, ha, hac⟩
    · rintro ⟨a, ha, hac⟩
      exact ⟨a, by rw [Function.update_of_ne hq]; exact ha, hac⟩

/-! ### Reading a written record -/

variable {P : Parameters}

/-- The round record a process holds at the round it has just written. -/
theorem roundRecord_update_self {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n} (hu : (u j).2 = p) (r : ℕ)
    (sr : RoundRecord P.n) (i : Fin P.n) :
    ((Function.update u j (c, p.setRoundRecord r sr) i).2.roundRecord r)
      = if i = j then sr else ((u i).2.roundRecord r) := by
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    simp
  · rw [Function.update_of_ne hi, if_neg hi]

/-- The round records a process holds at every other round. -/
theorem roundRecord_update_ne {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n} (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : RoundRecord P.n) (i : Fin P.n) :
    ((Function.update u j (c, p.setRoundRecord r sr) i).2.roundRecord r') =
    ((u i).2.roundRecord r') := by
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    change ((p.setRoundRecord r sr).roundRecord r') = _
    rw [Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr, hu]
  · rw [Function.update_of_ne hi]

/-- The round loop a process holds is untouched by a round-record write. -/
@[simp] theorem core_update {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {j : Fin P.n}
    (x : AFW.ProcessRecord P.n) (i : Fin P.n) :
    (Function.update u j x i).1 = if i = j then x.1 else (u i).1 := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hi, if_neg hi]

/-- The view reads a process family through its round records alone. -/
theorem roundProjection_congr {x u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n}
    {r : ℕ} (h : ∀ i, (x i).2.roundRecord r = (u i).2.roundRecord r) :
    roundProjection P x w r = roundProjection P u w r := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection, h]

/-! ### Transposing one written record

A row writes the acting process's round record, so each local state vector the
view reads becomes a one-point update of the old one. Each lemma below is that
observation at one component of the view, stated over the `ite` that reading a
written record produces. -/

section LocalStates
variable {j : Fin P.n} (Y : Fin P.n → RoundRecord P.n) (sr : RoundRecord P.n)

theorem locals_programProjection_if :
    (fun i => programProjection (if i = j then sr else Y i))
      = Function.update (fun i => programProjection (Y i)) j (programProjection sr) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherLocalState_if :
    (fun i => gatherLocalState P Bool (if i = j then sr else Y i).firstGather
        (if i = j then sr else Y i).firstGatherInputBroadcasts (if i = j then sr else Y
          i).firstGatherBindBroadcasts)
      = Function.update
          (fun i => gatherLocalState P Bool (Y i).firstGather (Y i).firstGatherInputBroadcasts (Y
            i).firstGatherBindBroadcasts) j
          (gatherLocalState P Bool sr.firstGather sr.firstGatherInputBroadcasts
            sr.firstGatherBindBroadcasts) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherLocalState_if :
    (fun i => gatherLocalState P (Option Bool) (if i = j then sr else Y i).secondGather
        (if i = j then sr else Y i).secondGatherInputBroadcasts (if i = j then sr else Y
          i).secondGatherBindBroadcasts)
      = Function.update
          (fun i => gatherLocalState P (Option Bool) (Y i).secondGather (Y
            i).secondGatherInputBroadcasts (Y i).secondGatherBindBroadcasts) j
          (gatherLocalState P (Option Bool) sr.secondGather sr.secondGatherInputBroadcasts
            sr.secondGatherBindBroadcasts) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherInputBroadcast_if (k : Fin P.n) :
    (fun i => broadcastLocalState P ((if i = j then sr else Y i).firstGatherInputBroadcasts k))
      = Function.update (fun i => broadcastLocalState P ((Y i).firstGatherInputBroadcasts k)) j
          (broadcastLocalState P (sr.firstGatherInputBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherBindBroadcast_if (k : Fin P.n) :
    (fun i => broadcastLocalState P ((if i = j then sr else Y i).firstGatherBindBroadcasts k))
      = Function.update (fun i => broadcastLocalState P ((Y i).firstGatherBindBroadcasts k)) j
          (broadcastLocalState P (sr.firstGatherBindBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherInputBroadcast_if (k : Fin P.n) :
    (fun i => broadcastLocalState P ((if i = j then sr else Y i).secondGatherInputBroadcasts k))
      = Function.update (fun i => broadcastLocalState P ((Y i).secondGatherInputBroadcasts k)) j
          (broadcastLocalState P (sr.secondGatherInputBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherBindBroadcast_if (k : Fin P.n) :
    (fun i => broadcastLocalState P ((if i = j then sr else Y i).secondGatherBindBroadcasts k))
      = Function.update (fun i => broadcastLocalState P ((Y i).secondGatherBindBroadcasts k)) j
          (broadcastLocalState P (sr.secondGatherBindBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

end LocalStates
/-! ### The view after one write

A row of the implementation writes one component of the acting process's round
record and records at most one tagged message. The two lemmas below are that
write read through the view: each local state vector becomes a one-point
update, and each network state is recovered from the written sent family by its
own tag. What every row still owes is then sent algebra alone. -/

section Writes
variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-- The view after a write, with the one-point update pushed inside every
coordinate: the acting process's local state replaced in each local state
vector, and each network state recovered from the written sent by its own tag.
The two cores
and the bound bit are the adversary's ghost record of the round, which a write
leaves alone. -/
noncomputable def roundProjectionUpdate (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) (j : Fin P.n) (sr : RoundRecord P.n)
    (sent : Fin P.n → Finset (Message P.n)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  ((Function.update (fun i => programProjection ((u i).2.roundRecord r)) j (programProjection sr),
      (w.ghostRecord r).2.2),
    (((Function.update
            (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u
              i).2.roundRecord r).firstGatherInputBroadcasts
              ((u i).2.roundRecord r).firstGatherBindBroadcasts) j
            (gatherLocalState P Bool sr.firstGather sr.firstGatherInputBroadcasts
              sr.firstGatherBindBroadcasts),
          ⟨⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj sent, w.F⟩,
            (w.ghostRecord r).1⟩),
        fun k => (Function.update (fun i => broadcastLocalState P (((u i).2.roundRecord
          r).firstGatherInputBroadcasts k)) j
            (broadcastLocalState P (sr.firstGatherInputBroadcasts k)),
          ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
            k) sent, w.F⟩),
        fun q => (Function.update (fun i => broadcastLocalState P (((u i).2.roundRecord
          r).firstGatherBindBroadcasts q)) j
            (broadcastLocalState P (sr.firstGatherBindBroadcasts q)),
          ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj
            q) sent, w.F⟩)),
      ((Function.update
            (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather
              ((u i).2.roundRecord r).secondGatherInputBroadcasts ((u i).2.roundRecord
                r).secondGatherBindBroadcasts) j
            (gatherLocalState P (Option Bool) sr.secondGather sr.secondGatherInputBroadcasts
              sr.secondGatherBindBroadcasts),
          ⟨⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj sent, w.F⟩,
            (w.ghostRecord r).2.1⟩),
        fun k => (Function.update (fun i => broadcastLocalState P (((u i).2.roundRecord
          r).secondGatherInputBroadcasts k)) j
            (broadcastLocalState P (sr.secondGatherInputBroadcasts k)),
          ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) sent, w.F⟩),
        fun q => (Function.update (fun i => broadcastLocalState P (((u i).2.roundRecord
          r).secondGatherBindBroadcasts q)) j
            (broadcastLocalState P (sr.secondGatherBindBroadcasts q)),
          ⟨messagesOf (secondGatherBindBroadcastMessageOf q) (secondGatherBindBroadcastMessageOf_inj
            q) sent, w.F⟩))))

/-- **A write, read through the view.** A row writes the acting process's round
record and records one tagged message; the round it names then reads as the
one-point update of every coordinate. -/
theorem roundProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n)
    (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n) (m : Message P.n) :
    roundProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = roundProjectionUpdate P u w r j sr
    (Function.update (w.sent r) j (insert m (w.sent r j))) := by
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, roundProjection, roundProjectionUpdate,
      roundRecord_update_self rfl, locals_programProjection_if]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, roundProjection, roundProjectionUpdate,
      firstGatherProjection, roundRecord_update_self rfl, locals_firstGatherLocalState_if]
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection, recordGBCASend_sent_self]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundRecord_update_self rfl,
        locals_firstGatherInputBroadcast_if]
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
        roundProjectionUpdate, firstGatherProjection, recordGBCASend_sent_self]
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundRecord_update_self rfl,
        locals_firstGatherBindBroadcast_if]
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
        roundProjectionUpdate, firstGatherProjection, recordGBCASend_sent_self]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, roundRecord_update_self rfl,
        locals_secondGatherLocalState_if]
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, recordGBCASend_sent_self]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundRecord_update_self rfl,
        locals_secondGatherInputBroadcast_if]
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, recordGBCASend_sent_self]
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundRecord_update_self rfl,
        locals_secondGatherBindBroadcast_if]
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, recordGBCASend_sent_self]

/-- A write that records nothing — a delivery, or a return — read through the
view. -/
theorem roundProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n) :
    roundProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr)) w r =
    roundProjectionUpdate P u w r j sr (w.sent r) := by
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, roundProjection, roundProjectionUpdate,
      roundRecord_update_self rfl, locals_programProjection_if]
  · refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, roundProjection, roundProjectionUpdate,
      firstGatherProjection, roundRecord_update_self rfl, locals_firstGatherLocalState_if]
  · funext k
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundRecord_update_self rfl,
        locals_firstGatherInputBroadcast_if]
  · funext q
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundRecord_update_self rfl,
        locals_firstGatherBindBroadcast_if]
  · refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, roundProjection, roundProjectionUpdate,
      secondGatherProjection, roundRecord_update_self rfl, locals_secondGatherLocalState_if]
  · funext k
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundRecord_update_self rfl,
        locals_secondGatherInputBroadcast_if]
  · funext q
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundRecord_update_self rfl,
        locals_secondGatherBindBroadcast_if]

end Writes
/-! ### The returned value under a local write

`broadcastReturnsFor` counts `VOTE` receipts, so a write of a local record leaves it where
it stands and a delivery is the only row that moves it. -/

section BroadcastReturns

variable {X : Type} [DecidableEq X]

/-- A local record write leaves the returned value where it stands. -/
theorem broadcastReturnsFor_setProcess (q : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X))
    (pr : BRB.ProcessRecord X) : broadcastReturnsFor P (q.setProcess pr) = broadcastReturnsFor P q
      := rfl

/-- The local record of a written local state. -/
theorem localState_setProcess_process {Pr M : Type} (q : LocalState P.n Pr M) (pr : Pr) :
    (q.setProcess pr).process = pr := rfl

/-- The delivered sets of a written local state. -/
theorem localState_setProcess_received {Pr M : Type} (q : LocalState P.n Pr M) (pr : Pr) :
    (q.setProcess pr).received = q.received := rfl

/-- The returned value reads the delivered sets alone. -/
theorem broadcastReturnsFor_mk_eq (pr : BRB.ProcessRecord X)
    (q : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) :
    broadcastReturnsFor P ({ process := pr, received := q.received } :
      LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) =
        broadcastReturnsFor P q := rfl

/-- A local record write in one instance leaves the whole family of returned values where it
stands. -/
theorem broadcastReturnsFor_update_setProcess
    (b : Fin P.n → LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) (i : Fin P.n)
    (pr : BRB.ProcessRecord X) :
    (fun k => broadcastReturnsFor P (Function.update b i ((b i).setProcess pr) k)) = fun k =>
    broadcastReturnsFor P (b k) := by
  funext k
  by_cases hk : k = i
  · subst hk; rw [Function.update_self, broadcastReturnsFor_setProcess]
  · rw [Function.update_of_ne hk]

/-- A delivery in one instance, read through the family of returned values. -/
theorem broadcastReturnsFor_update_deliverTo
    (b : Fin P.n → LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) (i k : Fin P.n)
    (m : BRB.Message X) :
    (fun k' => broadcastReturnsFor P (Function.update b i ((b i).deliverTo k m) k')) =
    Function.update (fun k' => broadcastReturnsFor P (b k')) i
    (broadcastReturnsFor P ((b i).deliverTo k m)) := by
  funext k'
  by_cases hk : k' = i
  · subst hk; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

/-- A delivery that leaves the returned value where it stands, read through the return flag. -/
theorem broadcastLocalState_deliverTo (q : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X))
    (k : Fin P.n) (m : BRB.Message X)
    (h : broadcastReturnsFor P (q.deliverTo k m) = broadcastReturnsFor P q) :
    broadcastLocalState P (q.deliverTo k m) = (broadcastLocalState P q).deliverTo k m := by
  unfold broadcastLocalState
  rw [h]
  rfl

/-- A delivery that completes a receipt quorum, read through the return flag:
the flag goes on. -/
theorem broadcastLocalState_deliverTo_ret (q : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X))
    (k : Fin P.n) (m : BRB.Message X) {v : X}
      (h : broadcastReturnsFor P (q.deliverTo k m) = some v) :
    broadcastLocalState P (q.deliverTo k m)
      = ((broadcastLocalState P q).deliverTo k m).setProcess
          { ((broadcastLocalState P q).deliverTo k m).process with returned := true } := by
  unfold broadcastLocalState LocalState.setProcess
  rw [h]
  rfl

end BroadcastReturns

/-! ### Reading the written view

The written view is read coordinate by coordinate, so that a row's remaining
obligations are stated over one local state vector or one network state at a
time. -/

section WrittenViewReaders
variable (v : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ) (j : Fin P.n)
    (sr : RoundRecord P.n) (sent : Fin P.n → Finset (Message P.n))

@[simp] theorem programs_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessRecord P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.programs (((a, bnd), (x, y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = a := rfl

@[simp] theorem bound_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessRecord P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.bound (((a, bnd), (x, y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = bnd := rfl

@[simp] theorem firstGather_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessRecord P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.firstGather (((a, bnd), (x,
      y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = x := rfl

@[simp] theorem secondGather_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessRecord P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.secondGather (((a, bnd), (x,
      y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = y := rfl

@[simp] theorem gatherTier_firstGatherProjection_fst :
    (Gather.gatherTier (firstGatherProjection P v w r)).1
      = fun i => gatherLocalState P Bool ((v i).2.roundRecord r).firstGather ((v i).2.roundRecord
        r).firstGatherInputBroadcasts
          ((v i).2.roundRecord r).firstGatherBindBroadcasts := rfl

@[simp] theorem gatherTier_secondGatherProjection_fst :
    (Gather.gatherTier (secondGatherProjection P v w r)).1
      = fun i => gatherLocalState P (Option Bool) ((v i).2.roundRecord r).secondGather ((v
        i).2.roundRecord r).secondGatherInputBroadcasts
          ((v i).2.roundRecord r).secondGatherBindBroadcasts := rfl

@[simp] theorem programs_roundProjection_eq :
    GBCA.ByAFW.programs (roundProjection P v w r) = fun i => programProjection ((v i).2.roundRecord
      r) := rfl

@[simp] theorem programs_roundProjectionUpdate :
    GBCA.ByAFW.programs (roundProjectionUpdate P v w r j sr sent)
      = Function.update (fun i => programProjection ((v i).2.roundRecord r)) j (programProjection
        sr) := rfl

@[simp] theorem bound_roundProjectionUpdate :
    GBCA.ByAFW.bound (roundProjectionUpdate P v w r j sr sent) = (w.ghostRecord r).2.2 := rfl

@[simp] theorem core_firstGather_roundProjectionUpdate :
    Gather.core (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent)) = (w.ghostRecord
      r).1 := rfl

@[simp] theorem core_secondGather_roundProjectionUpdate :
    Gather.core (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent)) = (w.ghostRecord
      r).2.1 := rfl

@[simp] theorem gatherTier_firstGather_roundProjectionUpdate :
    Gather.gatherTier (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent))
      = (Function.update (fun i => gatherLocalState P Bool ((v i).2.roundRecord r).firstGather
            ((v i).2.roundRecord r).firstGatherInputBroadcasts ((v i).2.roundRecord
              r).firstGatherBindBroadcasts) j
          (gatherLocalState P Bool sr.firstGather sr.firstGatherInputBroadcasts
            sr.firstGatherBindBroadcasts),
        ⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj sent, w.F⟩) := rfl

@[simp] theorem gatherTier_secondGather_roundProjectionUpdate :
    Gather.gatherTier (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent))
      = (Function.update (fun i => gatherLocalState P (Option Bool) ((v i).2.roundRecord
        r).secondGather
            ((v i).2.roundRecord r).secondGatherInputBroadcasts ((v i).2.roundRecord
              r).secondGatherBindBroadcasts) j
          (gatherLocalState P (Option Bool) sr.secondGather sr.secondGatherInputBroadcasts
            sr.secondGatherBindBroadcasts),
        ⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj sent, w.F⟩) := rfl

@[simp] theorem inputBroadcasts_firstGather_roundProjectionUpdate (k : Fin P.n) :
    Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent)) k
      = (Function.update (fun i => broadcastLocalState P (((v i).2.roundRecord
        r).firstGatherInputBroadcasts k)) j
          (broadcastLocalState P (sr.firstGatherInputBroadcasts k)),
            ⟨messagesOf (firstGatherInputBroadcastMessageOf k)
              (firstGatherInputBroadcastMessageOf_inj k) sent, w.F⟩) := rfl

@[simp] theorem bindBroadcasts_firstGather_roundProjectionUpdate (q : Fin P.n) :
    Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent)) q
      = (Function.update (fun i => broadcastLocalState P (((v i).2.roundRecord
        r).firstGatherBindBroadcasts q)) j
          (broadcastLocalState P (sr.firstGatherBindBroadcasts q)),
            ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj
              q) sent, w.F⟩) := rfl

@[simp] theorem inputBroadcasts_secondGather_roundProjectionUpdate (k : Fin P.n) :
    Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent)) k
      = (Function.update (fun i => broadcastLocalState P (((v i).2.roundRecord
        r).secondGatherInputBroadcasts k)) j
          (broadcastLocalState P (sr.secondGatherInputBroadcasts k)),
            ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
              (secondGatherInputBroadcastMessageOf_inj k) sent, w.F⟩) := rfl

@[simp] theorem bindBroadcasts_secondGather_roundProjectionUpdate (q : Fin P.n) :
    Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent)) q
      = (Function.update (fun i => broadcastLocalState P (((v i).2.roundRecord
        r).secondGatherBindBroadcasts q)) j
          (broadcastLocalState P (sr.secondGatherBindBroadcasts q)),
            ⟨messagesOf (secondGatherBindBroadcastMessageOf q)
              (secondGatherBindBroadcastMessageOf_inj q) sent, w.F⟩) := rfl

end WrittenViewReaders
end AFW
end ABA
end PLTS
