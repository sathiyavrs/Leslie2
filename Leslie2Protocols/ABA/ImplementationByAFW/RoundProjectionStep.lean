/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndErasures
import Leslie2Protocols.ABA.ImplementationByAFW.RoundProjection

/-!
# The view of the composed round after one implementation row

`AFW.roundProjection` (`ABA/ImplementationByAFW/RoundProjection.lean`) computes the round-`r` state
of the composed system from a state of `AFW.protocol P`. This file says where that
state stands after one row of the implementation: for each row, the view after
the row is the view before the row with the composed round's own effect
applied, written through the updaters `GBCA.ByAFW.setPrograms`, `GBCA.ByAFW.setBound`,
`GBCA.ByAFW.setFirstGather`, `GBCA.ByAFW.setSecondGather`, `Gather.setGatherTier`,
`Gather.setInputBroadcasts`, `Gather.setBindBroadcasts` and `Gather.setCore` exactly as the composed
rows write them.

## One written record, transposed

A row writes the acting process's round record and records at most one tagged
message. `roundProjection_write` and `roundProjection_writeNoSent` do that write once, through
`roundProjectionUpdate`: each local state vector becomes a one-point update of the old
one, and each network state is sliced out of the written sent family. What each
row still owes is then sent algebra alone, which `messagesOf_recordSent_some` and
`messagesOf_recordSent_none` supply.

## Three rows against two events

Three rows of the implementation are answered by two events of the composed round. The
return-then-call step is `firstGatherReturn` and `secondGatherCall`:
`roundProjection_firstGatherReturn_secondGatherCall` states the view after it as
`afterSecondGatherCall` of `afterFirstGatherReturn`, and `afterFirstGatherReturn` is the round after
the first event alone. The graded return is `secondGatherReturn` and `retG`, with
`afterSecondGatherReturn` the intermediate state. A delivery that completes a `2f + 1` `VOTE` quorum
is the broadcast instance's `deliver` and then the gather's `inputBroadcastRet` (or `bindRet`), with
`afterFirstGatherInputBroadcastDeliver` and its three companions the intermediate states.

## The returned value and the return flag

`broadcastReturnsFor` reads the delivered sets, so a broadcast delivery moves two coordinates of the
view at once. The instance's local state takes the message. And where the delivery completes the
receiver's `2f + 1` `VOTE` quorum, the receiver's return flag in that instance goes on and what the
receiver's gather instance returned records the value. The quorum lemmas
(`roundProjection_deliverFirstGatherInputBroadcast_ret` and its three companions) carry the
hypothesis that the returned value holds `v` after the delivery; the plain lemmas
(`roundProjection_deliverFirstGatherInputBroadcast` and its companions) carry the hypothesis that
the returned value does not move. `AFW.broadcastReturnsFor_eq_of_quorum` identifies the returned
value with the value an implementation receipt quorum carries, which is what supplies those
hypotheses under `AFW.BroadcastReturnsInvariant`.

## The two clauses that are not projections

`BroadcastReturnsInvariant` and `BoundInvariant` are the conjuncts of `AFW.ProtocolRelation` that no
frame lemma supplies. `broadcastReturnsInvariant_of` carries the first across a row from the
moves of the round's `4n` broadcast instances, each an application of
`BRB.Invariant.step`, and `broadcastReturnsInvariant_congr` covers a row that leaves every round's
view where it stands. `boundInvariant_writeGhost` carries the second.
-/

set_option linter.style.longFile 3800

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

/-! ### Slicing a tagged sent -/

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

/-- A sent message of the tag being sliced arrives in that messagesOf. -/
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

section Locals

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

end Locals

/-! ### The view after one write

A row of the implementation writes one component of the acting process's round
record and records at most one tagged message. The two lemmas below are that
write read through the view: each local state vector becomes a one-point
update, and each network state is sliced out of the written sent family. What
every row still owes is then sent algebra alone. -/

section Frame

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-- The view after a write, with the one-point update pushed inside every
coordinate: the acting process's local state replaced in each local state
vector, and each network state sliced out of the written sent. The two cores
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

end Frame

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

section UpdReaders

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

end UpdReaders

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### A send of a gather instance

A gather's `ECHO` and `VOTE` write the sender's gather record and record on the
gather's network state. Each is the gather's `send` event, which
`Gather.StepOverBracha.echo` and `Gather.StepOverBracha.vote` write through
`Gather.setGatherTier`. -/

/-- A send of the first gather, read through the view. -/
theorem roundProjection_firstGatherSend (hu : (u j).2 = p) (r : ℕ)
    (pr : Gather.BaseProcessRecord P.n Bool) (m : Gather.Message P.n Bool)
    (hin : pr.input = ((p.roundRecord r).firstGather.process).input) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with firstGather := (p.roundRecord r).firstGather.setProcess pr }))
      (w.recordGBCASend r j (.firstGather m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r)
            (((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { pr with
                  inputBroadcastReturned := fun k => broadcastReturnsFor P ((p.roundRecord
                    r).firstGatherInputBroadcasts k)
                  bindBroadcastReturned := fun q => broadcastReturnsFor P ((p.roundRecord
                    r).firstGatherBindBroadcasts q) }).multicast j m)) := by
  rw [← hu] at hin ⊢
  rw [roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
      roundProjectionUpdate, programProjection, LocalState.setProcess, hin]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        gatherLocalState, InstanceState.multicast, InstanceState.setProcess, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        InstanceState.multicast, ABA.NetworkState.recordSent]
      exact messagesOf_recordSent_some firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGather m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
        (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGather m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGather m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none
          (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj k)
            (w.sent r) j (.firstGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          q) (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGather m) rfl

/-- A send of the second gather, read through the view. -/
theorem roundProjection_secondGatherSend (hu : (u j).2 = p) (r : ℕ)
    (pr : Gather.BaseProcessRecord P.n (Option Bool)) (m : Gather.Message P.n (Option Bool))
    (hin : pr.input = ((p.roundRecord r).secondGather.process).input)
    (hret : pr.returned = ((p.roundRecord r).secondGather.process).returned) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with secondGather := (p.roundRecord r).secondGather.setProcess pr }))
      (w.recordGBCASend r j (.secondGather m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r)
            (((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { pr with
                  inputBroadcastReturned := fun k => broadcastReturnsFor P ((p.roundRecord
                    r).secondGatherInputBroadcasts k)
                  bindBroadcastReturned := fun q => broadcastReturnsFor P ((p.roundRecord
                    r).secondGatherBindBroadcasts q) }).multicast j m)) := by
  rw [← hu] at hin hret ⊢
  rw [roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
      roundProjectionUpdate, programProjection, LocalState.setProcess, hin, hret]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf
          firstGatherMessageOf_inj (w.sent r) j (.secondGather m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          q) (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.secondGather m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        gatherLocalState, InstanceState.multicast, InstanceState.setProcess, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        InstanceState.multicast, ABA.NetworkState.recordSent]
      exact messagesOf_recordSent_some secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGather m) m rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGather m) rfl
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setGatherTier, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
        (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.secondGather m) rfl

/-! ### A send in a broadcast instance

A Bracha row writes the sender's local state in one broadcast instance and records on that
instance's network state. Each is the instance's `send` event, which `BRB.BrachaStep.echo`,
`BRB.BrachaStep.voteQuorum` and `BRB.BrachaStep.voteAmplification` write, and the composed round
reaches it through `Gather.setInputBroadcasts` or `Gather.setBindBroadcasts`. The return flag the
view supplies is the returned value's, which a local write does not move. -/

/-- A send in an input-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherInputBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord Bool) (m : BRB.Message Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            i
            (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.firstGatherInputBroadcasts i m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).firstGatherInputBroadcasts
                        i)).isSome }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherInputBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.firstGatherInputBroadcasts k m) m (by simp [firstGatherInputBroadcastMessageOf])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts i m)
          (by simp [firstGatherInputBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k)
        (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts i m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGatherInputBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none
          (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj k)
            (w.sent r) j (.firstGatherInputBroadcasts i m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          k) (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts i
            m)
          rfl

/-- A send in a bind-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherBindBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord (Gather.AcceptedPairs P.n Bool)) (m : BRB.Message (Gather.AcceptedPairs
      P.n Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts i
            (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.firstGatherBindBroadcasts i m)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).firstGatherBindBroadcasts i)).isSome
                        }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
        gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherBindBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
      GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j
          (.firstGatherBindBroadcasts k m) m (by simp [firstGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts i m)
          (by simp [firstGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.firstGather,
        GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate, firstGatherProjection,
          Function.update_of_ne hk]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGatherBindBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none
          (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj k)
            (w.sent r) j (.firstGatherBindBroadcasts i m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          k) (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts i
            m) rfl

/-- A send in an input-broadcast instance of the second gather, read through
the view. -/
theorem roundProjection_secondGatherInputBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord (Option Bool)) (m : BRB.Message (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts i
            (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.secondGatherInputBroadcasts i m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).secondGatherInputBroadcasts
                        i)).isSome }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf
          firstGatherMessageOf_inj (w.sent r) j (.secondGatherInputBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i
            m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          k) (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i
            m)
          rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherInputBroadcasts i m) rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherInputBroadcasts k m) m (by simp [secondGatherInputBroadcastMessageOf])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i
            m)
          (by simp [secondGatherInputBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.inputBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, Gather.setInputBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k)
        (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherInputBroadcasts i m)
          rfl

/-- A send in a bind-broadcast instance of the second gather, read through the
view. -/
theorem roundProjection_secondGatherBindBroadcastSend (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (pr : BRB.ProcessRecord (Gather.AcceptedPairs P.n (Option Bool)))
    (m : BRB.Message (Gather.AcceptedPairs P.n (Option Bool))) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            i
            (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess pr) }))
      (w.recordGBCASend r j (.secondGatherBindBroadcasts i m)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { pr with
                    returned :=
                      (broadcastReturnsFor P ((p.roundRecord r).secondGatherBindBroadcasts
                        i)).isSome }).multicast
                j m))) := by
  rw [← hu, roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf
          firstGatherMessageOf_inj (w.sent r) j (.secondGatherBindBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i
            m)
          rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          k) (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i
            m) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
        gatherLocalState, broadcastReturnsFor_update_setProcess]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherBindBroadcasts i m) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
      GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i m)
          rfl
  · funext k
    by_cases hk : k = i
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
            broadcastLocalState,
        LocalState.setProcess, broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherBindBroadcasts k m) m (by simp [secondGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_self, InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]
        exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts i m)
          (by simp [secondGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, GBCA.ByAFW.secondGather,
        GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate, secondGatherProjection,
          Function.update_of_ne hk]

/-! ### The rows of the two gathers and of the broadcast instances

Each row below is one implementation row, read through the view over the effect the
composed round's own row writes. -/

/-- The first gather's `ECHO`, read through the view. -/
theorem roundProjection_firstGatherEcho (hu : (u j).2 = p) (r : ℕ)
    (A : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with sentEcho := some A } }))
      ((w.recordGBCASend r j (.firstGather (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGather (.echo A))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r)
            (((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                  sentEcho :=
                    some A }).multicast
              j (.echo A))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGather (.echo A)))) (fun _ _ => rfl)]
  exact roundProjection_firstGatherSend rfl r _ (.echo A) rfl

/-- The first gather's `VOTE`, read through the view. -/
theorem roundProjection_firstGatherVote (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with sentVote := some U } }))
      ((w.recordGBCASend r j (.firstGather (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGather (.vote U))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r)
            (((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                  sentVote :=
                    some U }).multicast
              j (.vote U))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGather (.vote U)))) (fun _ _ => rfl)]
  exact roundProjection_firstGatherSend rfl r _ (.vote U) rfl

/-- The second gather's `ECHO`, read through the view. -/
theorem roundProjection_secondGatherEcho (hu : (u j).2 = p) (r : ℕ)
    (A : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with sentEcho := some A } }))
      ((w.recordGBCASend r j (.secondGather (.echo A))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGather (.echo A))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r)
            (((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (secondGatherProjection P u w r)).process j with
                  sentEcho :=
                    some A }).multicast
              j (.echo A))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGather (.echo A)))) (fun _ _ => rfl)]
  exact roundProjection_secondGatherSend rfl r _ (.echo A) rfl rfl

/-- The second gather's `VOTE`, read through the view. -/
theorem roundProjection_secondGatherVote (hu : (u j).2 = p) (r : ℕ)
    (U : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with sentVote := some U } }))
      ((w.recordGBCASend r j (.secondGather (.vote U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGather (.vote U))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r)
            (((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (secondGatherProjection P u w r)).process j with
                  sentVote :=
                    some U }).multicast
              j (.vote U))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGather (.vote U)))) (fun _ _ => rfl)]
  exact roundProjection_secondGatherSend rfl r _ (.vote U) rfl rfl

/-- The first gather's `BIND`, read through the view: the payload is written to
the sender's gather record and is the input of the sender's own bind-broadcast
instance, which broadcasts it. -/
theorem roundProjection_firstGatherBind (hu : (u j).2 = p) (r : ℕ) (U : Gather.AcceptedPairs P.n
  Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with sentBind := some U }
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts j
            (((p.roundRecord r).firstGatherBindBroadcasts j).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts j).process) with input := some U })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts
            (Gather.setGatherTier (firstGatherProjection P u w r)
              ((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with
                  sentBind :=
                    some U }))
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) j).setProcess j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) j).process j with
                    input := some U }).multicast
                j (.init U)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))
    (fun _ _ => rfl),
    roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setFirstGather, roundProjection,
    roundProjectionUpdate, programProjection,
      LocalState.setProcess]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection, gatherLocalState, broadcastReturnsFor_update_setProcess]
      simp only [InstanceState.setProcess, InstanceState.process, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherBindBroadcasts j (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts j (.init
          U)) rfl
  · funext k
    by_cases hk : k = j
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_self, InstanceState.multicast,
            InstanceState.setProcess,
        InstanceState.process, broadcastLocalState, LocalState.setProcess,
          broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_self, InstanceState.multicast,
            ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) k
          (.firstGatherBindBroadcasts k (.init U)) (.init U) (by simp
            [firstGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_self, InstanceState.multicast,
            InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_of_ne hk]
        exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k)
          (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts j
            (.init U))
          (by simp [firstGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.firstGather, GBCA.ByAFW.setFirstGather, roundProjection, roundProjectionUpdate,
          firstGatherProjection, Function.update_of_ne hk]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf
          secondGatherMessageOf_inj (w.sent r) j (.firstGatherBindBroadcasts j (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none
          (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj k)
            (w.sent r) j (.firstGatherBindBroadcasts j
          (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, GBCA.ByAFW.setFirstGather,
      roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf
          k) (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherBindBroadcasts j
            (.init
          U)) rfl

/-- The second gather's `BIND`, read through the view. -/
theorem roundProjection_secondGatherBind (hu : (u j).2 = p) (r : ℕ) (U : Gather.AcceptedPairs P.n
  (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with sentBind := some U }
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            j
            (((p.roundRecord r).secondGatherBindBroadcasts j).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts j).process) with input := some U })
                }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts j (.init U))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts
            (Gather.setGatherTier (secondGatherProjection P u w r)
              ((Gather.gatherTier (secondGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (secondGatherProjection P u w r)).process j with
                  sentBind :=
                    some U }))
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) j
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) j).setProcess j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) j).process j with
                    input := some U }).multicast
                j (.init U)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))
    (fun _ _ => rfl),
    roundProjection_write]
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, GBCA.ByAFW.setSecondGather, roundProjection,
    roundProjectionUpdate, programProjection,
      LocalState.setProcess]
    exact Function.update_eq_self _ _
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.gatherTier, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none firstGatherMessageOf
          firstGatherMessageOf_inj (w.sent r) j (.secondGatherBindBroadcasts j (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf
          k) (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
          (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, GBCA.ByAFW.setSecondGather,
      roundProjection, roundProjectionUpdate,
        firstGatherProjection]
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf
          k) (firstGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
            (.init
          U)) rfl
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection, gatherLocalState, broadcastReturnsFor_update_setProcess]
      simp only [InstanceState.setProcess, InstanceState.process, LocalState.setProcess]
    · simp only [Gather.gatherTier, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
        (.secondGatherBindBroadcasts j (.init U)) rfl
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact Function.update_eq_self _ _
    · simp only [Gather.inputBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
      GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection, roundProjectionUpdate,
        secondGatherProjection]
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
          (.init U)) rfl
  · funext k
    by_cases hk : k = j
    · subst hk
      refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_self,
            InstanceState.multicast, InstanceState.setProcess,
        InstanceState.process, broadcastLocalState, LocalState.setProcess,
          broadcastReturnsFor_mk_eq]
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_self,
            InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) k
          (.secondGatherBindBroadcasts k (.init U)) (.init U) (by simp
            [secondGatherBindBroadcastMessageOf])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_self,
            InstanceState.multicast, InstanceState.setProcess,
        ABA.NetworkState.recordSent]
    · refine Prod.ext ?_ (networkState_ext ?_ ?_)
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_of_ne hk]
        exact Function.update_eq_self _ _
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_of_ne hk]
        exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k)
          (secondGatherBindBroadcastMessageOf_inj k) (w.sent r) j (.secondGatherBindBroadcasts j
            (.init U))
          (by simp [secondGatherBindBroadcastMessageOf, Ne.symm hk])
      · simp only [Gather.bindBroadcasts, Gather.setBindBroadcasts, Gather.setGatherTier,
        GBCA.ByAFW.secondGather, GBCA.ByAFW.setSecondGather, roundProjection,
          roundProjectionUpdate, secondGatherProjection, Function.update_of_ne hk]

/-- `ECHO` in an input-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherInputBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            i
            (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the first gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem roundProjection_firstGatherInputBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            i
            (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherInputBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the first gather, read through the
view. -/
theorem roundProjection_firstGatherBindBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts i
            (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentEcho := some m })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the first gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem roundProjection_firstGatherBindBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts i
            (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentVote := some m })
                }))
      ((w.recordGBCASend r j (.firstGatherBindBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (firstGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (firstGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_firstGatherBindBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in an input-broadcast instance of the second gather, read through
the view. -/
theorem roundProjection_secondGatherInputBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts i
            (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in an input-broadcast instance of the second gather, read through
the view. The quorum row and the amplification row write this record. -/
theorem roundProjection_secondGatherInputBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts i
            (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.inputBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.inputBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherInputBroadcastSend rfl r i _ (.vote m)

/-- `ECHO` in a bind-broadcast instance of the second gather, read through the
view. -/
theorem roundProjection_secondGatherBindBroadcastEcho (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            i
            (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentEcho := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts i (.echo m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentEcho := some m }).multicast
                j (.echo m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r i _ (.echo m)

/-- `VOTE` in a bind-broadcast instance of the second gather, read through the
view. The quorum row and the amplification row write this record. -/
theorem roundProjection_secondGatherBindBroadcastVote (hu : (u j).2 = p) (r : ℕ) (i : Fin P.n)
    (m : Gather.AcceptedPairs P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          secondGatherBindBroadcasts := Function.update (p.roundRecord r).secondGatherBindBroadcasts
            i
            (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
              { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentVote := some m
                }) }))
      ((w.recordGBCASend r j (.secondGatherBindBroadcasts i (.vote m))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              (((Gather.bindBroadcasts (secondGatherProjection P u w r) i).setProcess j
                  { (Gather.bindBroadcasts (secondGatherProjection P u w r) i).process j with
                    sentVote := some m }).multicast
                j (.vote m)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))
    (fun _ _ => rfl)]
  exact roundProjection_secondGatherBindBroadcastSend rfl r i _ (.vote m)

/-! ### The graded-agreement call and its loop

The call is fused (D28): the round's first gather records the input and the
caller's own input-broadcast instance of that gather is called with it. The
composed round answers on one label, whose program row records the input and
whose first gather takes `Gather.StepOverBracha.call`. The call against an
already-called record moves the round loop alone, which the view does not
read. -/

/-- The graded-agreement call, read through the view. -/
theorem roundProjection_callG (hu : (u j).2 = p) (r : ℕ) (b : Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with input := some b }
          firstGatherInputBroadcasts := Function.update (p.roundRecord r).firstGatherInputBroadcasts
            j
            (((p.roundRecord r).firstGatherInputBroadcasts j).setProcess
              { (((p.roundRecord r).firstGatherInputBroadcasts j).process) with input := some b })
                }))
      ((w.recordGBCASend r j (.firstGatherInputBroadcasts j (.init b))).writeGhost (ghostStep P)
        (Sum.inl (.callG r j b))) r
      = GBCA.ByAFW.setFirstGather (GBCA.ByAFW.setPrograms (roundProjection P u w r)
            (Function.update (GBCA.ByAFW.programs (roundProjection P u w r)) j
              { GBCA.ByAFW.programs (roundProjection P u w r) j with input := some b }))
          (Gather.setInputBroadcasts (Gather.setGatherTier (firstGatherProjection P u w r)
              ((Gather.gatherTier (firstGatherProjection P u w r)).setProcess j
                { (Gather.gatherTier (firstGatherProjection P u w r)).process j with input := some b
                  }))
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) j
              (((Gather.inputBroadcasts (firstGatherProjection P u w r) j).setProcess j
                  { (Gather.inputBroadcasts (firstGatherProjection P u w r) j).process j with
                    input := some b }).multicast j (.init b)))) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inl (.callG r j b)) (fun _ _ => rfl), roundProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
    (stateOverBroadcasts_ext ?_ ?_ ?_ ?_)
  · simp only [programs_roundProjectionUpdate, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setPrograms, programs_roundProjection_eq]
    refine congrArg (Function.update (fun i => programProjection ((u i).2.roundRecord r)) j) ?_
    simp only [programProjection, LocalState.setProcess]
  · simp
  · simp only [gatherTier_firstGather_roundProjectionUpdate, GBCA.ByAFW.firstGather_setFirstGather,
    Gather.gatherTier_setInputBroadcasts,
      Gather.gatherTier_setGatherTier]
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [InstanceState.setProcess]
      refine congrArg (Function.update
        (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
          r).firstGatherInputBroadcasts
          ((u i).2.roundRecord r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_setProcess, InstanceState.process,
        gatherTier_firstGatherProjection_process, localState_setProcess_process,
          localState_setProcess_received]
      simp only [LocalState.setProcess]
    · exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
        (.firstGatherInputBroadcasts j (.init b)) rfl
  · funext k
    simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_firstGatherProjection]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self, Function.update_self]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.multicast, InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => broadcastLocalState P (((u i).2.roundRecord r).firstGatherInputBroadcasts k)) k)
            ?_
        simp only [InstanceState.process, broadcastLocalState, LocalState.setProcess,
          broadcastReturnsFor_mk_eq]
      · simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf k)
          (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) k
          (.firstGatherInputBroadcasts k (.init b)) (.init b) (by simp
            [firstGatherInputBroadcastMessageOf])
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts j
          (.init b))
        (by simp [firstGatherInputBroadcastMessageOf, Ne.symm hk])
  · funext q
    simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
      GBCA.ByAFW.firstGather_setFirstGather, Gather.bindBroadcasts_setInputBroadcasts,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
      (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · simp
  · simp only [gatherTier_secondGather_roundProjectionUpdate,
    GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
      secondGather_roundProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext
        ?_ rfl)
    exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) j
      (.firstGatherInputBroadcasts j (.init b)) rfl
  · funext k
    simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, inputBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
      (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · funext q
    simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
      GBCA.ByAFW.secondGather_setFirstGather, GBCA.ByAFW.secondGather_setPrograms,
        secondGather_roundProjection, bindBroadcasts_secondGatherProjection]
    refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
    exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
      (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j (.firstGatherInputBroadcasts j (.init
        b)) rfl
  · simp

/-- The graded-agreement call against an already-called record, read through
the view: the round loop moves and the view is unchanged. -/
theorem roundProjection_gbcaCallLoop (hu : (u j).2 = p) (r r' : ℕ) (b : Bool)
    (c' : RoundLoopRecord P.n) :
    roundProjection P (Function.update u j (c', p))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaCallLoop r j b))) r' = roundProjection P u w r' := by
  rw [roundProjection_ghostId (Sum.inr (.gbcaCallLoop r j b)) (fun _ _ => rfl)]
  refine roundProjection_congr (fun i => ?_)
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, ← hu]
  · rw [Function.update_of_ne hi]

/-! ### The return-then-call step and the graded return

The return-then-call step is answered by two events, `firstGatherReturn` and `secondGatherCall`; the
graded return by `secondGatherReturn` and `retG`. Each pair is stated as one equation with the two
effects composed, and the state between them is named so that a run can be built through it. -/

/-- The view of one gather instance after a write. -/
theorem firstGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n)
    (m : Message P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.firstGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_write u w j c r sr m)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n)
    (m : Message P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr))
    (w.recordGBCASend r j m) r = GBCA.ByAFW.secondGather
    (roundProjectionUpdate P u w r j sr (Function.update (w.sent r) j (insert m (w.sent r j)))) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_write u w j c r sr m)

/-- The core the first gather's return carries: the one on record, and the core
of the gather's network state where none is on record. -/
noncomputable def firstGatherReturnCore (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) :
    Gather.AcceptedPairs P.n Bool :=
  (Gather.core (GBCA.ByAFW.firstGather s)).getD (Gather.coreOfNetwork P (Gather.gatherTier
    (GBCA.ByAFW.firstGather s)).2)

/-- The core the second gather's return carries. -/
noncomputable def secondGatherReturnCore (P : Parameters)
  (s : GBCA.ByAFW.RoundStateOverBracha P.n) :
    Gather.AcceptedPairs P.n (Option Bool) :=
  (Gather.core (GBCA.ByAFW.secondGather s)).getD (Gather.coreOfNetwork P (Gather.gatherTier
    (GBCA.ByAFW.secondGather s)).2)

/-- **The round after the first gather's return to `j` over `g`**: the program
records the candidate, the round's bound bit is written from the core the
return carries, and the first gather takes `Gather.StepOverBracha.ret`. -/
noncomputable def afterFirstGatherReturn (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (g : Fin P.n → Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather
    (GBCA.ByAFW.setBound
      (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
        { GBCA.ByAFW.programs s j with candidate := some (GBCA.candidate P g) }))
      (some ((GBCA.ByAFW.bound s).getD (GBCA.boundOfCore P (firstGatherReturnCore P s)))))
    (Gather.setCore
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with returned := true }))
      (some (firstGatherReturnCore P s)))

/-- **The round after `j`'s call of the second gather with `x`**: the program
marks the call and the second gather takes `Gather.StepOverBracha.call`. -/
noncomputable def afterSecondGatherCall (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (x : Option Bool) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with secondGatherCalled := true }))
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with input := some x }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) j
        (((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) j).setProcess j
            { (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) j).process j with input := some x
              }).multicast
          j (.init x))))

/-- **The round after the second gather's return to `j` over `g`**: the program
records the grade and the second gather takes `Gather.StepOverBracha.ret`. -/
noncomputable def afterSecondGatherReturn (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n)
  (j : Fin P.n)
    (g : Fin P.n → Option (Option Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather
    (GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
      { GBCA.ByAFW.programs s j with output := some (GBCA.gradeOf P g) }))
    (Gather.setCore
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with returned := true }))
      (some (secondGatherReturnCore P s)))

/-- **The round after its graded return to `j`**: the program announces the
grade and marks the record returned. -/
def afterRetG (P : Parameters) (s : GBCA.ByAFW.RoundStateOverBracha P.n) (j : Fin P.n) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setPrograms s (Function.update (GBCA.ByAFW.programs s) j
    { GBCA.ByAFW.programs s j with output := none, returned := true })

/-- **The return-then-call step, read through the view.** The first gather returns to `j`, which
records the candidate and calls the second gather with it; the round's bound bit is written from the
core the return carries. -/
theorem roundProjection_firstGatherReturn_secondGatherCall (hu : (u j).2 = p) (r : ℕ) (g : Fin P.n →
  Option Bool) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r
        { p.roundRecord r with
          firstGather := (p.roundRecord r).firstGather.setProcess
            { ((p.roundRecord r).firstGather.process) with returned := true }
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with input := some (GBCA.candidate P g) }
          secondGatherInputBroadcasts := Function.update (p.roundRecord
            r).secondGatherInputBroadcasts j
            (((p.roundRecord r).secondGatherInputBroadcasts j).setProcess
              { (((p.roundRecord r).secondGatherInputBroadcasts j).process) with
                input := some (GBCA.candidate P g) }) }))
      ((w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init (GBCA.candidate P
        g)))).writeGhost (ghostStep P)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g)))))) r
      = afterSecondGatherCall P (afterFirstGatherReturn P (roundProjection P u w r) j g) j
        (GBCA.candidate P g) := by
  subst hu
  have hcore : Gather.coreOf P
      (firstGatherOf P (w.recordGBCASend r j (.secondGatherInputBroadcasts j (.init (GBCA.candidate
        P g)))) r)
      = Gather.coreOfNetwork P (Gather.gatherTier (firstGatherProjection P u w r)).2 := by
    rw [coreOfNetwork_firstGatherProjection]
    refine Gather.coreOf_networkState_only _ _ (networkState_ext ?_ rfl)
    simp only [firstGatherOf, recordGBCASend_sent_self]
    exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
      (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
  rw [roundProjection_gbcaSendGhost, firstGatherProjection_write, secondGatherProjection_write]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherCall, afterFirstGatherReturn, GBCA.ByAFW.programs_setSecondGather,
    GBCA.ByAFW.programs_setPrograms, GBCA.ByAFW.programs_setFirstGather,
      GBCA.ByAFW.programs_setBound, programs_roundProjection_eq, Function.update_idem,
    roundRecord_update_self rfl, locals_programProjection_if, Function.update_self]
    simp only [programs_mk, programProjection, LocalState.setProcess, Option.isSome_some]
  · simp only [afterSecondGatherCall, afterFirstGatherReturn, GBCA.ByAFW.bound_setSecondGather,
    GBCA.ByAFW.bound_setPrograms, GBCA.ByAFW.bound_setFirstGather, GBCA.ByAFW.bound_setBound,
      bound_roundProjection, firstGatherReturnCore, firstGather_roundProjection,
        core_firstGatherProjection]
    simp only [bound_mk, ghostStep, hcore]
  · simp only [afterSecondGatherCall, afterFirstGatherReturn,
    GBCA.ByAFW.firstGather_setSecondGather, GBCA.ByAFW.firstGather_setPrograms,
      GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    simp only [firstGather_mk]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, gatherTier_firstGather_roundProjectionUpdate,
      Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
            r).firstGatherInputBroadcasts
            ((u i).2.roundRecord r).firstGatherBindBroadcasts) j) ?_
        simp only [gatherLocalState, InstanceState.process,
          gatherTier_firstGatherProjection_process, localState_setProcess_process,
            localState_setProcess_received]
        simp only [LocalState.setProcess]
      · exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) j
          (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherTier, inputBroadcasts_firstGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k)
        (firstGatherInputBroadcastMessageOf_inj k) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf q)
        (firstGatherBindBroadcastMessageOf_inj q) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · simp only [Gather.core_setCore, firstGatherReturnCore, firstGather_roundProjection,
      core_firstGatherProjection]
      simp only [ghostStep, hcore]
  · simp only [afterSecondGatherCall, afterFirstGatherReturn,
    GBCA.ByAFW.secondGather_setSecondGather, GBCA.ByAFW.secondGather_setPrograms,
      GBCA.ByAFW.secondGather_setBound, GBCA.ByAFW.secondGather_setFirstGather,
        secondGather_roundProjection]
    simp only [secondGather_mk]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, Gather.gatherTier_setInputBroadcasts,
      Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ (networkState_ext ?_ rfl)
      · simp only [InstanceState.setProcess]
        refine congrArg (Function.update
          (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
            i).2.roundRecord r).secondGatherInputBroadcasts
            ((u i).2.roundRecord r).secondGatherBindBroadcasts) j) ?_
        simp only [gatherLocalState, broadcastReturnsFor_update_setProcess, InstanceState.process,
          gatherTier_secondGatherProjection_process, localState_setProcess_process,
            localState_setProcess_received]
        simp only [LocalState.setProcess]
      · exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r)
          j
          (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_self]
        refine Prod.ext ?_ (networkState_ext ?_ rfl)
        · simp only [InstanceState.multicast, InstanceState.setProcess]
          refine congrArg (Function.update
            (fun i => broadcastLocalState P (((u i).2.roundRecord r).secondGatherInputBroadcasts k))
              k) ?_
          simp only [InstanceState.process, broadcastLocalState, LocalState.setProcess,
            broadcastReturnsFor_mk_eq]
        · simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
          exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) k
            (.secondGatherInputBroadcasts k (.init (GBCA.candidate P g))) (.init (GBCA.candidate P
              g)) (by simp [secondGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k)
          (secondGatherInputBroadcastMessageOf_inj k) (w.sent r) j
          (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) (by simp
            [secondGatherInputBroadcastMessageOf, Ne.symm hk])
    · funext q
      simp only [Gather.bindBroadcasts_setCore, Gather.bindBroadcasts_setInputBroadcasts,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_secondGather_roundProjectionUpdate,
          bindBroadcasts_secondGatherProjection]
      refine Prod.ext (Function.update_eq_self _ _) (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf q)
        (secondGatherBindBroadcastMessageOf_inj q) (w.sent r) j
        (.secondGatherInputBroadcasts j (.init (GBCA.candidate P g))) rfl
    · simp only [Gather.core_setCore, Gather.core_setInputBroadcasts, Gather.core_setGatherTier,
      core_secondGatherProjection]
      simp only [ghostStep]

/-- The view of the first gather instance after a write that records
nothing. -/
theorem firstGatherProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n) :
    firstGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr)) w r =
    GBCA.ByAFW.firstGather (roundProjectionUpdate P u w r j sr (w.sent r)) :=
  congrArg GBCA.ByAFW.firstGather (roundProjection_writeNoSent u w j c r sr)

/-- The same at the second gather instance. -/
theorem secondGatherProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopRecord P.n) (r : ℕ) (sr : RoundRecord P.n) :
    secondGatherProjection P (Function.update u j (c, (u j).2.setRoundRecord r sr)) w r =
    GBCA.ByAFW.secondGather (roundProjectionUpdate P u w r j sr (w.sent r)) :=
  congrArg GBCA.ByAFW.secondGather (roundProjection_writeNoSent u w j c r sr)

/-- **The graded return, read through the view.** The second gather returns to
`j`, which records the grade and announces it; the round's return clears the
record and marks it returned. -/
theorem roundProjection_secondGatherReturn_retG (hu : (u j).2 = p) (r : ℕ)
    (g : Fin P.n → Option (Option Bool)) (c' : RoundLoopRecord P.n) (bnd : Bool) :
    roundProjection P (Function.update u j (c', p.setRoundRecord r
        { p.roundRecord r with
          secondGather := (p.roundRecord r).secondGather.setProcess
            { ((p.roundRecord r).secondGather.process) with returned := true } }))
      (w.writeGhost (ghostStep P) (Sum.inl (.retG r j (GBCA.gradeOf P g) bnd))) r
      = afterRetG P (afterSecondGatherReturn P (roundProjection P u w r) j g) j := by
  subst hu
  rw [roundProjection_writeGhost _ _ (rfl : roundOf (Sum.inl
      (Label.retG r j (GBCA.gradeOf P g) bnd)) = some r),
    firstGatherProjection_writeNoSent, secondGatherProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.programs_setPrograms,
    GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq, Function.update_idem,
      Function.update_self, roundRecord_update_self rfl,
    locals_programProjection_if]
    simp only [programs_mk, programProjection, LocalState.setProcess]
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.bound_setPrograms,
      GBCA.ByAFW.bound_setSecondGather, bound_roundProjection]
    simp only [bound_mk, ghostStep]
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.firstGather_setPrograms,
    GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    simp only [firstGather_mk,
      ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k
      simp only [Gather.inputBroadcasts_setCore, inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, core_firstGatherProjection]
  · simp only [afterRetG, afterSecondGatherReturn, GBCA.ByAFW.secondGather_setPrograms,
    GBCA.ByAFW.secondGather_setSecondGather,
      secondGather_roundProjection]
    simp only [secondGather_mk, ghostStep]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [Gather.gatherTier_setCore, Gather.gatherTier_setGatherTier,
      gatherTier_secondGather_roundProjectionUpdate]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess]
      refine congrArg (Function.update
        (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
          i).2.roundRecord r).secondGatherInputBroadcasts
          ((u i).2.roundRecord r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, InstanceState.process,
        gatherTier_secondGatherProjection_process, localState_setProcess_process,
          localState_setProcess_received]
      simp only [LocalState.setProcess]
    · funext k
      simp only [Gather.inputBroadcasts_setCore, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setCore, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp only [Gather.core_setCore, secondGatherReturnCore, secondGather_roundProjection,
        core_secondGatherProjection, coreOfNetwork_secondGatherProjection]

/-! ### A delivery

A delivery of the implementation files the message in the receiver's own local state of the network
state the message's tag names. A gather message moves the gather instance alone. A broadcast message
moves the broadcast instance, and, where it completes a `2f + 1` `VOTE` quorum at the receiver, the
instance returns to the receiver as well: the return flag goes on and what the receiver's gather
instance returned records the value. -/

/-- A delivery on the first gather's network, read through the view. -/
theorem roundProjection_deliverFirstGather (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.Message P.n Bool) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGather mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGather mm)))) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r) ((Gather.gatherTier
            (firstGatherProjection P u w r)).receiveMessage j k mm)) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGather mm))) (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
    programs_roundProjectionUpdate, programProjection, LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setGatherTier,
      InstanceState.receiveMessage, gatherTier_firstGatherProjection_network]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
          r).firstGatherInputBroadcasts
          ((u i).2.roundRecord r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, gatherTier_firstGatherProjection_process, LocalState.deliverTo]
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherTier, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery on the second gather's network, read through the view. -/
theorem roundProjection_deliverSecondGather (hu : (u j).2 = p) (r : ℕ) (k : Fin P.n)
    (mm : Gather.Message P.n (Option Bool)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGather mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGather mm)))) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r) ((Gather.gatherTier
            (secondGatherProjection P u w r)).receiveMessage j k mm)) := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGather mm))) (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
    programs_roundProjectionUpdate, programProjection, LocalState.deliverTo]
    exact Function.update_eq_self _ _
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate, Gather.gatherTier_setGatherTier,
      InstanceState.receiveMessage,
        gatherTier_secondGatherProjection_network]
      refine Prod.ext ?_ rfl
      refine congrArg (Function.update
        (fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
          i).2.roundRecord r).secondGatherInputBroadcasts
          ((u i).2.roundRecord r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, gatherTier_secondGatherProjection_process, LocalState.deliverTo]
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setGatherTier, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setGatherTier, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in an input-broadcast instance of the first
gather.** -/
noncomputable def afterFirstGatherInputBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n) (m : BRB.Message Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setInputBroadcasts (GBCA.ByAFW.firstGather s)
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).receiveMessage j k m)))

/-- **The round after an input-broadcast instance of the first gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterFirstGatherInputBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with
            inputBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process
                j).inputBroadcastReturned i (some v) }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).setProcess j
          { (Gather.inputBroadcasts (GBCA.ByAFW.firstGather s) i).process j with returned := true
            })))

/-- A delivery in an input-broadcast instance of the first gather that leaves the returned value
where it stands, read through the view. -/
theorem roundProjection_deliverFirstGatherInputBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherInputBroadcasts i).deliverTo k mm) =
      broadcastReturnsFor P
    ((p.roundRecord r).firstGatherInputBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherInputBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm)))) r
    = afterFirstGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.programs_setFirstGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherInputBroadcastDeliver]
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.firstGather_setFirstGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setInputBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_firstGatherProjection_fst]
      have hv : gatherLocalState P Bool ((u j).2.roundRecord r).firstGather
          (Function.update ((u j).2.roundRecord r).firstGatherInputBroadcasts i
            ((((u j).2.roundRecord r).firstGatherInputBroadcasts i).deliverTo k mm)) ((u
              j).2.roundRecord r).firstGatherBindBroadcasts
          = gatherLocalState P Bool ((u j).2.roundRecord r).firstGather ((u j).2.roundRecord
            r).firstGatherInputBroadcasts
              ((u j).2.roundRecord r).firstGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherInputBroadcastDeliver, GBCA.ByAFW.secondGather_setFirstGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in an input-broadcast instance of the first gather that
completes a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverFirstGatherInputBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message Bool) (v : Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherInputBroadcasts i).deliverTo k mm) =
      some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherInputBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i
          mm)))) r
      = afterFirstGatherInputBroadcastReturn P (afterFirstGatherInputBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherInputBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver,
    GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver]
  · simp only [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver,
    GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection,
      Gather.gatherTier_setInputBroadcasts, Gather.inputBroadcasts_setInputBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate,
      Gather.gatherTier_setInputBroadcasts, Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_firstGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P Bool ((u i').2.roundRecord r).firstGather
          ((u i').2.roundRecord r).firstGatherInputBroadcasts ((u i').2.roundRecord
            r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_firstGatherProjection_process, LocalState.setProcess]
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_firstGather_roundProjectionUpdate, inputBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setInputBroadcasts, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_firstGather_roundProjectionUpdate, bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherInputBroadcastReturn, afterFirstGatherInputBroadcastDeliver,
    GBCA.ByAFW.secondGather_setFirstGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in a bind-broadcast instance of the first
gather.** -/
noncomputable def afterFirstGatherBindBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n)
    (m : BRB.Message (Gather.AcceptedPairs P.n Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setBindBroadcasts (GBCA.ByAFW.firstGather s)
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).receiveMessage j k m)))

/-- **The round after a bind-broadcast instance of the first gather returns `v`
to `j`**: the instance's return flag goes on at `j` and `j`'s gather record
files the value. -/
noncomputable def afterFirstGatherBindBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Gather.AcceptedPairs P.n Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setFirstGather s
    (Gather.setBindBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.firstGather s)
        ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.firstGather s)).process j with
            bindBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.firstGather s)).process
                j).bindBroadcastReturned i (some v) }))
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).setProcess j
          { (Gather.bindBroadcasts (GBCA.ByAFW.firstGather s) i).process j with returned := true
            })))

/-- A delivery in a bind-broadcast instance of the first gather that leaves the returned value where
it stands, read through the view. -/
theorem roundProjection_deliverFirstGatherBindBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n Bool))
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherBindBroadcasts i).deliverTo k mm) =
      broadcastReturnsFor P
    ((p.roundRecord r).firstGatherBindBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherBindBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm)))) r
    = afterFirstGatherBindBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherBindBroadcastDeliver, GBCA.ByAFW.programs_setFirstGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherBindBroadcastDeliver]
  · simp only [afterFirstGatherBindBroadcastDeliver, GBCA.ByAFW.firstGather_setFirstGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setBindBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_firstGatherProjection_fst]
      have hv : gatherLocalState P Bool ((u j).2.roundRecord r).firstGather
          ((u j).2.roundRecord r).firstGatherInputBroadcasts (Function.update ((u j).2.roundRecord
            r).firstGatherBindBroadcasts i
            ((((u j).2.roundRecord r).firstGatherBindBroadcasts i).deliverTo k mm))
          = gatherLocalState P Bool ((u j).2.roundRecord r).firstGather ((u j).2.roundRecord
            r).firstGatherInputBroadcasts
              ((u j).2.roundRecord r).firstGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext q
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts, bindBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherBindBroadcastDeliver, GBCA.ByAFW.secondGather_setFirstGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in a bind-broadcast instance of the first gather that completes
a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverFirstGatherBindBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message (Gather.AcceptedPairs P.n Bool))
    (v : Gather.AcceptedPairs P.n Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).firstGatherBindBroadcasts i).deliverTo k mm) =
      some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.firstGatherBindBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i
          mm)))) r
      = afterFirstGatherBindBroadcastReturn P (afterFirstGatherBindBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.firstGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver,
    GBCA.ByAFW.programs_setFirstGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver]
  · simp only [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver,
    GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection,
      Gather.gatherTier_setBindBroadcasts, Gather.bindBroadcasts_setBindBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate, Gather.gatherTier_setBindBroadcasts,
      Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_firstGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P Bool ((u i').2.roundRecord r).firstGather
          ((u i').2.roundRecord r).firstGatherInputBroadcasts ((u i').2.roundRecord
            r).firstGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_firstGatherProjection_process, LocalState.setProcess]
    · funext q
      simp only [Gather.inputBroadcasts_setBindBroadcasts, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_firstGather_roundProjectionUpdate, inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_firstGather_roundProjectionUpdate, bindBroadcasts_firstGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).firstGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterFirstGatherBindBroadcastReturn, afterFirstGatherBindBroadcastDeliver,
    GBCA.ByAFW.secondGather_setFirstGather,
      secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in an input-broadcast instance of the second
gather.** -/
noncomputable def afterSecondGatherInputBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n) (m : BRB.Message (Option Bool)) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setInputBroadcasts (GBCA.ByAFW.secondGather s)
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).receiveMessage j k m)))

/-- **The round after an input-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterSecondGatherInputBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n) (v : Option Bool) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setInputBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with
            inputBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process
                j).inputBroadcastReturned i (some v) }))
      (Function.update (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).setProcess j
          { (Gather.inputBroadcasts (GBCA.ByAFW.secondGather s) i).process j with returned := true
            })))

/-- A delivery in an input-broadcast instance of the second gather that leaves the returned value
where it stands, read through the view. -/
theorem roundProjection_deliverSecondGatherInputBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Option Bool))
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherInputBroadcasts i).deliverTo k mm)
      = broadcastReturnsFor P
    ((p.roundRecord r).secondGatherInputBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherInputBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm))))
    r = afterSecondGatherInputBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))
    (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.programs_setSecondGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherInputBroadcastDeliver]
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.firstGather_setSecondGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherInputBroadcastDeliver, GBCA.ByAFW.secondGather_setSecondGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
      Gather.gatherTier_setInputBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_secondGatherProjection_fst]
      have hv : gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather
          (Function.update ((u j).2.roundRecord r).secondGatherInputBroadcasts i
            ((((u j).2.roundRecord r).secondGatherInputBroadcasts i).deliverTo k mm)) ((u
              j).2.roundRecord r).secondGatherBindBroadcasts
          = gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather ((u
            j).2.roundRecord r).secondGatherInputBroadcasts
              ((u j).2.roundRecord r).secondGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext k'
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in an input-broadcast instance of the second gather that
completes a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverSecondGatherInputBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message (Option Bool)) (v : Option Bool)
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherInputBroadcasts i).deliverTo k mm)
      = some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherInputBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i
          mm)))) r
      = afterSecondGatherInputBroadcastReturn P (afterSecondGatherInputBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherInputBroadcasts i mm)))
    (fun _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver,
    GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver]
  · simp only [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver,
    GBCA.ByAFW.firstGather_setSecondGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherInputBroadcastReturn, afterSecondGatherInputBroadcastDeliver,
    GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection,
      Gather.gatherTier_setInputBroadcasts, Gather.inputBroadcasts_setInputBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
      Gather.gatherTier_setInputBroadcasts, Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_secondGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P (Option Bool) ((u i').2.roundRecord r).secondGather
          ((u i').2.roundRecord r).secondGatherInputBroadcasts ((u i').2.roundRecord
            r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_secondGatherProjection_process, LocalState.setProcess]
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherInputBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [Gather.bindBroadcasts_setInputBroadcasts, Gather.bindBroadcasts_setGatherTier,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- **The round after a delivery in a bind-broadcast instance of the second
gather.** -/
noncomputable def afterSecondGatherBindBroadcastDeliver (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j k : Fin P.n)
    (m : BRB.Message (Gather.AcceptedPairs P.n (Option Bool))) :
    GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setBindBroadcasts (GBCA.ByAFW.secondGather s)
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).receiveMessage j k m)))

/-- **The round after a bind-broadcast instance of the second gather returns
`v` to `j`**: the instance's return flag goes on at `j` and `j`'s gather
record files the value. -/
noncomputable def afterSecondGatherBindBroadcastReturn (P : Parameters)
    (s : GBCA.ByAFW.RoundStateOverBracha P.n) (i j : Fin P.n)
    (v : Gather.AcceptedPairs P.n (Option Bool)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  GBCA.ByAFW.setSecondGather s
    (Gather.setBindBroadcasts
      (Gather.setGatherTier (GBCA.ByAFW.secondGather s)
        ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).setProcess j
          { (Gather.gatherTier (GBCA.ByAFW.secondGather s)).process j with
            bindBroadcastReturned :=
              Function.update ((Gather.gatherTier (GBCA.ByAFW.secondGather s)).process
                j).bindBroadcastReturned i (some v) }))
      (Function.update (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s)) i
        ((Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).setProcess j
          { (Gather.bindBroadcasts (GBCA.ByAFW.secondGather s) i).process j with returned := true
            })))

/-- A delivery in a bind-broadcast instance of the second gather that leaves the returned value
where it stands, read through the view. -/
theorem roundProjection_deliverSecondGatherBindBroadcast (hu : (u j).2 = p) (r : ℕ) (i k : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n (Option Bool)))
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherBindBroadcasts i).deliverTo k mm) =
      broadcastReturnsFor P
    ((p.roundRecord r).secondGatherBindBroadcasts i)) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherBindBroadcasts i mm)))
    (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm)))) r
    = afterSecondGatherBindBroadcastDeliver P (roundProjection P u w r) i j k mm := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherBindBroadcastDeliver, GBCA.ByAFW.programs_setSecondGather,
    programs_roundProjection_eq, programs_roundProjectionUpdate,
      programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherBindBroadcastDeliver]
  · simp only [afterSecondGatherBindBroadcastDeliver, GBCA.ByAFW.firstGather_setSecondGather,
    firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherBindBroadcastDeliver, GBCA.ByAFW.secondGather_setSecondGather,
    secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate, Gather.gatherTier_setBindBroadcasts]
      refine Prod.ext ?_ rfl
      simp only [gatherTier_secondGatherProjection_fst]
      have hv : gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather
          ((u j).2.roundRecord r).secondGatherInputBroadcasts (Function.update ((u j).2.roundRecord
            r).secondGatherBindBroadcasts i
            ((((u j).2.roundRecord r).secondGatherBindBroadcasts i).deliverTo k mm))
          = gatherLocalState P (Option Bool) ((u j).2.roundRecord r).secondGather ((u
            j).2.roundRecord r).secondGatherInputBroadcasts
              ((u j).2.roundRecord r).secondGatherBindBroadcasts := by
        simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
          Function.update_eq_self]
      rw [hv]
      exact Function.update_eq_self _ _
    · funext q
      simp only [inputBroadcasts_secondGather_roundProjectionUpdate,
        Gather.inputBroadcasts_setBindBroadcasts, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [bindBroadcasts_secondGather_roundProjectionUpdate,
        Gather.bindBroadcasts_setBindBroadcasts, bindBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self]
        refine Prod.ext ?_ rfl
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-- A delivery in a bind-broadcast instance of the second gather that completes
a `2f + 1` `VOTE` quorum, read through the view. -/
theorem roundProjection_deliverSecondGatherBindBroadcast_ret (hu : (u j).2 = p) (r : ℕ)
    (i k : Fin P.n) (mm : BRB.Message (Gather.AcceptedPairs P.n (Option Bool)))
    (v : Gather.AcceptedPairs P.n (Option Bool))
    (hst : broadcastReturnsFor P (((p.roundRecord r).secondGatherBindBroadcasts i).deliverTo k mm) =
      some v) :
    roundProjection P (Function.update u j (c, p.deliverTo r k (.secondGatherBindBroadcasts i mm)))
        (w.writeGhost (ghostStep P) (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i
          mm)))) r
      = afterSecondGatherBindBroadcastReturn P (afterSecondGatherBindBroadcastDeliver P
        (roundProjection P u w r) i j k mm) i j v := by
  subst hu
  rw [roundProjection_ghostId (Sum.inr (.gbcaDeliver r j k (.secondGatherBindBroadcasts i mm))) (fun
    _ _ => rfl)]
  simp only [Implementation.RoundRecordMap.deliverTo, roundRecord_deliverTo, RoundRecord.deliverTo]
  rw [roundProjection_writeNoSent]
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp only [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver,
    GBCA.ByAFW.programs_setSecondGather, programs_roundProjection_eq,
      programs_roundProjectionUpdate, programProjection]
    exact Function.update_eq_self _ _
  · simp [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver]
  · simp only [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver,
    GBCA.ByAFW.firstGather_setSecondGather,
      firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_firstGather_roundProjectionUpdate]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [inputBroadcasts_firstGather_roundProjectionUpdate,
        inputBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext q
      simp only [bindBroadcasts_firstGather_roundProjectionUpdate,
        bindBroadcasts_firstGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp
  · simp only [afterSecondGatherBindBroadcastReturn, afterSecondGatherBindBroadcastDeliver,
    GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection,
      Gather.gatherTier_setBindBroadcasts, Gather.bindBroadcasts_setBindBroadcasts]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · simp only [gatherTier_secondGather_roundProjectionUpdate,
      Gather.gatherTier_setBindBroadcasts, Gather.gatherTier_setGatherTier]
      refine Prod.ext ?_ rfl
      simp only [InstanceState.setProcess, gatherTier_secondGatherProjection_fst]
      refine congrArg (Function.update
        (fun i' => gatherLocalState P (Option Bool) ((u i').2.roundRecord r).secondGather
          ((u i').2.roundRecord r).secondGatherInputBroadcasts ((u i').2.roundRecord
            r).secondGatherBindBroadcasts) j) ?_
      simp only [gatherLocalState, broadcastReturnsFor_update_deliverTo, hst,
        InstanceState.process, gatherTier_secondGatherProjection_process, LocalState.setProcess]
    · funext q
      simp only [Gather.inputBroadcasts_setBindBroadcasts, Gather.inputBroadcasts_setGatherTier,
        inputBroadcasts_secondGather_roundProjectionUpdate, inputBroadcasts_secondGatherProjection]
      exact Prod.ext (Function.update_eq_self _ _) rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setBindBroadcasts,
        bindBroadcasts_secondGather_roundProjectionUpdate, bindBroadcasts_secondGatherProjection]
      by_cases hk : k' = i
      · rw [hk, Function.update_self, Function.update_self,
          Function.update_self]
        refine Prod.ext ?_ rfl
        simp only [InstanceState.setProcess, InstanceState.receiveMessage, InstanceState.process,
          Function.update_self, Function.update_idem]
        refine congrArg (Function.update
          (fun i' => broadcastLocalState P (((u i').2.roundRecord r).secondGatherBindBroadcasts i))
            j) ?_
        exact broadcastLocalState_deliverTo_ret _ k mm hst
      · rw [Function.update_of_ne hk, Function.update_of_ne hk,
          Function.update_of_ne hk]
        exact Prod.ext (Function.update_eq_self _ _) rfl
    · simp

/-! ### A Byzantine injection

The adversary multicasts on behalf of a corrupted sender. The message reaches
the network state its tag names and no record moves. -/

/-- A Byzantine injection on the first gather's network state, read through the
view. -/
theorem roundProjection_byzantineFirstGather (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (mm : Gather.Message P.n Bool) :
    roundProjection P u (w.recordGBCASend r k (.firstGather mm)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setGatherTier (firstGatherProjection P u w r) ((Gather.gatherTier
            (firstGatherProjection P u w r)).multicast k mm)) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherTier_setGatherTier, InstanceState.multicast,
        ABA.NetworkState.recordSent, gatherTier_firstGatherProjection_network,
          recordGBCASend_sent_self]
      exact messagesOf_recordSent_some firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.firstGather mm) mm rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setGatherTier, inputBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGather mm) rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setGatherTier, bindBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k')
        (firstGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.firstGather mm) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherTier_secondGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.firstGather mm) rfl
    · funext k'
      simp only [inputBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGather mm) rfl
    · funext k'
      simp only [bindBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k')
        (secondGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.firstGather mm) rfl
    · simp

/-- A Byzantine injection on the second gather's network state, read through
the view. -/
theorem roundProjection_byzantineSecondGather (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (mm : Gather.Message P.n (Option Bool)) :
    roundProjection P u (w.recordGBCASend r k (.secondGather mm)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setGatherTier (secondGatherProjection P u w r) ((Gather.gatherTier
            (secondGatherProjection P u w r)).multicast k mm)) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherTier_firstGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.secondGather mm) rfl
    · funext k'
      simp only [inputBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGather mm) rfl
    · funext k'
      simp only [bindBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k')
        (firstGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.secondGather mm) rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherTier_setGatherTier, InstanceState.multicast,
        ABA.NetworkState.recordSent, gatherTier_secondGatherProjection_network,
          recordGBCASend_sent_self]
      exact messagesOf_recordSent_some secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.secondGather mm) mm rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setGatherTier, inputBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGather mm) rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setGatherTier, bindBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k')
        (secondGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.secondGather mm) rfl
    · simp

/-- A Byzantine injection on an input-broadcast instance of the first gather,
read through the view. -/
theorem roundProjection_byzantineFirstGatherInputBroadcast
    (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ) (k : Fin P.n)
    (i : Fin P.n) (mm : BRB.Message Bool) :
    roundProjection P u (w.recordGBCASend r k (.firstGatherInputBroadcasts i mm)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (firstGatherProjection P u w r)) i
              ((Gather.inputBroadcasts (firstGatherProjection P u w r) i).multicast k mm))) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherTier_setInputBroadcasts, gatherTier_firstGatherProjection_network,
        recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.firstGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherInputBroadcastMessageOf i)
          (firstGatherInputBroadcastMessageOf_inj i) (w.sent r) k
          (.firstGatherInputBroadcasts i mm) mm (by simp [firstGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [inputBroadcasts_firstGatherProjection]
        exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
          (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k
          (.firstGatherInputBroadcasts i mm) (by simp [firstGatherInputBroadcastMessageOf,
            Ne.symm hk])
    · funext k'
      simp only [Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k')
        (firstGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherInputBroadcasts i mm)
          rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherTier_secondGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.firstGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [inputBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherInputBroadcasts i mm)
          rfl
    · funext k'
      simp only [bindBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k')
        (secondGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherInputBroadcasts i mm)
          rfl
    · simp

/-- A Byzantine injection on a bind-broadcast instance of the first gather,
read through the view. -/
theorem roundProjection_byzantineFirstGatherBindBroadcast (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) (k : Fin P.n) (i : Fin P.n)
    (mm : BRB.Message (Gather.AcceptedPairs P.n Bool)) :
    roundProjection P u (w.recordGBCASend r k (.firstGatherBindBroadcasts i mm)) r
      = GBCA.ByAFW.setFirstGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (firstGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (firstGatherProjection P u w r)) i
              ((Gather.bindBroadcasts (firstGatherProjection P u w r) i).multicast k mm))) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setFirstGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherTier_setBindBroadcasts, gatherTier_firstGatherProjection_network,
        recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.firstGatherBindBroadcasts i mm) rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setBindBroadcasts, inputBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherBindBroadcasts i mm)
          rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setBindBroadcasts, bindBroadcasts_firstGatherProjection,
        recordGBCASend_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (firstGatherBindBroadcastMessageOf i)
          (firstGatherBindBroadcastMessageOf_inj i) (w.sent r) k
          (.firstGatherBindBroadcasts i mm) mm (by simp [firstGatherBindBroadcastMessageOf])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [bindBroadcasts_firstGatherProjection]
        exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k')
          (firstGatherBindBroadcastMessageOf_inj k') (w.sent r) k
          (.firstGatherBindBroadcasts i mm) (by simp [firstGatherBindBroadcastMessageOf,
            Ne.symm hk])
    · simp
  · simp only [GBCA.ByAFW.secondGather_setFirstGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherTier_secondGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.firstGatherBindBroadcasts i mm) rfl
    · funext k'
      simp only [inputBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherBindBroadcasts i mm)
          rfl
    · funext k'
      simp only [bindBroadcasts_secondGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k')
        (secondGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.firstGatherBindBroadcasts i mm)
          rfl
    · simp

/-- A Byzantine injection on an input-broadcast instance of the second gather,
read through the view. -/
theorem roundProjection_byzantineSecondGatherInputBroadcast
    (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ) (k : Fin P.n)
    (i : Fin P.n) (mm : BRB.Message (Option Bool)) :
    roundProjection P u (w.recordGBCASend r k (.secondGatherInputBroadcasts i mm)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setInputBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.inputBroadcasts (secondGatherProjection P u w r)) i
              ((Gather.inputBroadcasts (secondGatherProjection P u w r) i).multicast k mm))) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherTier_firstGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.secondGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [inputBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherInputBroadcasts i mm)
          rfl
    · funext k'
      simp only [bindBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k')
        (firstGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherInputBroadcasts i mm)
          rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherTier_setInputBroadcasts, gatherTier_secondGatherProjection_network,
        recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.secondGatherInputBroadcasts i mm) rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setInputBroadcasts, inputBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherInputBroadcastMessageOf i)
          (secondGatherInputBroadcastMessageOf_inj i) (w.sent r) k
          (.secondGatherInputBroadcasts i mm) mm (by simp [secondGatherInputBroadcastMessageOf])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [inputBroadcasts_secondGatherProjection]
        exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
          (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k
          (.secondGatherInputBroadcasts i mm) (by simp [secondGatherInputBroadcastMessageOf,
            Ne.symm hk])
    · funext k'
      simp only [Gather.bindBroadcasts_setInputBroadcasts, bindBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k')
        (secondGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherInputBroadcasts i mm)
          rfl
    · simp

/-- A Byzantine injection on a bind-broadcast instance of the second gather,
read through the view. -/
theorem roundProjection_byzantineSecondGatherBindBroadcast
    (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ) (k : Fin P.n)
    (i : Fin P.n) (mm : BRB.Message (Gather.AcceptedPairs P.n (Option Bool))) :
    roundProjection P u (w.recordGBCASend r k (.secondGatherBindBroadcasts i mm)) r
      = GBCA.ByAFW.setSecondGather (roundProjection P u w r)
          (Gather.setBindBroadcasts (secondGatherProjection P u w r)
            (Function.update (Gather.bindBroadcasts (secondGatherProjection P u w r)) i
              ((Gather.bindBroadcasts (secondGatherProjection P u w r) i).multicast k mm))) := by
  refine roundStateOverGathers_ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [GBCA.ByAFW.firstGather_setSecondGather, firstGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [gatherTier_firstGatherProjection_network, recordGBCASend_sent_self]
      exact messagesOf_recordSent_none firstGatherMessageOf firstGatherMessageOf_inj (w.sent r) k
        (.secondGatherBindBroadcasts i mm) rfl
    · funext k'
      simp only [inputBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherInputBroadcastMessageOf k')
        (firstGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherBindBroadcasts i mm)
          rfl
    · funext k'
      simp only [bindBroadcasts_firstGatherProjection, recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (firstGatherBindBroadcastMessageOf k')
        (firstGatherBindBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherBindBroadcasts i mm)
          rfl
    · simp
  · simp only [GBCA.ByAFW.secondGather_setSecondGather, secondGather_roundProjection]
    refine stateOverBroadcasts_ext ?_ ?_ ?_ ?_
    · refine Prod.ext rfl (networkState_ext ?_ rfl)
      simp only [Gather.gatherTier_setBindBroadcasts, gatherTier_secondGatherProjection_network,
        recordGBCASend_sent_self]
      exact messagesOf_recordSent_none secondGatherMessageOf secondGatherMessageOf_inj (w.sent r) k
        (.secondGatherBindBroadcasts i mm) rfl
    · funext k'
      simp only [Gather.inputBroadcasts_setBindBroadcasts, inputBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      refine Prod.ext rfl (networkState_ext ?_ rfl)
      exact messagesOf_recordSent_none (secondGatherInputBroadcastMessageOf k')
        (secondGatherInputBroadcastMessageOf_inj k') (w.sent r) k (.secondGatherBindBroadcasts i mm)
          rfl
    · funext k'
      simp only [Gather.bindBroadcasts_setBindBroadcasts, bindBroadcasts_secondGatherProjection,
        recordGBCASend_sent_self]
      by_cases hk : k' = i
      · rw [hk, Function.update_self]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [InstanceState.multicast, ABA.NetworkState.recordSent]
        exact messagesOf_recordSent_some (secondGatherBindBroadcastMessageOf i)
          (secondGatherBindBroadcastMessageOf_inj i) (w.sent r) k
          (.secondGatherBindBroadcasts i mm) mm (by simp [secondGatherBindBroadcastMessageOf])
      · rw [Function.update_of_ne hk]
        refine Prod.ext rfl (networkState_ext ?_ rfl)
        simp only [bindBroadcasts_secondGatherProjection]
        exact messagesOf_recordSent_none (secondGatherBindBroadcastMessageOf k')
          (secondGatherBindBroadcastMessageOf_inj k') (w.sent r) k
          (.secondGatherBindBroadcasts i mm) (by simp [secondGatherBindBroadcastMessageOf,
            Ne.symm hk])
    · simp

/-! ### Every other round is unchanged

A row names one round. The rounds it does not name read exactly as they did:
the acting process's other round records are untouched, the adversary's sent
family is written at one round only, and so is its ghost record. -/

/-- The view of a round the row does not name. -/
theorem roundProjection_otherRow (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr : RoundRecord P.n)
    (v : NetworkState P.n) (hsent : v.sent r' = w.sent r') (hF : v.F = w.F)
    (hghost : v.ghostRecord r' = w.ghostRecord r') :
    roundProjection P (Function.update u j (c, p.setRoundRecord r sr)) v r' = roundProjection P u w
    r' := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection,
    roundRecord_update_ne hu hr, hsent, hF, hghost]

/-- A send of round `r`, read at another round. -/
theorem roundProjection_other (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr : RoundRecord P.n)
    (m : Message P.n) {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
        ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r' = roundProjection P u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  exact roundProjection_otherRow hu hr sr _ (recordGBCASend_sent_ne w r j m hr) rfl rfl

/-- A row of round `r` that records nothing, read at another round. -/
theorem roundProjection_otherNoSent (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : RoundRecord P.n) {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
        (w.writeGhost (ghostStep P) L) r' = roundProjection P u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  exact roundProjection_otherRow hu hr sr w rfl rfl rfl

/-- A Byzantine injection of round `r`, read at another round. -/
theorem roundProjection_otherSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n)
    {r r' : ℕ} (hr : r' ≠ r) (k : Fin P.n) (m : Message P.n)
    {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r) :
    roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r' = roundProjection P
      u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  simp only [roundProjection, firstGatherProjection, secondGatherProjection,
    recordGBCASend_sent_ne w r k m hr, recordGBCASend_F, recordGBCASend_ghostRecord]

/-- **The whole family of rounds after a send**: the round the row names moves,
the rest remain unchanged. -/
theorem toRoundFamily (hu : (u j).2 = p) (r : ℕ) (sr : RoundRecord P.n) (m : Message P.n)
    {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r)
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r = X)
    :
    (fun r' => roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r')
    = Function.update (fun r' => roundProjection P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, roundProjection_other hu hr sr m hL]

/-- The same, for a row that records nothing. -/
theorem toRoundFamilyNoSent (hu : (u j).2 = p) (r : ℕ) (sr : RoundRecord P.n)
    {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r)
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      (w.writeGhost (ghostStep P) L) r = X)
    :
    (fun r' => roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      (w.writeGhost (ghostStep P) L) r')
    = Function.update (fun r' => roundProjection P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, roundProjection_otherNoSent hu hr sr hL]

/-- The same, for a Byzantine injection. -/
theorem toRoundFamilySent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ)
    (k : Fin P.n) (m : Message P.n) {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r)
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r = X) :
    (fun r' => roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r')
      = Function.update (fun r' => roundProjection P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, roundProjection_otherSent u w hr k m hL]

end Rows

/-! ### The two clauses that are not projections

`BroadcastReturnsInvariant` and `BoundInvariant` are the conjuncts of `AFW.ProtocolRelation` that no
frame lemma supplies. Each survives a row instance by instance: a broadcast instance either stands
still or takes a row of `BRB.BrachaStep`, which `BRB.Invariant.step` carries, and a process's
second-gather local input is written at the return-then-call step alone. -/

section Invariants

/-- One broadcast instance's move across a row: it is unchanged, or it takes a
row of `BRB.BrachaStep`. -/
def InvariantStep (P : Parameters) {M : Type} [DecidableEq M] (ldr : Fin P.n)
    (s s' : BRB.BrachaState P.n M) : Prop :=
  s' = s ∨ ∃ l, BRB.BrachaStep P ldr s l (PMF.pure s')

/-- An instance that is unchanged. -/
theorem InvariantStep.unchanged {M : Type} [DecidableEq M] (P : Parameters) (ldr : Fin P.n)
    (s : BRB.BrachaState P.n M) : InvariantStep P ldr s s := Or.inl rfl

/-- An instance that takes a row. -/
theorem InvariantStep.row {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {l : BRB.Label P.n M}
    (h : BRB.BrachaStep P ldr s l (PMF.pure s')) : InvariantStep P ldr s s' := Or.inr ⟨l, h⟩

/-- **The broadcast invariant survives one instance's move.** -/
theorem InvariantStep.invariant {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} (h : InvariantStep P ldr s s') (hInv : BRB.Invariant P ldr s) :
    BRB.Invariant P ldr s' := by
  rcases h with rfl | ⟨l, hl⟩
  · exact hInv
  · exact hInv.step hl (by simp)

/-- A row that moves one instance of a family: that instance takes its row and
every other instance is unchanged. -/
theorem invariantStep_update {M : Type} [DecidableEq M] {P : Parameters}
    (b : Fin P.n → BRB.BrachaState P.n M) (i : Fin P.n) (s' : BRB.BrachaState P.n M)
    {l : BRB.Label P.n M} (h : BRB.BrachaStep P i (b i) l (PMF.pure s')) (k : Fin P.n) :
    InvariantStep P k (b k) (Function.update b i s' k) := by
  by_cases hk : k = i
  · subst hk; rw [Function.update_self]; exact InvariantStep.row h
  · rw [Function.update_of_ne hk]; exact InvariantStep.unchanged P k (b k)

variable {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w v : NetworkState P.n}

/-- **The broadcast invariant survives a row**: at each of a round's `4n`
instances the state after the row is the state before it or a `BRB.BrachaStep`
successor of it. -/
theorem broadcastReturnsInvariant_of (hI : BroadcastReturnsInvariant P u w)
    (h1 : ∀ r k,
      InvariantStep P k (Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjection P u w r))
        k)
        (Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjection P x v r)) k))
    (h2 : ∀ r k,
      InvariantStep P k (Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjection P u w r)) k)
        (Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjection P x v r)) k))
    (h3 : ∀ r k,
      InvariantStep P k (Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjection P u w r))
        k)
        (Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjection P x v r)) k))
    (h4 : ∀ r k,
      InvariantStep P k (Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjection P u w r))
        k)
        (Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjection P x v r)) k)) :
    BroadcastReturnsInvariant P x v :=
  fun r k => ⟨(h1 r k).invariant (hI r k).1, (h2 r k).invariant (hI r k).2.1,
    (h3 r k).invariant (hI r k).2.2.1, (h4 r k).invariant (hI r k).2.2.2⟩

/-- A row that leaves every round's view where it stands keeps the broadcast
invariant. -/
theorem broadcastReturnsInvariant_congr (hI : BroadcastReturnsInvariant P u w)
    (h : ∀ r, roundProjection P x v r = roundProjection P u w r) :
    BroadcastReturnsInvariant P x v :=
  fun r k => by rw [h r]; exact hI r k

/-- The bound invariant survives a row that leaves every process's
second-gather local input where it stands and writes the ghost through
`AFW.ghostStep`. -/
theorem boundInvariant_writeGhost (hI : BoundInvariant P u w)
    (hx : ∀ i r,
      (((x i).2.roundRecord r).secondGather.process).input = (((u i).2.roundRecord
        r).secondGather.process).input)
    (hv : ∀ r, v.ghostRecord r = w.ghostRecord r) (L : ExtendedLabel P.n (Message P.n)) :
    BoundInvariant P x (v.writeGhost (ghostStep P) L) :=
  boundInvariant_of hI hx (fun r h => writeGhost_bound L (by rw [hv r]; exact h))

end Invariants

end AFW

end ABA
end PLTS
