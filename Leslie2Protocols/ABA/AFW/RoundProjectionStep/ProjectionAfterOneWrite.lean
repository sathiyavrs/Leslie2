/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndRemovals
import Leslie2Protocols.ABA.AFW.RoundProjection

/-!
# The projection of the composed round after one write

A transition of the implementation writes the acting process's round variables and records at most
one tagged message. `roundProjection_write` and `roundProjection_writeNoSent` do that write once,
through `roundProjectionUpdate`: each local state vector of the projection becomes a one-point
update of the old one, and each network state is recovered from the written sent family by its own
tag (`messagesOf`).
`messagesOf_recordSent_some` and `messagesOf_recordSent_none` are the sent algebra a transition
still owes, and one simp lemma per coordinate reads the written projection off
`roundProjectionUpdate`.
`networkState_ext`,
`stateOverBroadcasts_ext` and `roundStateOverGathers_ext` identify a network state, a
gather-over-Bracha state and a round state with their components. Every class of transitions in
`AFW/RoundProjectionStep/` rests on this file.
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

/-- A gather-over-Bracha state is its gather programs and network beside its two broadcast
families and its core. -/
theorem stateOverBroadcasts_ext {n : ℕ} {X B B' : Type} {a b : Gather.StateOverBroadcasts n X B B'}
    (h1 : Gather.gatherProgramsAndNetwork a = Gather.gatherProgramsAndNetwork b)
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

/-! ### Reading written variables -/

variable {P : Parameters}

/-- The variables a process holds at the round it has just written. -/
theorem roundVariables_update_self {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} (hu : (u j).2 = p) (r : ℕ)
    (sr : RoundVariables P.n) (i : Fin P.n) :
    ((Function.update u j (c, p.setRoundVariables r sr) i).2.roundVariables r)
      = if i = j then sr else ((u i).2.roundVariables r) := by
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    simp
  · rw [Function.update_of_ne hi, if_neg hi]

/-- The variables a process holds at every other round. -/
theorem roundVariables_update_ne {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} (hu : (u j).2 = p) {r r' : ℕ} (hr : r'
      ≠ r)
    (sr : RoundVariables P.n) (i : Fin P.n) :
    ((Function.update u j (c, p.setRoundVariables r sr) i).2.roundVariables r') =
    ((u i).2.roundVariables r') := by
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    change ((p.setRoundVariables r sr).roundVariables r') = _
    rw [Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr, hu]
  · rw [Function.update_of_ne hi]

/-- The round loop a process holds is untouched by a write to a round's variables. -/
@[simp] theorem core_update {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {j : Fin P.n}
    (x : AFW.ProcessVariables P.n) (i : Fin P.n) :
    (Function.update u j x i).1 = if i = j then x.1 else (u i).1 := by
  by_cases hi : i = j
  · subst hi; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hi, if_neg hi]

/-- The projection reads a process family through its round variables alone. -/
theorem roundProjection_congr {x u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n}
    {r : ℕ} (h : ∀ i, (x i).2.roundVariables r = (u i).2.roundVariables r) :
    roundProjection P x w r = roundProjection P u w r := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection, h]

/-! ### Transposing one written process's variables

A transition writes the acting process's round variables, so each local state vector
the projection reads becomes a one-point update of the old one. Each lemma below is that
observation at one component of the projection, stated over the `ite` that reading
written variables produces. -/

section LocalStates
variable {j : Fin P.n} (Y : Fin P.n → RoundVariables P.n) (sr : RoundVariables P.n)

theorem locals_programProjection_if :
    (fun i => programProjection (if i = j then sr else Y i))
      = Function.update (fun i => programProjection (Y i)) j (programProjection sr) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherLocalState_if :
    (fun i => (if i = j then sr else Y i).firstGather)
      = Function.update
          (fun i => (Y i).firstGather) j
          (sr.firstGather) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherLocalState_if :
    (fun i => (if i = j then sr else Y i).secondGather)
      = Function.update
          (fun i => (Y i).secondGather) j
          (sr.secondGather) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherInputBroadcast_if (k : Fin P.n) :
    (fun i => ((if i = j then sr else Y i).firstGatherInputBroadcasts k))
      = Function.update (fun i => ((Y i).firstGatherInputBroadcasts k)) j
          ((sr.firstGatherInputBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherBindBroadcast_if (k : Fin P.n) :
    (fun i => ((if i = j then sr else Y i).firstGatherBindBroadcasts k))
      = Function.update (fun i => ((Y i).firstGatherBindBroadcasts k)) j
          ((sr.firstGatherBindBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherInputBroadcast_if (k : Fin P.n) :
    (fun i => ((if i = j then sr else Y i).secondGatherInputBroadcasts k))
      = Function.update (fun i => ((Y i).secondGatherInputBroadcasts k)) j
          ((sr.secondGatherInputBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherBindBroadcast_if (k : Fin P.n) :
    (fun i => ((if i = j then sr else Y i).secondGatherBindBroadcasts k))
      = Function.update (fun i => ((Y i).secondGatherBindBroadcasts k)) j
          ((sr.secondGatherBindBroadcasts k)) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

end LocalStates
/-! ### The projection after one write

A transition of the implementation writes one component of the acting process's
round variables and records at most one tagged message. The two lemmas below are that
write read through the projection: each local state vector becomes a one-point
update, and each network state is recovered from the written sent family by its
own tag. What every transition still owes is then sent algebra alone. -/

section Writes
variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-- The projection after a write, with the one-point update pushed inside every
coordinate: the acting process's local state replaced in each local state
vector, and each network state recovered from the written sent by its own tag.
The two cores
and the bound bit are the adversary's ghost of the round, which a write
leaves alone. -/
noncomputable def roundProjectionUpdate (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables
  P.n)
    (w : NetworkState P.n) (r : ℕ) (j : Fin P.n) (sr : RoundVariables P.n)
    (sent : Fin P.n → Finset (Message P.n)) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  ((Function.update (fun i => programProjection ((u i).2.roundVariables r)) j (programProjection
    sr),
      (w.ghost r).2.2),
    (((Function.update
            (fun i => ((u i).2.roundVariables r).firstGather) j
            (sr.firstGather),
          ⟨⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj sent, w.F⟩,
            (w.ghost r).1⟩),
        fun k => (Function.update (fun i => (((u i).2.roundVariables
          r).firstGatherInputBroadcasts k)) j
            ((sr.firstGatherInputBroadcasts k)),
          ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
            k) sent, w.F⟩),
        fun q => (Function.update (fun i => (((u i).2.roundVariables
          r).firstGatherBindBroadcasts q)) j
            ((sr.firstGatherBindBroadcasts q)),
          ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj
            q) sent, w.F⟩)),
      ((Function.update
            (fun i => ((u i).2.roundVariables r).secondGather) j
            (sr.secondGather),
          ⟨⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj sent, w.F⟩,
            (w.ghost r).2.1⟩),
        fun k => (Function.update (fun i => (((u i).2.roundVariables
          r).secondGatherInputBroadcasts k)) j
            ((sr.secondGatherInputBroadcasts k)),
          ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) sent, w.F⟩),
        fun q => (Function.update (fun i => (((u i).2.roundVariables
          r).secondGatherBindBroadcasts q)) j
            ((sr.secondGatherBindBroadcasts q)),
          ⟨messagesOf (secondGatherBindBroadcastMessageOf q) (secondGatherBindBroadcastMessageOf_inj
            q) sent, w.F⟩))))

/-- **A write, read through the projection.** A transition writes the acting process's
round variables and records one tagged message; the round it names then reads as the
one-point update of every coordinate. -/
theorem roundProjection_write (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n)
    (j : Fin P.n) (c : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n) (m : Message P.n) :
    roundProjection P (Function.update u j (c, (u j).2.setRoundVariables r sr))
    (w.recordGBCASend r j m) r = roundProjectionUpdate P u w r j sr
    (Function.update (w.sent r) j (insert m (w.sent r j))) := by
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, roundProjection, roundProjectionUpdate,
      roundVariables_update_self rfl, locals_programProjection_if]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather, roundProjection,
        roundProjectionUpdate,
      firstGatherProjection, roundVariables_update_self rfl, locals_firstGatherLocalState_if]
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather, roundProjection,
        roundProjectionUpdate,
        firstGatherProjection, recordGBCASend_sent_self]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundVariables_update_self rfl,
        locals_firstGatherInputBroadcast_if]
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
        roundProjectionUpdate, firstGatherProjection, recordGBCASend_sent_self]
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundVariables_update_self rfl,
        locals_firstGatherBindBroadcast_if]
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
        roundProjectionUpdate, firstGatherProjection, recordGBCASend_sent_self]
  · refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, roundVariables_update_self rfl,
        locals_secondGatherLocalState_if]
    · simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, recordGBCASend_sent_self]
  · funext k
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundVariables_update_self rfl,
        locals_secondGatherInputBroadcast_if]
    · simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, recordGBCASend_sent_self]
  · funext q
    refine Prod.ext ?_ (networkState_ext ?_ rfl)
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundVariables_update_self rfl,
        locals_secondGatherBindBroadcast_if]
    · simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
        roundProjectionUpdate, secondGatherProjection, recordGBCASend_sent_self]

/-- A write that records nothing — a delivery, or a return — read through the
projection. -/
theorem roundProjection_writeNoSent (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (j : Fin P.n) (c : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables
      P.n) :
    roundProjection P (Function.update u j (c, (u j).2.setRoundVariables r sr)) w r =
    roundProjectionUpdate P u w r j sr (w.sent r) := by
  refine roundStateOverGathers_ext ?_ rfl (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
    (stateOverBroadcasts_ext ?_ ?_ ?_ rfl)
  · simp only [GBCA.ByAFW.programs, roundProjection, roundProjectionUpdate,
      roundVariables_update_self rfl, locals_programProjection_if]
  · refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate,
      firstGatherProjection, roundVariables_update_self rfl, locals_firstGatherLocalState_if]
  · funext k
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.inputBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundVariables_update_self rfl,
        locals_firstGatherInputBroadcast_if]
  · funext q
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.bindBroadcasts, GBCA.ByAFW.firstGather, roundProjection,
      roundProjectionUpdate, firstGatherProjection, roundVariables_update_self rfl,
        locals_firstGatherBindBroadcast_if]
  · refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.gatherProgramsAndNetwork, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate,
      secondGatherProjection, roundVariables_update_self rfl, locals_secondGatherLocalState_if]
  · funext k
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.inputBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundVariables_update_self rfl,
        locals_secondGatherInputBroadcast_if]
  · funext q
    refine Prod.ext ?_ (networkState_ext rfl rfl)
    simp only [Gather.bindBroadcasts, GBCA.ByAFW.secondGather, roundProjection,
      roundProjectionUpdate, secondGatherProjection, roundVariables_update_self rfl,
        locals_secondGatherBindBroadcast_if]

end Writes
/-! ### Reading the written projection

The written projection is read coordinate by coordinate, so that a transition's
remaining obligations are stated over one local state vector or one network
state at a time. -/

section WrittenProjectionReaders
variable (v : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n) (r : ℕ) (j : Fin P.n)
    (sr : RoundVariables P.n) (sent : Fin P.n → Finset (Message P.n))

@[simp] theorem programs_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessVariables P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.programs (((a, bnd), (x, y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = a := rfl

@[simp] theorem bound_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessVariables P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.bound (((a, bnd), (x, y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = bnd := rfl

@[simp] theorem firstGather_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessVariables P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.firstGather (((a, bnd), (x,
      y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = x := rfl

@[simp] theorem secondGather_mk {G₁ G₂ : Type} (a : ∀ _ : Fin P.n, GBCA.ByAFW.ProcessVariables P.n)
    (bnd : Option Bool) (x : G₁) (y : G₂) :
    GBCA.ByAFW.secondGather (((a, bnd), (x,
      y)) : GBCA.ByAFW.RoundStateOverGathers P.n G₁ G₂) = y := rfl

@[simp] theorem gatherProgramsAndNetwork_firstGatherProjection_fst :
    (Gather.gatherProgramsAndNetwork (firstGatherProjection P v w r)).1
      = fun i => ((v i).2.roundVariables r).firstGather := rfl

@[simp] theorem gatherProgramsAndNetwork_secondGatherProjection_fst :
    (Gather.gatherProgramsAndNetwork (secondGatherProjection P v w r)).1
      = fun i => ((v i).2.roundVariables r).secondGather := rfl

@[simp] theorem programs_roundProjection_eq :
    GBCA.ByAFW.programs (roundProjection P v w r) = fun i => programProjection ((v
      i).2.roundVariables
      r) := rfl

@[simp] theorem programs_roundProjectionUpdate :
    GBCA.ByAFW.programs (roundProjectionUpdate P v w r j sr sent)
      = Function.update (fun i => programProjection ((v i).2.roundVariables r)) j (programProjection
        sr) := rfl

@[simp] theorem bound_roundProjectionUpdate :
    GBCA.ByAFW.bound (roundProjectionUpdate P v w r j sr sent) = (w.ghost r).2.2 := rfl

@[simp] theorem core_firstGather_roundProjectionUpdate :
    Gather.core (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent)) = (w.ghost
      r).1 := rfl

@[simp] theorem core_secondGather_roundProjectionUpdate :
    Gather.core (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent)) = (w.ghost
      r).2.1 := rfl

@[simp] theorem gatherProgramsAndNetwork_firstGather_roundProjectionUpdate :
    Gather.gatherProgramsAndNetwork (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr
      sent))
      = (Function.update (fun i => ((v i).2.roundVariables r).firstGather) j
          (sr.firstGather),
        ⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj sent, w.F⟩) := rfl

@[simp] theorem gatherProgramsAndNetwork_secondGather_roundProjectionUpdate :
    Gather.gatherProgramsAndNetwork (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr
      sent))
      = (Function.update (fun i => ((v i).2.roundVariables
        r).secondGather) j
          (sr.secondGather),
        ⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj sent, w.F⟩) := rfl

@[simp] theorem inputBroadcasts_firstGather_roundProjectionUpdate (k : Fin P.n) :
    Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent)) k
      = (Function.update (fun i => (((v i).2.roundVariables
        r).firstGatherInputBroadcasts k)) j
          ((sr.firstGatherInputBroadcasts k)),
            ⟨messagesOf (firstGatherInputBroadcastMessageOf k)
              (firstGatherInputBroadcastMessageOf_inj k) sent, w.F⟩) := rfl

@[simp] theorem bindBroadcasts_firstGather_roundProjectionUpdate (q : Fin P.n) :
    Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjectionUpdate P v w r j sr sent)) q
      = (Function.update (fun i => (((v i).2.roundVariables
        r).firstGatherBindBroadcasts q)) j
          ((sr.firstGatherBindBroadcasts q)),
            ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj
              q) sent, w.F⟩) := rfl

@[simp] theorem inputBroadcasts_secondGather_roundProjectionUpdate (k : Fin P.n) :
    Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent)) k
      = (Function.update (fun i => (((v i).2.roundVariables
        r).secondGatherInputBroadcasts k)) j
          ((sr.secondGatherInputBroadcasts k)),
            ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
              (secondGatherInputBroadcastMessageOf_inj k) sent, w.F⟩) := rfl

@[simp] theorem bindBroadcasts_secondGather_roundProjectionUpdate (q : Fin P.n) :
    Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjectionUpdate P v w r j sr sent)) q
      = (Function.update (fun i => (((v i).2.roundVariables
        r).secondGatherBindBroadcasts q)) j
          ((sr.secondGatherBindBroadcasts q)),
            ⟨messagesOf (secondGatherBindBroadcastMessageOf q)
              (secondGatherBindBroadcastMessageOf_inj q) sent, w.F⟩) := rfl

end WrittenProjectionReaders
end AFW
end ABA
end PLTS
