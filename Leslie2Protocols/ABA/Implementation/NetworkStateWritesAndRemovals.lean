/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.StepCases

/-!
# The writes on the network's state, and the removal of the ghost

The network's state holds the sent sets, the DECIDED sets, the corrupted set with its budget, one
ghost per round, and the started rounds. Five writes touch it: a round multicast, a DECIDED
multicast, corruption, the record of a started round, and the ghost write. Each touches one field
and leaves the others where they stand. The lemmas here read each field of the state a write
delivers, the sent sets and the ghosts through the accessors `sent r` and `ghost r`, and they are
the field algebra the proofs over the implementation run on. The four writes other than the ghost
write leave the ghost alone. The ghost write leaves every other field alone, and it leaves the
whole state alone on a label naming no round and on a write returning the ghost standing there.

`NetworkState.forgetGhost` sends the network's state to the state over the trivial ghost `Unit`,
and it commutes with each of the four writes other than the ghost write. Over `Unit` the ghost
write is the identity, so the removal of a ghost write is the removal of the state it starts from.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The network's own field algebra

Each of the network's four writes other than the ghost write — a round multicast, a DECIDED
multicast, corruption and the record of a started round — touches one field of the state and
leaves the others alone, the ghost among them. -/

section Fields

variable {n : ℕ} {M E G : Type}

@[simp] theorem recordGBCASend_sent_self [DecidableEq M]
    (s : NetworkState n M G) (r : ℕ) (j : Fin n) (m : M) :
    (s.recordGBCASend r j m).sent r = Function.update (s.sent r) j (insert m (s.sent r j)) := by
  simp [NetworkState.sent, NetworkState.recordGBCASend, Finmap.lookup_insert]

theorem recordGBCASend_sent_ne [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) {r' : ℕ} (h : r' ≠ r) :
    (s.recordGBCASend r j m).sent r' = s.sent r' := by
  simp [NetworkState.sent, NetworkState.recordGBCASend, Finmap.lookup_insert_of_ne _ h]

@[simp] theorem recordGBCASend_decidedSent [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.recordGBCASend r j m).decidedSent = s.decidedSent := rfl

@[simp] theorem recordGBCASend_F [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.recordGBCASend r j m).F = s.F := rfl

@[simp] theorem recordGBCASend_ghost [DecidableEq M] [Inhabited G] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.recordGBCASend r j m).ghost = s.ghost := rfl

@[simp] theorem recordGBCASend_startedRounds [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) :
    (s.recordGBCASend r j m).startedRounds = s.startedRounds := rfl

@[simp] theorem recordDecided_sent (s : NetworkState n M G)
    (j : Fin n) (b : Bool) : (s.recordDecided j b).sent = s.sent := rfl

@[simp] theorem recordDecided_decidedSent (s : NetworkState n M G)
    (j : Fin n) (b : Bool) :
    (s.recordDecided j b).decidedSent = Function.update s.decidedSent j (insert b (s.decidedSent j))
      := rfl

@[simp] theorem recordDecided_F (s : NetworkState n M G)
    (j : Fin n) (b : Bool) : (s.recordDecided j b).F = s.F := rfl

@[simp] theorem recordDecided_ghost [Inhabited G] (s : NetworkState n M G)
    (j : Fin n) (b : Bool) : (s.recordDecided j b).ghost = s.ghost := rfl

@[simp] theorem recordDecided_startedRounds (s : NetworkState n M G)
    (j : Fin n) (b : Bool) :
    (s.recordDecided j b).startedRounds = s.startedRounds := rfl

@[simp] theorem recordStartedRound_sent (s : NetworkState n M G) (r : ℕ) (id : Fin n) :
    (s.recordStartedRound r id).sent = s.sent := by
  unfold NetworkState.recordStartedRound; split <;> rfl

@[simp] theorem recordStartedRound_decidedSent (s : NetworkState n M G) (r : ℕ) (id : Fin n) :
    (s.recordStartedRound r id).decidedSent = s.decidedSent := by
  unfold NetworkState.recordStartedRound; split <;> rfl

@[simp] theorem recordStartedRound_F (s : NetworkState n M G) (r : ℕ) (id : Fin n) :
    (s.recordStartedRound r id).F = s.F := by
  unfold NetworkState.recordStartedRound; split <;> rfl

@[simp] theorem recordStartedRound_ghost [Inhabited G] (s : NetworkState n M G) (r : ℕ)
    (id : Fin n) : (s.recordStartedRound r id).ghost = s.ghost := by
  unfold NetworkState.recordStartedRound; split <;> rfl

/-- The started rounds after a graded-agreement call: the called round enters them at a caller
outside the corrupted set, and they stand at a corrupted caller (D37). -/
@[simp] theorem recordStartedRound_startedRounds (s : NetworkState n M G) (r : ℕ)
    (id : Fin n) :
    (s.recordStartedRound r id).startedRounds =
      if id ∉ s.F then insert r s.startedRounds else s.startedRounds := by
  unfold NetworkState.recordStartedRound; split <;> rfl

theorem recordStartedRound_startedRounds_of_notMem (s : NetworkState n M G) {r : ℕ}
    {id : Fin n} (h : id ∉ s.F) :
    (s.recordStartedRound r id).startedRounds = insert r s.startedRounds := by
  simp [h]

theorem recordStartedRound_startedRounds_of_mem (s : NetworkState n M G) {r : ℕ}
    {id : Fin n} (h : id ∈ s.F) :
    (s.recordStartedRound r id).startedRounds = s.startedRounds := by
  simp [h]

/-- A graded-agreement call by a process outside the corrupted set at round `r` puts `r` among
the started rounds. -/
theorem mem_recordStartedRound_startedRounds_self (s : NetworkState n M G) (r : ℕ) {id : Fin n}
    (h : id ∉ s.F) : r ∈ (s.recordStartedRound r id).startedRounds := by
  rw [recordStartedRound_startedRounds_of_notMem s h]
  exact Finset.mem_insert_self r s.startedRounds

/-- A graded-agreement call removes no started round. -/
theorem subset_recordStartedRound_startedRounds (s : NetworkState n M G) (r : ℕ)
    (id : Fin n) : s.startedRounds ⊆ (s.recordStartedRound r id).startedRounds := by
  rw [recordStartedRound_startedRounds]
  split
  · exact Finset.subset_insert r s.startedRounds
  · exact Finset.Subset.refl _

end Fields

@[simp] theorem networkCorrupt_sent {P : Parameters} {M G : Type} (s : NetworkState P.n M G)
    (k : Fin P.n) : (NetworkState.corrupt P k s).sent = s.sent := by
  unfold NetworkState.corrupt; split <;> rfl

@[simp] theorem networkCorrupt_decidedSent {P : Parameters} {M G : Type}
    (s : NetworkState P.n M G)
    (k : Fin P.n) : (NetworkState.corrupt P k s).decidedSent = s.decidedSent := by
  unfold NetworkState.corrupt; split <;> rfl

/-- Corruption leaves the ghost where it stands. -/
@[simp] theorem networkCorrupt_ghost {P : Parameters} {M G : Type} [Inhabited G]
    (s : NetworkState P.n M G)
    (k : Fin P.n) : (NetworkState.corrupt P k s).ghost = s.ghost := by
  unfold NetworkState.corrupt; split <;> rfl

/-- Corruption leaves the started rounds where they stand. -/
@[simp] theorem networkCorrupt_startedRounds {P : Parameters} {M G : Type}
    (s : NetworkState P.n M G) (k : Fin P.n) :
    (NetworkState.corrupt P k s).startedRounds = s.startedRounds := by
  unfold NetworkState.corrupt; split <;> rfl

/-! ### The ghost write

The ghost write leaves every field but the ghost alone. It leaves the whole state alone on a
label naming no round, and on a write returning the ghost standing there. -/

section Ghost

variable {n : ℕ} {M E G : Type} [Inhabited G]
    {ghostStep : ExtendedLabel n M E → NetworkState n M G → G → G}

@[simp] theorem writeGhost_sent (s : NetworkState n M G) (L : ExtendedLabel n M E) :
    (s.writeGhost ghostStep L).sent = s.sent := by
  unfold NetworkState.writeGhost; split
  · split_ifs <;> rfl
  · rfl

@[simp] theorem writeGhost_decidedSent (s : NetworkState n M G) (L : ExtendedLabel n M E) :
    (s.writeGhost ghostStep L).decidedSent = s.decidedSent := by
  unfold NetworkState.writeGhost; split
  · split_ifs <;> rfl
  · rfl

@[simp] theorem writeGhost_F (s : NetworkState n M G) (L : ExtendedLabel n M E) :
    (s.writeGhost ghostStep L).F = s.F := by
  unfold NetworkState.writeGhost; split
  · split_ifs <;> rfl
  · rfl

@[simp] theorem writeGhost_startedRounds (s : NetworkState n M G)
    (L : ExtendedLabel n M E) :
    (s.writeGhost ghostStep L).startedRounds = s.startedRounds := by
  unfold NetworkState.writeGhost; split
  · split_ifs <;> rfl
  · rfl

/-- A label naming no round leaves the whole state where it stands. -/
theorem writeGhost_of_round_none (s : NetworkState n M G) {L : ExtendedLabel n M E}
    (h : roundOf L = none) : s.writeGhost ghostStep L = s := by
  unfold NetworkState.writeGhost; rw [h]

/-- A write returning the ghost standing at the round the label names leaves the whole state
where it stands. -/
theorem writeGhost_of_ghostStep_unchanged (s : NetworkState n M G) {L : ExtendedLabel n M E}
    (h : ∀ r, roundOf L = some r → ghostStep L s (s.ghost r) = s.ghost r) :
    s.writeGhost ghostStep L = s := by
  unfold NetworkState.writeGhost
  split
  · next r hr => exact if_pos (h r hr)
  · rfl

/-- The ghost of the round the label names, after the write. -/
theorem writeGhost_ghost_self (s : NetworkState n M G) {L : ExtendedLabel n M E} {r : ℕ}
    (h : roundOf L = some r) :
    (s.writeGhost ghostStep L).ghost r = ghostStep L s (s.ghost r) := by
  unfold NetworkState.writeGhost; rw [h]; dsimp only
  split_ifs with hg
  · exact hg.symm
  · simp [NetworkState.ghost, Finmap.lookup_insert]

/-- The ghost of any other round is untouched. -/
theorem writeGhost_ghost_ne (s : NetworkState n M G) {L : ExtendedLabel n M E} {r r' : ℕ}
    (h : roundOf L = some r) (hne : r' ≠ r) :
    (s.writeGhost ghostStep L).ghost r' = s.ghost r' := by
  unfold NetworkState.writeGhost; rw [h]; dsimp only
  split_ifs
  · rfl
  · simp [NetworkState.ghost, Finmap.lookup_insert_of_ne _ hne]

end Ghost

/-! ### Removing the ghost

`NetworkState.forgetGhost` sends the network's state to the state over the trivial ghost `Unit`,
and it commutes with each of the network's four writes other than the ghost write. Over `Unit`
the ghost write is the identity, so the removal of a ghost write is the removal of the state it
starts from. -/

section Forget

variable {n : ℕ} {M E G : Type}

@[simp] theorem forgetGhost_sent (s : NetworkState n M G) :
    s.forgetGhost.sent = s.sent := rfl

@[simp] theorem forgetGhost_decidedSent (s : NetworkState n M G) :
    s.forgetGhost.decidedSent = s.decidedSent := rfl

@[simp] theorem forgetGhost_F (s : NetworkState n M G) : s.forgetGhost.F = s.F := rfl

@[simp] theorem forgetGhost_startedRounds (s : NetworkState n M G) :
    s.forgetGhost.startedRounds = s.startedRounds := rfl

@[simp] theorem forgetGhost_recordGBCASend [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) :
    (s.recordGBCASend r j m).forgetGhost = s.forgetGhost.recordGBCASend r j m := rfl

@[simp] theorem forgetGhost_recordDecided (s : NetworkState n M G) (j : Fin n) (b : Bool) :
    (s.recordDecided j b).forgetGhost = s.forgetGhost.recordDecided j b := rfl

@[simp] theorem forgetGhost_corrupt {P : Parameters} (s : NetworkState P.n M G)
    (k : Fin P.n) :
    (NetworkState.corrupt P k s).forgetGhost = NetworkState.corrupt P k s.forgetGhost := by
  unfold NetworkState.corrupt
  simp only [forgetGhost_F]
  split <;> rfl

@[simp] theorem forgetGhost_recordStartedRound (s : NetworkState n M G) (r : ℕ) (id : Fin n) :
    (s.recordStartedRound r id).forgetGhost = s.forgetGhost.recordStartedRound r id := by
  unfold NetworkState.recordStartedRound
  simp only [forgetGhost_F]
  split <;> rfl

/-- The ghost write leaves the removal where it stands. -/
@[simp] theorem forgetGhost_writeGhost [Inhabited G] (s : NetworkState n M G)
    (ghostStep : ExtendedLabel n M E → NetworkState n M G → G → G) (L : ExtendedLabel n M E) :
    (s.writeGhost ghostStep L).forgetGhost = s.forgetGhost := by
  unfold NetworkState.writeGhost
  split
  · split_ifs <;> rfl
  · rfl

/-- Over the trivial ghost the ghost write is the identity. -/
@[simp] theorem writeGhost_unit (s : NetworkState n M Unit) (L : ExtendedLabel n M E) :
    s.writeGhost (fun _ _ _ => ()) L = s :=
  writeGhost_of_ghostStep_unchanged s fun _ _ => rfl

end Forget

end Implementation
end ABA
end PLTS
