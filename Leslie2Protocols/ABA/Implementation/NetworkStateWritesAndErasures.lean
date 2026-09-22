/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.StepInversion

/-!
# The writes on the network's state, and the two erasures

The network's state holds the sent sets, the DECIDED sets, the corrupted set with its budget, and
one ghost record per round. Four writes touch it: a round multicast, a DECIDED multicast,
corruption, and the ghost write. Each touches one field and leaves the others where they stand.
The lemmas here read each field of the state a write delivers, and they are the field algebra the
proofs over the implementation run on. The three writes on the message record leave the ghost
alone, and the ghost write leaves the message record alone and leaves the ghost alone too on a
label naming no round.

Two erasures read the implementation down. `NetworkState.forgetGhost` sends the network's state to
the state over the trivial ghost `Unit`, and it commutes with each of the three writes on the
message record. Over `Unit` the ghost write is the identity, so the erasure of a ghost write is the
erasure of the state it starts from. `forgetBound` sends a label to the label with the announced
bound bit fixed at `false`, and it is the identity elsewhere. Two labels agree under it exactly
when they are equal or are returns of the same round, process and graded outcome, and it keeps a
label inside the sub-protocol API and outside it.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The network's own field algebra

Each of the network's three writes on the message record — a round multicast, a DECIDED
multicast, and corruption — touches one field of the state and leaves the others alone, the ghost
among them. The ghost write touches the ghost and nothing else. -/

section Fields

variable {n : ℕ} {M G : Type}

@[simp] theorem recordGBCASend_sent_self [DecidableEq M]
    (s : NetworkState n M G) (r : ℕ) (j : Fin n) (m : M) :
    (s.recordGBCASend r j m).sent r = Function.update (s.sent r) j (insert m (s.sent r j)) := by
  simp [NetworkState.recordGBCASend]

theorem recordGBCASend_sent_ne [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) {r' : ℕ} (h : r' ≠ r) :
    (s.recordGBCASend r j m).sent r' = s.sent r' := by
  simp [NetworkState.recordGBCASend, Function.update_of_ne h]

@[simp] theorem recordGBCASend_decidedSent [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.recordGBCASend r j m).decidedSent = s.decidedSent := rfl

@[simp] theorem recordGBCASend_F [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.recordGBCASend r j m).F = s.F := rfl

@[simp] theorem recordGBCASend_ghostRecord [DecidableEq M] (s : NetworkState n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.recordGBCASend r j m).ghostRecord = s.ghostRecord := rfl

@[simp] theorem recordDecided_sent (s : NetworkState n M G)
    (j : Fin n) (b : Bool) : (s.recordDecided j b).sent = s.sent := rfl

@[simp] theorem recordDecided_decidedSent (s : NetworkState n M G)
    (j : Fin n) (b : Bool) :
    (s.recordDecided j b).decidedSent = Function.update s.decidedSent j (insert b (s.decidedSent j))
      := rfl

@[simp] theorem recordDecided_F (s : NetworkState n M G)
    (j : Fin n) (b : Bool) : (s.recordDecided j b).F = s.F := rfl

@[simp] theorem recordDecided_ghostRecord (s : NetworkState n M G)
    (j : Fin n) (b : Bool) : (s.recordDecided j b).ghostRecord = s.ghostRecord := rfl

end Fields

@[simp] theorem networkCorrupt_sent {P : Parameters} {M G : Type} (s : NetworkState P.n M G)
    (k : Fin P.n) : (NetworkState.corrupt P k s).sent = s.sent := by
  unfold NetworkState.corrupt; split <;> rfl

@[simp] theorem networkCorrupt_decidedSent {P : Parameters} {M G : Type} (s : NetworkState P.n M G)
    (k : Fin P.n) : (NetworkState.corrupt P k s).decidedSent = s.decidedSent := by
  unfold NetworkState.corrupt; split <;> rfl

/-- Corruption leaves the ghost where it stands. -/
@[simp] theorem networkCorrupt_ghostRecord {P : Parameters} {M G : Type} (s : NetworkState P.n M G)
    (k : Fin P.n) : (NetworkState.corrupt P k s).ghostRecord = s.ghostRecord := by
  unfold NetworkState.corrupt; split <;> rfl

/-! ### The ghost write

The ghost write leaves the message record alone, and it leaves the ghost alone
too on a label naming no round. -/

section Ghost

variable {n : ℕ} {M G : Type}
    {ghostStep : ExtendedLabel n M → NetworkState n M G → G → G}

@[simp] theorem writeGhost_sent (s : NetworkState n M G) (L : ExtendedLabel n M) :
    (s.writeGhost ghostStep L).sent = s.sent := by
  unfold NetworkState.writeGhost; split <;> rfl

@[simp] theorem writeGhost_decidedSent (s : NetworkState n M G) (L : ExtendedLabel n M) :
    (s.writeGhost ghostStep L).decidedSent = s.decidedSent := by
  unfold NetworkState.writeGhost; split <;> rfl

@[simp] theorem writeGhost_F (s : NetworkState n M G) (L : ExtendedLabel n M) :
    (s.writeGhost ghostStep L).F = s.F := by
  unfold NetworkState.writeGhost; split <;> rfl

/-- A label naming no round leaves the whole state where it stands. -/
theorem writeGhost_of_round_none (s : NetworkState n M G) {L : ExtendedLabel n M}
    (h : roundOf L = none) : s.writeGhost ghostStep L = s := by
  unfold NetworkState.writeGhost; rw [h]

/-- The ghost record of the round the label names, after the write. -/
theorem writeGhost_ghostRecord_self (s : NetworkState n M G) {L : ExtendedLabel n M} {r : ℕ}
    (h : roundOf L = some r) :
    (s.writeGhost ghostStep L).ghostRecord r = ghostStep L s (s.ghostRecord r) := by
  unfold NetworkState.writeGhost; rw [h]; simp

/-- The ghost record of any other round is untouched. -/
theorem writeGhost_ghostRecord_ne (s : NetworkState n M G) {L : ExtendedLabel n M} {r r' : ℕ}
    (h : roundOf L = some r) (hne : r' ≠ r) :
    (s.writeGhost ghostStep L).ghostRecord r' = s.ghostRecord r' := by
  unfold NetworkState.writeGhost; rw [h]; simp [Function.update_of_ne hne]

end Ghost

/-! ### Dropping the ghost

Two erasures. `NetworkState.forgetGhost` sends the network's state to the state
over the trivial ghost `Unit`, and it commutes with each of the adversary's
three writes on the message record. Over `Unit` the ghost write is the
identity, so the erasure of a ghost write is the erasure of the state it
starts from. `forgetBound` sends a label to the label with the announced bound
bit fixed at `false`, and it is the identity elsewhere; two labels agree under
it exactly when they are equal or are returns of the same round, process and
graded outcome. -/

section Forget

variable {n : ℕ} {M G : Type}

@[simp] theorem forgetGhost_sent (s : NetworkState n M G) :
    s.forgetGhost.sent = s.sent := rfl

@[simp] theorem forgetGhost_decidedSent (s : NetworkState n M G) :
    s.forgetGhost.decidedSent = s.decidedSent := rfl

@[simp] theorem forgetGhost_F (s : NetworkState n M G) : s.forgetGhost.F = s.F := rfl

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

/-- The ghost write leaves the erasure where it stands. -/
@[simp] theorem forgetGhost_writeGhost (s : NetworkState n M G)
    (ghostStep : ExtendedLabel n M → NetworkState n M G → G → G) (L : ExtendedLabel n M) :
    (s.writeGhost ghostStep L).forgetGhost = s.forgetGhost := by
  unfold NetworkState.writeGhost
  split <;> rfl

/-- Over the trivial ghost the ghost write is the identity. -/
@[simp] theorem writeGhost_unit (s : NetworkState n M Unit) (L : ExtendedLabel n M) :
    s.writeGhost (fun _ _ _ => ()) L = s := by
  obtain ⟨sent, decidedSent, F, g⟩ := s
  unfold NetworkState.writeGhost
  split
  · exact congrArg _ (funext fun _ => rfl)
  · rfl

/-- The label with the announced bound bit dropped: a graded-agreement return
keeps its round, the process it answers and its graded outcome, and every
other label stands. -/
def forgetBound : Label n → Label n
  | .retG r id out _ => .retG r id out false
  | l => l

@[simp] theorem forgetBound_tau : forgetBound (Label.tau : Label n) = Label.tau := rfl

@[simp] theorem forgetBound_retG (r : ℕ) (id : Fin n) (out : GBCAOutput) (bnd : Bool) :
    forgetBound (Label.retG r id out bnd) = Label.retG r id out false := rfl

/-- Two labels agree under the erasure exactly when they are equal, or are
graded-agreement returns of the same round, process and graded outcome. -/
theorem forgetBound_eq_iff (l l' : Label n) :
    forgetBound l = forgetBound l' ↔
      l = l' ∨ ∃ (r : ℕ) (id : Fin n) (out : GBCAOutput) (b b' : Bool),
        l = Label.retG r id out b ∧ l' = Label.retG r id out b' := by
  constructor
  · intro h
    cases l <;> cases l' <;> simp_all [forgetBound]
  · rintro (rfl | ⟨r, id, out, b, b', rfl, rfl⟩) <;> rfl

/-- The erasure keeps a label inside the sub-protocol API and outside it. -/
@[simp] theorem forgetBound_mem_hiddenAPI (l : Label n) :
    forgetBound l ∈ Label.hiddenAPI n ↔ l ∈ Label.hiddenAPI n := by
  cases l <;> simp [forgetBound]

end Forget

end Implementation
end ABA
end PLTS
