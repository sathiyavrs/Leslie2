/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components

/-!
# The ABA state of the composed system

The round-loop records beside the ABA network, read as one object.

`ABAState` is the pair `(∀ j, RoundLoopRecord) × ABANetworkState`. Its accessors gather the
data the two components hold apart: `processes` reads each process's control
record, `decidedReceived` its receipts, `corrupted` the replacement flag of its
program (D23), and `decidedSent` and `F` the network's sent sets and corrupted
set. The invariant of the core simulation is stated through these accessors, so
it reads the composed state without a change of system.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- **The ABA state**: the `n` round-loop records beside the ABA network. -/
abbrev ABAState (P : Parameters) : Type :=
  (∀ _ : Fin P.n, RoundLoopRecord P.n) × ABANetworkState P.n

namespace ABAState

/-- The control record of process `id`. -/
def processes (s : ABAState P) : Fin P.n → RoundLoopState P.n := fun j => (s.1 j).process

/-- `b ∈ s.decidedSent id` — process `id` has multicast `⟨DECIDED, b⟩`. -/
def decidedSent (s : ABAState P) : Fin P.n → Finset Bool := s.2.decidedSent

/-- `b ∈ s.decidedReceived i j` — `j`'s `⟨DECIDED, b⟩` has been delivered to `i`. -/
def decidedReceived (s : ABAState P) : Fin P.n → Fin P.n → Finset Bool :=
  fun i => (s.1 i).decidedDelivered

/-- `s.corrupted id = true` — the program of process `id` has been replaced
(D23). -/
def corrupted (s : ABAState P) : Fin P.n → Bool := fun j => (s.1 j).corrupted

/-- The corrupted set. -/
def F (s : ABAState P) : Finset (Fin P.n) := s.2.F

@[simp] theorem corrupted_apply (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (a : ABANetworkState P.n)
    (j : Fin P.n) : corrupted (P := P) (C, a) j = (C j).corrupted := rfl

@[simp] theorem processes_apply (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (a : ABANetworkState P.n)
    (j : Fin P.n) : processes (P := P) (C, a) j = (C j).process := rfl
@[simp] theorem decidedSent_apply (C : ∀ _ : Fin P.n,
    RoundLoopRecord P.n) (a : ABANetworkState P.n) : decidedSent (P := P) (C,
      a) = a.decidedSent := rfl
@[simp] theorem decidedReceived_apply (C : ∀ _ : Fin P.n,
    RoundLoopRecord P.n) (a : ABANetworkState P.n) (i : Fin P.n) : decidedReceived (P := P) (C,
      a) i = (C i).decidedDelivered := rfl
@[simp] theorem F_apply (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (a : ABANetworkState P.n) :
    F (P := P) (C, a) = a.F := rfl

/-- Dot notation resolves against `ABAState`, so the invariant reads the
composed state in the accessors' own names. -/
example (s : ABAState P) (j : Fin P.n) : s.processes j = (s.1 j).process := rfl

/-! ### State update helpers -/

/-- The initial ABA state: all round loops idle, nothing multicast, nobody corrupted. -/
def initial (P : Parameters) : ABAState P :=
  (fun _ => RoundLoopRecord.initial P.n, ABANetworkState.initial P.n)

/-! The two components' own initial states project componentwise, so unfolding
`initial` leaves no residue. -/

@[simp] theorem _root_.PLTS.ABA.RoundLoopRecord.initial_process (n : ℕ) :
    (RoundLoopRecord.initial n).process = RoundLoopState.initial n := rfl
@[simp] theorem _root_.PLTS.ABA.RoundLoopRecord.initial_decidedDelivered (n : ℕ) (j : Fin n) :
    (RoundLoopRecord.initial n).decidedDelivered j = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.Composition.ABANetworkState.initial_decidedSent (n : ℕ)
  (j : Fin n) :
    (ABANetworkState.initial n).decidedSent j = ∅ := rfl
@[simp] theorem _root_.PLTS.ABA.Composition.ABANetworkState.initial_F (n : ℕ) :
    (ABANetworkState.initial n).F = ∅ := rfl

@[simp] theorem initial_processes (id : Fin P.n) :
    (initial P).processes id = RoundLoopState.initial P.n := rfl
@[simp] theorem initial_decidedSent (id : Fin P.n) :
    (initial P).decidedSent id = ∅ := rfl
@[simp] theorem initial_decidedReceived (i j : Fin P.n) :
    (initial P).decidedReceived i j = ∅ := rfl
@[simp] theorem initial_corrupted (id : Fin P.n) :
    (initial P).corrupted id = false := rfl
@[simp] theorem initial_F : (initial P).F = ∅ := rfl

/-- The number of distinct senders whose `⟨DECIDED, b⟩` has been delivered to
receiver `id`. -/
def decidedCount (s : ABAState P) (id : Fin P.n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun j => b ∈ s.decidedReceived id j)).card

@[simp] theorem initial_decidedCount (id : Fin P.n) (b : Bool) :
    (initial P).decidedCount id b = 0 := by
  simp [decidedCount]

/-- Update the control record of process `id`. -/
def setProcess (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) : ABAState P :=
  (Function.update s.1 id ((s.1 id).setProcess p), s.2)

@[simp] theorem setProcess_decidedSent (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) :
    (s.setProcess id p).decidedSent = s.decidedSent := rfl
@[simp] theorem setProcess_F (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) :
    (s.setProcess id p).F = s.F := rfl

@[simp] theorem setProcess_decidedReceived (s : ABAState P) (id : Fin P.n)
  (p : RoundLoopState P.n) :
    (s.setProcess id p).decidedReceived = s.decidedReceived := by
  funext i
  by_cases hi : i = id
  · subst hi; simp [setProcess, decidedReceived, RoundLoopRecord.setProcess]
  · simp [setProcess, decidedReceived, Function.update_of_ne hi]

@[simp] theorem setProcess_corrupted (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) :
    (s.setProcess id p).corrupted = s.corrupted := by
  funext i
  by_cases hi : i = id
  · subst hi; simp [setProcess, corrupted, RoundLoopRecord.setProcess]
  · simp [setProcess, corrupted, Function.update_of_ne hi]

@[simp] theorem setProcess_decidedCount (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n)
    (i : Fin P.n) (b : Bool) :
    (s.setProcess id p).decidedCount i b = s.decidedCount i b := by
  simp [decidedCount]

@[simp] theorem setProcess_processes_self (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) :
    (s.setProcess id p).processes id = p := by
  simp [setProcess, processes, RoundLoopRecord.setProcess]

theorem setProcess_processes_ne (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n)
    {k : Fin P.n} (h : k ≠ id) : (s.setProcess id p).processes k = s.processes k := by
  simp [setProcess, processes, Function.update_of_ne h]

/-- Process `id` multicasts `⟨DECIDED, b⟩`: the network sent sets `b` under `id`
(deviation D12′ — the sent only ever grows). -/
def sendDecided (s : ABAState P) (id : Fin P.n) (b : Bool) : ABAState P :=
  (s.1, s.2.recordDecided id b)

@[simp] theorem sendDecided_processes (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).processes = s.processes := rfl
@[simp] theorem sendDecided_decidedReceived (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).decidedReceived = s.decidedReceived := rfl
@[simp] theorem sendDecided_corrupted (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).corrupted = s.corrupted := rfl
@[simp] theorem sendDecided_F (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).F = s.F := rfl
@[simp] theorem sendDecided_decidedSent (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecided id b).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := rfl
@[simp] theorem sendDecided_decidedCount (s : ABAState P) (id : Fin P.n) (b : Bool)
    (i : Fin P.n) (b' : Bool) :
    (s.sendDecided id b).decidedCount i b' = s.decidedCount i b' := rfl

/-- Sent sets only grow under `sendDecided`. -/
theorem sendDecided_decidedSent_mono (s : ABAState P) (id : Fin P.n) (b : Bool)
    {k : Fin P.n} {b' : Bool} (h : b' ∈ s.decidedSent k) :
    b' ∈ (s.sendDecided id b).decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp only [sendDecided_decidedSent, Function.update_self]
    exact Finset.mem_insert_of_mem h
  · simp only [sendDecided_decidedSent, Function.update_of_ne hk]
    exact h

/-- Membership in a post-`sendDecided` sent set: the fresh bit at `id`, or an
old sent member. -/
theorem mem_sendDecided_decidedSent_iff (s : ABAState P) (id : Fin P.n) (b : Bool)
    (k : Fin P.n) (b' : Bool) :
    b' ∈ (s.sendDecided id b).decidedSent k ↔
      (k = id ∧ b' = b) ∨ b' ∈ s.decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp [sendDecided_decidedSent, Function.update_self, Finset.mem_insert]
  · simp [sendDecided_decidedSent, hk]

/-- The adversary delivers `⟨DECIDED, b⟩` from sender `j` to receiver `i`:
the receiver's record files `b` under `j` (per-(receiver, sender, bit),
deviation D12′). -/
def deliverDecided (s : ABAState P) (i j : Fin P.n) (b : Bool) : ABAState P :=
  (Function.update s.1 i ((s.1 i).receiveDecided j b), s.2)

@[simp] theorem deliverDecided_decidedSent (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).decidedSent = s.decidedSent := rfl
@[simp] theorem deliverDecided_F (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).F = s.F := rfl

@[simp] theorem deliverDecided_corrupted (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).corrupted = s.corrupted := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [deliverDecided, corrupted, RoundLoopRecord.receiveDecided]
  · simp [deliverDecided, corrupted, Function.update_of_ne hk]

@[simp] theorem deliverDecided_processes (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).processes = s.processes := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [deliverDecided, processes, RoundLoopRecord.receiveDecided]
  · simp [deliverDecided, processes, Function.update_of_ne hk]

@[simp] theorem deliverDecided_decidedReceived_self (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).decidedReceived i j = insert b (s.decidedReceived i j) := by
  simp [deliverDecided, decidedReceived, RoundLoopRecord.receiveDecided]

/-- Deliveries to other (receiver, sender) edges are untouched. -/
theorem deliverDecided_decidedReceived_of_ne (s : ABAState P) (i j : Fin P.n) (b : Bool)
    {i' j' : Fin P.n} (h : i' ≠ i ∨ j' ≠ j) :
    (s.deliverDecided i j b).decidedReceived i' j' = s.decidedReceived i' j' := by
  rcases h with h | h
  · simp [deliverDecided, decidedReceived, Function.update_of_ne h]
  · by_cases hi : i' = i
    · subst hi
      simp [deliverDecided, decidedReceived, RoundLoopRecord.receiveDecided,
        Function.update_of_ne h]
    · simp [deliverDecided, decidedReceived, Function.update_of_ne hi]

/-- The round advance of process `id` on receiving the coin `c` (fused
DECIDED-send, deviation D10): adopt the coin when the estimate is `⊥`,
multicast `⟨DECIDED, b⟩` when the round's outcome was `grade2 b`, clear the grade and
move to `toCallG` of the next round. -/
def stepRound (s : ABAState P) (id : Fin P.n) (c : Bool) : ABAState P :=
  (match (s.processes id).lastGrade with
    | some (.grade2 b) => s.sendDecided id b
    | _ => s).setProcess id
    { s.processes id with
      estimate := some ((s.processes id).estimate.getD c),
      lastGrade := none,
      round := (s.processes id).round + 1,
      phase := .toCallG }

@[simp] theorem stepRound_processes_self (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).processes id =
      { s.processes id with
        estimate := some ((s.processes id).estimate.getD c),
        lastGrade := none,
        round := (s.processes id).round + 1,
        phase := .toCallG } := by
  unfold stepRound
  exact setProcess_processes_self _ _ _

theorem stepRound_processes_ne (s : ABAState P) (id : Fin P.n) (c : Bool)
    {k : Fin P.n} (h : k ≠ id) : (s.stepRound id c).processes k = s.processes k := by
  unfold stepRound
  cases (s.processes id).lastGrade with
  | none => exact setProcess_processes_ne _ _ _ h
  | some out => cases out <;> exact setProcess_processes_ne _ _ _ h

@[simp] theorem stepRound_decidedReceived (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).decidedReceived = s.decidedReceived := by
  unfold stepRound
  cases (s.processes id).lastGrade with
  | none => exact setProcess_decidedReceived _ _ _
  | some out => cases out <;> exact setProcess_decidedReceived _ _ _

@[simp] theorem stepRound_corrupted (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).corrupted = s.corrupted := by
  unfold stepRound
  cases (s.processes id).lastGrade with
  | none => exact setProcess_corrupted _ _ _
  | some out => cases out <;> exact setProcess_corrupted _ _ _

@[simp] theorem stepRound_F (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).F = s.F := by
  unfold stepRound
  cases (s.processes id).lastGrade with
  | none => rfl
  | some out => cases out <;> rfl

@[simp] theorem stepRound_decidedCount (s : ABAState P) (id : Fin P.n) (c : Bool)
    (i : Fin P.n) (b : Bool) :
    (s.stepRound id c).decidedCount i b = s.decidedCount i b := by
  unfold decidedCount
  rw [stepRound_decidedReceived]

/-- On a `grade2 b` outcome the round advance multicasts `⟨DECIDED, b⟩`. -/
theorem stepRound_decidedSent_of_grade2 (s : ABAState P) (id : Fin P.n) (c b : Bool)
    (h : (s.processes id).lastGrade = some (.grade2 b)) :
    (s.stepRound id c).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := by
  unfold stepRound
  rw [h]
  rfl

/-- Without a grade-2 outcome the round advance leaves the DECIDED sets alone. -/
theorem stepRound_decidedSent_of_not_grade2 (s : ABAState P) (id : Fin P.n) (c : Bool)
    (h : ∀ b, (s.processes id).lastGrade ≠ some (.grade2 b)) :
    (s.stepRound id c).decidedSent = s.decidedSent := by
  unfold stepRound
  cases hg : (s.processes id).lastGrade with
  | none => rfl
  | some out =>
    cases out with
    | grade2 b => exact absurd hg (h b)
    | grade1 b => rfl
    | grade0 => rfl

/-- The round advance when the round carried no grade-2 outcome: the round loop's
own advance, the network untouched. -/
theorem stepRound_of_not_grade2 (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (id : Fin P.n) (co : Bool)
    (hg : ∀ v : Bool, (C id).process.lastGrade ≠ some (.grade2 v)) :
    stepRound (P := P) (C, A) id co
      = (Function.update C id ((C id).stepRound co), A) := by
  unfold stepRound
  cases hlg : (C id).process.lastGrade with
  | none => rw [show (processes (P := P) (C, A) id).lastGrade = none from hlg]; rfl
  | some out =>
    cases out with
    | grade2 v => exact absurd hlg (hg v)
    | grade1 v => rw [show (processes (P := P) (C,
      A) id).lastGrade = some (.grade1 v) from hlg]; rfl
    | grade0 => rw [show (processes (P := P) (C, A) id).lastGrade = some .grade0 from hlg]; rfl

/-- The round advance on a `grade2 b` outcome: the round loop's advance joined with
the network's publication of `b` (the fused DECIDED-send, D10). -/
theorem stepRound_publish (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (id : Fin P.n) (co b : Bool) (hg : (C id).process.lastGrade = some (.grade2 b)) :
    stepRound (P := P) (C, A) id co
      = (Function.update C id ((C id).stepRound co), A.recordDecided id b) := by
  unfold stepRound
  rw [show (processes (P := P) (C, A) id).lastGrade = some (.grade2 b) from hg]
  rfl

/-- Corruption (deviations D1, D23): total, Dirac, monotone in `F`. The
network takes `id` into the corrupted set and the named round loop takes the
replacement flag; every other round loop stands still. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : ABAState P) : ABAState P :=
  (Function.update s.1 id { s.1 id with corrupted := true }, ABANetworkState.corrupt P id s.2)

@[simp] theorem corrupt_processes (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).processes = s.processes := by
  funext k
  by_cases hk : k = id
  · subst hk; simp [corrupt, processes]
  · simp [corrupt, processes, Function.update_of_ne hk]
@[simp] theorem corrupt_decidedReceived (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).decidedReceived = s.decidedReceived := by
  funext k
  by_cases hk : k = id
  · subst hk; simp [corrupt, decidedReceived]
  · simp [corrupt, decidedReceived, Function.update_of_ne hk]
@[simp] theorem corrupt_decidedSent (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).decidedSent = s.decidedSent := by
  unfold corrupt decidedSent ABANetworkState.corrupt; split <;> rfl
@[simp] theorem corrupt_decidedCount (s : ABAState P) (id : Fin P.n)
    (i : Fin P.n) (b : Bool) :
    (s.corrupt P id).decidedCount i b = s.decidedCount i b := by
  unfold decidedCount
  rw [corrupt_decidedReceived]

/-- The named process's program is replaced (D23). -/
@[simp] theorem corrupt_corrupted_self (s : ABAState P) (id : Fin P.n) :
    (s.corrupt P id).corrupted id = true := by
  simp [corrupt, corrupted]

/-- No other process's program is touched (D23). -/
theorem corrupt_corrupted_ne (s : ABAState P) (id : Fin P.n) {k : Fin P.n}
    (h : k ≠ id) : (s.corrupt P id).corrupted k = s.corrupted k := by
  simp [corrupt, corrupted, Function.update_of_ne h]

/-- The corrupted set after a corruption. `F` is the one field corruption
writes, and the budget guard sits in the network component, so the statement is
stated here rather than reached by unfolding. Not a simp lemma: it introduces
an `ite`. -/
theorem corrupt_F (P : Parameters) (id : Fin P.n) (s : ABAState P) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold corrupt F ABANetworkState.corrupt
  split_ifs <;> rfl

end ABAState

end ABA
end PLTS
