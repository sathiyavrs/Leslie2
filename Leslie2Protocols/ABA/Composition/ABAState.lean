/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components

/-!
# The ABA state of the composed system

The round-loop variables beside the ABA network, read as one object.

`ABAState` is the pair `(∀ j, RoundLoopVariables) × ABANetworkState`. Its accessors gather the
data the two components hold apart: `processes` reads each process's control
variables, `decidedReceived` its received DECIDED messages, `corrupted` the replacement flag of its
program (D23), and `decidedSent` and `F` the network's sent sets and corrupted
set. The invariant of the core simulation is stated through these accessors, so
it reads the composed state without a change of system.
-/

namespace PLTS
namespace ABA

open Implementation Composition

variable {P : Parameters}

/-- **The ABA state**: the `n` round-loop variables beside the ABA network. -/
abbrev ABAState (P : Parameters) : Type :=
  (∀ _ : Fin P.n, RoundLoopVariables P.n) × ABANetworkState P.n

namespace ABAState

/-- The control variables of process `id`. -/
def processes (s : ABAState P) : Fin P.n → RoundLoopState P.n := fun j => (s.1 j).processVariables

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

@[simp] theorem corrupted_apply (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (a : ABANetworkState
  P.n)
    (j : Fin P.n) : corrupted (P := P) (C, a) j = (C j).corrupted := rfl

@[simp] theorem processes_apply (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (a : ABANetworkState
  P.n)
    (j : Fin P.n) : processes (P := P) (C, a) j = (C j).processVariables := rfl
@[simp] theorem decidedSent_apply (C : ∀ _ : Fin P.n,
    RoundLoopVariables P.n) (a : ABANetworkState P.n) : decidedSent (P := P) (C,
      a) = a.decidedSent := rfl
@[simp] theorem decidedReceived_apply (C : ∀ _ : Fin P.n,
    RoundLoopVariables P.n) (a : ABANetworkState P.n) (i : Fin P.n) : decidedReceived (P := P) (C,
      a) i = (C i).decidedDelivered := rfl
@[simp] theorem F_apply (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (a : ABANetworkState P.n) :
    F (P := P) (C, a) = a.F := rfl

/-- Dot notation resolves against `ABAState`, so the invariant reads the
composed state in the accessors' own names. -/
example (s : ABAState P) (j : Fin P.n) : s.processes j = (s.1 j).processVariables := rfl

/-! ### State update helpers -/

/-- The initial ABA state: all round loops idle, nothing multicast, nobody corrupted. -/
def initial (P : Parameters) : ABAState P :=
  (fun _ => RoundLoopVariables.initial P.n, ABANetworkState.initial P.n)

/-! The two components' own initial states project componentwise, so unfolding
`initial` leaves no residue. -/

@[simp] theorem _root_.PLTS.ABA.RoundLoopVariables.initial_processVariables (n : ℕ) :
    (RoundLoopVariables.initial n).processVariables = RoundLoopState.initial n := rfl
@[simp] theorem _root_.PLTS.ABA.RoundLoopVariables.initial_decidedDelivered (n : ℕ) (j : Fin n) :
    (RoundLoopVariables.initial n).decidedDelivered j = ∅ := rfl
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

/-- Update the control variables of process `id`. -/
def setProcessVariables (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) : ABAState P :=
  (Function.update s.1 id ((s.1 id).setProcessVariables p), s.2)

@[simp] theorem setProcessVariables_decidedSent (s : ABAState P) (id : Fin P.n) (p : RoundLoopState
  P.n) :
    (s.setProcessVariables id p).decidedSent = s.decidedSent := rfl
@[simp] theorem setProcessVariables_F (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n) :
    (s.setProcessVariables id p).F = s.F := rfl

@[simp] theorem setProcessVariables_decidedReceived (s : ABAState P) (id : Fin P.n)
  (p : RoundLoopState P.n) :
    (s.setProcessVariables id p).decidedReceived = s.decidedReceived := by
  funext i
  by_cases hi : i = id
  · subst hi; simp [setProcessVariables, decidedReceived, RoundLoopVariables.setProcessVariables]
  · simp [setProcessVariables, decidedReceived, Function.update_of_ne hi]

@[simp] theorem setProcessVariables_corrupted (s : ABAState P) (id : Fin P.n) (p : RoundLoopState
  P.n) :
    (s.setProcessVariables id p).corrupted = s.corrupted := by
  funext i
  by_cases hi : i = id
  · subst hi; simp [setProcessVariables, corrupted, RoundLoopVariables.setProcessVariables]
  · simp [setProcessVariables, corrupted, Function.update_of_ne hi]

@[simp] theorem setProcessVariables_decidedCount (s : ABAState P) (id : Fin P.n) (p : RoundLoopState
  P.n)
    (i : Fin P.n) (b : Bool) :
    (s.setProcessVariables id p).decidedCount i b = s.decidedCount i b := by
  simp [decidedCount]

@[simp] theorem setProcessVariables_processes_self (s : ABAState P) (id : Fin P.n) (p :
  RoundLoopState P.n) :
    (s.setProcessVariables id p).processes id = p := by
  simp [setProcessVariables, processes, RoundLoopVariables.setProcessVariables]

theorem setProcessVariables_processes_ne (s : ABAState P) (id : Fin P.n) (p : RoundLoopState P.n)
    {k : Fin P.n} (h : k ≠ id) : (s.setProcessVariables id p).processes k = s.processes k := by
  simp [setProcessVariables, processes, Function.update_of_ne h]

/-- Process `id` multicasts `⟨DECIDED, b⟩`: the network sent sets `b` under `id`
(deviation D12′ — the sent only ever grows). -/
def recordDecided (s : ABAState P) (id : Fin P.n) (b : Bool) : ABAState P :=
  (s.1, s.2.recordDecided id b)

@[simp] theorem recordDecided_processes (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.recordDecided id b).processes = s.processes := rfl
@[simp] theorem recordDecided_decidedReceived (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.recordDecided id b).decidedReceived = s.decidedReceived := rfl
@[simp] theorem recordDecided_corrupted (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.recordDecided id b).corrupted = s.corrupted := rfl
@[simp] theorem recordDecided_F (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.recordDecided id b).F = s.F := rfl
@[simp] theorem recordDecided_decidedSent (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.recordDecided id b).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := rfl
@[simp] theorem recordDecided_decidedCount (s : ABAState P) (id : Fin P.n) (b : Bool)
    (i : Fin P.n) (b' : Bool) :
    (s.recordDecided id b).decidedCount i b' = s.decidedCount i b' := rfl

/-- Sent sets only grow under `recordDecided`. -/
theorem recordDecided_decidedSent_mono (s : ABAState P) (id : Fin P.n) (b : Bool)
    {k : Fin P.n} {b' : Bool} (h : b' ∈ s.decidedSent k) :
    b' ∈ (s.recordDecided id b).decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp only [recordDecided_decidedSent, Function.update_self]
    exact Finset.mem_insert_of_mem h
  · simp only [recordDecided_decidedSent, Function.update_of_ne hk]
    exact h

/-- Membership in a post-`recordDecided` sent set: the fresh bit at `id`, or an
old sent member. -/
theorem mem_recordDecided_decidedSent_iff (s : ABAState P) (id : Fin P.n) (b : Bool)
    (k : Fin P.n) (b' : Bool) :
    b' ∈ (s.recordDecided id b).decidedSent k ↔
      (k = id ∧ b' = b) ∨ b' ∈ s.decidedSent k := by
  by_cases hk : k = id
  · subst hk
    simp [recordDecided_decidedSent, Function.update_self, Finset.mem_insert]
  · simp [recordDecided_decidedSent, hk]

/-- The adversary delivers `⟨DECIDED, b⟩` from sender `j` to receiver `i`:
the receiver's variables file `b` under `j` (per-(receiver, sender, bit),
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
  · subst hk; simp [deliverDecided, corrupted, RoundLoopVariables.receiveDecided]
  · simp [deliverDecided, corrupted, Function.update_of_ne hk]

@[simp] theorem deliverDecided_processes (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).processes = s.processes := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [deliverDecided, processes, RoundLoopVariables.receiveDecided]
  · simp [deliverDecided, processes, Function.update_of_ne hk]

@[simp] theorem deliverDecided_decidedReceived_self (s : ABAState P) (i j : Fin P.n) (b : Bool) :
    (s.deliverDecided i j b).decidedReceived i j = insert b (s.decidedReceived i j) := by
  simp [deliverDecided, decidedReceived, RoundLoopVariables.receiveDecided]

/-- Deliveries to other (receiver, sender) edges are untouched. -/
theorem deliverDecided_decidedReceived_of_ne (s : ABAState P) (i j : Fin P.n) (b : Bool)
    {i' j' : Fin P.n} (h : i' ≠ i ∨ j' ≠ j) :
    (s.deliverDecided i j b).decidedReceived i' j' = s.decidedReceived i' j' := by
  rcases h with h | h
  · simp [deliverDecided, decidedReceived, Function.update_of_ne h]
  · by_cases hi : i' = i
    · subst hi
      simp [deliverDecided, decidedReceived, RoundLoopVariables.receiveDecided,
        Function.update_of_ne h]
    · simp [deliverDecided, decidedReceived, Function.update_of_ne hi]

/-- The round advance of process `id` on receiving the coin `c`: the round loop's own advance
`RoundLoopVariables.stepRound`, the network untouched. It adopts the coin when the estimate is `⊥`
and opens the next round. On a grade-2 outcome it keeps the grade and enters `toSendDecided`;
otherwise it clears the grade and enters `toCallG`. -/
def stepRound (s : ABAState P) (id : Fin P.n) (c : Bool) : ABAState P :=
  (Function.update s.1 id ((s.1 id).stepRound c), s.2)

theorem stepRound_apply (C : ∀ _ : Fin P.n, RoundLoopVariables P.n) (A : ABANetworkState P.n)
    (id : Fin P.n) (co : Bool) :
    stepRound (P := P) (C, A) id co = (Function.update C id ((C id).stepRound co), A) := rfl

theorem stepRound_processes_self_of_grade2 (s : ABAState P) (id : Fin P.n) (c b : Bool)
    (h : (s.processes id).lastGrade = some (.grade2 b)) :
    (s.stepRound id c).processes id =
      { s.processes id with
        estimate := some ((s.processes id).estimate.getD c),
        round := (s.processes id).round + 1,
        phase := .toSendDecided } := by
  simp only [stepRound, processes, Function.update_self]
  rw [RoundLoopVariables.stepRound_of_grade2 _ c b h]
  rfl

theorem stepRound_processes_self_of_not_grade2 (s : ABAState P) (id : Fin P.n) (c : Bool)
    (h : ∀ b, (s.processes id).lastGrade ≠ some (.grade2 b)) :
    (s.stepRound id c).processes id =
      { s.processes id with
        estimate := some ((s.processes id).estimate.getD c),
        lastGrade := none,
        round := (s.processes id).round + 1,
        phase := .toCallG } := by
  simp only [stepRound, processes, Function.update_self]
  rw [RoundLoopVariables.stepRound_of_not_grade2 _ c h]
  rfl

@[simp] theorem stepRound_processes_self_input (s : ABAState P) (id : Fin P.n) (c : Bool) :
    ((s.stepRound id c).processes id).input = (s.processes id).input := by
  simp only [stepRound, processes, Function.update_self, RoundLoopVariables.stepRound]
  split <;> rfl

@[simp] theorem stepRound_processes_self_estimate (s : ABAState P) (id : Fin P.n) (c : Bool) :
    ((s.stepRound id c).processes id).estimate = some ((s.processes id).estimate.getD c) := by
  simp only [stepRound, processes, Function.update_self, RoundLoopVariables.stepRound]
  split <;> rfl

@[simp] theorem stepRound_processes_self_round (s : ABAState P) (id : Fin P.n) (c : Bool) :
    ((s.stepRound id c).processes id).round = (s.processes id).round + 1 := by
  simp only [stepRound, processes, Function.update_self, RoundLoopVariables.stepRound]
  split <;> rfl

@[simp] theorem stepRound_processes_self_returned (s : ABAState P) (id : Fin P.n) (c : Bool) :
    ((s.stepRound id c).processes id).returned = (s.processes id).returned := by
  simp only [stepRound, processes, Function.update_self, RoundLoopVariables.stepRound]
  split <;> rfl

theorem stepRound_processes_ne (s : ABAState P) (id : Fin P.n) (c : Bool)
    {k : Fin P.n} (h : k ≠ id) : (s.stepRound id c).processes k = s.processes k := by
  simp [stepRound, processes, Function.update_of_ne h]

@[simp] theorem stepRound_decidedReceived (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).decidedReceived = s.decidedReceived := by
  funext i
  by_cases hi : i = id
  · subst hi
    simp only [stepRound, decidedReceived, Function.update_self, RoundLoopVariables.stepRound]
    split <;> rfl
  · simp [stepRound, decidedReceived, Function.update_of_ne hi]

@[simp] theorem stepRound_corrupted (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).corrupted = s.corrupted := by
  funext i
  by_cases hi : i = id
  · subst hi; simp [stepRound, corrupted]
  · simp [stepRound, corrupted, Function.update_of_ne hi]

@[simp] theorem stepRound_F (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).F = s.F := rfl

@[simp] theorem stepRound_decidedSent (s : ABAState P) (id : Fin P.n) (c : Bool) :
    (s.stepRound id c).decidedSent = s.decidedSent := rfl

@[simp] theorem stepRound_decidedCount (s : ABAState P) (id : Fin P.n) (c : Bool)
    (i : Fin P.n) (b : Bool) :
    (s.stepRound id c).decidedCount i b = s.decidedCount i b := by
  unfold decidedCount
  rw [stepRound_decidedReceived]

/-- The DECIDED send of process `id` on the grade-2 outcome `grade2 b` of the round it has just
closed: the network sets `b` under `id`, and the process clears the grade and enters the
next round's `toCallG`. -/
def sendDecidedOnGrade2 (s : ABAState P) (id : Fin P.n) (b : Bool) : ABAState P :=
  (s.recordDecided id b).setProcessVariables id
    { s.processes id with lastGrade := none, phase := .toCallG }

theorem sendDecidedOnGrade2_apply (C : ∀ _ : Fin P.n, RoundLoopVariables P.n)
    (A : ABANetworkState P.n) (id : Fin P.n) (b : Bool) :
    sendDecidedOnGrade2 (P := P) (C, A) id b =
      (Function.update C id ((C id).setProcessVariables
        { (C id).processVariables with lastGrade := none, phase := .toCallG }),
        A.recordDecided id b) := rfl

@[simp] theorem sendDecidedOnGrade2_processes_self (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecidedOnGrade2 id b).processes id =
      { s.processes id with lastGrade := none, phase := .toCallG } :=
  setProcessVariables_processes_self _ _ _

theorem sendDecidedOnGrade2_processes_ne (s : ABAState P) (id : Fin P.n) (b : Bool)
    {k : Fin P.n} (h : k ≠ id) : (s.sendDecidedOnGrade2 id b).processes k = s.processes k :=
  setProcessVariables_processes_ne _ _ _ h

@[simp] theorem sendDecidedOnGrade2_decidedSent (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecidedOnGrade2 id b).decidedSent =
      Function.update s.decidedSent id (insert b (s.decidedSent id)) := rfl

/-- Membership in a post-send sent set: the sent bit at `id`, or an old sent member. -/
theorem mem_sendDecidedOnGrade2_decidedSent_iff (s : ABAState P) (id : Fin P.n) (b : Bool)
    (k : Fin P.n) (b' : Bool) :
    b' ∈ (s.sendDecidedOnGrade2 id b).decidedSent k ↔
      (k = id ∧ b' = b) ∨ b' ∈ s.decidedSent k :=
  mem_recordDecided_decidedSent_iff s id b k b'

@[simp] theorem sendDecidedOnGrade2_decidedReceived (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecidedOnGrade2 id b).decidedReceived = s.decidedReceived :=
  setProcessVariables_decidedReceived _ _ _

@[simp] theorem sendDecidedOnGrade2_corrupted (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecidedOnGrade2 id b).corrupted = s.corrupted :=
  setProcessVariables_corrupted _ _ _

@[simp] theorem sendDecidedOnGrade2_F (s : ABAState P) (id : Fin P.n) (b : Bool) :
    (s.sendDecidedOnGrade2 id b).F = s.F := rfl

@[simp] theorem sendDecidedOnGrade2_decidedCount (s : ABAState P) (id : Fin P.n) (b : Bool)
    (i : Fin P.n) (b' : Bool) :
    (s.sendDecidedOnGrade2 id b).decidedCount i b' = s.decidedCount i b' :=
  setProcessVariables_decidedCount _ _ _ _ _

/-- Corruption (deviations D1, D23): total, Dirac, monotone in `F`. The
network takes `id` into the corrupted set and the named round loop takes the
replacement flag; every other round loop is unchanged. -/
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
