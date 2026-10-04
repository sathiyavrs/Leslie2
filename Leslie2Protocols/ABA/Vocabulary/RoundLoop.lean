/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels

/-!
# The ABA core (the source blueprint's Algorithm 1 = ABDY22's Algorithm 2)

The per-process algorithm of the round loop of ABDY22's Asynchronous Byzantine
Agreement protocol. The pseudocode is the source blueprint's Algorithm 1,
which realises **ABDY22's Algorithm 2** —
the weak-coin framework `AA_ε`: rounds of GBCA followed by a weak-coin flip,
the coin adopted only on a `⊥` decision — with the DECIDED gossip below in
place of the paper's bare grade-2 commit. (The paper's Algorithm 1 is the
*strong*-coin framework over ungraded BCA and is not encoded anywhere in this
development; algorithm numbers below refer to the source blueprint unless the
paper is named.) Per process, on external input `b`:

    r ← 0
    loop:
      (b, g) ← GBCA_r(b)          -- b ∈ {0,1,⊥}, g ∈ {A,B,C}
      c ← WCC_r()
      if b = ⊥ then b ← c
      else if g = A then multicast ⟨DECIDED, b⟩
      r ← r + 1

    upon ⟨DECIDED, b⟩ from f + 1 senders, not having multicast:
      multicast ⟨DECIDED, b⟩
    upon ⟨DECIDED, b⟩ from n − f senders, having multicast ⟨DECIDED, b⟩:
      return b

The file holds the algorithm alone: the phase `Phase`, the estimate a graded outcome
dictates (`GBCAOutput.estimate`), and the per-process control variables `RoundLoopState`. The
variables carry no sub-protocol state — the `callG`/`retG`/`callW`/`retW` interactions are calls and
returns over the API labels, advancing the process's `phase` and recording the returned data, while
the sub-protocol state itself lives in the round specifications and the common coin — and no network
state: the DECIDED sets and the corrupted set belong to the network. The transitions themselves are
`RoundLoopStep` (`ABA/Composition/Components.lean`), the transitions of the round-loop variables
`RoundLoopVariables` over the extended alphabet, and `Implementation.ProgramStep`
(`ABA/Implementation/System.lean`), the transitions of the protocol program that carries a round
loop beside its round variables. This file realises the assumptions of
`DESIGN-HybridRefinesSpecification.md`: the phase machine (invariant conjunct 4), the DECIDED
diffusion state (conjunct 6), and input coherence
(conjunct 5 — the correct `callG` guard ties the emitted bit to the current estimate).

## Model and deviations (continuing the project's D1–D8)

* **D9 (0-based rounds).** `round : ℕ` starts at `0` where Algorithm 1 starts
  at `r = 1`; the `GBCA_r`/`WCC_r` instance indices shift accordingly.
* **D10 (the DECIDED send of a grade-2 round).** Algorithm 1's `elif g = A: send ⟨DECIDED, b⟩`
  is a transition of its own, `decidedSend`, taken after the coin return. The coin return
  `retW` performs the round advance `RoundLoopVariables.stepRound`: it adopts the coin when
  `estimate = ⊥` and opens the next round. When the round's outcome was `grade2 b`, the advance
  keeps `lastGrade` and enters the phase `toSendDecided`. The DECIDED send then clears
  `lastGrade`, enters `toCallG`, and its network half inserts `b` into the process's DECIDED set.
* **D11 (Byzantine call and return transitions).** Corrupted processes may make their sub-protocol
  calls and returns arbitrarily: each of `callG`/`retG`/`callW`/`retW` has a Byzantine
  transition, authorised by `k ∈ F` at the network and constrained by no phase or estimate. The
  round loop contributes an idle transition to each of them, so the family's calls and returns for
  corrupted ids are never blocked by it.
* **D12′ (per-process DECIDED sets, equivocation-capable).** The DECIDED multicast state is the
  network's per-process sent `decidedSent : Fin n → Finset Bool`, read in the ABA component as
  `decidedSent` (`ABA/Composition/ABAState.lean`) and mirroring graded agreement's D5 sent-set
  pattern. Correct sends insert into the sent: the DECIDED send `decidedSend` of a grade-2 round,
  and the `f + 1` relay `decidedRelay`. In reachable states DECIDED coherence keeps every correct
  sent at card ≤ 1, so the insert is a first write or a re-send of the same bit. Byzantine injection
  (`byzantineDecided`, guarded only by `k ∈ F`) may insert either or both bits at any time — a
  corrupted process may send `DECIDED 0` to one receiver and `DECIDED 1` to another (delivery is
  selective). The synchronised delivery `decidedDeliver` moves one sent bit into the receiver's own
  set `decidedReceived i j` at most once per (receiver, sender, bit) triple, with soundness `b ∈
  decidedSent j` on the network's half; the `retABA` quorum guard counts distinct *senders* per bit
  (`decidedCount`). The per-process sent sets (D12′) let a corrupted process equivocate in the
  DECIDED sets; a single-entry model would bar that — an under-approximation inconsistent with
  graded agreement.
* **D23 (the corrupted process's replaced program).** A corruption replaces the
  program of the process it names. `RoundLoopVariables.corrupted` carries the
  replacement: the process's own half of `fail` writes the flag, every
  transition that reads or writes the process's own variables is guarded by
  `corrupted = false`, and the replaced program self-loops on every label of
  the alphabet other than `τ` and the labels on which the process would act on
  its own sub-protocol messages. Those messages are the business of the Byzantine
  call and return transitions (D11), which carry it with no round-loop transition of the named
  process.

Two further notes: the return transition has **no** correctness check — corrupted
returns must pass the same `n − f` DECIDED count as correct ones, and the
specification's return transition is likewise blind to correctness — and
`lastGrade` always refers to the GBCA return of the round in progress or of the round just
closed. It is cleared by the round advance, or, on a grade-2 outcome, by the DECIDED send.
-/

namespace PLTS
namespace ABA

/-- The phase of one core process. The phases make each
sub-protocol call and return guard crisp:
`idle → toCallG → awaitG → toCallW → awaitW → (next round) toCallG → …`.
On a grade-2 outcome the coin return enters `toSendDecided` (deviation D10), and the
DECIDED send leads from it to the next round's `toCallG`. -/
inductive Phase : Type
  /-- No external input received yet. -/
  | idle
  /-- Ready to call the current round's GBCA. -/
  | toCallG
  /-- Waiting for the current round's GBCA return. -/
  | awaitG
  /-- Ready to call the current round's WCC. -/
  | toCallW
  /-- Waiting for the current round's WCC return. -/
  | awaitW
  /-- Ready to send DECIDED on the grade-2 outcome of the round just closed. -/
  | toSendDecided
  deriving DecidableEq, Repr

/-- The estimate a graded outcome dictates: `grade2 b`/`grade1 b` set the estimate to
`b`, grade `0` clears it to `⊥` (awaiting the coin). -/
def GBCAOutput.estimate : GBCAOutput → Option Bool
  | .grade2 b => some b
  | .grade1 b => some b
  | .grade0 => none

@[simp] theorem GBCAOutput.estimate_grade2 (b : Bool) : (GBCAOutput.grade2 b).estimate = some b :=
  rfl

@[simp] theorem GBCAOutput.estimate_grade1 (b : Bool) : (GBCAOutput.grade1 b).estimate = some b :=
  rfl

@[simp] theorem GBCAOutput.estimate_grade0 : (GBCAOutput.grade0).estimate = none := rfl

/-- The per-process state of the ABA core. (No field mentions `n`; the
parameter is kept so the variables are addressed uniformly as `RoundLoopState n`
alongside the other per-process variables of the development.) -/
structure RoundLoopState (n : ℕ) : Type where
  /-- The original external input (`callABA` payload), `none` before the call. -/
  input : Option Bool
  /-- The current estimate; `none` encodes the algorithm's `⊥` (awaiting the
  coin). -/
  estimate : Option Bool
  /-- The current round (0-based, deviation D9). -/
  round : ℕ
  /-- The phase between the process's own calls and returns. -/
  phase : Phase
  /-- The graded outcome returned by the *current* round's GBCA (`none` before
  the return; cleared by the round advance, or by the DECIDED send on a grade-2 outcome). -/
  lastGrade : Option GBCAOutput
  /-- Whether this process has returned (fired `retABA`). -/
  returned : Bool
  deriving DecidableEq

namespace RoundLoopState

/-- The initial per-process state: no input, estimate `⊥`, round `0`, idle. -/
def initial (n : ℕ) : RoundLoopState n where
  input := none
  estimate := none
  round := 0
  phase := .idle
  lastGrade := none
  returned := false

@[simp] theorem initial_input (n : ℕ) : (initial n).input = none := rfl

@[simp] theorem initial_estimate (n : ℕ) : (initial n).estimate = none := rfl

@[simp] theorem initial_round (n : ℕ) : (initial n).round = 0 := rfl

@[simp] theorem initial_phase (n : ℕ) : (initial n).phase = .idle := rfl

@[simp] theorem initial_lastGrade (n : ℕ) : (initial n).lastGrade = none := rfl

@[simp] theorem initial_returned (n : ℕ) : (initial n).returned = false := rfl

end RoundLoopState

/-! ### The round-loop variables

A process's control variables are not by themselves what the composition moves: a round loop also
holds the DECIDED payloads delivered to it. The structure below pairs the two, and is one component
of the ABA state the core simulation reads (`ABA/Composition/ABAState.lean`). -/

/-- The round-loop variables of one process: its own control variables and the
DECIDED payloads delivered to it, indexed by sender. They hold nothing of
what it has multicast — the DECIDED sets live in the network. -/
structure RoundLoopVariables (n : ℕ) : Type where
  /-- The process's own control variables. -/
  processVariables : RoundLoopState n
  /-- The DECIDED payloads delivered to this process, indexed by sender. -/
  decidedDelivered : Fin n → Finset Bool
  /-- Whether this process's program has been replaced (D23). The process's own
  half of `fail` writes the flag, and the guard of every correct transition reads it.
  The variables beneath the flag are unchanged from that point on. -/
  corrupted : Bool
  deriving DecidableEq

namespace RoundLoopVariables

variable {n : ℕ}

/-- The initial round-loop variables: idle control variables, no received messages, program
not replaced. -/
def initial (n : ℕ) : RoundLoopVariables n where
  processVariables := RoundLoopState.initial n
  decidedDelivered := fun _ => ∅
  corrupted := false

@[simp] theorem initial_corrupted (n : ℕ) : (initial n).corrupted = false := rfl

/-- The number of distinct senders whose `⟨DECIDED, b⟩` this process holds. -/
def decidedCount (q : RoundLoopVariables n) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun k => b ∈ q.decidedDelivered k)).card

/-- Update the control variables. -/
def setProcessVariables (q : RoundLoopVariables n) (p : RoundLoopState n) : RoundLoopVariables n :=
  { q with
  processVariables := p }

@[simp] theorem setProcessVariables_corrupted (q : RoundLoopVariables n) (p : RoundLoopState n) :
    (q.setProcessVariables p).corrupted = q.corrupted := rfl

/-- Record a delivered `⟨DECIDED, b⟩` from sender `k`. -/
def receiveDecided (q : RoundLoopVariables n) (k : Fin n) (b : Bool) : RoundLoopVariables n :=
  { q with
    decidedDelivered :=
      Function.update q.decidedDelivered k (insert b (q.decidedDelivered k)) }

@[simp] theorem receiveDecided_corrupted (q : RoundLoopVariables n) (k : Fin n) (b : Bool) :
    (q.receiveDecided k b).corrupted = q.corrupted := rfl

/-- The round advance on receiving the coin `c`: adopt the coin if the
estimate is `⊥` and open the next round. On a grade-2 outcome the advance keeps the grade and
enters `toSendDecided`, where the DECIDED send of the round just closed is taken; otherwise it
clears the grade and enters `toCallG`. -/
def stepRound (q : RoundLoopVariables n) (c : Bool) : RoundLoopVariables n :=
  match q.processVariables.lastGrade with
  | some (.grade2 _) =>
    q.setProcessVariables
      { q.processVariables with
        estimate := some (q.processVariables.estimate.getD c),
        round := q.processVariables.round + 1,
        phase := .toSendDecided }
  | _ =>
    q.setProcessVariables
      { q.processVariables with
        estimate := some (q.processVariables.estimate.getD c),
        lastGrade := none,
        round := q.processVariables.round + 1,
        phase := .toCallG }

theorem stepRound_of_grade2 (q : RoundLoopVariables n) (c b : Bool)
    (h : q.processVariables.lastGrade = some (.grade2 b)) :
    q.stepRound c = q.setProcessVariables
      { q.processVariables with
        estimate := some (q.processVariables.estimate.getD c),
        round := q.processVariables.round + 1,
        phase := .toSendDecided } := by
  unfold stepRound; rw [h]

theorem stepRound_of_not_grade2 (q : RoundLoopVariables n) (c : Bool)
    (h : ∀ b, q.processVariables.lastGrade ≠ some (.grade2 b)) :
    q.stepRound c = q.setProcessVariables
      { q.processVariables with
        estimate := some (q.processVariables.estimate.getD c),
        lastGrade := none,
        round := q.processVariables.round + 1,
        phase := .toCallG } := by
  unfold stepRound
  split
  · next b' hb => exact absurd hb (h b')
  · rfl

@[simp] theorem stepRound_corrupted (q : RoundLoopVariables n) (c : Bool) :
    (q.stepRound c).corrupted = q.corrupted := by
  unfold stepRound; split <;> rfl

end RoundLoopVariables

end ABA
end PLTS
