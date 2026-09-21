/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.Implementation.System

/-!
# The protocol as it runs

The subject of the whole chain: `n` programs, one per process, beside one
network adversary and the coin oracle. A program reads its own records, its own
received sets and its own replacement flag, and nothing else about corruption: not
the corrupted set, not the budget, not another process's status (D23). The
adversary holds the round-tagged message sets, the DECIDED sets and the
corrupted set with its budget, and it is the sole authority on the Byzantine
labels. The coin oracle is held at specification level.

The shape of that reading is the flat reading of `ABA/Implementation/System.lean`, which
carries the round loop, the DECIDED sets, the coin handshake, corruption, the
network adversary and the composition pipeline for any graded-agreement
implementation. This file supplies the things a reading fixes and
nothing else:

* the stage message type, `GBCA.ByABDY.Message` — the five message levels of
  `GBCA/ABDY/Implementation.lean` (D18);
* the per-process per-round stage record, `GBCA.ByABDY.RoundRecord`, held by round in a
  finite map (D22);
* the rows of the implementation, `RoundStep`: the graded-agreement call, the
  eight stage multicasts, the stage delivery, the call against an
  already-called record, and the three graded returns;
* the network adversary's ghost — the type `Option Bool` of a round's bound
  bit, the write `abdyGhostStep`, the read `abdyGhostOut` and the guard
  `abdyAnnouncedBound` the two return rows put on the announced bit.

`ABDY.protocol P` is the flat reading at those three, named for the authors of
the implementation it runs, as `AFW.protocol P` is named for the authors of the
gather-based one. Its per-process record is a round-loop record beside a
stage-side record, and the stage records a process holds are retained across
the round advance, a round never touched reading as the initial record (D22).

## The stage-side rows

Every guard reads the process's own record. A stage-side row reads and writes
the stage record of the round its label tags, whichever round the round loop is
in, and is guarded by `p.terminated = false` (D22). The rows are taken in the
wait-until order of ABDY22's Algorithm 6 from the `BIND` level down, each of
those levels requiring the process's own send at the level below; the `VOTE`
rows ask for no own send, the `ECHO` they read being sent by an `upon` handler
that may still be pending. A rendezvous row carries the process's half of a
joint step with the network: on a send the record write, on a delivery the
recv write. The Byzantine stage rows have no row at the process they name
(D11, D22). The three return rows take the bit their label announces free: the
bit is the network's ghost output and the program neither guards on it nor
records it.
-/

namespace PLTS
namespace ABA
namespace ABDY

open Implementation Composition

/-! ### The stage-side vocabulary at ABDY22's implementation -/

/-- The stage-side record of one process: the stage record of every round the
process has touched, and whether it has terminated (D22). -/
abbrev RoundRecordMap (n : ℕ) : Type := Implementation.RoundRecordMap (GBCA.ByABDY.RoundRecord n)

/-- ABDY22's stage record, as the flat reading consumes it. -/
instance instIsRoundRecord (n : ℕ) : IsRoundRecord n GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord n)
  where
  initial := GBCA.ByABDY.RoundRecord.initial n
  deliverTo p k m := p.deliverTo k m

namespace RoundRecordMap

variable {n : ℕ}

/-- The initial stage-side record: no round touched, not terminated. -/
def initial (n : ℕ) : RoundRecordMap n := Implementation.RoundRecordMap.initial
  (GBCA.ByABDY.RoundRecord n)

@[simp] theorem initial_roundRecord (n r : ℕ) :
    (initial n).roundRecord r = GBCA.ByABDY.RoundRecord.initial n :=
  Implementation.RoundRecordMap.initial_roundRecord r

@[simp] theorem roundRecord_setRoundRecord_ne (q : RoundRecordMap n) (r : ℕ)
    (p : GBCA.ByABDY.RoundRecord n) {r' : ℕ} (h : r' ≠ r) :
    (q.setRoundRecord r p).roundRecord r' = q.roundRecord r' :=
  Implementation.RoundRecordMap.roundRecord_setRoundRecord_ne q r p h

end RoundRecordMap

/-- The state of one process: its round-loop record and its stage-side record
(D22). -/
abbrev ProcessRecord (n : ℕ) : Type := Implementation.ProcessRecord n (GBCA.ByABDY.RoundRecord n)

/-! ### The network adversary's state at ABDY22's implementation -/

/-- The state of the network adversary: the round-tagged message sets, the
DECIDED sets, the corrupted set with its budget, and the bound bit of every
round. -/
abbrev NetworkState (n : ℕ) : Type := Implementation.NetworkState n GBCA.ByABDY.Message (Option
  Bool)

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
abbrev NetworkState.recordDecided {n : ℕ} (s : NetworkState n) (j : Fin n) (b : Bool) : NetworkState
  n :=
  Implementation.NetworkState.recordDecided s j b

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
abbrev NetworkState.corrupt (P : Parameters) (id : Fin P.n) (s : NetworkState P.n) : NetworkState
  P.n :=
  Implementation.NetworkState.corrupt P id s

/-! ### The network adversary's ghost at ABDY22's implementation

The bound bit of a round is a ghost output: the specification announces it on
every return label (`ABA/GBCA/Specification.lean`) and no program reads it. At this
reading the network adversary holds it, one bit per round, in the ghost record
`Implementation.NetworkState.ghostRecord`.

`abdyGhostStep` writes it. A return records the bit its own label announces if
the round has none on record and leaves the record alone otherwise, so the
record is write-once and both returns of a round — the honest one and the
Byzantine one — write it the same way. Every other row leaves it alone.

`abdyGhostOut` reads it out: the bit on record if the round has one, and
`GBCA.ByABDY.boundOf` of the round's sent sets, the corrupted set and the outcome
otherwise. This is the reading of the round's bound bit that
`GBCA/ABDY/Implementation.lean` holds in its own network state, computed here from the
network's sent sets instead. `abdyAnnouncedBound` is the guard of the two
return rows: the bit a return announces is `abdyGhostOut` of the round. -/

/-- The ghost write of a row: a return records the bit its label announces
where the round has none on record; every other row leaves the record alone. -/
def abdyGhostStep (P : Parameters) :
    ExtendedLabel P.n → NetworkState P.n → Option Bool → Option Bool
  | Sum.inl (.retG _ _ _ bnd), _, g => some (g.getD bnd)
  | Sum.inr (.byzantineRetG _ _ _ bnd), _, g => some (g.getD bnd)
  | _, _, g => g

/-- The ghost output of a return: the round's bound bit on record, and
`GBCA.ByABDY.boundOf` of the round's messages where there is none. -/
def abdyGhostOut (P : Parameters) (s : NetworkState P.n) (r : ℕ) (_id : Fin P.n)
    (out : GBCAOutput) : Bool :=
  (s.ghostRecord r).getD (GBCA.ByABDY.boundOf (s.sent r) s.F out)

/-- The bit the network adversary announces on a return: the round's ghost
output, and no other. This is the relation the flat reading's `ghostOut`
parameter takes at this instantiation. It is reducible, so the guard of the two
return rows is the equation itself. -/
abbrev abdyAnnouncedBound (P : Parameters) (s : NetworkState P.n) (r : ℕ) (id : Fin P.n)
    (out : GBCAOutput) (bnd : Bool) : Prop :=
  bnd = abdyGhostOut P s r id out


/-- A row whose ghost write is the identity leaves the adversary's whole state
where it stands. Every row but the two returns is such a row. -/
theorem writeGhost_abdy_id (P : Parameters) (w : NetworkState P.n) (L : ExtendedLabel P.n)
    (h : ∀ g, abdyGhostStep P L w g = g) :
    w.writeGhost (abdyGhostStep P) L = w := by
  unfold Implementation.NetworkState.writeGhost
  split
  · next r _ => rw [h]; simp
  · rfl

section GhostFrame

variable (P : Parameters) (w : NetworkState P.n)

@[simp] theorem writeGhost_tau :
    w.writeGhost (abdyGhostStep P) (Sum.inl Label.tau) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_callABA (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.callABA id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_retABA (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.retABA id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_callG (r : ℕ) (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.callG r id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_callW (r : ℕ) (id : Fin P.n) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.callW r id)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_retW (r : ℕ) (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.retW r id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_fail (k : Fin P.n) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.fail k)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_gbcaSend (r : ℕ) (j : Fin P.n) (m : GBCA.ByABDY.Message) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.gbcaSend r j m)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_gbcaDeliver (r : ℕ) (i j : Fin P.n) (m : GBCA.ByABDY.Message) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.gbcaDeliver r i j m)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_decidedSend (j : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.decidedSend j b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_decidedDeliver (i j : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.decidedDeliver i j b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_retWPublish (r : ℕ) (id : Fin P.n) (c b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.retWPublish r id c b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_gbcaCallLoop (r : ℕ) (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.gbcaCallLoop r id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineCallG (r : ℕ) (k : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineCallG r k b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineCallGLoop (r : ℕ) (k : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineCallGLoop r k b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineCallW (r : ℕ) (k : Fin P.n) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineCallW r k)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineRetW (r : ℕ) (k : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineRetW r k b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl

/-! The two return rows, which do write. The ghost record of the round the
label names holds the announced bit after the write, and every other round's
record stands still. -/

@[simp] theorem writeGhost_retG_self (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
    (bnd : Bool) :
    (w.writeGhost (abdyGhostStep P) (Sum.inl (.retG r id out bnd))).ghostRecord r
      = some ((w.ghostRecord r).getD bnd) :=
  writeGhost_ghostRecord_self w rfl

theorem writeGhost_retG_ne (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
    {r' : ℕ} (h : r' ≠ r) :
    (w.writeGhost (abdyGhostStep P) (Sum.inl (.retG r id out bnd))).ghostRecord r'
      = w.ghostRecord r' :=
  writeGhost_ghostRecord_ne w rfl h

@[simp] theorem writeGhost_byzantineRetG_self (r : ℕ) (k : Fin P.n) (out : GBCAOutput)
    (bnd : Bool) :
    (w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineRetG r k out bnd))).ghostRecord r
      = some ((w.ghostRecord r).getD bnd) :=
  writeGhost_ghostRecord_self w rfl

theorem writeGhost_byzantineRetG_ne (r : ℕ) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
    {r' : ℕ} (h : r' ≠ r) :
    (w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineRetG r k out bnd))).ghostRecord r'
      = w.ghostRecord r' :=
  writeGhost_ghostRecord_ne w rfl h

end GhostFrame

/-! ### The rows of the graded-agreement implementation -/

/-- The stage-side rows of process `j`: the graded-agreement call, the eight
multicasts of the five message levels, the stage delivery, the call against an
already-called record, and the three graded returns. -/
inductive RoundStep (P : Parameters) (j : Fin P.n) :
    ProcessRecord P.n → ExtendedLabel P.n → PMF (ProcessRecord P.n) → Prop
  /-- The graded-agreement call: the round loop hands its estimate to the stage
  record of round `r`, which opens. The `⟨INPUT, b⟩` multicast is the network's
  half. -/
  | callG_call (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallG) (hr : c.process.round = r)
      (hterm : p.terminated = false)
      (hest : c.process.estimate = some b) (hin : (p.roundRecord r).process.input = none) :
      RoundStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcess { c.process with phase := .awaitG },
          p.setRoundRecord r ((p.roundRecord r).setProcess { (p.roundRecord r).process with
            input := some b,
            sentInput := Function.update (p.roundRecord r).process.sentInput b true })))
  /-- Return with grade `A v`: an `n − f` `ECHO5 v` quorum. The stage record has
  been called and its own `ECHO5` is out. Case (1) heads the algorithm's chain,
  so there is no higher case to deny. -/
  | retG_A (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (v : Bool) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitG) (hr : c.process.round = r)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).receivedCount (.echo5 (some v)))
      (hret : (p.roundRecord r).process.returned = false) :
      RoundStep P j (c, p) (Sum.inl (.retG r j (.A v) bnd))
        (PMF.pure (c.setProcess { c.process with
            estimate := (GBCAOutput.A v).estimate, lastGrade := some (.A v), phase := .toCallW },
          p.setRoundRecord r ((p.roundRecord r).setProcess { (p.roundRecord r).process with
            returned := true })))
  /-- Return with grade `B v`: an `n − f` any-`ECHO5` quorum containing
  `ECHO5 v`, `f + 1` `BIND v`s and `|Valid| > 1`. The stage record has been
  called, its own `ECHO5` is out, and `hnotA` denies case (1) at either bit. -/
  | retG_B (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (v : Bool) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitG) (hr : c.process.round = r)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentEcho5 ≠ none)
      (hnotA : ∀ v, (p.roundRecord r).receivedCount (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).echo5Count)
      (honce : ∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (p.roundRecord r).received k)
      (hbind : P.f + 1 ≤ (p.roundRecord r).receivedCount (.bind (some v)))
      (hval : (p.roundRecord r).bothValid P)
      (hret : (p.roundRecord r).process.returned = false) :
      RoundStep P j (c, p) (Sum.inl (.retG r j (.B v) bnd))
        (PMF.pure (c.setProcess { c.process with
            estimate := (GBCAOutput.B v).estimate, lastGrade := some (.B v), phase := .toCallW },
          p.setRoundRecord r ((p.roundRecord r).setProcess { (p.roundRecord r).process with
            returned := true })))
  /-- Return with grade `C`: an `n − f` `ECHO5 ⊥` quorum and `|Valid| > 1`. The
  stage record has been called, its own `ECHO5` is out, `hnotA` denies case (1)
  at either bit, and `hnotB` denies case (2) in the reduced form
  `GBCA.ByABDY.ImplementationStep.retC` states. -/
  | retG_C (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitG) (hr : c.process.round = r)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentEcho5 ≠ none)
      (hnotA : ∀ v, (p.roundRecord r).receivedCount (.echo5 (some v)) < P.n - P.f)
      (hnotB : ∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (p.roundRecord r).received k) →
        (p.roundRecord r).receivedCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).receivedCount (.echo5 none))
      (hval : (p.roundRecord r).bothValid P)
      (hret : (p.roundRecord r).process.returned = false) :
      RoundStep P j (c, p) (Sum.inl (.retG r j .C bnd))
        (PMF.pure (c.setProcess { c.process with
            estimate := GBCAOutput.C.estimate, lastGrade := some .C, phase := .toCallW },
          p.setRoundRecord r ((p.roundRecord r).setProcess { (p.roundRecord r).process with
            returned := true })))
  /-- The stage `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩` in the stage
  record of round `r`, not yet multicast there (D8, D18, D22). -/
  | gbcaSendRelay (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hcnt : P.f + 1 ≤ (p.roundRecord r).receivedCount (.input b))
      (hsend : (p.roundRecord r).process.sentInput b = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.input b)))
        (PMF.pure (c,
          p.setRoundRecord r ((p.roundRecord r).setProcess { (p.roundRecord r).process with
            sentInput := Function.update (p.roundRecord r).process.sentInput b true })))
  /-- The stage `ECHO`: an `n − f` `INPUT b` quorum (D18, D22). -/
  | gbcaSendEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).receivedCount (.input b))
      (hsend : (p.roundRecord r).process.sentEcho = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.echo b)))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentEcho := some b })))
  /-- The stage `VOTE b`: an `n − f` `ECHO b` quorum. The stage record's own
  `ECHO` is sent by one of the algorithm's `upon` handlers and may still be
  pending, so no own-send condition applies here (D18, D22). -/
  | gbcaSendVoteBit (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).receivedCount (.echo b))
      (hsend : (p.roundRecord r).process.sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.vote (some b))))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentVote := some (some b)
            })))
  /-- The stage `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`, and
  no single-bit `ECHO` quorum on record. The stage record's own `ECHO` is sent
  by one of the algorithm's `upon` handlers and may still be pending, so no
  own-send condition applies here (D18, D22). -/
  | gbcaSendVoteBot (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hnot : ∀ b, (p.roundRecord r).receivedCount (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).echoCount)
      (hval : (p.roundRecord r).bothValid P) (hsend : (p.roundRecord r).process.sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.vote none)))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentVote := some none })))
  /-- The stage `BIND b`: an `n − f` `VOTE b` quorum, the stage record's own
  `VOTE` already out (D18, D22). -/
  | gbcaSendBindBit (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentVote ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).receivedCount (.vote (some b)))
      (hsend : (p.roundRecord r).process.sentBind = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.bind (some b))))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentBind := some (some b)
            })))
  /-- The stage `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`, the
  stage record's own `VOTE` already out, and no single-bit `VOTE` quorum on
  record (D18, D22). -/
  | gbcaSendBindBot (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentVote ≠ none)
      (hnot : ∀ b, (p.roundRecord r).receivedCount (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).voteCount)
      (hval : (p.roundRecord r).bothValid P) (hsend : (p.roundRecord r).process.sentBind = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.bind none)))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentBind := some none })))
  /-- The stage `ECHO5 b`: an `n − f` `BIND b` quorum, the stage record's own
  `BIND` already out (D18, D22). -/
  | gbcaSendEcho5Bit (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentBind ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).receivedCount (.bind (some b)))
      (hsend : (p.roundRecord r).process.sentEcho5 = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.echo5 (some b))))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentEcho5 := some (some b)
            })))
  /-- The stage `ECHO5 ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`, the
  stage record's own `BIND` already out, and no single-bit `BIND` quorum on
  record (D18, D22). -/
  | gbcaSendEcho5Bot (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundRecord r).process.input ≠ none)
      (hlv : (p.roundRecord r).process.sentBind ≠ none)
      (hnot : ∀ b, (p.roundRecord r).receivedCount (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundRecord r).bindCount)
      (hval : (p.roundRecord r).bothValid P) (hsend : (p.roundRecord r).process.sentEcho5 = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.echo5 none)))
        (PMF.pure (c, p.setRoundRecord r
          ((p.roundRecord r).setProcess { (p.roundRecord r).process with sentEcho5 := some none })))
  /-- Stage delivery, receiver's half: file the message under the sender's
  recv row in the stage record of round `r`, whichever round the round loop is
  in. Authenticity is the network's conjunct (D22). -/
  | gbcaDeliverReceive (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.ByABDY.Message) (hh : c.corrupted = false)
      (hterm : p.terminated = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m))
        (PMF.pure (c, p.deliverTo r k m))
  /-- The graded-agreement call against an already-called stage record: the
  round loop moves, the stage record does not. The row carries no termination
  guard, so a terminated process in `toCallG` whose stage record of round `r`
  is uncalled has no row on either call label, a gap this reading
  accepts. -/
  | gbcaCallLoop (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallG) (hr : c.process.round = r)
      (hest : c.process.estimate = some b)
      (hin : (p.roundRecord r).process.input ≠ none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaCallLoop r j b))
        (PMF.pure (c.setProcess { c.process with phase := .awaitG }, p))

/-- The rows above meet the flat reading's conditions: each carries a label of
`roundOwn j`, each fires only at an unreplaced program, each is Dirac, and each
of the three returns takes the announced bit free (D29). -/
instance instIsRoundRuleTable (P : Parameters) :
    IsRoundRuleTable P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (RoundStep P) where
  own h := by
    cases h <;> rfl
  correct h := by
    cases h <;> assumption
  dirac h := by
    cases h <;> exact ⟨_, rfl⟩
  boundBitFree h := by cases h <;> constructor <;> assumption

/-! ### The tables, the automata and the pipeline -/

/-- The step relation of the program of process `j`: the flat reading's rows
beside ABDY22's own stage-side rows. -/
abbrev ABAProgramStep (P : Parameters) (j : Fin P.n) :
    ProcessRecord P.n → ExtendedLabel P.n → PMF (ProcessRecord P.n) → Prop :=
  ProgramStep P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (RoundStep P) j

/-- The message the graded-agreement call multicasts: `⟨INPUT, b⟩`. -/
def gbcaCallPayload (P : Parameters) : Fin P.n → Bool → GBCA.ByABDY.Message := fun _ b => .input b

/-- The step relation of the network adversary. -/
abbrev NetworkStep (P : Parameters) : NetworkState P.n → ExtendedLabel P.n → PMF (NetworkState P.n)
  → Prop :=
  Implementation.NetworkStep P GBCA.ByABDY.Message (Option Bool) (gbcaCallPayload P)
    (abdyGhostStep P)
    (abdyAnnouncedBound P)

/-- The program of process `j`. -/
noncomputable abbrev ABAProgram (P : Parameters) (j : Fin P.n) :
    System (ProcessRecord P.n) (ExtendedLabel P.n) :=
  program P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (RoundStep P) j

/-- The network adversary. -/
noncomputable abbrev network (P : Parameters) : System (NetworkState P.n) (ExtendedLabel P.n) :=
  Implementation.network P GBCA.ByABDY.Message (Option Bool) (gbcaCallPayload P) (abdyGhostStep P)
    (abdyAnnouncedBound P)


/-- The state of the protocol: the process family, the network adversary and
the coin oracle. -/
abbrev ProtocolState (P : Parameters) : Type :=
  Implementation.State P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (Option Bool)

/-- The three components side by side, over the extended alphabet: the
synchronised process group, the network adversary and the lifted oracle. -/
noncomputable def protocolExtended (P : Parameters) : System (ProtocolState P)
  (Composition.ExtendedLabel P.n) :=
  Implementation.systemExtended P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (Option Bool)
    (ABDY.RoundStep P)
    (ABDY.gbcaCallPayload P) (ABDY.abdyGhostStep P) (ABDY.abdyAnnouncedBound P)

/-- **The protocol group**: the rendezvous alphabet hidden, the result read
back over `Label n`. -/
noncomputable def protocolHidden (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.systemHidden P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (Option Bool)
    (ABDY.RoundStep P)
    (ABDY.gbcaCallPayload P) (ABDY.abdyGhostStep P) (ABDY.abdyAnnouncedBound P)

/-- **The protocol system**: the group with the sub-protocol API hidden. -/
noncomputable def protocol (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.system P GBCA.ByABDY.Message (GBCA.ByABDY.RoundRecord P.n) (Option Bool)
    (ABDY.RoundStep
    P)
    (ABDY.gbcaCallPayload P) (ABDY.abdyGhostStep P) (ABDY.abdyAnnouncedBound P)


/-! ### Reading composite transitions

The flat reading's own lemmas, named at this instantiation. -/

theorem protocolHidden_step_iff (P : Parameters) (q : ABDY.ProtocolState P) (l : Label P.n)
    (μ : PMF (ABDY.ProtocolState P)) :
    (ABDY.protocolHidden P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n, (ABDY.protocolExtended P).step q (Sum.inr e) μ) ∨
      (ABDY.protocolExtended P).step q (Sum.inl l) μ :=
  systemHidden_step_iff q l μ

theorem protocol_step_iff (P : Parameters) (q : ABDY.ProtocolState P) (l : Label P.n)
    (μ : PMF (ABDY.ProtocolState P)) :
    (ABDY.protocol P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n, (ABDY.protocolHidden P).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧ (ABDY.protocolHidden P).step q l μ) :=
  system_step_iff q l μ

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem protocolExtended_event_inv (P : Parameters) {u : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n} {e : NetworkEvent P.n}
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolExtended P).step (u, w, o) (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n) (w' : NetworkState P.n)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProgramStep P i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetworkStep P w (Sum.inr e) (PMF.pure w') ∧
      (coinOverRoundAlphabet P).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) :=
  systemExtended_event_inv h

/-- A visible shared-label transition. -/
theorem protocolExtended_label_inv (P : Parameters) {u : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n} {l : Label P.n} (hl : l ≠ Label.tau)
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolExtended P).step (u, w, o) (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n) (w' : NetworkState P.n)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProgramStep P i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetworkStep P w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) :=
  systemExtended_label_inv hl h

/-- A silent shared-label transition: one process terminating, or the network's
own injection. The coin oracle has no silent row, so it contributes none. -/
theorem protocolExtended_tau_inv (P : Parameters) {u : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolExtended P).step (u, w, o) (Sum.inl Label.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcessRecord P.n),
      ABAProgramStep P i (u i) (Sum.inl Label.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetworkStep P w (Sum.inl .tau) (PMF.pure w') ∧ μ = PMF.pure (u, w', o)) :=
  systemExtended_tau_inv h

/-! ### ABDY22's own rows, by label class

Each lemma reads a stage-side row off its label: the participant's row as its
guards together with the Dirac it produces. The idle row of a non-participant
and the replaced program's self-loop are read by the flat reading's own lemmas; here the label names
the acting process, so those two readings are the ones
ruled out. -/

section StageInversion

variable {P : Parameters} {j : Fin P.n} {q : ProcessRecord P.n} {ν : PMF (ProcessRecord P.n)}

theorem programStep_callG_own {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.callG r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .toCallG ∧ q.1.process.round = r ∧ q.2.terminated = false ∧
      q.1.process.estimate = some b ∧ (q.2.roundRecord r).process.input = none ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with phase := .awaitG },
        q.2.setRoundRecord r ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with
          input := some b,
          sentInput := Function.update (q.2.roundRecord r).process.sentInput b true })) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retG_A_own {r : ℕ} {v bnd : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.retG r j (.A v) bnd)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .awaitG ∧ q.1.process.round = r ∧ q.2.terminated = false ∧
      (q.2.roundRecord r).process.input ≠ none ∧ (q.2.roundRecord r).process.sentEcho5 ≠ none ∧
      P.n - P.f ≤ (q.2.roundRecord r).receivedCount (.echo5 (some v)) ∧
      (q.2.roundRecord r).process.returned = false ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with
          estimate := (GBCAOutput.A v).estimate, lastGrade := some (.A v), phase := .toCallW },
        q.2.setRoundRecord r
          ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with returned := true })) :=
            by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retG_B_own {r : ℕ} {v bnd : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.retG r j (.B v) bnd)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .awaitG ∧ q.1.process.round = r ∧ q.2.terminated = false ∧
      (q.2.roundRecord r).process.input ≠ none ∧ (q.2.roundRecord r).process.sentEcho5 ≠ none ∧
      (∀ v, (q.2.roundRecord r).receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundRecord r).echo5Count ∧
      (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (q.2.roundRecord r).received k) ∧
      P.f + 1 ≤ (q.2.roundRecord r).receivedCount (.bind (some v)) ∧
      (q.2.roundRecord r).bothValid P ∧
      (q.2.roundRecord r).process.returned = false ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with
          estimate := (GBCAOutput.B v).estimate, lastGrade := some (.B v), phase := .toCallW },
        q.2.setRoundRecord r
          ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with returned := true })) :=
            by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retG_C_own {r : ℕ} {bnd : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.retG r j .C bnd)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .awaitG ∧ q.1.process.round = r ∧ q.2.terminated = false ∧
      (q.2.roundRecord r).process.input ≠ none ∧ (q.2.roundRecord r).process.sentEcho5 ≠ none ∧
      (∀ v, (q.2.roundRecord r).receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (q.2.roundRecord r).received k) →
        (q.2.roundRecord r).receivedCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ (q.2.roundRecord r).receivedCount (.echo5 none) ∧
      (q.2.roundRecord r).bothValid P ∧
      (q.2.roundRecord r).process.returned = false ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with
          estimate := GBCAOutput.C.estimate, lastGrade := some .C, phase := .toCallW },
        q.2.setRoundRecord r
          ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with returned := true })) :=
            by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_input_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.input b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      P.f + 1 ≤ (q.2.roundRecord r).receivedCount (.input b) ∧
      (q.2.roundRecord r).process.sentInput b = false ∧
      ν = PMF.pure (q.1,
        q.2.setRoundRecord r ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with
          sentInput := Function.update (q.2.roundRecord r).process.sentInput b true })) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_echo_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.echo b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      P.n - P.f ≤ (q.2.roundRecord r).receivedCount (.input b) ∧
      (q.2.roundRecord r).process.sentEcho = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with sentEcho := some b })) :=
          by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_voteBit_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.vote (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      P.n - P.f ≤ (q.2.roundRecord r).receivedCount (.echo b) ∧
      (q.2.roundRecord r).process.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with sentVote := some (some b)
          })) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_voteBot_self {r : ℕ}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.vote none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      (∀ b, (q.2.roundRecord r).receivedCount (.echo b) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundRecord r).echoCount ∧
      (q.2.roundRecord r).bothValid P ∧ (q.2.roundRecord r).process.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with sentVote := some none }))
          := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_bindBit_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.bind (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      (q.2.roundRecord r).process.sentVote ≠ none ∧
      P.n - P.f ≤ (q.2.roundRecord r).receivedCount (.vote (some b)) ∧
      (q.2.roundRecord r).process.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with sentBind := some (some b)
          })) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_bindBot_self {r : ℕ}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.bind none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      (q.2.roundRecord r).process.sentVote ≠ none ∧
      (∀ b, (q.2.roundRecord r).receivedCount (.vote (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundRecord r).voteCount ∧
      (q.2.roundRecord r).bothValid P ∧ (q.2.roundRecord r).process.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with sentBind := some none }))
          := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_echo5Bit_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.echo5 (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      (q.2.roundRecord r).process.sentBind ≠ none ∧
      P.n - P.f ≤ (q.2.roundRecord r).receivedCount (.bind (some b)) ∧
      (q.2.roundRecord r).process.sentEcho5 = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with
          sentEcho5 :=
            some (some b) })) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_echo5Bot_self {r : ℕ}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.echo5 none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundRecord r).process.input ≠ none ∧
      (q.2.roundRecord r).process.sentBind ≠ none ∧
      (∀ b, (q.2.roundRecord r).receivedCount (.bind (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundRecord r).bindCount ∧
      (q.2.roundRecord r).bothValid P ∧ (q.2.roundRecord r).process.sentEcho5 = none ∧
      ν = PMF.pure (q.1, q.2.setRoundRecord r
        ((q.2.roundRecord r).setProcess { (q.2.roundRecord r).process with sentEcho5 := some none
          })) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaDeliver_self {r : ℕ} {k : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaDeliver r j k m)) ν) :
    q.1.corrupted = false ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, q.2.deliverTo r k m) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, rfl⟩
  case gbcaDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaCallLoop_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaCallLoop r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .toCallG ∧ q.1.process.round = r ∧ q.1.process.estimate = some b ∧
      (q.2.roundRecord r).process.input ≠ none ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with phase := .awaitG }, q.2) := by
  cases h
  case roundRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaCallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

end StageInversion

end ABDY

end ABA
end PLTS
