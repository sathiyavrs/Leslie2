/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.Alphabet
import Leslie2Protocols.ABA.Vocabulary.RoundLoop
import Leslie2Protocols.Framework.SynchronisedProduct
import Mathlib.Data.Finmap

/-!
# The implementation of a protocol

The implementation presents the protocol as it runs: `n` programs, one per process,
beside one network holding the message sets, the DECIDED sets and
the corrupted set with its budget, beside the coin oracle. A program reads its
own records, its own received sets and its own replacement flag, and nothing else
about corruption: not the corrupted set, not the budget, not another process's
status (D23).

Everything of that shape which does not depend on the graded-agreement implementation is written
here once. The parameters are the round message type `M`, the per-process per-round record `S`, and
the implementation's own rows, given as a relation `roundStep` embedded in one constructor of the
program table. An implementation supplies the three and inherits the round loop, the DECIDED sets,
the coin handshake, corruption, the network and the composition pipeline.

## The division of rows

A program's row is the implementation's business exactly when its label is one of `roundOwn j`: the
graded-agreement call and return at `j`, `j`'s own round multicast, a round delivery addressed to
`j`, and `j`'s own call against an already-called round record. Every other label — the ABA
interface, the coin handshake, the DECIDED relay and its delivery, the Byzantine handshake rows,
corruption, and the same five label classes at another process — is answered by a row here.
`IsRoundRuleTable` states that division: a program's row on a label outside `roundOwn j` is
one of the rows here, whichever implementation is being read.

## The network

The adversary's table is independent of the implementation except in two
places. The graded-agreement call and its Byzantine handshake row sent the
message the call multicasts, and which message that is belongs to the
implementation; it enters as the parameter `callPayload`. The other is the
ghost.

## The network's ghost

The adversary holds one further record: for each round `r`, a ghost record
`ghostRecord r` of a type `G` the implementation fixes. It belongs to the network and to
no program. No program's row reads it and no program's record holds it.

Two parameters carry it. `ghostStep` writes it. On every row, the record of
the round the label names is replaced by `ghostStep` of that label, the
network's state and the record standing there, and the records of the other
rounds are left where they stand; a label naming no round leaves the whole
ghost alone. `ghostOutput` reads it out. It is a relation on the bit a return
announces: the network's state, the round, the process being answered, the
graded outcome and the bit. It is read by the two graded-agreement return rows —
`retG`, and `byzantineRetG` at a replaced program — each of which fires only with
the bound bit its label carries standing in it. What the read decides is the bit
announced and not whether the row fires: each implementation below instantiates the
relation so that it admits a bit at every state (`ghostOutput_total`,
`ABA/GhostErasure/GhostFreeSystem.lean`). An implementation that computes the
announced bit instantiates the relation as an equation against it. An implementation
that leaves the announcement to the network instantiates it as the full
relation, and the bit is unconstrained.

The content is the implementation's own. ABDY22's implementation and the gather-based one
hold different records and write them at different rows, so `G`, `ghostStep`
and `ghostOutput` are parameters here, as `M`, `S`, `roundStep` and `callPayload`
are. Each of the two writes the record at the first return of a round, from
the sent sets and the corrupted set, and reads the same record back at every
later return of that round. Each instantiates `ghostOutput` as the equation
between the announced bit and that record.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The state of one process -/

/-- The round records of one process: the round record of every round the process has touched, and
whether it has terminated (D22). -/
structure RoundRecordMap (S : Type) : Type where
  /-- The finite map of round records; a round off the map has the initial record. -/
  roundRecords : Finmap (fun _ : ℕ => S)
  /-- Whether this process has terminated (ABDY22 §3, Termination).
  `terminated` is not `returned`: the round-loop record's `returned` says the
  process has fired `retABA`; `terminated` says it has stopped participating. -/
  terminated : Bool

namespace RoundRecordMap

variable {n : ℕ} {M S : Type}

/-- The initial round records: no round touched, not terminated. -/
def initial (S : Type) : RoundRecordMap S where
  roundRecords := ∅
  terminated := false

/-- Retain `p` as the round record of round `r`. -/
def setRoundRecord (q : RoundRecordMap S) (r : ℕ) (p : S) : RoundRecordMap S :=
  { q with roundRecords := q.roundRecords.insert r p }

end RoundRecordMap

/-- What the implementation's round record supplies: the record of a round the process has not
touched, and the filing of a delivered message under its sender's recv row. -/
class IsRoundRecord (n : outParam ℕ) (M : outParam Type) (S : Type) where
  /-- The round record of a round the process has not touched. -/
  initial : S
  /-- File a message under its sender's recv row. -/
  deliverTo : S → Fin n → M → S

namespace RoundRecordMap

variable {n : ℕ} {M S : Type} [IsRoundRecord n M S]

/-- The round record of round `r`: the retained record if the process has touched round `r`, the
initial record otherwise. -/
def roundRecord (q : RoundRecordMap S) (r : ℕ) : S :=
  (q.roundRecords.lookup r).getD IsRoundRecord.initial

/-- File `m` under the recv row of sender `k` in the round record of round `r`. -/
def deliverTo (q : RoundRecordMap S) (r : ℕ) (k : Fin n) (m : M) : RoundRecordMap S :=
  q.setRoundRecord r (IsRoundRecord.deliverTo (q.roundRecord r) k m)

@[simp] theorem initial_roundRecord (r : ℕ) :
    (initial S).roundRecord r = (IsRoundRecord.initial : S) := by
  simp [roundRecord, initial]

@[simp] theorem initial_terminated (S : Type) : (initial S).terminated = false := rfl

@[simp] theorem roundRecord_setRoundRecord_self (q : RoundRecordMap S) (r : ℕ) (p : S) :
    (q.setRoundRecord r p).roundRecord r = p := by
  simp [roundRecord, setRoundRecord, Finmap.lookup_insert]

@[simp] theorem roundRecord_setRoundRecord_ne (q : RoundRecordMap S) (r : ℕ) (p : S)
    {r' : ℕ} (h : r' ≠ r) : (q.setRoundRecord r p).roundRecord r' = q.roundRecord r' := by
  simp [roundRecord, setRoundRecord, Finmap.lookup_insert_of_ne _ h]

@[simp] theorem terminated_setRoundRecord (q : RoundRecordMap S) (r : ℕ) (p : S) :
    (q.setRoundRecord r p).terminated = q.terminated := rfl

@[simp] theorem terminated_deliverTo (q : RoundRecordMap S) (r : ℕ) (k : Fin n)
    (m : M) : (q.deliverTo r k m).terminated = q.terminated := rfl

end RoundRecordMap

/-- The state of one process: its round-loop record and its round records (D22). -/
abbrev ProcessRecord (n : ℕ) (S : Type) : Type := RoundLoopRecord n × RoundRecordMap S

/-! ### The round a label names -/

/-- The round a label of the extended alphabet names, if any. A shared label
names a round when it is a graded-agreement handshake, which is
`Label.gbcaRound`; a rendezvous label names the round its constructor carries.
The ABA interface, corruption, the DECIDED relay and the DECIDED delivery name
no round. This is the round whose ghost record a row writes. -/
def roundOf {n : ℕ} {M : Type} : ExtendedLabel n M → Option ℕ
  | Sum.inl l => l.gbcaRound
  | Sum.inr (.gbcaSend r _ _) => some r
  | Sum.inr (.gbcaDeliver r _ _ _) => some r
  | Sum.inr (.decidedSend _ _) => none
  | Sum.inr (.decidedDeliver _ _ _) => none
  | Sum.inr (.retWPublish r _ _ _) => some r
  | Sum.inr (.gbcaCallLoop r _ _) => some r
  | Sum.inr (.byzantineCallG r _ _) => some r
  | Sum.inr (.byzantineCallGLoop r _ _) => some r
  | Sum.inr (.byzantineRetG r _ _ _) => some r
  | Sum.inr (.byzantineCallW r _) => some r
  | Sum.inr (.byzantineRetW r _ _) => some r

/-! ### The network's state -/

/-- The state of the network: the round-tagged message sets, the
DECIDED sets, the corrupted set with its budget, and the ghost record of every
round. -/
structure NetworkState (n : ℕ) (M : Type) (G : Type) : Type where
  /-- `sent r j` — the round-`r` messages process `j` has multicast (D5). -/
  sent : ℕ → Fin n → Finset M
  /-- `decidedSent j` — the DECIDED payloads process `j` has multicast (D12′). -/
  decidedSent : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- `ghostRecord r` — the ghost record the network holds for round `r`. No
  program reads it. -/
  ghostRecord : ℕ → G

namespace NetworkState

variable {n : ℕ} {M G : Type} [DecidableEq M]

/-- The initial network: nothing multicast, nobody corrupted, every round's
ghost record the default one. -/
def initial (n : ℕ) (M G : Type) [Inhabited G] : NetworkState n M G where
  sent := fun _ _ => ∅
  decidedSent := fun _ => ∅
  F := ∅
  ghostRecord := fun _ => default

/-- Sent `m` under sender `j` in round `r` (D5). -/
def recordGBCASend (s : NetworkState n M G) (r : ℕ) (j : Fin n) (m : M) : NetworkState n M G :=
  { s with
    sent :=
      Function.update s.sent r (Function.update (s.sent r) j (insert m (s.sent r j))) }

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def recordDecided (s : NetworkState n M G) (j : Fin n) (b : Bool) : NetworkState n M G :=
  { s with decidedSent := Function.update s.decidedSent j (insert b (s.decidedSent j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : NetworkState P.n M G) : NetworkState P.n M G :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

/-- The ghost write of a row: `ghostStep` applied to the record of the round
`L` names, the records of the other rounds left where they stand. A label
naming no round leaves the whole ghost alone. -/
def writeGhost (s : NetworkState n M G)
    (ghostStep : ExtendedLabel n M → NetworkState n M G → G → G) (L : ExtendedLabel n M) :
    NetworkState n M G :=
  match roundOf L with
  | some r =>
      { s with ghostRecord := Function.update s.ghostRecord r (ghostStep L s (s.ghostRecord r)) }
  | none => s

/-- The same network state over the trivial ghost: the message record, the
DECIDED sets and the corrupted set stand, and every round's record is `()`. -/
def forgetGhost (s : NetworkState n M G) : NetworkState n M Unit where
  sent := s.sent
  decidedSent := s.decidedSent
  F := s.F
  ghostRecord := fun _ => ()

end NetworkState

/-! ### The labels a round row carries -/

/-- The labels on which a program's row belongs to the graded-agreement implementation: process
`j`'s own call and return at the interface, its own round multicast, a round delivery addressed to
it, and its own call against an already-called round record. Every other label is answered by a row
of `ProgramStep`. -/
def roundOwn {n : ℕ} {M : Type} (j : Fin n) : ExtendedLabel n M → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _ _) => id = j
  | Sum.inr (.gbcaSend _ k _) => k = j
  | Sum.inr (.gbcaDeliver _ i _ _) => i = j
  | Sum.inr (.gbcaCallLoop _ id _) => id = j
  | _ => False

/-- A round label is one the process acts on: the replaced program has no row on either (D23). -/
theorem actsAt_of_roundOwn {n : ℕ} {M : Type} {j : Fin n} {L : ExtendedLabel n M}
    (h : roundOwn j L) : actsAt j L := by
  match L with
  | Sum.inl l => cases l <;> exact h
  | Sum.inr e => cases e <;> first | exact h | exact h.elim

/-! ### The rule table of one program

Process `j`'s program. Every guard reads the process's own record and nothing else: none asks
whether another process is correct, and none asks what this one has multicast. The DECIDED relay and
the ABA return are participation-guarded (D8). The DECIDED rows carry no termination guard, so a
terminated process keeps relaying the payloads it holds. The Byzantine round rows have no row at the
process they name (D11, D22). Every label of the extended alphabet outside `roundOwn j` has a row
here: the participant's, or an idle one.

A corruption replaces the program of the process it names (D23). Every
participant's row carries the health guard `c.corrupted = false`, so the record
stays as it is at the corruption; `failSelf` is the row that writes the flag, and
`corruptedIdle` is the replaced program. That self-loop is taken on every label
other than `τ` and the labels of `actsAt j`, on which the replaced program has
no row at all. -/

/-- The step relation of the program of process `j`, over a graded-agreement implementation given by
its message type, its round record and its rows. -/
inductive ProgramStep (P : Parameters) (M S : Type)
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M →
      PMF (ProcessRecord P.n S) → Prop) (j : Fin P.n) :
    ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) → Prop
  /-- A row of the graded-agreement implementation. -/
  | roundRow (q : ProcessRecord P.n S) (L : ExtendedLabel P.n M) (μ : PMF (ProcessRecord P.n S))
      (h : roundStep j q L μ) : ProgramStep P M S roundStep j q L μ
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (b : Bool)
      (hh : c.corrupted = false) (h : c.process.input = none) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProcess { c.process with
          input := some b, estimate := some b, round := 0, phase := .toCallG }, p))
  /-- Input-enabledness loop on `j`'s own `callABA`: the loop absorbs a call at
  a process holding an input. The `input` row carries the label at a process
  holding none, so the label is enabled in every state and a first call at a
  process whose program stands commits (D36). -/
  | inputLoop (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.process.input ≠ none) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.callABA j b)) (PMF.pure (c, p))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.callABA id b)) (PMF.pure (c, p))
  /-- Return `b` on an `n − f` DECIDED quorum, the round-loop record having
  received its input (D8). Having multicast `b` oneself is a condition on the
  sent, hence the network's conjunct. -/
  | ret (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.process.input ≠ none)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.process.returned = false) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProcess { c.process with returned := true }, p))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.retABA id b)) (PMF.pure (c, p))
  /-- The process terminates (ABDY22 Definitions 3.1/3.2 and the p.7 note on
  termination): its own return is fired and DECIDED receipts from `2f + 1`
  distinct senders are on record, so every process still running will cross the
  relay threshold without further response from this one. -/
  | terminate (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (b : Bool)
      (hh : c.corrupted = false) (hret : c.process.returned = true)
      (hcnt : 2 * P.f + 1 ≤ c.decidedCount b)
      (hterm : p.terminated = false) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl Label.tau)
        (PMF.pure (c, { p with terminated := true }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.callG r id b)) (PMF.pure (c, p))
  /-- A graded-agreement return to another process: not `j`'s business. The
  bound bit the label announces is the network's ghost output, and no program
  reads it, so this row leaves it free. -/
  | retGIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.retG r id out bnd))
        (PMF.pure (c, p))
  /-- `c ← WCC_r()`, the call half at the round loop. -/
  | callW (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (r : ℕ)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallW) (hr : c.process.round = r) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.callW r j))
        (PMF.pure (c.setProcess { c.process with phase := .awaitW }, p))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.callW r id)) (PMF.pure (c, p))
  /-- The coin return without a publication: the round advances and nothing is multicast, the
  round's grade not being a grade-2 outcome (D10). The advance opens a new round; the round records
  the process holds are retained across it (D22). -/
  | retW (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (r : ℕ) (co : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitW) (hr : c.process.round = r)
      (hgr : ∀ v : Bool, c.process.lastGrade ≠ some (.grade2 v)) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.retW r j co))
        (PMF.pure (c.stepRound co, p))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.retW r id co)) (PMF.pure (c, p))
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the row (D23). -/
  | failSelf (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (hh : c.corrupted = false) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.fail j))
        (PMF.pure ({ c with corrupted := true }, p))
  /-- Another process's corruption is not this process's business. -/
  | failIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (k : Fin P.n) (hk : k ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inl (.fail k)) (PMF.pure (c, p))
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `actsAt j`, on which the process has no row at all. -/
  | corruptedIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (L : ExtendedLabel P.n M)
      (hh : c.corrupted = true) (hτ : L ≠ Sum.inl Label.tau) (hown : ¬ actsAt j L) :
      ProgramStep P M S roundStep j (c, p) L (PMF.pure (c, p))
  /-- A round multicast by another process: not `j`'s business. -/
  | gbcaSendIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) (m : M) (hk : k ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.gbcaSend r k m)) (PMF.pure (c, p))
  /-- A round delivery to another process: not `j`'s business. -/
  | gbcaDeliverIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (i k : Fin P.n) (m : M) (hi : i ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.gbcaDeliver r i k m)) (PMF.pure (c, p))
  /-- The DECIDED relay on an `f + 1` quorum, the round-loop record having
  received its input (D8, D12′). Not having multicast `b` is a condition on the
  sent, hence the network's conjunct; the sent insert is the network's half
  too. -/
  | decidedSendRelay (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.process.input ≠ none)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.decidedSend j b)) (PMF.pure (c, p))
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | decidedSendIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.decidedSend k b)) (PMF.pure (c, p))
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is the network's conjunct. -/
  | decidedDeliverReceive (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (k : Fin P.n) (b : Bool) (hh : c.corrupted = false) (hr : b ∉ c.decidedDelivered k) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.decidedDeliver j k b))
        (PMF.pure (c.receiveDecided k b, p))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | decidedDeliverIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.decidedDeliver i k b)) (PMF.pure (c, p))
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the round's outcome was
  `grade2 b`, so the round advance publishes `b`, the sent insert being the network's half. The
  advance opens a new round; the round records the process holds are retained across it (D22). -/
  | retWPublish (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (co : Bool) (b : Bool) (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitW) (hr : c.process.round = r)
      (hgr : c.process.lastGrade = some (.grade2 b)) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.retWPublish r j co b))
        (PMF.pure (c.stepRound co, p))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPublishIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.retWPublish r id co b))
        (PMF.pure (c, p))
  /-- Such a call at another process: not `j`'s business. -/
  | gbcaCallLoopIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.gbcaCallLoop r id b))
        (PMF.pure (c, p))
  /-- A Byzantine graded-agreement call at another process: not `j`'s
  business. The process the label names has no row either (D11, D22). -/
  | byzantineCallGIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.byzantineCallG r k b))
        (PMF.pure (c, p))
  /-- A Byzantine graded-agreement call against an already-called round record (D11): nothing moves
  anywhere. -/
  | byzantineCallGLoopIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.byzantineCallGLoop r k b))
        (PMF.pure (c, p))
  /-- A Byzantine graded-agreement return at another process: not `j`'s
  business. The process the label names has no row either (D11, D22). -/
  | byzantineRetGIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool) (hk : k ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.byzantineRetG r k out bnd))
        (PMF.pure (c, p))
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback,
  no process moves. -/
  | byzantineCallWIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.byzantineCallW r k)) (PMF.pure (c, p))
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback, no process moves. -/
  | byzantineRetWIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.byzantineRetW r k b)) (PMF.pure (c, p))

/-! ### The network

The one local state that holds what no process may see: the sent sets, the corrupted set
and the budget. It participates in every send and every delivery — a send by
recording the message, a delivery by checking that the message is sent — and
it is the sole authority on the Byzantine labels, where its `k ∈ F` guard is
the whole authorisation. -/

/-- The step relation of the network. All transitions are Dirac.
`callPayload id b` is the message the graded-agreement call of `id` at `b`
multicasts. The successor of every row is that row's effect on the sent sets,
the DECIDED sets and the corrupted set, with the ghost record of the round the
label names written by `ghostStep`. The two graded-agreement returns fire only
with the bound bit their label carries standing in `ghostOutput` at the state
before the row, the round, the process being answered and the graded
outcome. -/
inductive NetworkStep (P : Parameters) (M G : Type) [DecidableEq M]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOutput : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop) :
    NetworkState P.n M G → ExtendedLabel P.n M → PMF (NetworkState P.n M G) → Prop
  /-- The network's half of a round multicast: sent the message under its sender. Authenticity is
  the sender's joint participation (D5). -/
  | gbcaSend (s : NetworkState P.n M G) (r : ℕ) (j : Fin P.n) (m : M) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.gbcaSend r j m))
        (PMF.pure ((s.recordGBCASend r j m).writeGhost ghostStep (Sum.inr (.gbcaSend r j m))))
  /-- The network's half of a round delivery: the message must be sent under the named sender.
  Delivery does not consume it (D5). -/
  | gbcaDeliver (s : NetworkState P.n M G) (r : ℕ) (i j : Fin P.n) (m : M)
      (h : m ∈ s.sent r j) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.gbcaDeliver r i j m))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaDeliver r i j m))))
  /-- The network's half of a DECIDED relay: the payload must not be sent
  yet (D12′). -/
  | decidedSend (s : NetworkState P.n M G) (j : Fin P.n) (b : Bool) (h : b ∉ s.decidedSent j) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.decidedSend j b))
        (PMF.pure ((s.recordDecided j b).writeGhost ghostStep (Sum.inr (.decidedSend j b))))
  /-- The network's half of a DECIDED delivery: the payload must be sent
  under the named sender (D12′). -/
  | decidedDeliver (s : NetworkState P.n M G) (i j : Fin P.n) (b : Bool) (h : b ∈ s.decidedSent j) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.decidedDeliver i j b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.decidedDeliver i j b))))
  /-- The network's half of the fused coin return: sent the published payload
  (D10, D12′). -/
  | retWPublish (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.retWPublish r id c b))
        (PMF.pure ((s.recordDecided id b).writeGhost ghostStep (Sum.inr (.retWPublish r id c b))))
  /-- A graded-agreement call against an already-called round record sends nothing. -/
  | gbcaCallLoop (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.gbcaCallLoop r id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaCallLoop r id b))))
  /-- A Byzantine graded-agreement call (D11): authorised here, and the
  message its call multicasts sent here. -/
  | byzantineCallG (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineCallG r k b))
        (PMF.pure ((s.recordGBCASend r k (callPayload k b)).writeGhost ghostStep
          (Sum.inr (.byzantineCallG r k b))))
  /-- A Byzantine graded-agreement call against an already-called round record (D11). -/
  | byzantineCallGLoop (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineCallGLoop r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallGLoop r k b))))
  /-- A Byzantine graded-agreement return (D11). The bound bit stands in the
  ghost relation of the round, as at a return to an unreplaced program: a
  replaced program is answered, and the announcement is the network's. -/
  | byzantineRetG (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hF : k ∈ s.F) (hbnd : ghostOutput s r k out bnd) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineRetG r k out bnd))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetG r k out bnd))))
  /-- A Byzantine coin call (D11). -/
  | byzantineCallW (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineCallW r k))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallW r k))))
  /-- A Byzantine coin return (D11). -/
  | byzantineRetW (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineRetW r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetW r k b))))
  /-- An external input is not the network's business. -/
  | callABAIdle (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.callABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callABA id b))))
  /-- A return requires the returning process to have multicast the payload —
  a condition on its sent (D12′). -/
  | retABA (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) (h : b ∈ s.decidedSent id) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- A corrupted process returns whatever it likes (D23): its program has been
  replaced, so the DECIDED evidence the correct row asks for is not required of
  it. The authorisation is this component's `id ∈ F`, and the process's half is
  the replaced program's self-loop. -/
  | retByzantine (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) (hF : id ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- The graded-agreement call multicasts: the network records the message. -/
  | callG (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.callG r id b))
        (PMF.pure ((s.recordGBCASend r id (callPayload id b)).writeGhost ghostStep
          (Sum.inl (.callG r id b))))
  /-- A graded-agreement return sends nothing, and announces the round's bound
  bit: the label's `bnd` stands in the ghost relation of the round at this
  state. This is the one row of the development that reads the ghost. -/
  | retG (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hbnd : ghostOutput s r id out bnd) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retG r id out bnd))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out bnd))))
  /-- A coin call sends nothing. -/
  | callWIdle (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.callW r id))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callW r id))))
  /-- An unfused coin return sends nothing. -/
  | retWIdle (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retW r id c))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retW r id c))))
  /-- Corruption (deviation D1): total, Dirac, budget-guarded; no process
  record keeps a copy. -/
  | fail (s : NetworkState P.n M G) (k : Fin P.n) (hnew : k ∉ s.F)
      (hbud : s.F.card < P.f) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.fail k))
        (PMF.pure ((s.corrupt P k).writeGhost ghostStep (Sum.inl (.fail k))))
  /-- Byzantine round injection (D5, D11): the network multicasts on behalf of a corrupted
  sender. -/
  | byzantineGBCA (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (m : M) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl .tau)
        (PMF.pure ((s.recordGBCASend r k m).writeGhost ghostStep (Sum.inl .tau)))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate. -/
  | byzantineDecided (s : NetworkState P.n M G) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl .tau)
        (PMF.pure ((s.recordDecided k b).writeGhost ghostStep (Sum.inl .tau)))

/-! ### The automata and the composition pipeline -/

section Programs

variable (P : Parameters) (M S : Type)
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop)

/-- The program of process `j`. -/
noncomputable def program (j : Fin P.n) : System (ProcessRecord P.n S) (ExtendedLabel P.n M) where
  init := (RoundLoopRecord.initial P.n, RoundRecordMap.initial S)
  step := ProgramStep P M S roundStep j

@[simp] theorem program_init (j : Fin P.n) :
    (program P M S roundStep j).init
      = (RoundLoopRecord.initial P.n, RoundRecordMap.initial S) := rfl

@[simp] theorem program_step (j : Fin P.n) (q : ProcessRecord P.n S)
    (l : ExtendedLabel P.n M) (μ : PMF (ProcessRecord P.n S)) :
    (program P M S roundStep j).step q l μ ↔ ProgramStep P M S roundStep j q l μ :=
  Iff.rfl

end Programs

/-- The state of the implementation: the process family, the network and
the coin oracle. -/
abbrev State (P : Parameters) (M S G : Type) : Type :=
  (∀ _ : Fin P.n, ProcessRecord P.n S) × (NetworkState P.n M G × (ℕ → WCC.SpecState P.n))

section NetworkAdversary

variable (P : Parameters) (M G : Type) [DecidableEq M] [Inhabited G]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOutput : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop)

/-- The network. -/
noncomputable def network : System (NetworkState P.n M G) (ExtendedLabel P.n M) where
  init := NetworkState.initial P.n M G
  step := NetworkStep P M G callPayload ghostStep ghostOutput

@[simp] theorem network_init :
    (network P M G callPayload ghostStep ghostOutput).init
      = NetworkState.initial P.n M G := rfl

@[simp] theorem network_step (s : NetworkState P.n M G) (l : ExtendedLabel P.n M)
    (μ : PMF (NetworkState P.n M G)) :
    (network P M G callPayload ghostStep ghostOutput).step s l μ ↔
      NetworkStep P M G callPayload ghostStep ghostOutput s l μ :=
  Iff.rfl

end NetworkAdversary

section Pipe

variable (P : Parameters) (M S G : Type) [DecidableEq M] [Inhabited G]
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop)
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOutput : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop)

/-- The three components in parallel, over the extended alphabet: the synchronised process group,
the network and the lifted oracle. -/
noncomputable def systemExtended : System (State P M S G) (ExtendedLabel P.n M) :=
  (System.synchronisedProduct (program P M S roundStep)).parallel
    ((network P M G callPayload ghostStep ghostOutput).parallel (coinOverExtendedAlphabet P M))

/-- The rendezvous alphabet hidden, the result read back over `Label n`. -/
noncomputable def systemHidden : System (State P M S G) (Label P.n) :=
  ((systemExtended P M S G roundStep callPayload ghostStep ghostOutput).abstract
    (networkEventLabels P.n)).relabel

/-- **The implementation**: the group with the sub-protocol API hidden. -/
noncomputable def system : System (State P M S G) (Label P.n) :=
  (systemHidden P M S G roundStep callPayload ghostStep ghostOutput).abstract
    (Label.hiddenAPI P.n)

end Pipe

/-! ### What an implementation must supply about its own rows -/

/-- What the implementation's graded-agreement rows must satisfy for the readers of
`Implementation/StepInversion.lean` to read the rest of the table off a label: a row of process `j`
carries a label of `roundOwn j`, it fires only at a process whose program has
not been replaced (D23), it is Dirac, and its return takes the announced bit
free (D29). -/
class IsRoundRuleTable (P : Parameters) (M S : Type)
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M →
      PMF (ProcessRecord P.n S) → Prop) : Prop where
  /-- A round row carries a round label. -/
  own : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {L : ExtendedLabel P.n M}
    {μ : PMF (ProcessRecord P.n S)}, roundStep j q L μ → roundOwn j L
  /-- A round row fires only at an unreplaced program. -/
  correct : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {L : ExtendedLabel P.n M}
    {μ : PMF (ProcessRecord P.n S)}, roundStep j q L μ → q.1.corrupted = false
  /-- A round row is Dirac. -/
  dirac : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {L : ExtendedLabel P.n M}
    {μ : PMF (ProcessRecord P.n S)}, roundStep j q L μ → ∃ q', μ = PMF.pure q'
  /-- A program's return row takes the announced bit free (D29): the bit the
  label carries is the network's business, so a return row that fires at one
  bit fires at every other, with the same successor. -/
  boundBitFree : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {r : ℕ} {id : Fin P.n}
    {out : GBCAOutput} {b b' : Bool} {μ : PMF (ProcessRecord P.n S)},
    roundStep j q (Sum.inl (.retG r id out b)) μ →
      roundStep j q (Sum.inl (.retG r id out b')) μ

end Implementation
end ABA
end PLTS
