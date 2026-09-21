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
# The flat reading of a protocol

A flat reading presents the protocol as it runs: `n` programs, one per process,
beside one network adversary holding the message sets, the DECIDED sets and
the corrupted set with its budget, beside the coin oracle. A program reads its
own records, its own received sets and its own replacement flag, and nothing else
about corruption: not the corrupted set, not the budget, not another process's
status (D23).

Everything of that shape which does not depend on the graded-agreement
implementation is written here once. The parameters are the stage-side message
type `M`, the per-process per-round stage record `S`, and the implementation's
own rows, given as a relation `roundStep` embedded in one constructor of the
program table. A reading supplies the three and inherits the round loop, the
DECIDED sets, the coin handshake, corruption, the network adversary, the
composition pipeline and the inversion lemmas.

## The division of rows

A program's row is the implementation's business exactly when its label is one
of `roundOwn j`: the graded-agreement call and return at `j`, `j`'s own stage
multicast, a stage delivery addressed to `j`, and `j`'s own call against an
already-called stage record. Every other label — the ABA interface, the coin
handshake, the DECIDED relay and its delivery, the Byzantine handshake rows,
corruption, and the same five label classes at another process — is answered
by a row here. The side condition `roundOwn` is what the inversion lemmas
consume: a program's row on a label outside `roundOwn j` is one of the rows
below, whichever implementation is being read.

## The network adversary

The adversary's table is independent of the implementation except in two
places. The graded-agreement call and its Byzantine handshake row sent the
message the call multicasts, and which message that is belongs to the
implementation; it enters as the parameter `callPayload`. The other is the
ghost.

## The network's ghost

The adversary holds one further record: for each round `r`, a ghost record
`ghostRecord r` of a type `G` the reading fixes. It belongs to the network and to
no program. No program's row reads it and no program's record holds it.

Two parameters carry it. `ghostStep` writes it. On every row, the record of
the round the label names is replaced by `ghostStep` of that label, the
network's state and the record standing there, and the records of the other
rounds are left where they stand; a label naming no round leaves the whole
ghost alone. `ghostOut` reads it out. It is a relation on the bit a return
announces: the network's state, the round, the process being answered, the
graded outcome and the bit. It is read by the two graded-agreement return rows —
`retG`, and `byzantineRetG` at a replaced program — each of which fires only with
the bound bit its label carries standing in it. What the read decides is the bit
announced and not whether the row fires: each reading below instantiates the
relation so that it admits a bit at every state (`ghostOut_total`,
`ABA/GhostErasure/GhostFreeSystem.lean`). A reading that computes the
announced bit instantiates the relation as an equation against it. A reading
that leaves the announcement to the adversary instantiates it as the full
relation, and the bit is unconstrained.

The content is the reading's own. ABDY22's reading and the gather-based one
hold different records and write them at different rows, so `G`, `ghostStep`
and `ghostOut` are parameters here, as `M`, `S`, `roundStep` and `callPayload`
are. Each of the two writes the record at the first return of a round, from
the sent sets and the corrupted set, and reads the same record back at every
later return of that round. Each instantiates `ghostOut` as the equation
between the announced bit and that record.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The state of one process -/

/-- The stage-side record of one process: the stage record of every round the
process has touched, and whether it has terminated (D22). -/
structure RoundRecordMap (S : Type) : Type where
  /-- The finite map of stage records; a round off the map has the initial
  record. -/
  roundRecords : Finmap (fun _ : ℕ => S)
  /-- Whether this process has terminated (ABDY22 §3, Termination).
  `terminated` is not `returned`: the round-loop record's `returned` says the
  process has fired `retABA`; `terminated` says it has stopped participating. -/
  terminated : Bool

namespace RoundRecordMap

variable {n : ℕ} {M S : Type}

/-- The initial stage-side record: no round touched, not terminated. -/
def initial (S : Type) : RoundRecordMap S where
  roundRecords := ∅
  terminated := false

/-- Retain `p` as the stage record of round `r`. -/
def setRoundRecord (q : RoundRecordMap S) (r : ℕ) (p : S) : RoundRecordMap S :=
  { q with roundRecords := q.roundRecords.insert r p }

end RoundRecordMap

/-- What a flat reading's stage record supplies: the record of a round the
process has not touched, and the filing of a delivered message under its
sender's recv row. -/
class IsRoundRecord (n : outParam ℕ) (M : outParam Type) (S : Type) where
  /-- The stage record of a round the process has not touched. -/
  initial : S
  /-- File a message under its sender's recv row. -/
  deliverTo : S → Fin n → M → S

namespace RoundRecordMap

variable {n : ℕ} {M S : Type} [IsRoundRecord n M S]

/-- The stage record of round `r`: the retained record if the process has
touched round `r`, the initial record otherwise. -/
def roundRecord (q : RoundRecordMap S) (r : ℕ) : S :=
  (q.roundRecords.lookup r).getD IsRoundRecord.initial

/-- File `m` under the recv row of sender `k` in the stage record of round
`r`. -/
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

/-- The state of one process: its round-loop record and its stage-side record
(D22). -/
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

/-! ### The network adversary's state -/

/-- The state of the network adversary: the round-tagged message sets, the
DECIDED sets, the corrupted set with its budget, and the ghost record of every
round. -/
structure NetworkState (n : ℕ) (M : Type) (G : Type) : Type where
  /-- `sent r j` — the stage-`r` messages process `j` has multicast (D5). -/
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

/-- Sent `m` under sender `j` in stage `r` (D5). -/
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

/-! ### The labels a stage-side row carries -/

/-- The labels on which a program's row belongs to the graded-agreement
implementation: process `j`'s own call and return at the interface, its own
stage multicast, a stage delivery addressed to it, and its own call against an
already-called stage record. Every other label is answered by a row of
`ProgramStep`. -/
def roundOwn {n : ℕ} {M : Type} (j : Fin n) : ExtendedLabel n M → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _ _) => id = j
  | Sum.inr (.gbcaSend _ k _) => k = j
  | Sum.inr (.gbcaDeliver _ i _ _) => i = j
  | Sum.inr (.gbcaCallLoop _ id _) => id = j
  | _ => False

/-- A stage-side label is one the process acts on: the replaced program has no
row on either (D23). -/
theorem actsAt_of_roundOwn {n : ℕ} {M : Type} {j : Fin n} {L : ExtendedLabel n M}
    (h : roundOwn j L) : actsAt j L := by
  match L with
  | Sum.inl l => cases l <;> exact h
  | Sum.inr e => cases e <;> first | exact h | exact h.elim

/-! ### The rule table of one program

Process `j`'s program. Every guard reads the process's own record and nothing
else: none asks whether another process is honest, and none asks what this one
has multicast. The DECIDED relay and the ABA return are participation-guarded
(D8). The DECIDED rows carry no termination guard, so a terminated process
keeps relaying the payloads it holds. The Byzantine stage rows have no row at
the process they name (D11, D22). Every label of the extended alphabet outside
`roundOwn j` has a row here: the participant's, or an idle one.

A corruption replaces the program of the process it names (D23). Every
participant's row carries the health guard `c.corrupted = false`, so the record
freezes at the corruption; `failSelf` is the row that writes the flag, and
`corruptedIdle` is the replaced program. That self-loop is taken on every label
other than `τ` and the labels of `actsAt j`, on which the replaced program has
no row at all. -/

/-- The step relation of the program of process `j`, over a graded-agreement
implementation given by its message type, its stage record and its rows. -/
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
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being an `A` (D10). The advance opens a new
  round; the stage records the process holds are retained across it (D22). -/
  | retW (c : RoundLoopRecord P.n) (p : RoundRecordMap S) (r : ℕ) (co : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitW) (hr : c.process.round = r)
      (hgr : ∀ v : Bool, c.process.lastGrade ≠ some (.A v)) :
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
  /-- A stage multicast by another process: not `j`'s business. -/
  | gbcaSendIdle (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (k : Fin P.n) (m : M) (hk : k ≠ j) :
      ProgramStep P M S roundStep j (c, p) (Sum.inr (.gbcaSend r k m)) (PMF.pure (c, p))
  /-- A stage delivery to another process: not `j`'s business. -/
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
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's grade was `A b`, so the round advance publishes `b`, the sent insert
  being the network's half. The advance opens a new round; the stage records
  the process holds are retained across it (D22). -/
  | retWPublish (c : RoundLoopRecord P.n) (p : RoundRecordMap S)
      (r : ℕ) (co : Bool) (b : Bool) (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitW) (hr : c.process.round = r)
      (hgr : c.process.lastGrade = some (.A b)) :
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
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11): nothing moves anywhere. -/
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

/-! ### The network adversary

The one local state that holds what no process may see: the sent sets, the corrupted set
and the budget. It participates in every send and every delivery — a send by
recording the message, a delivery by checking that the message is sent — and
it is the sole authority on the Byzantine labels, where its `k ∈ F` guard is
the whole authorisation. -/

/-- The step relation of the network adversary. All transitions are Dirac.
`callPayload id b` is the message the graded-agreement call of `id` at `b`
multicasts. The successor of every row is that row's effect on the sent sets,
the DECIDED sets and the corrupted set, with the ghost record of the round the
label names written by `ghostStep`. The two graded-agreement returns fire only
with the bound bit their label carries standing in `ghostOut` at the state
before the row, the round, the process being answered and the graded
outcome. -/
inductive NetworkStep (P : Parameters) (M G : Type) [DecidableEq M]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop) :
    NetworkState P.n M G → ExtendedLabel P.n M → PMF (NetworkState P.n M G) → Prop
  /-- The network's half of a stage multicast: sent the message under its
  sender. Authenticity is the sender's joint participation (D5). -/
  | gbcaSend (s : NetworkState P.n M G) (r : ℕ) (j : Fin P.n) (m : M) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.gbcaSend r j m))
        (PMF.pure ((s.recordGBCASend r j m).writeGhost ghostStep (Sum.inr (.gbcaSend r j m))))
  /-- The network's half of a stage delivery: the message must be sent under
  the named sender. Delivery does not consume it (D5). -/
  | gbcaDeliver (s : NetworkState P.n M G) (r : ℕ) (i j : Fin P.n) (m : M)
      (h : m ∈ s.sent r j) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.gbcaDeliver r i j m))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaDeliver r i j m))))
  /-- The network's half of a DECIDED relay: the payload must not be sent
  yet (D12′). -/
  | decidedSend (s : NetworkState P.n M G) (j : Fin P.n) (b : Bool) (h : b ∉ s.decidedSent j) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.decidedSend j b))
        (PMF.pure ((s.recordDecided j b).writeGhost ghostStep (Sum.inr (.decidedSend j b))))
  /-- The network's half of a DECIDED delivery: the payload must be sent
  under the named sender (D12′). -/
  | decidedDeliver (s : NetworkState P.n M G) (i j : Fin P.n) (b : Bool) (h : b ∈ s.decidedSent j) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.decidedDeliver i j b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.decidedDeliver i j b))))
  /-- The network's half of the fused coin return: sent the published payload
  (D10, D12′). -/
  | retWPublish (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.retWPublish r id c b))
        (PMF.pure ((s.recordDecided id b).writeGhost ghostStep (Sum.inr (.retWPublish r id c b))))
  /-- A graded-agreement call against an already-called stage record sends
  nothing. -/
  | gbcaCallLoop (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.gbcaCallLoop r id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaCallLoop r id b))))
  /-- A Byzantine graded-agreement call (D11): authorised here, and the
  message its call multicasts sent here. -/
  | byzantineCallG (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzantineCallG r k b))
        (PMF.pure ((s.recordGBCASend r k (callPayload k b)).writeGhost ghostStep
          (Sum.inr (.byzantineCallG r k b))))
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11). -/
  | byzantineCallGLoop (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzantineCallGLoop r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallGLoop r k b))))
  /-- A Byzantine graded-agreement return (D11). The bound bit stands in the
  ghost relation of the round, as at a return to an unreplaced program: a
  replaced program is answered, and the announcement is the network's. -/
  | byzantineRetG (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hF : k ∈ s.F) (hbnd : ghostOut s r k out bnd) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzantineRetG r k out bnd))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetG r k out bnd))))
  /-- A Byzantine coin call (D11). -/
  | byzantineCallW (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzantineCallW r k))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallW r k))))
  /-- A Byzantine coin return (D11). -/
  | byzantineRetW (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzantineRetW r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetW r k b))))
  /-- An external input is not the network's business. -/
  | callABAIdle (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.callABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callABA id b))))
  /-- A return requires the returning process to have multicast the payload —
  a condition on its sent (D12′). -/
  | retABA (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) (h : b ∈ s.decidedSent id) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- A corrupted process returns whatever it likes (D23): its program has been
  replaced, so the DECIDED evidence the honest row asks for is not required of
  it. The authorisation is this component's `id ∈ F`, and the process's half is
  the replaced program's self-loop. -/
  | retByzantine (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) (hF : id ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- The graded-agreement call multicasts: the network records the message. -/
  | callG (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.callG r id b))
        (PMF.pure ((s.recordGBCASend r id (callPayload id b)).writeGhost ghostStep
          (Sum.inl (.callG r id b))))
  /-- A graded-agreement return sends nothing, and announces the round's bound
  bit: the label's `bnd` stands in the ghost relation of the round at this
  state. This is the one row of the development that reads the ghost. -/
  | retG (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hbnd : ghostOut s r id out bnd) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retG r id out bnd))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out bnd))))
  /-- A coin call sends nothing. -/
  | callWIdle (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.callW r id))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callW r id))))
  /-- An unfused coin return sends nothing. -/
  | retWIdle (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retW r id c))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retW r id c))))
  /-- Corruption (deviation D1): total, Dirac, budget-guarded; no process
  record keeps a copy. -/
  | fail (s : NetworkState P.n M G) (k : Fin P.n) (hnew : k ∉ s.F)
      (hbud : s.F.card < P.f) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.fail k))
        (PMF.pure ((s.corrupt P k).writeGhost ghostStep (Sum.inl (.fail k))))
  /-- Byzantine stage injection (D5, D11): the network multicasts on behalf of
  a corrupted sender. -/
  | byzantineGBCA (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (m : M) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl .tau)
        (PMF.pure ((s.recordGBCASend r k m).writeGhost ghostStep (Sum.inl .tau)))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate. -/
  | byzantineDecided (s : NetworkState P.n M G) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl .tau)
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

/-- The state of a flat reading: the process family, the network adversary and
the coin oracle. -/
abbrev State (P : Parameters) (M S G : Type) : Type :=
  (∀ _ : Fin P.n, ProcessRecord P.n S) × (NetworkState P.n M G × (ℕ → WCC.SpecState P.n))

section NetworkAdversary

variable (P : Parameters) (M G : Type) [DecidableEq M] [Inhabited G]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop)

/-- The network adversary. -/
noncomputable def network : System (NetworkState P.n M G) (ExtendedLabel P.n M) where
  init := NetworkState.initial P.n M G
  step := NetworkStep P M G callPayload ghostStep ghostOut

@[simp] theorem network_init :
    (network P M G callPayload ghostStep ghostOut).init
      = NetworkState.initial P.n M G := rfl

@[simp] theorem network_step (s : NetworkState P.n M G) (l : ExtendedLabel P.n M)
    (μ : PMF (NetworkState P.n M G)) :
    (network P M G callPayload ghostStep ghostOut).step s l μ ↔
      NetworkStep P M G callPayload ghostStep ghostOut s l μ :=
  Iff.rfl

end NetworkAdversary

section Pipe

variable (P : Parameters) (M S G : Type) [DecidableEq M] [Inhabited G]
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop)
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop)

/-- The three components side by side, over the extended alphabet: the
synchronised process group, the network adversary and the lifted oracle. -/
noncomputable def systemExtended : System (State P M S G) (ExtendedLabel P.n M) :=
  (System.synchronisedProduct (program P M S roundStep)).parallel
    ((network P M G callPayload ghostStep ghostOut).parallel (coinOverExtendedAlphabet P M))

/-- The rendezvous alphabet hidden, the result read back over `Label n`. -/
noncomputable def systemHidden : System (State P M S G) (Label P.n) :=
  ((systemExtended P M S G roundStep callPayload ghostStep ghostOut).abstract
    (networkEventLabels P.n)).relabel

/-- **A flat reading**: the group with the sub-protocol API hidden. -/
noncomputable def system : System (State P M S G) (Label P.n) :=
  (systemHidden P M S G roundStep callPayload ghostStep ghostOut).abstract
    (Label.hiddenAPI P.n)

end Pipe

/-! ### What a reading must supply about its own rows -/

/-- What a flat reading's graded-agreement rows must satisfy for the inversion
lemmas below to read the rest of the table off a label: a row of process `j`
carries a label of `roundOwn j`, it fires only at a process whose program has
not been replaced (D23), it is Dirac, and its return takes the announced bit
free (D29). -/
class IsRoundRuleTable (P : Parameters) (M S : Type)
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M →
      PMF (ProcessRecord P.n S) → Prop) : Prop where
  /-- A stage-side row carries a stage-side label. -/
  own : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {L : ExtendedLabel P.n M}
    {μ : PMF (ProcessRecord P.n S)}, roundStep j q L μ → roundOwn j L
  /-- A stage-side row fires only at an unreplaced program. -/
  correct : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {L : ExtendedLabel P.n M}
    {μ : PMF (ProcessRecord P.n S)}, roundStep j q L μ → q.1.corrupted = false
  /-- A stage-side row is Dirac. -/
  dirac : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {L : ExtendedLabel P.n M}
    {μ : PMF (ProcessRecord P.n S)}, roundStep j q L μ → ∃ q', μ = PMF.pure q'
  /-- A program's return row takes the announced bit free (D29): the bit the
  label carries is the network's business, so a return row that fires at one
  bit fires at every other, with the same successor. -/
  boundBitFree : ∀ {j : Fin P.n} {q : ProcessRecord P.n S} {r : ℕ} {id : Fin P.n}
    {out : GBCAOutput} {b b' : Bool} {μ : PMF (ProcessRecord P.n S)},
    roundStep j q (Sum.inl (.retG r id out b)) μ →
      roundStep j q (Sum.inl (.retG r id out b')) μ

/-! ### Determinacy of the two rule tables

The composite is not an LTS — the coin resolution is probabilistic — but both
tables written here are Dirac, provided the reading's own rows are. -/

section Inversion

variable {P : Parameters} {M S : Type}
    {roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop}
    {j : Fin P.n} {q : ProcessRecord P.n S} {ν : PMF (ProcessRecord P.n S)}

/-- Every process transition is Dirac: the rows here are, and so are the
reading's own by `IsRoundRuleTable.dirac`. -/
theorem programStep_dirac [IsRoundRuleTable P M S roundStep]
    {l : ExtendedLabel P.n M} (h : ProgramStep P M S roundStep j q l ν) :
    ∃ q', ν = PMF.pure q' := by
  cases h
  case roundRow h' => exact IsRoundRuleTable.dirac h'
  all_goals exact ⟨_, rfl⟩

variable [IsRoundRuleTable P M S roundStep]

/-- The one `τ` row of a program's table is `terminate`: a silent step of a
program is that program's own termination, taken on a fired return and DECIDED
receipts from `2f + 1` distinct senders (D22). A replaced program has no silent
row at all, so the reading carries `corrupted = false` (D23), and no
graded-agreement row is silent, `roundOwn` holding of no `τ`. -/
theorem programStep_tau_terminate
    (h : ProgramStep P M S roundStep j q (Silent.τ : ExtendedLabel P.n M) ν) :
    ∃ b : Bool, q.1.corrupted = false ∧ q.1.process.returned = true ∧
      2 * P.f + 1 ≤ q.1.decidedCount b ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, { q.2 with terminated := true }) := by
  rw [extendedLabel_tau] at h
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case terminate b hh hret hcnt hterm => exact ⟨b, hh, hret, hcnt, hterm, rfl⟩
  case corruptedIdle hh hτ hown => exact absurd rfl hτ

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as
its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any record. A participant's row carries the health
guard `corrupted = false`, and on a label outside `actsAt j` the replaced
program's self-loop is a second reading of the same label (D23). -/

theorem programStep_callABA_own {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.process.input = none ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with
        input := some b, estimate := some b, round := 0, phase := .toCallG }, q.2)) ∨
    ((q.1.corrupted = true ∨ q.1.process.input ≠ none) ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem programStep_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retABA_own {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.process.input ≠ none ∧
      P.n - P.f ≤ q.1.decidedCount b ∧ q.1.process.returned = false ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with returned := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case ret =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem programStep_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callG r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retG_foreign {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retG r id out bnd)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem programStep_callW_own {r : ℕ}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callW r j)) ν) :
    (q.1.corrupted = false ∧ q.1.process.phase = .toCallW ∧ q.1.process.round = r ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with phase := .awaitW }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callW r id)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retW_own {r : ℕ} {co : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retW r j co)) ν) :
    (q.1.corrupted = false ∧ q.1.process.phase = .awaitW ∧ q.1.process.round = r ∧
      (∀ v : Bool, q.1.process.lastGrade ≠ some (.A v)) ∧
      ν = PMF.pure (q.1.stepRound co, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retW r id co)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
replaced, and a replaced program stands still. -/
theorem programStep_fail_own
    (h : ProgramStep P M S roundStep j q (Sum.inl (.fail j)) ν) :
    (q.1.corrupted = false ∧
      ν = PMF.pure ({ q.1 with corrupted := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_fail_foreign {k : Fin P.n} (hk : k ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.fail k)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

/-! ### One program's rules on the rendezvous alphabet

The Byzantine stage rows have no row at the process they name (D22, D23), so
on `byzantineCallG`, `byzantineCallGLoop` and `byzantineRetG` every process idles and there is no
participant's row to read. -/

theorem programStep_gbcaSend_foreign {r : ℕ} {k : Fin P.n} {m : M} (hk : k ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.gbcaSend r k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hk
  case gbcaSendIdle => rfl
  case corruptedIdle => rfl

theorem programStep_gbcaDeliver_foreign {r : ℕ} {i k : Fin P.n} {m : M} (hi : i ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.gbcaDeliver r i k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hi
  case gbcaDeliverIdle => rfl
  case corruptedIdle => rfl

theorem programStep_decidedSend_self {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedSend j b)) ν) :
    (q.1.corrupted = false ∧ q.1.process.input ≠ none ∧
      P.f + 1 ≤ q.1.decidedCount b ∧ ν = PMF.pure q) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedSendRelay =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case decidedSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_decidedSend_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedSend k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedSendRelay => exact absurd rfl hk
  case decidedSendIdle => rfl
  case corruptedIdle => rfl

theorem programStep_decidedDeliver_self {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedDeliver j k b)) ν) :
    q.1.corrupted = false ∧ b ∉ q.1.decidedDelivered k ∧
      ν = PMF.pure (q.1.receiveDecided k b, q.2) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedDeliverReceive => exact ⟨by assumption, by assumption, rfl⟩
  case decidedDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_decidedDeliver_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedDeliver i k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedDeliverReceive => exact absurd rfl hi
  case decidedDeliverIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retWPublish_self {r : ℕ} {co b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.retWPublish r j co b)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .awaitW ∧ q.1.process.round = r ∧
      q.1.process.lastGrade = some (.A b) ∧
      ν = PMF.pure (q.1.stepRound co, q.2) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retWPublish =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWPublishIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retWPublish_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.retWPublish r id co b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retWPublish => exact absurd rfl hid
  case retWPublishIdle => rfl
  case corruptedIdle => rfl

theorem programStep_gbcaCallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.gbcaCallLoop r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hid
  case gbcaCallLoopIdle => rfl
  case corruptedIdle => rfl

theorem programStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineCallGLoop r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  all_goals rfl

theorem programStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineCallW r k)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  all_goals rfl

theorem programStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineRetW r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  all_goals rfl

/-- The Byzantine graded-agreement call has no row at the process it names
(D11, D22, D23): the row carries its effect outside the program, and the
replaced program has no row on a label it acts on. -/
theorem programStep_byzantineCallG_noStep {r : ℕ} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineCallG r j b)) ν) : False := by
  cases h with
  | roundRow _ _ _ h' => exact (IsRoundRuleTable.own h').elim
  | byzantineCallGIdle _ _ _ _ _ hk => exact hk rfl
  | corruptedIdle _ _ _ _ _ hown => exact hown rfl

/-- The Byzantine graded-agreement return has no row at the process it names
(D11, D22, D23). -/
theorem programStep_byzantineRetG_noStep {r : ℕ} {out : GBCAOutput} {bnd : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineRetG r j out bnd)) ν) :
    False := by
  cases h with
  | roundRow _ _ _ h' => exact (IsRoundRuleTable.own h').elim
  | byzantineRetGIdle _ _ _ _ _ _ hk => exact hk rfl
  | corruptedIdle _ _ _ _ _ hown => exact hown rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a
process whose flag is up leaves both halves of its record where they stand.
Every row that writes carries the health guard, the reading's own rows by
`IsRoundRuleTable.correct`, so no row of a replaced program survives except a
self-loop. -/
theorem programStep_noStep {L : ExtendedLabel P.n M} (hc : q.1.corrupted = true)
    (h : ProgramStep P M S roundStep j q L ν) : ν = PMF.pure q := by
  cases h
  case roundRow h' => rw [IsRoundRuleTable.correct h'] at hc; exact absurd hc (by simp)
  all_goals simp_all

end Inversion

/-! ### The network adversary's rules, by label class -/

section NetInversion

variable {P : Parameters} {M G : Type} [DecidableEq M]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G}
    {ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop}
    {s : NetworkState P.n M G} {μ : PMF (NetworkState P.n M G)}

/-- Every network transition is Dirac. -/
theorem networkStep_dirac {l : ExtendedLabel P.n M}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s l μ) :
    ∃ s', μ = PMF.pure s' := by
  cases h <;> exact ⟨_, rfl⟩

theorem networkStep_gbcaSend {r : ℕ} {j : Fin P.n} {m : M}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.gbcaSend r j m)) μ) :
    μ = PMF.pure ((s.recordGBCASend r j m).writeGhost ghostStep (Sum.inr (.gbcaSend r j m))) := by
  cases h; rfl

theorem networkStep_gbcaDeliver {r : ℕ} {i j : Fin P.n} {m : M}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.gbcaDeliver r i j m)) μ) :
    m ∈ s.sent r j ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaDeliver r i j m))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_decidedSend {j : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.decidedSend j b)) μ) :
    b ∉ s.decidedSent j ∧ μ = PMF.pure (s.recordDecided j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_decidedDeliver {i j : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.decidedDeliver i j b)) μ) :
    b ∈ s.decidedSent j ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_retWPublish {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.retWPublish r id c b)) μ) :
    μ = PMF.pure ((s.recordDecided id b).writeGhost ghostStep
      (Sum.inr (.retWPublish r id c b))) := by
  cases h; rfl

theorem networkStep_gbcaCallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.gbcaCallLoop r id b)) μ) :
    μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaCallLoop r id b))) := by
  cases h; rfl

theorem networkStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzantineCallGLoop r k b)) μ) :
    k ∈ s.F ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallGLoop r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzantineCallW r k)) μ) :
    k ∈ s.F ∧ μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallW r k))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzantineRetW r k b)) μ) :
    k ∈ s.F ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetW r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzantineCallG r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure ((s.recordGBCASend r k (callPayload k b)).writeGhost ghostStep
      (Sum.inr (.byzantineCallG r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

/-- A Byzantine graded-agreement return is authorised by the corrupted set, and
the bound bit on its label stands in the round's ghost relation (D11). -/
theorem networkStep_byzantineRetG {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzantineRetG r k out bnd)) μ) :
    k ∈ s.F ∧ ghostOut s r k out bnd ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetG r k out bnd))) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem networkStep_callABA {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.callABA id b)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

/-- A return is authorised either by the DECIDED sent of the returning process
or by its corruption (D23); the two rows share the label and the identity
successor. -/
theorem networkStep_retABA {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.retABA id b)) μ) :
    (b ∈ s.decidedSent id ∨ id ∈ s.F) ∧ μ = PMF.pure s := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByzantine => exact ⟨Or.inr (by assumption), rfl⟩

theorem networkStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.callG r id b)) μ) :
    μ = PMF.pure ((s.recordGBCASend r id (callPayload id b)).writeGhost ghostStep
      (Sum.inl (.callG r id b))) := by
  cases h; rfl

/-- A graded-agreement return announces the round's ghost output: the bound bit
on the label stands in `ghostOut` at the state the row starts from. -/
theorem networkStep_retG {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.retG r id out bnd)) μ) :
    ghostOut s r id out bnd ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out bnd))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_callW {r : ℕ} {id : Fin P.n}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.callW r id)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem networkStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.retW r id c)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem networkStep_fail {k : Fin P.n}
    (h : NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl (.fail k)) μ) :
    k ∉ s.F ∧ s.F.card < P.f ∧ μ = PMF.pure (s.corrupt P k) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem networkStep_tau
    (h : NetworkStep P M G callPayload ghostStep ghostOut s (Sum.inl .tau) μ) :
    (∃ (r : ℕ) (k : Fin P.n) (m : M), k ∈ s.F ∧ μ = PMF.pure (s.recordGBCASend r k m)) ∨
    (∃ (k : Fin P.n) (b : Bool), k ∈ s.F ∧ μ = PMF.pure (s.recordDecided k b)) := by
  cases h
  case byzantineGBCA => exact Or.inl ⟨_, _, _, by assumption, rfl⟩
  case byzantineDecided => exact Or.inr ⟨_, _, by assumption, rfl⟩

end NetInversion

/-! ### The network's own field algebra

Each of the network adversary's three writes on the message record — a stage
multicast, a DECIDED multicast, and corruption — touches one field of the
state and leaves the others alone, the ghost among them. The ghost write
touches the ghost and nothing else. -/

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

/-! ### Reading composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct`; the
lemmas below unfold it once and for all. -/

section Composite

variable {P : Parameters} {M S : Type}
    {roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop}
    [IsRoundRuleTable P M S roundStep]

/-- A synchronised transition of the process group on a visible label: every
process steps, and the joint distribution is Dirac. -/
theorem programProduct_inv {u : ∀ _ : Fin P.n, ProcessRecord P.n S} {l : ExtendedLabel P.n M}
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n S)} (hl : l ≠ Silent.τ)
    (h : (System.synchronisedProduct (program P M S roundStep)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, ProcessRecord P.n S,
      μ = PMF.pure x ∧ ∀ i, ProgramStep P M S roundStep i (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => programStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd rfl hl

/-- A silent transition of the process group: `τ` is interleaved, so exactly
one program moves and the rest hold their state. -/
theorem programProduct_tau_inv {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n S)}
    (h : (System.synchronisedProduct (program P M S roundStep)).step u
      (Silent.τ : ExtendedLabel P.n M) μ) :
    ∃ (i : Fin P.n) (y : ProcessRecord P.n S),
      ProgramStep P M S roundStep i (u i) (Silent.τ : ExtendedLabel P.n M) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y) := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, rfl⟩
  · exact absurd rfl hτ
  · obtain ⟨y, rfl⟩ := programStep_dirac hstep
    exact ⟨i, y, hstep, by rw [piPMF_update_pure, PMF.pure_map]⟩

section WithNet

variable {G : Type} [DecidableEq M] [Inhabited G]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G}
    {ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop}

omit [IsRoundRuleTable P M S roundStep] in
/-- The composite step relation of the group, unfolded to the hidden
rendezvous case and the shared-label case. -/
theorem systemHidden_step_iff (q : State P M S G) (l : Label P.n)
    (μ : PMF (State P M S G)) :
    (systemHidden P M S G roundStep callPayload ghostStep ghostOut).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n M,
        (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step q (Sum.inr e) μ) ∨
      (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

omit [IsRoundRuleTable P M S roundStep] in
/-- The flat reading's step relation: a sub-protocol API label seen as `τ`, or
a label that survives the hiding. -/
theorem system_step_iff (q : State P M S G) (l : Label P.n)
    (μ : PMF (State P M S G)) :
    (system P M S G roundStep callPayload ghostStep ghostOut).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n,
        (systemHidden P M S G roundStep callPayload ghostStep ghostOut).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧
        (systemHidden P M S G roundStep callPayload ghostStep ghostOut).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem systemExtended_event_inv {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n} {e : NetworkEvent P.n M}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n S) (w' : NetworkState P.n M G)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ProgramStep P M S roundStep i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetworkStep P M G callPayload ghostStep ghostOut w (Sum.inr e) (PMF.pure w') ∧
      (coinOverExtendedAlphabet P M).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := programProduct_inv (by simp) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN, hO, rfl⟩
    · simp [extendedLabel_tau] at habs
    · simp [extendedLabel_tau] at habs
  · simp [extendedLabel_tau] at habs
  · simp [extendedLabel_tau] at habs

/-- A visible shared-label transition. -/
theorem systemExtended_label_inv {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n} {l : Label P.n}
    (hl : l ≠ Label.tau) {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n S) (w' : NetworkState P.n M G)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ProgramStep P M S roundStep i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetworkStep P M G callPayload ghostStep ghostOut w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ :=
      programProduct_inv (by rw [extendedLabel_tau]; exact fun hh => hl (Sum.inl_injective hh)) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN,
        (System.mapIdle_step_some (coinLabelMap_inl l) μ₃).mp hO, rfl⟩
    · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl
    · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [extendedLabel_tau] at habs; exact absurd (Sum.inl_injective habs) hl

/-- A silent shared-label transition: one process terminating, or the network's
own injection. The coin oracle has no silent row, so it contributes none. -/
theorem systemExtended_tau_inv {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inl Label.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcessRecord P.n S),
      ProgramStep P M S roundStep i (u i) (Sum.inl Label.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetworkStep P M G callPayload ghostStep ghostOut w (Sum.inl .tau)
        (PMF.pure w') ∧
      μ = PMF.pure (u, w', o)) := by
  rw [systemExtended, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hS, rfl⟩ | ⟨-, μ₂₃, hNW, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨i, y, hstep, rfl⟩ := programProduct_tau_inv hS
    exact Or.inl ⟨i, y, hstep, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hNW
    rcases hNW with ⟨habs, -⟩ | ⟨-, μ₂, hN, rfl⟩ | ⟨-, μ₃, hO, rfl⟩
    · exact absurd rfl habs
    · obtain ⟨w', rfl⟩ := networkStep_dirac hN
      exact Or.inr ⟨w', hN, by rw [prodPMF_pure_pure, prodPMF_pure_pure]⟩
    · exact (ABA.WCC.specFamily_tau_inv P
        ((System.mapIdle_step_some (coinLabelMap_inl Label.tau) μ₃).mp hO)).elim

/-! ### The bound bit on a return

The two graded-agreement returns are the only rows that read the ghost, and
what they read is the relation `ghostOut` at the network's state. A composite
transition on either therefore constrains the bound bit its label carries. -/

/-- A composite graded-agreement return announces a bit the network's ghost
relation admits. -/
theorem systemExtended_retG_bound {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n}
    {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inl (.retG r id out bnd)) μ) :
    ghostOut w r id out bnd := by
  have hne : (Label.retG r id out bnd : Label P.n) ≠ Label.tau := by
    simp
  obtain ⟨x, w', ω, -, hN, -, -⟩ := systemExtended_label_inv hne h
  exact (networkStep_retG hN).1

/-- A composite Byzantine graded-agreement return announces a bit the same
ghost relation admits (D11). -/
theorem systemExtended_byzantineRetG_bound {u : ∀ _ : Fin P.n, ProcessRecord P.n S}
    {w : NetworkState P.n M G} {o : ℕ → WCC.SpecState P.n}
    {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    {μ : PMF (State P M S G)}
    (h : (systemExtended P M S G roundStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inr (.byzantineRetG r k out bnd)) μ) :
    ghostOut w r k out bnd := by
  obtain ⟨x, w', μ₃, -, hN, -, -⟩ := systemExtended_event_inv h
  exact (networkStep_byzantineRetG hN).2.1

end WithNet

end Composite

end Implementation
end ABA
end PLTS
