/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Reading.Alphabet
import Leslie2Protocols.ABA.Vocabulary.RoundLoop
import Leslie2Protocols.Framework.SyncProduct
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
own rows, given as a relation `stageStep` embedded in one constructor of the
program table. A reading supplies the three and inherits the round loop, the
DECIDED sets, the coin handshake, corruption, the network adversary, the
composition pipeline and the inversion lemmas.

## The division of rows

A program's row is the implementation's business exactly when its label is one
of `stageOwn j`: the graded-agreement call and return at `j`, `j`'s own stage
multicast, a stage delivery addressed to `j`, and `j`'s own call against an
already-called stage record. Every other label — the ABA interface, the coin
handshake, the DECIDED relay and its delivery, the Byzantine handshake rows,
corruption, and the same five label classes at another process — is answered
by a row here. The side condition `stageOwn` is what the inversion lemmas
consume: a program's row on a label outside `stageOwn j` is one of the rows
below, whichever implementation is being read.

## The network adversary

The adversary's table is independent of the implementation except in two
places. The graded-agreement call and its Byzantine handshake row sent the
message the call multicasts, and which message that is belongs to the
implementation; it enters as the parameter `callPayload`. The other is the
ghost.

## The network's ghost

The adversary holds one further record: for each round `r`, a ghost record
`ghostRec r` of a type `G` the reading fixes. It belongs to the network and to
no program. No program's row reads it and no program's record holds it.

Two parameters carry it. `ghostStep` writes it. On every row, the record of
the round the label names is replaced by `ghostStep` of that label, the
network's state and the record standing there, and the records of the other
rounds are left where they stand; a label naming no round leaves the whole
ghost alone. `ghostOut` reads it out. It is a relation on the bit a return
announces: the network's state, the round, the process being answered, the
graded outcome and the bit. It guards the two graded-agreement return rows —
`retG`, and `byzRetG` at a replaced program — each of which fires only with
the bound bit its label carries standing in it. A reading that computes the
announced bit instantiates the relation as an equation against it. A reading
that leaves the announcement to the adversary instantiates it as the full
relation, and the bit is unconstrained.

The content is the reading's own. ABDY22's reading and the gather-based one
hold different records and write them at different rows, so `G`, `ghostStep`
and `ghostOut` are parameters here, as `M`, `S`, `stageStep` and `callPayload`
are. Each of the two writes the record at the first return of a round, from
the sent sets and the corrupted set, and reads the same record back at every
later return of that round. Each instantiates `ghostOut` as the equation
between the announced bit and that record.
-/

namespace PLTS
namespace ABA
namespace Net

/-! ### The state of one process -/

/-- The stage-side record of one process: the stage record of every round the
process has touched, and whether it has terminated (D22). -/
structure StageSideRecP (S : Type) : Type where
  /-- The finite map of stage records; a round off the map has the initial
  record. -/
  stages : Finmap (fun _ : ℕ => S)
  /-- Whether this process has terminated (ABDY22 §3, Termination).
  `terminated` is not `returned`: the round-loop record's `returned` says the
  process has fired `retABA`; `terminated` says it has stopped participating. -/
  terminated : Bool

namespace StageSideRecP

variable {n : ℕ} {M S : Type}

/-- The initial stage-side record: no round touched, not terminated. -/
def initial (S : Type) : StageSideRecP S where
  stages := ∅
  terminated := false

/-- Retain `p` as the stage record of round `r`. -/
def setStage (q : StageSideRecP S) (r : ℕ) (p : S) : StageSideRecP S :=
  { q with stages := q.stages.insert r p }

end StageSideRecP

/-- What a flat reading's stage record supplies: the record of a round the
process has not touched, and the filing of a delivered message under its
sender's recv row. -/
class StageRecord (n : outParam ℕ) (M : outParam Type) (S : Type) where
  /-- The stage record of a round the process has not touched. -/
  initial : S
  /-- File a message under its sender's recv row. -/
  deliverTo : S → Fin n → M → S

namespace StageSideRecP

variable {n : ℕ} {M S : Type} [StageRecord n M S]

/-- The stage record of round `r`: the retained record if the process has
touched round `r`, the initial record otherwise. -/
def stage (q : StageSideRecP S) (r : ℕ) : S :=
  (q.stages.lookup r).getD StageRecord.initial

/-- File `m` under the recv row of sender `k` in the stage record of round
`r`. -/
def deliverTo (q : StageSideRecP S) (r : ℕ) (k : Fin n) (m : M) : StageSideRecP S :=
  q.setStage r (StageRecord.deliverTo (q.stage r) k m)

@[simp] theorem initial_stage (r : ℕ) :
    (initial S).stage r = (StageRecord.initial : S) := by
  simp [stage, initial]

@[simp] theorem initial_terminated (S : Type) : (initial S).terminated = false := rfl

@[simp] theorem stage_setStage_self (q : StageSideRecP S) (r : ℕ) (p : S) :
    (q.setStage r p).stage r = p := by
  simp [stage, setStage, Finmap.lookup_insert]

@[simp] theorem stage_setStage_ne (q : StageSideRecP S) (r : ℕ) (p : S)
    {r' : ℕ} (h : r' ≠ r) : (q.setStage r p).stage r' = q.stage r' := by
  simp [stage, setStage, Finmap.lookup_insert_of_ne _ h]

@[simp] theorem terminated_setStage (q : StageSideRecP S) (r : ℕ) (p : S) :
    (q.setStage r p).terminated = q.terminated := rfl

@[simp] theorem terminated_deliverTo (q : StageSideRecP S) (r : ℕ) (k : Fin n)
    (m : M) : (q.deliverTo r k m).terminated = q.terminated := rfl

end StageSideRecP

/-- The state of one process: its round-loop record and its stage-side record
(D22). -/
abbrev ProcRecP (n : ℕ) (S : Type) : Type := CoreRec n × StageSideRecP S

/-! ### The round a label names -/

/-- The round a label of the extended alphabet names, if any. A shared label
names a round when it is a graded-agreement handshake, which is
`Lab.gbcaRound`; a rendezvous label names the round its constructor carries.
The ABA interface, corruption, the DECIDED relay and the DECIDED delivery name
no round. This is the round whose ghost record a row writes. -/
def roundOf {n : ℕ} {M : Type} : NLabP n M → Option ℕ
  | Sum.inl l => l.gbcaRound
  | Sum.inr (.gsnd r _ _) => some r
  | Sum.inr (.gdlv r _ _ _) => some r
  | Sum.inr (.dsnd _ _) => none
  | Sum.inr (.ddlv _ _ _) => none
  | Sum.inr (.retWPub r _ _ _) => some r
  | Sum.inr (.gcallLoop r _ _) => some r
  | Sum.inr (.byzCallG r _ _) => some r
  | Sum.inr (.byzCallGLoop r _ _) => some r
  | Sum.inr (.byzRetG r _ _ _) => some r
  | Sum.inr (.byzCallW r _) => some r
  | Sum.inr (.byzRetW r _ _) => some r

/-! ### The network adversary's state -/

/-- The state of the network adversary: the round-tagged message sets, the
DECIDED sets, the corrupted set with its budget, and the ghost record of every
round. -/
structure NetStateP (n : ℕ) (M : Type) (G : Type) : Type where
  /-- `sent r j` — the stage-`r` messages process `j` has multicast (D5). -/
  sent : ℕ → Fin n → Finset M
  /-- `dsent j` — the DECIDED payloads process `j` has multicast (D12′). -/
  dsent : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- `ghostRec r` — the ghost record the network holds for round `r`. No
  program reads it. -/
  ghostRec : ℕ → G

namespace NetStateP

variable {n : ℕ} {M G : Type} [DecidableEq M]

/-- The initial network: nothing multicast, nobody corrupted, every round's
ghost record the default one. -/
def initial (n : ℕ) (M G : Type) [Inhabited G] : NetStateP n M G where
  sent := fun _ _ => ∅
  dsent := fun _ => ∅
  F := ∅
  ghostRec := fun _ => default

/-- Sent `m` under sender `j` in stage `r` (D5). -/
def gsent (s : NetStateP n M G) (r : ℕ) (j : Fin n) (m : M) : NetStateP n M G :=
  { s with
    sent :=
      Function.update s.sent r (Function.update (s.sent r) j (insert m (s.sent r j))) }

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def dput (s : NetStateP n M G) (j : Fin n) (b : Bool) : NetStateP n M G :=
  { s with dsent := Function.update s.dsent j (insert b (s.dsent j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Params) (id : Fin P.n) (s : NetStateP P.n M G) : NetStateP P.n M G :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

/-- The ghost write of a row: `ghostStep` applied to the record of the round
`L` names, the records of the other rounds left where they stand. A label
naming no round leaves the whole ghost alone. -/
def writeGhost (s : NetStateP n M G)
    (ghostStep : NLabP n M → NetStateP n M G → G → G) (L : NLabP n M) :
    NetStateP n M G :=
  match roundOf L with
  | some r =>
      { s with ghostRec := Function.update s.ghostRec r (ghostStep L s (s.ghostRec r)) }
  | none => s

/-- The same network state over the trivial ghost: the message record, the
DECIDED sets and the corrupted set stand, and every round's record is `()`. -/
def forgetGhost (s : NetStateP n M G) : NetStateP n M Unit where
  sent := s.sent
  dsent := s.dsent
  F := s.F
  ghostRec := fun _ => ()

end NetStateP

/-! ### The labels a stage-side row carries -/

/-- The labels on which a program's row belongs to the graded-agreement
implementation: process `j`'s own call and return at the interface, its own
stage multicast, a stage delivery addressed to it, and its own call against an
already-called stage record. Every other label is answered by a row of
`FlatProcStep`. -/
def stageOwn {n : ℕ} {M : Type} (j : Fin n) : NLabP n M → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _ _) => id = j
  | Sum.inr (.gsnd _ k _) => k = j
  | Sum.inr (.gdlv _ i _ _) => i = j
  | Sum.inr (.gcallLoop _ id _) => id = j
  | _ => False

/-- A stage-side label is one the process acts on: the replaced program has no
row on either (D23). -/
theorem actsAt_of_stageOwn {n : ℕ} {M : Type} {j : Fin n} {L : NLabP n M}
    (h : stageOwn j L) : actsAt j L := by
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
`stageOwn j` has a row here: the participant's, or an idle one.

A corruption replaces the program of the process it names (D23). Every
participant's row carries the health guard `c.corrupted = false`, so the record
freezes at the corruption; `failSelf` is the row that writes the flag, and
`corruptedIdle` is the replaced program. That self-loop is taken on every label
other than `τ` and the labels of `actsAt j`, on which the replaced program has
no row at all. -/

/-- The step relation of the program of process `j`, over a graded-agreement
implementation given by its message type, its stage record and its rows. -/
inductive FlatProcStep (P : Params) (M S : Type)
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M →
      PMF (ProcRecP P.n S) → Prop) (j : Fin P.n) :
    ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop
  /-- A row of the graded-agreement implementation. -/
  | stageRow (q : ProcRecP P.n S) (L : NLabP P.n M) (μ : PMF (ProcRecP P.n S))
      (h : stageStep j q L μ) : FlatProcStep P M S stageStep j q L μ
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : CoreRec P.n) (p : StageSideRecP S) (b : Bool)
      (hh : c.corrupted = false) (h : c.proc.input = none) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }, p))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreRec P.n) (p : StageSideRecP S) (b : Bool)
      (hh : c.corrupted = false) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.callABA j b)) (PMF.pure (c, p))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.callABA id b)) (PMF.pure (c, p))
  /-- Return `b` on an `n − f` DECIDED quorum, the round-loop record having
  received its input (D8). Having multicast `b` oneself is a condition on the
  sent, hence the network's conjunct. -/
  | ret (c : CoreRec P.n) (p : StageSideRecP S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.proc.input ≠ none)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.proc.returned = false) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }, p))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.retABA id b)) (PMF.pure (c, p))
  /-- The process terminates (ABDY22 Definitions 3.1/3.2 and the p.7 note on
  termination): its own return is fired and DECIDED receipts from `2f + 1`
  distinct senders are on record, so every process still running will cross the
  relay threshold without further response from this one. -/
  | terminate (c : CoreRec P.n) (p : StageSideRecP S) (b : Bool)
      (hh : c.corrupted = false) (hret : c.proc.returned = true)
      (hcnt : 2 * P.f + 1 ≤ c.decidedCount b)
      (hterm : p.terminated = false) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl Lab.tau)
        (PMF.pure (c, { p with terminated := true }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.callG r id b)) (PMF.pure (c, p))
  /-- A graded-agreement return to another process: not `j`'s business. The
  bound bit the label announces is the network's ghost output, and no program
  reads it, so this row leaves it free. -/
  | retGIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (id : Fin P.n) (out : GbcaOut) (bnd : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.retG r id out bnd))
        (PMF.pure (c, p))
  /-- `c ← WCC_r()`, the call half at the round loop. -/
  | callW (c : CoreRec P.n) (p : StageSideRecP S) (r : ℕ)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }, p))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.callW r id)) (PMF.pure (c, p))
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being an `A` (D10). The advance opens a new
  round; the stage records the process holds are retained across it (D22). -/
  | retW (c : CoreRec P.n) (p : StageSideRecP S) (r : ℕ) (co : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : ∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.retW r j co))
        (PMF.pure (c.stepRound co, p))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.retW r id co)) (PMF.pure (c, p))
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the row (D23). -/
  | failSelf (c : CoreRec P.n) (p : StageSideRecP S) (hh : c.corrupted = false) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.fail j))
        (PMF.pure ({ c with corrupted := true }, p))
  /-- Another process's corruption is not this process's business. -/
  | failIdle (c : CoreRec P.n) (p : StageSideRecP S) (k : Fin P.n) (hk : k ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inl (.fail k)) (PMF.pure (c, p))
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `actsAt j`, on which the process has no row at all. -/
  | corruptedIdle (c : CoreRec P.n) (p : StageSideRecP S) (L : NLabP P.n M)
      (hh : c.corrupted = true) (hτ : L ≠ Sum.inl Lab.tau) (hown : ¬ actsAt j L) :
      FlatProcStep P M S stageStep j (c, p) L (PMF.pure (c, p))
  /-- A stage multicast by another process: not `j`'s business. -/
  | gsndIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (k : Fin P.n) (m : M) (hk : k ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.gsnd r k m)) (PMF.pure (c, p))
  /-- A stage delivery to another process: not `j`'s business. -/
  | gdlvIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (i k : Fin P.n) (m : M) (hi : i ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.gdlv r i k m)) (PMF.pure (c, p))
  /-- The DECIDED relay on an `f + 1` quorum, the round-loop record having
  received its input (D8, D12′). Not having multicast `b` is a condition on the
  sent, hence the network's conjunct; the sent insert is the network's half
  too. -/
  | dsndRelay (c : CoreRec P.n) (p : StageSideRecP S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.proc.input ≠ none)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.dsnd j b)) (PMF.pure (c, p))
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | dsndIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.dsnd k b)) (PMF.pure (c, p))
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is the network's conjunct. -/
  | ddlvRecv (c : CoreRec P.n) (p : StageSideRecP S)
      (k : Fin P.n) (b : Bool) (hh : c.corrupted = false) (hr : b ∉ c.decIn k) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.ddlv j k b))
        (PMF.pure (c.recvDec k b, p))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | ddlvIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.ddlv i k b)) (PMF.pure (c, p))
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's grade was `A b`, so the round advance publishes `b`, the sent insert
  being the network's half. The advance opens a new round; the stage records
  the process holds are retained across it (D22). -/
  | retWPub (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (co : Bool) (b : Bool) (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : c.proc.lastGrade = some (.A b)) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.retWPub r j co b))
        (PMF.pure (c.stepRound co, p))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPubIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.retWPub r id co b))
        (PMF.pure (c, p))
  /-- Such a call at another process: not `j`'s business. -/
  | gcallLoopIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.gcallLoop r id b))
        (PMF.pure (c, p))
  /-- A Byzantine graded-agreement call at another process: not `j`'s
  business. The process the label names has no row either (D11, D22). -/
  | byzCallGIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.byzCallG r k b))
        (PMF.pure (c, p))
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11): nothing moves anywhere. -/
  | byzCallGLoopIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.byzCallGLoop r k b))
        (PMF.pure (c, p))
  /-- A Byzantine graded-agreement return at another process: not `j`'s
  business. The process the label names has no row either (D11, D22). -/
  | byzRetGIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (k : Fin P.n) (out : GbcaOut) (bnd : Bool) (hk : k ≠ j) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.byzRetG r k out bnd))
        (PMF.pure (c, p))
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback,
  no process moves. -/
  | byzCallWIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (k : Fin P.n) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.byzCallW r k)) (PMF.pure (c, p))
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback, no process moves. -/
  | byzRetWIdle (c : CoreRec P.n) (p : StageSideRecP S)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      FlatProcStep P M S stageStep j (c, p) (Sum.inr (.byzRetW r k b)) (PMF.pure (c, p))

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
inductive FlatNetStep (P : Params) (M G : Type) [DecidableEq M]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : NLabP P.n M → NetStateP P.n M G → G → G)
    (ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop) :
    NetStateP P.n M G → NLabP P.n M → PMF (NetStateP P.n M G) → Prop
  /-- The network's half of a stage multicast: sent the message under its
  sender. Authenticity is the sender's joint participation (D5). -/
  | gsnd (s : NetStateP P.n M G) (r : ℕ) (j : Fin P.n) (m : M) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.gsnd r j m))
        (PMF.pure ((s.gsent r j m).writeGhost ghostStep (Sum.inr (.gsnd r j m))))
  /-- The network's half of a stage delivery: the message must be sent under
  the named sender. Delivery does not consume it (D5). -/
  | gdlv (s : NetStateP P.n M G) (r : ℕ) (i j : Fin P.n) (m : M)
      (h : m ∈ s.sent r j) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.gdlv r i j m))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gdlv r i j m))))
  /-- The network's half of a DECIDED relay: the payload must not be sent
  yet (D12′). -/
  | dsnd (s : NetStateP P.n M G) (j : Fin P.n) (b : Bool) (h : b ∉ s.dsent j) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.dsnd j b))
        (PMF.pure ((s.dput j b).writeGhost ghostStep (Sum.inr (.dsnd j b))))
  /-- The network's half of a DECIDED delivery: the payload must be sent
  under the named sender (D12′). -/
  | ddlv (s : NetStateP P.n M G) (i j : Fin P.n) (b : Bool) (h : b ∈ s.dsent j) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.ddlv i j b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.ddlv i j b))))
  /-- The network's half of the fused coin return: sent the published payload
  (D10, D12′). -/
  | retWPub (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.retWPub r id c b))
        (PMF.pure ((s.dput id b).writeGhost ghostStep (Sum.inr (.retWPub r id c b))))
  /-- A graded-agreement call against an already-called stage record sends
  nothing. -/
  | gcallLoop (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.gcallLoop r id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gcallLoop r id b))))
  /-- A Byzantine graded-agreement call (D11): authorised here, and the
  message its call multicasts sent here. -/
  | byzCallG (s : NetStateP P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzCallG r k b))
        (PMF.pure ((s.gsent r k (callPayload k b)).writeGhost ghostStep
          (Sum.inr (.byzCallG r k b))))
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11). -/
  | byzCallGLoop (s : NetStateP P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzCallGLoop r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzCallGLoop r k b))))
  /-- A Byzantine graded-agreement return (D11). The bound bit stands in the
  ghost relation of the round, as at a return to an unreplaced program: a
  replaced program is answered, and the announcement is the network's. -/
  | byzRetG (s : NetStateP P.n M G) (r : ℕ) (k : Fin P.n) (out : GbcaOut) (bnd : Bool)
      (hF : k ∈ s.F) (hbnd : ghostOut s r k out bnd) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzRetG r k out bnd))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzRetG r k out bnd))))
  /-- A Byzantine coin call (D11). -/
  | byzCallW (s : NetStateP P.n M G) (r : ℕ) (k : Fin P.n) (hF : k ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzCallW r k))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzCallW r k))))
  /-- A Byzantine coin return (D11). -/
  | byzRetW (s : NetStateP P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inr (.byzRetW r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzRetW r k b))))
  /-- An external input is not the network's business. -/
  | callABAIdle (s : NetStateP P.n M G) (id : Fin P.n) (b : Bool) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.callABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callABA id b))))
  /-- A return requires the returning process to have multicast the payload —
  a condition on its sent (D12′). -/
  | retABA (s : NetStateP P.n M G) (id : Fin P.n) (b : Bool) (h : b ∈ s.dsent id) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- A corrupted process returns whatever it likes (D23): its program has been
  replaced, so the DECIDED evidence the honest row asks for is not required of
  it. The authorisation is this component's `id ∈ F`, and the process's half is
  the replaced program's self-loop. -/
  | retByz (s : NetStateP P.n M G) (id : Fin P.n) (b : Bool) (hF : id ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- The graded-agreement call multicasts: the network records the message. -/
  | callG (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.callG r id b))
        (PMF.pure ((s.gsent r id (callPayload id b)).writeGhost ghostStep
          (Sum.inl (.callG r id b))))
  /-- A graded-agreement return sends nothing, and announces the round's bound
  bit: the label's `bnd` stands in the ghost relation of the round at this
  state. This is the one row of the development that reads the ghost. -/
  | retG (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (out : GbcaOut) (bnd : Bool)
      (hbnd : ghostOut s r id out bnd) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retG r id out bnd))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out bnd))))
  /-- A coin call sends nothing. -/
  | callWIdle (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.callW r id))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callW r id))))
  /-- An unfused coin return sends nothing. -/
  | retWIdle (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.retW r id c))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retW r id c))))
  /-- Corruption (deviation D1): total, Dirac, budget-guarded; no process
  record keeps a copy. -/
  | fail (s : NetStateP P.n M G) (k : Fin P.n) (hnew : k ∉ s.F)
      (hbud : s.F.card < P.f) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.fail k))
        (PMF.pure ((s.corrupt P k).writeGhost ghostStep (Sum.inl (.fail k))))
  /-- Byzantine stage injection (D5, D11): the network multicasts on behalf of
  a corrupted sender. -/
  | byzG (s : NetStateP P.n M G) (r : ℕ) (k : Fin P.n) (m : M) (hF : k ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl .tau)
        (PMF.pure ((s.gsent r k m).writeGhost ghostStep (Sum.inl .tau)))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate. -/
  | byzD (s : NetStateP P.n M G) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl .tau)
        (PMF.pure ((s.dput k b).writeGhost ghostStep (Sum.inl .tau)))

/-! ### The automata and the composition pipeline -/

section Programs

variable (P : Params) (M S : Type)
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop)

/-- The program of process `j`. -/
noncomputable def flatProcN (j : Fin P.n) : System (ProcRecP P.n S) (NLabP P.n M) where
  init := (CoreRec.initial P.n, StageSideRecP.initial S)
  step := FlatProcStep P M S stageStep j

@[simp] theorem flatProcN_init (j : Fin P.n) :
    (flatProcN P M S stageStep j).init
      = (CoreRec.initial P.n, StageSideRecP.initial S) := rfl

@[simp] theorem flatProcN_step (j : Fin P.n) (q : ProcRecP P.n S)
    (l : NLabP P.n M) (μ : PMF (ProcRecP P.n S)) :
    (flatProcN P M S stageStep j).step q l μ ↔ FlatProcStep P M S stageStep j q l μ :=
  Iff.rfl

end Programs

/-- The state of a flat reading: the process family, the network adversary and
the coin oracle. -/
abbrev FlatState (P : Params) (M S G : Type) : Type :=
  (∀ _ : Fin P.n, ProcRecP P.n S) × (NetStateP P.n M G × (ℕ → WCC.SpecState P.n))

section Network

variable (P : Params) (M G : Type) [DecidableEq M] [Inhabited G]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : NLabP P.n M → NetStateP P.n M G → G → G)
    (ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop)

/-- The network adversary. -/
noncomputable def flatNetAdv : System (NetStateP P.n M G) (NLabP P.n M) where
  init := NetStateP.initial P.n M G
  step := FlatNetStep P M G callPayload ghostStep ghostOut

@[simp] theorem flatNetAdv_init :
    (flatNetAdv P M G callPayload ghostStep ghostOut).init
      = NetStateP.initial P.n M G := rfl

@[simp] theorem flatNetAdv_step (s : NetStateP P.n M G) (l : NLabP P.n M)
    (μ : PMF (NetStateP P.n M G)) :
    (flatNetAdv P M G callPayload ghostStep ghostOut).step s l μ ↔
      FlatNetStep P M G callPayload ghostStep ghostOut s l μ :=
  Iff.rfl

end Network

section Pipe

variable (P : Params) (M S G : Type) [DecidableEq M] [Inhabited G]
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop)
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : NLabP P.n M → NetStateP P.n M G → G → G)
    (ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop)

/-- The three components side by side, over the extended alphabet: the
synchronised process group, the network adversary and the lifted oracle. -/
noncomputable def flatPre : System (FlatState P M S G) (NLabP P.n M) :=
  (System.syncProduct (flatProcN P M S stageStep)).parallel
    ((flatNetAdv P M G callPayload ghostStep ghostOut).parallel (wccLiftP P M))

/-- The rendezvous alphabet hidden, the result read back over `Lab n`. -/
noncomputable def flatGroup : System (FlatState P M S G) (Lab P.n) :=
  ((flatPre P M S G stageStep callPayload ghostStep ghostOut).abstract
    (netEvtLabels P.n)).relabel

/-- **A flat reading**: the group with the sub-protocol API hidden. -/
noncomputable def flat : System (FlatState P M S G) (Lab P.n) :=
  (flatGroup P M S G stageStep callPayload ghostStep ghostOut).abstract
    (Lab.hiddenAPI P.n)

end Pipe

/-! ### What a reading must supply about its own rows -/

/-- What a flat reading's graded-agreement rows must satisfy for the inversion
lemmas below to read the rest of the table off a label: a row of process `j`
carries a label of `stageOwn j`, it fires only at a process whose program has
not been replaced (D23), it is Dirac, and its return takes the announced bit
free (D29). -/
class IsStageTable (P : Params) (M S : Type)
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M →
      PMF (ProcRecP P.n S) → Prop) : Prop where
  /-- A stage-side row carries a stage-side label. -/
  own : ∀ {j : Fin P.n} {q : ProcRecP P.n S} {L : NLabP P.n M}
    {μ : PMF (ProcRecP P.n S)}, stageStep j q L μ → stageOwn j L
  /-- A stage-side row fires only at an unreplaced program. -/
  honest : ∀ {j : Fin P.n} {q : ProcRecP P.n S} {L : NLabP P.n M}
    {μ : PMF (ProcRecP P.n S)}, stageStep j q L μ → q.1.corrupted = false
  /-- A stage-side row is Dirac. -/
  dirac : ∀ {j : Fin P.n} {q : ProcRecP P.n S} {L : NLabP P.n M}
    {μ : PMF (ProcRecP P.n S)}, stageStep j q L μ → ∃ q', μ = PMF.pure q'
  /-- A program's return row takes the announced bit free (D29): the bit the
  label carries is the network's business, so a return row that fires at one
  bit fires at every other, with the same successor. -/
  bndFree : ∀ {j : Fin P.n} {q : ProcRecP P.n S} {r : ℕ} {id : Fin P.n}
    {out : GbcaOut} {b b' : Bool} {μ : PMF (ProcRecP P.n S)},
    stageStep j q (Sum.inl (.retG r id out b)) μ →
      stageStep j q (Sum.inl (.retG r id out b')) μ

/-! ### Determinacy of the two rule tables

The composite is not an LTS — the coin resolution is probabilistic — but both
tables written here are Dirac, provided the reading's own rows are. -/

section Inversion

variable {P : Params} {M S : Type}
    {stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop}
    {j : Fin P.n} {q : ProcRecP P.n S} {ν : PMF (ProcRecP P.n S)}

/-- Every process transition is Dirac: the rows here are, and so are the
reading's own by `IsStageTable.dirac`. -/
theorem procStepN_dirac [IsStageTable P M S stageStep]
    {l : NLabP P.n M} (h : FlatProcStep P M S stageStep j q l ν) :
    ∃ q', ν = PMF.pure q' := by
  cases h
  case stageRow h' => exact IsStageTable.dirac h'
  all_goals exact ⟨_, rfl⟩

variable [IsStageTable P M S stageStep]

/-- The one `τ` row of a program's table is `terminate`: a silent step of a
program is that program's own termination, taken on a fired return and DECIDED
receipts from `2f + 1` distinct senders (D22). A replaced program has no silent
row at all, so the reading carries `corrupted = false` (D23), and no
graded-agreement row is silent, `stageOwn` holding of no `τ`. -/
theorem stepN_tau_terminate
    (h : FlatProcStep P M S stageStep j q (Silent.τ : NLabP P.n M) ν) :
    ∃ b : Bool, q.1.corrupted = false ∧ q.1.proc.returned = true ∧
      2 * P.f + 1 ≤ q.1.decidedCount b ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, { q.2 with terminated := true }) := by
  rw [nlab_tau] at h
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case terminate b hh hret hcnt hterm => exact ⟨b, hh, hret, hcnt, hterm, rfl⟩
  case corruptedIdle hh hτ hown => exact absurd rfl hτ

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as
its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any record. A participant's row carries the health
guard `corrupted = false`, and on a label outside `actsAt j` the replaced
program's self-loop is a second reading of the same label (D23). -/

theorem stepN_callABA_own {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.callABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
        input := some b, est := some b, round := 0, phase := .toCallG }, q.2)) ∨
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr rfl

theorem stepN_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.callABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retABA_own {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.retABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.input ≠ none ∧
      P.n - P.f ≤ q.1.decidedCount b ∧ q.1.proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with returned := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case ret =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.retABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem stepN_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.callG r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact absurd (IsStageTable.own h') hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.retG r id out bnd)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact absurd (IsStageTable.own h') hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem stepN_callW_own {r : ℕ}
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.callW r j)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.phase = .toCallW ∧ q.1.proc.round = r ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitW }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.callW r id)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retW_own {r : ℕ} {co : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.retW r j co)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      (∀ v : Bool, q.1.proc.lastGrade ≠ some (.A v)) ∧
      ν = PMF.pure (q.1.stepRound co, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.retW r id co)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
replaced, and a replaced program stands still. -/
theorem stepN_fail_own
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.fail j)) ν) :
    (q.1.corrupted = false ∧
      ν = PMF.pure ({ q.1 with corrupted := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_fail_foreign {k : Fin P.n} (hk : k ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inl (.fail k)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

/-! ### One program's rules on the rendezvous alphabet

The Byzantine stage rows have no row at the process they name (D22, D23), so
on `byzCallG`, `byzCallGLoop` and `byzRetG` every process idles and there is no
participant's row to read. -/

theorem stepN_gsnd_foreign {r : ℕ} {k : Fin P.n} {m : M} (hk : k ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.gsnd r k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact absurd (IsStageTable.own h') hk
  case gsndIdle => rfl
  case corruptedIdle => rfl

theorem stepN_gdlv_foreign {r : ℕ} {i k : Fin P.n} {m : M} (hi : i ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.gdlv r i k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact absurd (IsStageTable.own h') hi
  case gdlvIdle => rfl
  case corruptedIdle => rfl

theorem stepN_dsnd_self {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.dsnd j b)) ν) :
    (q.1.corrupted = false ∧ q.1.proc.input ≠ none ∧
      P.f + 1 ≤ q.1.decidedCount b ∧ ν = PMF.pure q) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case dsndRelay =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case dsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepN_dsnd_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.dsnd k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case dsndRelay => exact absurd rfl hk
  case dsndIdle => rfl
  case corruptedIdle => rfl

theorem stepN_ddlv_self {k : Fin P.n} {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.ddlv j k b)) ν) :
    q.1.corrupted = false ∧ b ∉ q.1.decIn k ∧
      ν = PMF.pure (q.1.recvDec k b, q.2) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case ddlvRecv => exact ⟨by assumption, by assumption, rfl⟩
  case ddlvIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_ddlv_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.ddlv i k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case ddlvRecv => exact absurd rfl hi
  case ddlvIdle => rfl
  case corruptedIdle => rfl

theorem stepN_retWPub_self {r : ℕ} {co b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.retWPub r j co b)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitW ∧ q.1.proc.round = r ∧
      q.1.proc.lastGrade = some (.A b) ∧
      ν = PMF.pure (q.1.stepRound co, q.2) := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case retWPub =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWPubIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retWPub_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.retWPub r id co b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  case retWPub => exact absurd rfl hid
  case retWPubIdle => rfl
  case corruptedIdle => rfl

theorem stepN_gcallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.gcallLoop r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact absurd (IsStageTable.own h') hid
  case gcallLoopIdle => rfl
  case corruptedIdle => rfl

theorem stepN_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.byzCallGLoop r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  all_goals rfl

theorem stepN_byzCallW {r : ℕ} {k : Fin P.n}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.byzCallW r k)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  all_goals rfl

theorem stepN_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.byzRetW r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case stageRow h' => exact (IsStageTable.own h').elim
  all_goals rfl

/-- The Byzantine graded-agreement call has no row at the process it names
(D11, D22, D23): the row carries its effect outside the program, and the
replaced program has no row on a label it acts on. -/
theorem stepN_byzCallG_noStep {r : ℕ} {b : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.byzCallG r j b)) ν) : False := by
  cases h with
  | stageRow _ _ _ h' => exact (IsStageTable.own h').elim
  | byzCallGIdle _ _ _ _ _ hk => exact hk rfl
  | corruptedIdle _ _ _ _ _ hown => exact hown rfl

/-- The Byzantine graded-agreement return has no row at the process it names
(D11, D22, D23). -/
theorem stepN_byzRetG_noStep {r : ℕ} {out : GbcaOut} {bnd : Bool}
    (h : FlatProcStep P M S stageStep j q (Sum.inr (.byzRetG r j out bnd)) ν) :
    False := by
  cases h with
  | stageRow _ _ _ h' => exact (IsStageTable.own h').elim
  | byzRetGIdle _ _ _ _ _ _ hk => exact hk rfl
  | corruptedIdle _ _ _ _ _ hown => exact hown rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a
process whose flag is up leaves both halves of its record where they stand.
Every row that writes carries the health guard, the reading's own rows by
`IsStageTable.honest`, so no row of a replaced program survives except a
self-loop. -/
theorem stepN_inert {L : NLabP P.n M} (hc : q.1.corrupted = true)
    (h : FlatProcStep P M S stageStep j q L ν) : ν = PMF.pure q := by
  cases h
  case stageRow h' => rw [IsStageTable.honest h'] at hc; exact absurd hc (by simp)
  all_goals simp_all

end Inversion

/-! ### The network adversary's rules, by label class -/

section NetInversion

variable {P : Params} {M G : Type} [DecidableEq M]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : NLabP P.n M → NetStateP P.n M G → G → G}
    {ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop}
    {s : NetStateP P.n M G} {μ : PMF (NetStateP P.n M G)}

/-- Every network transition is Dirac. -/
theorem netStep_dirac {l : NLabP P.n M}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s l μ) :
    ∃ s', μ = PMF.pure s' := by
  cases h <;> exact ⟨_, rfl⟩

theorem netStep_gsnd {r : ℕ} {j : Fin P.n} {m : M}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.gsnd r j m)) μ) :
    μ = PMF.pure ((s.gsent r j m).writeGhost ghostStep (Sum.inr (.gsnd r j m))) := by
  cases h; rfl

theorem netStep_gdlv {r : ℕ} {i j : Fin P.n} {m : M}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.gdlv r i j m)) μ) :
    m ∈ s.sent r j ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gdlv r i j m))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_dsnd {j : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.dsnd j b)) μ) :
    b ∉ s.dsent j ∧ μ = PMF.pure (s.dput j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_ddlv {i j : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.ddlv i j b)) μ) :
    b ∈ s.dsent j ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_retWPub {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.retWPub r id c b)) μ) :
    μ = PMF.pure ((s.dput id b).writeGhost ghostStep
      (Sum.inr (.retWPub r id c b))) := by
  cases h; rfl

theorem netStep_gcallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.gcallLoop r id b)) μ) :
    μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gcallLoop r id b))) := by
  cases h; rfl

theorem netStep_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzCallGLoop r k b)) μ) :
    k ∈ s.F ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzCallGLoop r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzCallW {r : ℕ} {k : Fin P.n}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzCallW r k)) μ) :
    k ∈ s.F ∧ μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzCallW r k))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzRetW r k b)) μ) :
    k ∈ s.F ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzRetW r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_byzCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzCallG r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure ((s.gsent r k (callPayload k b)).writeGhost ghostStep
      (Sum.inr (.byzCallG r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

/-- A Byzantine graded-agreement return is authorised by the corrupted set, and
the bound bit on its label stands in the round's ghost relation (D11). -/
theorem netStep_byzRetG {r : ℕ} {k : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inr (.byzRetG r k out bnd)) μ) :
    k ∈ s.F ∧ ghostOut s r k out bnd ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzRetG r k out bnd))) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem netStep_callABA {id : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.callABA id b)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

/-- A return is authorised either by the DECIDED sent of the returning process
or by its corruption (D23); the two rows share the label and the identity
successor. -/
theorem netStep_retABA {id : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.retABA id b)) μ) :
    (b ∈ s.dsent id ∨ id ∈ s.F) ∧ μ = PMF.pure s := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByz => exact ⟨Or.inr (by assumption), rfl⟩

theorem netStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.callG r id b)) μ) :
    μ = PMF.pure ((s.gsent r id (callPayload id b)).writeGhost ghostStep
      (Sum.inl (.callG r id b))) := by
  cases h; rfl

/-- A graded-agreement return announces the round's ghost output: the bound bit
on the label stands in `ghostOut` at the state the row starts from. -/
theorem netStep_retG {r : ℕ} {id : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.retG r id out bnd)) μ) :
    ghostOut s r id out bnd ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out bnd))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem netStep_callW {r : ℕ} {id : Fin P.n}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.callW r id)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem netStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s
      (Sum.inl (.retW r id c)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem netStep_fail {k : Fin P.n}
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl (.fail k)) μ) :
    k ∉ s.F ∧ s.F.card < P.f ∧ μ = PMF.pure (s.corrupt P k) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem netStep_tau
    (h : FlatNetStep P M G callPayload ghostStep ghostOut s (Sum.inl .tau) μ) :
    (∃ (r : ℕ) (k : Fin P.n) (m : M), k ∈ s.F ∧ μ = PMF.pure (s.gsent r k m)) ∨
    (∃ (k : Fin P.n) (b : Bool), k ∈ s.F ∧ μ = PMF.pure (s.dput k b)) := by
  cases h
  case byzG => exact Or.inl ⟨_, _, _, by assumption, rfl⟩
  case byzD => exact Or.inr ⟨_, _, by assumption, rfl⟩

end NetInversion

/-! ### The network's own field algebra

Each of the network adversary's three writes on the message record — a stage
multicast, a DECIDED multicast, and corruption — touches one field of the
state and leaves the others alone, the ghost among them. The ghost write
touches the ghost and nothing else. -/

section Fields

variable {n : ℕ} {M G : Type}

@[simp] theorem gsent_sent_self [DecidableEq M]
    (s : NetStateP n M G) (r : ℕ) (j : Fin n) (m : M) :
    (s.gsent r j m).sent r = Function.update (s.sent r) j (insert m (s.sent r j)) := by
  simp [NetStateP.gsent]

theorem gsent_sent_ne [DecidableEq M] (s : NetStateP n M G)
    (r : ℕ) (j : Fin n) (m : M) {r' : ℕ} (h : r' ≠ r) :
    (s.gsent r j m).sent r' = s.sent r' := by
  simp [NetStateP.gsent, Function.update_of_ne h]

@[simp] theorem gsent_dsent [DecidableEq M] (s : NetStateP n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.gsent r j m).dsent = s.dsent := rfl

@[simp] theorem gsent_F [DecidableEq M] (s : NetStateP n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.gsent r j m).F = s.F := rfl

@[simp] theorem gsent_ghostRec [DecidableEq M] (s : NetStateP n M G)
    (r : ℕ) (j : Fin n) (m : M) : (s.gsent r j m).ghostRec = s.ghostRec := rfl

@[simp] theorem dput_sent (s : NetStateP n M G)
    (j : Fin n) (b : Bool) : (s.dput j b).sent = s.sent := rfl

@[simp] theorem dput_dsent (s : NetStateP n M G)
    (j : Fin n) (b : Bool) :
    (s.dput j b).dsent = Function.update s.dsent j (insert b (s.dsent j)) := rfl

@[simp] theorem dput_F (s : NetStateP n M G)
    (j : Fin n) (b : Bool) : (s.dput j b).F = s.F := rfl

@[simp] theorem dput_ghostRec (s : NetStateP n M G)
    (j : Fin n) (b : Bool) : (s.dput j b).ghostRec = s.ghostRec := rfl

end Fields

@[simp] theorem netCorrupt_sent {P : Params} {M G : Type} (s : NetStateP P.n M G)
    (k : Fin P.n) : (NetStateP.corrupt P k s).sent = s.sent := by
  unfold NetStateP.corrupt; split <;> rfl

@[simp] theorem netCorrupt_dsent {P : Params} {M G : Type} (s : NetStateP P.n M G)
    (k : Fin P.n) : (NetStateP.corrupt P k s).dsent = s.dsent := by
  unfold NetStateP.corrupt; split <;> rfl

/-- Corruption leaves the ghost where it stands. -/
@[simp] theorem netCorrupt_ghostRec {P : Params} {M G : Type} (s : NetStateP P.n M G)
    (k : Fin P.n) : (NetStateP.corrupt P k s).ghostRec = s.ghostRec := by
  unfold NetStateP.corrupt; split <;> rfl

/-! ### The ghost write

The ghost write leaves the message record alone, and it leaves the ghost alone
too on a label naming no round. -/

section Ghost

variable {n : ℕ} {M G : Type}
    {ghostStep : NLabP n M → NetStateP n M G → G → G}

@[simp] theorem writeGhost_sent (s : NetStateP n M G) (L : NLabP n M) :
    (s.writeGhost ghostStep L).sent = s.sent := by
  unfold NetStateP.writeGhost; split <;> rfl

@[simp] theorem writeGhost_dsent (s : NetStateP n M G) (L : NLabP n M) :
    (s.writeGhost ghostStep L).dsent = s.dsent := by
  unfold NetStateP.writeGhost; split <;> rfl

@[simp] theorem writeGhost_F (s : NetStateP n M G) (L : NLabP n M) :
    (s.writeGhost ghostStep L).F = s.F := by
  unfold NetStateP.writeGhost; split <;> rfl

/-- A label naming no round leaves the whole state where it stands. -/
theorem writeGhost_of_round_none (s : NetStateP n M G) {L : NLabP n M}
    (h : roundOf L = none) : s.writeGhost ghostStep L = s := by
  unfold NetStateP.writeGhost; rw [h]

/-- The ghost record of the round the label names, after the write. -/
theorem writeGhost_ghostRec_self (s : NetStateP n M G) {L : NLabP n M} {r : ℕ}
    (h : roundOf L = some r) :
    (s.writeGhost ghostStep L).ghostRec r = ghostStep L s (s.ghostRec r) := by
  unfold NetStateP.writeGhost; rw [h]; simp

/-- The ghost record of any other round is untouched. -/
theorem writeGhost_ghostRec_ne (s : NetStateP n M G) {L : NLabP n M} {r r' : ℕ}
    (h : roundOf L = some r) (hne : r' ≠ r) :
    (s.writeGhost ghostStep L).ghostRec r' = s.ghostRec r' := by
  unfold NetStateP.writeGhost; rw [h]; simp [Function.update_of_ne hne]

end Ghost

/-! ### Dropping the ghost

Two erasures. `NetStateP.forgetGhost` sends the network's state to the state
over the trivial ghost `Unit`, and it commutes with each of the adversary's
three writes on the message record. Over `Unit` the ghost write is the
identity, so the erasure of a ghost write is the erasure of the state it
starts from. `forgetBound` sends a label to the label with the announced bound
bit fixed at `false`, and it is the identity elsewhere; two labels agree under
it exactly when they are equal or are returns of the same round, process and
graded outcome. -/

section Forget

variable {n : ℕ} {M G : Type}

@[simp] theorem forgetGhost_sent (s : NetStateP n M G) :
    s.forgetGhost.sent = s.sent := rfl

@[simp] theorem forgetGhost_dsent (s : NetStateP n M G) :
    s.forgetGhost.dsent = s.dsent := rfl

@[simp] theorem forgetGhost_F (s : NetStateP n M G) : s.forgetGhost.F = s.F := rfl

@[simp] theorem forgetGhost_gsent [DecidableEq M] (s : NetStateP n M G)
    (r : ℕ) (j : Fin n) (m : M) :
    (s.gsent r j m).forgetGhost = s.forgetGhost.gsent r j m := rfl

@[simp] theorem forgetGhost_dput (s : NetStateP n M G) (j : Fin n) (b : Bool) :
    (s.dput j b).forgetGhost = s.forgetGhost.dput j b := rfl

@[simp] theorem forgetGhost_corrupt {P : Params} (s : NetStateP P.n M G)
    (k : Fin P.n) :
    (NetStateP.corrupt P k s).forgetGhost = NetStateP.corrupt P k s.forgetGhost := by
  unfold NetStateP.corrupt
  simp only [forgetGhost_F]
  split <;> rfl

/-- The ghost write leaves the erasure where it stands. -/
@[simp] theorem forgetGhost_writeGhost (s : NetStateP n M G)
    (ghostStep : NLabP n M → NetStateP n M G → G → G) (L : NLabP n M) :
    (s.writeGhost ghostStep L).forgetGhost = s.forgetGhost := by
  unfold NetStateP.writeGhost
  split <;> rfl

/-- Over the trivial ghost the ghost write is the identity. -/
@[simp] theorem writeGhost_unit (s : NetStateP n M Unit) (L : NLabP n M) :
    s.writeGhost (fun _ _ _ => ()) L = s := by
  obtain ⟨sent, dsent, F, g⟩ := s
  unfold NetStateP.writeGhost
  split
  · exact congrArg _ (funext fun _ => rfl)
  · rfl

/-- The label with the announced bound bit dropped: a graded-agreement return
keeps its round, the process it answers and its graded outcome, and every
other label stands. -/
def forgetBound : Lab n → Lab n
  | .retG r id out _ => .retG r id out false
  | l => l

@[simp] theorem forgetBound_tau : forgetBound (Lab.tau : Lab n) = Lab.tau := rfl

@[simp] theorem forgetBound_retG (r : ℕ) (id : Fin n) (out : GbcaOut) (bnd : Bool) :
    forgetBound (Lab.retG r id out bnd) = Lab.retG r id out false := rfl

/-- Two labels agree under the erasure exactly when they are equal, or are
graded-agreement returns of the same round, process and graded outcome. -/
theorem forgetBound_eq_iff (l l' : Lab n) :
    forgetBound l = forgetBound l' ↔
      l = l' ∨ ∃ (r : ℕ) (id : Fin n) (out : GbcaOut) (b b' : Bool),
        l = Lab.retG r id out b ∧ l' = Lab.retG r id out b' := by
  constructor
  · intro h
    cases l <;> cases l' <;> simp_all [forgetBound]
  · rintro (rfl | ⟨r, id, out, b, b', rfl, rfl⟩) <;> rfl

/-- The erasure keeps a label inside the sub-protocol API and outside it. -/
@[simp] theorem forgetBound_mem_hiddenAPI (l : Lab n) :
    forgetBound l ∈ Lab.hiddenAPI n ↔ l ∈ Lab.hiddenAPI n := by
  cases l <;> simp [forgetBound]

end Forget

/-! ### Reading composite transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ parallel ∘ syncProduct`; the
lemmas below unfold it once and for all. -/

section Composite

variable {P : Params} {M S : Type}
    {stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop}
    [IsStageTable P M S stageStep]

/-- A synchronised transition of the process group on a visible label: every
process steps, and the joint distribution is Dirac. -/
theorem syncN_inv {u : ∀ _ : Fin P.n, ProcRecP P.n S} {l : NLabP P.n M}
    {μ : PMF (∀ _ : Fin P.n, ProcRecP P.n S)} (hl : l ≠ Silent.τ)
    (h : (System.syncProduct (flatProcN P M S stageStep)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, ProcRecP P.n S,
      μ = PMF.pure x ∧ ∀ i, FlatProcStep P M S stageStep i (u i) l (PMF.pure (x i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => procStepN_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd rfl hl

/-- A silent transition of the process group: `τ` is interleaved, so exactly
one program moves and the rest hold their state. -/
theorem syncN_tau_inv {u : ∀ _ : Fin P.n, ProcRecP P.n S}
    {μ : PMF (∀ _ : Fin P.n, ProcRecP P.n S)}
    (h : (System.syncProduct (flatProcN P M S stageStep)).step u
      (Silent.τ : NLabP P.n M) μ) :
    ∃ (i : Fin P.n) (y : ProcRecP P.n S),
      FlatProcStep P M S stageStep i (u i) (Silent.τ : NLabP P.n M) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y) := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, rfl⟩
  · exact absurd rfl hτ
  · obtain ⟨y, rfl⟩ := procStepN_dirac hstep
    exact ⟨i, y, hstep, by rw [piPMF_update_pure, PMF.pure_map]⟩

section WithNet

variable {G : Type} [DecidableEq M] [Inhabited G]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : NLabP P.n M → NetStateP P.n M G → G → G}
    {ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop}

omit [IsStageTable P M S stageStep] in
/-- The composite step relation of the group, unfolded to the hidden
rendezvous case and the shared-label case. -/
theorem flatGroup_step_iff (q : FlatState P M S G) (l : Lab P.n)
    (μ : PMF (FlatState P M S G)) :
    (flatGroup P M S G stageStep callPayload ghostStep ghostOut).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvtP P.n M,
        (flatPre P M S G stageStep callPayload ghostStep ghostOut).step q (Sum.inr e) μ) ∨
      (flatPre P M S G stageStep callPayload ghostStep ghostOut).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

omit [IsStageTable P M S stageStep] in
/-- The flat reading's step relation: a sub-protocol API label seen as `τ`, or
a label that survives the hiding. -/
theorem flat_step_iff (q : FlatState P M S G) (l : Lab P.n)
    (μ : PMF (FlatState P M S G)) :
    (flat P M S G stageStep callPayload ghostStep ghostOut).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n,
        (flatGroup P M S G stageStep callPayload ghostStep ghostOut).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧
        (flatGroup P M S G stageStep callPayload ghostStep ghostOut).step q l μ) :=
  System.abstract_step _ _ _ _ _

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem flatPre_event_inv {u : ∀ _ : Fin P.n, ProcRecP P.n S}
    {w : NetStateP P.n M G} {o : ℕ → WCC.SpecState P.n} {e : NetEvtP P.n M}
    {μ : PMF (FlatState P M S G)}
    (h : (flatPre P M S G stageStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRecP P.n S) (w' : NetStateP P.n M G)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, FlatProcStep P M S stageStep i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      FlatNetStep P M G callPayload ghostStep ghostOut w (Sum.inr e) (PMF.pure w') ∧
      (wccLiftP P M).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) := by
  rw [flatPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ := syncN_inv (by simp) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN, hO, rfl⟩
    · simp [nlab_tau] at habs
    · simp [nlab_tau] at habs
  · simp [nlab_tau] at habs
  · simp [nlab_tau] at habs

/-- A visible shared-label transition. -/
theorem flatPre_lab_inv {u : ∀ _ : Fin P.n, ProcRecP P.n S}
    {w : NetStateP P.n M G} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n}
    (hl : l ≠ Lab.tau) {μ : PMF (FlatState P M S G)}
    (h : (flatPre P M S G stageStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRecP P.n S) (w' : NetStateP P.n M G)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, FlatProcStep P M S stageStep i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      FlatNetStep P M G callPayload ghostStep ghostOut w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) := by
  rw [flatPre, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂₃, hS, hNW, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
  · obtain ⟨x, rfl, hall⟩ :=
      syncN_inv (by rw [nlab_tau]; exact fun hh => hl (Sum.inl_injective hh)) hS
    rw [System.parallel_step] at hNW
    rcases hNW with ⟨-, μ₂, μ₃, hN, hO, rfl⟩ | ⟨habs, -⟩ | ⟨habs, -⟩
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact ⟨x, w', μ₃, hall, hN,
        (System.mapIdle_step_some (wccPull_inl l) μ₃).mp hO, rfl⟩
    · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
    · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl
  · rw [nlab_tau] at habs; exact absurd (Sum.inl_injective habs) hl

/-- A silent shared-label transition: one process terminating, or the network's
own injection. The coin oracle has no silent row, so it contributes none. -/
theorem flatPre_tau_inv {u : ∀ _ : Fin P.n, ProcRecP P.n S}
    {w : NetStateP P.n M G} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (FlatState P M S G)}
    (h : (flatPre P M S G stageStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inl Lab.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcRecP P.n S),
      FlatProcStep P M S stageStep i (u i) (Sum.inl Lab.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', FlatNetStep P M G callPayload ghostStep ghostOut w (Sum.inl .tau)
        (PMF.pure w') ∧
      μ = PMF.pure (u, w', o)) := by
  rw [flatPre, System.parallel_step] at h
  rcases h with ⟨habs, -⟩ | ⟨-, μ₁, hS, rfl⟩ | ⟨-, μ₂₃, hNW, rfl⟩
  · exact absurd rfl habs
  · obtain ⟨i, y, hstep, rfl⟩ := syncN_tau_inv hS
    exact Or.inl ⟨i, y, hstep, by rw [prodPMF_pure_pure]⟩
  · rw [System.parallel_step] at hNW
    rcases hNW with ⟨habs, -⟩ | ⟨-, μ₂, hN, rfl⟩ | ⟨-, μ₃, hO, rfl⟩
    · exact absurd rfl habs
    · obtain ⟨w', rfl⟩ := netStep_dirac hN
      exact Or.inr ⟨w', hN, by rw [prodPMF_pure_pure, prodPMF_pure_pure]⟩
    · exact (ABA.WCC.specFamily_tau_inv P
        ((System.mapIdle_step_some (wccPull_inl Lab.tau) μ₃).mp hO)).elim

/-! ### The bound bit on a return

The two graded-agreement returns are the only rows that read the ghost, and
what they read is the relation `ghostOut` at the network's state. A composite
transition on either therefore constrains the bound bit its label carries. -/

/-- A composite graded-agreement return announces a bit the network's ghost
relation admits. -/
theorem flatPre_retG_bound {u : ∀ _ : Fin P.n, ProcRecP P.n S}
    {w : NetStateP P.n M G} {o : ℕ → WCC.SpecState P.n}
    {r : ℕ} {id : Fin P.n} {out : GbcaOut} {bnd : Bool}
    {μ : PMF (FlatState P M S G)}
    (h : (flatPre P M S G stageStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inl (.retG r id out bnd)) μ) :
    ghostOut w r id out bnd := by
  have hne : (Lab.retG r id out bnd : Lab P.n) ≠ Lab.tau := by simp
  obtain ⟨x, w', ω, -, hN, -, -⟩ := flatPre_lab_inv hne h
  exact (netStep_retG hN).1

/-- A composite Byzantine graded-agreement return announces a bit the same
ghost relation admits (D11). -/
theorem flatPre_byzRetG_bound {u : ∀ _ : Fin P.n, ProcRecP P.n S}
    {w : NetStateP P.n M G} {o : ℕ → WCC.SpecState P.n}
    {r : ℕ} {k : Fin P.n} {out : GbcaOut} {bnd : Bool}
    {μ : PMF (FlatState P M S G)}
    (h : (flatPre P M S G stageStep callPayload ghostStep ghostOut).step (u, w, o)
      (Sum.inr (.byzRetG r k out bnd)) μ) :
    ghostOut w r k out bnd := by
  obtain ⟨x, w', μ₃, -, hN, -, -⟩ := flatPre_event_inv h
  exact (netStep_byzRetG hN).2.1

end WithNet

end Composite

end Net
end ABA
end PLTS
