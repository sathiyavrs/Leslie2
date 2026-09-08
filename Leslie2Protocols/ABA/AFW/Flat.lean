/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Reading.Flat
import Leslie2Protocols.ABA.Round.Low

/-!
# The gather-based protocol as it runs

The gather-based graded agreement, read as a protocol rather than as a
composition: `n` programs beside one network adversary and the coin oracle.
This is the flat reading of `ABA/Reading/Flat.lean` at the gather-based
implementation, as `ABA/ABDY/Protocol.lean` is that reading at the ladder, and it
supplies the same three things — a stage message type, a stage record, and the
implementation's rows. It sits in the namespace `AFW`, after Attiya, Flam and
Welch, and so `AFW.protocol` is what `protocol` is at the ladder.

## One pool for every fabric

A round of the gather-based implementation carries `4n + 2` message fabrics:
one for each of the two gather instances, and one for each of the `4n` Bracha
instances — `n` carrying the inputs and `n` carrying the `BIND` payloads, in
each of the two gathers. The adversary here holds one pool family per round
instead, over the tagged message type `Msg`, whose tag names the fabric a
message belongs to and, for a Bracha message, the instance it belongs to. The
pool index stays the sender, so a threshold still counts distinct senders
(D5).

## The record of one process

A process's data is scattered across those instances: `j` holds its own box in
each of the `4n + 2` of them, and the composed reading indexes those boxes by
instance and then by process. A program must hold its own data and no one
else's, so `StageRec` holds them the other way round — `j`'s box in each
gather instance, and `j`'s box in each of the `n` instances of each Bracha
family. Every guard of the gather-based implementation reads the acting
process's own boxes and the fabrics, and the two rows that read a fabric are
the adversary's delivery and its Byzantine injection, so the transposition
loses nothing.

## The rows

The stage-side rows are the rows of `Gather.LowStep` and `GBCA.LowPairStep`
cut into their process half and their network half. A send writes the sender's
own record and the network pools the message; a delivery files the message in
the receiver's own box, dispatched on the tag. Three rows are fused, as they
are in the composed reading (D28): the graded-agreement call broadcasts the
input, the `BIND` send is a broadcast call, and the first gather's return to a
process is that process's call of the second gather.

The Bracha return is not a row here. Gather reads a broadcast delivery as an
`n − f` `VOTE` receipt quorum on the receiving box (`apIn`, `apBind`), never
through a returned flag, and the composed reading embeds only the silent rows
of a Bracha instance, its return not among them.
-/

namespace PLTS
namespace ABA
namespace AFW

open Net Gather

/-! ### The tagged message type -/

/-- A round's messages: the two gather fabrics and the `4n` Bracha fabrics,
tagged by the fabric they belong to. A Bracha tag carries the instance, whose
index is its leader. -/
inductive Msg (n : ℕ) : Type
  /-- A message of the first gather's fabric. -/
  | ga1 (m : GaMsg n Bool)
  /-- A message of the second gather's fabric. -/
  | ga2 (m : GaMsg n (Option Bool))
  /-- A message of the input-broadcast instance `k` of the first gather. -/
  | brbIn1 (k : Fin n) (m : BRB.BMsg Bool)
  /-- A message of the bind-broadcast instance `k` of the first gather. -/
  | brbBind1 (k : Fin n) (m : BRB.BMsg (APSet n Bool))
  /-- A message of the input-broadcast instance `k` of the second gather. -/
  | brbIn2 (k : Fin n) (m : BRB.BMsg (Option Bool))
  /-- A message of the bind-broadcast instance `k` of the second gather. -/
  | brbBind2 (k : Fin n) (m : BRB.BMsg (APSet n (Option Bool)))
  deriving DecidableEq

/-! ### The record of one process in one round -/

/-- One process's data in one round, held by instance: its box in each gather
instance, and its box in each of the `n` instances of each broadcast family.
This is the composed reading's instance-major indexing transposed. -/
structure StageRec (n : ℕ) : Type where
  /-- The process's box in the first gather instance. -/
  ga1 : Box n (PRec n Bool) (GaMsg n Bool)
  /-- The process's box in the second gather instance. -/
  ga2 : Box n (PRec n (Option Bool)) (GaMsg n (Option Bool))
  /-- The process's box in each input-broadcast instance of the first
  gather. -/
  brbIn1 : ∀ _ : Fin n, Box n (BRB.PState Bool) (BRB.BMsg Bool)
  /-- The process's box in each bind-broadcast instance of the first
  gather. -/
  brbBind1 : ∀ _ : Fin n, Box n (BRB.PState (APSet n Bool)) (BRB.BMsg (APSet n Bool))
  /-- The process's box in each input-broadcast instance of the second
  gather. -/
  brbIn2 : ∀ _ : Fin n, Box n (BRB.PState (Option Bool)) (BRB.BMsg (Option Bool))
  /-- The process's box in each bind-broadcast instance of the second
  gather. -/
  brbBind2 : ∀ _ : Fin n,
    Box n (BRB.PState (APSet n (Option Bool))) (BRB.BMsg (APSet n (Option Bool)))

namespace StageRec

variable {n : ℕ}

/-- The initial record: every box empty over the initial local record. -/
def initial (n : ℕ) : StageRec n where
  ga1 := Box.initial n _ (PRec.initial n Bool)
  ga2 := Box.initial n _ (PRec.initial n (Option Bool))
  brbIn1 := fun _ => Box.initial n _ (BRB.PState.initial Bool)
  brbBind1 := fun _ => Box.initial n _ (BRB.PState.initial (APSet n Bool))
  brbIn2 := fun _ => Box.initial n _ (BRB.PState.initial (Option Bool))
  brbBind2 := fun _ => Box.initial n _ (BRB.PState.initial (APSet n (Option Bool)))

/-- File a delivered message in the box of the fabric its tag names. -/
def deliverTo (s : StageRec n) (k : Fin n) : Msg n → StageRec n
  | .ga1 m => { s with ga1 := s.ga1.deliverTo k m }
  | .ga2 m => { s with ga2 := s.ga2.deliverTo k m }
  | .brbIn1 i m =>
      { s with brbIn1 := Function.update s.brbIn1 i ((s.brbIn1 i).deliverTo k m) }
  | .brbBind1 i m =>
      { s with brbBind1 := Function.update s.brbBind1 i ((s.brbBind1 i).deliverTo k m) }
  | .brbIn2 i m =>
      { s with brbIn2 := Function.update s.brbIn2 i ((s.brbIn2 i).deliverTo k m) }
  | .brbBind2 i m =>
      { s with brbBind2 := Function.update s.brbBind2 i ((s.brbBind2 i).deliverTo k m) }

end StageRec

/-- The gather-based stage record, as the flat reading consumes it. -/
instance instStageRecord (n : ℕ) : StageRecord n (Msg n) (StageRec n) where
  initial := StageRec.initial n
  deliverTo s k m := s.deliverTo k m

@[simp] theorem stageRecord_initial (n : ℕ) :
    (StageRecord.initial : StageRec n) = StageRec.initial n := rfl

@[simp] theorem stageRecord_deliverTo (n : ℕ) (s : StageRec n) (k : Fin n)
    (m : Msg n) : (StageRecord.deliverTo s k m : StageRec n) = s.deliverTo k m := rfl

/-- The stage-side record of one process: the round records it holds, and
whether it has terminated (D22). -/
abbrev StageSideRec (n : ℕ) : Type := StageSideRecP (StageRec n)

/-- The state of one process: its round-loop record and its stage-side
record. -/
abbrev ProcRec (n : ℕ) : Type := ProcRecP n (StageRec n)

/-- The state of the network adversary. -/
abbrev NetState (n : ℕ) : Type := NetStateP n (Msg n)

/-! ### The derived receipt predicates

A broadcast delivery is a receipt quorum on the receiving box, not an event
(D28). Read at the process that holds the box, each predicate below is a count
on that process's own record. -/

variable {P : Params}

/-- The process holds the pair `(k, v)` of the first gather: an `n − f`
`VOTE v` receipt quorum in the input-broadcast instance `k`. -/
def apIn1 (P : Params) (s : StageRec P.n) (k : Fin P.n) (v : Bool) : Prop :=
  P.n - P.f ≤ (s.brbIn1 k).recvCount (BRB.BMsg.vote v)

/-- The process holds `q`'s bind payload of the first gather. -/
def apBind1 (P : Params) (s : StageRec P.n) (q : Fin P.n) (U : APSet P.n Bool) : Prop :=
  P.n - P.f ≤ (s.brbBind1 q).recvCount (BRB.BMsg.vote U)

/-- A payload set of the first gather is approved here: every pair is held. -/
def approved1 (P : Params) (s : StageRec P.n) (A : APSet P.n Bool) : Prop :=
  ∀ p ∈ A, apIn1 P s p.1 p.2

/-- The process holds the pair `(k, v)` of the second gather. -/
def apIn2 (P : Params) (s : StageRec P.n) (k : Fin P.n) (v : Option Bool) : Prop :=
  P.n - P.f ≤ (s.brbIn2 k).recvCount (BRB.BMsg.vote v)

/-- The process holds `q`'s bind payload of the second gather. -/
def apBind2 (P : Params) (s : StageRec P.n) (q : Fin P.n)
    (U : APSet P.n (Option Bool)) : Prop :=
  P.n - P.f ≤ (s.brbBind2 q).recvCount (BRB.BMsg.vote U)

/-- A payload set of the second gather is approved here. -/
def approved2 (P : Params) (s : StageRec P.n) (A : APSet P.n (Option Bool)) : Prop :=
  ∀ p ∈ A, apIn2 P s p.1 p.2

/-! ### The stage-side rows -/

/-- The stage-side rows of process `j`: the two gather ladders, the `4n`
Bracha instances beneath them, the three fused rows, and the delivery. -/
inductive StageStep (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLabP P.n (Msg P.n) → PMF (ProcRec P.n) → Prop
  /-- The graded-agreement call: the round loop hands its estimate to the
  round's first gather, which records it and broadcasts it through the
  process's own input-broadcast instance. The `⟨INIT, b⟩` multicast is the
  network's half. -/
  | callG (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hest : c.proc.est = some b)
      (hin : ((p.stage r).ga1.proc).input = none)
      (hbin : (((p.stage r).brbIn1 j).proc).input = none) :
      StageStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          p.setStage r
            { (p.stage r) with
              ga1 := (p.stage r).ga1.setP
                { ((p.stage r).ga1.proc) with input := some b }
              brbIn1 := Function.update (p.stage r).brbIn1 j
                (((p.stage r).brbIn1 j).setP
                  { (((p.stage r).brbIn1 j).proc) with input := some b }) }))
  /-- The graded-agreement call against an already-called record: the round
  loop moves, the round record does not. -/
  | gcallLoop (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b)
      (hin : ((p.stage r).ga1.proc).input ≠ none) :
      StageStep P j (c, p) (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, p))
  /-- The first gather's `ECHO`: the process holds `n − f` pairs. -/
  | ga1Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (A : APSet P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (happ : approved1 P (p.stage r) A) (hcard : P.n - P.f ≤ A.card)
      (hsend : ((p.stage r).ga1.proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga1 (.echo A))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with sentEcho := some A } }))
  /-- The first gather's `VOTE`: `n − f` senders' `ECHO` payloads, each held
  here and contained in the vote payload, are delivered. -/
  | ga1Vote (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (U : APSet P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (happ : approved1 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ ((p.stage r).ga1.inbox q) ∧
          approved1 P (p.stage r) A ∧ A ⊆ U)
      (hsend : ((p.stage r).ga1.proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga1 (.vote U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with sentVote := some U } }))
  /-- The first gather's `BIND`: `n − f` senders' `VOTE` payloads, each held
  here and contained in the bind payload, are delivered; the payload is
  broadcast through the process's own bind-broadcast instance. -/
  | ga1Bind (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (U : APSet P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (hbc : (((p.stage r).brbBind1 j).proc).input = none)
      (happ : approved1 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ ((p.stage r).ga1.inbox q) ∧
          approved1 P (p.stage r) W ∧ W ⊆ U) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 j (.init U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 j
              (((p.stage r).brbBind1 j).setP
                { (((p.stage r).brbBind1 j).proc) with input := some U }) }))
  /-- The second gather's `ECHO`. -/
  | ga2Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (A : APSet P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (happ : approved2 P (p.stage r) A) (hcard : P.n - P.f ≤ A.card)
      (hsend : ((p.stage r).ga2.proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga2 (.echo A))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with sentEcho := some A } }))
  /-- The second gather's `VOTE`. -/
  | ga2Vote (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (U : APSet P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (happ : approved2 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ ((p.stage r).ga2.inbox q) ∧
          approved2 P (p.stage r) A ∧ A ⊆ U)
      (hsend : ((p.stage r).ga2.proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga2 (.vote U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with sentVote := some U } }))
  /-- The second gather's `BIND`. -/
  | ga2Bind (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (U : APSet P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (hbc : (((p.stage r).brbBind2 j).proc).input = none)
      (happ : approved2 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ ((p.stage r).ga2.inbox q) ∧
          approved2 P (p.stage r) W ∧ W ⊆ U) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 j (.init U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 j
              (((p.stage r).brbBind2 j).setP
                { (((p.stage r).brbBind2 j).proc) with input := some U }) }))
  /-- The first gather returns and the process calls the second gather with
  the candidate, broadcasting it through its own input-broadcast instance of
  the second gather (D24, D28). -/
  | link (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (g : Fin P.n → Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (hsubap : ∀ k x, g k = some x → apIn1 P (p.stage r) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, apBind1 P (p.stage r) q U ∧ APSet.subMap U g)
      (hr1 : ((p.stage r).ga1.proc).returned = false)
      (hin2 : ((p.stage r).ga2.proc).input = none)
      (hbin2 : (((p.stage r).brbIn2 j).proc).input = none) :
      StageStep P j (c, p)
        (Sum.inr (.gsnd r j (.brbIn2 j (.init (GBCA.cand P g)))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with returned := true }
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with input := some (GBCA.cand P g) }
            brbIn2 := Function.update (p.stage r).brbIn2 j
              (((p.stage r).brbIn2 j).setP
                { (((p.stage r).brbIn2 j).proc) with
                  input := some (GBCA.cand P g) }) }))
  /-- The second gather returns and the round returns the graded outcome
  (D24). -/
  | retG (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (g : Fin P.n → Option (Option Bool))
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (hsubap : ∀ k x, g k = some x → apIn2 P (p.stage r) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, apBind2 P (p.stage r) q U ∧ APSet.subMap U g)
      (hr2 : ((p.stage r).ga2.proc).returned = false) :
      StageStep P j (c, p) (Sum.inl (.retG r j (GBCA.gradeOf P g)))
        (PMF.pure (c.setProc { c.proc with
            est := (GBCA.gradeOf P g).est, lastGrade := some (GBCA.gradeOf P g),
            phase := .toCallW },
          p.setStage r
            { (p.stage r) with
              ga2 := (p.stage r).ga2.setP
                { ((p.stage r).ga2.proc) with returned := true } }))
  /-- `ECHO` in an input-broadcast instance of the first gather: the leader's
  `⟨INIT, m⟩` is delivered here and no `ECHO` is out. -/
  | in1Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbIn1 i).inbox i)
      (hsend : (((p.stage r).brbIn1 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn1 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn1 := Function.update (p.stage r).brbIn1 i
              (((p.stage r).brbIn1 i).setP
                { (((p.stage r).brbIn1 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `n − f` `ECHO` quorum in an input-broadcast instance of the
  first gather. -/
  | in1VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.n - P.f ≤ ((p.stage r).brbIn1 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbIn1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn1 := Function.update (p.stage r).brbIn1 i
              (((p.stage r).brbIn1 i).setP
                { (((p.stage r).brbIn1 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification, on `f + 1` `VOTE` receipts. -/
  | in1VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbIn1 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbIn1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn1 := Function.update (p.stage r).brbIn1 i
              (((p.stage r).brbIn1 i).setP
                { (((p.stage r).brbIn1 i).proc) with sentVote := some m }) }))
  /-- `ECHO` in a bind-broadcast instance of the first gather. -/
  | bind1Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbBind1 i).inbox i)
      (hsend : (((p.stage r).brbBind1 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 i
              (((p.stage r).brbBind1 i).setP
                { (((p.stage r).brbBind1 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `n − f` `ECHO` quorum in a bind-broadcast instance of the
  first gather. -/
  | bind1VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.n - P.f ≤ ((p.stage r).brbBind1 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbBind1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 i
              (((p.stage r).brbBind1 i).setP
                { (((p.stage r).brbBind1 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification in a bind-broadcast instance of the first
  gather. -/
  | bind1VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbBind1 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbBind1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 i
              (((p.stage r).brbBind1 i).setP
                { (((p.stage r).brbBind1 i).proc) with sentVote := some m }) }))
  /-- `ECHO` in an input-broadcast instance of the second gather. -/
  | in2Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbIn2 i).inbox i)
      (hsend : (((p.stage r).brbIn2 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn2 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn2 := Function.update (p.stage r).brbIn2 i
              (((p.stage r).brbIn2 i).setP
                { (((p.stage r).brbIn2 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `n − f` `ECHO` quorum in an input-broadcast instance of the
  second gather. -/
  | in2VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.n - P.f ≤ ((p.stage r).brbIn2 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbIn2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn2 := Function.update (p.stage r).brbIn2 i
              (((p.stage r).brbIn2 i).setP
                { (((p.stage r).brbIn2 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification in an input-broadcast instance of the second
  gather. -/
  | in2VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbIn2 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbIn2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn2 := Function.update (p.stage r).brbIn2 i
              (((p.stage r).brbIn2 i).setP
                { (((p.stage r).brbIn2 i).proc) with sentVote := some m }) }))
  /-- `ECHO` in a bind-broadcast instance of the second gather. -/
  | bind2Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbBind2 i).inbox i)
      (hsend : (((p.stage r).brbBind2 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 i
              (((p.stage r).brbBind2 i).setP
                { (((p.stage r).brbBind2 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `n − f` `ECHO` quorum in a bind-broadcast instance of the
  second gather. -/
  | bind2VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hcnt : P.n - P.f ≤ ((p.stage r).brbBind2 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbBind2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 i
              (((p.stage r).brbBind2 i).setP
                { (((p.stage r).brbBind2 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification in a bind-broadcast instance of the second
  gather. -/
  | bind2VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbBind2 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbBind2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 i
              (((p.stage r).brbBind2 i).setP
                { (((p.stage r).brbBind2 i).proc) with sentVote := some m }) }))
  /-- Delivery, receiver's half: file the message in the box of the fabric its
  tag names. Authenticity is the network's conjunct. -/
  | gdlvRecv (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (k : Fin P.n)
      (m : Msg P.n) (hh : c.corrupted = false) (hterm : p.terminated = false) :
      StageStep P j (c, p) (Sum.inr (.gdlv r j k m))
        (PMF.pure (c, p.deliverTo r k m))

/-- The rows above meet the flat reading's conditions: each carries a label of
`stageOwn j`, each fires only at an unreplaced program, and each is Dirac. -/
instance instIsStageTable (P : Params) :
    IsStageTable P (Msg P.n) (StageRec P.n) (StageStep P) where
  own h := by cases h <;> rfl
  honest h := by cases h <;> assumption
  dirac h := by cases h <;> exact ⟨_, rfl⟩

/-! ### The transposed record writes one box at a time

A tagged delivery reaches exactly the box its tag names and leaves every other
box of the record where it stands. These are the facts the substitution into
the composed reading rests on, the composed side writing the same box through
its instance-major indexing. -/

section Transposition

variable {n : ℕ}

example (s : StageRec n) (k i : Fin n) (m : BRB.BMsg Bool) :
    ((s.deliverTo k (.brbIn1 i m)).brbIn1 i).inbox k
      = insert m ((s.brbIn1 i).inbox k) := by
  simp [StageRec.deliverTo, Box.deliverTo]

example (s : StageRec n) (k i i' : Fin n) (m : BRB.BMsg Bool) (h : i' ≠ i) :
    (s.deliverTo k (.brbIn1 i m)).brbIn1 i' = s.brbIn1 i' := by
  simp [StageRec.deliverTo, Function.update_of_ne h]

example (s : StageRec n) (k i : Fin n) (m : BRB.BMsg Bool) :
    (s.deliverTo k (.brbIn1 i m)).ga1 = s.ga1 := by
  simp [StageRec.deliverTo]

example (s : StageRec n) (k : Fin n) (m : GaMsg n Bool) :
    (s.deliverTo k (.ga1 m)).ga1.inbox k = insert m (s.ga1.inbox k) := by
  simp [StageRec.deliverTo, Box.deliverTo]

example (s : StageRec n) (k : Fin n) (m : GaMsg n Bool) (i : Fin n) :
    (s.deliverTo k (.ga1 m)).brbIn1 i = s.brbIn1 i := by
  simp [StageRec.deliverTo]

example (P : Params) (p : StageSideRec P.n) (r : ℕ) (sr : StageRec P.n) :
    (p.setStage r sr).stage r = sr := by simp

end Transposition

/-! ### The protocol -/

/-- The message the graded-agreement call multicasts: the caller's input,
broadcast through the caller's own input-broadcast instance of the first
gather. -/
def gCallPayload (P : Params) : Fin P.n → Bool → Msg P.n := fun id b => .brbIn1 id (.init b)

/-- The step relation of the program of process `j`. -/
abbrev ProcStep (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLabP P.n (Msg P.n) → PMF (ProcRec P.n) → Prop :=
  FlatProcStep P (Msg P.n) (StageRec P.n) (StageStep P) j

/-- The step relation of the network adversary. -/
abbrev NetStep (P : Params) :
    NetState P.n → NLabP P.n (Msg P.n) → PMF (NetState P.n) → Prop :=
  FlatNetStep P (Msg P.n) (gCallPayload P)


/-- The state of the gather-based protocol: the process family, the network
adversary and the coin oracle. -/
abbrev ProtocolState (P : Params) : Type :=
  Net.FlatState P (Msg P.n) (StageRec P.n)

/-- The three components side by side, over the extended alphabet. -/
noncomputable def protocolPre (P : Params) :
    System (ProtocolState P) (Net.NLabP P.n (Msg P.n)) :=
  Net.flatPre P (Msg P.n) (StageRec P.n) (StageStep P)
    (gCallPayload P)

/-- The gather-based protocol group: the rendezvous alphabet hidden, the
result read back over `Lab n`. -/
noncomputable def protocolGroup (P : Params) : System (ProtocolState P) (Lab P.n) :=
  Net.flatGroup P (Msg P.n) (StageRec P.n) (StageStep P)
    (gCallPayload P)

/-- **The gather-based protocol**: the group with the sub-protocol API
hidden. -/
noncomputable def protocol (P : Params) : System (ProtocolState P) (Lab P.n) :=
  Net.flat P (Msg P.n) (StageRec P.n) (StageStep P)
    (gCallPayload P)

end AFW

end ABA
end PLTS
