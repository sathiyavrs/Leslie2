/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ABDY.Components
import Leslie2Protocols.ABA.Reading.Flat

/-!
# The protocol as it runs

The subject of the whole chain: `n` programs, one per process, beside one
network adversary and the coin oracle. A program reads its own records, its own
inboxes and its own replacement flag, and nothing else about corruption: not
the corrupted set, not the budget, not another process's status (D23). The
adversary holds the round-tagged message pools, the DECIDED pools and the
corrupted set with its budget, and it is the sole authority on the Byzantine
labels. The coin oracle is held at specification level.

The shape of that reading is the flat reading of `ABA/Reading/Flat.lean`, which
carries the round loop, the DECIDED pools, the coin handshake, corruption, the
network adversary and the composition pipeline for any graded-agreement
implementation. This file supplies the three things a reading fixes and
nothing else:

* the stage message type, `GBCA.Msg` — the five message levels of
  `ABA/ABDY/Impl.lean` (D18);
* the per-process per-round stage record, `GBCA.StageRec`, held by round in a
  finite map (D22);
* the rows of the implementation, `AbdyStageStep`: the graded-agreement call, the
  eight stage multicasts, the stage delivery, the call against an
  already-called record, and the three graded returns.

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
inbox write. The Byzantine stage drives have no row at the process they name
(D11, D22).
-/

namespace PLTS
namespace ABA
namespace Net

/-! ### The stage-side vocabulary at ABDY22's implementation -/

/-- The stage-side record of one process: the stage record of every round the
process has touched, and whether it has terminated (D22). -/
abbrev StageSideRec (n : ℕ) : Type := StageSideRecP (GBCA.StageRec n)

/-- ABDY22's stage record, as the flat reading consumes it. -/
instance instStageRecord (n : ℕ) : StageRecord n GBCA.Msg (GBCA.StageRec n) where
  initial := GBCA.StageRec.initial n
  deliverTo p k m := p.deliverTo k m

namespace StageSideRec

variable {n : ℕ}

/-- The initial stage-side record: no round touched, not terminated. -/
def initial (n : ℕ) : StageSideRec n := StageSideRecP.initial (GBCA.StageRec n)

@[simp] theorem initial_stage (n r : ℕ) :
    (initial n).stage r = GBCA.StageRec.initial n :=
  StageSideRecP.initial_stage r

@[simp] theorem stage_setStage_ne (q : StageSideRec n) (r : ℕ)
    (p : GBCA.StageRec n) {r' : ℕ} (h : r' ≠ r) :
    (q.setStage r p).stage r' = q.stage r' :=
  StageSideRecP.stage_setStage_ne q r p h

end StageSideRec

/-- The state of one process: its round-loop record and its stage-side record
(D22). -/
abbrev ProcRec (n : ℕ) : Type := ProcRecP n (GBCA.StageRec n)

/-! ### The network adversary's state at ABDY22's implementation -/

/-- The state of the network adversary: the round-tagged message pools, the
DECIDED pools, and the corrupted set with its budget. -/
abbrev NetState (n : ℕ) : Type := NetStateP n GBCA.Msg

/-- Pool `⟨DECIDED, b⟩` under sender `j` (D12′). -/
abbrev NetState.dput {n : ℕ} (s : NetState n) (j : Fin n) (b : Bool) : NetState n :=
  NetStateP.dput s j b

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
abbrev NetState.corrupt (P : Params) (id : Fin P.n) (s : NetState P.n) : NetState P.n :=
  NetStateP.corrupt P id s

/-! ### The rows of the graded-agreement implementation -/

/-- The stage-side rows of process `j`: the graded-agreement call, the eight
multicasts of the five message levels, the stage delivery, the call against an
already-called record, and the three graded returns. -/
inductive AbdyStageStep (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLab P.n → PMF (ProcRec P.n) → Prop
  /-- The graded-agreement call: the round loop hands its estimate to the stage
  record of round `r`, which opens. The `⟨INPUT, b⟩` multicast is the network's
  half. -/
  | callG_call (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hest : c.proc.est = some b) (hin : (p.stage r).proc.input = none) :
      AbdyStageStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with
            input := some b,
            sentInput := Function.update (p.stage r).proc.sentInput b true })))
  /-- Return with grade `A v`: an `n − f` `SEAL v` quorum. The stage record has
  been called and its own `SEAL` is out. Case (1) heads the algorithm's chain,
  so there is no higher case to deny. -/
  | retG_A (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (v : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentSeal ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.seal (some v)))
      (hret : (p.stage r).proc.returned = false) :
      AbdyStageStep P j (c, p) (Sum.inl (.retG r j (.A v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with returned := true })))
  /-- Return with grade `B v`: an `n − f` any-`SEAL` quorum containing
  `SEAL v`, `f + 1` `BIND v`s and `|Valid| > 1`. The stage record has been
  called, its own `SEAL` is out, and `hnotA` denies case (1) at either bit. -/
  | retG_B (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (v : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentSeal ≠ none)
      (hnotA : ∀ v, (p.stage r).recvCount (.seal (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).sealCount)
      (honce : ∃ k, GBCA.Msg.seal (some v) ∈ (p.stage r).inbox k)
      (hbind : P.f + 1 ≤ (p.stage r).recvCount (.bind (some v)))
      (hval : (p.stage r).bothValid P)
      (hret : (p.stage r).proc.returned = false) :
      AbdyStageStep P j (c, p) (Sum.inl (.retG r j (.B v)))
        (PMF.pure (c.setProc { c.proc with
            est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with returned := true })))
  /-- Return with grade `C`: an `n − f` `SEAL ⊥` quorum and `|Valid| > 1`. The
  stage record has been called, its own `SEAL` is out, `hnotA` denies case (1)
  at either bit, and `hnotB` denies case (2) in the reduced form
  `GBCA.ImplStep.retC` states. -/
  | retG_C (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentSeal ≠ none)
      (hnotA : ∀ v, (p.stage r).recvCount (.seal (some v)) < P.n - P.f)
      (hnotB : ∀ v, (∃ k, GBCA.Msg.seal (some v) ∈ (p.stage r).inbox k) →
        (p.stage r).recvCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.seal none))
      (hval : (p.stage r).bothValid P)
      (hret : (p.stage r).proc.returned = false) :
      AbdyStageStep P j (c, p) (Sum.inl (.retG r j .C))
        (PMF.pure (c.setProc { c.proc with
            est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
          p.setStage r ((p.stage r).setP { (p.stage r).proc with returned := true })))
  /-- The stage `INPUT` relay: `f + 1` receipts of `⟨INPUT, b⟩` in the stage
  record of round `r`, not yet multicast there (D8, D18, D22). -/
  | gsndRelay (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hcnt : P.f + 1 ≤ (p.stage r).recvCount (.input b))
      (hsend : (p.stage r).proc.sentInput b = false) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.input b)))
        (PMF.pure (c, p.setStage r ((p.stage r).setP { (p.stage r).proc with
          sentInput := Function.update (p.stage r).proc.sentInput b true })))
  /-- The stage `ECHO`: an `n − f` `INPUT b` quorum (D18, D22). -/
  | gsndEcho (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.input b))
      (hsend : (p.stage r).proc.sentEcho = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.echo b)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentEcho := some b })))
  /-- The stage `VOTE b`: an `n − f` `ECHO b` quorum. The stage record's own
  `ECHO` is sent by one of the algorithm's `upon` handlers and may still be
  pending, so no own-send condition applies here (D18, D22). -/
  | gsndVoteBit (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.echo b))
      (hsend : (p.stage r).proc.sentVote = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.vote (some b))))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentVote := some (some b) })))
  /-- The stage `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`, and
  no single-bit `ECHO` quorum on record. The stage record's own `ECHO` is sent
  by one of the algorithm's `upon` handlers and may still be pending, so no
  own-send condition applies here (D18, D22). -/
  | gsndVoteBot (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hnot : ∀ b, (p.stage r).recvCount (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).echoCount)
      (hval : (p.stage r).bothValid P) (hsend : (p.stage r).proc.sentVote = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.vote none)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentVote := some none })))
  /-- The stage `BIND b`: an `n − f` `VOTE b` quorum, the stage record's own
  `VOTE` already out (D18, D22). -/
  | gsndBindBit (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentVote ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.vote (some b)))
      (hsend : (p.stage r).proc.sentBind = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.bind (some b))))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentBind := some (some b) })))
  /-- The stage `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`, the
  stage record's own `VOTE` already out, and no single-bit `VOTE` quorum on
  record (D18, D22). -/
  | gsndBindBot (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentVote ≠ none)
      (hnot : ∀ b, (p.stage r).recvCount (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).voteCount)
      (hval : (p.stage r).bothValid P) (hsend : (p.stage r).proc.sentBind = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.bind none)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentBind := some none })))
  /-- The stage `SEAL b`: an `n − f` `BIND b` quorum, the stage record's own
  `BIND` already out (D18, D22). -/
  | gsndSealBit (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentBind ≠ none)
      (hcnt : P.n - P.f ≤ (p.stage r).recvCount (.bind (some b)))
      (hsend : (p.stage r).proc.sentSeal = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.seal (some b))))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentSeal := some (some b) })))
  /-- The stage `SEAL ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`, the
  stage record's own `BIND` already out, and no single-bit `BIND` quorum on
  record (D18, D22). -/
  | gsndSealBot (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.stage r).proc.input ≠ none)
      (hlv : (p.stage r).proc.sentBind ≠ none)
      (hnot : ∀ b, (p.stage r).recvCount (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.stage r).bindCount)
      (hval : (p.stage r).bothValid P) (hsend : (p.stage r).proc.sentSeal = none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gsnd r j (.seal none)))
        (PMF.pure (c, p.setStage r
          ((p.stage r).setP { (p.stage r).proc with sentSeal := some none })))
  /-- Stage delivery, receiver's half: file the message under the sender's
  inbox row in the stage record of round `r`, whichever round the round loop is
  in. Authenticity is the network's conjunct (D22). -/
  | gdlvRecv (c : CoreRec P.n) (p : StageSideRec P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (hh : c.corrupted = false)
      (hterm : p.terminated = false) :
      AbdyStageStep P j (c, p) (Sum.inr (.gdlv r j k m))
        (PMF.pure (c, p.deliverTo r k m))
  /-- The graded-agreement call against an already-called stage record: the
  round loop moves, the stage record does not. The row carries no termination
  guard, so a terminated process in `toCallG` whose stage record of round `r`
  is uncalled has no row on either call label, a dead region this reading
  accepts. -/
  | gcallLoop (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b)
      (hin : (p.stage r).proc.input ≠ none) :
      AbdyStageStep P j (c, p) (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, p))

/-- The rows above meet the flat reading's conditions: each carries a label of
`stageOwn j`, each fires only at an unreplaced program, and each is Dirac. -/
instance instIsStageTable (P : Params) :
    IsStageTable P GBCA.Msg (GBCA.StageRec P.n) (AbdyStageStep P) where
  own h := by cases h <;> rfl
  honest h := by cases h <;> assumption
  dirac h := by cases h <;> exact ⟨_, rfl⟩

/-! ### The tables, the automata and the pipeline -/

/-- The step relation of the program of process `j`: the flat reading's rows
beside ABDY22's own stage-side rows. -/
abbrev ABAProcStepN (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLab P.n → PMF (ProcRec P.n) → Prop :=
  FlatProcStep P GBCA.Msg (GBCA.StageRec P.n) (AbdyStageStep P) j

/-- The message the graded-agreement call multicasts: `⟨INPUT, b⟩`. -/
def gCallPayload (P : Params) : Fin P.n → Bool → GBCA.Msg := fun _ b => .input b

/-- The step relation of the network adversary. -/
abbrev NetStep (P : Params) : NetState P.n → NLab P.n → PMF (NetState P.n) → Prop :=
  FlatNetStep P GBCA.Msg (gCallPayload P)

/-- The program of process `j`. -/
noncomputable abbrev ABAProcN (P : Params) (j : Fin P.n) :
    System (ProcRec P.n) (NLab P.n) :=
  flatProcN P GBCA.Msg (GBCA.StageRec P.n) (AbdyStageStep P) j

/-- The network adversary. -/
noncomputable abbrev netAdv (P : Params) : System (NetState P.n) (NLab P.n) :=
  flatNetAdv P GBCA.Msg (gCallPayload P)

end Net

namespace ABDY

/-- The state of the protocol: the process family, the network adversary and
the coin oracle. -/
abbrev ProtocolState (P : Params) : Type :=
  Net.FlatState P GBCA.Msg (GBCA.StageRec P.n)

/-- The three components side by side, over the extended alphabet: the
synchronised process group, the network adversary and the lifted oracle. -/
noncomputable def protocolPre (P : Params) : System (ProtocolState P) (Net.NLab P.n) :=
  Net.flatPre P GBCA.Msg (GBCA.StageRec P.n) (Net.AbdyStageStep P) (Net.gCallPayload P)

/-- **The protocol group**: the rendezvous alphabet hidden, the result read
back over `Lab n`. -/
noncomputable def protocolGroup (P : Params) : System (ProtocolState P) (Lab P.n) :=
  Net.flatGroup P GBCA.Msg (GBCA.StageRec P.n) (Net.AbdyStageStep P) (Net.gCallPayload P)

/-- **The protocol system**: the group with the sub-protocol API hidden. -/
noncomputable def protocol (P : Params) : System (ProtocolState P) (Lab P.n) :=
  Net.flat P GBCA.Msg (GBCA.StageRec P.n) (Net.AbdyStageStep P) (Net.gCallPayload P)

end ABDY

namespace Net

/-! ### Reading composite transitions

The flat reading's own lemmas, named at this instantiation. -/

theorem protocolGroup_step_iff (P : Params) (q : ABDY.ProtocolState P) (l : Lab P.n)
    (μ : PMF (ABDY.ProtocolState P)) :
    (ABDY.protocolGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (ABDY.protocolPre P).step q (Sum.inr e) μ) ∨
      (ABDY.protocolPre P).step q (Sum.inl l) μ :=
  flatGroup_step_iff q l μ

theorem protocol_step_iff (P : Params) (q : ABDY.ProtocolState P) (l : Lab P.n)
    (μ : PMF (ABDY.ProtocolState P)) :
    (ABDY.protocol P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Lab.hiddenAPI P.n, (ABDY.protocolGroup P).step q l' μ) ∨
      (l ∉ Lab.hiddenAPI P.n ∧ (ABDY.protocolGroup P).step q l μ) :=
  flat_step_iff q l μ

/-- A rendezvous transition: every process, the network and the lifted oracle
move together, and only the oracle's successor can fail to be a Dirac. -/
theorem protocolPre_event_inv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {e : NetEvt P.n}
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolPre P).step (u, w, o) (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRec P.n) (w' : NetState P.n)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inr e) (PMF.pure w') ∧
      (wccLift P).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) :=
  flatPre_event_inv h

/-- A visible shared-label transition. -/
theorem protocolPre_lab_inv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n} {l : Lab P.n} (hl : l ≠ Lab.tau)
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolPre P).step (u, w, o) (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRec P.n) (w' : NetState P.n)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProcStepN P i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetStep P w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) :=
  flatPre_lab_inv hl h

/-- A silent shared-label transition: one process terminating, the network's own
injection, or the coin resolution. -/
theorem protocolPre_tau_inv (P : Params) {u : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolPre P).step (u, w, o) (Sum.inl Lab.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcRec P.n),
      ABAProcStepN P i (u i) (Sum.inl Lab.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetStep P w (Sum.inl .tau) (PMF.pure w') ∧ μ = PMF.pure (u, w', o)) ∨
    (∃ ω, (WCC.specFamily P).step o Lab.tau ω ∧
      μ = prodPMF (PMF.pure u) (prodPMF (PMF.pure w) ω)) :=
  flatPre_tau_inv h

/-! ### ABDY22's own rows, by label class

Each lemma reads a stage-side row off its label: the participant's row as its
guards together with the Dirac it produces. The idle row of a non-participant
and the replaced program's self-loop are read by the flat reading's own lemmas;
here the label names the acting process, so those two readings are the ones
ruled out. -/

section StageInversion

variable {P : Params} {j : Fin P.n} {q : ProcRec P.n} {ν : PMF (ProcRec P.n)}

theorem stepN_callG_own {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.callG r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      q.1.proc.est = some b ∧ (q.2.stage r).proc.input = none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG },
        q.2.setStage r ((q.2.stage r).setP { (q.2.stage r).proc with
          input := some b,
          sentInput := Function.update (q.2.stage r).proc.sentInput b true })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retG_A_own {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j (.A v))) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      (q.2.stage r).proc.input ≠ none ∧ (q.2.stage r).proc.sentSeal ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.seal (some v)) ∧
      (q.2.stage r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := (GbcaOut.A v).est, lastGrade := some (.A v), phase := .toCallW },
        q.2.setStage r
          ((q.2.stage r).setP { (q.2.stage r).proc with returned := true })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retG_B_own {r : ℕ} {v : Bool}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j (.B v))) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      (q.2.stage r).proc.input ≠ none ∧ (q.2.stage r).proc.sentSeal ≠ none ∧
      (∀ v, (q.2.stage r).recvCount (.seal (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).sealCount ∧
      (∃ k, GBCA.Msg.seal (some v) ∈ (q.2.stage r).inbox k) ∧
      P.f + 1 ≤ (q.2.stage r).recvCount (.bind (some v)) ∧
      (q.2.stage r).bothValid P ∧
      (q.2.stage r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := (GbcaOut.B v).est, lastGrade := some (.B v), phase := .toCallW },
        q.2.setStage r
          ((q.2.stage r).setP { (q.2.stage r).proc with returned := true })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_retG_C_own {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inl (.retG r j .C)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .awaitG ∧ q.1.proc.round = r ∧ q.2.terminated = false ∧
      (q.2.stage r).proc.input ≠ none ∧ (q.2.stage r).proc.sentSeal ≠ none ∧
      (∀ v, (q.2.stage r).recvCount (.seal (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.Msg.seal (some v) ∈ (q.2.stage r).inbox k) →
        (q.2.stage r).recvCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.seal none) ∧
      (q.2.stage r).bothValid P ∧
      (q.2.stage r).proc.returned = false ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with
          est := GbcaOut.C.est, lastGrade := some .C, phase := .toCallW },
        q.2.setStage r
          ((q.2.stage r).setP { (q.2.stage r).proc with returned := true })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_input_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.input b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      P.f + 1 ≤ (q.2.stage r).recvCount (.input b) ∧
      (q.2.stage r).proc.sentInput b = false ∧
      ν = PMF.pure (q.1, q.2.setStage r ((q.2.stage r).setP { (q.2.stage r).proc with
        sentInput := Function.update (q.2.stage r).proc.sentInput b true })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_echo_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.echo b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.input b) ∧
      (q.2.stage r).proc.sentEcho = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentEcho := some b })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_voteBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.vote (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.echo b) ∧
      (q.2.stage r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentVote := some (some b) })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_voteBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.vote none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (∀ b, (q.2.stage r).recvCount (.echo b) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).echoCount ∧
      (q.2.stage r).bothValid P ∧ (q.2.stage r).proc.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentVote := some none })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_bindBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.bind (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentVote ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.vote (some b)) ∧
      (q.2.stage r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentBind := some (some b) })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_bindBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.bind none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentVote ≠ none ∧
      (∀ b, (q.2.stage r).recvCount (.vote (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).voteCount ∧
      (q.2.stage r).bothValid P ∧ (q.2.stage r).proc.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentBind := some none })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_sealBit_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.seal (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentBind ≠ none ∧
      P.n - P.f ≤ (q.2.stage r).recvCount (.bind (some b)) ∧
      (q.2.stage r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentSeal := some (some b) })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gsnd_sealBot_self {r : ℕ}
    (h : ABAProcStepN P j q (Sum.inr (.gsnd r j (.seal none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.stage r).proc.input ≠ none ∧
      (q.2.stage r).proc.sentBind ≠ none ∧
      (∀ b, (q.2.stage r).recvCount (.bind (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.stage r).bindCount ∧
      (q.2.stage r).bothValid P ∧ (q.2.stage r).proc.sentSeal = none ∧
      ν = PMF.pure (q.1, q.2.setStage r
        ((q.2.stage r).setP { (q.2.stage r).proc with sentSeal := some none })) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gdlv_self {r : ℕ} {k : Fin P.n} {m : GBCA.Msg}
    (h : ABAProcStepN P j q (Sum.inr (.gdlv r j k m)) ν) :
    q.1.corrupted = false ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, q.2.deliverTo r k m) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, rfl⟩
  case gdlvIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepN_gcallLoop_self {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.gcallLoop r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.proc.phase = .toCallG ∧ q.1.proc.round = r ∧ q.1.proc.est = some b ∧
      (q.2.stage r).proc.input ≠ none ∧
      ν = PMF.pure (q.1.setProc { q.1.proc with phase := .awaitG }, q.2) := by
  cases h
  case stageRow h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gcallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

end StageInversion

end Net

end ABA
end PLTS
