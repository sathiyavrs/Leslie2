/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.RoundLoop
import Leslie2Protocols.ABA.Reading.Alphabet
import Leslie2Protocols.ABA.ABDY.Impl
import Leslie2Protocols.ABA.Spec.ABASafety
import Leslie2Protocols.ABA.Spec.WCC
import Leslie2Protocols.Framework.IdleFamily
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SyncProduct

/-!
# The extended alphabet and the components composed over it

The protocol is composed twice in this development. The protocol reading
(`ABA/ABDY/Protocol.lean`) puts `n` per-process programs beside a network
adversary and the coin oracle. The composed reading (`ABA/ABDY/Hybrid.lean`) cuts
the same protocol into its components. Both compositions speak one
alphabet, and some of what they compose is the same object on both sides.
This file holds that alphabet and those components.

## The extended alphabet

`Lab n` is the shared alphabet of the protocol and of its specification. It
cannot name the two message networks, the Byzantine handshake rows, or the branches of
a handshake that it does not distinguish. The rendezvous alphabet
`NetEvtP n M` names them, over a graded-agreement message type `M`
(`ABA/Reading/Alphabet.lean`); `NetEvt n` is that alphabet at the stage messages of
`ABA/ABDY/Impl.lean`, and `NLab n = Lab n ⊕ NetEvt n` is the alphabet every
component here speaks. Its silent label is `Sum.inl τ`, so every `Sum.inr`
label is observable, and `netEvtLabels n` — the set of all of them — is what
both compositions hide before reading the result back over `Lab n`.

## The coin oracle

The coin oracle `WCC.specFamily` speaks `Lab n`, so it is joined to the
extended alphabet through the label pullback `wccPull`, which sends a shared
label to itself, the Byzantine handshake rows and the fused coin return to
the oracle's own handshake rows, and every other rendezvous label out of the
domain. `wccLift` is the oracle read along that pullback at this alphabet. It
is a component of both compositions, unchanged.

## The round loop of one process

`CoreProcStepN` is the rule table of one process's round loop: the API rows
`callABA` and `retABA`, the graded-agreement and coin handshakes, the DECIDED
relay and its delivery, and an idle row for every label the process does not
act on. It writes no stage record. The composed system runs `n` of these
automata (`coreProcN`) under a full-synchronisation product. The protocol
composition fuses each round loop with the stage-side record into one program
(`Net.ABAProcStepN`), whose record is the pair.

A corruption replaces the program of the process it names (D23). The flag
`CoreRec.corrupted` goes up on the process's own half of `fail`, every
participant's row is guarded by `corrupted = false`, and the replaced program
is the single self-loop `corruptedIdle`. The replaced program has no row on the
labels of `actsAt j` — the labels on which the process would act on its own
sub-protocol messages — so those messages enter only through the Byzantine handshake rows
(D11).

## The ABA-side network

`ANetStep` is what the network adversary retains once the round message states have
taken the stage sent sets: the DECIDED sets `dsent j`, the corrupted set `F` with
its budget, and the authorisation of every Byzantine handshake row. `aNet` is that
automaton. Its `fail` row carries the budget guard `k ∉ F ∧ |F| < f`, so a
corruption fires exactly when it takes effect, and its `retByz` row lets a
corrupted process return without DECIDED evidence, pairing with the replaced
program's self-loop on `retABA` (D23). It holds no ghost record: the bound bit
a graded-agreement return announces belongs to the round, so the round's
instance carries it and both rows here idle on it.

## What this file supplies

The two rule tables above, the two automata they carry, the determinacy of
both tables, and the inversion tables that read a row of each off its label
(`stepC_*`, `aStep_*`) — among them `stepC_inert`, which reads every row of a
replaced program as a self-loop. It also supplies the readings of the
synchronised round-loop group in both directions (`syncCore_inv`,
`syncCore_pure`) and the lemmas that pin a round-loop tuple down from its
per-process rows (`coresN_*`).
-/

namespace PLTS
namespace ABA

namespace Net

/-! ### The auxiliary alphabet

The rendezvous alphabet, the hidden-label set, the labels a process acts on,
the coin oracle's label pullback and the lifted oracle are parametric in the
graded-agreement message type (`ABA/Reading/Alphabet.lean`). This reading fixes that
type to the stage messages of `ABA/ABDY/Impl.lean`. -/

/-- The rendezvous alphabet at the stage messages of `ABA/ABDY/Impl.lean`. -/
abbrev NetEvt (n : ℕ) : Type := NetEvtP n GBCA.Msg

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev NLab (n : ℕ) : Type := Lab n ⊕ NetEvt n

/-- The coin oracle, read over this alphabet through the pullback. -/
noncomputable def wccLift (P : Params) : System (ℕ → WCC.SpecState P.n) (NLab P.n) :=
  wccLiftP P GBCA.Msg

@[simp] theorem wccLift_init (P : Params) :
    (wccLift P).init = (WCC.specFamily P).init := rfl

end Net

open Net

/-! ## The `Comp` namespace

Everything the component boundary names lives under `PLTS.ABA.Comp`, so that
`PLTS.ABA` itself carries only what the chain cites. `Net` is the protocol's
own namespace; `Comp` is the components'. -/

namespace Comp

/-! ### The round-loop program of one process

The automaton that calls a round's graded-agreement instance and the coin, and
decides. It writes no stage record: the five multicast levels and the stage
delivery are internal to a round instance, so they leave no row here, and the
three Byzantine graded-agreement rows change no round-loop data, which is
why they appear below only as idle rows.

The programs sit under a full-synchronisation product, so every label that can
fire in the composite has a row: the participant's, or an idle one. Unlike the
round-indexed families, these programs are not round-filtered. A round loop
must answer every round's `callG`, its own as a participant and every other
process's as a bystander.

A corruption replaces the program of the process it names (D23). The
replacement is carried by the flag `CoreRec.corrupted`, which `failSelf` writes
on the process's own `fail`; every participant's row is guarded by
`corrupted = false`, so the record freezes at the corruption. In place of those
rows the replaced program has the single row `corruptedIdle`: a self-loop on
every label other than `τ` and the labels of `actsAt j`. On the latter the
replaced program has no row at all, so those labels cannot fire; the corrupted
process's graded-agreement messages enters through the Byzantine handshake rows (D11)
and its DECIDED messages through `byzD`. -/

/-- The step relation of the round-loop program of process `j`. -/
inductive CoreProcStepN (P : Params) (j : Fin P.n) :
    CoreRec P.n → NLab P.n → PMF (CoreRec P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : CoreRec P.n) (b : Bool) (hh : c.corrupted = false)
      (h : c.proc.input = none) :
      CoreProcStepN P j c (Sum.inl (.callABA j b))
        (PMF.pure (c.setProc { c.proc with
          input := some b, est := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop on `j`'s own `callABA`. -/
  | inputLoop (c : CoreRec P.n) (b : Bool) (hh : c.corrupted = false) :
      CoreProcStepN P j c (Sum.inl (.callABA j b)) (PMF.pure c)
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : CoreRec P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.callABA id b)) (PMF.pure c)
  /-- Return `b` on an `n − f` DECIDED quorum. Having multicast `b` oneself is
  a condition on the DECIDED sets, hence `aNet`'s conjunct. -/
  | ret (c : CoreRec P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.proc.returned = false) :
      CoreProcStepN P j c (Sum.inl (.retABA j b))
        (PMF.pure (c.setProc { c.proc with returned := true }))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : CoreRec P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.retABA id b)) (PMF.pure c)
  /-- The graded-agreement call, round-loop half: hand the estimate over and
  wait. Opening the stage record is the round instance's half. -/
  | callG (c : CoreRec P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b) :
      CoreProcStepN P j c (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : CoreRec P.n) (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.callG r id b)) (PMF.pure c)
  /-- The graded-agreement return, round-loop half: record the grade and head
  for the coin. The evidence for the grade is the round instance's conjunct.
  The round's bound bit is announced beside the grade and written nowhere: the
  round loop is one of the programs that do not read it. -/
  | retG (c : CoreRec P.n) (r : ℕ) (out : GbcaOut) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r) :
      CoreProcStepN P j c (Sum.inl (.retG r j out bnd))
        (PMF.pure (c.setProc { c.proc with
          est := out.est, lastGrade := some out, phase := .toCallW }))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : CoreRec P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut) (bnd : Bool)
      (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.retG r id out bnd)) (PMF.pure c)
  /-- `c ← WCC_r()`, the call half. -/
  | callW (c : CoreRec P.n) (r : ℕ) (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallW) (hr : c.proc.round = r) :
      CoreProcStepN P j c (Sum.inl (.callW r j))
        (PMF.pure (c.setProc { c.proc with phase := .awaitW }))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : CoreRec P.n) (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.callW r id)) (PMF.pure c)
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being an `A` (D10). -/
  | retW (c : CoreRec P.n) (r : ℕ) (co : Bool) (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : ∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) :
      CoreProcStepN P j c (Sum.inl (.retW r j co)) (PMF.pure (c.stepRound co))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : CoreRec P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inl (.retW r id co)) (PMF.pure c)
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the row (D23). -/
  | failSelf (c : CoreRec P.n) (hh : c.corrupted = false) :
      CoreProcStepN P j c (Sum.inl (.fail j))
        (PMF.pure { c with corrupted := true })
  /-- Another process's corruption is not the round loop's business (D1). -/
  | failIdle (c : CoreRec P.n) (k : Fin P.n) (hk : k ≠ j) :
      CoreProcStepN P j c (Sum.inl (.fail k)) (PMF.pure c)
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `actsAt j`, on which the process has no row at all. -/
  | corruptedIdle (c : CoreRec P.n) (L : NLab P.n) (hh : c.corrupted = true)
      (hτ : L ≠ Sum.inl Lab.tau) (hown : ¬ actsAt j L) :
      CoreProcStepN P j c L (PMF.pure c)
  /-- The DECIDED relay on an `f + 1` quorum (D12′): the quorum is a condition
  on the record, the write-once condition and the sent insert are `aNet`'s. -/
  | dsndRelay (c : CoreRec P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      CoreProcStepN P j c (Sum.inr (.dsnd j b)) (PMF.pure c)
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | dsndIdle (c : CoreRec P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      CoreProcStepN P j c (Sum.inr (.dsnd k b)) (PMF.pure c)
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is `aNet`'s conjunct. -/
  | ddlvRecv (c : CoreRec P.n) (k : Fin P.n) (b : Bool) (hh : c.corrupted = false)
      (hr : b ∉ c.decIn k) :
      CoreProcStepN P j c (Sum.inr (.ddlv j k b)) (PMF.pure (c.recvDec k b))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | ddlvIdle (c : CoreRec P.n) (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      CoreProcStepN P j c (Sum.inr (.ddlv i k b)) (PMF.pure c)
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's grade was `A b`, so the round advance publishes `b`, the sent insert
  being `aNet`'s half. -/
  | retWPub (c : CoreRec P.n) (r : ℕ) (co : Bool) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitW) (hr : c.proc.round = r)
      (hgr : c.proc.lastGrade = some (.A b)) :
      CoreProcStepN P j c (Sum.inr (.retWPub r j co b)) (PMF.pure (c.stepRound co))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPubIdle (c : CoreRec P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool)
      (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inr (.retWPub r id co b)) (PMF.pure c)
  /-- The graded-agreement call against an already-called stage record: the
  round loop moves and nothing else does — the whole row is core content. -/
  | gcallLoop (c : CoreRec P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b) :
      CoreProcStepN P j c (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }))
  /-- Such a call at another process: not `j`'s business. -/
  | gcallLoopIdle (c : CoreRec P.n) (r : ℕ) (id : Fin P.n) (b : Bool)
      (hid : id ≠ j) :
      CoreProcStepN P j c (Sum.inr (.gcallLoop r id b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call (D11) writes a stage record and no
  round-loop data: every round loop, the named one included, stands still. -/
  | byzCallGIdle (c : CoreRec P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzCallG r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call against an already-called stage record
  (D11): nothing moves anywhere. -/
  | byzCallGLoopIdle (c : CoreRec P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzCallGLoop r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement return (D11): stage content only. -/
  | byzRetGIdle (c : CoreRec P.n) (r : ℕ) (k : Fin P.n) (out : GbcaOut)
      (bnd : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzRetG r k out bnd)) (PMF.pure c)
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback. -/
  | byzCallWIdle (c : CoreRec P.n) (r : ℕ) (k : Fin P.n) :
      CoreProcStepN P j c (Sum.inr (.byzCallW r k)) (PMF.pure c)
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback. -/
  | byzRetWIdle (c : CoreRec P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      CoreProcStepN P j c (Sum.inr (.byzRetW r k b)) (PMF.pure c)

/-! ### The DECIDED sets and the corrupted set

What is left of the network adversary once the round-tagged sent sets have gone to
the round message states: the DECIDED sets, the corrupted set with its budget, and
the authorisation of every Byzantine handshake row. -/

/-- The state of the ABA-side network: the DECIDED sets and the corrupted
set. -/
structure ANetState (n : ℕ) : Type where
  /-- `dsent j` — the DECIDED payloads process `j` has multicast (D12′). -/
  dsent : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)

namespace ANetState

variable {n : ℕ}

/-- The initial network: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) : ANetState n where
  dsent := fun _ => ∅
  F := ∅

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def dput (a : ANetState n) (j : Fin n) (b : Bool) : ANetState n :=
  { a with dsent := Function.update a.dsent j (insert b (a.dsent j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Params) (id : Fin P.n) (a : ANetState P.n) : ANetState P.n :=
  if id ∉ a.F ∧ a.F.card < P.f then { a with F := insert id a.F } else a

@[simp] theorem dput_dsent (a : ANetState n) (j : Fin n) (b : Bool) :
    (a.dput j b).dsent = Function.update a.dsent j (insert b (a.dsent j)) := rfl

@[simp] theorem dput_F (a : ANetState n) (j : Fin n) (b : Bool) :
    (a.dput j b).F = a.F := rfl

end ANetState

/-- The step relation of the ABA-side network. All transitions are Dirac. -/
inductive ANetStep (P : Params) :
    ANetState P.n → NLab P.n → PMF (ANetState P.n) → Prop
  /-- The DECIDED relay's half: the payload must not be sent yet (D12′). -/
  | dsnd (a : ANetState P.n) (j : Fin P.n) (b : Bool) (h : b ∉ a.dsent j) :
      ANetStep P a (Sum.inr (.dsnd j b)) (PMF.pure (a.dput j b))
  /-- The DECIDED delivery's half: the payload must be sent under the named
  sender (D12′). -/
  | ddlv (a : ANetState P.n) (i j : Fin P.n) (b : Bool) (h : b ∈ a.dsent j) :
      ANetStep P a (Sum.inr (.ddlv i j b)) (PMF.pure a)
  /-- The fused coin return's half: sent the published payload (D10, D12′). -/
  | retWPub (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      ANetStep P a (Sum.inr (.retWPub r id c b)) (PMF.pure (a.dput id b))
  /-- A graded-agreement call against an already-called stage record publishes
  nothing here. -/
  | gcallLoop (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ANetStep P a (Sum.inr (.gcallLoop r id b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement call (D11): the round
  instance carries the effect, this component carries the guard. -/
  | byzCallG (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzCallG r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine call against an already-called stage
  record (D11). -/
  | byzCallGLoop (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzCallGLoop r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement return (D11). -/
  | byzRetG (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (out : GbcaOut) (bnd : Bool)
      (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzRetG r k out bnd)) (PMF.pure a)
  /-- The authorisation of a Byzantine coin call (D11). -/
  | byzCallW (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzCallW r k)) (PMF.pure a)
  /-- The authorisation of a Byzantine coin return (D11). -/
  | byzRetW (a : ANetState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inr (.byzRetW r k b)) (PMF.pure a)
  /-- An external input is not this component's business. -/
  | callABAIdle (a : ANetState P.n) (id : Fin P.n) (b : Bool) :
      ANetStep P a (Sum.inl (.callABA id b)) (PMF.pure a)
  /-- A return requires the returning process to have multicast the payload —
  a condition on its DECIDED sent (D12′). -/
  | retABA (a : ANetState P.n) (id : Fin P.n) (b : Bool) (h : b ∈ a.dsent id) :
      ANetStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- A corrupted process returns whatever it likes (D23): its program has been
  replaced, so the DECIDED evidence the honest row asks for is not required of
  it. The authorisation is this component's `id ∈ F`, and the round loop's half
  is the replaced program's self-loop. -/
  | retByz (a : ANetState P.n) (id : Fin P.n) (b : Bool) (hF : id ∈ a.F) :
      ANetStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- The graded-agreement call's `⟨INPUT, b⟩` is sent in the round's message state,
  not here. -/
  | callGIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ANetStep P a (Sum.inl (.callG r id b)) (PMF.pure a)
  /-- A graded-agreement return publishes nothing here, and the bound bit it
  announces is the round instance's: this component holds no ghost. -/
  | retGIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (out : GbcaOut)
      (bnd : Bool) :
      ANetStep P a (Sum.inl (.retG r id out bnd)) (PMF.pure a)
  /-- A coin call publishes nothing. -/
  | callWIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) :
      ANetStep P a (Sum.inl (.callW r id)) (PMF.pure a)
  /-- An unfused coin return publishes nothing. -/
  | retWIdle (a : ANetState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) :
      ANetStep P a (Sum.inl (.retW r id c)) (PMF.pure a)
  /-- Corruption (deviations D1, D23): Dirac, and guarded by the budget. The
  guard sits on the row rather than inside `ANetState.corrupt` alone, so that a
  corruption fires exactly when it takes effect and the round loop's half may
  write the replacement flag outright. -/
  | fail (a : ANetState P.n) (k : Fin P.n) (hnew : k ∉ a.F) (hbud : a.F.card < P.f) :
      ANetStep P a (Sum.inl (.fail k)) (PMF.pure (ANetState.corrupt P k a))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate in the DECIDED sets. -/
  | byzD (a : ANetState P.n) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ANetStep P a (Sum.inl .tau) (PMF.pure (a.dput k b))

/-! ### The two automata -/

/-- The round-loop program of process `j`. -/
noncomputable def coreProcN (P : Params) (j : Fin P.n) :
    System (CoreRec P.n) (NLab P.n) where
  init := CoreRec.initial P.n
  step := CoreProcStepN P j

@[simp] theorem coreProcN_init (P : Params) (j : Fin P.n) :
    (coreProcN P j).init = CoreRec.initial P.n := rfl

@[simp] theorem coreProcN_step (P : Params) (j : Fin P.n) (c : CoreRec P.n)
    (l : NLab P.n) (ν : PMF (CoreRec P.n)) :
    (coreProcN P j).step c l ν ↔ CoreProcStepN P j c l ν := Iff.rfl

/-- The ABA-side network. -/
noncomputable def aNet (P : Params) : System (ANetState P.n) (NLab P.n) where
  init := ANetState.initial P.n
  step := ANetStep P

@[simp] theorem aNet_init (P : Params) : (aNet P).init = ANetState.initial P.n := rfl

@[simp] theorem aNet_step (P : Params) (a : ANetState P.n) (l : NLab P.n)
    (μ : PMF (ANetState P.n)) : (aNet P).step a l μ ↔ ANetStep P a l μ := Iff.rfl

/-! ### Determinacy of the two rule tables -/

/-- Every round-loop transition is Dirac. -/
theorem coreProcStepN_dirac {P : Params} {j : Fin P.n} {c : CoreRec P.n}
    {l : NLab P.n} {ν : PMF (CoreRec P.n)} (h : CoreProcStepN P j c l ν) :
    ∃ c', ν = PMF.pure c' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every ABA-side network transition is Dirac. -/
theorem aNetStep_dirac {P : Params} {a : ANetState P.n} {l : NLab P.n}
    {μ : PMF (ANetState P.n)} (h : ANetStep P a l μ) : ∃ a', μ = PMF.pure a' := by
  cases h <;> exact ⟨_, rfl⟩

/-- No round-loop rule fires on `τ`: a round loop only ever moves in a
rendezvous or on a shared API label. -/
theorem coreProcStepN_no_tau {P : Params} {j : Fin P.n} {c : CoreRec P.n}
    {ν : PMF (CoreRec P.n)} (h : CoreProcStepN P j c (Silent.τ : NLab P.n) ν) :
    False := by
  rw [nlab_tau] at h
  cases h
  rename_i hτ _
  exact hτ rfl

/-! ### Reading and building a transition of the round-loop group -/

/-- A synchronised transition of the round-loop group on a visible label. -/
theorem syncCore_inv {P : Params} {C : ∀ _ : Fin P.n, CoreRec P.n} {l : NLab P.n}
    {μ : PMF (∀ _ : Fin P.n, CoreRec P.n)}
    (h : (System.syncProduct (coreProcN P)).step C l μ) :
    ∃ y : ∀ _ : Fin P.n, CoreRec P.n,
      μ = PMF.pure y ∧ ∀ i, CoreProcStepN P i (C i) l (PMF.pure (y i)) := by
  rw [System.syncProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hy : ∀ i, ∃ c', μ_ i = PMF.pure c' := fun i => coreProcStepN_dirac (hall i)
    choose y hy using hy
    refine ⟨y, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (y i) from funext hy]
      exact piPMF_pure y
    · rw [← hy i]; exact hall i
  · exact absurd hstep coreProcStepN_no_tau

/-- Build a synchronised transition of the round-loop group from per-process
Dirac steps. -/
theorem syncCore_pure {P : Params} {C y : ∀ _ : Fin P.n, CoreRec P.n}
    {l : NLab P.n} (hl : l ≠ Silent.τ)
    (h : ∀ i, CoreProcStepN P i (C i) l (PMF.pure (y i))) :
    (System.syncProduct (coreProcN P)).step C l (PMF.pure y) := by
  rw [System.syncProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (y i), h, (piPMF_pure y).symm⟩

/-- The round-loop group has no silent transition. -/
theorem syncCore_no_tau {P : Params} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {μ : PMF (∀ _ : Fin P.n, CoreRec P.n)}
    (h : (System.syncProduct (coreProcN P)).step C (Silent.τ : NLab P.n) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact coreProcStepN_no_tau hstep

/-! ### One round loop's rules, by label class

Each lemma reads a row of `CoreProcStepN` off its label: the participant's row
as its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. A participant's row carries the health guard
`corrupted = false`, and on a label outside `actsAt j` the replaced program's
self-loop is a second reading of the same label (D23). -/

section CoreInversion

variable {P : Params} {j : Fin P.n} {c : CoreRec P.n} {ν : PMF (CoreRec P.n)}

theorem stepC_callABA_own {b : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.callABA j b)) ν) :
    (c.corrupted = false ∧ c.proc.input = none ∧
      ν = PMF.pure (c.setProc { c.proc with
        input := some b, est := some b, round := 0, phase := .toCallG })) ∨
    ν = PMF.pure c := by
  cases h
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr rfl
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr rfl

theorem stepC_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.callABA id b)) ν) : ν = PMF.pure c := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem stepC_retABA_own {b : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.retABA j b)) ν) :
    (c.corrupted = false ∧ P.n - P.f ≤ c.decidedCount b ∧
      c.proc.returned = false ∧
      ν = PMF.pure (c.setProc { c.proc with returned := true })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case ret => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepC_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.retABA id b)) ν) : ν = PMF.pure c := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem stepC_callG_own {r : ℕ} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.callG r j b)) ν) :
    c.corrupted = false ∧ c.proc.phase = .toCallG ∧ c.proc.round = r ∧
      c.proc.est = some b ∧
      ν = PMF.pure (c.setProc { c.proc with phase := .awaitG }) := by
  cases h
  case callG =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepC_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.callG r id b)) ν) : ν = PMF.pure c := by
  cases h
  case callG => exact absurd rfl hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem stepC_retG_own {r : ℕ} {out : GbcaOut} {bnd : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.retG r j out bnd)) ν) :
    c.corrupted = false ∧ c.proc.phase = .awaitG ∧ c.proc.round = r ∧
      ν = PMF.pure (c.setProc { c.proc with
        est := out.est, lastGrade := some out, phase := .toCallW }) := by
  cases h
  case retG => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepC_retG_foreign {r : ℕ} {id : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.retG r id out bnd)) ν) :
    ν = PMF.pure c := by
  cases h
  case retG => exact absurd rfl hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem stepC_callW_own {r : ℕ}
    (h : CoreProcStepN P j c (Sum.inl (.callW r j)) ν) :
    (c.corrupted = false ∧ c.proc.phase = .toCallW ∧ c.proc.round = r ∧
      ν = PMF.pure (c.setProc { c.proc with phase := .awaitW })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepC_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.callW r id)) ν) : ν = PMF.pure c := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem stepC_retW_own {r : ℕ} {co : Bool}
    (h : CoreProcStepN P j c (Sum.inl (.retW r j co)) ν) :
    (c.corrupted = false ∧ c.proc.phase = .awaitW ∧ c.proc.round = r ∧
      (∀ v : Bool, c.proc.lastGrade ≠ some (.A v)) ∧
      ν = PMF.pure (c.stepRound co)) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepC_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.retW r id co)) ν) : ν = PMF.pure c := by
  cases h
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
replaced, and a replaced program stands still. -/
theorem stepC_fail_own (h : CoreProcStepN P j c (Sum.inl (.fail j)) ν) :
    (c.corrupted = false ∧ ν = PMF.pure { c with corrupted := true }) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepC_fail_foreign {k : Fin P.n} (hk : k ≠ j)
    (h : CoreProcStepN P j c (Sum.inl (.fail k)) ν) : ν = PMF.pure c := by
  cases h
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

theorem stepC_dsnd_self {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.dsnd j b)) ν) :
    (c.corrupted = false ∧ P.f + 1 ≤ c.decidedCount b ∧ ν = PMF.pure c) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case dsndRelay => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case dsndIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem stepC_dsnd_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.dsnd k b)) ν) : ν = PMF.pure c := by
  cases h
  case dsndRelay => exact absurd rfl hk
  case dsndIdle => rfl
  case corruptedIdle => rfl

theorem stepC_ddlv_self {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.ddlv j k b)) ν) :
    c.corrupted = false ∧ b ∉ c.decIn k ∧ ν = PMF.pure (c.recvDec k b) := by
  cases h
  case ddlvRecv => exact ⟨by assumption, by assumption, rfl⟩
  case ddlvIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepC_ddlv_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.ddlv i k b)) ν) : ν = PMF.pure c := by
  cases h
  case ddlvRecv => exact absurd rfl hi
  case ddlvIdle => rfl
  case corruptedIdle => rfl

theorem stepC_retWPub_self {r : ℕ} {co b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.retWPub r j co b)) ν) :
    c.corrupted = false ∧ c.proc.phase = .awaitW ∧ c.proc.round = r ∧
      c.proc.lastGrade = some (.A b) ∧ ν = PMF.pure (c.stepRound co) := by
  cases h
  case retWPub =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWPubIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepC_retWPub_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.retWPub r id co b)) ν) : ν = PMF.pure c := by
  cases h
  case retWPub => exact absurd rfl hid
  case retWPubIdle => rfl
  case corruptedIdle => rfl

theorem stepC_gcallLoop_self {r : ℕ} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.gcallLoop r j b)) ν) :
    c.corrupted = false ∧ c.proc.phase = .toCallG ∧ c.proc.round = r ∧
      c.proc.est = some b ∧
      ν = PMF.pure (c.setProc { c.proc with phase := .awaitG }) := by
  cases h
  case gcallLoop =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gcallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem stepC_gcallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : CoreProcStepN P j c (Sum.inr (.gcallLoop r id b)) ν) : ν = PMF.pure c := by
  cases h
  case gcallLoop => exact absurd rfl hid
  case gcallLoopIdle => rfl
  case corruptedIdle => rfl

theorem stepC_byzCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzCallG r k b)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

theorem stepC_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzCallGLoop r k b)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

theorem stepC_byzRetG {r : ℕ} {k : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzRetG r k out bnd)) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem stepC_byzCallW {r : ℕ} {k : Fin P.n}
    (h : CoreProcStepN P j c (Sum.inr (.byzCallW r k)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

theorem stepC_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : CoreProcStepN P j c (Sum.inr (.byzRetW r k b)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a round
loop whose flag is up leaves its record where it stands. The proof is by cases
on the table: every row that writes carries the health guard, so no row of a
replaced program survives except a self-loop. -/
theorem stepC_inert {L : NLab P.n} (hc : c.corrupted = true)
    (h : CoreProcStepN P j c L ν) : ν = PMF.pure c := by
  cases h <;> simp_all

end CoreInversion

/-! ### The ABA-side network's rules, by label class -/

section ANetInversion

variable {P : Params} {a : ANetState P.n} {μ : PMF (ANetState P.n)}

theorem aStep_dsnd {j : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.dsnd j b)) μ) :
    b ∉ a.dsent j ∧ μ = PMF.pure (a.dput j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_ddlv {i j : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.ddlv i j b)) μ) :
    b ∈ a.dsent j ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_retWPub {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : ANetStep P a (Sum.inr (.retWPub r id c b)) μ) :
    μ = PMF.pure (a.dput id b) := by
  cases h; rfl

theorem aStep_gcallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.gcallLoop r id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_byzCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.byzCallG r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.byzCallGLoop r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzRetG {r : ℕ} {k : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : ANetStep P a (Sum.inr (.byzRetG r k out bnd)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzCallW {r : ℕ} {k : Fin P.n}
    (h : ANetStep P a (Sum.inr (.byzCallW r k)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_byzRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inr (.byzRetW r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem aStep_callABA {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inl (.callABA id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

/-- A return is authorised either by the DECIDED sent of the returning process
or by its corruption (D23); the two rows share the label and the identity
successor. -/
theorem aStep_retABA {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inl (.retABA id b)) μ) :
    (b ∈ a.dsent id ∨ id ∈ a.F) ∧ μ = PMF.pure a := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByz => exact ⟨Or.inr (by assumption), rfl⟩

theorem aStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ANetStep P a (Sum.inl (.callG r id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_retG {r : ℕ} {id : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : ANetStep P a (Sum.inl (.retG r id out bnd)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_callW {r : ℕ} {id : Fin P.n}
    (h : ANetStep P a (Sum.inl (.callW r id)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : ANetStep P a (Sum.inl (.retW r id c)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem aStep_fail {k : Fin P.n}
    (h : ANetStep P a (Sum.inl (.fail k)) μ) :
    k ∉ a.F ∧ a.F.card < P.f ∧ μ = PMF.pure (ANetState.corrupt P k a) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem aStep_tau (h : ANetStep P a (Sum.inl .tau) μ) :
    ∃ (k : Fin P.n) (b : Bool), k ∈ a.F ∧ μ = PMF.pure (a.dput k b) := by
  cases h
  case byzD => exact ⟨_, _, by assumption, rfl⟩

theorem aStep_gsnd_noStep {r : ℕ} {k : Fin P.n} {m : GBCA.Msg}
    (h : ANetStep P a (Sum.inr (.gsnd r k m)) μ) : False := by cases h

theorem aStep_gdlv_noStep {r : ℕ} {i k : Fin P.n} {m : GBCA.Msg}
    (h : ANetStep P a (Sum.inr (.gdlv r i k m)) μ) : False := by cases h

end ANetInversion

/-! ### Pinning the round-loop tuple -/

theorem coresN_update {P : Params} {C y : ∀ _ : Fin P.n, CoreRec P.n}
    {id : Fin P.n} {nd : CoreRec P.n}
    (hown : (PMF.pure (y id) : PMF (CoreRec P.n)) = PMF.pure nd)
    (hfor : ∀ i, i ≠ id → (PMF.pure (y i) : PMF (CoreRec P.n)) = PMF.pure (C i)) :
    y = Function.update C id nd := by
  funext i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact pureN_inj hown
  · rw [Function.update_of_ne hi]; exact pureN_inj (hfor i hi)

theorem coresN_id {P : Params} {C y : ∀ _ : Fin P.n, CoreRec P.n}
    (hall : ∀ i, (PMF.pure (y i) : PMF (CoreRec P.n)) = PMF.pure (C i)) : y = C :=
  funext fun i => pureN_inj (hall i)

/-- One round loop moves and every other idles. -/
theorem coresN_family {P : Params} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {L : NLab P.n} (id : Fin P.n) (nd : CoreRec P.n)
    (hown : CoreProcStepN P id (C id) L (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → CoreProcStepN P i (C i) L (PMF.pure (C i))) :
    ∀ i, CoreProcStepN P i (C i) L (PMF.pure (Function.update C id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

end Comp

end ABA
end PLTS
