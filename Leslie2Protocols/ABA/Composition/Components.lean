/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.RoundLoop
import Leslie2Protocols.ABA.Implementation.Alphabet
import Leslie2Protocols.ABA.GBCA.ABDY.Implementation
import Leslie2Protocols.ABA.Specifications.ABASafety
import Leslie2Protocols.ABA.Specifications.WCC
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# The extended alphabet and the components composed over it

The protocol is composed twice in this development. The protocol
(`ABA/ImplementationByABDY/System.lean`) puts `n` per-process programs beside a network adversary
and the coin oracle. The composed system (`ABA/Composition/HybridAndSubstitution.lean`) cuts the
same protocol into its components. Both compositions speak one alphabet, and some of what they
compose is the same object in both systems. This file holds that alphabet and those components.

## The extended alphabet

`Label n` is the shared alphabet of the protocol and of its specification. It cannot name the two
message networks, the Byzantine handshake rows, or the branches of a handshake that it does not
distinguish. The rendezvous alphabet `NetworkEvent n M` names them, over a graded-agreement message
type `M` (`ABA/Implementation/Alphabet.lean`); `NetworkEvent n` is that alphabet at the round
messages of `GBCA/ABDY/Implementation.lean`, and `ExtendedLabel n = Label n ⊕ NetworkEvent n` is the
alphabet every component here speaks. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable, and `networkEventLabels n` — the set of all of them — is what both compositions hide
before reading the result back over `Label n`.

## The coin oracle

The coin oracle `WCC.specFamily` speaks `Label n`, so it is joined to the
extended alphabet through the label pullback `coinLabelMap`, which sends a shared
label to itself, the Byzantine handshake rows and the fused coin return to
the oracle's own handshake rows, and every other rendezvous label out of the
domain. `coinOverRoundAlphabet` is the oracle read along that pullback at this alphabet. It
is a component of both compositions, unchanged.

## The round loop of one process

`RoundLoopStep` is the rule table of one process's round loop: the API rows `callABA` and `retABA`,
the graded-agreement and coin handshakes, the DECIDED relay and its delivery, and an idle row for
every label the process does not act on. It writes no round record. The composed system runs `n` of
these automata (`roundLoopProgram`) under a full-synchronisation product. The protocol composition
fuses each round loop with the round records into one program (`ABDY.ABAProgramStep`), whose record
is the pair.

A corruption replaces the program of the process it names (D23). The flag
`RoundLoopRecord.corrupted` goes up on the process's own half of `fail`, every
participant's row is guarded by `corrupted = false`, and the replaced program
is the single self-loop `corruptedIdle`. The replaced program has no row on the
labels of `actsAt j` — the labels on which the process would act on its own
sub-protocol messages — so those messages enter only through the Byzantine handshake rows
(D11).

## The ABA network

`ABANetworkStep` is what the network adversary retains once the round networks have taken the round
sent sets: the DECIDED sets `decidedSent j`, the corrupted set `F` with its budget, and the
authorisation of every Byzantine handshake row. `ABANetwork` is that automaton. Its `fail` row
carries the budget guard `k ∉ F ∧ |F| < f`, so a corruption fires exactly when it takes effect, and
its `retByzantine` row lets a corrupted process return without DECIDED evidence, pairing with the
replaced program's self-loop on `retABA` (D23). It holds no ghost record: the bound bit a
graded-agreement return announces belongs to the round, so the round's instance carries it and both
rows here idle on it.

## What this file supplies

The two rule tables above, the two automata they carry, the determinacy of
both tables, and the inversion tables that read a row of each off its label
(`roundLoopStep_*`, `abaNetworkStep_*`) — among them `roundLoopStep_noStep`, which reads every row
of a replaced program as a self-loop. It also supplies the systems of the
synchronised round-loop group in both directions (`roundLoopProduct_inversion`,
`roundLoopProduct_pure`) and the lemmas that pin a round-loop tuple down from its
per-process rows (`roundLoopRecords_*`).
-/

namespace PLTS
namespace ABA

namespace Composition

open Implementation

/-! ### The auxiliary alphabet

The rendezvous alphabet, the hidden-label set, the labels a process acts on, the coin oracle's label
pullback and the lifted oracle are parametric in the graded-agreement message type
(`ABA/Implementation/Alphabet.lean`). This file fixes that type to the round messages of
`GBCA/ABDY/Implementation.lean`. -/

/-- The rendezvous alphabet at the round messages of `GBCA/ABDY/Implementation.lean`. -/
abbrev NetworkEvent (n : ℕ) : Type := Implementation.NetworkEvent n GBCA.ByABDY.Message

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev ExtendedLabel (n : ℕ) : Type := Label n ⊕ NetworkEvent n

/-- The coin oracle, read over this alphabet through the pullback. -/
noncomputable def coinOverRoundAlphabet (P : Parameters) : System (ℕ → WCC.SpecState P.n)
  (ExtendedLabel
  P.n) :=
  coinOverExtendedAlphabet P GBCA.ByABDY.Message

@[simp] theorem coinOverRoundAlphabet_init (P : Parameters) :
    (coinOverRoundAlphabet P).init = (WCC.specFamily P).init := rfl

/-! ## The component vocabulary

Everything the component boundary names lives under `PLTS.ABA.Composition`, so
that `PLTS.ABA` itself carries only what the chain cites. -/

/-! ### The round-loop program of one process

The automaton that calls a round's graded-agreement instance and the coin, and decides. It writes no
round record: the five multicast levels and the round delivery are internal to a round instance, so
they leave no row here, and the three Byzantine graded-agreement rows change no round-loop data,
which is why they appear below only as idle rows.

The programs sit under a full-synchronisation product, so every label that can
fire in the composite has a row: the participant's, or an idle one. Unlike the
round-indexed families, these programs are not round-filtered. A round loop
must answer every round's `callG`, its own as a participant and every other
process's as a bystander.

A corruption replaces the program of the process it names (D23). The
replacement is carried by the flag `RoundLoopRecord.corrupted`, which `failSelf` writes
on the process's own `fail`; every participant's row is guarded by
`corrupted = false`, so the record freezes at the corruption. In place of those
rows the replaced program has the single row `corruptedIdle`: a self-loop on
every label other than `τ` and the labels of `actsAt j`. On the latter the
replaced program has no row at all, so those labels cannot fire; the corrupted
process's graded-agreement messages enters through the Byzantine handshake rows (D11)
and its DECIDED messages through `byzantineDecided`. -/

/-- The step relation of the round-loop program of process `j`. -/
inductive RoundLoopStep (P : Parameters) (j : Fin P.n) :
    RoundLoopRecord P.n → ExtendedLabel P.n → PMF (RoundLoopRecord P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : RoundLoopRecord P.n) (b : Bool) (hh : c.corrupted = false)
      (h : c.process.input = none) :
      RoundLoopStep P j c (Sum.inl (.callABA j b))
        (PMF.pure (c.setProcess { c.process with
          input := some b, estimate := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop on `j`'s own `callABA`: the loop absorbs a call at
  a process holding an input. The `input` row carries the label at a process
  holding none, so the label is enabled in every state and a first call at a
  process whose program stands commits (D36). -/
  | inputLoop (c : RoundLoopRecord P.n) (b : Bool) (hh : c.corrupted = false)
      (hin : c.process.input ≠ none) :
      RoundLoopStep P j c (Sum.inl (.callABA j b)) (PMF.pure c)
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : RoundLoopRecord P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callABA id b)) (PMF.pure c)
  /-- Return `b` on an `n − f` DECIDED quorum. Having multicast `b` oneself is
  a condition on the DECIDED sets, hence `ABANetwork`'s conjunct. -/
  | ret (c : RoundLoopRecord P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.process.returned = false) :
      RoundLoopStep P j c (Sum.inl (.retABA j b))
        (PMF.pure (c.setProcess { c.process with returned := true }))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : RoundLoopRecord P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retABA id b)) (PMF.pure c)
  /-- The graded-agreement call, round-loop half: hand the estimate over and wait. Opening the round
  record is the round instance's half. -/
  | callG (c : RoundLoopRecord P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallG) (hr : c.process.round = r)
      (hest : c.process.estimate = some b) :
      RoundLoopStep P j c (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcess { c.process with phase := .awaitG }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : RoundLoopRecord P.n) (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callG r id b)) (PMF.pure c)
  /-- The graded-agreement return, round-loop half: record the grade and head
  for the coin. The evidence for the grade is the round instance's conjunct.
  The round's bound bit is announced beside the grade and written nowhere: the
  round loop is one of the programs that do not read it. -/
  | retG (c : RoundLoopRecord P.n) (r : ℕ) (out : GBCAOutput) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitG) (hr : c.process.round = r) :
      RoundLoopStep P j c (Sum.inl (.retG r j out bnd))
        (PMF.pure (c.setProcess { c.process with
          estimate := out.estimate, lastGrade := some out, phase := .toCallW }))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : RoundLoopRecord P.n) (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retG r id out bnd)) (PMF.pure c)
  /-- `c ← WCC_r()`, the call half. -/
  | callW (c : RoundLoopRecord P.n) (r : ℕ) (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallW) (hr : c.process.round = r) :
      RoundLoopStep P j c (Sum.inl (.callW r j))
        (PMF.pure (c.setProcess { c.process with phase := .awaitW }))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : RoundLoopRecord P.n) (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callW r id)) (PMF.pure c)
  /-- The coin return without a publication: the round advances and nothing is
  multicast, the round's grade not being a grade-2 outcome (D10). -/
  | retW (c : RoundLoopRecord P.n) (r : ℕ) (co : Bool) (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitW) (hr : c.process.round = r)
      (hgr : ∀ v : Bool, c.process.lastGrade ≠ some (.grade2 v)) :
      RoundLoopStep P j c (Sum.inl (.retW r j co)) (PMF.pure (c.stepRound co))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : RoundLoopRecord P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retW r id co)) (PMF.pure c)
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the row (D23). -/
  | failSelf (c : RoundLoopRecord P.n) (hh : c.corrupted = false) :
      RoundLoopStep P j c (Sum.inl (.fail j))
        (PMF.pure { c with corrupted := true })
  /-- Another process's corruption is not the round loop's business (D1). -/
  | failIdle (c : RoundLoopRecord P.n) (k : Fin P.n) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inl (.fail k)) (PMF.pure c)
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `actsAt j`, on which the process has no row at all. -/
  | corruptedIdle (c : RoundLoopRecord P.n) (L : ExtendedLabel P.n) (hh : c.corrupted = true)
      (hτ : L ≠ Sum.inl Label.tau) (hown : ¬ actsAt j L) :
      RoundLoopStep P j c L (PMF.pure c)
  /-- The DECIDED relay on an `f + 1` quorum (D12′): the quorum is a condition
  on the record, the write-once condition and the sent insert are `ABANetwork`'s. -/
  | decidedSendRelay (c : RoundLoopRecord P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      RoundLoopStep P j c (Sum.inr (.decidedSend j b)) (PMF.pure c)
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | decidedSendIdle (c : RoundLoopRecord P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedSend k b)) (PMF.pure c)
  /-- DECIDED delivery, receiver's half: at most one receipt per (sender, bit)
  (D12′). Authenticity is `ABANetwork`'s conjunct. -/
  | decidedDeliverReceive (c : RoundLoopRecord P.n) (k : Fin P.n) (b : Bool) (hh : c.corrupted =
    false)
      (hr : b ∉ c.decidedDelivered k) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b)) (PMF.pure (c.receiveDecided k b))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | decidedDeliverIdle (c : RoundLoopRecord P.n) (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver i k b)) (PMF.pure c)
  /-- The coin return fused with the `⟨DECIDED, b⟩` publication (D10): the
  round's outcome was `grade2 b`, so the round advance publishes `b`, the sent insert
  being `ABANetwork`'s half. -/
  | retWPublish (c : RoundLoopRecord P.n) (r : ℕ) (co : Bool) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitW) (hr : c.process.round = r)
      (hgr : c.process.lastGrade = some (.grade2 b)) :
      RoundLoopStep P j c (Sum.inr (.retWPublish r j co b)) (PMF.pure (c.stepRound co))
  /-- A fused coin return at another process: not `j`'s business. -/
  | retWPublishIdle (c : RoundLoopRecord P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (b : Bool)
      (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inr (.retWPublish r id co b)) (PMF.pure c)
  /-- The graded-agreement call against an already-called round record: the round loop moves and
  nothing else does — the whole row is core content. -/
  | gbcaCallLoop (c : RoundLoopRecord P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallG) (hr : c.process.round = r)
      (hest : c.process.estimate = some b) :
      RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r j b))
        (PMF.pure (c.setProcess { c.process with phase := .awaitG }))
  /-- Such a call at another process: not `j`'s business. -/
  | gbcaCallLoopIdle (c : RoundLoopRecord P.n) (r : ℕ) (id : Fin P.n) (b : Bool)
      (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r id b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call (D11) writes a round record and no round-loop data: every
  round loop, the named one included, stands still. -/
  | byzantineCallGIdle (c : RoundLoopRecord P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallG r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call against an already-called round record (D11): nothing moves
  anywhere. -/
  | byzantineCallGLoopIdle (c : RoundLoopRecord P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallGLoop r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement return (D11): round content only. -/
  | byzantineRetGIdle (c : RoundLoopRecord P.n) (r : ℕ) (k : Fin P.n) (out : GBCAOutput)
      (bnd : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineRetG r k out bnd)) (PMF.pure c)
  /-- A Byzantine coin call (D11): the coin oracle reacts through the pullback. -/
  | byzantineCallWIdle (c : RoundLoopRecord P.n) (r : ℕ) (k : Fin P.n) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallW r k)) (PMF.pure c)
  /-- A Byzantine coin return (D11): the coin oracle reacts through the
  pullback. -/
  | byzantineRetWIdle (c : RoundLoopRecord P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineRetW r k b)) (PMF.pure c)

/-! ### The DECIDED sets and the corrupted set

What is left of the network adversary once the round-tagged sent sets have gone to
the round networks: the DECIDED sets, the corrupted set with its budget, and
the authorisation of every Byzantine handshake row. -/

/-- The state of the ABA network: the DECIDED sets and the corrupted set. -/
structure ABANetworkState (n : ℕ) : Type where
  /-- `decidedSent j` — the DECIDED payloads process `j` has multicast (D12′). -/
  decidedSent : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)

namespace ABANetworkState

variable {n : ℕ}

/-- The initial network: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) : ABANetworkState n where
  decidedSent := fun _ => ∅
  F := ∅

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def recordDecided (a : ABANetworkState n) (j : Fin n) (b : Bool) : ABANetworkState n :=
  { a with decidedSent := Function.update a.decidedSent j (insert b (a.decidedSent j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Parameters) (id : Fin P.n) (a : ABANetworkState P.n) : ABANetworkState P.n :=
  if id ∉ a.F ∧ a.F.card < P.f then { a with F := insert id a.F } else a

@[simp] theorem recordDecided_decidedSent (a : ABANetworkState n) (j : Fin n) (b : Bool) :
    (a.recordDecided j b).decidedSent = Function.update a.decidedSent j (insert b (a.decidedSent j))
      := rfl

@[simp] theorem recordDecided_F (a : ABANetworkState n) (j : Fin n) (b : Bool) :
    (a.recordDecided j b).F = a.F := rfl

end ABANetworkState

/-- The step relation of the ABA network. All transitions are Dirac. -/
inductive ABANetworkStep (P : Parameters) :
    ABANetworkState P.n → ExtendedLabel P.n → PMF (ABANetworkState P.n) → Prop
  /-- The DECIDED relay's half: the payload must not be sent yet (D12′). -/
  | decidedSend (a : ABANetworkState P.n) (j : Fin P.n) (b : Bool) (h : b ∉ a.decidedSent j) :
      ABANetworkStep P a (Sum.inr (.decidedSend j b)) (PMF.pure (a.recordDecided j b))
  /-- The DECIDED delivery's half: the payload must be sent under the named
  sender (D12′). -/
  | decidedDeliver (a : ABANetworkState P.n) (i j : Fin P.n) (b : Bool) (h : b ∈ a.decidedSent j) :
      ABANetworkStep P a (Sum.inr (.decidedDeliver i j b)) (PMF.pure a)
  /-- The fused coin return's half: sent the published payload (D10, D12′). -/
  | retWPublish (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) (b : Bool) :
      ABANetworkStep P a (Sum.inr (.retWPublish r id c b)) (PMF.pure (a.recordDecided id b))
  /-- A graded-agreement call against an already-called round record publishes nothing here. -/
  | gbcaCallLoop (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inr (.gbcaCallLoop r id b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement call (D11): the round
  instance carries the effect, this component carries the guard. -/
  | byzantineCallG (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inr (.byzantineCallG r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine call against an already-called round record (D11). -/
  | byzantineCallGLoop (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (b : Bool)
      (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inr (.byzantineCallGLoop r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement return (D11). -/
  | byzantineRetG (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inr (.byzantineRetG r k out bnd)) (PMF.pure a)
  /-- The authorisation of a Byzantine coin call (D11). -/
  | byzantineCallW (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inr (.byzantineCallW r k)) (PMF.pure a)
  /-- The authorisation of a Byzantine coin return (D11). -/
  | byzantineRetW (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inr (.byzantineRetW r k b)) (PMF.pure a)
  /-- An external input is not this component's business. -/
  | callABAIdle (a : ABANetworkState P.n) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.callABA id b)) (PMF.pure a)
  /-- A return requires the returning process to have multicast the payload —
  a condition on its DECIDED sent (D12′). -/
  | retABA (a : ABANetworkState P.n) (id : Fin P.n) (b : Bool) (h : b ∈ a.decidedSent id) :
      ABANetworkStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- A corrupted process returns whatever it likes (D23): its program has been
  replaced, so the DECIDED evidence the correct row asks for is not required of
  it. The authorisation is this component's `id ∈ F`, and the round loop's half
  is the replaced program's self-loop. -/
  | retByzantine (a : ABANetworkState P.n) (id : Fin P.n) (b : Bool) (hF : id ∈ a.F) :
      ABANetworkStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- The graded-agreement call's `⟨INPUT, b⟩` is sent in the round's network,
  not here. -/
  | callGIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.callG r id b)) (PMF.pure a)
  /-- A graded-agreement return publishes nothing here, and the bound bit it
  announces is the round instance's: this component holds no ghost. -/
  | retGIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
      (bnd : Bool) :
      ABANetworkStep P a (Sum.inl (.retG r id out bnd)) (PMF.pure a)
  /-- A coin call publishes nothing. -/
  | callWIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) :
      ABANetworkStep P a (Sum.inl (.callW r id)) (PMF.pure a)
  /-- An unfused coin return publishes nothing. -/
  | retWIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) :
      ABANetworkStep P a (Sum.inl (.retW r id c)) (PMF.pure a)
  /-- Corruption (deviations D1, D23): Dirac, and guarded by the budget. The
  guard sits on the row rather than inside `ABANetworkState.corrupt` alone, so that a
  corruption fires exactly when it takes effect and the round loop's half may
  write the replacement flag outright. -/
  | fail (a : ABANetworkState P.n) (k : Fin P.n) (hnew : k ∉ a.F) (hbud : a.F.card < P.f) :
      ABANetworkStep P a (Sum.inl (.fail k)) (PMF.pure (ABANetworkState.corrupt P k a))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate in the DECIDED sets. -/
  | byzantineDecided (a : ABANetworkState P.n) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inl .tau) (PMF.pure (a.recordDecided k b))

/-! ### The two automata -/

/-- The round-loop program of process `j`. -/
noncomputable def roundLoopProgram (P : Parameters) (j : Fin P.n) :
    System (RoundLoopRecord P.n) (ExtendedLabel P.n) where
  init := RoundLoopRecord.initial P.n
  step := RoundLoopStep P j

@[simp] theorem roundLoopProgram_init (P : Parameters) (j : Fin P.n) :
    (roundLoopProgram P j).init = RoundLoopRecord.initial P.n := rfl

@[simp] theorem roundLoopProgram_step (P : Parameters) (j : Fin P.n) (c : RoundLoopRecord P.n)
    (l : ExtendedLabel P.n) (ν : PMF (RoundLoopRecord P.n)) :
    (roundLoopProgram P j).step c l ν ↔ RoundLoopStep P j c l ν := Iff.rfl

/-- The ABA network. -/
noncomputable def ABANetwork (P : Parameters) : System (ABANetworkState P.n) (ExtendedLabel P.n)
  where
  init := ABANetworkState.initial P.n
  step := ABANetworkStep P

@[simp] theorem ABANetwork_init (P : Parameters) : (ABANetwork P).init = ABANetworkState.initial P.n
  := rfl

@[simp] theorem ABANetwork_step (P : Parameters) (a : ABANetworkState P.n) (l : ExtendedLabel P.n)
    (μ : PMF (ABANetworkState P.n)) : (ABANetwork P).step a l μ ↔ ABANetworkStep P a l μ := Iff.rfl

/-! ### Determinacy of the two rule tables -/

/-- Every round-loop transition is Dirac. -/
theorem roundLoopStep_dirac {P : Parameters} {j : Fin P.n} {c : RoundLoopRecord P.n}
    {l : ExtendedLabel P.n} {ν : PMF (RoundLoopRecord P.n)} (h : RoundLoopStep P j c l ν) :
    ∃ c', ν = PMF.pure c' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every ABA network transition is Dirac. -/
theorem abaNetworkStep_dirac {P : Parameters} {a : ABANetworkState P.n} {l : ExtendedLabel P.n}
    {μ : PMF (ABANetworkState P.n)} (h : ABANetworkStep P a l μ) : ∃ a', μ = PMF.pure a' := by
  cases h <;> exact ⟨_, rfl⟩

/-- No round-loop rule fires on `τ`: a round loop only ever moves in a
rendezvous or on a shared API label. -/
theorem roundLoopStep_no_tau {P : Parameters} {j : Fin P.n} {c : RoundLoopRecord P.n}
    {ν : PMF (RoundLoopRecord P.n)} (h : RoundLoopStep P j c (Silent.τ : ExtendedLabel P.n) ν) :
    False := by
  rw [extendedLabel_tau] at h
  cases h
  rename_i hτ _
  exact hτ rfl

/-! ### Reading and building a transition of the round-loop group -/

/-- A synchronised transition of the round-loop group on a visible label. -/
theorem roundLoopProduct_inversion {P : Parameters} {C : ∀ _ : Fin P.n,
    RoundLoopRecord P.n} {l : ExtendedLabel P.n} {μ : PMF (∀ _ : Fin P.n, RoundLoopRecord P.n)}
    (h : (System.synchronisedProduct (roundLoopProgram P)).step C l μ) :
    ∃ y : ∀ _ : Fin P.n, RoundLoopRecord P.n,
      μ = PMF.pure y ∧ ∀ i, RoundLoopStep P i (C i) l (PMF.pure (y i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hy : ∀ i, ∃ c', μ_ i = PMF.pure c' := fun i => roundLoopStep_dirac (hall i)
    choose y hy using hy
    refine ⟨y, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (y i) from funext hy]
      exact piPMF_pure y
    · rw [← hy i]; exact hall i
  · exact absurd hstep roundLoopStep_no_tau

/-- Build a synchronised transition of the round-loop group from per-process
Dirac steps. -/
theorem roundLoopProduct_pure {P : Parameters} {C y : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {l : ExtendedLabel P.n} (hl : l ≠ Silent.τ)
    (h : ∀ i, RoundLoopStep P i (C i) l (PMF.pure (y i))) :
    (System.synchronisedProduct (roundLoopProgram P)).step C l (PMF.pure y) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (y i), h, (piPMF_pure y).symm⟩

/-- The round-loop group has no silent transition. -/
theorem roundLoopProduct_no_tau {P : Parameters} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {μ : PMF (∀ _ : Fin P.n, RoundLoopRecord P.n)}
    (h : (System.synchronisedProduct (roundLoopProgram P)).step C (Silent.τ : ExtendedLabel P.n) μ)
      :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact roundLoopStep_no_tau hstep

/-! ### One round loop's rules, by label class

Each lemma reads a row of `RoundLoopStep` off its label: the participant's row
as its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. A participant's row carries the health guard
`corrupted = false`, and on a label outside `actsAt j` the replaced program's
self-loop is a second row on the same label (D23). -/

section CoreInversion

variable {P : Parameters} {j : Fin P.n} {c : RoundLoopRecord P.n} {ν : PMF (RoundLoopRecord P.n)}

theorem roundLoopStep_callABA_own {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.callABA j b)) ν) :
    (c.corrupted = false ∧ c.process.input = none ∧
      ν = PMF.pure (c.setProcess { c.process with
        input := some b, estimate := some b, round := 0, phase := .toCallG })) ∨
    ((c.corrupted = true ∨ c.process.input ≠ none) ∧ ν = PMF.pure c) := by
  cases h
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem roundLoopStep_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callABA id b)) ν) : ν = PMF.pure c := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_retABA_own {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retABA j b)) ν) :
    (c.corrupted = false ∧ P.n - P.f ≤ c.decidedCount b ∧
      c.process.returned = false ∧
      ν = PMF.pure (c.setProcess { c.process with returned := true })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case ret => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retABA id b)) ν) : ν = PMF.pure c := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_callG_own {r : ℕ} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.callG r j b)) ν) :
    c.corrupted = false ∧ c.process.phase = .toCallG ∧ c.process.round = r ∧
      c.process.estimate = some b ∧
      ν = PMF.pure (c.setProcess { c.process with phase := .awaitG }) := by
  cases h
  case callG =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callG r id b)) ν) : ν = PMF.pure c := by
  cases h
  case callG => exact absurd rfl hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_retG_own {r : ℕ} {out : GBCAOutput} {bnd : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retG r j out bnd)) ν) :
    c.corrupted = false ∧ c.process.phase = .awaitG ∧ c.process.round = r ∧
      ν = PMF.pure (c.setProcess { c.process with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW }) := by
  cases h
  case retG => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_retG_foreign {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retG r id out bnd)) ν) :
    ν = PMF.pure c := by
  cases h
  case retG => exact absurd rfl hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_callW_own {r : ℕ}
    (h : RoundLoopStep P j c (Sum.inl (.callW r j)) ν) :
    (c.corrupted = false ∧ c.process.phase = .toCallW ∧ c.process.round = r ∧
      ν = PMF.pure (c.setProcess { c.process with phase := .awaitW })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callW r id)) ν) : ν = PMF.pure c := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_retW_own {r : ℕ} {co : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retW r j co)) ν) :
    (c.corrupted = false ∧ c.process.phase = .awaitW ∧ c.process.round = r ∧
      (∀ v : Bool, c.process.lastGrade ≠ some (.grade2 v)) ∧
      ν = PMF.pure (c.stepRound co)) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retW r id co)) ν) : ν = PMF.pure c := by
  cases h
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
replaced, and a replaced program stands still. -/
theorem roundLoopStep_fail_own (h : RoundLoopStep P j c (Sum.inl (.fail j)) ν) :
    (c.corrupted = false ∧ ν = PMF.pure { c with corrupted := true }) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_fail_foreign {k : Fin P.n} (hk : k ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.fail k)) ν) : ν = PMF.pure c := by
  cases h
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_decidedSend_self {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedSend j b)) ν) :
    (c.corrupted = false ∧ P.f + 1 ≤ c.decidedCount b ∧ ν = PMF.pure c) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case decidedSendRelay => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case decidedSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_decidedSend_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.decidedSend k b)) ν) : ν = PMF.pure c := by
  cases h
  case decidedSendRelay => exact absurd rfl hk
  case decidedSendIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_decidedDeliver_self {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b)) ν) :
    c.corrupted = false ∧ b ∉ c.decidedDelivered k ∧ ν = PMF.pure (c.receiveDecided k b) := by
  cases h
  case decidedDeliverReceive => exact ⟨by assumption, by assumption, rfl⟩
  case decidedDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_decidedDeliver_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.decidedDeliver i k b)) ν) : ν = PMF.pure c := by
  cases h
  case decidedDeliverReceive => exact absurd rfl hi
  case decidedDeliverIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_retWPublish_self {r : ℕ} {co b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.retWPublish r j co b)) ν) :
    c.corrupted = false ∧ c.process.phase = .awaitW ∧ c.process.round = r ∧
      c.process.lastGrade = some (.grade2 b) ∧ ν = PMF.pure (c.stepRound co) := by
  cases h
  case retWPublish =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWPublishIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_retWPublish_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.retWPublish r id co b)) ν) : ν = PMF.pure c := by
  cases h
  case retWPublish => exact absurd rfl hid
  case retWPublishIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_gbcaCallLoop_self {r : ℕ} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r j b)) ν) :
    c.corrupted = false ∧ c.process.phase = .toCallG ∧ c.process.round = r ∧
      c.process.estimate = some b ∧
      ν = PMF.pure (c.setProcess { c.process with phase := .awaitG }) := by
  cases h
  case gbcaCallLoop =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gbcaCallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_gbcaCallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r id b)) ν) : ν = PMF.pure c := by
  cases h
  case gbcaCallLoop => exact absurd rfl hid
  case gbcaCallLoopIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineCallG r k b)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineCallGLoop r k b)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineRetG {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineRetG r k out bnd)) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineCallW r k)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineRetW r k b)) ν) : ν = PMF.pure c := by
  cases h <;> rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a round
loop whose flag is up leaves its record where it stands. The proof is by cases
on the table: every row that writes carries the health guard, so no row of a
replaced program survives except a self-loop. -/
theorem roundLoopStep_noStep {L : ExtendedLabel P.n} (hc : c.corrupted = true)
    (h : RoundLoopStep P j c L ν) : ν = PMF.pure c := by
  cases h <;> simp_all

end CoreInversion

/-! ### The ABA network's rules, by label class -/

section ANetInversion

variable {P : Parameters} {a : ABANetworkState P.n} {μ : PMF (ABANetworkState P.n)}

theorem abaNetworkStep_decidedSend {j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedSend j b)) μ) :
    b ∉ a.decidedSent j ∧ μ = PMF.pure (a.recordDecided j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_decidedDeliver {i j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedDeliver i j b)) μ) :
    b ∈ a.decidedSent j ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_retWPublish {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.retWPublish r id c b)) μ) :
    μ = PMF.pure (a.recordDecided id b) := by
  cases h; rfl

theorem abaNetworkStep_gbcaCallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.gbcaCallLoop r id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallG r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallGLoop r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineRetG {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineRetG r k out bnd)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallW r k)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineRetW r k b)) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_callABA {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.callABA id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

/-- A return is authorised either by the DECIDED sent of the returning process
or by its corruption (D23); the two rows share the label and the identity
successor. -/
theorem abaNetworkStep_retABA {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.retABA id b)) μ) :
    (b ∈ a.decidedSent id ∨ id ∈ a.F) ∧ μ = PMF.pure a := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByzantine => exact ⟨Or.inr (by assumption), rfl⟩

theorem abaNetworkStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.callG r id b)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_retG {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : ABANetworkStep P a (Sum.inl (.retG r id out bnd)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_callW {r : ℕ} {id : Fin P.n}
    (h : ABANetworkStep P a (Sum.inl (.callW r id)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : ABANetworkStep P a (Sum.inl (.retW r id c)) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_fail {k : Fin P.n}
    (h : ABANetworkStep P a (Sum.inl (.fail k)) μ) :
    k ∉ a.F ∧ a.F.card < P.f ∧ μ = PMF.pure (ABANetworkState.corrupt P k a) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem abaNetworkStep_tau (h : ABANetworkStep P a (Sum.inl .tau) μ) :
    ∃ (k : Fin P.n) (b : Bool), k ∈ a.F ∧ μ = PMF.pure (a.recordDecided k b) := by
  cases h
  case byzantineDecided => exact ⟨_, _, by assumption, rfl⟩

theorem abaNetworkStep_gbcaSend_noStep {r : ℕ} {k : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : ABANetworkStep P a (Sum.inr (.gbcaSend r k m)) μ) : False := by cases h

theorem abaNetworkStep_gbcaDeliver_noStep {r : ℕ} {i k : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : ABANetworkStep P a (Sum.inr (.gbcaDeliver r i k m)) μ) : False := by cases h

end ANetInversion

/-! ### Pinning the round-loop tuple -/

theorem roundLoopRecords_update {P : Parameters} {C y : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {id : Fin P.n} {nd : RoundLoopRecord P.n}
    (hown : (PMF.pure (y id) : PMF (RoundLoopRecord P.n)) = PMF.pure nd)
    (hfor : ∀ i, i ≠ id → (PMF.pure (y i) : PMF (RoundLoopRecord P.n)) = PMF.pure (C i)) :
    y = Function.update C id nd := by
  funext i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact pure_inj hown
  · rw [Function.update_of_ne hi]; exact pure_inj (hfor i hi)

theorem roundLoopRecords_id {P : Parameters} {C y : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    (hall : ∀ i, (PMF.pure (y i) : PMF (RoundLoopRecord P.n)) = PMF.pure (C i)) : y = C :=
  funext fun i => pure_inj (hall i)

/-- One round loop moves and every other idles. -/
theorem roundLoopRecords_family {P : Parameters} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {L : ExtendedLabel P.n} (id : Fin P.n) (nd : RoundLoopRecord P.n)
    (hown : RoundLoopStep P id (C id) L (PMF.pure nd))
    (hfor : ∀ i, i ≠ id → RoundLoopStep P i (C i) L (PMF.pure (C i))) :
    ∀ i, RoundLoopStep P i (C i) L (PMF.pure (Function.update C id nd i)) := by
  intro i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne hi]; exact hfor i hi

end Composition

end ABA
end PLTS
