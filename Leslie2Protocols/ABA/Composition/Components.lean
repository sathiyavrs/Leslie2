/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.RoundLoop
import Leslie2Protocols.ABA.Implementation.Alphabet
import Leslie2Protocols.ABA.Specifications.ABASafety
import Leslie2Protocols.ABA.Specifications.WCC
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# The extended alphabet and the components composed over it

The protocol is composed twice in this development. The protocol
(`ABA/ABDY/System.lean`) puts `n` per-process programs beside a network
and the common coin. The composed system (`ABA/ABDY/Composition.lean`) cuts
the same protocol into its components. Both compositions are over one alphabet, and some of
what they compose is the same object in both systems. This file holds that alphabet and those
components.

## The extended alphabet

`Label n` is the shared alphabet of the protocol and of its specification. It cannot name the two
message networks or a corrupted process's sub-protocol calls. `NetworkEvent n M` names them, over
the type `M` of the messages a graded-agreement round exchanges
(`ABA/Implementation/Alphabet.lean`), and `ExtendedLabel n M = Label n ⊕ NetworkEvent n M` is the
alphabet of every component here. Its silent label is `Sum.inl τ`, so every `Sum.inr` label is
observable, and `networkEventLabels n`, the set of all of them, is what both compositions hide
before reading the result back over `Label n`.

## The common coin

The common coin `WCC.specFamily` is over `Label n`, so it is joined to the extended alphabet through
the label pullback `coinLabelMap`, which sends a shared label to itself, a corrupted process's coin
call to the coin's own call, and every other network event out of the domain. `τ` is a shared
label, so the coin's resolution is a silent transition of the coin read along the pullback.
`coinOverRoundAlphabet` is the coin read along that pullback at this alphabet. It is a component of
both compositions.

## The round loop of one process

`RoundLoopStep` is the step relation of one process's round loop: the API transitions `callABA` and
`retABA`, the graded-agreement and coin calls and returns, the DECIDED send, the DECIDED relay and
its delivery, and an idle transition for every label the process does not act on. It writes no
round variables. The composed system runs `n` of these automata (`roundLoopProgram`) under a
full-synchronisation product. The protocol composition pairs each round loop with the round
variables into one program (`ABDY.ABAProgramStep`), whose variables are the pair.

The round loop of `j` outputs its graded-agreement call `callG _ j _`, its coin call `callW _ j`,
its DECIDED send and relay and its return `retABA j _`. It takes every other non-silent label as an
input, at every state. The round's return `retG _ j _` and the coin's return `retW _ j _` are taken
on the return transition at the phase and the round it waits for and on a loop elsewhere
(`retGLoop`, `retWLoop`). A DECIDED delivery is taken on `decidedDeliverReceive` or, where the
payload is already held from its sender, on `decidedDeliverLoop`. The announcement `boundG`, a
corrupted process's sub-protocol calls, every label at another process and, over ABDY22's
messages, every round multicast and round delivery are taken on idle transitions
(`ABA/Composition/InputEnabledness.lean`).

A corruption replaces the program of the process it names (D23). The flag
`RoundLoopVariables.corrupted` is set on the process's own half of `fail`, every participant's
transition is guarded by `corrupted = false`, and the replaced program is the single self-loop
`corruptedIdle`. The replaced program takes no transition on the outputs of `roundLoopActsAt j`,
its graded-agreement call, its coin call and its DECIDED send, and takes every other non-silent
label on the self-loop, the round's return `retG _ j _` among them (D11).

## The ABA network

`ABANetworkStep` is the step relation of the network a composed system holds beside its rounds:
the DECIDED sets `decidedSent j`, the corrupted set `F` with its budget, and the rounds a process
outside `F` has started, `startedRounds` (D37). `ABANetwork` is that automaton. It outputs the
DECIDED deliveries, `fail`, and a corrupted process's two sub-protocol calls `byzantineCallG` and
`byzantineCallW` under `k ∈ F` and `r ∈ startedRounds` (D11, D37). Its
`fail` transition carries the budget guard `k ∉ F ∧ |F| < f`, so a corruption fires exactly when
it takes effect. It takes each of its inputs on one unguarded transition: the call `callG r id b`
records the round's start through `recordStartedRound`, and the DECIDED send and relay record the
bit. Over ABDY22's messages it also outputs the round multicast and the round delivery, on which
it has no transition: the round instance exchanges its messages under labels of its own. It holds
no ghost. The round's bound bit is announced by the round instance on `boundG`, and the network
idles on the announcement.

## What this file supplies

The two step relations above, the two automata they carry, the determinacy of both, and the lemmas
that determine a transition of each from its label (`roundLoopStep_*`, `abaNetworkStep_*`), among
them `roundLoopStep_noStep`, which reads every transition of a replaced program as a self-loop. It
also supplies the systems of the synchronised round-loop group in both directions
(`roundLoopProduct_cases`, `roundLoopProduct_pure`) and the lemmas that determine a round-loop
tuple from its per-process transitions (`roundLoopVariables_*`). -/

namespace PLTS
namespace ABA

namespace Composition

open Implementation

/-! ### The auxiliary alphabet

The labels the programs and the network synchronise on, the hidden-label set, the labels a process
acts on, the common coin's label pullback and the lifted coin are parametric in the type of the
messages a graded-agreement round
exchanges (`ABA/Implementation/Alphabet.lean`). The components below are stated over that alphabet
for every such type `M`. ABDY22's chain takes the messages of
`GBCA/ABDY/MessagesAndVariables.lean` for `M`; the gather-based chain takes `Empty`, and the round
multicast and the round delivery then name no label there. -/

/-- The labels the programs and the network synchronise on, over the type `M` of the messages a
graded-agreement round exchanges. A round of the composed system takes no call or return of its
own, so the type of those events is empty here. -/
abbrev NetworkEvent (n : ℕ) (M : Type) : Type := Implementation.NetworkEvent n M Empty

/-- The extended alphabet. Its silent label is `Sum.inl τ`, so every
`Sum.inr` label is observable and hence hideable. -/
abbrev ExtendedLabel (n : ℕ) (M : Type) : Type := Label n ⊕ NetworkEvent n M

/-- The common coin, read over this alphabet through the pullback. -/
noncomputable def coinOverRoundAlphabet (P : Parameters) (M : Type) [DecidableEq M] :
    System (InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
      (ExtendedLabel P.n M) :=
  coinOverExtendedAlphabet P M Empty

@[simp] theorem coinOverRoundAlphabet_init (P : Parameters) (M : Type) [DecidableEq M] :
    (coinOverRoundAlphabet P M).init = (WCC.specFamily P).init := rfl

/-! ## The component vocabulary

Everything the component boundary names lives under `PLTS.ABA.Composition`, so
that `PLTS.ABA` itself carries only what the chain cites. -/

/-! ### The labels a round loop acts on

A replaced round loop takes no transition on three of the outputs of its process: its
graded-agreement call, its coin call and its DECIDED send. It takes its two other outputs,
`decidedRelay j _` and `retABA j _`, on its self-loop at either bit, and every input on the same
self-loop, the round's return `retG _ j _` among them, which the round instance outputs (D11,
D23). -/

/-- The outputs of the round loop of process `j` on which a replaced round loop takes no
transition: its own graded-agreement call, its own coin call and its own DECIDED send. -/
def roundLoopActsAt {n : ℕ} {M : Type} (j : Fin n) : ExtendedLabel n M → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.callW _ id) => id = j
  | Sum.inr (.decidedSend id _) => id = j
  | _ => False

instance {n : ℕ} {M : Type} (j : Fin n) : DecidablePred (roundLoopActsAt (M := M) j) :=
  fun l => by
    match l with
    | Sum.inl l => cases l <;> unfold roundLoopActsAt <;> infer_instance
    | Sum.inr e => cases e <;> unfold roundLoopActsAt <;> infer_instance

/-! ### The round-loop program of one process

The automaton that calls a round's graded-agreement instance and the coin, and decides. It writes no
round variables: the multicasts and the deliveries of a round are internal to the round instance,
and a corrupted process's graded-agreement call changes no round-loop data, so these labels have
only idle transitions here.

The programs sit under a full-synchronisation product, so every label that can fire in the composite
has a transition: the participant's, or an idle one. A round loop takes every round's `callG`,
its own as a participant and every other process's on an idle transition. Every input of the
round loop has a transition at every state: a return or a DECIDED delivery that the guards of its
transition refuse is taken on a loop (`retGLoop`, `retWLoop`, `decidedDeliverLoop`).

A corruption replaces the program of the process it names (D23). The replacement is carried by the
flag `RoundLoopVariables.corrupted`, which `failSelf` writes on the process's own `fail`; every
participant's transition is guarded by `corrupted = false`, so the variables stay as they are at the
corruption. The replaced program has the single transition `corruptedIdle`: a self-loop on every
label other than `τ` and the labels of `roundLoopActsAt j`. The labels of `roundLoopActsAt j` have
no transition at the replaced program, so they cannot fire. The corrupted process's
graded-agreement and coin calls are the network's outputs `byzantineCallG` and `byzantineCallW`
(D11), and its DECIDED messages enter through `byzantineDecided`. -/

/-- The step relation of the round-loop program of process `j`. -/
inductive RoundLoopStep (P : Parameters) {M : Type} [DecidableEq M] (j : Fin P.n) :
    RoundLoopVariables P.n → ExtendedLabel P.n M → PMF (RoundLoopVariables P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, start round `0`. -/
  | input (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (h : c.processVariables.input = none) :
      RoundLoopStep P j c (Sum.inl (.callABA j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with
          input := some b, estimate := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop on `j`'s own `callABA`: the loop absorbs a call at
  a process holding an input. The `input` transition carries the label at a
  process holding none, so the label is enabled in every state and a first call
  at an unreplaced program commits (D36). -/
  | inputLoop (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hin : c.processVariables.input ≠ none) :
      RoundLoopStep P j c (Sum.inl (.callABA j b)) (PMF.pure c)
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : RoundLoopVariables P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callABA id b)) (PMF.pure c)
  /-- Return `b` on an `n − f` DECIDED quorum, having multicast `⟨DECIDED, b⟩` oneself: LeslieBP
  Algorithm 1's "having sent it", read on the round loop's own record `decidedSent`. -/
  | ret (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hsent : b ∈ c.decidedSent)
      (hret : c.processVariables.returned = false) :
      RoundLoopStep P j c (Sum.inl (.retABA j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with returned := true }))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : RoundLoopVariables P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retABA id b)) (PMF.pure c)
  /-- The graded-agreement call, round-loop half: hand the estimate over and wait. It is the round
  loop's one transition on its call; whether the round records the call or loops on it is the
  round instance's half. -/
  | callG (c : RoundLoopVariables P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hest : c.processVariables.estimate = some b) :
      RoundLoopStep P j c (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callG r id b)) (PMF.pure c)
  /-- The graded-agreement return, round-loop half: record the grade and head
  for the coin. The witness for the grade is the round instance's conjunct. -/
  | retG (c : RoundLoopVariables P.n) (r : ℕ) (out : GBCAOutput)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitG) (hr : c.processVariables.round = r) :
      RoundLoopStep P j c (Sum.inl (.retG r j out))
        (PMF.pure (c.setProcessVariables { c.processVariables with
          estimate := out.estimate, lastGrade := some out, phase := .toCallW }))
  /-- Input-enabledness loop on `j`'s own graded-agreement return: a return of round `r` at a
  round loop that does not wait for round `r`'s return leaves the round loop where it stands. -/
  | retGLoop (c : RoundLoopVariables P.n) (r : ℕ) (out : GBCAOutput) (hh : c.corrupted = false)
      (h : ¬ (c.processVariables.phase = .awaitG ∧ c.processVariables.round = r)) :
      RoundLoopStep P j c (Sum.inl (.retG r j out)) (PMF.pure c)
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
      (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retG r id out)) (PMF.pure c)
  /-- The announcement of a round's bound bit: no round loop reads it, so it is not `j`'s
  business (D29). -/
  | boundGIdle (c : RoundLoopVariables P.n) (r : ℕ) (b : Bool) :
      RoundLoopStep P j c (Sum.inl (.boundG r b)) (PMF.pure c)
  /-- `c ← WCC_r()`, the call half. -/
  | callW (c : RoundLoopVariables P.n) (r : ℕ) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallW) (hr : c.processVariables.round = r) :
      RoundLoopStep P j c (Sum.inl (.callW r j))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitW }))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callW r id)) (PMF.pure c)
  /-- The coin return: the round advances and nothing is sent. On a grade-2 outcome the advance
  enters `toSendDecided`, where the DECIDED send follows. -/
  | retW (c : RoundLoopVariables P.n) (r : ℕ) (co : Bool) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitW) (hr : c.processVariables.round = r) :
      RoundLoopStep P j c (Sum.inl (.retW r j co)) (PMF.pure (c.stepRound co))
  /-- Input-enabledness loop on `j`'s own coin return: a return of round `r` at a round loop that
  does not wait for round `r`'s coin leaves the round loop where it stands. -/
  | retWLoop (c : RoundLoopVariables P.n) (r : ℕ) (co : Bool) (hh : c.corrupted = false)
      (h : ¬ (c.processVariables.phase = .awaitW ∧ c.processVariables.round = r)) :
      RoundLoopStep P j c (Sum.inl (.retW r j co)) (PMF.pure c)
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retW r id co)) (PMF.pure c)
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the transition (D23). -/
  | failSelf (c : RoundLoopVariables P.n) (hh : c.corrupted = false) :
      RoundLoopStep P j c (Sum.inl (.fail j))
        (PMF.pure { c with corrupted := true })
  /-- Another process's corruption is not the round loop's business (D1). -/
  | failIdle (c : RoundLoopVariables P.n) (k : Fin P.n) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inl (.fail k)) (PMF.pure c)
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `roundLoopActsAt j`, on which the process has no transition at all. -/
  | corruptedIdle (c : RoundLoopVariables P.n) (L : ExtendedLabel P.n M) (hh : c.corrupted = true)
      (hτ : L ≠ Sum.inl Label.tau) (hown : ¬ roundLoopActsAt j L) :
      RoundLoopStep P j c L (PMF.pure c)
  /-- The DECIDED relay on an `f + 1` quorum, not having multicast `⟨DECIDED, b⟩`: LeslieBP
  Algorithm 1's "having not sent it", read on the round loop's own record, which the relay writes
  (D12′). The network's half inserts the bit into its DECIDED set. -/
  | decidedRelay (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.f + 1 ≤ c.decidedCount b) (hnot : b ∉ c.decidedSent) :
      RoundLoopStep P j c (Sum.inr (.decidedRelay j b)) (PMF.pure (c.recordDecided b))
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | decidedRelayIdle (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedRelay k b)) (PMF.pure c)
  /-- DECIDED delivery, receiver's half: at most one received message per (sender, bit)
  (D12′). Authenticity is `ABANetwork`'s conjunct. -/
  | decidedDeliverReceive (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool)
      (hh : c.corrupted = false) (hr : b ∉ c.decidedDelivered k) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b)) (PMF.pure (c.receiveDecided k b))
  /-- Input-enabledness loop on a DECIDED delivery to `j`: a payload already held from the same
  sender leaves the round loop where it stands. -/
  | decidedDeliverLoop (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool)
      (hh : c.corrupted = false) (hr : b ∈ c.decidedDelivered k) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b)) (PMF.pure c)
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | decidedDeliverIdle (c : RoundLoopVariables P.n) (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver i k b)) (PMF.pure c)
  /-- The DECIDED send of a grade-2 round: the outcome of the round just closed was
  `grade2 b`, so the process sends `⟨DECIDED, b⟩` to all, records the bit in its own
  `decidedSent`, clears the grade and enters the next round's `toCallG`. The network's half
  inserts the bit into its DECIDED set. -/
  | decidedSend (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toSendDecided)
      (hgr : c.processVariables.lastGrade = some (.grade2 b)) :
      RoundLoopStep P j c (Sum.inr (.decidedSend j b))
        (PMF.pure ((c.setProcessVariables
          { c.processVariables with lastGrade := none, phase := .toCallG }).recordDecided b))
  /-- A DECIDED send by another process: not `j`'s business. -/
  | decidedSendIdle (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedSend k b)) (PMF.pure c)
  /-- A corrupted process's graded-agreement call (D11) writes round variables and no round-loop
  data: it is not `j`'s business, at every process. -/
  | byzantineCallGIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallG r k b)) (PMF.pure c)
  /-- A corrupted process's coin call (D11): the common coin takes it through the pullback, and
  it is not `j`'s business. -/
  | byzantineCallWIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallW r k)) (PMF.pure c)
  /-- A round multicast is internal to the round instance: not `j`'s business. -/
  | gbcaSendIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) (m : M) :
      RoundLoopStep P j c (Sum.inr (.gbcaSend r k m)) (PMF.pure c)
  /-- A round delivery is internal to the round instance: not `j`'s business. -/
  | gbcaDeliverIdle (c : RoundLoopVariables P.n) (r : ℕ) (i k : Fin P.n) (m : M) :
      RoundLoopStep P j c (Sum.inr (.gbcaDeliver r i k m)) (PMF.pure c)

/-! ### The DECIDED sets, the corrupted set and the started rounds

The network a composed system holds beside its rounds: the DECIDED sets, the corrupted set with
its budget, and the rounds a process outside `F` has started, the rounds at which a corrupted
process calls (D37). -/

/-- The state of the ABA network: the DECIDED sets, the corrupted set and the started rounds. -/
structure ABANetworkState (n : ℕ) : Type where
  /-- `decidedSent j` — the DECIDED payloads process `j` has multicast (D12′). -/
  decidedSent : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- The rounds at which a process outside `F` has called graded agreement, in ABDY22's words
  the rounds a correct process has started (D37). The round instances beside this network exist
  exactly at these rounds, so a corrupted process's call at a round of this set is matched by that
  round's own transitions. -/
  startedRounds : Finset ℕ

namespace ABANetworkState

variable {n : ℕ}

/-- The initial network: nothing multicast, nobody corrupted, no round started. -/
def initial (n : ℕ) : ABANetworkState n where
  decidedSent := fun _ => ∅
  F := ∅
  startedRounds := ∅

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def recordDecided (a : ABANetworkState n) (j : Fin n) (b : Bool) : ABANetworkState n :=
  { a with decidedSent := Function.update a.decidedSent j (insert b (a.decidedSent j)) }

/-- Process `id` starts round `r`: a call by a process outside `F` puts `r` among the started
rounds, and a call by a process in `F` leaves the state as it is (D37). -/
def recordStartedRound (a : ABANetworkState n) (r : ℕ) (id : Fin n) : ABANetworkState n :=
  if id ∉ a.F then { a with startedRounds := insert r a.startedRounds } else a

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Parameters) (id : Fin P.n) (a : ABANetworkState P.n) : ABANetworkState P.n :=
  if id ∉ a.F ∧ a.F.card < P.f then { a with F := insert id a.F } else a

@[simp] theorem recordDecided_decidedSent (a : ABANetworkState n) (j : Fin n) (b : Bool) :
    (a.recordDecided j b).decidedSent = Function.update a.decidedSent j (insert b (a.decidedSent j))
      := rfl

@[simp] theorem recordDecided_F (a : ABANetworkState n) (j : Fin n) (b : Bool) :
    (a.recordDecided j b).F = a.F := rfl

@[simp] theorem recordDecided_startedRounds (a : ABANetworkState n) (j : Fin n) (b : Bool) :
    (a.recordDecided j b).startedRounds = a.startedRounds := rfl

@[simp] theorem recordStartedRound_decidedSent (a : ABANetworkState n) (r : ℕ) (id : Fin n) :
    (a.recordStartedRound r id).decidedSent = a.decidedSent := by
  unfold recordStartedRound; split <;> rfl

@[simp] theorem recordStartedRound_F (a : ABANetworkState n) (r : ℕ) (id : Fin n) :
    (a.recordStartedRound r id).F = a.F := by
  unfold recordStartedRound; split <;> rfl

/-- The started rounds after a call: the call's round enters them at a process outside `F`, and
they stand at a process in `F`. -/
theorem recordStartedRound_startedRounds (a : ABANetworkState n) (r : ℕ) (id : Fin n) :
    (a.recordStartedRound r id).startedRounds =
      if id ∉ a.F then insert r a.startedRounds else a.startedRounds := by
  unfold recordStartedRound; split <;> rfl

theorem recordStartedRound_startedRounds_of_notMem (a : ABANetworkState n) {r : ℕ} {id : Fin n}
    (hid : id ∉ a.F) : (a.recordStartedRound r id).startedRounds = insert r a.startedRounds := by
  rw [recordStartedRound_startedRounds, if_pos hid]

theorem recordStartedRound_startedRounds_of_mem (a : ABANetworkState n) {r : ℕ} {id : Fin n}
    (hid : id ∈ a.F) : (a.recordStartedRound r id).startedRounds = a.startedRounds := by
  rw [recordStartedRound_startedRounds, if_neg (not_not_intro hid)]

/-- A call removes no started round. -/
theorem subset_recordStartedRound_startedRounds (a : ABANetworkState n) (r : ℕ) (id : Fin n) :
    a.startedRounds ⊆ (a.recordStartedRound r id).startedRounds := by
  rw [recordStartedRound_startedRounds]
  split
  · exact Finset.subset_insert r a.startedRounds
  · exact Finset.Subset.refl _

/-- A call by a process outside `F` at round `r` puts `r` among the started rounds. -/
theorem mem_recordStartedRound_startedRounds_self (a : ABANetworkState n) (r : ℕ) {id : Fin n}
    (hid : id ∉ a.F) : r ∈ (a.recordStartedRound r id).startedRounds := by
  rw [recordStartedRound_startedRounds_of_notMem a hid]
  exact Finset.mem_insert_self r a.startedRounds

@[simp] theorem corrupt_decidedSent (P : Parameters) (id : Fin P.n) (a : ABANetworkState P.n) :
    (corrupt P id a).decidedSent = a.decidedSent := by
  unfold corrupt; split <;> rfl

@[simp] theorem corrupt_startedRounds (P : Parameters) (id : Fin P.n)
    (a : ABANetworkState P.n) :
    (corrupt P id a).startedRounds = a.startedRounds := by
  unfold corrupt; split <;> rfl

end ABANetworkState

/-- The step relation of the ABA network. All transitions are Dirac. -/
inductive ABANetworkStep (P : Parameters) {M : Type} [DecidableEq M] :
    ABANetworkState P.n → ExtendedLabel P.n M → PMF (ABANetworkState P.n) → Prop
  /-- The DECIDED relay's half: the payload enters the relaying process's DECIDED set (D12′). -/
  | decidedRelay (a : ABANetworkState P.n) (j : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inr (.decidedRelay j b)) (PMF.pure (a.recordDecided j b))
  /-- The DECIDED delivery's half: the payload must be sent under the named
  sender (D12′). -/
  | decidedDeliver (a : ABANetworkState P.n) (i j : Fin P.n) (b : Bool) (h : b ∈ a.decidedSent j) :
      ABANetworkStep P a (Sum.inr (.decidedDeliver i j b)) (PMF.pure a)
  /-- The DECIDED send's half: the payload enters the sender's DECIDED set (D12′). -/
  | decidedSend (a : ABANetworkState P.n) (j : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inr (.decidedSend j b)) (PMF.pure (a.recordDecided j b))
  /-- A corrupted process's graded-agreement call, output by the network under `k ∈ F` at a round
  a process outside `F` has started; the round instance takes it on its call or its loop (D11,
  D37). -/
  | byzantineCallG (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F)
      (hr : r ∈ a.startedRounds) :
      ABANetworkStep P a (Sum.inr (.byzantineCallG r k b)) (PMF.pure a)
  /-- A corrupted process's coin call, output by the network under `k ∈ F` at a round a process
  outside `F` has started; the common coin takes it on its call or its loop (D11, D37). -/
  | byzantineCallW (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (hF : k ∈ a.F)
      (hr : r ∈ a.startedRounds) :
      ABANetworkStep P a (Sum.inr (.byzantineCallW r k)) (PMF.pure a)
  /-- An external input is not this component's business. -/
  | callABAIdle (a : ABANetworkState P.n) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.callABA id b)) (PMF.pure a)
  /-- A return sends nothing. The condition of a correct return on the DECIDED sends is the round
  loop's own record, and a replaced round loop returns either bit (D23). -/
  | retABAIdle (a : ABANetworkState P.n) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- A graded-agreement call sends nothing; the network records the start of round `r` by a
  process outside `F` (D37). -/
  | callG (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.callG r id b)) (PMF.pure (a.recordStartedRound r id))
  /-- A graded-agreement return sends nothing: not this component's business. -/
  | retGIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (out : GBCAOutput) :
      ABANetworkStep P a (Sum.inl (.retG r id out)) (PMF.pure a)
  /-- The announcement of a round's bound bit is the round instance's: this component holds no
  ghost, and the announcement is not its business (D29). -/
  | boundGIdle (a : ABANetworkState P.n) (r : ℕ) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.boundG r b)) (PMF.pure a)
  /-- A coin call sends nothing. -/
  | callWIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) :
      ABANetworkStep P a (Sum.inl (.callW r id)) (PMF.pure a)
  /-- A coin return sends nothing. -/
  | retWIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) :
      ABANetworkStep P a (Sum.inl (.retW r id c)) (PMF.pure a)
  /-- Corruption (deviations D1, D23): Dirac, and guarded by the budget. The guard sits on the
  transition, so a corruption fires exactly when it takes effect and the round loop's half writes
  the replacement flag outright. -/
  | fail (a : ABANetworkState P.n) (k : Fin P.n) (hnew : k ∉ a.F) (hbud : a.F.card < P.f) :
      ABANetworkStep P a (Sum.inl (.fail k)) (PMF.pure (ABANetworkState.corrupt P k a))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate in the DECIDED sets. -/
  | byzantineDecided (a : ABANetworkState P.n) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inl .tau) (PMF.pure (a.recordDecided k b))

/-! ### The two automata -/

/-- The round-loop program of process `j`. -/
noncomputable def roundLoopProgram (P : Parameters) (M : Type) [DecidableEq M] (j : Fin P.n) :
    System (RoundLoopVariables P.n) (ExtendedLabel P.n M) where
  init := RoundLoopVariables.initial P.n
  step := RoundLoopStep P j

@[simp] theorem roundLoopProgram_init (P : Parameters) (M : Type) [DecidableEq M] (j : Fin P.n) :
    (roundLoopProgram P M j).init = RoundLoopVariables.initial P.n := rfl

@[simp] theorem roundLoopProgram_step (P : Parameters) (M : Type) [DecidableEq M] (j : Fin P.n)
    (c : RoundLoopVariables P.n) (l : ExtendedLabel P.n M) (ν : PMF (RoundLoopVariables P.n)) :
    (roundLoopProgram P M j).step c l ν ↔ RoundLoopStep P j c l ν := Iff.rfl

/-- The ABA network. -/
noncomputable def ABANetwork (P : Parameters) (M : Type) [DecidableEq M] :
    System (ABANetworkState P.n) (ExtendedLabel P.n M) where
  init := ABANetworkState.initial P.n
  step := ABANetworkStep P

@[simp] theorem ABANetwork_init (P : Parameters) (M : Type) [DecidableEq M] :
    (ABANetwork P M).init = ABANetworkState.initial P.n := rfl

@[simp] theorem ABANetwork_step (P : Parameters) (M : Type) [DecidableEq M]
    (a : ABANetworkState P.n) (l : ExtendedLabel P.n M) (μ : PMF (ABANetworkState P.n)) :
    (ABANetwork P M).step a l μ ↔ ABANetworkStep P a l μ := Iff.rfl

/-! ### Determinacy of the two step relations -/

/-- Every round-loop transition is Dirac. -/
theorem roundLoopStep_dirac {P : Parameters} {M : Type} [DecidableEq M] {j : Fin P.n}
    {c : RoundLoopVariables P.n}
    {l : ExtendedLabel P.n M} {ν : PMF (RoundLoopVariables P.n)} (h : RoundLoopStep P j c l ν) :
    ∃ c', ν = PMF.pure c' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every ABA network transition is Dirac. -/
theorem abaNetworkStep_dirac {P : Parameters} {M : Type} [DecidableEq M]
    {a : ABANetworkState P.n} {l : ExtendedLabel P.n M}
    {μ : PMF (ABANetworkState P.n)} (h : ABANetworkStep P a l μ) : ∃ a', μ = PMF.pure a' := by
  cases h <;> exact ⟨_, rfl⟩

/-- No round-loop transition fires on `τ`: a round loop only ever moves on a
network event or on a shared API label. -/
theorem roundLoopStep_no_tau {P : Parameters} {M : Type} [DecidableEq M] {j : Fin P.n}
    {c : RoundLoopVariables P.n}
    {ν : PMF (RoundLoopVariables P.n)} (h : RoundLoopStep P j c (Silent.τ : ExtendedLabel P.n M) ν)
      :
    False := by
  rw [extendedLabel_tau] at h
  cases h
  rename_i hτ _
  exact hτ rfl

/-! ### Reading and building a transition of the round-loop group -/

/-- A synchronised transition of the round-loop group on a visible label. -/
theorem roundLoopProduct_cases {P : Parameters} {M : Type} [DecidableEq M]
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {l : ExtendedLabel P.n M} {μ : PMF (∀ _ : Fin P.n, RoundLoopVariables P.n)}
    (h : (System.synchronisedProduct (roundLoopProgram P M)).step C l μ) :
    ∃ y : ∀ _ : Fin P.n, RoundLoopVariables P.n, μ = PMF.pure y ∧ ∀ i, RoundLoopStep P i (C i) l
    (PMF.pure (y i)) := by
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
theorem roundLoopProduct_pure {P : Parameters} {M : Type} [DecidableEq M]
    {C y : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {l : ExtendedLabel P.n M} (hl : l ≠ Silent.τ)
    (h : ∀ i, RoundLoopStep P i (C i) l (PMF.pure (y i))) :
    (System.synchronisedProduct (roundLoopProgram P M)).step C l (PMF.pure y) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (y i), h, (piPMF_pure y).symm⟩

/-- The round-loop group has no silent transition. -/
theorem roundLoopProduct_no_tau {P : Parameters} {M : Type} [DecidableEq M]
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n} {μ : PMF (∀ _ : Fin P.n, RoundLoopVariables P.n)}
    (h : (System.synchronisedProduct (roundLoopProgram P M)).step C
      (Silent.τ : ExtendedLabel P.n M) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact roundLoopStep_no_tau hstep

/-! ### One round loop's transitions, by label class

Each lemma determines a transition of `RoundLoopStep` from its label: the participant's
transition as its guards together with the Dirac it produces, the loop of an input where the
guards fail, and the idle transition of a non-participant as the identity. A participant's
transition carries the replacement guard `corrupted = false`, and on a label outside
`roundLoopActsAt j` the replaced program's self-loop is a further transition on the same label
(D23). -/

section RoundLoopCases

variable {P : Parameters} {M : Type} [DecidableEq M] {j : Fin P.n} {c : RoundLoopVariables P.n}
  {ν : PMF (RoundLoopVariables P.n)}

theorem roundLoopStep_callABA_own {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.callABA j b) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ c.processVariables.input = none ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with
        input := some b, estimate := some b, round := 0, phase := .toCallG })) ∨
    ((c.corrupted = true ∨ c.processVariables.input ≠ none) ∧ ν = PMF.pure c) := by
  cases h
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem roundLoopStep_callABA_notOwn {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callABA id b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_retABA_own {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retABA j b) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ P.n - P.f ≤ c.decidedCount b ∧ b ∈ c.decidedSent ∧
      c.processVariables.returned = false ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with returned := true })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case ret => exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_retABA_notOwn {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retABA id b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_callG_own {r : ℕ} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.callG r j b) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ c.processVariables.phase = .toCallG ∧ c.processVariables.round = r ∧
      c.processVariables.estimate = some b ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }) := by
  cases h
  case callG =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_callG_notOwn {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callG r id b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case callG => exact absurd rfl hid
  case callGIdle => rfl
  case corruptedIdle => rfl

/-- The round's return at `j`: the return at the phase and the round it waits for, and a
self-loop elsewhere or at a replaced program. -/
theorem roundLoopStep_retG_own {r : ℕ} {out : GBCAOutput}
    (h : RoundLoopStep P j c (Sum.inl (.retG r j out) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ c.processVariables.phase = .awaitG ∧ c.processVariables.round = r ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW })) ∨
    ((c.corrupted = true ∨ ¬ (c.processVariables.phase = .awaitG ∧ c.processVariables.round = r))
      ∧ ν = PMF.pure c) := by
  cases h
  case retG => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case retGLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem roundLoopStep_retG_notOwn {r : ℕ} {id : Fin P.n} {out : GBCAOutput} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retG r id out) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case retG => exact absurd rfl hid
  case retGLoop => exact absurd rfl hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_boundG {r : ℕ} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.boundG r b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_callW_own {r : ℕ}
    (h : RoundLoopStep P j c (Sum.inl (.callW r j) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ c.processVariables.phase = .toCallW ∧ c.processVariables.round = r ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitW }) := by
  cases h
  case callW => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_callW_notOwn {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callW r id) : ExtendedLabel P.n M) ν) : ν = PMF.pure c := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

/-- The coin's return at `j`: the round advance at the phase and the round it waits for, and a
self-loop elsewhere or at a replaced program. -/
theorem roundLoopStep_retW_own {r : ℕ} {co : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retW r j co) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ c.processVariables.phase = .awaitW ∧ c.processVariables.round = r ∧
      ν = PMF.pure (c.stepRound co)) ∨
    ((c.corrupted = true ∨ ¬ (c.processVariables.phase = .awaitW ∧ c.processVariables.round = r))
      ∧ ν = PMF.pure c) := by
  cases h
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem roundLoopStep_retW_notOwn {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retW r id co) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case retW => exact absurd rfl hid
  case retWLoop => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag is set on a program not yet
replaced, and a replaced program is unchanged. -/
theorem roundLoopStep_fail_own (h : RoundLoopStep P j c (Sum.inl (.fail j) :
    ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ ν = PMF.pure { c with corrupted := true }) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_fail_notOwn {k : Fin P.n} (hk : k ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.fail k) : ExtendedLabel P.n M) ν) : ν = PMF.pure c := by
  cases h
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_decidedRelay_self {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedRelay j b) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ P.f + 1 ≤ c.decidedCount b ∧ b ∉ c.decidedSent ∧
      ν = PMF.pure (c.recordDecided b)) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case decidedRelay => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case decidedRelayIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_decidedRelay_notOwn {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.decidedRelay k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case decidedRelay => exact absurd rfl hk
  case decidedRelayIdle => rfl
  case corruptedIdle => rfl

/-- A DECIDED delivery to `j`: the receipt of a payload not held from the sender, and a
self-loop at a payload already held or at a replaced program. -/
theorem roundLoopStep_decidedDeliver_self {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ b ∉ c.decidedDelivered k ∧ ν = PMF.pure (c.receiveDecided k b)) ∨
    ((c.corrupted = true ∨ b ∈ c.decidedDelivered k) ∧ ν = PMF.pure c) := by
  cases h
  case decidedDeliverReceive => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case decidedDeliverLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case decidedDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem roundLoopStep_decidedDeliver_notOwn {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.decidedDeliver i k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case decidedDeliverReceive => exact absurd rfl hi
  case decidedDeliverLoop => exact absurd rfl hi
  case decidedDeliverIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_decidedSend_self {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedSend j b) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ c.processVariables.phase = .toSendDecided ∧
      c.processVariables.lastGrade = some (.grade2 b) ∧
      ν = PMF.pure ((c.setProcessVariables
        { c.processVariables with lastGrade := none, phase := .toCallG }).recordDecided b) := by
  cases h
  case decidedSend => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case decidedSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_decidedSend_notOwn {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : RoundLoopStep P j c (Sum.inr (.decidedSend k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case decidedSend => exact absurd rfl hk
  case decidedSendIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineCallG r k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineCallW r k) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_gbcaSend {r : ℕ} {k : Fin P.n} {m : M}
    (h : RoundLoopStep P j c (Sum.inr (.gbcaSend r k m) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_gbcaDeliver {r : ℕ} {i k : Fin P.n} {m : M}
    (h : RoundLoopStep P j c (Sum.inr (.gbcaDeliver r i k m) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a round
loop whose flag is set leaves its variables unchanged. The proof is by cases
on the algorithm: every transition that writes carries the replacement guard `corrupted = false`, so
every transition of a replaced program is a self-loop. -/
theorem roundLoopStep_noStep {L : ExtendedLabel P.n M} (hc : c.corrupted = true)
    (h : RoundLoopStep P j c L ν) : ν = PMF.pure c := by
  cases h <;> simp_all

end RoundLoopCases

/-! ### The ABA network's transitions, by label class -/

section ABANetworkStepCases
variable {P : Parameters} {M : Type} [DecidableEq M] {a : ABANetworkState P.n}
  {μ : PMF (ABANetworkState P.n)}

theorem abaNetworkStep_decidedRelay {j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedRelay j b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure (a.recordDecided j b) := by
  cases h; rfl

theorem abaNetworkStep_decidedDeliver {i j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedDeliver i j b) : ExtendedLabel P.n M) μ) :
    b ∈ a.decidedSent j ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_decidedSend {j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedSend j b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure (a.recordDecided j b) := by
  cases h; rfl

theorem abaNetworkStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallG r k b) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ r ∈ a.startedRounds ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem abaNetworkStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallW r k) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ r ∈ a.startedRounds ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem abaNetworkStep_callABA {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.callABA id b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_retABA {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.retABA id b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

/-- A graded-agreement call records the start of its round by a process outside `F` (D37). -/
theorem abaNetworkStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.callG r id b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure (a.recordStartedRound r id) := by
  cases h; rfl

theorem abaNetworkStep_retG {r : ℕ} {id : Fin P.n} {out : GBCAOutput}
    (h : ABANetworkStep P a (Sum.inl (.retG r id out) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_boundG {r : ℕ} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.boundG r b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_callW {r : ℕ} {id : Fin P.n}
    (h : ABANetworkStep P a (Sum.inl (.callW r id) : ExtendedLabel P.n M) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : ABANetworkStep P a (Sum.inl (.retW r id c) : ExtendedLabel P.n M) μ) : μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_fail {k : Fin P.n}
    (h : ABANetworkStep P a (Sum.inl (.fail k) : ExtendedLabel P.n M) μ) :
    k ∉ a.F ∧ a.F.card < P.f ∧ μ = PMF.pure (ABANetworkState.corrupt P k a) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem abaNetworkStep_tau (h : ABANetworkStep P a (Sum.inl .tau : ExtendedLabel P.n M) μ) :
    ∃ (k : Fin P.n) (b : Bool), k ∈ a.F ∧ μ = PMF.pure (a.recordDecided k b) := by
  cases h
  case byzantineDecided => exact ⟨_, _, by assumption, rfl⟩

theorem abaNetworkStep_gbcaSend_noStep {r : ℕ} {k : Fin P.n} {m : M}
    (h : ABANetworkStep P a (Sum.inr (.gbcaSend r k m) : ExtendedLabel P.n M) μ) :
    False := by cases h

theorem abaNetworkStep_gbcaDeliver_noStep {r : ℕ} {i k : Fin P.n} {m : M}
    (h : ABANetworkStep P a (Sum.inr (.gbcaDeliver r i k m) : ExtendedLabel P.n M) μ) :
    False := by cases h

end ABANetworkStepCases

/-! ### Determining the round-loop tuple -/

theorem roundLoopVariables_update {P : Parameters} {C y : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {id : Fin P.n} {nd : RoundLoopVariables P.n}
    (hown : (PMF.pure (y id) : PMF (RoundLoopVariables P.n)) = PMF.pure nd)
    (hfor : ∀ i, i ≠ id → (PMF.pure (y i) : PMF (RoundLoopVariables P.n)) = PMF.pure (C i)) :
    y = Function.update C id nd := by
  funext i
  by_cases hi : i = id
  · subst hi; rw [Function.update_self]; exact pure_inj hown
  · rw [Function.update_of_ne hi]; exact pure_inj (hfor i hi)

theorem roundLoopVariables_id {P : Parameters} {C y : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    (hall : ∀ i, (PMF.pure (y i) : PMF (RoundLoopVariables P.n)) = PMF.pure (C i)) : y = C :=
  funext fun i => pure_inj (hall i)

/-- One round loop moves and every other idles. -/
theorem roundLoopVariables_family {P : Parameters} {M : Type} [DecidableEq M]
    {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
    {L : ExtendedLabel P.n M} (id : Fin P.n) (nd : RoundLoopVariables P.n)
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
