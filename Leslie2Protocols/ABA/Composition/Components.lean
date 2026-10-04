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
message networks, the Byzantine call and return transitions, or the branches of a call or return
that it does not distinguish. `NetworkEvent n M` names them, over the type `M` of the
messages a graded-agreement round exchanges (`ABA/Implementation/Alphabet.lean`), and
`ExtendedLabel n M = Label n ⊕ NetworkEvent n M` is the alphabet of every component here. Its
silent label is `Sum.inl τ`, so every `Sum.inr` label is observable, and `networkEventLabels n` —
the set of all of them — is what both compositions hide before reading the result back over
`Label n`.

## The common coin

The common coin `WCC.specFamily` is over `Label n`, so it is joined to the extended alphabet through
the label pullback `coinLabelMap`, which sends a shared label to itself, the Byzantine call and
return transitions to the coin's own call and return transitions, and every other network event
out of the domain. `τ` is a shared label, so the coin's resolution is a silent transition of the
coin read along the pullback. `coinOverRoundAlphabet` is the coin read along that
pullback at this alphabet. It is a component of both compositions, unchanged.

## The round loop of one process

`RoundLoopStep` is the step relation of one process's round loop: the API transitions `callABA` and
`retABA`, the graded-agreement and coin calls and returns, the DECIDED send, the DECIDED relay and
its delivery, and
an idle transition for every label the process does not act on. It writes no round variables. The
composed system runs `n` of these automata (`roundLoopProgram`) under a full-synchronisation
product. The protocol composition pairs each round loop with the round variables into one program
(`ABDY.ABAProgramStep`), whose variables are the pair.

A corruption replaces the program of the process it names (D23). The flag
`RoundLoopVariables.corrupted` goes up on the process's own half of `fail`, every participant's
transition is guarded by `corrupted = false`, and the replaced program is the single self-loop
`corruptedIdle`. The replaced program has no transition on the labels of `actsAt j` — the labels on
which the process would act on its own sub-protocol messages — so those messages enter only through
the Byzantine call and return transitions (D11).

## The ABA network

`ABANetworkStep` is what the network retains once the round networks have taken the round
sent sets: the DECIDED sets `decidedSent j`, the corrupted set `F` with its budget, and the
authorisation of every Byzantine call and return transition. `ABANetwork` is that automaton. Its
`fail`
transition carries the budget guard `k ∉ F ∧ |F| < f`, so a corruption fires exactly when it takes
effect, and its `retByzantine` transition lets a corrupted process return without having multicast
`⟨DECIDED, b⟩`, pairing with the replaced program's self-loop on `retABA` (D23). It holds no
ghost: the bound
bit a graded-agreement return announces belongs to the round, so the round's instance carries it and
both transitions here idle on it.

## What this file supplies

The two step relations above, the two automata they carry, the determinacy of both, and the lemmas
that read a transition of each off its label (`roundLoopStep_*`, `abaNetworkStep_*`) — among them
`roundLoopStep_noStep`, which reads every transition of a replaced program as a self-loop. It also
supplies the systems of the synchronised round-loop group in both directions
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
    System (ℕ → WCC.SpecState P.n) (ExtendedLabel P.n M) :=
  coinOverExtendedAlphabet P M Empty

@[simp] theorem coinOverRoundAlphabet_init (P : Parameters) (M : Type) [DecidableEq M] :
    (coinOverRoundAlphabet P M).init = (WCC.specFamily P).init := rfl

/-! ## The component vocabulary

Everything the component boundary names lives under `PLTS.ABA.Composition`, so
that `PLTS.ABA` itself carries only what the chain cites. -/

/-! ### The round-loop program of one process

The automaton that calls a round's graded-agreement instance and the coin, and decides. It writes no
round variables: the five multicast levels and the round delivery are internal to a round instance,
so
they leave no transition here, and the three Byzantine graded-agreement transitions change no
round-loop data, which is why they appear below only as idle transitions.

The programs sit under a full-synchronisation product, so every label that can fire in the composite
has a transition: the participant's, or an idle one. Unlike the round-indexed families, these
programs are not round-filtered. A round loop must answer every round's `callG`, its own as a
participant and every other process's as a bystander.

A corruption replaces the program of the process it names (D23). The replacement is carried by the
flag `RoundLoopVariables.corrupted`, which `failSelf` writes on the process's own `fail`; every
participant's transition is guarded by `corrupted = false`, so the variables stay as they are at the
corruption. In place of those transitions the replaced program has the single transition
`corruptedIdle`: a self-loop on every label other than `τ` and the labels of `actsAt j`. On the
latter the replaced program has no transition at all, so those labels cannot fire; the corrupted
process's graded-agreement messages enter through the Byzantine call and return transitions (D11)
and
its DECIDED messages through `byzantineDecided`. -/

/-- The step relation of the round-loop program of process `j`. -/
inductive RoundLoopStep (P : Parameters) {M : Type} [DecidableEq M] (j : Fin P.n) :
    RoundLoopVariables P.n → ExtendedLabel P.n M → PMF (RoundLoopVariables P.n) → Prop
  /-- `upon ABA(b)`: record input and estimate, open round `0`. -/
  | input (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (h : c.processVariables.input = none) :
      RoundLoopStep P j c (Sum.inl (.callABA j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with
          input := some b, estimate := some b, round := 0, phase := .toCallG }))
  /-- Input-enabledness loop on `j`'s own `callABA`: the loop absorbs a call at
  a process holding an input. The `input` transition carries the label at a
  process holding none, so the label is enabled in every state and a first call
  at a process whose program stands commits (D36). -/
  | inputLoop (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hin : c.processVariables.input ≠ none) :
      RoundLoopStep P j c (Sum.inl (.callABA j b)) (PMF.pure c)
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : RoundLoopVariables P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callABA id b)) (PMF.pure c)
  /-- Return `b` on an `n − f` DECIDED quorum. Having multicast `b` oneself is
  a condition on the DECIDED sets, hence `ABANetwork`'s conjunct. -/
  | ret (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hret : c.processVariables.returned = false) :
      RoundLoopStep P j c (Sum.inl (.retABA j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with returned := true }))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : RoundLoopVariables P.n) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retABA id b)) (PMF.pure c)
  /-- The graded-agreement call, round-loop half: hand the estimate over and wait. Opening the round
  variables is the round instance's half. -/
  | callG (c : RoundLoopVariables P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hest : c.processVariables.estimate = some b) :
      RoundLoopStep P j c (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.callG r id b)) (PMF.pure c)
  /-- The graded-agreement return, round-loop half: record the grade and head
  for the coin. The witness for the grade is the round instance's conjunct.
  The round's bound bit is announced beside the grade and written nowhere: the
  round loop is one of the programs that do not read it. -/
  | retG (c : RoundLoopVariables P.n) (r : ℕ) (out : GBCAOutput) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitG) (hr : c.processVariables.round = r) :
      RoundLoopStep P j c (Sum.inl (.retG r j out bnd))
        (PMF.pure (c.setProcessVariables { c.processVariables with
          estimate := out.estimate, lastGrade := some out, phase := .toCallW }))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
      (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inl (.retG r id out bnd)) (PMF.pure c)
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
  the labels of `actsAt j`, on which the process has no transition at all. -/
  | corruptedIdle (c : RoundLoopVariables P.n) (L : ExtendedLabel P.n M) (hh : c.corrupted = true)
      (hτ : L ≠ Sum.inl Label.tau) (hown : ¬ actsAt j L) :
      RoundLoopStep P j c L (PMF.pure c)
  /-- The DECIDED relay on an `f + 1` quorum (D12′): the quorum is a condition
  on the variables, the write-once condition and the sent insert are `ABANetwork`'s. -/
  | decidedRelay (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hcnt : P.f + 1 ≤ c.decidedCount b) :
      RoundLoopStep P j c (Sum.inr (.decidedRelay j b)) (PMF.pure c)
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | decidedRelayIdle (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedRelay k b)) (PMF.pure c)
  /-- DECIDED delivery, receiver's half: at most one received message per (sender, bit)
  (D12′). Authenticity is `ABANetwork`'s conjunct. -/
  | decidedDeliverReceive (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool) (hh : c.corrupted =
    false)
      (hr : b ∉ c.decidedDelivered k) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b)) (PMF.pure (c.receiveDecided k b))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | decidedDeliverIdle (c : RoundLoopVariables P.n) (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedDeliver i k b)) (PMF.pure c)
  /-- The DECIDED send of a grade-2 round: the outcome of the round just closed was
  `grade2 b`, so the process sends `⟨DECIDED, b⟩` to all, clears the grade and enters the next
  round's `toCallG`. The sent insert is `ABANetwork`'s half. -/
  | decidedSend (c : RoundLoopVariables P.n) (b : Bool) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toSendDecided)
      (hgr : c.processVariables.lastGrade = some (.grade2 b)) :
      RoundLoopStep P j c (Sum.inr (.decidedSend j b))
        (PMF.pure (c.setProcessVariables
          { c.processVariables with lastGrade := none, phase := .toCallG }))
  /-- A DECIDED send by another process: not `j`'s business. -/
  | decidedSendIdle (c : RoundLoopVariables P.n) (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      RoundLoopStep P j c (Sum.inr (.decidedSend k b)) (PMF.pure c)
  /-- The graded-agreement call against a round already called: the round loop moves and
  nothing else does — the whole transition is core content. -/
  | gbcaCallLoop (c : RoundLoopVariables P.n) (r : ℕ) (b : Bool) (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hest : c.processVariables.estimate = some b) :
      RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }))
  /-- Such a call at another process: not `j`'s business. -/
  | gbcaCallLoopIdle (c : RoundLoopVariables P.n) (r : ℕ) (id : Fin P.n) (b : Bool)
      (hid : id ≠ j) :
      RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r id b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call (D11) writes round variables and no round-loop data: every
  round loop, the named one included, is unchanged. -/
  | byzantineCallGIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallG r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement call against a round already called (D11): nothing moves
  anywhere. -/
  | byzantineCallGLoopIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallGLoop r k b)) (PMF.pure c)
  /-- A Byzantine graded-agreement return (D11): round content only. -/
  | byzantineRetGIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) (out : GBCAOutput)
      (bnd : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineRetG r k out bnd)) (PMF.pure c)
  /-- A Byzantine coin call (D11): the common coin reacts through the pullback. -/
  | byzantineCallWIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) :
      RoundLoopStep P j c (Sum.inr (.byzantineCallW r k)) (PMF.pure c)
  /-- A Byzantine coin return (D11): the common coin reacts through the
  pullback. -/
  | byzantineRetWIdle (c : RoundLoopVariables P.n) (r : ℕ) (k : Fin P.n) (b : Bool) :
      RoundLoopStep P j c (Sum.inr (.byzantineRetW r k b)) (PMF.pure c)

/-! ### The DECIDED sets and the corrupted set

What is left of the network once the round-tagged sent sets have gone to
the round networks: the DECIDED sets, the corrupted set with its budget, and
the authorisation of every Byzantine call and return transition. -/

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
inductive ABANetworkStep (P : Parameters) {M : Type} [DecidableEq M] :
    ABANetworkState P.n → ExtendedLabel P.n M → PMF (ABANetworkState P.n) → Prop
  /-- The DECIDED relay's half: the payload must not be sent yet (D12′). -/
  | decidedRelay (a : ABANetworkState P.n) (j : Fin P.n) (b : Bool) (h : b ∉ a.decidedSent j) :
      ABANetworkStep P a (Sum.inr (.decidedRelay j b)) (PMF.pure (a.recordDecided j b))
  /-- The DECIDED delivery's half: the payload must be sent under the named
  sender (D12′). -/
  | decidedDeliver (a : ABANetworkState P.n) (i j : Fin P.n) (b : Bool) (h : b ∈ a.decidedSent j) :
      ABANetworkStep P a (Sum.inr (.decidedDeliver i j b)) (PMF.pure a)
  /-- The DECIDED send's half: the payload enters the sender's DECIDED set (D12′). -/
  | decidedSend (a : ABANetworkState P.n) (j : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inr (.decidedSend j b)) (PMF.pure (a.recordDecided j b))
  /-- A graded-agreement call against a round already called sends nothing. -/
  | gbcaCallLoop (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inr (.gbcaCallLoop r id b)) (PMF.pure a)
  /-- The authorisation of a Byzantine graded-agreement call (D11): the round
  instance carries the effect, this component carries the guard. -/
  | byzantineCallG (a : ABANetworkState P.n) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ a.F) :
      ABANetworkStep P a (Sum.inr (.byzantineCallG r k b)) (PMF.pure a)
  /-- The authorisation of a Byzantine call against a round already called (D11). -/
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
  replaced, so the multicast of `⟨DECIDED, b⟩` the correct transition asks for is
  not required of it. The authorisation is this component's `id ∈ F`, and the round
  loop's half is the replaced program's self-loop. -/
  | retByzantine (a : ABANetworkState P.n) (id : Fin P.n) (b : Bool) (hF : id ∈ a.F) :
      ABANetworkStep P a (Sum.inl (.retABA id b)) (PMF.pure a)
  /-- A graded-agreement call sends nothing. -/
  | callGIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (b : Bool) :
      ABANetworkStep P a (Sum.inl (.callG r id b)) (PMF.pure a)
  /-- A graded-agreement return sends nothing, and the bound bit it
  announces is the round instance's: this component holds no ghost. -/
  | retGIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
      (bnd : Bool) :
      ABANetworkStep P a (Sum.inl (.retG r id out bnd)) (PMF.pure a)
  /-- A coin call sends nothing. -/
  | callWIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) :
      ABANetworkStep P a (Sum.inl (.callW r id)) (PMF.pure a)
  /-- A coin return sends nothing. -/
  | retWIdle (a : ABANetworkState P.n) (r : ℕ) (id : Fin P.n) (c : Bool) :
      ABANetworkStep P a (Sum.inl (.retW r id c)) (PMF.pure a)
  /-- Corruption (deviations D1, D23): Dirac, and guarded by the budget. The
  guard sits on the transition rather than inside `ABANetworkState.corrupt`
  alone, so that a corruption fires exactly when it takes effect and the round
  loop's half may write the replacement flag outright. -/
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

Each lemma reads a transition of `RoundLoopStep` off its label: the participant's transition as its
guards together with the Dirac it produces, and the idle transition of a non-participant as the
identity. A participant's transition carries the health guard `corrupted = false`, and on a label
outside `actsAt j` the replaced program's self-loop is a second transition on the same label
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
    (c.corrupted = false ∧ P.n - P.f ≤ c.decidedCount b ∧
      c.processVariables.returned = false ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with returned := true })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case ret => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
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

theorem roundLoopStep_retG_own {r : ℕ} {out : GBCAOutput} {bnd : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retG r j out bnd) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ c.processVariables.phase = .awaitG ∧ c.processVariables.round = r ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with
        estimate := out.estimate, lastGrade := some out, phase := .toCallW }) := by
  cases h
  case retG => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_retG_notOwn {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.retG r id out bnd) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case retG => exact absurd rfl hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_callW_own {r : ℕ}
    (h : RoundLoopStep P j c (Sum.inl (.callW r j) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ c.processVariables.phase = .toCallW ∧ c.processVariables.round = r ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitW })) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_callW_notOwn {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : RoundLoopStep P j c (Sum.inl (.callW r id) : ExtendedLabel P.n M) ν) : ν = PMF.pure c := by
  cases h
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_retW_own {r : ℕ} {co : Bool}
    (h : RoundLoopStep P j c (Sum.inl (.retW r j co) : ExtendedLabel P.n M) ν) :
    (c.corrupted = false ∧ c.processVariables.phase = .awaitW ∧ c.processVariables.round = r ∧
      ν = PMF.pure (c.stepRound co)) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_retW_notOwn {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
(h : RoundLoopStep P j c (Sum.inl (.retW r id co) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
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
    (c.corrupted = false ∧ P.f + 1 ≤ c.decidedCount b ∧ ν = PMF.pure c) ∨
    (c.corrupted = true ∧ ν = PMF.pure c) := by
  cases h
  case decidedRelay => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case decidedRelayIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem roundLoopStep_decidedRelay_notOwn {k : Fin P.n} {b : Bool} (hk : k ≠ j)
(h : RoundLoopStep P j c (Sum.inr (.decidedRelay k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case decidedRelay => exact absurd rfl hk
  case decidedRelayIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_decidedDeliver_self {k : Fin P.n} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedDeliver j k b) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ b ∉ c.decidedDelivered k ∧ ν = PMF.pure (c.receiveDecided k b) := by
  cases h
  case decidedDeliverReceive => exact ⟨by assumption, by assumption, rfl⟩
  case decidedDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_decidedDeliver_notOwn {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
(h : RoundLoopStep P j c (Sum.inr (.decidedDeliver i k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case decidedDeliverReceive => exact absurd rfl hi
  case decidedDeliverIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_decidedSend_self {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.decidedSend j b) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ c.processVariables.phase = .toSendDecided ∧
      c.processVariables.lastGrade = some (.grade2 b) ∧
      ν = PMF.pure (c.setProcessVariables
        { c.processVariables with lastGrade := none, phase := .toCallG }) := by
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

theorem roundLoopStep_gbcaCallLoop_self {r : ℕ} {b : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r j b) : ExtendedLabel P.n M) ν) :
    c.corrupted = false ∧ c.processVariables.phase = .toCallG ∧ c.processVariables.round = r ∧
      c.processVariables.estimate = some b ∧
      ν = PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }) := by
  cases h
  case gbcaCallLoop =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gbcaCallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem roundLoopStep_gbcaCallLoop_notOwn {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
(h : RoundLoopStep P j c (Sum.inr (.gbcaCallLoop r id b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h
  case gbcaCallLoop => exact absurd rfl hid
  case gbcaCallLoopIdle => rfl
  case corruptedIdle => rfl

theorem roundLoopStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
(h : RoundLoopStep P j c (Sum.inr (.byzantineCallG r k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
(h : RoundLoopStep P j c (Sum.inr (.byzantineCallGLoop r k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineRetG {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : RoundLoopStep P j c (Sum.inr (.byzantineRetG r k out bnd) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineCallW {r : ℕ} {k : Fin P.n}
(h : RoundLoopStep P j c (Sum.inr (.byzantineCallW r k) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

theorem roundLoopStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
(h : RoundLoopStep P j c (Sum.inr (.byzantineRetW r k b) : ExtendedLabel P.n M) ν) :
    ν = PMF.pure c := by
  cases h <;> rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a round
loop whose flag is up leaves its variables where they stand. The proof is by cases
on the algorithm: every transition that writes carries the health guard, so no
transition of a replaced program survives except a self-loop. -/
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
    b ∉ a.decidedSent j ∧ μ = PMF.pure (a.recordDecided j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_decidedDeliver {i j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedDeliver i j b) : ExtendedLabel P.n M) μ) :
    b ∈ a.decidedSent j ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_decidedSend {j : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.decidedSend j b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure (a.recordDecided j b) := by
  cases h; rfl

theorem abaNetworkStep_gbcaCallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
(h : ABANetworkStep P a (Sum.inr (.gbcaCallLoop r id b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallG r k b) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallGLoop r k b) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineRetG {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineRetG r k out bnd) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : ABANetworkStep P a (Sum.inr (.byzantineCallW r k) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inr (.byzantineRetW r k b) : ExtendedLabel P.n M) μ) :
    k ∈ a.F ∧ μ = PMF.pure a := by
  cases h; exact ⟨by assumption, rfl⟩

theorem abaNetworkStep_callABA {id : Fin P.n} {b : Bool}
(h : ABANetworkStep P a (Sum.inl (.callABA id b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

/-- A return is authorised either by the DECIDED sent of the returning process
or by its corruption (D23); the two transitions share the label and the
identity successor. -/
theorem abaNetworkStep_retABA {id : Fin P.n} {b : Bool}
    (h : ABANetworkStep P a (Sum.inl (.retABA id b) : ExtendedLabel P.n M) μ) :
    (b ∈ a.decidedSent id ∨ id ∈ a.F) ∧ μ = PMF.pure a := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByzantine => exact ⟨Or.inr (by assumption), rfl⟩

theorem abaNetworkStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
(h : ABANetworkStep P a (Sum.inl (.callG r id b) : ExtendedLabel P.n M) μ) :
    μ = PMF.pure a := by
  cases h; rfl

theorem abaNetworkStep_retG {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
(h : ABANetworkStep P a (Sum.inl (.retG r id out bnd) : ExtendedLabel P.n M) μ) :
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
