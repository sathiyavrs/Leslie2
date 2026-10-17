# Composition — why the chains are cut where they are

The ABA case study relates two protocols, each as it runs, to one small specification:

```
ABDY.protocol  ⊑  ABDY.composed                                  ⊑  hybrid  ⊑  ABA.spec
 AFW.protocol  ⊑   AFW.composed  ⊑  AFW.composedOverBroadcastSpecification  ⊑  AFW.composedOverGatherSpecifications  ⊑  hybrid  ⊑  ABA.spec
```

A protocol is what runs: `n` programs beside a network and the common coin. A program reads
its own replacement flag and nothing else about corruption: not the corrupted set, not the budget,
not another process's status (D23). A composed system is the same protocol read as a composition of
components. `hybrid` replaces each round's graded-agreement instance by the graded agreement
specification, and is where the two chains meet: every inclusion above it is shared. `ABA.spec` is
the single-automaton system of agreement.

The two protocols differ only in how graded agreement is implemented. `ABDY.protocol` runs
ABDY22's Algorithm 6 (D18), which calls no sub-protocol, so one substitution takes it to
`hybrid`. `AFW.protocol` runs AFW25's two-gather construction over reliable broadcast (D24),
so the recursion continues two levels further and its chain carries three.

This note records why the cut is placed where it is, what it gives, and what the model already
weakens. The systems themselves are in `ABA/ABDY/System.lean`,
`ABA/AFW/System.lean` and `ABA/Specifications/ABA.lean`;
`ABA/Composition/Hybrid.lean` carries `hybrid` over the components of
`ABA/Composition/Components.lean`, `ABA/ABDY/Composition.lean` carries
`ABDY.composed` over the same components and `ABA/ABDY/Substitution.lean` the one stage
above it, and
`ABA/AFW/Composition.lean` carries the three gather-based composed systems and
`ABA/AFW/Substitution.lean` the three stages over them. The first
inclusions are `ABA/ABDY/Simulation.lean` and
`ABA/AFW/Simulation.lean`. The file
guide is `ABA/README.md`, and the gather stack's own proofs are `DESIGN-GatherComposition.md`.

## The first inclusion

The first inclusion is where a chain passes from implementation to specification: a protocol is the
system that runs, and everything above it is specification. Both first inclusions are therefore
inclusions, `ABDY.protocol_composed` and `AFW.protocol_composed`, and not equalities.

The two protocols are one construction. What the protocol fixes — the round loop, the DECIDED
sets, the coin's call and return, corruption, the network and the composition pipeline — is
settled by the round interface and the specification, so `ABA/Implementation/System.lean` writes it
once, parametric in the round message type, the per-process per-round variables, the round's
transitions and the adversary's per-round ghost (D30). `ABA/ABDY/System.lean` and
`ABA/AFW/System.lean` supply the two instances.

The variables of a process in a protocol are the round-loop variables, its variables in every
round it has touched, and a flag saying whether it has terminated (D22). A composed
state carries the graded-agreement instances of the rounds its family has touched in a finite map,
every other round reading the initial instance under the recorded corruptions, and no termination
flag.
`ABDY.ProtocolRelation` and `AFW.ProtocolRelation` determine every composed coordinate from the
protocol state but one: a round instance's local states are the round variables the processes hold
for that round, its network states are the adversary's sent sets for it, and the ABA network is
the protocol network's DECIDED sets beside its corrupted set and its started rounds. The coordinate
left free is the family's list of the broadcasts it has applied, which the protocol state does not
hold. The rounds of the family's map are exactly the started rounds, the rounds at which a process
outside `F` has called graded agreement (D37). Two conjuncts of each relation are invariants of
the protocol state: at a round outside the started rounds no process has sent, the ghost holds
nothing and no process holds variables, and every process of the corrupted set has a replaced
program. Together they place every round a transition touches among the started rounds, where the
family takes its silent transitions. `AFW.ProtocolRelation` carries one further conjunct,
`AFW.BoundInvariant`, which is not a projection of the protocol state: a process holding a
candidate has the first gather's core on record, a returned process has the round's bound bit on
record, and the recorded bit is `GBCA.boundOfCore` of the recorded core. The round's announcement
of its bound bit rests on that conjunct.

What makes each inclusion one-directional is on the composed system, and it is the same on both. A
round instance records a corrupted process's graded-agreement call, which every program of a
protocol takes on an idle transition (D11), and the instance's round transitions carry no
termination guard, so the instance takes a send or a delivery at a process the protocol has
terminated (D22).

## What the composition gives

A sub-protocol is swappable exactly when its component holds its network.

Giving each round its own network is what makes the round a component, and a
component can be replaced. The substitution is one family congruence and one parallel
precongruence, then `abstract`, `relabel`, `abstract` to run the composition pipeline
out. Nothing else in the chain is touched.

That is a modular axis rather than a one-off. Varying the power of the network —
losses, reordering, a different forgery model — is a change inside the round instance,
swapped in by the same precongruence. Exchanging the whole implementation of graded agreement
is that same move at that same place, which is what the second chain is.

Idealizing the round also exposes an asymmetry worth naming. The round's sent sets, its delivery
guards and its injections are removed by the graded-agreement idealization. The DECIDED sets, the
corruption budget, the started rounds and the guards `k ∈ F` and `r ∈ startedRounds` of a corrupted
process's calls are kept, at the ABA network. What a component holds is what disappears with it.

## The gather-based chain

The gather-based implementation applies that device three more times, inside the round,
before the round itself is exchanged at `hybrid`.

One shape carries every message-passing level: `n` programs beside the one network that
carries their messages. A program holds one process's variables and the messages
delivered to it, indexed by sender, and its guards read that and nothing else. The
network holds the per-sender sent sets and the corrupted set (`ABA.NetworkState`, D5)
and reads no program's variables. A multicast is a synchronised step of the sender and the
network, a delivery a synchronised step of the network and the receiver, and both labels are
hidden inside the instance. `ABA.InstanceState n Pr M` is the state of such a pair.

Three levels are built that way, each the level below it in parallel with programs and a
network of its own:

- a reliable-broadcast instance is `n` programs beside the instance's network at the
  broadcast message type (`BRB.brachaInstance`, `ABA/ReliableBroadcast/Bracha/Composition.lean`);
- a gather instance is `n` gather programs beside the gather network, in parallel with
  `n` reliable-broadcast instances, one per process for the inputs, each read along the pullback
  `Gather.inputBroadcastLabelMap` that names it (`Gather.instanceOverBroadcasts`,
  `ABA/Gather/Composition.lean`). `Gather.instanceOverBracha` plugs Bracha's instances into
  that slot and `Gather.instanceOverBroadcastSpecification` the broadcast specifications;
- a round is `n` graded-agreement programs beside the round's network, in parallel with two gather
  instances read along `firstGatherLabelMap` and `secondGatherLabelMap`
  (`GBCA.ByAFW.roundOverGathers`, `ABA/GBCA/AFW/Composition.lean`). `GBCA.ByAFW.roundOverBracha`,
  `GBCA.ByAFW.roundOverBroadcastSpecification` and `GBCA.ByAFW.roundOverGatherSpecifications` are
  the three compositions, by which gather system fills the two slots.

The state of each is the product of its components, and the three compositions of a level are the
same expression at a different component:

```
BRB.BrachaState  n M       = (Fin n → LocalState n (ProcessVariables M) (Message M)) × NetworkState n (Message M)
Gather.StateOverBroadcasts n X B = ((Fin n → LocalState n (ProcessVariables n X) (Message n X)) × NetworkState n X)
                             × (Fin n → B)
GBCA.ByAFW.RoundStateOverGathers n G₁ G₂  = ((Fin n → GBCA.ByAFW.ProcessVariables n) × GBCA.ByAFW.NetworkState n) × (G₁ × G₂)
```

A program reads no neighbouring coordinate, so what a sub-protocol has returned to a process is
written into that process's own variables. A gather program's variables for what the broadcast
instances returned (`Gather.ProcessVariables.inputBroadcastReturned`) are written on the return
event of a broadcast instance and read by the four transitions that read what has been returned. A round program's variables (`GBCA.ByAFW.ProcessVariables`) hold the candidate
between the first gather's return and the second gather's call, and the graded outcome between the
second gather's return and the round's own return: each of those two is a pair of events, and the
variables are what carry the round across them.

Three substitutions take one composition to the next, and each removes exactly what the
component it replaces held.

- `Gather.broadcastSubstitution` replaces each of a gather's `n` Bracha instances by a broadcast
  specification. An instance's programs and its network are removed together; what is kept
  of each is the committed value, written once.
- `Gather.refinesSpecification` replaces a gather instance by the gather specification. The `n`
  gather programs, the gather network and the `n` broadcast specifications beneath them
  are removed together; what is kept is the per-entry committed value and the recorded core.
- `GBCA.ByAFW.refinesSpecification` replaces the round over the two gather specifications by
  `GBCA.specInst`. The graded-agreement programs, the round's network and the two gather
  specifications are removed; what is kept is `excluded` and `grade`.

The first two are applied inside the round by congruence. `GBCA.ByAFW.broadcastSubstitution` carries
`Gather.broadcastSubstitution` and `GBCA.ByAFW.gatherSubstitution` carries
`Gather.refinesSpecification` through the operators a round is built from — `mapIdle` at the gather
coordinate, `parallel_left` and `parallel_right` to hold the round's programs and the other gather,
then `abstract` and `relabel` (`ABA/GBCA/AFW/BroadcastSubstitution.lean` and
`ABA/GBCA/AFW/GatherSubstitution.lean`, over
`Framework/Congruence.lean`), and `Gather.broadcastSubstitution` itself carries
`BRB.brachaRefinesSpecification` through the operators a gather instance is built from,
`synchronisedProduct` among them. `Gather.refinesSpecification` and
`GBCA.ByAFW.refinesSpecification` are proved on the compositions themselves, through the
characterisations by their algorithms
`Gather.instanceOverBroadcastSpecification_step_iff_algorithm` and
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm`.

The round's network carries no messages. Its state, `GBCA.ByAFW.NetworkState`, is the first
gather's core it has recorded and whether the round has returned, the gather counterpart of
`GBCA.ByABDY.NetworkState.bound`. It records the core from the first gather's announcement
`firstGatherCore C` and the return at the round's `retG`, and once both are recorded it announces
the bit `GBCA.boundOfCore P C` on `boundG` (D29). No program reads it, and it meets the
specification only at the last of the three substitutions, where `GBCA.ByAFW.SpecificationRelation`
ties the announced bit to `excluded`. The recorded core plays the same part one level down: it is a
field of the gather network that no process reads, written at the instance's first return and
announced on `core C`, as the gather specification announces its own core (D29).

A gather's `BIND` payloads are messages of the gather network, each multicast once, as AFW25's
Algorithm 5 sends them at line 17. At the protocol a `BIND` is tagged `firstGather` or
`secondGather`, as the gather's `ECHO` and `VOTE` are. The counting of
`DESIGN-GatherComposition.md` runs on `Gather.withoutBindAbove`, the processes outside `F` whose
sent set holds no `BIND` above the core, a set that corruption and sends only shrink.

At the protocol shape the three stages are `AFW.composed ⊑
AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid`,
each the four congruences applied to one family substitution under a single context term:

```
(((FAMILY.parallel ((System.synchronisedProduct (roundLoopProgram P)).parallel
                  ((ABANetwork P).parallel (coinOverRoundAlphabet P)))).abstract
    (networkEventLabels P.n)).relabel).abstract (Label.hiddenAPI P.n)
```

`FAMILY` is the family of round compositions — `AFW.roundFamilyOverBracha`,
`AFW.roundFamilyOverBroadcastSpecification`, `AFW.roundFamilyOverGatherSpecifications` — and
`GBCA.ByABDY.gbcaInstanceFamily` and `gbcaSpecificationFamily` stand in the same position in the
other chain. The context term is the same expression in all five, which is why the third stage's
target is `hybrid P` itself and why the two chains meet there.

Beneath `AFW.composed` the protocol collapses the round's `2n + 2` network states into the one
sent-set family the adversary holds, tagging each message with the instance it belongs to:
`AFW.Message` carries a constructor per component, `firstGather`, `secondGather`,
`firstGatherInputBroadcasts` and `secondGatherInputBroadcasts`. `AFW.RoundVariables` is the composed system's instance-major indexing
transposed, one process's local state in each of those instances, and `AFW.Ghost` is the adversary's
ghost for one round, the two recorded cores beside the bound bit.

## Where each network is external

No network is internal to a process, and none is a field of a process's variables.

Both chains carry the ABA DECIDED network `Composition.ABANetwork`. It is a component of every
system of both chains and the second component of `ABAState`, the state
`hybridSpecificationRelation` is defined on, and neither chain idealizes it.

Below that the two chains own different things. ABDY22's carries one further network, the
round's network `GBCA.ByABDY.GBCANetwork`, a component of `ABDY.composed` and of `hybrid`, which
disappears at the substitution inside the component that is exchanged. It is also the
second component of `GBCA.ByABDY.RoundState`, the state the round refinement is defined on.
It carries one field that is not a message set: the round's bound bit, written at the round's
first return and announced by the network on `boundG` (D29). The field is an auxiliary variable —
no program reads it, the network's transition on a return writes it and its announcement reads
it — and it belongs to the round for the same reason the sent sets do, so it disappears with the
round at the substitution.

The gather-based chain carries `2n + 2` of them per round: one for each gather instance,
and one for each of the `2n` broadcast instances beneath the two. They disappear in two
stages rather than one, the broadcast networks at `Gather.broadcastSubstitution`, carried into the
round by `GBCA.ByAFW.broadcastSubstitution`, and the gather networks at
`Gather.refinesSpecification`, carried by `GBCA.ByAFW.gatherSubstitution`, each inside the component
being exchanged.

Every invariant therefore reads its network through accessors on a pair — the
`GBCA.ByABDY.RoundState` accessors in `ABA/GBCA/ABDY/MessagesAndVariables.lean`, the `ABAState`
accessors in `ABA/Composition/ABAState.lean`, the `ABA.InstanceState` accessors in
`ABA/Vocabulary/ProcessAndNetworkState.lean` — and names the network's own sent sets
rather than a copy of them held inside a program's variables. Weakening any one of them is a change
to that one component.

The ghost field of the network is removable, and `ABA/GhostRemoval/GhostFreeSystem.lean` removes it.
The ghost-free system `Implementation.systemGhostFree` is the implementation over a one-element
ghost, whose network never announces. The map that drops the ghost is an auxiliary-variable removal
of the network onto it (`Framework/AuxiliaryVariableRemoval.lean`), at the identity on labels, whose
set `K` is the announcements `boundG r b`: a transition on one of them leaves the projection where
it stands (`projectUnchanged`). The congruences of that file carry the removal through the same
pipeline the composition is built by — the common coin, the process group, the hiding of the labels
the components synchronise on, and the restriction — each neighbour idling on the announcements.
`Label.hiddenAPI` contains `boundG r b`, so after the last hiding the set `K` is empty, and
`ABDY.protocol_ghostRemoval` and `AFW.protocol_ghostRemoval` are equalities of achievable trace
distributions with no map on labels in them. The bound bit is therefore a field the chain may keep
or drop, and the choice to keep it is a choice about what the invariants read, not about what the
protocol does.

## Every state is one component's own or a product of them

The property holds across the development, and a reader should not have to re-derive it.

Each leaf structure holds exactly one local state's data: `RoundLoopState` and `RoundLoopVariables`
for a round loop, `GBCA.ByABDY.ProcessVariables` and `GBCA.ByABDY.RoundVariables` for a
graded-agreement round, `ABDY.RoundVariablesMap` and `AFW.RoundVariablesMap` for the round variables
of one process, `GBCA.ByABDY.NetworkState` for a round's network state beside its bound bit,
`GBCA.ByAFW.NetworkState` for the gather-based round's network, `ABA.NetworkState` for the network
state of a reliable-broadcast instance, `Gather.NetworkState` for the gather network's state beside
the instance's core, `Composition.ABANetworkState` for the DECIDED network beside the started
rounds, and one `SpecState` for each of the five specifications. Each composite state is an explicit
product of those: `ABDY.ProcessVariables`, `AFW.ProcessVariables`, `ABA.InstanceState`,
`GBCA.ByABDY.RoundState`, `ABAState`, `Composition.ComposedState` and `HybridState` for the ABDY22
chain, with `InstanceFamilyState` for a family of instances, and `Gather.StateOverBracha`,
`Gather.StateOverBroadcastSpecification`, `GBCA.ByAFW.RoundStateOverBracha`,
`GBCA.ByAFW.RoundStateOverBroadcastSpecification`, `GBCA.ByAFW.RoundStateOverGatherSpecifications`
and `AFW.RoundVariables` for the gather-based one.

One structure holds two kinds of message set at once, and it is the right one to.
`ABDY.NetworkState`
(`ABA/ABDY/System.lean`) and `AFW.NetworkState`
(`ABA/AFW/System.lean`), both `Implementation.NetworkState`, carry the round sent sets, the DECIDED
sets, the corrupted set and the started rounds together, because each is the network of a
protocol — the subject of a chain, not a vehicle for proving anything about it. Each carries one
ghost per round beside them (D30), for the same reason: the round's bound bit is determined by the
round's messages and the corrupted set, which this network state holds. The implementation of
`ABA/Implementation/System.lean` is parametric in that ghost's type, its update `ghostStep`,
applied on every transition to the round the label names, and its read `ghostBound`, the bit the
ghost holds. The one transition that reads the ghost is the network's announcement `boundG r b`, a
self-loop enabled when `ghostBound` of the round's ghost is `some b` (D29), which is what makes the
ghost removable.

The protocol's network outputs the deliveries, `fail`, the announcement `boundG` and a corrupted
process's two sub-protocol calls `byzantineCallG` and `byzantineCallW`, the calls under `k ∈ F` and
at a round of `startedRounds` (D11, D37). Its injection of a corrupted process's round messages is a
silent transition under the same two guards, and its DECIDED injection a silent transition under
`k ∈ F`. A replaced program takes no transition on its own calls (D23), so a corrupted process reaches a
sub-protocol through the network alone, which holds both the corrupted set and the started rounds.
The ABA network of a composed system outputs the same two calls under the same guards, and the
round instance and the coin take them on their call transitions.
 `ABDY.protocol_composed` and `AFW.protocol_composed` carry those
systems into ones where each round holds its network states beside `Composition.ABANetworkState`, and
every step above the first inclusion runs there. A round's ghost is, in the composed system, the
values the round's own state holds, which is one conjunct of each protocol relation.

## What the DECIDED model already weakens

The ABA network is the one neither chain idealizes, so what it assumes is what the development
assumes. Much of the weakening one might ask for is already in it.

`decidedSent` is a `Finset`, so there is no delivery order to disturb. Received sets are sets too
and `RoundLoopVariables.receiveDecided` files by insertion, so a repeated delivery of one (receiver,
sender, bit) triple carries no information: `Composition.ABANetworkStep.decidedDeliver` consumes
nothing, the receiver's `Composition.RoundLoopStep.decidedDeliverReceive` files a payload not yet
held from its sender, under `b ∉ decidedDelivered k`, and
`Composition.RoundLoopStep.decidedDeliverLoop` takes a repeat and changes no state. Duplication is
immaterial here, not assumed away.

No transition forces a delivery, so any subset of the multicasts may be lost. `byzantineDecided`
injects either bit for any `k ∈ F`, so a corrupted process may equivocate in the DECIDED sets.
The replaced round loop of a corrupted process outputs `retABA` at either bit at any time, with no
DECIDED quorum at all, on its self-loop `corruptedIdle`, and the ABA network takes the return on its
one unguarded transition `Composition.ABANetworkStep.retABAIdle` (D23), so the DECIDED quorum is a
condition on correct returns alone.

What remains assumed is unforgeability of a correct process's DECIDED multicast. The
delivery guard `b ∈ decidedSent j` attributes every received message to a genuine send by the
named sender, and no transition lets one process record a send under another's name.
