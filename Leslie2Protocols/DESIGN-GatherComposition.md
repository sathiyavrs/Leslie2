# The gather-based graded-agreement stack: `GBCA.ByAFW.roundOverBracha ⊑ … ⊑ GBCA.specInst`
and its chain

Companion design document to the gather-based implementation of graded agreement: the
sub-protocol compositions (`ABA/Vocabulary/ProcessAndNetworkState.lean`,
`ABA/ReliableBroadcast/Specification.lean`,
`ABA/ReliableBroadcast/Bracha/MessagesAndVariables.lean`,
`ABA/ReliableBroadcast/Bracha/Components.lean`,
`ABA/ReliableBroadcast/Bracha/Composition.lean`,
`ABA/ReliableBroadcast/Bracha/SpecificationOverInstanceAlphabet.lean`,
`ABA/ReliableBroadcast/Bracha/CompositionStepCases.lean`,
`ABA/ReliableBroadcast/Bracha/Algorithm.lean`, `ABA/Gather/Specification.lean`,
`ABA/Gather/MessagesAndCommonCore.lean`, `ABA/Gather/Components.lean`,
`ABA/Gather/Composition.lean`,
`ABA/Gather/SpecificationOverInstanceAlphabet.lean`,
`ABA/Gather/CompositionStepCases.lean`,
`ABA/Gather/AlgorithmOverBroadcastSpecification.lean`, `ABA/Gather/AlgorithmOverBracha.lean`), their
refinements (`ABA/ReliableBroadcast/Bracha/EchoWitness.lean`,
`ABA/ReliableBroadcast/Bracha/Invariant.lean`,
`ABA/ReliableBroadcast/Bracha/SpecificationRelation.lean`,
`ABA/ReliableBroadcast/Bracha/RefinesSpecification.lean`,
`ABA/Gather/Invariant.lean`, `ABA/Gather/CommonCoreCounting.lean`,
`ABA/Gather/SpecificationRelation.lean`, `ABA/Gather/RefinesSpecification.lean`,
`ABA/Gather/BroadcastSubstitution.lean`, `ABA/Gather/CommonCore.lean`), the
two-gather round and its three compositions (`ABA/GBCA/AFW/Counting.lean`,
`ABA/GBCA/AFW/Components.lean`, `ABA/GBCA/AFW/Composition.lean`,
`ABA/GBCA/AFW/CompositionStepCases.lean`,
`ABA/GBCA/AFW/AlgorithmOverGatherSpecifications.lean`,
`ABA/GBCA/AFW/OutputWitness.lean`, `ABA/GBCA/AFW/Invariant.lean`,
`ABA/GBCA/AFW/SpecificationRelation.lean`, `ABA/GBCA/AFW/RefinesSpecification.lean`,
`ABA/GBCA/AFW/BroadcastSubstitution.lean`, `ABA/GBCA/AFW/GatherSubstitution.lean`,
`ABA/GBCA/AFW/Binding.lean`), the assembly at the protocol shape
(`ABA/AFW/Composition.lean`, `ABA/AFW/Substitution.lean`), and the protocol beneath it
(`ABA/AFW/System.lean`, `ABA/AFW/RoundProjection.lean`,
`ABA/AFW/RoundProjectionStep/`,
`ABA/AFW/SimulationOfEachTransition.lean`, `ABA/AFW/Simulation.lean`). The
gather subsections of
`blueprint/src/content.tex` are a condensation of this document; the deviations D24,
D26–D30, D32 and D33 it realises are glossed in that file's registry, and the
source-fidelity items it rests on are §§2, 5 and 6 of `NOTES-Fidelity.md`.

## Systems

Every system of the stack is a composition of components, and one shape carries
every message-passing level: `n` programs beside the one network that carries
their messages. A program holds one process's variables and the messages
delivered to it, indexed by sender, and its guards read that and nothing else;
the network holds the per-sender sent sets and the corrupted set
(`ABA.NetworkState`, D5) and reads no program's variables. A multicast is a
synchronised step of the sender and the network, a delivery a synchronised step
of the network and the receiver, and both are hidden inside the instance.

Three levels are built that way, each the level below it in parallel with
programs and a network of its own.

```
BRB.brachaInstance P ldr M     -- n programs beside the instance's network (ReliableBroadcast/Bracha/Composition.lean)
Gather.instanceOverBroadcasts P X BIn BBind
                         -- n gather programs beside the gather network, in parallel with
                         -- 2n broadcast instances, each read along a pullback naming it
                         -- (Gather/Composition.lean); instanceOverBracha plugs in Bracha,
                         -- instanceOverBroadcastSpecification the
                         -- broadcast specifications
GBCA.ByAFW.roundOverGathers P r firstGather secondGather
                         -- n graded-agreement programs beside the round's network, in
                         -- parallel with two gathers read along firstGatherLabelMap/secondGatherLabelMap
                         -- (GBCA/AFW/Composition.lean); roundOverBracha,
                         -- roundOverBroadcastSpecification, roundOverGatherSpecifications by the
                         -- gather system plugged in
```

Per round, three forward simulations between the compositions, and their
probabilistic composite:

```
roundOverBracha P r                   -- two gather-over-Bracha instances
  ⊑ broadcastSubstitution                    (broadcast substitution, by congruence)
roundOverBroadcastSpecification P r   -- two gather-over-BRB.Spec instances
  ⊑ gatherSubstitution                      (gather substitution, by congruence)
roundOverGatherSpecifications P r     -- two gather specifications + the round's network
  ⊑ refinesSpecification                       (core counting into TS 2, on the composition)
GBCA.specInst P r                     -- GBCA/Specification.lean, D19/D29, read along
                                      -- GBCA.specificationLabelMap

roundOverBracha_refinesSpecification P r : roundOverBracha ⊑ GBCA.specificationOverRoundAlphabet   (probabilistic, trans ×2)
```

Beneath the round, the two gather compositions and the broadcast instance, citable on their
own:

```
BRB.brachaInstance P ldr M ⊑ BRB.specInst P ldr M     (brachaRefinesSpecification, ReliableBroadcast/Bracha/RefinesSpecification.lean)
Gather.instanceOverBracha P X   ⊑ Gather.instanceOverBroadcastSpecification P X      (broadcastSubstitution,  Gather/BroadcastSubstitution.lean, by congruence)
Gather.instanceOverBroadcastSpecification P X ⊑ Gather.specInst P X       (refinesSpecification, Gather/RefinesSpecification.lean)
```

Each composition has an alphabet of its own, in which the call's
input-enabledness loop is a label of its own, and its specification is read
along a pullback that sends the loop to the call (`BRB.specificationLabelMap`,
`Gather.specificationLabelMap`): the specification answers its call label on two transitions, and a
composition whose caller and network are different components could otherwise
combine the caller's loop with the network's post. The round is over the family
alphabet `ExtendedLabel P.n Empty` natively, as the ABDY chain's round
`GBCA.ByABDY.composition` is over `ExtendedLabel P.n GBCA.ByABDY.Message`, so the family's call
loops are its loop labels and `GBCA.specificationLabelMap` reads its specification. The family
alphabet is parametric in the type of the messages a graded-agreement round exchanges; the round
takes the empty type for it, so the round multicast and the round delivery name no label in
this chain.

At the protocol shape (`AFW/Composition.lean` and `AFW/Substitution.lean`), each round composition is
gathered into the ℕ-indexed family under the corruption broadcast and put through the
composed system's pipeline; the three substitutions become three stages whose last lands
on `hybrid P`:

```
AFW.protocol ⊑ AFW.composed ⊑ AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid ⊑ ABA.spec
```

Beneath `AFW.composed` is `AFW.protocol`, the gather-based protocol as it runs
(`ABA/AFW/System.lean`), carried into the composed system by
`AFW.protocolSimulation` (`ABA/AFW/Simulation.lean`). Everything from `hybrid` up
— the core simulation, `spec_safe`, the safety transfer — is shared with the ABDY
chain.

Every protocol-shaped system and headline of this chain sits in the namespace
`AFW`, after Attiya, Flam and Welch, and carries the name of its counterpart in
the ABDY chain: `AFW.composed` is to the gather-based implementation what
`ABDY.composed` is to ABDY22's. A `G` elsewhere in the development is graded
agreement — `callG`, `retG`, `GBCANetwork`, `GBCAOutput` — and never the chain.

## What a program holds of a sub-protocol's answer

A program reads no neighbouring component. What a sub-protocol has returned to a
process is therefore written into that process's own variables, on the return
event, and read there.

A gather program's variables (`Gather.ProcessVariables`) extend `BaseProcessVariables` with two
returned values: `inputBroadcastReturned k`, the value the input-broadcast instance `k` has returned here,
and `bindBroadcastReturned q`, the payload the bind-broadcast instance `q` has returned here. The
return of an instance is a hidden event of the gather composition
(`Gather.GatherEvent.inputBroadcastRet`, `bindRet`), on which that instance takes its own return
transition and the receiving program records the returned value. The four transitions that read what
has been returned — `sendEcho`, `sendVote`, `bindCall` and `ret` — read the returned values through
`Gather.ProcessVariables.accepted`, `holdsInputBroadcastReturn`, `holdsBindBroadcastReturn` and
`approvedBy`, in the same shape at both gather compositions. The tie between a returned value and
the instance it records is an invariant clause of `Gather.Conformance` (`inputBroadcastReturned_val`,
`bindBroadcastReturned_val`): a returned value is the instance's committed value, established at the
return event and kept by the write-once commit.

A round program's variables (`GBCA.ByAFW.ProcessVariables`) hold the process's input, its
candidate, whether it has called the second gather, its graded outcome and its
return flag. The first gather's return and the second gather's call are two
events, `firstGatherReturn` and `secondGatherCall`, and so are the second gather's return and the
round's graded return, `secondGatherReturn` and `retG`; the variables are what carry the round
across each pair. The graded return drops the recorded outcome, so no variables
hold a round's grade after its return.

## The core of the gather specification

The classical binding property of gather says: once the first correct process
returns, there is a set of at least `n − f` entries on which every future
correct return is defined. TS 4 states this with a single set, and
`Gather.SpecState.core : Option (AcceptedPairs n X)` carries it. The internal transition
`Gather.Step.bindCore` is its only writer and fires only from `core = none`,
under two guards: the set's entries are committed entries (`hval`), and it has
at least `n − f` of them (`hcard`). `Gather.Step.ret` demands that the returned
map dominate it, and the return label carries it (D29).

A forward simulation has to produce that write at a reachable prefix state, no
later than the first return it answers, and then hold every later return above
the set it chose. `ABA/Gather/CommonCoreCounting.lean` is the argument that the
gather-over-BRB instance determines such a set.

**The core.** Let `w` be the gather network's state in a state of the instance:
the per-sender sent sets beside the corrupted set `F`. Say that `q` *dominates*
`j` when every `VOTE` payload `q` has multicast lies above some `ECHO` payload
of `j`. Write `dominatedBy w q` for the senders `q` dominates and
`dominators w j` for the processes outside `F` that dominate `j`.
`Gather.coreOf P w` is the `ECHO` payload of a sender outside `F` carrying at
least `f + 1` dominators, and `∅` where there is no such sender. It reads the
sent sets and the corrupted set alone (`coreOf_networkState_only`,
`coreOfNetwork`), so the gather network computes it from its own state and writes
it at the first return (D29).

**The counting.** Read `dominatedBy` as an incidence whose rows and columns are
the processes outside `F`. A `VOTE` payload of a process outside `F` is
multicast above `n − f` delivered `ECHO` payloads, and `VOTE` is write-once, so
`n − f ≤ (dominatedBy w q).card` for every `q` outside `F` — vacuously for a `q`
that has multicast no `VOTE`, whose row is everything (`dominatedBy_card`).
Restricting a row to the columns costs at most `|F|`, so every row carries at
least `n − f − |F|` of them (`dominatedBy_correct_card`). Summing the rows and
reading the same sum by columns (`sum_dominatedBy`) gives a column `j₀` outside
`F` with `n − f − |F| ≤ (dominators w j₀).card` (`exists_dominators`), and
`n − f − |F| ≥ f + 1` under `n > 3f` and `|F| ≤ f`. The core is `j₀`'s `ECHO`
payload, whose own send guard gives it `n − f` entries.

**The transfer.** Take a committed `BIND` payload `U` of a process outside `F`. It is that process's
contributed payload, multicast above `n − f` delivered `VOTE` payloads. Those `n − f` senders meet
the `f + 1` dominators of `j₀` in a process `q`, whose write-once `VOTE` payload lies above the core
by domination and below `U` by the bind guard, so `coreOf P w ⊆ U` (`transfer`, `single_core`).
Every `ECHO` field holds entries of what the sender's input instance returned, and a returned value
is a committed value, so the core's entries are committed entries (`single_core_approved`), which is
`bindCore`'s other guard.

**The witness that the core is written once.** `coreOf_recorded` packages the three facts with the count the simulation
carries along the run: at least `f + 1` coordinates hold a committed `BIND` payload above the core
(`Gather.bindAbove`). That count is blind to `F` and monotone under every transition (`bindAbove_mono`),
so it survives every later corruption, and it is what holds the returns after the first to the set
the first one wrote. A returner's quorum of `n − f` returned payloads is a quorum of committed
payloads, it meets the `f + 1` witnessed coordinates, and BRB values are functional, so the returned
map lies above the recorded core.

**Why the counting closes here.** `BIND` payloads are sent by reliable broadcast
rather than on the gather network, so a committed payload is write-once
whatever happens to its sender afterwards, where a multicast payload is fixed
only by its sender's correctness and D1 withdraws that at any moment. A gather
instance holds one bind-broadcast instance per process, and the `BIND` send is
that instance's call, a hidden event of the composition (D32), which is what
makes the objects the witness counts stable.

## The commit splits (D26, D27)

The same dynamic-corruption reading, one level down. TS 6 fixes the delivered
value at a correct `call`; Bracha's rounds with the leader corrupted after
its `INIT` can deliver a different value until some correct process holds an
ECHO quorum of more than `(n+f)/2` senders, so the specification that fixes it
excludes its own implementation
(`NOTES-Fidelity.md` §5). `BRB.SpecState` therefore splits `input` (the
call wrote) from `val` (the committed value), with the silent commit transition
guarded `ldr ∈ F ∨ input = some m`: the corrupted leader's power is a commit
of any value, the correct leader's value is fixed, and the window closes at
the commit. `Gather.SpecState` carries the per-entry form: `call` and `val`
split, `Gather.Step.commit` guarded `k ∈ F ∨ call k = some v`.

The refinement counterpart is *commit-on-demand*: the abstract commit is a
silent transition with no implementation event to synchronise with, so the simulations
fire it inside the matching weak run of the first transition that reads it —
`BRB.commitReach` under a return, the `commitOne/commitList` chains of
`ABA/Gather/RefinesSpecification.lean` under a return.

The gather specification's call follows the gather program's variables
(`Gather.SpecificationRelation.call_eq`). The specification's call and the gather program's input
move on the one interface label under the one write-once guard, and a broadcast specification
answers the call label and the call loop on either of its two transitions, so the gather program's
variables and an input instance's call can differ. `Gather.Invariant.inputBroadcastCall_backed`
carries the instance's call back to those variables,
and the specification's `commit` guard is dischargeable against the instance's.
`DESIGN-Decomposition.md` §2 is the argument.

## Counting at the round over the gather specifications (`refinesSpecification`)

`roundOverGatherSpecifications` is AFW25's Algorithm 4 at `R = 2`, its two-gather branch
(D24): candidate at `|dom g| − f` occurrences after the first gather, grade at
`|dom h| − f` / `f + 1` after the second. The refinement into TS 2 witnesses
the specification's `excluded` and `grade` on the two instances' recorded cores.
One transfer lemma carries a count from a returned map down to a core below
it: `count_aboveThreshold_of_subMap` (AFW25 Lemma 13) says that a map carrying `x` on all
but `f` of its entries makes such a core carry `x` on at least `|S| − f` of its
own, the core sitting below the map and losing at most `f` entries to it.

A core has at least `n − f > 2f` entries, so at most one value is on at least `|S| − f` of them,
and the three witnesses are readings of that:

- the round's bound bit is `GBCA.boundOfCore` of the first instance's core — the bit on at least
  `|S| − f` of its entries where one exists (`boundOfCore_of_aboveThreshold`), the complement being
  on fewer (`count_boundOfCore_belowThreshold`); the round's network writes it at the first gather's return,
  from the core that return carries;
- the exclusion witness is `ExclusionWitness b = ∃ S, core₁ = some S ∧ count S b < |S| − f`.
  The core is write-once, so the witness stands from the moment it holds — monotonicity for free,
  where the direct implementation's refinement maintains monotone quorums of received messages;
- the grade-2/grade-0 exclusivity is the second instance's core carrying `some v` on at least
  `|S| − f` entries for grade 2 and each bit on at most `f` for grade 0.

The return-then-call step and the return place the witnesses in the invariant
(`GBCA.ByAFW.Invariant`). A candidate is on at least `|S| − f` entries of the first core (`candidate_aboveThreshold`) or, at
`⊥`, witnesses `f + 1` for both bits (`candidate_bot`); both are established at `firstGatherReturn`,
where the first gather's return carries the core, and consumed at `secondGatherCall`, where the
second gather's call takes the candidate (`secondGatherCall_candidate`). The bound bit is on
record from the first `firstGatherReturn` on (`candidate_bound`, `secondGatherCall_bound`). The
graded outcome's witness, `OutputWitness`, is established at `secondGatherReturn` from the
second gather's return and consumed at `retG`, which sees the outcome alone (`out_witness`). The
return transitions then mirror `GBCA.ByABDY.refinesSpecification` shape for shape: a grade-2 or grade-1 return
hands out the bound bit and witnesses `ExclusionWitness` of its complement, and the grade-0 return
announces the bit the first return wrote. The D15 support counts come off the first core through the
committed entries — a core entry is a committed entry, a committed entry of a correct
process is its call, and the count is `F`-blind (`callSupport_of_core`) — or off a correct `⊥`
candidate. Exclusions fire on demand as the two-step run `bindUnset; ret`, as in the direct
refinement.

## Substitution by congruence

A substitution that replaces a component by a system that simulates it is an application of the
congruences of `Framework/Congruence.lean`: forward simulation between labelled transition systems
survives parallel composition in either position, the synchronised product of a finite family,
hiding and restriction, and two simulations compose. Every substitution inside a composition of the
stack is proved that way and nothing else:

- `Gather.broadcastSubstitution` lifts `BRB.brachaRefinesSpecification` at each of the `2n`
  broadcast coordinates along the pullback naming the coordinate (`ForwardSimulation.mapIdle`),
  through the two synchronised products, the parallel composition with the gather programs and
  network held, the hiding and the restriction; its relation
  `Gather.BroadcastSubstitutionRelation` is the gather programs and network held equal beside
  `BRB.SpecificationRelation` at every coordinate
  (`ABA/Gather/BroadcastSubstitution.lean`);
- `GBCA.ByAFW.broadcastSubstitution` and `GBCA.ByAFW.gatherSubstitution` lift
  `Gather.broadcastSubstitution` and `Gather.refinesSpecification` at each of the two gather
  coordinates the same way, with the round's programs held
  (`ABA/GBCA/AFW/BroadcastSubstitution.lean`, `ABA/GBCA/AFW/GatherSubstitution.lean`); their
  relations hold the round's programs equal beside
  the gather relation at each gather.

The two refinements into a specification, `Gather.refinesSpecification` and
`GBCA.ByAFW.refinesSpecification`, are proved on the compositions themselves. Each composition
carries a characterisation by an algorithm —
`Gather.instanceOverBroadcastSpecification_step_iff_algorithm`,
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm` — stating that its transitions over
the labels the pullback sends to one specification label are exactly the transitions of an
algorithm at that label (`Gather.AlgorithmOverBroadcastSpecification`,
`GBCA.ByAFW.AlgorithmOverGatherSpecifications`), on the same state and with the same
distribution. A refinement is then a case analysis over the transitions, and the specification's
matching run, a run of `specInst`, is lifted to the specification read along the pullback by a
section of it (`Gather.weakLStep_specificationOverInstanceAlphabet`,
`GBCA.ByABDY.weakLStep_specificationOverRoundAlphabet`), as `GBCA.ByABDY.refinesSpecification` does
for the ABDY chain's round.

Two facts of the characterisations are worth reading. A specification answers its call label on two
transitions, so where a specification is a component the composition offers both under the label
that reaches it, and the algorithm lists them: two transitions at each call of an instance of the
gather over the broadcast specifications, two at the round over the gather specifications. And a
label outside a round's interface blocks the round rather than letting it idle
(`GBCA.ByAFW.ProgramLabel.outside`), exactly as `GBCA.ByABDY.composition` blocks, which is what
makes that composition's characterisation exact at the specification's labels.

## The assembly at the protocol shape (`AFW/Composition.lean`, `AFW/Substitution.lean`)

Two ingredients, both shared with the ABDY chain:

- **The family congruence** (`ForwardSimulation.family`): per-round simulations lift to the
  ℕ-indexed families; the broadcast hypothesis is each relation's simultaneous-corruption statement
  (`broadcastSubstitutionRelation_corrupt`, `gatherSubstitutionRelation_corrupt`,
  `specificationRelation_corrupt`), exactly as `refinesSpecification_failAct` discharges it for the
  ABDY chain. The family's act corrupts the two gathers of every round and leaves the programs
  and the round's network alone.
- **The four congruences** (`parallel_right`, `abstract`, `relabel`, `abstract`): each
  family substitution runs under the composed system's own context, the same term
  `ABDY/Substitution.lean`'s `ABDY.substitutionSimulation` uses, so the third
  stage's target is definitionally `hybrid P`.

The round is over the family alphabet natively, so no lift precedes the family; the families are
`System.family (GBCA.ByAFW.roundOverBracha P) roundOwnsLabel isFailLabel corruptionOverBracha` and
their two siblings, as `GBCA.ByABDY.gbcaInstanceFamily` is. The stages compose by
`ProbabilisticForwardSimulation.trans`; the inclusions compose by `Set.Subset.trans` and never
invoke transitivity of simulation — the two routes of `Results.lean`, reproduced.

## The protocol beneath the composed system (`AFW/System.lean`,
`AFW/RoundProjection.lean`, `AFW/RoundProjectionStep/`,
`AFW/SimulationOfEachTransition.lean`, `AFW/Simulation.lean`)

`AFW.composed P` is the gather-based protocol read as a composition of components. What runs is the
implementation: `n` programs, each reading its own variables and nothing else, beside one network
adversary holding every sent set and the corrupted set, beside the common coin. That shape is the
same for either implementation of graded agreement — the round loop, the DECIDED sets, the coin's
call and return, corruption, the adversary's transitions and the composition pipeline are fixed by
the round interface and the specification — so `ABA/Implementation/System.lean` writes it once,
parametric in the round message type `M`, the per-process per-round variables `S`, the round's
transitions, supplied as a relation embedded in one constructor of the program's step relation, and
the adversary's per-round ghost `G` with its update `ghostStep` and its output `ghostOutput` (D30).
`ABA/ABDY/System.lean` instantiates it at ABDY22's implementation;
`ABA/AFW/System.lean` instantiates it here.

The division of labour is by label. `Implementation.roundOwn j` is the set of label classes an
implementation owns at process `j`: the graded-agreement call and return, `j`'s own round multicast,
a delivery addressed to `j`, and `j`'s call against a round whose variables already hold a call. An
instantiation
supplies `Implementation.IsRoundStep` — its transitions carry such a label, fire only at an
unreplaced
program, and are Dirac — and the shared lemmas that read a transition off its label consume
exactly those three facts.
`AFW.roundTransition_of_own` runs the argument the other way: a program's step on a label of
`roundOwn j` is a step of the implementation, which is what lets each case of the simulation rule
the others out.

Three things separate the implementation's round from the composed system's, and all
three are forced by the shape of the implementation.

- **The tagged sent set.** A round of `AFW.composed` carries `4n + 2` network components — one per
  gather instance, one per Bracha instance. The implementation's network carries one sent-set family
  per round, so `AFW.Message n` tags each message with the network it belongs to, and for a Bracha
  message with the instance, whose index is its leader. The sender index stays the sender, so a
  threshold still counts distinct senders (D5). No new adversary transitions are needed: recording
  a multicast, checking a delivery and authorising a Byzantine call or return transition are already
  payload-blind.
- **The transposition.** The composed system indexes local states by instance
  and then by process. A program must hold its own data and no one else's, so
  `AFW.RoundVariables n` is process-major: process `j`'s local state in each gather
  instance, and its local state in each of the `n` instances of each broadcast family.
  Nothing is lost, because every guard of the gather-based implementation
  reads the acting process's own local states and the networks, and the two transitions that
  read a network — the adversary's delivery and its Byzantine injection —
  belong to the adversary either way.
- **The calls and returns of the sub-protocols.** An implementation program takes one transition per
  statement of the pseudocode, so eleven transitions are the calls and the returns of the round's
  sub-protocols: the graded-agreement call, the first gather's return, the second gather's call, the
  second gather's return, the round's own return, the call of the process's own input-broadcast
  instance in each of the two gathers, and the return of each of the four broadcast families. Seven
  of them carry a `gbcaRoundEvent` label, a synchronisation the network moves on and the protocol
  reads as `τ`; the graded-agreement call and the round's own return are the visible `callG` and `retG`,
  and neither sends a message; and the two input-broadcast calls carry the `⟨INIT, ·⟩` of the
  instance they call, on a `gbcaSend` of their own.

`AFW.ProtocolRelation` has five conjuncts. The round loop, the common coin and the ABA network are
shared objects, and the round family is *computed* from the implementation's state by
`AFW.roundProjection`, which undoes the two separations: it transposes the local states back and
projects each network's sent set out of the tagged family by `Finset.filterMap`. The round
variables hold each gather local state over `Gather.ProcessVariables`, so what an instance returned
is there already and the projection is the identity on it. A round program's variables are read off
the process's
first-gather input, its candidate, its second-gather input, its graded outcome and its
second-gather return flag. Four of the five conjuncts are that computation, so there is nothing to
choose in the witness.

The ghost is part of that computation. The composed round holds three values no guard of it reads —
the core of each of its two gather networks and the round's network's bound bit — and the adversary
holds the same three as the round's ghost `AFW.Ghost`, which `AFW.roundProjection` reads them
off. Two transitions write the ghost. The first gather's return writes that gather's core at
`Gather.coreOf` of that gather's projection of the tagged sent sets, and the bound bit at
`GBCA.boundOfCore` of that core; the second gather's return writes the second core the same way.
The composed `firstGatherReturn` and `secondGatherReturn` write the same two values off the core
their gather's return carries, and the values agree because each is `Gather.coreOfNetwork` of one
network's state (`coreOfNetwork_firstGatherProjection`, `coreOfNetwork_secondGatherProjection`).

The fifth conjunct, `AFW.BoundInvariant`, is what makes the announced bits agree: a process holding
a round-`r` candidate has passed that round's first gather return, so the round's bound bit is on
record, and a graded outcome on record reaches a candidate on record through the two fields between
them.

The proof is organised around that computation. The files of
`ABA/AFW/RoundProjectionStep/` state, for every implementation transition, the projection after
the transition as the composed round before it with the corresponding composed effect applied,
written through the round's updaters exactly as the algorithms write it; the master lemma
`roundProjection_write` of `ABA/AFW/RoundProjectionStep/ProjectionAfterOneWrite.lean`
pushes a one-point round write and a single sent-set insertion inside every coordinate, and each
transition then owes only projection algebra, discharged by `messagesOf_recordSent_some` and
`messagesOf_recordSent_none`.
`ABA/AFW/SimulationOfEachTransition.lean` matches each implementation transition by one step of the
composed group: a send and a delivery are hidden events of the round instance, matched by one of
its silent steps, the adversary's authenticity conjunct becoming membership in the sent set
projected onto the instance; the call is the instance's own. A call or a return of a sub-protocol
is a transition of its own on either side, and the states it reaches are named by
`ABA/AFW/RoundProjectionStep/FirstGatherReturn.lean`,
`ABA/AFW/RoundProjectionStep/SecondGatherCall.lean`,
`ABA/AFW/RoundProjectionStep/SecondGatherReturn.lean`,
`ABA/AFW/RoundProjectionStep/GradedReturn.lean` and
`ABA/AFW/RoundProjectionStep/BroadcastReturn.lean`. The remaining labels move
the round loop and the ABA network while the family of rounds is unchanged, and corruption is one
broadcast, the corrupted set the adversary holds being the corrupted set of every network under the
same guard.

`ABA/AFW/Simulation.lean` closes with `AFW.protocolSimulation` and
`AFW.protocol_composed`, the composition inclusion it yields. `ABA/Results.lean` takes that
inclusion to the headlines of the gather-based chain — `AFW.refines`, `AFW.main`,
`AFW.chainSimulation` and the composed-level `AFW.composed_refines`, `AFW.composed_safe`,
`AFW.chainSimulationOfComposed` — each behind a `#print axioms` check, beside the protocol
chain's own.

## Boundaries

- The union sends of the source's Algorithm 4 are read as bounds
  (`NOTES-Fidelity.md` §2); the widening is monotone in every guard the
  proofs consume.
- Liveness — gather Termination, BRB Totality — is unclaimed throughout
  (`NOTES-Fidelity.md` §6).
