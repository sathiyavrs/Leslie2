# Design — the gather-based GBCA stack `GBCA.ByAFW.roundOverBracha ⊑ … ⊑ GBCA.specInst` and
its chain

Companion design document to the gather-based implementation of graded agreement: the
sub-protocol compositions (`ABA/Vocabulary/ProcessAndNetworkState.lean`,
`ABA/ReliableBroadcast/Specification.lean`,
`ABA/ReliableBroadcast/BrachaComposition.lean`,
`ABA/ReliableBroadcast/BrachaImplementation.lean`, `ABA/Gather/Specification.lean`,
`ABA/Gather/MessagesAndCommonCore.lean`, `ABA/Gather/Composition.lean`,
`ABA/Gather/StepOverBroadcastSpecification.lean`, `ABA/Gather/StepOverBracha.lean`), their
refinements (`ABA/ReliableBroadcast/BrachaRefinesSpecification.lean`,
`ABA/Gather/RefinesSpecification.lean`, `ABA/Gather/BroadcastSubstitution.lean`), the
two-gather round and its three tiers (`ABA/GBCA/AFW/Counting.lean`,
`ABA/GBCA/AFW/Composition.lean`, `ABA/GBCA/AFW/StepOverGatherSpecifications.lean`,
`ABA/GBCA/AFW/RefinesSpecification.lean`, `ABA/GBCA/AFW/GatherSubstitutions.lean`,
`ABA/GBCA/AFW/Binding.lean`), the assembly at the protocol shape
(`ABA/ImplementationByAFW/CompositionChain.lean`), and the protocol beneath it
(`ABA/ImplementationByAFW/System.lean`, `ABA/ImplementationByAFW/RoundProjection.lean`,
`ABA/ImplementationByAFW/RoundProjectionStep.lean`,
`ABA/ImplementationByAFW/Simulation.lean`). The gather subsections of
`blueprint/src/content.tex` are a condensation of this document; the deviations D24,
D26–D30, D32 and D33 it realises are glossed in that file's registry, and the
source-fidelity items it rests on are §§2, 5 and 6 of `NOTES-Fidelity.md`.

## Systems

Every system of the stack is a composition of components, and one shape carries
every message-passing level: `n` programs beside the one network that carries
their messages. A program holds one process's local record and the messages
delivered to it, indexed by sender, and its guards read that and nothing else;
the network holds the per-sender sent sets and the corrupted set
(`ABA.NetworkState`, D5) and reads no program's record. A multicast is a joint
step of the sender and the network, a delivery a joint step of the network and
the receiver, and both are hidden inside the instance.

Three levels are built that way, each the level below it in parallel with a tier
of its own.

```
BRB.brachaInstance P ldr M     -- n programs beside the instance's network (ReliableBroadcast/BrachaComposition.lean)
Gather.instAt P X BIn BBind
                         -- n gather programs beside the gather network, in parallel with
                         -- 2n broadcast instances, each read along a pullback naming it
                         -- (Gather/Composition.lean); instanceOverBracha plugs in Bracha,
                         -- instanceOverBroadcastSpecification the
                         -- broadcast specifications
GBCA.ByAFW.roundAt P r ga1 ga2
                         -- n graded-agreement programs beside the layer's network, in
                         -- parallel with two gathers read along firstGatherLabelMap/secondGatherLabelMap
                         -- (GBCA/AFW/Composition.lean); roundOverBracha,
                         -- roundOverBroadcastSpecification, roundOverGatherSpecifications by the
                         -- gather system plugged in
```

Per round, three forward simulations between the tiers, and their
probabilistic composite:

```
roundOverBracha P r                   -- two gather-over-Bracha instances
  ⊑ lowPairRefines                    (broadcast substitution, by congruence)
roundOverBroadcastSpecification P r   -- two gather-over-BRB.Spec instances
  ⊑ idealRefines                      (gather substitution, by congruence)
roundOverGatherSpecifications P r     -- two gather specifications + the layer's network
  ⊑ pairRefines                       (core counting into TS 2, on the composition)
GBCA.specInst P r                     -- GBCA/Specification.lean, D19/D29, read along
                                      -- GBCA.ByABDY.gbcaLabelMap

gatherImplRefines P r : roundOverBracha ⊑ GBCA.ByABDY.specificationOverRoundAlphabet   (probabilistic, trans ×2)
```

Beneath the round, the two gather tiers and the broadcast tier, citable on their
own:

```
BRB.brachaInstance P ldr M ⊑ BRB.specInst P ldr M     (brbRefines, ReliableBroadcast/BrachaRefinesSpecification.lean)
Gather.instanceOverBracha P X   ⊑ Gather.instanceOverBroadcastSpecification P X      (gatherLow,  Gather/BroadcastSubstitution.lean, by congruence)
Gather.instanceOverBroadcastSpecification P X ⊑ Gather.specInst P X       (gatherCore, Gather/RefinesSpecification.lean)
```

Each composition speaks an alphabet of its own, in which the call's
input-enabledness loop is a label of its own, and its specification is read
along a pullback that sends the loop to the call (`BRB.specificationLabelMap`,
`Gather.specificationLabelMap`): the specification answers its call label on two rows, and a
composition whose caller and network are different components could otherwise
combine the caller's loop with the network's post. The round speaks the family
alphabet `ExtendedLabel P.n` natively, as the protocol chain's round
`GBCA.ByABDY.composition` does, so the family's call loops are its loop labels and
`GBCA.ByABDY.gbcaLabelMap` reads its specification.

At the protocol shape (`ImplementationByAFW/CompositionChain.lean`), each round tier is
gathered into the ℕ-indexed family under the corruption broadcast and put through the
composed reading's pipeline; the three substitutions become three stages whose last lands
on `hybrid P`:

```
AFW.protocol ⊑ AFW.composed ⊑ AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid ⊑ ABA.spec
```

Beneath `AFW.composed` is `AFW.protocol`, the gather-based protocol as it runs
(`ABA/ImplementationByAFW/System.lean`), carried into the composed reading by
`AFW.protocolSim` (`ABA/ImplementationByAFW/Simulation.lean`). Everything from `hybrid` up
— the core simulation, `spec_safe`, the safety transfer — is shared with the protocol
chain.

Every protocol-shaped system and headline of this chain sits in the namespace
`AFW`, after Attiya, Flam and Welch, and carries the name of its counterpart in
the protocol chain: `AFW.composed` is to the gather-based implementation what
`ABDY.composed` is to ABDY22's. A `G` elsewhere in the development is graded
agreement — `callG`, `retG`, `GBCANetwork`, `GNetState` — and never the chain.

## What a program holds of a sub-protocol's answer

A program reads no neighbouring component. What a sub-protocol has returned to a
process is therefore written into that process's own record, on the return
event, and read there.

A gather program's record (`Gather.ProcRec`) extends the local record with two
stores: `delivIn k`, the value the input-broadcast instance `k` has returned
here, and `delivBind q`, the payload the bind-broadcast instance `q` has returned
here. The return of an instance is a hidden event of the gather composition
(`Gather.GatherEvent.inRet`, `bindRet`), on which that instance takes its own return
row and the receiving program writes its store. The four rows that read what has
been returned — `sndEcho`, `sndVote`, `bindCall` and `ret` — read the stores
through `Gather.ProcRec.accepted`, `holdsIn`, `holdsBind` and `approvedBy`, in the
same shape at both gather tiers. The tie between a store and the instance it records is an
invariant clause of `Gather.IdealConf` (`delivIn_val`, `delivBind_val`): a
stored value is the instance's committed value, established at the return event
and kept by the write-once commit.

A round program's record (`GBCA.ByAFW.ProcRec`) holds the process's input, its
candidate, whether it has called the second gather, its graded outcome and its
return flag. The first gather's return and the second gather's call are two
events, `ret1` and `call2`, and so are the second gather's return and the
round's graded return, `ret2` and `retG`; the record is what carries the round
across each pair. The graded return drops the recorded outcome, so a record
holds no round's grade after its return.

## The core of the gather specification

The classical binding property of gather says: once the first correct process
returns, there is a set of at least `n − f` entries on which every future
correct return is defined. TS 4 states this with a single set, and
`Gather.SpecState.core : Option (APSet n X)` carries it. The internal rule
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
`coreOfNet`), so the gather network computes it from its own state and writes
it at the first return (D29).

**The counting.** Read `dominatedBy` as an incidence whose rows and columns are
the processes outside `F`. A `VOTE` payload of a process outside `F` is
multicast above `n − f` delivered `ECHO` payloads, and `VOTE` is write-once, so
`n − f ≤ (dominatedBy w q).card` for every `q` outside `F` — vacuously for a `q`
that has multicast no `VOTE`, whose row is everything (`dominatedBy_card`).
Restricting a row to the columns costs at most `|F|`, so every row carries at
least `n − f − |F|` of them (`dominatedBy_honest_card`). Summing the rows and
reading the same sum by columns (`sum_dominatedBy`) gives a column `j₀` outside
`F` with `n − f − |F| ≤ (dominators w j₀).card` (`exists_dominators`), and
`n − f − |F| ≥ f + 1` under `n > 3f` and `|F| ≤ f`. The core is `j₀`'s `ECHO`
payload, whose own send guard gives it `n − f` entries.

**The transfer.** Take a committed `BIND` payload `U` of a process outside `F`.
It is that process's contributed payload, multicast above `n − f` delivered
`VOTE` payloads. Those `n − f` senders meet the `f + 1` dominators of `j₀` in a
process `q`, whose write-once `VOTE` payload lies above the core by domination
and below `U` by the bind guard, so `coreOf P w ⊆ U` (`transfer`,
`single_core`). Every `ECHO` field holds entries of the sender's input store,
and a stored value is a committed value, so the core's entries are committed
entries (`single_core_approved`), which is `bindCore`'s other guard.

**The freeze certificate.** `coreOf_freeze` packages the three facts with the
count the simulation carries along the run: at least `f + 1` coordinates hold a
committed `BIND` payload above the core (`Gather.bindAbove`). That count is
blind to `F` and monotone under every rule (`bindAbove_mono`), so it survives
every later corruption, and it is what holds the returns after the first to the
set the first one froze. A returner's quorum of `n − f` stored payloads is a
quorum of committed payloads, it meets the `f + 1` certified coordinates, and
BRB values are functional, so the returned map lies above the frozen core.

**Why the counting closes here.** `BIND` payloads travel by reliable broadcast
rather than on the gather network, so a committed payload is write-once
whatever happens to its sender afterwards, where a multicast payload is pinned
only by its sender's honesty and D1 withdraws that at any moment. A gather
instance holds one bind-broadcast instance per process, and the `BIND` send is
that instance's call, a hidden event of the composition (D32), which is what
makes the objects the certificate counts stable.

## The commit splits (D26, D27)

The same dynamic-corruption reading, one level down. TS 6 pins the delivered
value at an honest `call`; Bracha's rounds with the leader corrupted after
its `INIT` can deliver a different value until some correct process holds an
ECHO quorum of more than `(n+f)/2` senders, so the pinned specification
excludes its own implementation
(`NOTES-Fidelity.md` §5). `BRB.SpecState` therefore splits `input` (the
call's record) from `val` (the committed value), with the commit τ-rule
guarded `ldr ∈ F ∨ input = some m`: the corrupted leader's power is a commit
of any value, the honest leader's value is pinned, and the window closes at
the commit. `Gather.SpecState` carries the per-entry form: `call` and `val`
split, `Gather.Step.commit` guarded `k ∈ F ∨ call k = some v`.

The refinement counterpart is *commit-on-demand*: the abstract commit is a
τ-rule with no implementation event to synchronise with, so the simulations
fire it inside the weak answer of the first row that reads it —
`BRB.commitReach` under a return, the `commitOne/commitList` chains of
`ABA/Gather/RefinesSpecification.lean` under a return.

The gather specification's call record follows the input instance's record
rather than the gather program's (`Gather.CoreRel.call_eq`). The specification's
call record and an input instance's call record move on the same interface
labels, the call and the call loop, under the same write-once guard, and a
broadcast specification answers either label on either of its two rows; the
gather program's record and the instance's record can therefore differ, and the
specification's `commit` guard is dischargeable against the instance's.

## Counting at the pair tier (`pairRefines`)

`roundOverGatherSpecifications` is AFW25's Algorithm 4 at `R = 2`, its two-gather branch
(D24): candidate at `|dom g| − f` occurrences after the first gather, grade at
`|dom h| − f` / `f + 1` after the second. The refinement into TS 2 certifies
the specification's `excluded` and `grade` on the two instances' frozen cores.
One transfer lemma carries a count from a returned map down to a core below
it: `cnt_heavy_of_subMap` (AFW25 Lemma 13) says that a map heavy at `x` — all
but `f` of its entries — makes such a core heavy at `x` too, the core sitting
below the map and losing at most `f` entries to it.

A core has at least `n − f > 2f` entries, so at most one value is heavy in it,
and the three certificates are readings of that:

- the round's bound bit is `GBCA.boundOfCore` of the first instance's core —
  its heavy bit where one exists (`boundOfCore_of_heavy`), the complement
  being light (`cnt_boundOfCore_light`); the layer's network writes it at the
  first gather's return, from the core that return carries;
- the exclusion certificate is
  `ExcludedEv b = ∃ S, core₁ = some S ∧ cnt S b < |S| − f`. The core is
  write-once, so the certificate is frozen the moment it holds — monotonicity
  for free, where the direct implementation's refinement maintains monotone
  receipt walls;
- the A/C grade exclusivity is the second instance's core being heavy at
  `some v` on the A side and light at both bits on the C side.

The two-event link and return place the certificates in the invariant
(`GBCA.ByAFW.PairInv`). A candidate is heavy in the first core (`cand_heavy`) or, at
`⊥`, certifies `f + 1` for both bits (`cand_bot`); both are established at
`ret1`, where the first gather's return carries the core, and consumed at
`call2`, where the second gather's call record takes the candidate
(`call2_cand`). The bound bit is on record from the first `ret1` on
(`cand_bound`, `call2_bound`). The graded outcome's certificate, `OutCert`, is
established at `ret2` from the second gather's return and consumed at `retG`,
which sees the outcome alone (`out_cert`). The return rows then mirror
`GBCASim.implRefines` shape for shape: an `A`/`B` return hands out the bound bit
and certifies `ExcludedEv` of its complement, and the `C`-return announces the
bit the first return wrote. The D15 support counts come off the first core
through the committed-entry provenance — a core entry is a committed entry, a
committed entry of an honest process is its call, and the count is `F`-blind
(`supp_spec_of_core`) — or off an honest `⊥` candidate. Exclusions fire on
demand as the two-step run `bindUnset; ret`, as in the direct refinement.

## Substitution by congruence

A substitution that replaces a component by a system that simulates it is an
application of the congruences of `Framework/Congruence.lean`: forward
simulation between labelled transition systems survives parallel composition on
either side, the synchronised product of a finite family, hiding and restriction,
and two simulations compose. Every substitution inside a composition of the stack
is proved that way and nothing else:

- `Gather.gatherLow` lifts `BRB.brbRefines` at each of the `2n` broadcast
  coordinates along the pullback naming the coordinate
  (`ForwardSimulation.mapIdle`), through the two synchronised products, the
  parallel composition with the gather tier held, the hiding and the
  restriction; its relation `Gather.LowRel` is the gather tier held equal beside
  `BRB.InstRel` at every coordinate (`ABA/Gather/BroadcastSubstitution.lean`);
- `GBCA.ByAFW.lowPairRefines` and `GBCA.ByAFW.idealRefines` lift `Gather.gatherLow` and
  `Gather.gatherCore` at each of the two gather coordinates the same way, with
  the layer held (`ABA/GBCA/AFW/GatherSubstitutions.lean`); their relations hold the
  layer equal beside the gather relation at each gather.

The two refinements into a specification, `Gather.gatherCore` and
`GBCA.ByAFW.pairRefines`, are proved on the compositions themselves. Each composition
carries a row characterisation — `Gather.instanceOverBroadcastSpecification_step_iff_row`,
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_row` — stating that its transitions over
the labels the pullback sends to one specification label are exactly the rows of a rule table
at that label (`Gather.StepOverBroadcastSpecification`,
`GBCA.ByAFW.StepOverGatherSpecifications`), on the same state and with the same
distribution. A refinement is then a case analysis over the rows, and the specification's
answer, a run of `specInst`, is lifted to the specification read along the pullback by a
section of it (`Gather.weakLStep_specificationOverInstanceAlphabet`,
`GBCA.ByABDY.weakLStep_specificationOverRoundAlphabet`), as `GBCA.ByABDY.subSim` does for
the protocol chain's round.

Two facts of the characterisations are worth reading. A specification answers its call
label on two rows, so where a specification is a component the composition offers both
rows under either interface label, and the rule table lists the combinations: four call
rows at the gather-over-specification tier, two at the round's pair tier. And a label
outside a round's interface blocks the round rather than letting it idle
(`GBCA.ByAFW.ProgramLabel.outside`), exactly as `GBCA.ByABDY.composition` blocks, which is
what makes the pair tier's characterisation exact at the specification's labels.

## The assembly at the protocol shape (`ImplementationByAFW/CompositionChain.lean`)

Two ingredients, both shared with the protocol chain:

- **The family congruence** (`ForwardSimulation.family`): per-round simulations lift to
  the ℕ-indexed sides; the broadcast hypothesis is each relation's lockstep-corruption
  statement (`lowPairRel_corrupt`, `idealRel_corrupt`, `pairRel_corrupt`), exactly as
  `subSim_failAct` discharges it for the protocol chain. The family's act corrupts the two
  gathers of every round and leaves the programs and the layer's network alone.
- **The four congruences** (`parallel_right`, `abstract`, `relabel`, `abstract`): each
  family substitution runs under the composed reading's own context, the same term
  `Composition/HybridAndSubstitution.lean`'s `ABDY.substSim` uses, so the third stage's
  target is definitionally `hybrid P`.

The round speaks the family alphabet natively, so no lift precedes the family;
the sides are `System.family (GBCA.ByAFW.roundOverBracha P) gOwns isFailN gActLow` and
their two siblings, as `GBCA.ByABDY.gbcaInstanceFamily` is. The stages compose by
`ProbabilisticForwardSimulation.trans`; the inclusions compose by
`Set.Subset.trans` and never invoke transitivity of simulation — the two routes
of `Results.lean`, reproduced.

## The protocol beneath the composed reading (`ImplementationByAFW/System.lean`,
`ImplementationByAFW/RoundProjection.lean`, `ImplementationByAFW/RoundProjectionStep.lean`,
`ImplementationByAFW/Simulation.lean`)

`AFW.composed P` is the gather-based protocol read as a composition of components. What
runs is a flat system: `n` programs, each reading its own records and nothing else, beside
one network adversary holding every sent set and the corrupted set, beside the coin
oracle. That shape is the same for either implementation of graded agreement — the round
loop, the DECIDED sets, the coin handshake, corruption, the adversary's table and the
composition pipeline are fixed by the round interface and the specification — so
`ABA/Implementation/System.lean` writes it once, parametric in the stage message type `M`,
the per-process per-round stage record `S`, the stage-side rows, supplied as a relation
embedded in one constructor of the program table, and the adversary's per-round ghost
record `G` with its update `ghostStep` and its output `ghostOut` (D30).
`ABA/ImplementationByABDY/System.lean` instantiates it at ABDY22's implementation;
`ABA/ImplementationByAFW/System.lean` instantiates it here.

The division of labour is by label. `Implementation.roundOwn j` is the set of label
classes an implementation owns at process `j`: the graded-agreement call and
return, `j`'s own stage multicast, a delivery addressed to `j`, and `j`'s call
against an already-opened record. An instantiation supplies `Implementation.IsRoundRuleTable`
— its rows carry such a label, fire only at an unreplaced program, and are
Dirac — and the shared inversion lemmas consume exactly those three facts.
`AFW.stageRow_of_own` runs the argument the other way: a program's step on a
label of `roundOwn j` is a step of the implementation, which is what lets each
case of the simulation rule the others out.

Three things separate the flat stage side from the composed reading's, and all
three are forced by the flat shape.

- **The tagged sent set.** A round of `AFW.composed` carries `4n + 2`
  network components — one per gather instance, one per Bracha instance. A flat
  adversary carries one sent-set family per round, so `AFW.Msg n` tags each
  message with the network it belongs to, and for a Bracha message with the
  instance, whose index is its leader. The sender index stays the sender, so a
  threshold still counts distinct senders (D5). No new adversary rows are
  needed: recording a multicast, checking a delivery and authorising a handshake row are
  already payload-blind.
- **The transposition.** The composed reading indexes local states by instance
  and then by process. A program must hold its own data and no one else's, so
  `AFW.StageRec n` is process-major: process `j`'s local state in each gather
  instance, and its local state in each of the `n` instances of each broadcast family.
  Nothing is lost, because every guard of the gather-based implementation
  reads the acting process's own local states and the networks, and the two rows that
  read a network — the adversary's delivery and its Byzantine injection —
  belong to the adversary either way.
- **The fused rows.** A flat program takes one row per thing it does, so the
  graded-agreement call broadcasts the input, the `BIND` send is a broadcast
  call, and the first gather's return to a process is that process's call of the
  second gather (D28). The flat reading has no broadcast return either: a gather
  guard reads a `2f + 1` `VOTE` receipt quorum on the acting process's own local
  state in the instance (`apIn1` and its companions), where a composed gather
  program reads its store.

`AFW.ProtocolRel` has six conjuncts. The round loop, the coin oracle and the
ABA-side network are shared objects, and the round family is *computed* from
the flat state by `AFW.toRound`, which undoes the three separations: it
transposes the local states back, slices each network's sent set out of the
tagged family by `Finset.filterMap`, and reads each store off the process's own
local state in the instance as the value with a vote quorum there
(`AFW.storeIn`), the composed broadcast program's return flag being whether the
store holds a value. A round program's record is read off the process's two
gather inputs and its second-gather return flag, its recorded outcome being
`none` outside a run. Four of the six conjuncts are that computation, so there
is nothing to choose in the witness.

The ghost is part of that computation. The composed round holds three values no
guard of it reads — the core of each of its two gather networks and the layer's
network's bound bit — and the adversary holds the same three as the round's
ghost record `AFW.Ghost`, which `AFW.toRound` reads them off. Two rows write the
record. The link's broadcast of the candidate freezes the first gather's core at
`Gather.coreOf` of that gather's slice of the tagged sent sets, and the bound bit
at `GBCA.boundOfCore` of that core; a graded return freezes the second core the
same way. The composed `ret1` and `ret2` freeze the same two values off the core
their gather's return carries, and the values agree because each is
`Gather.coreOfNet` of one network's state (`coreOfNet_toGa1`, `coreOfNet_toGa2`).

The fifth conjunct, `AFW.BoundInv`, is what makes the announced bits agree: a
process whose round-`r` second-gather local state carries an input has passed
that round's link, so the round's bound bit is on record. The sixth,
`AFW.StoreInv`, is the broadcast invariant `BRB.Inv` at every broadcast
instance of the view. It is what identifies the stored value with the value a
flat guard names: a flat row hands its composed counterpart a specific value
with a vote quorum, the store holds the value the view chose, and under the
invariant two vote quorums at one process name one value
(`BRB.echoCert_unique`, `AFW.storeIn_eq_of_quorum`). The invariant is carried
on the composed side and re-established after every matched row by the
instance's own preservation lemma, since every matched composed step is a
genuine step of the instance.

The proof is organised around that computation.
`ABA/ImplementationByAFW/RoundProjectionStep.lean` states, for every flat row, the view
after the row as the composed round before the row with the corresponding composed effect
applied, written through the round's updaters exactly as the row tables write it; the
master lemma `toRound_write` pushes a one-point stage write and a single sent-set
insertion inside every coordinate, and each row then owes only slice algebra, discharged
by `slice_post_some` and `slice_post_none`. `ABA/ImplementationByAFW/Simulation.lean`
matches each flat row by a run of the composed group: a send and a delivery are hidden
events of the round instance, answered by one of its silent steps, the adversary's
authenticity conjunct becoming membership in the sliced sent set; the call is the
instance's own. Three flat rows are answered by two composed steps, through the
intermediate states `Frame.lean` names: the link by `ret1` then `call2`, the graded return
by `ret2` then the visible `retG`, and a delivery that completes a vote quorum by the
instance's delivery then its return, which writes the store (`toRound_ret1_call2`,
`toRound_ret2_retG`, the `_ret` delivery lemmas). The remaining labels move the round loop
and the ABA-side network while the family of rounds stands still, and corruption is one
broadcast, the corrupted set the adversary holds being the corrupted set of every network
under the same guard.

`ABA/ImplementationByAFW/Simulation.lean` closes with the headlines mirroring
`Results.lean`'s: `AFW.protocol_composed`, `AFW.refines`, `AFW.main` and `AFW.chainSim`,
each behind a `#print axioms` check.

## Boundaries

- The union sends of the source's Algorithm 4 are read as bounds
  (`NOTES-Fidelity.md` §2); the widening is monotone in every guard the
  proofs consume.
- Liveness — gather Termination, BRB Totality — is unclaimed throughout
  (`NOTES-Fidelity.md` §6).
