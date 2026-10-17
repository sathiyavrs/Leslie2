# Design — the input-output discipline of the components

Every system of the case study is a composition under full synchronisation: a non-silent label
fires when every component takes a transition on it, the component that acts and every other one
idling. LeslieBP §1.3 restricts such compositions to the input-output approach: "the set of labels
is partitioned between input labels In and output labels Out", "we require that the input labels
are always enabled", a requirement "easily fulfilled by adding self-looping transition labelled by
each input label to all states", and "we restrict composition to PLTSs whose outputs labels are
distinct". The simulations paper states the same as Assumption 1 (input-enabledness) and
Definition 2 (two systems are compatible if `Out₁ ∩ Out₂ = ∅`). Under these two conditions a
composition creates no deadlock, and the inclusion of fair traces is preserved by composition.

This note records that discipline as the tree carries it: which component outputs each label,
where each guard sits, and which loop makes each input enabled. It also records the four parts of
the model that come with it: the started rounds of D37, the announcement events of D29 and D30,
the finite maps of the families and the network, and the loops on the call labels. Each constraint
names the statement that is false or unprovable without it, so that a reader can tell a
constraint from a convention. The entries D11, D23, D29, D30 and D37 are stated in
`blueprint/src/deviations.tex`, the registry of record, and the sections below point at them.

## 1. Inputs and outputs

`Framework/InputEnabledness.lean` states the discipline. `System.InputEnabled sys A` holds when
every label of `A` has a transition at every state:

```
System.InputEnabled sys A  :=  ∀ s, ∀ l ∈ A, ∃ μ, sys.step s l μ
```

`InputOutputLabels L` is a pair of label sets, `inputLabels` and `outputLabels`, and
`InputOutputLabels.Compatible a b := Disjoint a.outputLabels b.outputLabels` is Definition 2 of the
simulations paper. A guard on an output decides whether the component that outputs the label
acts; a guard on an input would let a component refuse a label another component outputs, and
that is what the discipline excludes.

The five combinators the compositions are built from preserve input-enabledness. Let `sys` be
input-enabled on `A`. Then `System.withIdle sys busy` is input-enabled on `A` and on every label
outside `busy`, and `System.mapIdle φ sys` on every label with no image under `φ` and on every label
whose image lies in `A`. `System.parallel` of two systems is input-enabled on the intersection of
their two sets, and `System.synchronisedProduct` of a nonempty family on the intersection of all of
them (the silent label needs a component to move, so an empty family has no silent transition).
`System.family inst owns glob act initial` is input-enabled on every non-silent label that `owns`
assigns to no instance, on every broadcast label, and on every label that `owns` assigns to an
instance input-enabled on it; its silent transitions range over the rounds of its map, so the
silent label is not among them. The outputs of a composite are the union of the outputs of its
components, which the compatibility lemma asks to be pairwise disjoint.

A component under full synchronisation takes as inputs every non-silent label outside its outputs.
Its `_inputEnabled` theorem therefore covers the labels it idles on as well as the labels it reads.
An instance inside a family takes as inputs only the labels the family assigns to it, and a system
read along a pullback only the labels the pullback carries to it, less its outputs: a round's
graded-agreement instance has no transition at the labels of another round, and the family idles
there (`DESIGN-Decomposition.md` §4).

Each level carries a file `InputEnabledness.lean` after its `Components.lean`, with the label sets
of the level's components, one `<component>_inputEnabled` theorem per component and one
`<composition>_compatible` lemma per composition. In the tables below a label is written without
its `Sum` injections, `_` stands for any value, and `j` is the process the component belongs to.

### The implementation

`Implementation.systemExtended` is the synchronised product of the `n` programs, in parallel with
the network and the lifted coin (`Implementation/System.lean`). The lemma is
`Implementation.systemExtended_compatible`.

| component | outputs | inputs | every input enabled by |
|---|---|---|---|
| `program j` (`ProgramStep`) | `callG _ j _`, `retG _ j _`, `gbcaSend _ j _`, `gbcaRoundEvent _ j _` (the round's transitions `roundStep`); `callW _ j`; `decidedSend j _`; `decidedRelay j _`; `retABA j _` | every other non-silent label | `input` and `inputLoop` (D36); `retW` and `retWLoop`; the round's delivery and `deliverLoop`; `decidedDeliverReceive` and `decidedDeliverLoop`; `failSelf`; `boundGIdle`; `byzantineCallGIdle` and `byzantineCallWIdle` at every process; an idle transition for each label at another process; at a replaced program, `corruptedIdle` |
| `network` (`NetworkStep`) | `gbcaDeliver`, `decidedDeliver`, `fail`, `byzantineCallG`, `byzantineCallW`, `boundG`; silent: `byzantineGBCA`, `byzantineDecided` | `callABA`, `retABA`, `callG`, `retG`, `callW`, `retW`, `gbcaSend`, `gbcaRoundEvent`, `decidedSend`, `decidedRelay` | one unguarded transition per input; `callG` writes the started rounds (§3), `retG` and `gbcaRoundEvent` write the ghost (§4), `gbcaSend`, `decidedSend` and `decidedRelay` record the message |
| coin (`coinOverExtendedAlphabet`) | `retW` (`WCC.Step.ret`); silent: `WCC.Step.resolve` | `callW`, `byzantineCallW`, `fail`, every other label | `WCC.Step.call` and `WCC.Step.callLoop` on both call labels through `coinLabelMap`; `fail` by the family's broadcast; every other label by the family's or the pullback's idle transition |

A replaced program takes no transition on the labels of `actsAt j` and takes every other
non-silent label on `corruptedIdle` (§7).

### The composed systems and `hybrid`

`ABDY.composedExtended`, `hybridExtended` and the three composed systems of `AFW/Composition.lean`
place a round family in parallel with the `n` round loops, the ABA network and the lifted coin
(`Composition/Components.lean`). The lemma is `Composition.composedComponents_compatible`, which
states the outputs of the round loops, the ABA network, the round family and the coin pairwise
disjoint for every round family. The round families are input-enabled by
`GBCA.ByABDY.gbcaInstanceFamily_inputEnabled`, `gbcaSpecificationFamily_inputEnabled`,
`AFW.roundFamilyOverBracha_inputEnabled`, `AFW.roundFamilyOverBroadcastSpecification_inputEnabled`
and `AFW.roundFamilyOverGatherSpecifications_inputEnabled`.

| component | outputs | inputs | every input enabled by |
|---|---|---|---|
| round loop `j` (`RoundLoopStep`) | `callG _ j _`, `callW _ j`, `decidedSend j _`, `decidedRelay j _`, `retABA j _` | every other non-silent label | `input` and `inputLoop` (D36); `retG` and `retGLoop`; `retW` and `retWLoop`; `decidedDeliverReceive` and `decidedDeliverLoop`; `failSelf`; `boundGIdle`; over ABDY22's messages, `gbcaSendIdle` and `gbcaDeliverIdle` at every process; the Byzantine idles; an idle transition for each label at another process; at a replaced round loop, `corruptedIdle` outside `roundLoopActsAt j` |
| ABA network (`ABANetworkStep`) | `decidedDeliver`, `fail`, `byzantineCallG`, `byzantineCallW`; silent: `byzantineDecided`; over ABDY22's messages, `gbcaSend` and `gbcaDeliver`, on which it has no transition | `callABA`, `retABA`, `callG`, `retG`, `boundG`, `callW`, `retW`, `decidedSend`, `decidedRelay` | one unguarded transition per input; `callG` writes the started rounds (§3); `decidedSend` and `decidedRelay` record the bit |
| coin (`coinOverRoundAlphabet`) | `retW`; silent: the resolution | as at the implementation | as at the implementation |
| round family (`GBCA.ByABDY.gbcaInstanceFamily`, `gbcaSpecificationFamily`, `AFW.roundFamilyOverBracha`, `AFW.roundFamilyOverBroadcastSpecification`, `AFW.roundFamilyOverGatherSpecifications`) | `retG`, `boundG`; silent: the instances' | `callG`, `byzantineCallG`, `fail`, every label `roundOwnsLabel` assigns to no round | the instance's call or loop at the round `roundOwnsLabel` names; `fail` by the broadcast; every other label by the family's idle |

Over ABDY22's messages the extended alphabet has the round multicast and the round delivery, which
the round instance exchanges under labels of its own and hides. The ABA network outputs them and
never fires them, and every other component idles on them. Over the gather-based chain's message
type `Empty` they name no label.

### Bracha's reliable broadcast

`BRB.brachaInstanceExtended` places the `n` programs beside the instance's network over
`BroadcastLabel n M = Label n M ⊕ BroadcastEvent n M`. The lemma is `BRB.brachaInstance_compatible`,
and `BRB.brachaInstance_inputEnabled` states the instance input-enabled on the inputs of the BRB
specification.

| component | outputs | inputs | every input enabled by |
|---|---|---|---|
| program `j` (`BRB.ProgramStep`) | `send j _` (`sendInit`, `sendEcho`, `sendVoteQuorum`, `sendVoteAmplification`), `ret j _` | `call`, `send` and `ret` at another process, `deliver`, `fail` | at the leader, `call` at a program holding no input and `callLoop` at a program holding one; elsewhere `callIdle`; `deliverReceive`, `deliverIdle`, `sendIdle`, `retIdle`, `failIdle` |
| network (`BRB.NetworkStep`) | `deliver`; silent: `byzantine` | `call`, `send`, `ret`, `fail` | one unguarded transition per input |

### Gather

`Gather.instanceOverBroadcastsExtended` places the `n` gather programs beside the gather network,
in parallel with the `n` input broadcasts, each read along `Gather.inputBroadcastLabelMap k`; the
input broadcast is `BRB.brachaInstance` in `Gather.instanceOverBracha` and the BRB specification in
`Gather.instanceOverBroadcastSpecification`. The lemma is
`Gather.instanceOverBroadcastsExtended_compatible`.

| component | outputs | inputs | every input enabled by |
|---|---|---|---|
| gather program `j` (`Gather.ProgramStep`) | `send j _` (`sendEcho`, `sendVote`, `sendBind`), `inputBroadcastCall j _`, `ret j _` | `call`, `deliver`, `inputBroadcastRet`, `core`, `fail`, and the outputs of another process | `call` at a program holding no input and `callLoop` at a program holding one; `deliverReceive`; `inputBroadcastRetReceive`; `coreIdle`; `failIdle`; an idle transition for each label at another process |
| gather network (`Gather.NetworkStep`) | `deliver`, `core` (`announceCore`); silent: `byzantine` | `call`, `send`, `ret`, `inputBroadcastCall`, `inputBroadcastRet`, `fail` | one unguarded transition per input; `ret` writes the core at the instance's first return (§4) |
| input broadcast `k` | `inputBroadcastRet k _ _` | `inputBroadcastCall k _`, `fail`, every other label | the leader's `call` or `callLoop` (the specification's `call` or `callLoop`); `fail`; the pullback's idle |

### Graded agreement by ABDY22's algorithm

`GBCA.ByABDY.compositionExtended` places the `n` programs of round `r` beside the round's network
over `GBCALabel n = ExtendedLabel n Message ⊕ GBCAEvent n`. In the family the instance takes the
labels `roundOwnsLabel` assigns to round `r`, so its inputs are `callG r _ _` and
`byzantineCallG r _ _`. The lemma is `GBCA.ByABDY.compositionExtended_compatible`.

| component | outputs | inputs | every input enabled by |
|---|---|---|---|
| program `j` (`GBCAProgramStep`) | `send j _` (the nine sends), `retG r j _` (`retGrade2`, `retGrade1`, `retGrade0`) | `callG r _ _`, `byzantineCallG r _ _`, `deliver`, `boundG r _`, the outputs of another process | `call` and `callLoop`; `byzantineCall` and `byzantineCallLoop`; `deliverReceive`; `boundGIdle`; an idle transition for each label at another process |
| round's network (`GBCANetworkStep`) | `deliver`, `boundG r _` (`announceBound`); silent: `byzantineGBCA` | `send`, `callG`, `byzantineCallG`, `retG` | one unguarded transition per input; `retG` writes the bound bit at the round's first return (§4) |

### Graded agreement by the two gathers

`GBCA.ByAFW.roundOverGathersExtended` places the round's programs and the round's network, each
read along `GBCA.ByAFW.programLabelMap`, in parallel with the first gather read along
`firstGatherLabelMap` and the second along `secondGatherLabelMap`, over
`RoundLabel n = ExtendedLabel n Empty ⊕ RoundEvent n`. The round events are `firstGatherReturn id g`,
`firstGatherCore C`, `secondGatherCall id x` and `secondGatherReturn id g`. The lemma is
`GBCA.ByAFW.roundOverGathersExtended_compatible`.

| component | outputs | inputs | every input enabled by |
|---|---|---|---|
| program `j` (`GBCA.ByAFW.ProgramStep`) | `secondGatherCall j _`, `retG r j _` | `callG`, `byzantineCallG`, `firstGatherReturn`, `firstGatherCore`, `secondGatherReturn`, `boundG`, `fail`, the outputs of another process | `callG` and `callLoop`; `firstGatherReturn` and `firstGatherReturnLoop`; `secondGatherReturn` and `secondGatherReturnLoop`; `firstGatherCoreIdle`, `boundGIdle`; `fail` by the pullback's idle; an idle transition for each label at another process |
| round's network (`GBCA.ByAFW.NetworkStep`) | `boundG r _` (`announceBound`) | `callG`, `firstGatherReturn`, `firstGatherCore`, `secondGatherCall`, `secondGatherReturn`, `retG` | one unguarded transition per input; `firstGatherCore` records the first core, `retG` records the round's first return (§4) |
| first gather | `firstGatherReturn`, `firstGatherCore` | `callG r _ _`, `byzantineCallG r _ _`, `fail` | the gather's `call` or `callLoop`; `fail` |
| second gather | `secondGatherReturn` | `secondGatherCall`, `fail` | the gather's `call` or `callLoop`; `fail` |

The second gather's core announcement has no round label over it, so it never fires inside the round.
A family label outside the round's interface maps to `ProgramLabel.outside` and blocks the round
(`DESIGN-Decomposition.md` §4); the family assigns no such label to the round, so it is no input
of the round.

### The five specifications and the coin

Each specification is one component, over its own alphabet. The lemmas are
`ABA.spec_inputEnabled`, `GBCA.specInst_inputEnabled`, `WCC.specInst_inputEnabled`,
`Gather.specInst_inputEnabled` and `BRB.specInst_inputEnabled`, with the family lemmas
`GBCA.specFamily_inputEnabled` and `WCC.specFamily_inputEnabled`.

| specification | outputs | inputs | every input enabled by |
|---|---|---|---|
| Transition System 1 (`ABA.spec`) | `retABA` (`ret`, `retByzantine`), `fail` (`fail`, under `id ∉ F` and `|F| < f`); silent: `coinFlip`, `decide` | `callABA` | `callSet` at an empty entry, `callLoop` at a filled one, `callByzantine` at a corrupted caller |
| Transition System 2 (`GBCA.specInst`) | `retG` (`retGrade2`, `retGrade1`, `retGrade0`), `boundG` (`announceBound`); silent: `bindUnset` | `callG`, `fail` | `call` and `callLoop`; `fail` |
| Transition System 3 (`WCC.specInst`) | `retW` (`ret`); silent: `resolve` | `callW`, `fail` | `call` and `callLoop`; `fail` |
| Transition System 4 (`Gather.specInst`) | `ret`, `core` (`announceCore`); silent: `commit`, `bindCore` | `call`, `fail` | `call` and `callLoop`; `fail` |
| the BRB specification (`BRB.specInst`) | `ret`; silent: `commit` | `call`, `fail` | `call` and `callLoop`; `fail` |

The source lists `fail` among the inputs of all five transition systems. Four of them take it on a
total transition. Transition System 1 guards it by the budget, so `fail` is an output there, as it
is at the implementation's network and at the ABA network (D1).

## 2. Guards on outputs

The table below pairs each guard that would sit on an input with the transition that carries it.
A guard on an output is a guard of the component that outputs the label. A guard on a value that
an announcement carries has no place on a return (§4).

**What fails.** Let a component guard a label another component outputs. At a state where the guard
fails and the transition of the component that outputs the label is enabled, the composite has no
transition on the label, a deadlock "that is an artefact of the model rather than a genuine protocol
issue" (the simulations paper, after Assumption 1). The `_inputEnabled` theorem of that component is
false, and LeslieBP §1.3's argument that composition preserves the inclusion of fair traces does not
apply to the composition.

**The constraint.** Each guard below sits at the component that outputs its label, or the input
it guards has a loop that fires exactly where its other transitions do not.

| component | constructor | guard on an input | where it sits |
|---|---|---|---|
| program | `ProgramStep.input` | `input = none` | `input` at an empty input beside `inputLoop` at a filled one (D36) |
| program | `ProgramStep.retW` | phase `awaitW`, round `r` | `retWLoop` at an unreplaced program where either fails; `corruptedIdle` at a replaced program |
| program | `ProgramStep.failSelf` | `corrupted = false` | `failSelf` at an unreplaced program beside `corruptedIdle` at a replaced one |
| program | `ProgramStep.decidedDeliverReceive` | `b ∉ decidedDelivered k` | `decidedDeliverLoop` at `b ∈ decidedDelivered k`; `corruptedIdle` at a replaced program, the delivery being outside `actsAt j` |
| program | `ABDY.RoundStep.gbcaDeliverReceive`, `AFW.RoundStep.gbcaDeliverReceive` | `hterm`, `hh` | `deliverLoop` at a terminated program; `corruptedIdle` at a replaced program, the delivery being outside `actsAt j` |
| network | `NetworkStep.decidedRelay` | `b ∉ decidedSent j` | `ProgramStep.decidedRelay` as `b ∉ c.decidedSent`, LeslieBP Algorithm 1's "having not sent it" |
| network | `NetworkStep.retABAIdle` | `b ∈ decidedSent id` | `ProgramStep.ret` as `b ∈ c.decidedSent`, "having sent it"; the network takes `retABA` on one unguarded transition |
| round loop | `RoundLoopStep.retG` | phase `awaitG`, round `r` | `retGLoop`; `corruptedIdle` at a replaced round loop |
| round loop | `RoundLoopStep.retW` | phase `awaitW`, round `r` | `retWLoop`; `corruptedIdle` at a replaced round loop |
| round loop | `RoundLoopStep.decidedDeliverReceive` | `b ∉ decidedDelivered k` | `decidedDeliverLoop`; `corruptedIdle` at a replaced round loop |
| ABA network | `ABANetworkStep.decidedRelay` | `b ∉ decidedSent j` | `RoundLoopStep.decidedRelay` as `b ∉ c.decidedSent` |
| ABA network | `ABANetworkStep.retABAIdle` | `b ∈ decidedSent id` | `RoundLoopStep.ret` as `b ∈ c.decidedSent`; one unguarded transition |
| ABDY22's round | `GBCAProgramStep.call`, `GBCAProgramStep.byzantineCall` | `input = none` | `callLoop`, `byzantineCallLoop` on the same label at `input ≠ none` (§6) |
| gather-based round | `GBCA.ByAFW.ProgramStep.callG` | `input = none` | `callLoop` on the call label at `input ≠ none` |
| gather-based round | `GBCA.ByAFW.ProgramStep.firstGatherReturn` | `hin`, `hc` | `firstGatherReturnLoop` where either fails |
| gather-based round | `GBCA.ByAFW.ProgramStep.secondGatherReturn` | `h2`, `ho` | `secondGatherReturnLoop` where either fails |
| Bracha | `BRB.ProgramStep.call` at the leader | `input = none` | `callLoop` on the call label at `input ≠ none`; it takes a repeated `inputBroadcastCall` of the gather above |
| gather | `Gather.ProgramStep.call` | `input = none` | `callLoop` on the call label at `input ≠ none` |
| specifications | `SpecStep.callSet`; `GBCA.Step.call`, `WCC.Step.call`, `Gather.Step.call`, `BRB.Step.call` | an empty entry | the call at an empty entry beside `SpecStep.callLoop` and `callByzantine`, and beside the four unguarded `callLoop` transitions |

Every other input is taken on an unguarded transition. Both networks take `retABA` on one
unguarded transition at every process, corrupted or not, and the returner's own record of its
DECIDED sends guards a correct return (§7). The networks take a graded or a gather return at any
value: `NetworkStep.retG`, `GBCANetworkStep.retG`, `GBCA.ByAFW.NetworkStep.retG` and
`Gather.NetworkStep.ret` write the value the network computes, and an event of the network's own
announces it (§4). Every program idles on a corrupted process's call `byzantineCallG r k b`, the
process `k` included (`ProgramStep.byzantineCallGIdle`). No alphabet carries a Byzantine return
label: a return to a corrupted process is the instance's own return (§7).

The program's record of its own DECIDED sends is `RoundLoopVariables.decidedSent : Finset Bool`,
written at `decidedSend` and at `decidedRelay`, the two sends LeslieBP's Algorithm 1 has. The
network holds its own `decidedSent j`, written on the same two labels and by `byzantineDecided`,
for the guard of its delivery (D12′). The two records agree at every process outside `F`, which is
the invariant that matches the program's `ret` and `decidedRelay` with the transitions of the
composed system and of Transition System 1.

Two consequences lie outside the discipline. First, Transition Systems 2 and 3 return to a process
that has not called, as the source's do, so in `hybrid` and at the coin a return can reach a round
loop or a program that stands at another phase or round. The loop takes it, and the instance
records the return. Safety is unaffected; `NOTES-Liveness-Roadmap.md` §8 records what it means for
fairness. The returns of the two graded-agreement implementations ask for the returner's call, so
there `retGLoop` is not reached at an unreplaced round loop. Second, `RoundLoopStep.ret` and
`RoundLoopStep.decidedRelay` carry no participation guard, where `ProgramStep.ret` and
`ProgramStep.decidedRelay` carry `hin` (D8). Both are outputs, so the discipline leaves them as
they are.

## 3. The started rounds

A corrupted process acts at rounds a correct process has started, in ABDY22's verb: a party
"starts round `r`". The network records the set of such rounds, the rounds at which a process
outside `F` has called graded agreement.

```
NetworkState.startedRounds     : Finset ℕ   -- initially ∅
ABANetworkState.startedRounds  : Finset ℕ   -- initially ∅
recordStartedRound s r id  :=  if id ∉ s.F then { s with startedRounds := insert r s.startedRounds } else s
```

The network writes it on its transition on `callG r id b`, which is an input of the network and an
output of the program, or of the round loop, of `id`. The initial set is empty, so the adversary
acts at no round before the first correct call. A replaced program takes no transition on `callG`,
so the write happens at a correct call; the test `id ∉ F` states that and nothing more. The guard
`r ∈ s.startedRounds` sits on `NetworkStep.byzantineCallG`, `NetworkStep.byzantineCallW` and the
injection `NetworkStep.byzantineGBCA`, and on `ABANetworkStep.byzantineCallG` and
`ABANetworkStep.byzantineCallW`. No transition of a correct process reads the set.

The guard loses nothing a correct process can read. A correct process reads round-`r` messages only
in a round it has called, since every send and every return of a round asks for the round's input
(D8). Deliveries are ordered by the adversary, so an injection at a round no correct process has
started can stand at the round's start without changing what any correct process reads. A coin
resolves only above `f` callers, so a corrupted process's coin calls at such a round resolve
nothing.

**What fails.** Let the network admit a corrupted process's call and injection at every round. At a
state with a nonempty corrupted set, `NetworkStep.byzantineGBCA` is enabled at every round `r`, and
after `networkEventLabels` is hidden so are `byzantineCallG` and `byzantineCallW`: the
implementation has a distinct silent successor for every round. The statement that
`ABDY.protocol` and `AFW.protocol` are finitely branching, finitely many transitions on each label
at every state with the silent label among them, is false.

Let the guard read `r ≤ m`, for the largest started round `m`. An injection is then enabled
at a round below `m` that no process outside `F` has called, and the composed family takes silent
transitions only at the rounds in its map (§5). The relation alone does not exclude an injection
at a round below `m` that is not in the family's map, so the simulation needs the invariant that
the started rounds are `0` to `m`.

**The constraint.** `NetworkState.startedRounds` and `ABANetworkState.startedRounds`, written by
`recordStartedRound` on `callG`; the guard `r ∈ s.startedRounds` on the five transitions above.
`ABDY.ProtocolRelation` and `AFW.ProtocolRelation` carry the set in the ABA network's component
beside the DECIDED sets and the corrupted set, and they state that the rounds in the map of the
composed system's family are exactly the started rounds. The round networks inside a composed
system hold no such set, and their injections carry `k ∈ F` alone. Since §5 restricts the
family's silent transitions to the rounds in its map, an injection or a Byzantine call of the
implementation at a started round is matched by that round's own transitions.

The registry entry is D37 of `blueprint/src/deviations.tex`, the registry of record.

## 4. Announcements

Every value a network computes is announced by an event of its own, and so is the value each
specification holds in its place. A return label carries the returned value and nothing else.

```
Label.retG r id out            -- the graded return: round, process, graded outcome
Label.boundG r b               -- the round's bound bit, announced
Gather.Label.ret id g          -- the gather return: process, returned map
Gather.Label.core C            -- the instance's common core, announced
GBCA.ByAFW.RoundEvent.firstGatherCore C   -- the first gather's core, inside a gather-based round
```

`Label.gbcaRound (boundG r b) = some r`, so `boundG` lies in `Label.hiddenAPI` beside `callG` and
`retG`, and `roundOwnsLabel` assigns it to round `r`. Every announcement is a self-loop of the
component that holds the value: it writes nothing, it is enabled at every state where the value is
held, and it may repeat. A self-loop leaves every component's state where it stands, which is what
the removal of the ghost needs below.

The conditions are these.

- **Transition System 2.** `GBCA.Step.announceBound s b (h : (!b) ∈ s.excluded)`. The returns carry
  no bit: `retGrade2` and `retGrade1` carry the guard pair `v ∉ excluded ∧ (!v) ∈ excluded`, and
  `retGrade0` asks for an excluded bit, `s.excluded ≠ ∅`, beside its two support counts. Every
  return therefore requires an excluded bit, and `excluded` is written once, so the announcement is
  enabled at every state from the round's first return on.
- **Transition System 4.** `Gather.Step.announceCore s C (h : s.core = some C)`. The return
  `Gather.Step.ret s id g` asks for `s.core = some C` and `C.subMap g` for some `C`, which the label
  does not carry.
- **The implementation's network.**
  `NetworkStep.announceBound s r b (h : ghostBound (s.ghost r) = some b)`, with
  `ghostBound : G → Option Bool` the implementation's parameter. ABDY22's implementation takes
  `G = Option Bool` and `ghostBound = id`; its `abdyGhostStep` writes
  `some (g.getD (GBCA.ByABDY.boundOf (s.sent r) s.F out))` on `retG r id out`. The gather-based
  implementation holds the triple `AFW.Ghost`: `AFW.ghostStep` records the first gather's core at
  the round's first `firstGatherReturn`, the second gather's core at the first `secondGatherReturn`,
  and the bit `GBCA.boundOfCore P` of the recorded first core at the first `retG`; `ghostBound`
  reads the bit. A replaced program takes no transition on `retG`, so the first return is a return
  by a process outside `F`.
- **ABDY22's round network.** `GBCANetworkStep.retG` writes the field `bound` at the round's first
  return, from `GBCA.ByABDY.boundOf w.sent w.F out`; `GBCANetworkStep.announceBound (h : w.bound =
  some b)`.
- **The gather-based round's network.** Its state is the first gather's core it has recorded and
  whether the round has returned. `firstGatherCore C` records `C` where none is recorded, `retG`
  records the return, and `announceBound` fires with the bit `GBCA.boundOfCore P C` once both are
  recorded. Inside the round the first gather's announcement and the round's first return occur in
  either order, so the announcement waits for both.
- **The gather network.** `Gather.NetworkStep.ret` writes the field `core` at the instance's first
  return, from `coreOfNetwork P w.network`; `Gather.NetworkStep.announceCore (h : w.core = some C)`.

Each network writes at the first return of its instance, whichever process returns. In an
implementation that process is outside `F`, since a replaced program takes no transition on the
return. In a composed system the round's return at a corrupted process is the round's own
transition, with the guards of a correct return (§7), and the specification's exclusion stands from
its first return at any process. A write at a later return would compute the bit from a larger
message record than the one the exclusion was matched at.

The implementation's network announces at every state at which the ghost of the round holds a bit,
any number of times, and the ghost holds a bit exactly from the round's first return on. The
specification announces at every state at which a bit is excluded, and every return of the
specification requires an excluded bit. Each refinement matches the instance's first return by the
exclusion, fired on demand, and then the return, and it relates the network's bit to the bit not
excluded. From that step on both announcements are enabled with the same bit, so each announcement
of the implementation is matched by the specification's announcement.

**What fails.** Let a return carry the bit, as Transition System 2's `return(id, x, bind)` does. The
program outputs the return and computes the grade, and the network fixes the bit: `NetworkStep.retG`
refuses every bit but the ghost's, while the program takes the return at any bit.
`network_inputEnabled` is false. The gather network's `ret`, which
fixes the core on the gather program's return, fails the same way. Let a return carry no value and
no event announce it. `BindingTrace` then has no bit to name, and binding, a property of the
extensions of an execution, is not a property of a single trace (D29).

**The constraint.** `Label.boundG` and `Gather.Label.core`; `GBCA.Step.announceBound`,
`Gather.Step.announceCore`, `NetworkStep.announceBound`, `GBCANetworkStep.announceBound`,
`GBCA.ByAFW.NetworkStep.announceBound` and `Gather.NetworkStep.announceCore`; the idle transitions
`boundGIdle` and `coreIdle` at every program and round loop; and the first-return writes above.

### Binding and the common core on the announcements

`GBCA.BindingTrace` (`GBCA/SpecificationSafety.lean`) reads the announcements and the returns of
round `r` in three conjuncts:

```
BindingTrace P r t :=
  (∀ β₁ β₂, boundG r β₁ ∈ t → boundG r β₂ ∈ t → β₁ = β₂) ∧
  (∀ id o v β, retG r id o ∈ t → outValue o = some v → boundG r β ∈ t → v = β) ∧
  (∀ id₁ id₂ o₁ o₂ v₁ v₂, retG r id₁ o₁ ∈ t → retG r id₂ o₂ ∈ t →
      outValue o₁ = some v₁ → outValue o₂ = some v₂ → v₁ = v₂)
```

Two announcements agree; a return of a value and an announcement name the same bit; two returns of
values agree, which the guard pair gives alone. ABDY22's Graded Binding asks for a bit that no
correct process decides against in any extension. On the trace set the announcement supplies it: it
is enabled at every state from the first return on, so every trace with a return extends by it, and
the second conjunct binds every return of a value in every extension. `GBCA.specInst_binding`,
`GBCA.ByABDY.composition_binding` (`GBCA/ABDY/Binding.lean`),
`GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding`,
`GBCA.roundOverBracha_binding` (`GBCA/AFW/Binding.lean`) and the statement over the round alphabet
in `GBCA/BindingOverRoundAlphabet.lean` are stated on this predicate.

`Gather.CoreTrace` (`Gather/SpecificationSafety.lean`) has the three analogous conjuncts:

```
CoreTrace P t :=
  (∀ C, core C ∈ t → n - f ≤ C.card) ∧
  (∀ C₁ C₂, core C₁ ∈ t → core C₂ ∈ t → C₁ = C₂) ∧
  (∀ id g C, ret id g ∈ t → core C ∈ t → C.subMap g)
```

`Gather.specInst_core`, `Gather.instanceOverBroadcastSpecification_core` and
`Gather.instanceOverBracha_core` (`Gather/CommonCore.lean`) are stated on it.

### The ghost-free system

`Implementation.systemGhostFree` is the implementation at the ghost `Unit`, with the write
`fun _ _ _ => ()` and `ghostBound := fun _ => none`: its network never announces. The removal
`system_auxiliaryVariableRemoval` runs along `forgetGhostState` at the identity on labels, since no
return carries a value of the ghost. `NetworkState.forgetGhost` keeps the message record, the
DECIDED sets, the corrupted set and `startedRounds`, which a guard reads.

The implementation's announcements have no counterpart in the ghost-free system.
`AuxiliaryVariableRemoval` (`Framework/AuxiliaryVariableRemoval.lean`) carries a set `K` of labels
and the clause `projectUnchanged`: a step of `sysA` on a label of `K` leaves the projection where it
stands, `μ.map π = PMF.pure (π s)`. The clause `project` is asked of the labels outside `K`. The
congruences carry the clause through `parallel` against a neighbour that idles on `K`, which the
programs do by `boundGIdle` and the coin by the family's idle. `abstract` of a set containing `K`
turns those steps into silent steps that leave the projection where it stands, and the inclusion
`AuxiliaryVariableRemoval.achievableTraceDists_subset` matches each of them by a stutter of `sys0`.
`boundG` lies in `Label.hiddenAPI`, so `ABDY.protocol_ghostRemoval` and `AFW.protocol_ghostRemoval`
state that the protocol and the ghost-free protocol achieve the same trace distributions, and
`ghostFreeProtocol_safe` states Validity and Agreement of the ghost-free protocol.
`network_ghostRemoval` rebuilds every constructor of `NetworkStep` by name, `announceBound` falling
under `projectUnchanged`.

The registry entries are D29 and D30 of `blueprint/src/deviations.tex`, the registry of record.

## 5. Finite maps

Every ℕ-indexed state is a finite map with a default. A family of instances is

```
structure InstanceFamilyState (initial : σ) (act : L → σ → σ) where
  broadcasts  : List L                     -- the broadcast labels applied, the latest first
  instanceMap : Finmap (fun _ : ℕ => σ)
untouchedInstance g  :=  g.broadcasts.foldr act initial                      -- the oldest first
instanceState g r    :=  (g.instanceMap.lookup r).getD g.untouchedInstance   -- a CoeFun: g r
```

with `InstanceFamilyState.initial`, which records no broadcast and has an empty map, so every
round reads `initial`; `setInstanceState g r x`, which inserts `x` at `r`; and `applyBroadcast g
l`, which records `l` and applies `act l` to every entry of the map. The untouched instance is
computed from the recorded broadcasts, so `(g.applyBroadcast l) r = act l (g r)` at every round,
in the map or not (`InstanceFamilyState.applyBroadcast_apply`). An untouched instance is therefore
the instance `initial` under a list of broadcasts. Mathlib's `Finmap` has no map on values, so
`applyBroadcast` is a Framework definition. `System.family inst owns glob act initial` is over
`InstanceFamilyState initial act`:

- on `τ`, at a round `r` of the map, `(inst r).step (g r) τ μr` with `μ = μr.map (g.setInstanceState r)`;
- on a label with `owns l = some r`, the same at round `r`, in the map or not;
- on a broadcast label, `PMF.pure (g.applyBroadcast l)`;
- on every other label, the idle `PMF.pure g`.

The family starts from `InstanceFamilyState.initial`, which reads `(inst r).init` at every round
when every instance starts from `initial` (`System.family_init_apply`).

The network's sent sets and ghosts are finite maps behind the accessors `s.sent r j` and
`s.ghost r`, which default to `∅` and to `default`. A round never touched reads as the initial
instance, as D22 has it for a process's round variables (`Implementation.RoundVariablesMap`).

Two states with equal accessors need not have equal maps: an owned step that leaves an untouched
instance where it stands inserts an entry equal to the default. Every relation reads a family
through the accessor, and through the set of its rounds where a silent step needs it.
`AFW.ProtocolRelation` states `∀ r, t.1 r = roundProjection P s.1 s.2.1 r`, an equation at every
round, and both protocol relations state that a round lies in the composed family's map exactly
when a process outside `F` has called it. The hybrid's `F_gbca` and `F_wcc`
(`HybridRefinesSpecification/Relation.lean`), `call_round` and `wcc_callRound` read `g r` and `w r`
through the accessor.

`ForwardSimulation.family` relates two families that record the same broadcasts, have the same
rounds in their maps and have related instances at every round. Besides the per-round simulations
and the preservation of the relation by the broadcast actions, it asks one hypothesis,
`hUntouchedFirstStep`: from a related pair of untouched instances, a step on a label `owns` assigns
to the round is matched by an abstract transition on that label followed by a silent run. The family
takes no silent transition at an untouched round, so a weak run that matches such a step cannot
begin with a silent transition. `ForwardSimulation.family_of_noSilentAtUntouched` discharges the
hypothesis when no owned label is silent and the abstract instance has no silent transition at an
untouched state. In the ABA development the first transition of a round is a call, and a call is
matched by a call.

**What fails.** Let a broadcast apply its action to the entries of the map alone. After a `fail`, a
round first touched afterwards starts from an untouched instance whose corrupted set misses the
corrupted process, so `F_gbca : ∀ r, (g r).F = c.F` and `F_wcc` are false at that round, and the
corrupted process's support stops counting in that round's guards. Let the family take a silent
transition at a round outside its map. After a corruption every untouched round of
`GBCA.ByABDY.gbcaInstanceFamily` enables the injection `GBCANetworkStep.byzantineGBCA`, one for each
round, and the composed system is not finitely branching at that state.

**The constraint.** `InstanceFamilyState.applyBroadcast` records the broadcast, from which
`untouchedInstance` is computed, and applies the action to every entry of the map; the family's
silent disjunct ranges over the rounds of `instanceMap`. At a reachable state an untouched instance
is the initial instance with the corrupted set applied. It enables no output, since it has excluded
no bit, resolved no coin and received no message, and its only silent transitions are the
injections the restriction excludes.

## 6. The loops on the call labels

A call label carries the call and the input-enabledness loop, as at the ABA interface (D36): the
component the call names records it at a state holding no input and loops at a state holding one.
No alphabet carries a loop label, so no component needs an idle transition for one.

- `ABDY.RoundStep.callG_call` and `AFW.RoundStep.callG` record the input at an uncalled round, and
  `callGLoop` moves the round loop alone at a called one, both on `callG r j b`.
- `RoundLoopStep.callG` is the round loop's one transition on its call: whether the round records
  the call or loops is the round instance's business.
- `GBCAProgramStep.callLoop` and `byzantineCallLoop` sit on `callG r j b` and
  `byzantineCallG r j b` at `input ≠ none`; `GBCA.ByAFW.ProgramStep.callLoop` on `callG r j b`;
  `BRB.ProgramStep.callLoop` on `call m` at the leader; `Gather.ProgramStep.callLoop` on
  `call j x`. A reliable-broadcast instance and a gather instance are over their specifications'
  alphabets, `BRB.Label n M` and `Gather.Label n X`, so each specification is a component of the
  level above with no label map.
- `GBCA.specificationLabelMap`, `GBCA.ByAFW.programLabelMap`, `GBCA.ByAFW.firstGatherLabelMap` and
  `GBCA.ByABDY.roundOwnsLabel` have no loop arm; `roundOwnsLabel` assigns `callG r`, `retG r`,
  `boundG r` and `byzantineCallG r` to round `r`.
- The loop case of `GBCA.ByABDY.Algorithm`, `BRB.BrachaAlgorithm`, `Gather.AlgorithmOverBracha`,
  `Gather.AlgorithmOverBroadcastSpecification` and `GBCA.ByAFW.AlgorithmOverGatherSpecifications`
  sits on the call label.

`DESIGN-Decomposition.md` §1 states the constraint in these words:

> ## 1. A call sends nothing
>
> A specification takes its call label on two transitions, the call and the input-enabledness
> loop (`BRB.Step.call`, `BRB.Step.callLoop`; `Gather.Step.call`, `Gather.Step.callLoop`). A
> composition takes it on the program the call names: `BRB.ProgramStep.call` records the payload
> at a leader holding no input, `BRB.ProgramStep.callLoop` leaves a leader holding one where it
> stands, and the same pair stands at `Gather.ProgramStep`, `GBCA.ByABDY.GBCAProgramStep` and
> `GBCA.ByAFW.ProgramStep`. Every other component takes the call label on a Dirac self-loop. A
> program's first message is a send of its own, guarded by the recorded input: the leader's
> `⟨INIT, m⟩` is `BRB.ProgramStep.sendInit`.
>
> **What fails.** Let the call also post a message at the network. On the call label the leader
> records or loops and the network posts in both cases, and the loop with the post is a behaviour
> of no algorithm: it reaches a state whose network holds `⟨INIT, m'⟩` while the leader holds the
> payload `m` of an earlier call, which only `BRB.BrachaAlgorithm.byzantine` produces and only
> under `ldr ∈ F`. The characterisation by the algorithm, `brachaInstance.step s l μ ↔
> BrachaAlgorithm s l μ`, is false at the call label, and the refinement into the specification
> fails with it, since a second call with another payload would let the specification commit a
> value the instance never broadcast.
>
> **The constraint.** The network transitions on a call label are Dirac self-loops
> (`BRB.NetworkStep.call`, `Gather.NetworkStep.call`, `GBCA.ByABDY.GBCANetworkStep.callG`,
> `GBCA.ByAFW.NetworkStep.callG`), and the loop is a case of the algorithm on the call label
> (`BRB.BrachaAlgorithm.callLoop` and its companions), so the characterisation holds label by
> label: `BRB.brachaInstance_step_iff_algorithm`,
> `Gather.instanceOverBroadcastSpecification_step_iff_algorithm`,
> `Gather.instanceOverBracha_step_iff_algorithm`,
> `GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm`. The guard of the loop on a filled
> input is a convention: the specification's unguarded loop matches a program that drops a first
> call, so no statement turns on it, and the guard makes the program's transition on its call
> a function of its state, as at the ABA interface (D36).

## 7. A corrupted process's actions

A replaced program takes no transition on the labels of `actsAt j` and takes `corruptedIdle` on
every other non-silent label:

```
actsAt j  :=  callG _ j _,  retG _ j _,  gbcaSend _ j _,  gbcaRoundEvent _ j _,  callW _ j,  decidedSend j _
roundLoopActsAt j  :=  callG _ j _,  callW _ j,  decidedSend j _          -- the round loop's
```

Every label of `actsAt j` is an output of the program of `j`, so a replaced program takes every input:
the deliveries addressed to it, the coin's return, the Byzantine calls, `boundG`, `fail`. Its
two other outputs, `decidedRelay j _` and `retABA j _`, it takes on `corruptedIdle` at either bit.
The round loop of `ABA/Composition/Components.lean` takes the round's return as an input, so
`RoundLoopStep.corruptedIdle` reads `Composition.roundLoopActsAt j`, which leaves `retG _ j _` out.

The network outputs a corrupted process's sub-protocol calls on labels of its own,
`byzantineCallG r k b` and `byzantineCallW r k`, under `k ∈ F` and `r ∈ startedRounds`. The round
family takes `byzantineCallG` on the instance's call or loop, through `roundOwnsLabel` and
`GBCA.specificationLabelMap`, and the coin takes `byzantineCallW` on its call or loop, through
`coinLabelMap`. The injections are silent transitions of the network, `byzantineGBCA` under the same
two guards and `byzantineDecided` under `k ∈ F`. A return to a corrupted process is the output of
the instance that computes it, on its own return label. In an implementation the replaced program
takes no transition on `retG`, so a round never returns at it; in a composed system the replaced
round loop takes the round's `retG r k out` on `corruptedIdle`, and both take the coin's `retW`
there. The replaced program outputs `retABA k b`, and Transition System 1's `retByzantine` matches
it.

**What fails.** Let a replaced program output its process's calls on the plain labels.
`corruptedIdle` reads nothing, so it outputs `callG r k b` and `callW r k` at every round, and the
guard on the started rounds of §3 would sit on an input of the network, which makes
`network_inputEnabled` false. Let the network output a corrupted process's return on a label of its
own, `byzantineRetG r k out`, which the round instance reads as its return. The instance's return
transitions carry the return's guards (`GBCA.Step.retGrade1`, the quorum guards of
`GBCAProgramStep.retGrade1`), so at a state where those guards fail the instance refuses a label the
network outputs, and `GBCA.specificationOverRoundAlphabet_inputEnabled` is false. Let the instance
take the label on a loop at those states, and `BindingTrace` of the specification over the round
alphabet is false, since the loop carries a return of either value. The coin fails the same way at
`byzantineRetW`, `WCC.Step.ret` asking for the resolved value.

**The constraint.** `actsAt`, `Composition.roundLoopActsAt`, `ProgramStep.corruptedIdle` and
`RoundLoopStep.corruptedIdle`; `NetworkStep.byzantineCallG` and `byzantineCallW` and their
companions at `ABANetworkStep`, each under `k ∈ F` and the guard on the started rounds; the returns
of the instances on their own labels, with no Byzantine return label in `NetworkEvent`;
`coinLabelMap` and `GBCA.specificationLabelMap` with one Byzantine arm each.

The registry entries are D11 and D23 of `blueprint/src/deviations.tex`, the registry of record.

## Appendix: vocabulary

Each name of the discipline, the word it takes, and the count of that word in the four sources, in
the order LeslieBP / ABDY22 / AFW25 / the simulations paper, from `pdftotext -layout` and
`grep -i -o`.

| name | word and sense in the sources | counts | rejected |
|---|---|---|---|
| `startedRounds`, `recordStartedRound` | "starts round", "started": ABDY22, a party starting a round; "record" is the tree's (`recordDecided`) | started 0/16/0/0, starts round 0/7/0/0 | `largestStartedRound`, the maximum, which needs an invariant to relate to the rounds the composed family has touched; `roundBound` (the bound bit's word); "opens" (in no source) |
| `Label.boundG`, `announceBound`, `boundGIdle` | "bound value": LeslieBP, the value binding fixes; the tree's "bound bit"; "announce" is the tree's word for an event that announces a value | bound value 3/0/0/4, announce 0/2/0/0 (ABDY22's two are "Brief announcement" in titles) | `bindG` (LeslieBP's `bind` is the state field) |
| `ghostBound` | "ghost" is the tree's word (D13, D29, D30) | ghost 0/0/0/0 | `ghostOutput` (a relation on a label's bit, which no label carries) |
| `Gather.Label.core`, `announceCore`, `coreIdle`, `RoundEvent.firstGatherCore` | "common core": AFW25's word for the set every correct output contains | core 24/1/44/0, common core 3/0/38/0 | `bind` (Transition System 4's field, which the tree calls `core`) |
| `System.InputEnabled`, `InputEnabledness.lean`, `_inputEnabled` | "input-enabledness": LeslieBP §1.3, the simulations paper's Assumption 1 | input-enabledness 16/0/0/5, enabled 20/0/0/7 | |
| `InputOutputLabels`, `inputLabels`, `outputLabels` | "input labels In and output labels Out" | input label 2/0/0/2, output label 1/0/0/3 | `IOSig` (an abbreviation) |
| `InputOutputLabels.Compatible`, `_compatible` | "compatible if Out₁ ∩ Out₂ = ∅": the simulations paper, Definition 2; LeslieBP's three uses are of adversaries "compatible on S", another sense | compatible 3/0/1/7 | `Disjoint` alone (says nothing of outputs) |
| `InstanceFamilyState`, `instanceMap`, `instanceState`, `setInstanceState` | "instance": every source, one copy of a sub-protocol; the state is parametrised by the initial instance `initial` and the broadcast action `act` | instance 11/25/8/7 | `RoundMap` (a family is not always of rounds) |
| `untouchedInstance` | "untouched" is the tree's word for a round never touched (D22); the instance at such a round, `initial` under the recorded broadcasts | untouched 0/0/0/0 | `default` (says nothing of the role) |
| `applyBroadcast`, `broadcasts` | "broadcast" in the tree's family sense, D1's "broadcast on fail": `applyBroadcast` records a broadcast label in `broadcasts` and applies its action to every entry of the map; in the sources the word names reliable broadcast, another sense | broadcast 4/66/75/2 | `mapValues` (Mathlib's sense, which `Finmap` lacks) |
| `retGLoop`, `retWLoop`, `deliverLoop`, `decidedDeliverLoop`, `firstGatherReturnLoop`, `secondGatherReturnLoop`, `callLoop` on a call label | "loop for input-enabledness": LeslieBP's specifications | loop 25/0/2/7, call loop 7/0/0/0, self-loop 1/0/0/5 | `…Idle` (an idle transition is at another process) |
| `callGLoop` | the caller's call at a round already called, the loop case of `callG` beside `callG_call`; the same word | as above | `gbcaCallLoop` (a label of its own) |
| `boundGIdle`, `coreIdle`, `firstGatherCoreIdle`, `RoundLoopStep.gbcaSendIdle`, `RoundLoopStep.gbcaDeliverIdle` | the tree's `…Idle`, a self-loop at a label that is not the component's business | idle 0/0/0/0 | |
| `RoundLoopVariables.decidedSent` | "having sent it": LeslieBP's Algorithm 1; the network's `decidedSent` (D12′) | having sent 1/3/0/0 | `sentDecided` (a second name for one record) |
| `Composition.roundLoopActsAt` | `actsAt` is the tree's word (D23) | acts 0/0/1/0 | widening `actsAt` (it holds the program's return) |
| `AuxiliaryVariableRemoval.projectUnchanged` | "projection" is the tree's and the simulations paper's; "unchanged" is the tree's | projection 4/0/0/2 | `silentStep` (the label is visible until hidden) |
