# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary agreement,
following the "Verifying ABA with Leslie" blueprint. The headlines of both chains are in
`Results.lean` — `ABDY.main`, `ABDY.refines`, `ABDY.chainSimulation`, `ABDY.protocol_safe`,
`ABDY.protocol_traces`, `ABDY.composed_safe` for the ABDY chain, and `AFW.main`,
`AFW.refines`, `AFW.chainSimulation`, `AFW.composed_refines`, `AFW.composed_safe`,
`AFW.chainSimulationOfComposed` for the gather-based one — beside the shared `hybrid_spec` in
`HybridRefinesSpecification/Simulation.lean` and `GBCA.roundOverBracha_specificationTraces` in
`GBCA/AFW/Binding.lean`, all axiom-clean and guarded.
Each chain carries two headlines about its ghost-free system, in
`GhostRemoval/ImplementationByABDY.lean` and `GhostRemoval/ImplementationByAFW.lean`:
`protocol_ghostRemoval`, the equality of achievable trace distributions between the protocol and that
ghost-free system, and `ghostFreeProtocol_safe`, Validity and Agreement at it. The two sub-protocol
interfaces carry headlines of their own: `GBCA.specInst_binding` in `GBCA/SpecificationSafety.lean`,
with its two implementations `GBCA.ByABDY.composition_binding` in `GBCA/ABDY/Binding.lean` and
`GBCA.roundOverBracha_binding` in `GBCA/AFW/Binding.lean`, and with the two compositions over
specifications `GBCA.roundOverBroadcastSpecification_binding` and
`GBCA.roundOverGatherSpecifications_binding` in the same file; and `Gather.specInst_core` in
`Gather/SpecificationSafety.lean`, with its implementation `Gather.instanceOverBracha_core` and the
composition over the broadcast specification `Gather.instanceOverBroadcastSpecification_core`, both
in `Gather/CommonCore.lean`.

The architecture in two lines, all of it in the protocol's own coordinates:

```
ABDY.protocol  ⊑  ABDY.composed                                                                                      ⊑  hybrid  ⊑  ABA.spec
 AFW.protocol  ⊑   AFW.composed  ⊑  AFW.composedOverBroadcastSpecification  ⊑  AFW.composedOverGatherSpecifications  ⊑  hybrid  ⊑  ABA.spec
```

One GBCA specification, two verified implementations, each carried from the protocol as it runs. The
first line carries the direct implementation (ABDY22's Algorithm 6, D18), the second the
gather-based one (AFW25's two-gather construction, D24), and the two chains share every inclusion
from `hybrid` up. Every system above a protocol is a composition of components, the lowest of them the programs
that run it. On the first line a round is the `n` graded-agreement programs beside the round's
network. On the second a round is `n` programs beside the round's network, in parallel with two
gather instances, and a gather instance is `n` programs beside the gather network, in parallel with
`n` reliable-broadcast instances, each of them `n` programs beside the instance's network. The
three inner inclusions of the second line each replace the components of one level by the
specification above them.

A system below that meeting point belongs to one implementation or the other and is
named for its source: `ABDY`, after Abraham, Ben-David and Yandamuri, and `AFW`, after
Attiya, Flam and Welch. Across the two namespaces a name means the same thing —
`AFW.composed` is to the gather-based implementation what `ABDY.composed` is to
ABDY22's — and `hybrid` and `ABA.spec`, which the chains share, are named in neither.
The rest of the gather-based chain sits in `AFW` as well: its headlines are `AFW.main`
and `AFW.refines`, where ABDY22's are `ABDY.main` and `ABDY.refines`. A `G` elsewhere in the
development is graded agreement — `callG`, `retG`, `GBCANetwork`, `GBCAOutput` — and never the
chain.

Both implementations are one construction. What the protocol fixes — the round loop, the DECIDED
sets, the coin's call and return, corruption, the network and the composition pipeline — is settled
by the round interface and the specification, so `Implementation/System.lean` writes it once,
parametric in the round message type, the per-process per-round variables, the round's transitions,
and a per-round ghost of the network, updated on every transition and read by the network's
announcement of the round's bound bit alone (D29, D30). `ABDY/System.lean` supplies ABDY22's;
`AFW/System.lean` supplies the gather-based one.

- `ABDY.protocol` — ABDY22's protocol as it runs: `n` programs beside the network, which
  holds the message sets, the corrupted set and the rounds a correct process has started (D37),
  and the common coin, the only component whose
  transitions are not Dirac. A program reads its own replacement flag and nothing else about
  corruption: not the corrupted set, not the budget, not another process's status. A corruption
  replaces the program of the process it names (D23). A program holds its round loop beside its
  round variables — its variables in every round it has touched, in a finite map — and
  terminates once its own return has fired and `2f + 1` DECIDED messages have been received (D22).
- `ABDY.composed` — the same protocol read as a composition of components: the round instances, the
  `n` round loops, the ABA network holding the DECIDED sets, and the common coin. `ABDY.protocolSimulation`
  carries `ABDY.protocol` into it along the Dirac lift of `ABDY.ProtocolRelation`, and
  `ABDY.protocol_composed` is the inclusion it yields. The relation determines every composed coordinate
  from the protocol state but the family's list of broadcasts: the entry of process `j` in the
  instance of round `r` is the round-`r` variables that `j` holds (D22), and the rounds of the
  family's map are the started rounds (D37). What makes the inclusion one-directional is on the
  composed system. A round instance records a corrupted process's graded-agreement call, which
  every program of the protocol takes on an idle transition (D11), and the instance's round
  transitions carry no termination guard, so the instance takes a send or a delivery at a process
  the protocol has terminated. This is where the
  chain passes from implementation to specification.
- `hybrid` — each round's instance replaced by the graded agreement specification
  (`ABDY.substitutionSimulation`), the other three components untouched. This is what the core
  simulation runs on.
- `ABA.spec` — the single-automaton system of agreement, reached by `hybridRefinesSpecification`.

Components talk only through synchronised labels, and no component reads another's state.
Why the cuts sit there, and what they give, is `../DESIGN-Composition.md`.

## Ghost outputs

Two values that no program computes are announced by events of their own (D29). The announcement
`boundG r b` names the round's bound bit, and the announcement `core C` names a gather instance's
common core. A return label carries the returned value alone: `retG r id out` the graded outcome,
`ret id g` the returned map. Each announced value is state of the specification, written once by an
internal transition, and each announcement is a self-loop, enabled at every state at which the
value is held, that may repeat. The implementations hold the same values as auxiliary state, in
each case at the component whose own state determines it. A gather instance's core is a field of
the gather network, written at the instance's first return from `Gather.coreOfNetwork` of that
network's sent sets and corrupted set alone. ABDY22's round holds the bound bit as a field of the
round's network state, written at the round's first return. The gather-based round's network
carries no messages: it records the first gather's core from that gather's announcement and whether
the round has returned, and once both are recorded it announces the bit `GBCA.boundOfCore` of the
recorded core. In the implementations both values belong to the network, which holds a ghost per
round (D30) and announces the round's bound bit while the ghost of the round holds it. No program's
variables carry either value and no program's transition reads one: the announcement is the one
transition that reads the ghost.

What a program does hold of a sub-protocol's answer is its own variables holding what the instances
have returned to it: the field `Gather.ProcessVariables.inputBroadcastReturned`, written on the
broadcast return events. Four transitions of a gather program read it — `sendEcho`, `sendVote`,
`sendBind` and `ret` — so it is state a guard consults and not ghost state.

For the bound bit that inertness is a theorem. `GhostRemoval/GhostFreeSystem.lean` removes
the network's ghost onto the ghost-free system `Implementation.systemGhostFree`, whose network
announces nothing, and `ABDY.protocol_ghostRemoval` and `AFW.protocol_ghostRemoval` are the
resulting equalities of achievable trace distributions. No map on labels appears in either
statement: the removal runs at the identity on labels, an announcement leaving the state with the
ghost removed where it stands, and `Label.boundG` lies in `Label.hiddenAPI`, so the announcement is
silent at protocol level.

What the announcement gives is binding as a property of a single trace, at the instance level. The
round-`r` announcements of a trace of `GBCA.specInst` name one bit, every round-`r` return of a
value returns that bit, and two returns of values return the same bit (`GBCA.BindingTrace`,
`GBCA.specInst_binding`). Every announced core of a trace of `Gather.specInst` has at least `n − f`
entries, two announcements name the same set, and every returned map contains every announced core
(`Gather.CoreTrace`, `Gather.specInst_core`). Both predicates are stated on labels alone, so a
trace-distribution inclusion carries them. `GBCA.ByABDY.composition_binding`,
`GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding` and
`GBCA.roundOverBracha_binding` are binding at the two verified graded-agreement implementations and
at the two compositions between them, along their own refinements, and
`Gather.instanceOverBroadcastSpecification_core` and `Gather.instanceOverBracha_core` are the same
statement at the two gather implementations, along theirs.

## Scope

GBCA is verified to **implementation** level, by both implementations — the
gather-based one down through gather and Bracha's reliable broadcast, each of them a
composition of programs beside the instance's network and encoded at specification and
implementation level of its own; WCC is **assumed** at specification level
(its coin is `wccPMF`). Both trace predicates are read at never-corrupted returners.
`ValidityTrace` is the paper-form predicate (D13): every return of `b` by a never-corrupted
process is preceded by the first `callABA` of a caller that is never corrupted anywhere in
the trace, and that call carries `b`; `AgreementTrace` asks two such returns to carry the
same bit. A process has one input, and its first call is the event that carries it. That is
the quantification of the papers' own contracts, and it is what the model forces: the model
contains the corrupted interface, so a corrupted process may call one bit and record
another, and may return either bit at any time (D23). The `f + 1` `InputSupport` support counts
are the invariant machinery that makes this provable, not the predicate itself. Safety
only — no termination, liveness, unpredictability or fairness. The protocol's `terminate`
transition is a transition of the model, not a result: no theorem says when it fires, or that it ever
does.

## Deviations

Each departure from the source blueprint carries a label D1–D37, cited at the point where
it applies. The registry is `../../blueprint/src/deviations.tex`, the Deviations section of the
blueprint chapter: a table of the labels in use, and under each label the departure, its reason
and what following the source would take, with a closing sentence naming the numbers the range
skips. The full edition carries the same registry in `deviations-full.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its sources beyond that
registry.

## What to expect

Each verified sub-protocol level is one folder: `ReliableBroadcast/Bracha/`, `Gather/`,
`GBCA/ABDY/` and `GBCA/AFW/`. Its files come in import order, and a kind of file carries one
name at every level that has it. The messages and variables come first (`MessagesAndVariables.lean`,
`MessagesAndCommonCore.lean`), preceded at `Gather/` by the specification and its safety
(`Specification.lean`, `SpecificationSafety.lean`). The components follow: the programs and the network, with their
step relations and alphabets (`Components.lean`). The input-output discipline of the components
comes next (`InputEnabledness.lean`): the input and output labels of each component, one
`…_inputEnabled` theorem per component, and the `…_compatible` lemma of the composition; where the
file states the input-enabledness of a composition as well, it follows the file that composition
is in, and the algorithm where that proof reads it (`ReliableBroadcast/Bracha/`, `GBCA/AFW/`). The composition places the programs beside the network and the sub-instances in parallel,
hides the level's own events, and reads the result back over the interface alphabet
(`Composition.lean`). A reliable-broadcast instance and a gather instance are over their
specifications' alphabets. A round is over the alphabet of the round family, and its
specification is read over that alphabet in `GBCA/SpecificationOverRoundAlphabet.lean`.
The cases of a composition step read a step back into the transitions of the components
(`CompositionStepCases.lean`), and at `GBCA/ABDY/` the labels the round family owns follow them
(`RoundFamilyOwnedLabels.lean`). The algorithm states the transitions of the composition as one
relation on its state, characterised by a `…_step_iff_algorithm` theorem (at `GBCA/ABDY/`, by
`composition_projects`), one algorithm per composition where a level has several (`Algorithm.lean`,
`AlgorithmOverBracha.lean`, `AlgorithmOverBroadcastSpecification.lean`,
`AlgorithmOverGatherSpecifications.lean`). Then come the witnesses (`EchoWitness.lean`,
`ExclusionWitness.lean`, `OutputWitness.lean`) and the invariant (`Invariant.lean`), with a
counting file where the argument counts (`Gather/CommonCoreCounting.lean`, and
`GBCA/AFW/Counting.lean`, which the components read and which heads its folder). The
specification relation (`SpecificationRelation.lean`) precedes the refinement, which opens with
the per-transition matching (`RefinesSpecification.lean`). The substitutions by congruence follow
(`BroadcastSubstitution.lean`, `GatherSubstitution.lean`), and the property carried down a trace
closes the folder (`Binding.lean`, `CommonCore.lean`). A protocol level, `ABDY/` or `AFW/`, holds
the protocol as it runs (`System.lean`), its composed systems (`Composition.lean`), the
simulation of the protocol into its composition (`Simulation.lean`, at `AFW/` over
`RoundProjection.lean`, `RoundProjectionStep/` and `SimulationOfEachTransition.lean`) and the
substitution to `hybrid` (`Substitution.lean`). Both protocols instantiate one implementation
shape, written once in `Implementation/`, whose input-output discipline is
`Implementation/InputEnabledness.lean`; the components of the composed systems are in
`Composition/Components.lean`, with theirs in `Composition/InputEnabledness.lean`.

A system is named for what sits beneath it: `instanceOverBracha`,
`instanceOverBroadcastSpecification`, `roundOverGatherSpecifications`,
`composedOverBroadcastSpecification`. A simulation is named by its kind and its level:
`refinesSpecification` along a `SpecificationRelation`, a `…Substitution` for each level replaced by
its specification, and `protocolSimulation` along a `ProtocolRelation`. A lemma is named by the
transition and the role: `programStep_<label>_own` for the program of the process the label names
and `programStep_<label>_notOwn` for any other, `networkStep_<label>`,
`roundProjection_<transition>`, `Invariant.step_<label>`, and the suffixes `…_cases`,
`…_specificationTraces`, `…_binding`, `…_core`, `…_inputEnabled` and `…_compatible`. The headlines
sit in the chain's namespace, `ABDY.main` and `AFW.refines` among them, under the naming of the
chains stated above.

The words are the sources' words: the Leslie blueprint, ABDY22, AFW25, and the simulations paper for
the terms of simulation. A transition is one case of a step relation, and an algorithm is a list of
cases. The tree writes variables, witness, cases, synchronisation, received messages, removal of an
auxiliary variable and projection. A transition is matched by a step of the other system, and a
relation is preserved by a transition. A system is over its alphabet. A process is correct or
corrupted, and the grades are 2, 1 and 0. A component has input labels and output labels. A
component is input-enabled when every input label has
a transition at every state, and two components are compatible when they share no output label. A
loop takes an input where the component's other transitions on that label are not enabled. The
component that holds a value no program computes announces it by an event of its own: the round's
bound bit on `boundG`, a gather instance's common core on `core`. The started rounds are the rounds
at which a process outside `F` has called graded agreement. A family of instances holds the recorded
broadcasts beside a finite map of its touched instances, and an untouched round reads as the initial
instance under the recorded broadcasts. Beside the source names ABDY and AFW, the acronyms are ABA,
GBCA, WCC and BRB, and no word is abbreviated. A deviation from the source blueprint is cited by its
label where it applies.

## The files

Each file's module docstring is the account of record for it. The table gives one clause per
file: what it holds, and the declarations a reader looks for. The folders are given in import
order, and no folder imports one below it:
`Vocabulary/` is written over by everything, `GhostRemoval/` writes over everything.
The sub-folders and files with positions of their own in that order are the ones
`scripts/check-folder-order.py` names: `ReliableBroadcast/Bracha/`, `GBCA/ABDY/`,
`GBCA/AFW/`, `ABDY/`, `AFW/`, `Results.lean`,
`GBCA/SpecificationOverRoundAlphabet.lean` and
`GBCA/BindingOverRoundAlphabet.lean`, which read the extended alphabet of `Composition/` and so
sit above it, and `Composition/Hybrid.lean`, which sits above `GBCA/ABDY/` while
the rest of `Composition/` sits below it. Every other sub-folder holds its parent's position.
Within a folder the files are given in import order.
Each file holds one object or one result together
with the lemmas that exist only to prove it.


**`ABA/Vocabulary/`** — the variables and alphabets every implementation is written over.

| file | lines | what it is |
|---|---|---|
| `Vocabulary/Parameters.lean` | 145 | The parameters `P` — `n`, `f` with `n > 3f`, the reliable broadcast's `ECHO` quorum `receivedEchoQuorum`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Vocabulary/Labels.lean` | 166 | The shared label alphabet `Label n`: the visible API, the hidden sub-protocol calls and returns, the announcement `boundG` of a round's bound bit, `τ`. |
| `Vocabulary/ProcessAndNetworkState.lean` | 442 | The two-part vocabulary of the gather-based development: network state (D5) beside `n` process local states, with the multicast/delivery/corrupt operations and the quorum-intersection lemmas, stated once and shared by the three sub-protocol encodings. |
| `Vocabulary/RoundLoop.lean` | 323 | **The ABA round loop**, per process and nothing else: the phase machine, the control state, the round-loop variables. |

**`ABA/Specifications/`** — the specification all safety is measured against, and the
coin the protocol calls.

| file | lines | what it is |
|---|---|---|
| `Specifications/ABA.lean` | 273 | **The top-level ABA specification**, the system all safety is measured against. Eight transitions over `SpecState`, whose control mode carries the flip (D21) and two of which are the corrupted interface (D23). The decision is guarded by the `f + 1` support guard `InputSupport` alone (D13). The calls are its inputs, each enabled at every state (`spec_inputEnabled`). |
| `Specifications/ABASafety.lean` | 894 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `Specifications/WCC.lean` | 315 | The weak common coin specification, per round, and the coin value domain `CoinValue`. Five transitions: a call that records its caller, an unguarded loop on the call label that records nothing, the resolution on `τ`, enabled at `val = ⊥` once the callers number more than `f` (D31) and drawing the coin, a return and the corruption. Its calls and corruptions are enabled at every state (`WCC.specInst_inputEnabled`). Held at specification level by design. |

**`ABA/Implementation/`** — the shape of a protocol as it runs, written once and
parametric in the graded-agreement implementation: the process programs, the network
adversary, the adversary's ghost, the composition of the three beside the common
coin, the lemmas that determine a transition from its label, and the input-output discipline of
the three kinds of component.

| file | lines | what it is |
|---|---|---|
| `Implementation/Alphabet.lean` | 222 | The extended alphabet `ExtendedLabel n M E` of the implementation, parametric in the round message type and in the type of the round's own calls and returns, the component that outputs each label, and the label pullback the common coin is read along. |
| `Implementation/System.lean` | 707 | **The implementation of a protocol**, parametric in the graded-agreement implementation: the shared transitions of a program and of the network, the started rounds the network records and the guard they place on a corrupted process's calls and injection (D37), the network's per-round ghost with its update and its read `ghostBound`, which enables the announcement `boundG` alone (D29, D30), the pipeline that composes them beside the common coin, and `IsRoundStep`, what an implementation states about its own transitions. |
| `Implementation/StepCases.lean` | 520 | The transitions of one program and of the network, determined by their labels: the participant's transition as its guards together with the Dirac it produces, the loop that takes an input where the participant's transition is not enabled, the idle transition of a non-participant as the identity, and the determinacy of both step relations; and `programStep_notRound`, a transition on a label outside `roundOwn j` other than `τ` and `fail` leaving the replacement flag and the round variables. |
| `Implementation/NetworkStateWritesAndRemovals.lean` | 283 | The field algebra of the network's five writes: a round multicast, a DECIDED multicast, corruption, the record of a started round and the ghost write, each read field by field through the accessors `sent r` and `ghost r`. With them the removal of the ghost, `NetworkState.forgetGhost` to the state over the trivial ghost `Unit`, which commutes with the four writes other than the ghost write. |
| `Implementation/CompositeTransitions.lean` | 317 | The transitions of the implementation, determined by their labels: the pipeline `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct` unfolded to the transitions of the process group, of the network and of the common coin, and the composite transitions on the announcement of a round's bound bit and on a corrupted process's two sub-protocol calls. |
| `Implementation/InputEnabledness.lean` | 234 | The input-output discipline of the implementation: the input and output labels of a program, of the network and of the common coin, `program_inputEnabled`, `network_inputEnabled` and `coin_inputEnabled`, and `systemExtended_compatible`. |

**`ABA/ReliableBroadcast/`** — the reliable-broadcast specification and Bracha's
implementation of it.

| file | lines | what it is |
|---|---|---|
| `ReliableBroadcast/Specification.lean` | 179 | The reliable-broadcast specification, per leader (blueprint TS 6, safety-only): the input/committed-value split with the guarded commit (D27). The call and corruption are enabled at every state (`specInst_inputEnabled`). |

**`ABA/ReliableBroadcast/Bracha/`** — Bracha's implementation of that specification, from the
messages it sends to its refinement: the components one instance runs on, the composition they
make, the algorithm that composition realises, and the simulation into the specification.

| file | lines | what it is |
|---|---|---|
| `ReliableBroadcast/Bracha/MessagesAndVariables.lean` | 76 | `BRB.Message`, Bracha's three message levels; `BRB.ProcessVariables`, the variables one process keeps in one instance, holding the leader's call, the write-once `INIT`, `ECHO` and `VOTE` send fields and the return flag; and `BRB.BrachaState`, the composed state they make with the instance's network (D1, D5). |
| `ReliableBroadcast/Bracha/Components.lean` | 231 | The pieces one instance runs on: the instance-internal alphabet `BRB.BroadcastLabel`, the specification's alphabet with the multicast and the delivery beside it, the local program `BRB.broadcastProgram` with its transitions, the leader recording its call at no input and looping at one, and the instance's network `BRB.broadcastNetwork` with its own. |
| `ReliableBroadcast/Bracha/Composition.lean` | 103 | **The Bracha instance, composed**: `BRB.brachaInstance`, the `n` per-process programs beside the instance's network with the instance's own events hidden, read back over the specification's alphabet `BRB.Label n M`; `BRB.brachaInstanceExtended` before the hiding, and the determinacy of the programs, the network and the instance. |
| `ReliableBroadcast/Bracha/CompositionStepCases.lean` | 402 | The transitions of `BRB.brachaInstance`, determined by their labels: a step of the instance split into a hidden synchronisation and an interface label, a synchronised step read as the transitions of the programs and the network, one program's transition and the network's per label class, and the write each transition makes on the composed state. |
| `ReliableBroadcast/Bracha/Algorithm.lean` | 292 | `BRB.BrachaAlgorithm`, the transitions of the composed instance `BRB.brachaInstance`: Bracha's three message levels in the form of AFW25's Algorithm 1 (D34) over the two-part state, one constructor per case of the characterisation `brachaInstance_step_iff_algorithm`, which is proved here. A relation on that state; the system is the composition of `ReliableBroadcast/Bracha/Composition.lean`. |
| `ReliableBroadcast/Bracha/InputEnabledness.lean` | 137 | The inputs and the outputs of the `n` programs and the instance's network: `program_inputEnabled`, `network_inputEnabled` and `brachaInstance_compatible`; and `brachaInstance_inputEnabled`, the instance input-enabled on the inputs of the BRB specification, the call and the corruption. |
| `ReliableBroadcast/Bracha/EchoWitness.lean` | 60 | `BRB.EchoWitness`: some process holds a quorum of received `ECHO m` messages, more than `(n + f) / 2` senders. It is blind to the corrupted set and monotone, so every transition of the instance and every corruption preserves it. |
| `ReliableBroadcast/Bracha/Invariant.lean` | 662 | `BRB.Invariant`, what the instance maintains: a correct sender's sent message matches its write-once field, a correct echo carries a correct leader's input, and a correct vote has a received echo quorum as its witness. With it the three consequences the refinement needs — at most one value is ever witnessed, every return guard yields a witness, and under a correct leader a witness identifies the leader's input. |
| `ReliableBroadcast/Bracha/SpecificationRelation.lean` | 74 | `BRB.SpecificationRelation`, which the gather substitution lifts: the calls, the return flags and the corrupted sets agree, the invariant holds, and a committed value carries an echo witness. With it at the two initial states and across a corruption of both systems at once. |
| `ReliableBroadcast/Bracha/RefinesSpecification.lean` | 515 | `brachaRefinesSpecification`: the Bracha instance refines TS 6 (D27) over the specification's alphabet, along `BRB.SpecificationRelation`. `specificationRelation_transition` matches every transition of `BRB.BrachaAlgorithm` by a weak run of the specification, the commit fired on demand at the first return that needs it, and four lemmas beside it hold the relation across one transition. |

**`ABA/Gather/`** — gather over reliable broadcast.

| file | lines | what it is |
|---|---|---|
| `Gather/Specification.lean` | 240 | The gather specification (blueprint TS 4): call/commit split (D26) and the write-once core, announced on `core C` by an event of its own (D29); its calls and corruptions are enabled at every state. |
| `Gather/SpecificationSafety.lean` | 170 | `CoreTrace`, the common core stated on a trace, and `specInst_core`, which holds it at the specification. |
| `Gather/MessagesAndCommonCore.lean` | 172 | What a gather instance is written over — the `ECHO`, `VOTE` and `BIND` messages and one process's variables — and the core `coreOf` of a gather network state, with the incidence lemmas the counting argument sums. |
| `Gather/Components.lean` | 428 | The components of one gather instance: the instance-internal alphabet over the specification's, the four events the instance hides, one process's variables and the gather network state with the instance's core, the pullback `inputBroadcastLabelMap` along which an input instance joins the composition, the step relations of the gather program and the gather network, the network writing the core at the instance's first return and announcing it, and the gather programs beside the gather network. |
| `Gather/InputEnabledness.lean` | 218 | The inputs and the outputs of the gather programs, the gather network and the `n` input broadcasts: `program_inputEnabled`, `network_inputEnabled`, `inputBroadcast_inputEnabled` at Bracha's instance and at the broadcast specification, and `instanceOverBroadcastsExtended_compatible`. |
| `Gather/Composition.lean` | 286 | **The gather instance, composed**: the gather programs and network in parallel with `n` composed broadcast instances carrying the inputs — `Gather.instanceOverBroadcastSpecification` over the broadcast specifications and `Gather.instanceOverBracha` over Bracha's — read back over the gather specification's alphabet, with the three projections of the composed state and the determinacy the LTS instances rest on. |
| `Gather/CompositionStepCases.lean` | 562 | The transitions of `Gather.instanceOverBroadcasts`, determined by their labels: a step of the instance split into a hidden gather event and an interface label, a synchronised step read as the transitions of the three factors, the pullback computed label by label, one gather program's transition and the gather network's per label class, and the write each transition makes on the composed state. |
| `Gather/AlgorithmOverBracha.lean` | 491 | `Gather.AlgorithmOverBracha`, the transitions of `Gather.instanceOverBracha` stated over the composition's state, one constructor per case of `instanceOverBracha_step_iff_algorithm`, with `ECHO`, `VOTE` and `BIND` the three multicasts of the gather network; a transition that reaches a broadcast coordinate carries that Bracha instance's own transition as a hypothesis. A relation on that state; the system is the composition of `Gather/Composition.lean`. |
| `Gather/AlgorithmOverBroadcastSpecification.lean` | 506 | `Gather.AlgorithmOverBroadcastSpecification`, the transitions of `Gather.instanceOverBroadcastSpecification` (blueprint Algorithm 4, the binding form of AFW25's Algorithm 5) stated over the composition's state, one constructor per case of `instanceOverBroadcastSpecification_step_iff_algorithm`, with `ECHO`, `VOTE` and `BIND` the three multicasts of the gather network. A relation on that state; the system is the composition of `Gather/Composition.lean`. |
| `Gather/Invariant.lean` | 1121 | `Gather.Invariant`, what the gather instance over the broadcast specifications maintains: the conformance clauses — the corruption budget, delivery soundness, the returned values a program holds, a committed entry is the payload its instance recorded, a correct sender's sent `ECHO`, `VOTE` and `BIND` matching its write-once fields, the received messages backing them, and the gather variables backing the payload an input instance was called with — beside the approval of every `ECHO` field. |
| `Gather/CommonCoreCounting.lean` | 375 | The counting argument for the core: `coreOfNetwork` has `n − f` committed entries and lies below the `BIND` payload every process outside `F` has multicast (`transfer`), with the `f + 1` witness the specification's `bindCore` guard consumes, and the witness `withoutBindAbove` that holds the returns after the first to the core (`coreOf_recorded`, `exists_correct_bindAbove_of_quorum`). |
| `Gather/SpecificationRelation.lean` | 101 | `Gather.SpecificationRelation`, which the counting refinement runs along: the specification's calls agree with the gather's variables, the return flags, the corrupted sets and the core agree, the invariant holds, a committed entry is bounded by the commitment of its input instance (`val_witness`), and at most `f` processes outside `F` have sent no `BIND` payload containing the recorded core (`withoutBindAbove_card`). |
| `Gather/RefinesSpecification.lean` | 866 | `refinesSpecification`: the gather-over-BRB instance refines TS 4. The return run commits the entries it reads, writes the core at `coreOfNetwork` of the network state, and returns, in one weak transition; a member outside `F` of the returner's `n − f` senders holds a `BIND` payload above the core (`subMap_of_withoutBindAbove_card`); the announcement of the core is matched by the specification's. |
| `Gather/BroadcastSubstitution.lean` | 124 | `broadcastSubstitution`: the broadcast substitution inside gather, per input-broadcast coordinate, carried through the composition by the congruences. |
| `Gather/CommonCore.lean` | 63 | `instanceOverBroadcastSpecification_core` and `instanceOverBracha_core`: the common core stated on a trace holds at the two gather implementations, carried from the specification along their refinements. |

**`ABA/GBCA/`** — the graded-agreement specification, the binding it carries, and the reading of it over the alphabet of a round.

| file | lines | what it is |
|---|---|---|
| `GBCA/Specification.lean` | 353 | The graded binding crusader agreement specification, per round. Binding is negative, the returns carry the returned value alone, and `announceBound` announces the round's bound bit by an event of its own once a bit is excluded (D19, D29). |
| `GBCA/SpecificationSafety.lean` | 881 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. `specInst_binding` states binding on a trace. |
| `GBCA/SpecificationOverRoundAlphabet.lean` | 186 | `GBCA.specificationOverRoundAlphabet`: the graded-agreement specification read along `GBCA.specificationLabelMap`, which identifies a corrupted process's call `byzantineCallG` with the specification's call, with its input-enabledness and the sections along which a weak run of the specification is read back over a round's interface (D11). |
| `GBCA/BindingOverRoundAlphabet.lean` | 224 | `GBCA.specificationOverRoundAlphabet_binding`: binding of the specification read over a round's alphabet. The exclusion set only grows along an execution and no state of one excludes two bits, so two announcements of round `r` name the same bit, a return of a value returns the announced bit, and two returns of values agree (`GBCA.BindingTraceExtended`). |

**`ABA/Composition/`** — the components the composed systems are built from with their
input-output discipline, the ABA state and the protocol-shaped specification.

| file | lines | what it is |
|---|---|---|
| `Composition/Components.lean` | 938 | The extended alphabet `ExtendedLabel n M`, parametric in the type `M` of the messages a graded-agreement round exchanges and over the empty type of round calls and returns, the common coin read along its label pullback, the round loop of one process, and the ABA network, which records the started rounds and outputs a corrupted process's calls (D11, D37) — the pieces the two compositions are built from. |
| `Composition/InputEnabledness.lean` | 231 | The inputs and the outputs of the round loops, the ABA network and the round family: `roundLoop_inputEnabled`, `abaNetwork_inputEnabled`, and `composedComponents_compatible`, which states the outputs of the three and of the common coin pairwise disjoint. |
| `Composition/ABAState.lean` | 550 | The ABA state as one object: the round-loop variables beside the DECIDED network and the started rounds, with the accessors the invariant is stated in, the DECIDED relay `ABAState.relayDecided`, and `corrupt_abaNetwork`, the ABA network after a corruption read from the implementation's network. |
| `Composition/Hybrid.lean` | 608 | **`hybrid P M`**: the protocol-shaped specification over the round message type `M` — the family of round specifications beside the round loops, the ABA network and the common coin, under the pipeline that hides the labels the components synchronise on, reads the result back over `Label n` and hides the sub-protocol API — with the transitions of its four components, the input-enabledness of the family of round specifications, and the three routes a labelled transition takes through the two hidings. |

**`ABA/GBCA/ABDY/`** — ABDY22's implementation of that specification: the round's
graded-agreement instance, the algorithm it runs, the labels its family owns, and the refinement
into the graded-agreement specification with the binding it carries. The files are given in import
order.

| file | lines | what it is |
|---|---|---|
| `GBCA/ABDY/MessagesAndVariables.lean` | 664 | The messages a graded-agreement round exchanges and the state it runs on: the five message levels of Algorithm 6, the round's bound bit `boundOf` (D29), one process's round variables beside the round's network state `NetworkState`, their pair `RoundState` with the projections and writes of each component, the counting the algorithm's guards read, and the two quorum lemmas (D1, D5). |
| `GBCA/ABDY/Components.lean` | 406 | The components of the round's graded-agreement instance: the instance-internal alphabet that carries the multicast and the delivery, the step relation `GBCAProgramStep` of one corruption-blind local program and `GBCANetworkStep` of the round's network, which writes the round's bound bit at the first return and announces it on `boundG` (D29), and the two systems `gbcaProgram` and `GBCANetwork` they carry (D11). |
| `GBCA/ABDY/Composition.lean` | 294 | **The round's graded-agreement instance**: `GBCA.ByABDY.composition`, the programs beside the round's network with their two synchronisations hidden and the result read back over the extended alphabet, the round-indexed family `gbcaInstanceFamily` over `InstanceFamilyState` with the three functions it is built from, the determinacy the LTS instances rest on, and the readers and builders of one instance transition. |
| `GBCA/ABDY/InputEnabledness.lean` | 213 | The inputs and the outputs of the round's programs and network, of the composition and of the round family: `gbcaProgram_inputEnabled`, `gbcaNetwork_inputEnabled`, `composition_inputEnabled`, `gbcaInstanceFamily_inputEnabled` and `compositionExtended_compatible`. |
| `GBCA/ABDY/CompositionStepCases.lean` | 463 | The transitions of the round instance, determined by their labels: one program's transition and the network's transition per label class, the round variables beside the network state read as one composed state, the two cases of a transition of the composition, and the network's transition determined by a round-tagged label. |
| `GBCA/ABDY/RoundFamilyOwnedLabels.lean` | 79 | The labels the round-indexed family owns, evaluated: `GBCA.ByABDY.roundOwnsLabel` and `GBCA.ByABDY.isFailLabel` at every label of the extended alphabet, over every round message type, which is what discharges the premises of the composed system by `simp`. |
| `GBCA/ABDY/Algorithm.lean` | 497 | **The algorithm of the round's graded-agreement composition**, ABDY22's Algorithm 6 in full (D18): `Algorithm`, one transition per line of Algorithm 6 (D8), and the characterisation `composition_projects` — at a label of the round's interface, every transition of the composition is the algorithm's transition at the specification label that interface label projects to, one step for one step. One axiom check. |
| `GBCA/ABDY/Invariant.lean` | 842 | The inductive invariant `Invariant` of the composed state: the corruption budget, delivery soundness, protocol conformance and write-once recording of correct multicasts, participation, budget-robust input origin, and the `f + 1` genuine-holder support `InputSupport` (D15). `Invariant.initial` and `Invariant.step` hold it at the initial state and along every transition of the algorithm. |
| `GBCA/ABDY/ExclusionWitness.lean` | 337 | The exclusion witnesses `ReceivedEchoQuorum` (Case A), `VoteQuorumAgainst` (Case B) and their disjunction `ExclusionWitness`: a monotone witness on the received messages that a bit can never gain grade-≥1 support. The derivation chains derive a witness from a return's own received messages. |
| `GBCA/ABDY/SpecificationRelation.lean` | 414 | The simulation relation `specificationRelation`: the specification's `call`, `ret` and `F` taken from the composed state, `excluded` and `grade` carried as witnesses on the pattern of received messages, and the round's bound bit tied to `excluded`; `specificationRelation_init` at the two initial states and `specificationRelation_corrupt` across a corruption of both systems, which the family lifting consumes. The specification's guards and the two-step exclusion-then-return runs are derived from it. |
| `GBCA/ABDY/RefinesSpecification.lean` | 824 | The matching `specificationRelation_transition` and the refinement `refinesSpecification` of the round's composition by the specification read over the round's interface, by exclude-on-demand, the network's announcement matched by the specification's; its soundness inclusion `composition_specificationTraces`; and the broadcast corruption act at the round's alphabet with `refinesSpecification_failAct` and the first step at an untouched round `refinesSpecification_untouchedFirstStep`, the two further premises the family lift consumes. Three axiom checks. |
| `GBCA/ABDY/Binding.lean` | 53 | **`composition_binding`**: binding of the round's composition on a trace, carried from the specification over the round's alphabet along `composition_specificationTraces`. One axiom check. |

**`ABA/GBCA/AFW/`** — the two-gather round and the three compositions that carry it.

| file | lines | what it is |
|---|---|---|
| `GBCA/AFW/Counting.lean` | 367 | **The counting of the two-gather round** (AFW25 Algorithm 4 at R = 2, its approximate-agreement subroutine replaced by a local count, D24): the candidate and the grade, `candidate` and `gradeOf`, the bound bit `boundOfCore` computed from the first gather's core (D29), and the entry counts the refinement consumes. |
| `GBCA/AFW/Components.lean` | 539 | The components of the graded-agreement round: the round-internal alphabet and a program's alphabet, the program's variables `ProcessVariables`, the three pullbacks along which the programs and the two gather instances join the round, the step relations `ProgramStep` and `NetworkStep` of one graded-agreement program and of the round's network, which records the first gather's core and the round's return and announces the bound bit (D29), and `roundPrograms`, the `n` programs beside that network. |
| `GBCA/AFW/Composition.lean` | 351 | **The graded-agreement round, composed**: the round's programs in parallel with two gather instances — `GBCA.ByAFW.roundOverGatherSpecifications` over the gather specifications, `GBCA.ByAFW.roundOverBroadcastSpecification` over gather-over-BRB, and **`GBCA.ByAFW.roundOverBracha`, the gather-based GBCA implementation**, over gather-over-Bracha — read over the family alphabet `ExtendedLabel n Empty`, with the four projections of the round's state and the determinacy the LTS instances rest on. |
| `GBCA/AFW/CompositionStepCases.lean` | 580 | The transitions of `GBCA.ByAFW.roundOverGathers`, determined by their labels: a step of the round split into a hidden event and a family label, a synchronised step read as the transitions of the round's programs, the round's network and the two gather instances, and one graded-agreement program's transition and the round's network's transition per label class. |
| `GBCA/AFW/AlgorithmOverGatherSpecifications.lean` | 502 | `GBCA.ByAFW.AlgorithmOverGatherSpecifications`, the transitions of `GBCA.ByAFW.roundOverGatherSpecifications` stated over the round's state, one constructor per case of `roundOverGatherSpecifications_step_iff_algorithm`. A relation on that state; the system is the composition of `GBCA/AFW/Composition.lean`. |
| `GBCA/AFW/InputEnabledness.lean` | 376 | The inputs and the outputs of the round's programs, the round's network and the two gathers, and of the round itself: `roundProgram_inputEnabled`, `roundNetwork_inputEnabled`, the input-enabledness of the three compositions, and `roundOverGathersExtended_compatible`. One axiom check. |
| `GBCA/AFW/OutputWitness.lean` | 272 | The counts the counting refinement consumes, and the two witnesses it carries: `OutputWitness`, what a recorded graded outcome witnesses about the two cores, and `ExclusionWitness`, the first gather's core counting a bit below `|S| − f`. Every later transition preserves both, the cores being written once. |
| `GBCA/AFW/Invariant.lean` | 784 | `GBCA.ByAFW.Invariant`, what the round over the gather specifications maintains: the corruption budget, a committed gather entry of a correct process is its call, what a candidate and a recorded grade witness, the transfer of the candidate to the second gather's call, the core the round's network records being the first gather's core (D29), and the core-write guards. |
| `GBCA/AFW/SpecificationRelation.lean` | 137 | `GBCA.ByAFW.SpecificationRelation`, which the counting refinement runs along: the invariant holds, the calls, the return flags and the corrupted sets agree, an excluded bit carries an exclusion witness and is the complement of the round's bound bit, which is excluded from the round's first return on, and each grade guard is witnessed on the second gather's core. Broadcast compatibility and one axiom check. |
| `GBCA/AFW/RefinesSpecification.lean` | 687 | `refinesSpecification`: the two-gather round refines the GBCA specification. Every case of the algorithm is matched by a weak run of the specification, at most two steps long, the run is lifted to the round's interface, and `refinesSpecification_untouchedFirstStep` is the first step at an untouched round. Two axiom checks. |
| `GBCA/AFW/BroadcastSubstitution.lean` | 264 | `broadcastSubstitution`: Bracha's broadcast replaced by the broadcast specification at each of the two gather coordinates, carried through the round by the congruences, with its trace-distribution inclusion, its broadcast compatibility and the first step at an untouched round. Three axiom checks. |
| `GBCA/AFW/GatherSubstitution.lean` | 245 | `gatherSubstitution`: each gather instance replaced by the gather specification, carried through the round the same way, with its trace-distribution inclusion, its broadcast compatibility and the first step at an untouched round. Three axiom checks. |
| `GBCA/AFW/Binding.lean` | 161 | The three compositions of the round reach the specification over the round's alphabet: the inclusions `roundOverGatherSpecifications_refines`, `roundOverBroadcastSpecification_specificationTraces` and `roundOverBracha_specificationTraces`, the round composite `roundOverBracha_refinesSpecification`, and the binding each of them carries — `GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding`. Six axiom checks. |

**`ABA/HybridRefinesSpecification/`** — the core simulation of the blueprint's §3,
`hybrid ⊑ ABA.spec`, and its witnesses.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/InvariantPreservation.lean` | 33 | The module that imports the thirteen files of `InvariantPreservation/`. |
| `HybridRefinesSpecification/AbstractStatePreservation.lean` | 491 | `AbstractState` preservation for the stutter transitions, and the assembly `Invariant.step`. |
| `HybridRefinesSpecification/NonVacuity.lean` | 1003 | A concrete 24-step run of `hybrid fourProcesses` to a `retABA` decision, so the simulation about it is not vacuous. |
| `HybridRefinesSpecification/Relation.lean` | 748 | The core simulation's relation: the lazy abstract state `AbstractState` and the concrete invariant `Invariant`. |
| `HybridRefinesSpecification/WeakTransitions.lean` | 52 | The abstract-state run lemmas: `SpecStep.decide` as a τ-run (`decide_step`), and a run closed by a visible step (`weakStep_of_run_then_step`). |
| `HybridRefinesSpecification/Simulation.lean` | 411 | **`hybridRefinesSpecification`**: the simulation proof itself, one case per concrete step class, and `hybrid_spec`, its soundness inclusion. One axiom check. |

**`ABA/HybridRefinesSpecification/InvariantPreservation/`** — the cases of a transition of
`hybrid`, and the preservation of `Invariant` across the transitions of each label class.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/InvariantPreservation/CallABA.lean` | 232 | `Invariant.step_callABA`: `Invariant` across a call of the ABA interface — a never-corrupted process's genuine external input, or the idle self-loop. |
| `HybridRefinesSpecification/InvariantPreservation/CallG.lean` | 521 | `Invariant.step_callG`: `Invariant` across a call of the graded-agreement specification, a correct round loop's call, which touches `.call` at the round's instance and `.phase` at the round loop, or the network's call for a process of `F` at a started round (D11, D37). |
| `HybridRefinesSpecification/InvariantPreservation/CallW.lean` | 349 | `Invariant.step_callW`: `Invariant` across a call of the coin, over the two transitions of `WCC.step_callW_cases` — the enabledness loop and the recording call. |
| `HybridRefinesSpecification/InvariantPreservation/GBCATau.lean` | 351 | `Invariant.step_gbcaTau`: `Invariant` across `bindUnset`, the graded-agreement family's only genuine `τ`-step. |
| `HybridRefinesSpecification/InvariantPreservation/RetABA.lean` | 164 | `Invariant.step_retABA`: `Invariant` across a return of the ABA interface, which sets `returned` alone. |
| `HybridRefinesSpecification/InvariantPreservation/RetG.lean` | 961 | `Invariant.step_retG`: `Invariant` across a return of the graded-agreement specification, with the two round-chaining lemmas the proof runs on. |
| `HybridRefinesSpecification/InvariantPreservation/Resolve.lean` | 144 | `Invariant.step_resolve`: `Invariant` across the coin's silent resolution, which writes the drawn outcome to `val`, with `Invariant.exists_correct_wccCaller`, the never-corrupted caller the threshold supplies. |
| `HybridRefinesSpecification/InvariantPreservation/RetW.lean` | 455 | `Invariant.step_retW`: `Invariant` across a return of the coin, the transition that closes a round and, on a grade-2 outcome, enters `toSendDecided`. |
| `HybridRefinesSpecification/InvariantPreservation/DecidedSend.lean` | 181 | `Invariant.step_decidedSend`: `Invariant` across the DECIDED send of a grade-2 round, which inserts the bit into the sender's DECIDED set and moves the sender to `toCallG`. |
| `HybridRefinesSpecification/InvariantPreservation/RoundLoopTau.lean` | 378 | `Invariant.step_roundLoopTau`: `Invariant` across a silent DECIDED transition — a delivery, the relay of a correct process, or the injection or relay of a process of `F`. |
| `HybridRefinesSpecification/InvariantPreservation/SpecificationStateCorruption.lean` | 66 | The readings of corruption at a graded-agreement or coin specification state that the `fail` transition consumes: the accessor of each family after the broadcast, the coin's value, and the corrupted set of a specification state that agrees with the ABA state. |
| `HybridRefinesSpecification/InvariantPreservation/Fail.lean` | 233 | `Invariant.step_fail`: `Invariant` across a synchronised corruption of the two families, the round loops and the ABA network, where `F` gains exactly the named process. |
| `HybridRefinesSpecification/InvariantPreservation/StepCases.lean` | 578 | `hybrid_step_callABA`, `hybrid_step_retABA`, `hybrid_step_fail` and `hybrid_step_tau`: a transition of `hybrid` read back into the transitions of its four components, with `corrupted_eq_false_iff`, the reading of a round loop's replacement flag on the corrupted set. |

**`ABA/ABDY/`** — ABDY22's protocol as it runs, its composed system, the substitution to
`hybrid`, and the simulation into the composition.

| file | lines | what it is |
|---|---|---|
| `ABDY/System.lean` | 897 | **ABDY22's protocol as it runs**, and the subject of the ABDY chain: the implementation at ABDY22's Algorithm 6 — its sixteen round transitions, the network's bound-bit ghost with its write `abdyGhostStep`, and the lemmas that determine them from their labels. |
| `ABDY/Composition.lean` | 295 | **`ABDY.composed`**: the same protocol read as four components, the round instances in a finite map of the rounds the family has touched, with the lemmas that determine a transition of the composite from its label and the builders that assemble one out of transitions of the components. |
| `ABDY/Simulation.lean` | 1071 | **`ABDY.protocolSimulation`**, **`ABDY.protocol_composed`**: the protocol carried into the composed system along `ABDY.ProtocolRelation`, whose eight conjuncts determine the composed state but the family's list of broadcasts. One axiom check. |
| `ABDY/Substitution.lean` | 108 | **`ABDY.substitutionSimulation`**, **`ABDY.substitution`**: the one stage that carries the composed system to `hybrid` — each round's graded-agreement instance replaced by that round's specification, the family substitution under the four congruences. The mirror of `AFW/Substitution.lean`, which takes three stages. |

**`ABA/AFW/`** — AFW25's protocol as it runs, its three composed systems, the substitution to
`hybrid`, and the simulation into the composition.

| file | lines | what it is |
|---|---|---|
| `AFW/System.lean` | 865 | **The gather-based protocol as it runs**: the implementation at AFW25's two-gather construction — the tagged message type collapsing a round's `2n + 2` network states into one sent-set family, the process-major round variables, the network's ghost of the two cores and the bound bit, and the 26 round transitions. |
| `AFW/Composition.lean` | 609 | **`AFW.composed`** and the two systems above it, `AFW.composedOverBroadcastSpecification` and `AFW.composedOverGatherSpecifications`: the three round families `roundFamilyOverBracha`, `roundFamilyOverBroadcastSpecification` and `roundFamilyOverGatherSpecifications` under the composed system's pipeline, each input-enabled (`roundFamilyOverBracha_inputEnabled`, `roundFamilyOverBroadcastSpecification_inputEnabled`, `roundFamilyOverGatherSpecifications_inputEnabled`), with the lemmas that determine a transition of the composite from its label and the builders that assemble one out of transitions of the components. |
| `AFW/RoundProjection.lean` | 683 | `AFW.roundProjection`, the projection that computes a composed state from the implementation, and the relation `AFW.ProtocolRelation` it carries. |
| `AFW/RoundProjectionStep.lean` | 41 | The module that imports the fifteen files of `RoundProjectionStep/`. |
| `AFW/SimulationOfEachTransition.lean` | 1059 | Each transition of the gather-based implementation matched by a run of the composed round: the lemmas that identify a transition from its label, the builders of a transition of one gather instance and of one round, corruption read through the projection, one matching per label class, and `relation_roundStep`, the relation across a transition of a process at its round, the family's round set to the projection after it. |
| `AFW/Simulation.lean` | 727 | **`AFW.protocolSimulation`**, **`AFW.protocol_composed`**: the matching label class by label class, and the gather-based protocol carried into `AFW.composed` along a relation that computes the composed state from the implementation, the ghost included. Two axiom checks. |
| `AFW/Substitution.lean` | 282 | **`AFW.substitutionSimulation`**, **`AFW.substitution`**: the three stages `AFW.composed ⊑ AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid`, each one family substitution under the four congruences, replacing Bracha's broadcast by the broadcast specification, then the gather instances by the gather specifications, then the rounds by the round specifications. One axiom check. |

**`ABA/AFW/RoundProjectionStep/`** — the projection of the composed round after one transition
of the gather-based implementation, one file per class of transitions.

| file | lines | what it is |
|---|---|---|
| `AFW/RoundProjectionStep/ProjectionAfterOneWrite.lean` | 479 | `roundProjection_write` and `roundProjection_writeNoSent`, the write to the round variables and the tagged send every transition performs, read through the projection, with the sent algebra and the lemmas about the projection after the write the transition classes run on. |
| `AFW/RoundProjectionStep/BroadcastReturn.lean` | 198 | `roundProjection_firstGatherInputBroadcastReturn` and its companion at the second gather: the projection after a broadcast instance of either gather returns to the acting process, which files what it returned in that process's gather variables. |
| `AFW/RoundProjectionStep/BroadcastSend.lean` | 228 | `roundProjection_firstGatherInputBroadcastSend` and its companion at the second gather: the projection after a Bracha send in one broadcast instance of either gather. |
| `AFW/RoundProjectionStep/ByzantineInjection.lean` | 232 | `roundProjection_byzantineFirstGather` and its three companions: the projection after the adversary multicasts on behalf of a corrupted sender at a started round, a transition that moves no variables. |
| `AFW/RoundProjectionStep/Delivery.lean` | 277 | `roundProjection_deliverFirstGather` and its three companions: the projection after a delivery, which moves the instance the message's tag names and nothing else, and `roundProjection_deliverLoop`, the delivery at a terminated program, after which every round projects as it did. |
| `AFW/RoundProjectionStep/FirstGatherReturn.lean` | 158 | `roundProjection_firstGatherReturn`: the projection after the first gather returns to the acting process, which records the candidate and whose ghost write records that gather's core, matched by the gather's return and its announcement of the core. |
| `AFW/RoundProjectionStep/GatherSend.lean` | 174 | `roundProjection_firstGatherSend` and `roundProjection_secondGatherSend`: the projection after a gather's `ECHO`, `VOTE` or `BIND`. |
| `AFW/RoundProjectionStep/GatherAndBroadcastTransitions.lean` | 344 | `roundProjection_firstGatherEcho` and its eleven companions: the projection after each `ECHO`, `VOTE` and `BIND` transition of the two gathers and after each `INIT`, `ECHO` and `VOTE` transition of their two input-broadcast families. |
| `AFW/RoundProjectionStep/GradedAgreementCall.lean` | 113 | `roundProjection_callG` and `roundProjection_callGLoop`: the projection after the graded-agreement call, which records the round's input on its first gather, and after the call at a round whose first gather holds an input. |
| `AFW/RoundProjectionStep/GradedReturn.lean` | 101 | `roundProjection_retG`: the projection after the round returns the graded outcome on record to the round loop, whose ghost write records the round's bound bit. |
| `AFW/RoundProjectionStep/OtherRoundsUnchanged.lean` | 139 | `roundProjection_otherTransition` and its three companions: the rounds a transition does not name read exactly as the transition found them, and `toRoundFamily` and its two companions state that as a one-point update of the family of rounds. |
| `AFW/RoundProjectionStep/InputBroadcastCall.lean` | 152 | `roundProjection_firstGatherInputBroadcastCall` and its companion at the second gather: the projection after the acting process calls the instance broadcasting its input, which records the payload as that instance's input. The `⟨INIT, ·⟩` send is the transition `AFW.RoundStep.firstGatherInputBroadcastInit` with its companion `AFW.RoundStep.secondGatherInputBroadcastInit`, projected in `GatherAndBroadcastTransitions.lean`. |
| `AFW/RoundProjectionStep/SecondGatherCall.lean` | 98 | `roundProjection_secondGatherCall`: the projection after the acting process calls the second gather with the candidate on record, which that gather records. |
| `AFW/RoundProjectionStep/SecondGatherReturn.lean` | 127 | `roundProjection_secondGatherReturn`: the projection after the second gather returns to the acting process, which records the graded outcome and whose ghost write records that gather's core. |
| `AFW/RoundProjectionStep/ProtocolRelationConjuncts.lean` | 516 | The four conjuncts of `AFW.ProtocolRelation` that are not projections — the started rounds as the rounds of the family's map, the empty rounds, the replaced programs and `BoundInvariant` — carried across a transition: `protocolRelation_sameRounds`, `protocolRelation_oneRound`, `boundInvariant_writeGhost` and their companions; a round transition leaving the variables of every other round (`roundVariablesMap_lookup_roundStep`); a send, a round event and the graded return firing at variables other than the initial ones (`roundVariables_ne_initial_gbcaSend`, `roundVariables_ne_initial_gbcaRoundEvent`, `roundVariables_ne_initial_retG`); and `boundInvariant_roundStep`, `AFW.BoundInvariant` across every round transition. |

**`ABA/`** — the headlines.

| file | lines | what it is |
|---|---|---|
| `Results.lean` | 326 | The deliverables of both chains, gathered so every citable statement is in one file. Seventeen `#guard_msgs` axiom checks. |

**`ABA/GhostRemoval/`** — the ghost-free system of each protocol, and the removal that
reaches it.

| file | lines | what it is |
|---|---|---|
| `GhostRemoval/GhostFreeSystem.lean` | 346 | **The ghost-free system** `Implementation.systemGhostFree`: `Implementation/System.lean` over a one-element ghost, whose network never announces, and `Implementation.system_ghostRemoval`, the two systems' equality of achievable trace distributions, by an auxiliary-variable removal of the network carried through the pipeline. |
| `GhostRemoval/ImplementationByABDY.lean` | 104 | **`ABDY.ghostFreeProtocol`** and **`ABDY.protocol_ghostRemoval`**: the protocol with the adversary's bound-bit ghost dropped, and the headlines re-derived at it — `ghostFreeProtocol_composed`, `ghostFreeProtocol_refines`, `ghostFreeProtocol_safe`, `ghostFreeProtocol_traces`. Three axiom checks. |
| `GhostRemoval/ImplementationByAFW.lean` | 112 | **`AFW.ghostFreeProtocol`** and **`AFW.protocol_ghostRemoval`**: the gather-based protocol with the adversary's ghost of the two cores and the bound bit dropped, and the headlines re-derived at it — `ghostFreeProtocol_composed`, `ghostFreeProtocol_refines`, `ghostFreeProtocol_safe`, `ghostFreeProtocol_traces`. Five axiom checks. |

The pieces both compositions are built from are in `Composition/Components.lean`, over the
alphabet of `Implementation/Alphabet.lean`. `ABDY/System.lean` and
`GBCA/ABDY/Components.lean` each import it and neither imports the other, so the
two systems of the protocol are assembled independently over one set of components.
`Implementation/System.lean` sits beside `Composition/Components.lean` over the same
alphabet and imports no implementation, which is what lets both implementations instantiate
it. The specification family — `GBCA/ABDY/`,
`Composition/Hybrid.lean` and the core simulation above them — never
imports `ABDY/System.lean`; the protocol enters only at
`ABDY/Simulation.lean`, which is where the two systems meet, and
`Results.lean` reaches it through that file. `ABDY/Composition.lean` sits above the
specification family and carries the composed system; `ABDY/Substitution.lean` sits above that
and carries the substitution to `hybrid`.

The gather-based files form their own stack over `Vocabulary/ProcessAndNetworkState.lean` and
`GBCA/Specification.lean`, meeting the rest of the development in four places:
`GBCA/AFW/Counting.lean` reads the shared round alphabet, `GBCA/AFW/Components.lean` imports
`Composition/Components.lean` for the extended alphabet, which it reads at the empty round message
type, and `GBCA/AFW/AlgorithmOverGatherSpecifications.lean` imports
`GBCA/SpecificationOverRoundAlphabet.lean`, whose
`GBCA.specificationLabelMap` and `GBCA.specificationOverRoundAlphabet` read the
graded-agreement specification over the family alphabet of the round, `AFW/System.lean`
instantiates `Implementation/System.lean`, and `AFW/Substitution.lean` imports
`Composition/Hybrid.lean` for `hybrid`, the system its third stage lands on. No file
of the ABDY chain imports a gather-based one, and `Results.lean` is where the two chains meet,
so either chain reads standalone below it.

## Suggested first read

`Vocabulary/Parameters.lean` → `Vocabulary/Labels.lean` → `Specifications/ABA.lean` → skim
`Specifications/ABASafety.lean`'s two trace predicates →
`HybridRefinesSpecification/Relation.lean`'s module docstring →
`ABDY/System.lean`'s (the system the headlines are about) →
`Composition/Hybrid.lean`'s (the system the core simulation starts from) →
`Results.lean`, whose docstring names the steps of both chains and their files. Follow
it into the statements along `ABDY.protocolSimulation` → `ABDY.substitutionSimulation` →
`hybridRefinesSpecification`, with `Composition/ABAState.lean`'s `ABAState` beside the last. That is
roughly 700 lines of reading and gives the full statement-level picture; descend into the GBCA and
core-simulation proofs only when you want them.

For the two sub-protocol interfaces, read the specification beside the trace property it
carries: `GBCA/Specification.lean` with `GBCA/SpecificationSafety.lean`'s
`specInst_binding`, and `Gather/Specification.lean` with
`Gather/SpecificationSafety.lean`'s `specInst_core`.

For the gather-based chain, by module docstring: `ReliableBroadcast/Bracha/Components.lean` →
`ReliableBroadcast/Bracha/Composition.lean` →
`ReliableBroadcast/Bracha/CompositionStepCases.lean` →
`ReliableBroadcast/Bracha/Algorithm.lean` → `Gather/Components.lean` →
`Gather/Composition.lean` → `Gather/CompositionStepCases.lean` →
`Gather/AlgorithmOverBroadcastSpecification.lean` → `GBCA/AFW/Components.lean` →
`GBCA/AFW/Composition.lean` → `GBCA/AFW/CompositionStepCases.lean` →
`GBCA/AFW/AlgorithmOverGatherSpecifications.lean` →
`AFW/Composition.lean` → `AFW/Substitution.lean` → `AFW/Simulation.lean`. The first twelve are
the three levels, four files each, in the pattern of the section What to expect;
`GBCA/AFW/AlgorithmOverGatherSpecifications.lean` is the algorithm the counting
refinement runs on;
`AFW/Composition.lean` holds the three systems at the protocol shape and `AFW/Substitution.lean`
the three stages between them; `AFW/Simulation.lean` is the simulation into `AFW/System.lean`, the
system that runs, over the matching runs of `AFW/SimulationOfEachTransition.lean`, one per transition of
the implementation. The two
counting arguments are `Gather/CommonCoreCounting.lean`, read against `Gather/Invariant.lean` and
`Gather/Specification.lean` alone, and `GBCA/AFW/Counting.lean`. Each refinement rests on the
characterisation of its composition by an algorithm, so it is readable against the file that states
that algorithm.

## Where else to look

`../README.md` maps the library and its shared framework. `../DESIGN-Composition.md` is why
the chains are cut where they are; `../DESIGN-HybridRefinesSpecification.md` and `../DESIGN-GBCARefinesSpecification.md` are the
narrative accounts of the two large protocol-chain proofs, and `../DESIGN-GatherComposition.md`
of the gather-based stack — including the counting argument for the gather
specification's core; `../DESIGN-InputOutput.md` is the input-output discipline of
the components — which component outputs each label, where each guard sits, and which loop makes
each input enabled — and `../DESIGN-Decomposition.md` the constraints the decomposition proofs
impose on the compositions; `../NOTES-Fidelity.md` is the encoding against
its sources and `../NOTES-Liveness-Roadmap.md` what termination would take. The prose
account is the ABA chapter of `../../blueprint/src/`, in two editions over one set of
statements: the default one (`content.tex`, each object and result stated against its Lean
declaration) and the full one (`content-full.tex`, adding the full lists of transitions, the
pseudocode and the proof bodies).

## Future work

- **Achievability theorem**: one explicit scheduler taking `protocol fourProcesses` to a two-return
  decision trace `t`, with `∃ D ∈ achievableTraceDists (protocol fourProcesses), D t ≠ 0` — the
  machine-checked non-vacuity for `ABDY.main`'s own system, exercising Agreement with two
  returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `ABDY/System.lean` the budget is a component guard on the one local
  state that holds the corrupted set, so `ABDY.protocol_safe` and `ABDY.protocol_traces`
  need no hypothesis on the trace.
