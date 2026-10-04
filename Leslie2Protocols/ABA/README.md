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
with its four implementations `GBCA.ByABDY.composition_binding` in
`GBCA/ABDY/Binding.lean` and `GBCA.roundOverGatherSpecifications_binding`,
`GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding` in
`GBCA/AFW/Binding.lean`; and `Gather.specInst_core` in `Gather/SpecificationSafety.lean`, with
the two implementations `Gather.instanceOverBroadcastSpecification_core` and
`Gather.instanceOverBracha_core` in `Gather/CommonCore.lean`.

The architecture in two lines, all of it in the protocol's own coordinates:

```
ABDY.protocol  ⊑  ABDY.composed                                                                                      ⊑  hybrid  ⊑  ABA.spec
 AFW.protocol  ⊑   AFW.composed  ⊑  AFW.composedOverBroadcastSpecification  ⊑  AFW.composedOverGatherSpecifications  ⊑  hybrid  ⊑  ABA.spec
```

One GBCA specification, two verified implementations, each carried from the protocol as it runs. The
first line carries the direct implementation (ABDY22's Algorithm 6, D18), the second the
gather-based one (AFW25's two-gather construction, D24), and the two chains share every inclusion
from `hybrid` up. Every system above a protocol is a composition of components, down to the programs
that run it. On the first line a round is the `n` graded-agreement programs beside the round's
network. On the second a round is `n` programs beside the round's network, in parallel with two
gather instances, and a gather instance is `n` programs beside the gather network, in parallel with
`2n` reliable-broadcast instances, each of them `n` programs beside the instance's network. The
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
sets, the coin's call and return, corruption, the network and the composition pipeline — is
settled by the round interface and the specification, so `Implementation/System.lean` writes it
once, parametric in the round message type, the per-process per-round variables, the round's
transitions, and a per-round ghost of the network, updated on every transition and read as
the guard of the two graded-agreement return transitions (D30). `ABDY/System.lean` supplies ABDY22's;
`AFW/System.lean` supplies the gather-based one.

- `ABDY.protocol` — ABDY22's protocol as it runs: `n` programs beside the network, which
  owns the message sets and the corrupted set, and the common coin, the only component whose
  transitions are not Dirac. A program reads its own replacement flag and nothing else about
  corruption: not the corrupted set, not the budget, not another process's status. A corruption
  replaces the program of the process it names (D23). A program holds its round loop beside its
  round variables — its variables in every round it has touched, in a finite map — and
  terminates once its own return has fired and `2f + 1` DECIDED messages have been received (D22).
- `ABDY.composed` — the same protocol read as a composition of components: the round instances, the
  `n` round loops, the ABA network holding the DECIDED sets, and the common coin. `ABDY.protocolSimulation`
  carries `ABDY.protocol` into it along the Dirac lift of `ABDY.ProtocolRelation`, and
  `ABDY.protocol_composed` is the inclusion it yields. The relation determines every composed coordinate
  from the protocol state: the entry of process `j` in the instance of round `r` is the round-`r`
  variables that `j` holds (D22). What makes the inclusion one-directional is on the
  composed system. A round instance has transitions for the Byzantine graded-agreement call and
  return, and no program of the protocol has one (D11), and the instance's round transitions carry no
  termination guard, so the instance answers a send or a delivery at a process the protocol has
  terminated. This is where the
  chain passes from implementation to specification.
- `hybrid` — each round's instance replaced by the graded agreement specification
  (`ABDY.substitutionSimulation`), the other three components untouched. This is what the core
  simulation runs on.
- `ABA.spec` — the single-automaton system of agreement, reached by `hybridRefinesSpecification`.

Components talk only through synchronized labels, and no component reads another's state.
Why the cuts sit there, and what they buy, is `../DESIGN-Composition.md`.

## Ghost outputs

Two return labels announce a value that no program computes. A graded-agreement return `retG r id
out β` names the round's bound bit `β` beside the graded outcome, and a gather return `ret id g C`
names the instance's common core beside the map (D29). Each value is state of the specification,
written once by an internal transition. The implementations hold the same value as ghost state, in each
case at the component whose own state determines it. A gather instance's core is a field of the
gather network, computed by `Gather.coreOf` from that network's sent sets and corrupted set alone.
ABDY22's round holds the bound bit as a field of the round's network state; the gather-based round
gives it a component of its own, the round's network, which carries no messages and holds the bit
alone. In the implementations both belong to the network, which holds a ghost per
round (D30). No program's variables carry either and no program's transition reads one. The two
graded-agreement return transitions of the network do read the round's ghost, and what they read
from it is the value the label announces, never whether the transition fires: the read admits a bit
at every state
(`ghostOutput_total` in `GhostRemoval/GhostFreeSystem.lean`). The announcement therefore leaves every
execution of the protocol as it is.

What a program does hold of a sub-protocol's answer is its own variables holding what the instances
have returned to it: the fields `Gather.ProcessVariables.inputBroadcastReturned` and
`bindBroadcastReturned`, written on the broadcast return events. Four transitions of a gather
program read them — `sendEcho`, `sendVote`, `bindCall` and `ret` — so they are state a guard consults and not
ghost state.

For the bound bit that inertness is a theorem. `GhostRemoval/GhostFreeSystem.lean` removes
the adversary's ghost onto the ghost-free system `Implementation.systemGhostFree`, whose
returns announce any bit, and `ABDY.protocol_ghostRemoval` and `AFW.protocol_ghostRemoval` are the
resulting equalities of achievable trace distributions. No map on labels appears in either
statement: `Label.retG` lies in `Label.hiddenAPI`, so the announced bit is silent at protocol
level and the final hiding discharges the label identification the removal runs on.

What the announcement buys is binding as a property of a single trace, at the instance level. Every
round-`r` return of a trace of `GBCA.specInst` names one bit, and every one of them that hands out a
value hands out that bit (`GBCA.BindingTrace`, `GBCA.specInst_binding`). Every return of a trace of
`Gather.specInst` names one payload set, of at least `n − f` entries and below the returned map
(`Gather.CoreTrace`, `Gather.specInst_core`). Both predicates are read off labels alone, so a
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

Each departure from the source blueprint carries a label D1–D36, cited at the point where
it applies. The registry — every active label glossed, and the numbers the range skips —
is the Deviations paragraph of `../../blueprint/src/content.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its sources beyond that
registry.

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
with the lemmas that exist only to prove it, and Mathlib's `linter.style.longFile` caps a file
at 1500 lines, a file over the cap carrying an explicit `set_option linter.style.longFile`
raise.


**`ABA/Vocabulary/`** — the variables and alphabets every implementation is written over.

| file | lines | what it is |
|---|---|---|
| `Vocabulary/Parameters.lean` | 145 | The parameters `P` — `n`, `f` with `n > 3f`, the reliable broadcast's `ECHO` quorum `receivedEchoQuorum`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Vocabulary/Labels.lean` | 147 | The shared label alphabet `Label n`: the visible API, the hidden sub-protocol calls and returns, `τ`. |
| `Vocabulary/ProcessAndNetworkState.lean` | 442 | The two-part vocabulary of the gather-based development: network state (D5) beside `n` process local states, with the multicast/delivery/corrupt operations and the quorum-intersection lemmas, stated once and shared by the three sub-protocol encodings. |
| `Vocabulary/RoundLoop.lean` | 250 | **The ABA round loop**, per process and nothing else: the phase machine, the control state, the round-loop variables. |

**`ABA/Specifications/`** — the specification all safety is measured against, and the
coin the protocol calls.

| file | lines | what it is |
|---|---|---|
| `Specifications/ABA.lean` | 251 | **The top-level ABA specification**, the system all safety is measured against. Eight transitions over `SpecState`, whose control mode carries the flip (D21) and two of which are the corrupted interface (D23). The decision is guarded by the `f + 1` support guard `InputSupport` alone (D13). |
| `Specifications/ABASafety.lean` | 894 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `Specifications/WCC.lean` | 233 | The weak common coin specification, per round, and the coin value domain `CoinValue`. Five transitions: a call that records its caller, an unguarded loop on the call label that records nothing, the resolution on `τ`, enabled at `val = ⊥` once the callers number more than `f` (D31) and drawing the coin, a return and the corruption. Held at specification level by design. |

**`ABA/Implementation/`** — the shape of a protocol as it runs, written once and
parametric in the graded-agreement implementation: the process programs, the network
adversary, the adversary's ghost, the composition of the three beside the common
coin, and the lemmas that read a transition off its label.

| file | lines | what it is |
|---|---|---|
| `Implementation/Alphabet.lean` | 219 | The extended alphabet `ExtendedLabel n M E` of the implementation, parametric in the round message type and in the type of the round's own calls and returns, with the label pullback the common coin is read along. |
| `Implementation/System.lean` | 717 | **The implementation of a protocol**, parametric in the graded-agreement implementation: the shared transitions of a program and of the network, the payload a graded-agreement call multicasts where it multicasts one, the adversary's per-round ghost with its update and its output (D30), the pipeline that composes them beside the common coin, and `IsRoundStep`, what an implementation states about its own transitions. |
| `Implementation/StepCases.lean` | 517 | The transitions of one program and of the network, read off their labels: the participant's transition as its guards together with the Dirac it produces, the idle transition of a non-participant as the identity, and the determinacy of both step relations. |
| `Implementation/NetworkStateWritesAndRemovals.lean` | 243 | The field algebra of the network's four writes: a round multicast, a DECIDED multicast, corruption and the ghost write, each read down to the fields of the state it delivers. With them the two removals, `NetworkState.forgetGhost` to the state over the trivial ghost `Unit` and `forgetBound` to the label with the announced bound bit fixed at `false`. |
| `Implementation/CompositeTransitions.lean` | 231 | The transitions of the implementation, read off their labels: the pipeline `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct` unfolded to the transitions of the process group, of the network and of the common coin, and the constraint a graded-agreement return places on the bound bit its label carries. |

**`ABA/ReliableBroadcast/`** — the reliable-broadcast specification and Bracha's
implementation of it.

| file | lines | what it is |
|---|---|---|
| `ReliableBroadcast/Specification.lean` | 160 | The reliable-broadcast specification, per leader (blueprint TS 6, safety-only): the input/committed-value split with the guarded commit (D27). |

**`ABA/ReliableBroadcast/Bracha/`** — Bracha's implementation of that specification, from the
messages it sends to its refinement: the components one instance runs on, the composition they
make, the algorithm that composition realises, and the simulation into the specification.

| file | lines | what it is |
|---|---|---|
| `ReliableBroadcast/Bracha/MessagesAndVariables.lean` | 71 | `BRB.Message`, Bracha's three message levels; `BRB.ProcessVariables`, the variables one process keeps in one instance, holding the leader's call, the write-once `ECHO` and `VOTE` send fields and the return flag; and `BRB.BrachaState`, the composed state they make with the instance's network (D1, D5). |
| `ReliableBroadcast/Bracha/Components.lean` | 242 | The pieces one instance runs on: the interface alphabet `BRB.InstanceLabel`, in which the call loop is a label of its own, the instance-internal alphabet `BRB.BroadcastLabel` with the multicast and the delivery beside it, the local program `BRB.broadcastProgram` with its transitions, and the instance's network `BRB.broadcastNetwork` with its own. |
| `ReliableBroadcast/Bracha/Composition.lean` | 49 | **The Bracha instance, composed**: `BRB.brachaInstance`, the `n` per-process programs beside the instance's network with the instance's own events hidden, over the interface alphabet in which the call loop is a label of its own; `BRB.brachaInstanceExtended` before the hiding. |
| `ReliableBroadcast/Bracha/SpecificationOverInstanceAlphabet.lean` | 218 | `BRB.specificationOverInstanceAlphabet`: the broadcast specification read along `BRB.specificationLabelMap`, which sends the call loop to the call it stands for; the determinacy of the composition's transitions, and the sections along which a weak run of the specification is read back over the instance's interface. |
| `ReliableBroadcast/Bracha/CompositionStepCases.lean` | 402 | The transitions of `BRB.brachaInstance` read off their labels: a step of the instance split into a hidden synchronisation and an interface label, a synchronised step read as the transitions of the programs and the network, one program's transition and the network's per label class, and the write each transition makes on the composed state. |
| `ReliableBroadcast/Bracha/Algorithm.lean` | 297 | `BRB.BrachaAlgorithm`, the transitions of the composed instance `BRB.brachaInstance`: Bracha's three message levels in the form of AFW25's Algorithm 1 (D34) over the two-part state, one constructor per case of the characterisation `brachaInstance_step_iff_algorithm`, which is proved here. A relation on that state; the system is the composition of `ReliableBroadcast/Bracha/Composition.lean`. |
| `ReliableBroadcast/Bracha/EchoWitness.lean` | 59 | `BRB.EchoWitness`: some process holds a quorum of received `ECHO m` messages, more than `(n + f) / 2` senders. It is blind to the corrupted set and monotone, so it survives every transition of the instance and every corruption. |
| `ReliableBroadcast/Bracha/Invariant.lean` | 624 | `BRB.Invariant`, what the instance maintains: a correct sender's sent message matches its write-once field, a correct echo carries a correct leader's input, and a correct vote is backed by an echo witness. With it the three consequences the refinement needs — at most one value is ever witnessed, every return guard yields a witness, and under a correct leader a witness identifies the leader's input. |
| `ReliableBroadcast/Bracha/SpecificationRelation.lean` | 74 | `BRB.SpecificationRelation`, which the gather substitution lifts: the calls, the return flags and the corrupted sets agree, the invariant holds, and a committed value carries an echo witness. With it at the two initial states and across a corruption of both systems at once. |
| `ReliableBroadcast/Bracha/RefinesSpecification.lean` | 495 | `brachaRefinesSpecification`: the Bracha instance refines TS 6 (D27), read over the instance's interface and along `BRB.SpecificationRelation`. `specificationRelation_transition` matches every transition of `BRB.BrachaAlgorithm` by a weak run of the specification, the commit fired on demand at the first return that needs it, and four lemmas beside it hold the relation across one transition. |

**`ABA/Gather/`** — gather over reliable broadcast.

| file | lines | what it is |
|---|---|---|
| `Gather/Specification.lean` | 215 | The gather specification (blueprint TS 4): call/commit split (D26) and the write-once core the return labels announce (D29). |
| `Gather/SpecificationSafety.lean` | 147 | `CoreTrace`, the common core read off a trace, and `specInst_core`, which holds it at the specification. |
| `Gather/MessagesAndCommonCore.lean` | 172 | What a gather instance is written over — the `ECHO`/`VOTE` messages and one process's variables — and the core `coreOf` of a gather network state, with the incidence lemmas the counting argument sums. |
| `Gather/Components.lean` | 510 | The components of one gather instance: the interface and instance-internal alphabets, the six events the instance hides, one process's variables and the gather network state, the two pullbacks along which a broadcast instance joins the composition (D32), the step relations of the gather program and the gather network, and the gather programs beside the gather network the two automata make. |
| `Gather/Composition.lean` | 355 | **The gather instance, composed**: the gather programs and network in parallel with `2n` composed broadcast instances — `Gather.instanceOverBroadcastSpecification` over the broadcast specifications and `Gather.instanceOverBracha` over Bracha's — read back over the gather alphabet extended by the call loop, with the four projections of the composed state and the determinacy the LTS instances rest on. |
| `Gather/SpecificationOverInstanceAlphabet.lean` | 157 | `Gather.specificationOverInstanceAlphabet`: the gather specification read along `Gather.specificationLabelMap`, which sends the call loop to the call it stands for, with the sections along which a weak run of the specification is read back over the instance's interface. |
| `Gather/CompositionStepCases.lean` | 692 | The transitions of `Gather.instanceOverBroadcasts` read off their labels: a step of the instance split into a hidden gather event and an interface label, a synchronised step read as the transitions of the four factors, the pullbacks computed label by label, one gather program's transition and the gather network's per label class, and the write each transition makes on the composed state. |
| `Gather/AlgorithmOverBracha.lean` | 621 | `Gather.AlgorithmOverBracha`, the transitions of `Gather.instanceOverBracha` stated over the composition's state, one constructor per case of `instanceOverBracha_step_iff_algorithm`; a transition that reaches a broadcast coordinate carries that Bracha instance's own transition as a hypothesis. A relation on that state; the system is the composition of `Gather/Composition.lean`. |
| `Gather/AlgorithmOverBroadcastSpecification.lean` | 722 | `Gather.AlgorithmOverBroadcastSpecification`, the transitions of `Gather.instanceOverBroadcastSpecification` (blueprint Algorithm 4, the binding form of AFW25's Algorithm 5) stated over the composition's state, one constructor per case of `instanceOverBroadcastSpecification_step_iff_algorithm`. A relation on that state; the system is the composition of `Gather/Composition.lean`. |
| `Gather/Invariant.lean` | 1301 | `Gather.Invariant`, what the gather instance over the broadcast specifications maintains: the conformance clauses — the corruption budget, delivery soundness, the returned values a program holds, a committed entry is the payload its instance recorded, the received messages backing a correct `ECHO`, `VOTE` and `BIND`, and the gather variables backing the payload an input instance was called with — beside the approval of every `ECHO` field. |
| `Gather/CommonCoreCounting.lean` | 334 | The counting argument for the core: `coreOfNetwork` has `n − f` committed entries and lies below the committed `BIND` payload of every process outside `F`, with the `f + 1` witness the specification's bind guard consumes. |
| `Gather/SpecificationRelation.lean` | 101 | `Gather.SpecificationRelation`, which the counting refinement runs along: the specification's calls agree with the gather's variables, the return flags, the corrupted sets and the core agree, the invariant holds, and a committed entry and the recorded core carry the witnesses on the received messages the counting supplies. |
| `Gather/RefinesSpecification.lean` | 936 | `refinesSpecification`: the gather-over-BRB instance refines TS 4. The return run commits the entries it reads, writes the core at `coreOfNetwork` of the network state, and returns, in one weak transition. |
| `Gather/BroadcastSubstitution.lean` | 153 | `broadcastSubstitution`: the broadcast substitution inside gather, per coordinate, carried through the composition by the congruences. |
| `Gather/CommonCore.lean` | 142 | `instanceOverBroadcastSpecification_core` and `instanceOverBracha_core`: the common core read off a trace holds at the two gather implementations, carried down from the specification along their refinements. |

**`ABA/GBCA/`** — the graded-agreement specification, the binding it carries, and the reading of it over the alphabet of a round.

| file | lines | what it is |
|---|---|---|
| `GBCA/Specification.lean` | 291 | The graded binding crusader agreement specification, per round. Binding is negative, and every return announces the round's bound bit (D19, D29). |
| `GBCA/SpecificationSafety.lean` | 875 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. `specInst_binding` reads binding off a trace. |
| `GBCA/SpecificationOverRoundAlphabet.lean` | 188 | `GBCA.specificationOverRoundAlphabet`: the graded-agreement specification read along `GBCA.specificationLabelMap`, which identifies the three Byzantine call and return transitions and the call loop with the specification labels they stand for, with the sections along which a weak run of the specification is read back over a round's interface (D11). |
| `GBCA/BindingOverRoundAlphabet.lean` | 208 | `GBCA.specificationOverRoundAlphabet_binding`: binding of the specification read over a round's alphabet. The exclusion set only grows along an execution and no state of one excludes two bits, so every label the projection sends to a round-`r` return announces the same bit, and every one of them that hands out a value hands out that bit (`GBCA.BindingTraceExtended`). |

**`ABA/Composition/`** — the components the composed systems are built from, the ABA state
and the protocol-shaped specification.

| file | lines | what it is |
|---|---|---|
| `Composition/Components.lean` | 876 | The extended alphabet `ExtendedLabel n M`, parametric in the type `M` of the messages a graded-agreement round exchanges and over the empty type of round calls and returns, the common coin read along its label pullback, the round loop of one process, and the ABA network — the pieces the two compositions are built from. |
| `Composition/ABAState.lean` | 391 | The ABA state as one object: the round-loop variables beside the DECIDED network, with the accessors the invariant is stated in. |
| `Composition/Hybrid.lean` | 439 | **`hybrid P M`**: the protocol-shaped specification over the round message type `M` — the family of round specifications beside the round loops, the ABA network and the common coin, under the pipeline that hides the labels the components synchronise on, reads the result back over `Label n` and hides the sub-protocol API — with the transitions of its four components and the three routes a labelled transition takes through the two hidings. |

**`ABA/GBCA/ABDY/`** — ABDY22's implementation of that specification: the round's
graded-agreement instance, the algorithm it runs, the labels its family owns, and the refinement
into the graded-agreement specification with the binding it carries. The files are given in import
order.

| file | lines | what it is |
|---|---|---|
| `GBCA/ABDY/MessagesAndVariables.lean` | 664 | The messages a graded-agreement round exchanges and the state it runs on: the five message levels of Algorithm 6, the round's bound bit `boundOf` (D29), one process's round variables beside the round's network state `NetworkState`, their pair `RoundState` with the projections and writes of each component, the counting the algorithm's guards read, and the two quorum lemmas (D1, D5). |
| `GBCA/ABDY/Components.lean` | 430 | The components of the round's graded-agreement instance: the instance-internal alphabet that carries the multicast and the delivery, the step relation `GBCAProgramStep` of one corruption-blind local program and `GBCANetworkStep` of the round's network, and the two systems `gbcaProgram` and `GBCANetwork` they carry (D11). |
| `GBCA/ABDY/Composition.lean` | 282 | **The round's graded-agreement instance**: `GBCA.ByABDY.composition`, the programs beside the round's network with their two synchronisations hidden and the result read back over the extended alphabet, the round-indexed family `gbcaInstanceFamily` with the three functions it is built from, the determinacy the LTS instances rest on, and the readers and builders of one instance transition. |
| `GBCA/ABDY/CompositionStepCases.lean` | 520 | The transitions of the round instance read off their labels: one program's transition and the network's transition per label class, the round variables beside the network state read as one composed state, the two cases of a transition of the composition, and the network's transition off a round-tagged label. |
| `GBCA/ABDY/RoundFamilyOwnedLabels.lean` | 88 | The labels the round-indexed family owns, evaluated: `GBCA.ByABDY.roundOwnsLabel` and `GBCA.ByABDY.isFailLabel` at every label of the extended alphabet, over every round message type, which is what discharges the premises of the composed system by `simp`. |
| `GBCA/ABDY/Algorithm.lean` | 512 | **The algorithm of the round's graded-agreement composition**, ABDY22's Algorithm 6 in full (D18): `Algorithm`, one transition per line of Algorithm 6 (D8), and the characterisation `composition_projects` — at a label of the round's interface, every transition of the composition is the algorithm's transition at the specification label that interface label projects to, one step for one step. One axiom check. |
| `GBCA/ABDY/Invariant.lean` | 833 | The inductive invariant `Invariant` of the composed state: the corruption budget, delivery soundness, protocol conformance and write-once recording of correct multicasts, participation, budget-robust input origin, and the `f + 1` genuine-holder support `InputSupport` (D15). `Invariant.initial` and `Invariant.step` hold it at the initial state and along every transition of the algorithm. |
| `GBCA/ABDY/ExclusionWitness.lean` | 337 | The exclusion witnesses `ReceivedEchoQuorum` (Case A), `VoteQuorumAgainst` (Case B) and their disjunction `ExclusionWitness`: a monotone witness on the received messages that a bit can never gain grade-≥1 support. The derivation chains read a witness off a return's own received messages. |
| `GBCA/ABDY/SpecificationRelation.lean` | 409 | The simulation relation `specificationRelation`: the specification's `call`, `ret` and `F` read off the composed state, `excluded` and `grade` carried as witnesses on the pattern of received messages, and the round's bound bit tied to `excluded`; `specificationRelation_init` at the two initial states and `specificationRelation_corrupt` across a corruption of both systems, which the family lifting consumes. The specification's guards and the two-step exclusion-then-return runs are derived from it. |
| `GBCA/ABDY/RefinesSpecification.lean` | 669 | The matching `specificationRelation_transition` and the refinement `refinesSpecification` of the round's composition by the specification read over the round's interface, by exclude-on-demand; its soundness inclusion `composition_specificationTraces`; and the broadcast corruption act at the round's alphabet with `refinesSpecification_failAct`, the second premise the family lift consumes. Two axiom checks. |
| `GBCA/ABDY/Binding.lean` | 51 | **`composition_binding`**: binding of the round's composition on a trace, carried from the specification over the round's alphabet along `composition_specificationTraces`. One axiom check. |

**`ABA/GBCA/AFW/`** — the two-gather round and the three compositions that carry it.

| file | lines | what it is |
|---|---|---|
| `GBCA/AFW/Counting.lean` | 368 | **The counting of the two-gather round** (AFW25 Algorithm 4 at R = 2, its approximate-agreement subroutine replaced by a local count, D24): the candidate and the grade, `candidate` and `gradeOf`, the bound bit `boundOfCore` read off the first gather's core (D29), and the entry counts the refinement consumes. |
| `GBCA/AFW/Components.lean` | 536 | The components of the graded-agreement round: the round-internal alphabet and a program's alphabet, the program's variables `ProcessVariables`, the three pullbacks along which the programs and the two gather instances join the round, the step relations `ProgramStep` and `NetworkStep` of one graded-agreement program and of the round's network, and `roundPrograms`, the `n` programs beside that network. |
| `GBCA/AFW/Composition.lean` | 352 | **The graded-agreement round, composed**: the round's programs in parallel with two gather instances — `GBCA.ByAFW.roundOverGatherSpecifications` over the gather specifications, `GBCA.ByAFW.roundOverBroadcastSpecification` over gather-over-BRB, and **`GBCA.ByAFW.roundOverBracha`, the gather-based GBCA implementation**, over gather-over-Bracha — read over the family alphabet `ExtendedLabel n Empty`, with the four projections of the round's state and the determinacy the LTS instances rest on. |
| `GBCA/AFW/CompositionStepCases.lean` | 459 | The transitions of `GBCA.ByAFW.roundOverGathers` read off their labels: a step of the round split into a hidden event and a family label, a synchronised step read as the transitions of the round's programs, the round's network and the two gather instances, and one graded-agreement program's transition and the round's network's transition per label class. |
| `GBCA/AFW/AlgorithmOverGatherSpecifications.lean` | 534 | `GBCA.ByAFW.AlgorithmOverGatherSpecifications`, the transitions of `GBCA.ByAFW.roundOverGatherSpecifications` stated over the round's state, one constructor per case of `roundOverGatherSpecifications_step_iff_algorithm`. A relation on that state; the system is the composition of `GBCA/AFW/Composition.lean`. |
| `GBCA/AFW/OutputWitness.lean` | 257 | The counts the counting refinement consumes, and the two witnesses it carries: `OutputWitness`, what a recorded graded outcome witnesses about the two cores, and `ExclusionWitness`, the first gather's core counting a bit below `|S| − f`. Both survive every later transition, the cores being written once. |
| `GBCA/AFW/Invariant.lean` | 739 | `GBCA.ByAFW.Invariant`, what the round over the gather specifications maintains: the corruption budget, a committed gather entry of a correct process is its call, what a candidate and a recorded grade witness, the transfer of the candidate to the second gather's call, the bound bit read off the first gather's core (D29), and the core-write guards. |
| `GBCA/AFW/SpecificationRelation.lean` | 124 | `GBCA.ByAFW.SpecificationRelation`, which the counting refinement runs along: the invariant holds, the calls, the return flags and the corrupted sets agree, an excluded bit carries an exclusion witness and is the complement of the round's bound bit, and each grade guard is witnessed on the second gather's core. Broadcast compatibility and one axiom check. |
| `GBCA/AFW/RefinesSpecification.lean` | 508 | `refinesSpecification`: the two-gather round refines the GBCA specification. Every case of the algorithm is matched by a weak run of the specification, at most two steps long, and the run is lifted to the round's interface. One axiom check. |
| `GBCA/AFW/BroadcastSubstitution.lean` | 139 | `broadcastSubstitution`: Bracha's broadcast replaced by the broadcast specification at each of the two gather coordinates, carried through the round by the congruences, with its trace-distribution inclusion and its broadcast compatibility. Two axiom checks. |
| `GBCA/AFW/GatherSubstitution.lean` | 136 | `gatherSubstitution`: each gather instance replaced by the gather specification, carried through the round the same way, with its trace-distribution inclusion and its broadcast compatibility. Two axiom checks. |
| `GBCA/AFW/Binding.lean` | 158 | The three compositions of the round reach the specification over the round's alphabet: the inclusions `roundOverGatherSpecifications_refines`, `roundOverBroadcastSpecification_specificationTraces` and `roundOverBracha_specificationTraces`, the round composite `roundOverBracha_refinesSpecification`, and the binding each of them carries — `GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding`. Six axiom checks. |

**`ABA/HybridRefinesSpecification/`** — the core simulation of the blueprint's §3,
`hybrid ⊑ ABA.spec`, and its witnesses.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/InvariantPreservation.lean` | 33 | The module that imports the thirteen files of `InvariantPreservation/`. |
| `HybridRefinesSpecification/AbstractStatePreservation.lean` | 392 | `AbstractState` preservation for the stutter transitions, and the assembly `Invariant.step`. |
| `HybridRefinesSpecification/NonVacuity.lean` | 920 | A concrete 24-step run of `hybrid fourProcesses` to a `retABA` decision, so the simulation about it is not vacuous. |
| `HybridRefinesSpecification/Relation.lean` | 695 | The core simulation's relation: the lazy abstract state `AbstractState` and the concrete invariant `Invariant`. |
| `HybridRefinesSpecification/WeakTransitions.lean` | 52 | The abstract-state run lemmas: `SpecStep.decide` as a τ-run (`decide_step`), and a run closed by a visible step (`weakStep_of_run_then_step`). |
| `HybridRefinesSpecification/Simulation.lean` | 468 | **`hybridRefinesSpecification`**: the simulation proof itself, one case per concrete step class, and `hybrid_spec`, its soundness inclusion. One axiom check. |

**`ABA/HybridRefinesSpecification/InvariantPreservation/`** — the cases of a transition of
`hybrid`, and the preservation of `Invariant` across the transitions of each label class.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/InvariantPreservation/CallABA.lean` | 224 | `Invariant.step_callABA`: `Invariant` across a call of the ABA interface — a never-corrupted process's genuine external input, or the idle self-loop. |
| `HybridRefinesSpecification/InvariantPreservation/CallG.lean` | 502 | `Invariant.step_callG`: `Invariant` across a call of the graded-agreement specification, which touches `.call` at the GBCA instance and `.phase` at the core. |
| `HybridRefinesSpecification/InvariantPreservation/CallW.lean` | 334 | `Invariant.step_callW`: `Invariant` across a call of the coin, over the two transitions of `WCC.step_callW_cases` — the enabledness loop and the recording call. |
| `HybridRefinesSpecification/InvariantPreservation/GBCATau.lean` | 341 | `Invariant.step_gbcaTau`: `Invariant` across `bindUnset`, the graded-agreement family's only genuine `τ`-step. |
| `HybridRefinesSpecification/InvariantPreservation/RetABA.lean` | 152 | `Invariant.step_retABA`: `Invariant` across a return of the ABA interface, which sets `returned` alone. |
| `HybridRefinesSpecification/InvariantPreservation/RetG.lean` | 943 | `Invariant.step_retG`: `Invariant` across a return of the graded-agreement specification, with the two round-chaining lemmas the proof runs on. |
| `HybridRefinesSpecification/InvariantPreservation/Resolve.lean` | 142 | `Invariant.step_resolve`: `Invariant` across the coin's silent resolution, which writes the drawn outcome to `val`, with `Invariant.exists_correct_wccCaller`, the never-corrupted caller the threshold supplies. |
| `HybridRefinesSpecification/InvariantPreservation/RetW.lean` | 436 | `Invariant.step_retW`: `Invariant` across a return of the coin, the transition that closes a round and, on a grade-2 outcome, enters `toSendDecided`. |
| `HybridRefinesSpecification/InvariantPreservation/DecidedSend.lean` | 172 | `Invariant.step_decidedSend`: `Invariant` across the DECIDED send of a grade-2 round, which inserts the bit into the sender's DECIDED set and moves the sender to `toCallG`. |
| `HybridRefinesSpecification/InvariantPreservation/RoundLoopTau.lean` | 344 | `Invariant.step_roundLoopTau`: `Invariant` across a core `τ` — DECIDED delivery, echo, or byzantine injection. |
| `HybridRefinesSpecification/InvariantPreservation/SpecificationStateCorruption.lean` | 51 | The four readings of corruption at a graded-agreement or coin specification state that the `fail` transition consumes. |
| `HybridRefinesSpecification/InvariantPreservation/Fail.lean` | 219 | `Invariant.step_fail`: `Invariant` across a synchronised corruption of all three components, where `F` gains exactly the named process. |
| `HybridRefinesSpecification/InvariantPreservation/StepCases.lean` | 590 | `hybrid_step_callABA`, `hybrid_step_retABA`, `hybrid_step_fail` and `hybrid_step_tau`: a transition of `hybrid` read back into the transitions of its four components, with `corrupted_eq_false_iff`, the reading of a round loop's replacement flag on the corrupted set. |

**`ABA/ABDY/`** — ABDY22's protocol as it runs, its composed system, the substitution to
`hybrid`, and the simulation into the composition.

| file | lines | what it is |
|---|---|---|
| `ABDY/System.lean` | 915 | **ABDY22's protocol as it runs**, and the subject of the ABDY chain: the implementation at ABDY22's Algorithm 6 — its fourteen round transitions, the payload the call multicasts, the adversary's bound-bit ghost, and the lemmas that read them off their labels. |
| `ABDY/Composition.lean` | 266 | **`ABDY.composed`**: the same protocol read as four components, one round instance per round retained at every moment, with the lemmas that read a transition of the composite off its label and the builders that assemble one out of transitions of the components. |
| `ABDY/Simulation.lean` | 1094 | **`ABDY.protocolSimulation`**, **`ABDY.protocol_composed`**: the protocol carried into the composed system along `ABDY.ProtocolRelation`, whose five unguarded conjuncts determine the composed state. |
| `ABDY/Substitution.lean` | 93 | **`ABDY.substitutionSimulation`**, **`ABDY.substitution`**: the one stage that carries the composed system to `hybrid` — each round's graded-agreement instance replaced by that round's specification, the family substitution under the four congruences. The mirror of `AFW/Substitution.lean`, which takes three stages. |

**`ABA/AFW/`** — AFW25's protocol as it runs, its three composed systems, the substitution to
`hybrid`, and the simulation into the composition.

| file | lines | what it is |
|---|---|---|
| `AFW/System.lean` | 1045 | **The gather-based protocol as it runs**: the implementation at AFW25's two-gather construction — the tagged message type collapsing a round's `4n + 2` network states into one sent-set family, the process-major round variables, the adversary's ghost of the two cores and the bound bit, and the 31 round transitions. |
| `AFW/Composition.lean` | 404 | **`AFW.composed`** and the two systems above it, `AFW.composedOverBroadcastSpecification` and `AFW.composedOverGatherSpecifications`: the three round families `roundFamilyOverBracha`, `roundFamilyOverBroadcastSpecification` and `roundFamilyOverGatherSpecifications` under the composed system's pipeline, with the lemmas that read a transition of the composite off its label and the builders that assemble one out of transitions of the components. |
| `AFW/RoundProjection.lean` | 543 | `AFW.roundProjection`, the projection that computes a composed state from the implementation, and the relation `AFW.ProtocolRelation` it carries. |
| `AFW/RoundProjectionStep.lean` | 40 | The module that imports the fifteen files of `RoundProjectionStep/`. |
| `AFW/SimulationOfEachTransition.lean` | 1156 | Each transition of the gather-based implementation matched by one event of `AFW.composed`: the readers that identify a transition off its label, the builders of a transition of one gather instance and of one round, corruption read through the projection, and one matching per label class. |
| `AFW/Simulation.lean` | 990 | **`AFW.protocolSimulation`**, **`AFW.protocol_composed`**: the matching label class by label class, and the gather-based protocol carried into `AFW.composed` along a relation that computes the composed state from the implementation, the ghost included. Two axiom checks. |
| `AFW/Substitution.lean` | 256 | **`AFW.substitutionSimulation`**, **`AFW.substitution`**: the three stages `AFW.composed ⊑ AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid`, each one family substitution under the four congruences, replacing Bracha's broadcast by the broadcast specification, then the gather instances by the gather specifications, then the rounds by the round specifications. One axiom check. |

**`ABA/AFW/RoundProjectionStep/`** — the projection of the composed round after one transition
of the gather-based implementation, one file per class of transitions.

| file | lines | what it is |
|---|---|---|
| `AFW/RoundProjectionStep/ProtocolRelationConjuncts.lean` | 54 | `boundInvariant_writeGhost`: the conjunct of `AFW.ProtocolRelation` that no lemma on a write elsewhere supplies, carried across a transition that writes the ghost. |
| `AFW/RoundProjectionStep/ProjectionAfterOneWrite.lean` | 510 | `roundProjection_write` and `roundProjection_writeNoSent`, the write to the round variables and the tagged send every transition performs, read through the projection, with the sent algebra and the readers of the projection after the write the transition classes run on. |
| `AFW/RoundProjectionStep/BroadcastReturn.lean` | 387 | `roundProjection_firstGatherInputBroadcastReturn` and its three companions: the projection after a broadcast instance of either gather returns to the acting process, which files what it returned in that process's gather variables. |
| `AFW/RoundProjectionStep/BroadcastSend.lean` | 501 | `roundProjection_firstGatherInputBroadcastSend` and its three companions: the projection after a Bracha send in one broadcast instance of either gather. |
| `AFW/RoundProjectionStep/ByzantineInjection.lean` | 412 | `roundProjection_byzantineFirstGather` and its five companions: the projection after the adversary multicasts on behalf of a corrupted sender, a transition that moves no variables. |
| `AFW/RoundProjectionStep/Delivery.lean` | 425 | `roundProjection_deliverFirstGather` and its five companions: the projection after a delivery, which moves the instance the message's tag names and nothing else. |
| `AFW/RoundProjectionStep/FirstGatherReturn.lean` | 158 | `roundProjection_firstGatherReturn`: the projection after the first gather returns to the acting process, which records the candidate and whose ghost write is that gather's core beside the round's bound bit. |
| `AFW/RoundProjectionStep/GatherSend.lean` | 214 | `roundProjection_firstGatherSend` and `roundProjection_secondGatherSend`: the projection after a gather's `ECHO` or `VOTE`. |
| `AFW/RoundProjectionStep/GatherAndBroadcastTransitions.lean` | 654 | `roundProjection_firstGatherEcho` and its thirteen companions: the projection after each `ECHO`, `VOTE` and `BIND` transition of the two gathers and of their four broadcast families. |
| `AFW/RoundProjectionStep/GradedAgreementCall.lean` | 118 | `roundProjection_callG` and `roundProjection_gbcaCallLoop`: the projection after the graded-agreement call, which records the round's input on its first gather, and after a call against variables that already hold a call. |
| `AFW/RoundProjectionStep/GradedReturn.lean` | 97 | `roundProjection_retG`: the projection after the round returns the graded outcome on record to the round loop. |
| `AFW/RoundProjectionStep/OtherRoundsUnchanged.lean` | 131 | `roundProjection_otherTransition` and its three companions: the rounds a transition does not name read exactly as the transition found them, and `toRoundFamily` and its two companions state that as a one-point update of the family of rounds. |
| `AFW/RoundProjectionStep/InputBroadcastCall.lean` | 247 | `roundProjection_firstGatherInputBroadcastCall` and its companion at the second gather: the projection after the acting process calls the instance broadcasting its input, which records the payload and multicasts its `⟨INIT, ·⟩`. |
| `AFW/RoundProjectionStep/SecondGatherCall.lean` | 106 | `roundProjection_secondGatherCall`: the projection after the acting process calls the second gather with the candidate on record, which that gather records. |
| `AFW/RoundProjectionStep/SecondGatherReturn.lean` | 134 | `roundProjection_secondGatherReturn`: the projection after the second gather returns to the acting process, which records the graded outcome and whose ghost write is that gather's core. |

**`ABA/`** — the headlines.

| file | lines | what it is |
|---|---|---|
| `Results.lean` | 322 | The deliverables of both chains, gathered so every citable statement is in one file. Seventeen `#guard_msgs` axiom checks. |

**`ABA/GhostRemoval/`** — the ghost-free system of each protocol, and the removal that
reaches it.

| file | lines | what it is |
|---|---|---|
| `GhostRemoval/GhostFreeSystem.lean` | 417 | **The ghost-free system** `Implementation.systemGhostFree`: `Implementation/System.lean` over a one-element ghost, with its returns free to announce any bit, and `Implementation.system_ghostRemoval`, the two systems' equality of achievable trace distributions, by an auxiliary-variable removal of the network carried through the pipeline. |
| `GhostRemoval/ImplementationByABDY.lean` | 103 | **`ABDY.ghostFreeProtocol`** and **`ABDY.protocol_ghostRemoval`**: the protocol with the adversary's bound-bit ghost dropped, and the headlines re-derived at it — `ghostFreeProtocol_composed`, `ghostFreeProtocol_refines`, `ghostFreeProtocol_safe`, `ghostFreeProtocol_traces`. Three axiom checks. |
| `GhostRemoval/ImplementationByAFW.lean` | 114 | **`AFW.ghostFreeProtocol`** and **`AFW.protocol_ghostRemoval`**: the gather-based protocol with the adversary's ghost of the two cores and the bound bit dropped, and the headlines re-derived at it — `ghostFreeProtocol_composed`, `ghostFreeProtocol_refines`, `ghostFreeProtocol_safe`, `ghostFreeProtocol_traces`. Five axiom checks. |

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
the three levels, four files each: the components and their alphabet, the composition
they are assembled into, the cases of a transition of the composition, read back into
the transitions of its components, and the algorithm that reads a transition of the composition
off its label; `GBCA/AFW/AlgorithmOverGatherSpecifications.lean` is the algorithm the counting
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
of the gather-based stack — including the counting argument behind the gather
specification's core; `../NOTES-Fidelity.md` is the encoding against
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
  state that owns the corrupted set, so `ABDY.protocol_safe` and `ABDY.protocol_traces`
  need no hypothesis on the trace.
- **By-type finiteness of the environment coordinates** (not pursued): the process types enforce
  finitely many variables by construction — the finite map of round variables, one round counter —
  where the network's round-indexed sent sets, the coin family, and the composed system's instance
  family are `ℕ`-indexed types whose reachable states have finite support. The by-type form is
  available throughout, by finite maps at the sent sets and a finitely-supported family combinator
  in `Framework/`. The finite-program principle does not ask for it: the network is the adversary,
  and the coin and the instance family are specifications.
