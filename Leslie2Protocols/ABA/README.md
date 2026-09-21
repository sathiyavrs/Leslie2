# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary
agreement, following the "Verifying ABA with Leslie" blueprint. The headlines of the
protocol chain are in `Results.lean` — `ABDY.main`, `ABDY.refines`, `ABDY.chainSim`,
`ABDY.protocol_safe`, `ABDY.protocol_traces`, `ABDY.composed_safe`, and the shared
`hybrid_spec` — and those of the gather-based chain in
`ImplementationByAFW/Simulation.lean` — `AFW.main`, `AFW.refines`, `AFW.chainSim`,
`AFW.protocol_composed` — beside the composed-level `AFW.composed_refines`,
`AFW.composed_safe`, `AFW.chainSimComposed` in `ImplementationByAFW/CompositionChain.lean`
and `GBCA.gatherRoundRefines` in `GBCA/AFW/Binding.lean`, all axiom-clean and guarded.
Each chain carries two headlines about its ghost-free reading, in
`GhostErasure/ImplementationByABDY.lean` and `GhostErasure/ImplementationByAFW.lean`:
`protocol_erasure`, the equality of achievable trace distributions between the protocol
and that reading, and `protocol₀_safe`, Validity and Agreement at it. The two sub-protocol
interfaces carry headlines of their own: `GBCA.specInst_binding` in
`GBCA/SpecificationSafety.lean`, with its four implementation readings
`GBCA.ByABDY.implInst_binding` in `GBCA/ABDY/RefinesSpecification.lean` and
`GBCA.roundOverGatherSpecifications_binding`,
`GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding` in
`GBCA/AFW/Binding.lean`; and `Gather.specInst_core` in
`Gather/CommonCoreAtSpecification.lean`, with the two implementation readings
`Gather.instanceOverBroadcastSpecification_core` in `Gather/RefinesSpecification.lean` and
`Gather.instanceOverBracha_core` in `Gather/BroadcastSubstitution.lean`.

The architecture in two lines, all of it in the protocol's own coordinates:

```
ABDY.protocol  ⊑  ABDY.composed                                                                                      ⊑  hybrid  ⊑  ABA.spec
 AFW.protocol  ⊑   AFW.composed  ⊑  AFW.composedOverBroadcastSpecification  ⊑  AFW.composedOverGatherSpecifications  ⊑  hybrid  ⊑  ABA.spec
```

One GBCA specification, two verified implementations, each carried from the protocol
as it runs. The first line carries the direct implementation (ABDY22's Algorithm 6,
D18), the second the gather-based one (AFW25's two-gather construction, D24), and the
two chains share every link from `hybrid` up. Every system above a protocol is a
composition of components, down to the programs that run it. On the first line a round
is the `n` stage programs beside the round's network. On the second a round is `n`
programs beside the network of the graded-agreement layer, in parallel with two gather
instances, and a gather instance is `n` programs beside the gather network, in parallel
with `2n` reliable-broadcast instances, each of them `n` programs beside the instance's
network. The three inner links of the second line each replace one tier of those
components by the tier above it.

A system below that meeting point belongs to one implementation or the other and is
named for its source: `ABDY`, after Abraham, Ben-David and Yandamuri, and `AFW`, after
Attiya, Flam and Welch. Across the two namespaces a name means the same thing —
`AFW.composed` is to the gather-based implementation what `ABDY.composed` is to the
ABDY22's — and `hybrid` and `ABA.spec`, which the chains share, are named in neither.
The rest of the gather-based chain sits in `AFW` as well: its headlines are `AFW.main`
and `AFW.refines`, where ABDY22's are `ABDY.main` and `ABDY.refines`. A `G` elsewhere in the
development is graded agreement — `callG`, `retG`, `GBCANetwork`, `GNetState` — and never the
chain.

Both flat readings are one construction. What a protocol reading fixes — the round
loop, the DECIDED sets, the coin handshake, corruption, the network adversary and
the composition pipeline — is settled by the round interface and the specification,
so `Implementation/System.lean` writes it once, parametric in the stage message type, the
per-process per-round stage record, the stage-side rows, and a per-round ghost record
of the network adversary, updated on every row and read as the guard of the two
graded-agreement return rows (D30). `ImplementationByABDY/System.lean` supplies ABDY22's;
`ImplementationByAFW/System.lean` supplies the gather-based one.

- `ABDY.protocol` — ABDY22's protocol as it runs: `n` programs beside the network
  adversary, which owns the message sets and the corrupted set, and the coin oracle,
  the only component whose transitions are not Dirac. A program reads its own replacement
  flag and nothing else about corruption: not the corrupted set, not the budget, not
  another process's status. A corruption replaces the program of the process it names
  (D23). A program holds its round loop beside
  its stage-side record — the stage record of every round the process has touched, in a
  finite map — and terminates once its own return has fired and `2f + 1` DECIDED receipts
  are on record (D22).
- `ABDY.composed` — the same protocol read as a composition of components: the round
  instances, the `n` round loops, the ABA-side network holding the DECIDED sets, and the
  coin oracle. `ABDY.protocolSim` carries `ABDY.protocol` into it along the Dirac lift of
  `ABDY.ProtocolRel`, and `ABDY.protocol_composed` is the inclusion it yields. The relation
  pins every composed coordinate against the protocol state: the entry of process `j` in the
  instance of round `r` is the stage record of round `r` that `j` holds (D22). What makes
  the inclusion one-directional is on the composed side. A round instance has a row for the
  Byzantine graded-agreement rows and no program of the protocol has one (D11), and the instance's
  stage rules carry no termination guard, so the instance answers a send or a delivery at a
  process the protocol has terminated. This is where the chain passes from implementation to
  specification.
- `hybrid` — each round's instance replaced by the graded agreement specification
  (`ABDY.substSim`), the other three components untouched. This is what the core simulation runs on.
- `ABA.spec` — the single-automaton reading of agreement, reached by `coreSim`.

Components talk only through synchronized labels, and no component reads another's state.
Why the cuts sit there, and what they buy, is `../DESIGN-Composition.md`.

## Ghost outputs

Two return labels announce a value that no program computes. A graded-agreement return
`retG r id out β` names the round's bound bit `β` beside the graded outcome, and a gather
return `ret id g C` names the instance's common core beside the map (D29). Each value is
state of the specification, written once by an internal rule. The implementations hold the
same value as ghost state, in each case at the component whose own state determines it. A
gather instance's core is a field of the gather network, computed by `Gather.coreOf` from
that network's sent sets and corrupted set alone. ABDY22's round holds the bound bit as a
field of the round's network state; the gather-based round gives it a component of its
own, the network of the graded-agreement layer, which carries no messages and holds the
bit alone. In the flat readings both belong to the network adversary, which holds a ghost
record per round (D30). No program's record carries either and no program's row reads one.
The two graded-agreement return rows of the network do read the round's record, and what
they read from it is the value the label announces, never whether the row fires: the read
admits a bit at every state (`ghostOut_total` in `GhostErasure/GhostFreeSystem.lean`). The
announcement therefore leaves every execution of the protocol as it is.

What a program does hold of a sub-protocol's answer is its own record of what the
instances have returned to it: the stores `Gather.ProcRec.delivIn` and `delivBind`,
written on the broadcast return events. Four rows of a gather program read them —
`sndEcho`, `sndVote`, `bindCall` and `ret` — so they are state a guard consults and not
ghost state.

For the bound bit that inertness is a theorem. `GhostErasure/GhostFreeSystem.lean` erases
the adversary's ghost record onto the ghost-free reading `Implementation.systemGhostFree`, whose
returns announce any bit, and `ABDY.protocol_erasure` and `AFW.protocol_erasure` are the
resulting equalities of achievable trace distributions. No map on labels appears in either
statement: `Label.retG` lies in `Label.hiddenAPI`, so the announced bit is silent at protocol
level and the final hiding frame discharges the label identification the erasure runs on.

What the announcement buys is binding as a property of a single trace, at the instance
level. Every round-`r` return of a trace of `GBCA.specInst` names one bit, and every one
of them that hands out a value hands out that bit (`GBCA.BindingTrace`,
`GBCA.specInst_binding`). Every return of a trace of `Gather.specInst` names one payload
set, of at least `n − f` entries and below the returned map (`Gather.CoreTrace`,
`Gather.specInst_core`). Both predicates are read off labels alone, so a
trace-distribution inclusion transports them. `GBCA.ByABDY.implInst_binding`,
`GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding`
and `GBCA.roundOverBracha_binding` are binding at the two verified graded-agreement
implementations and at the two tiers between them, along their own refinements, and
`Gather.instanceOverBroadcastSpecification_core` and `Gather.instanceOverBracha_core` are
the two gather implementations' readings along theirs.

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
another, and may return either bit at any time (D23). The `f + 1` `SuppOK` support counts
are the invariant machinery that makes this provable, not the predicate itself. Safety
only — no termination, liveness, unpredictability or fairness. The protocol's `terminate`
rule is a rule of the model, not a result: no theorem says when it fires, or that it ever
does.

## Deviations

Each departure from the source blueprint carries a label D1–D36, cited at the point where
it applies. The registry — every active label glossed, and the numbers the range skips —
is the Deviations paragraph of `../../blueprint/src/content.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its sources beyond that
registry.

## The files

Each file's module docstring is the account of record for it; the table says only what
the file is. The folders are given in import order, and no folder imports one below it:
`Vocabulary/` is written over by everything, `GhostErasure/` writes over everything.
Within a folder the files are alphabetical.


**`ABA/Vocabulary/`** — the records and alphabets every reading is written over.

| file | lines | what it is |
|---|---|---|
| `Vocabulary/Labels.lean` | 147 | The shared label alphabet `Label n`: the visible API, the hidden sub-protocol handshakes, `τ`. |
| `Vocabulary/Parameters.lean` | 143 | The parameters `P` — `n`, `f` with `n > 3f`, the reliable broadcast's `ECHO` quorum `echoQuorum`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Vocabulary/ProcessAndNetworkState.lean` | 429 | The two-part vocabulary of the gather-based development: network state (D5) beside `n` process local states, with the multicast/delivery/corrupt operations and the quorum-intersection kit, stated once and shared by the three sub-protocol encodings. |
| `Vocabulary/RoundLoop.lean` | 249 | **The ABA round loop**, per process and nothing else: the phase machine, the control record, the round-loop record. |

**`ABA/Specifications/`** — the specification all safety is measured against, and the
coin the protocol calls.

| file | lines | what it is |
|---|---|---|
| `Specifications/ABA.lean` | 251 | **The top-level ABA specification**, the system all safety is measured against. Eight rules over `SpecState`, whose control mode carries the flip (D21) and two of which are the corrupted interface (D23). The decision is guarded by the `f + 1` support guard `SuppOK` alone (D13). |
| `Specifications/ABASafety.lean` | 889 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `Specifications/WCC.lean` | 259 | The weak common coin specification, per round, and the coin value domain `TVal`. The call carries three rows: an unguarded loop that records nothing, one that records a caller, and one that records the caller whose access carries the count above `f` and draws the coin in the same step (D31). Held at specification level by design. |

**`ABA/Implementation/`** — the shape of a protocol as it runs, written once and
parametric in the graded-agreement implementation: the process programs, the network
adversary, the adversary's ghost record, and the composition of the three beside the coin
oracle.

| file | lines | what it is |
|---|---|---|
| `Implementation/Alphabet.lean` | 209 | The rendezvous alphabet `ExtendedLabel n M` a flat reading speaks, parametric in the stage message type, with the label pullback the coin oracle is read along. |
| `Implementation/System.lean` | 1540 | **The flat reading of a protocol**, parametric in the graded-agreement implementation: the shared rows of a program and of the network adversary, the adversary's per-round ghost record with its update and its output (D30), the pipeline that composes them beside the coin oracle, and the inversion lemmas that read a row off its label. |

**`ABA/ReliableBroadcast/`** — the reliable-broadcast specification and Bracha's
implementation of it.

| file | lines | what it is |
|---|---|---|
| `ReliableBroadcast/BrachaComposition.lean` | 956 | **The Bracha instance, composed**: `BRB.brachaInstance`, the `n` per-process programs beside the instance's network with the instance's own events hidden, and the row characterisation `brachaInstance_step_iff_row` that reads a transition off its label. |
| `ReliableBroadcast/BrachaImplementation.lean` | 149 | `BRB.BrachaStep`, the rows of the composed instance: Bracha's three message levels in the form of AFW25's Algorithm 1 (D34) over the two-part state. |
| `ReliableBroadcast/BrachaRefinesSpecification.lean` | 1072 | `brbRefines`: the Bracha instance refines TS 6, the committed value certified by an ECHO receipt quorum, the commit fired on demand. Carries the relation `BRB.InstRel`, which the gather substitution lifts, and the instance invariant `BRB.Inv`, which the flat link carries. |
| `ReliableBroadcast/Specification.lean` | 160 | The reliable-broadcast specification, per leader (blueprint TS 6, safety-only): the input/committed-value split with the guarded commit (D27). |

**`ABA/Gather/`** — gather over reliable broadcast.

| file | lines | what it is |
|---|---|---|
| `Gather/BroadcastSubstitution.lean` | 134 | `gatherLow`: the broadcast substitution inside gather, per coordinate, carried through the composition by the congruences. |
| `Gather/CommonCoreAtSpecification.lean` | 148 | `CoreTrace`, the common core read off a trace, and `specInst_core` at the specification. |
| `Gather/CommonCoreCounting.lean` | 1483 | The invariant of the gather-over-BRB instance and the counting argument for its core: `coreOf` has `n − f` committed entries and lies below the committed `BIND` payload of every process outside `F`, with the `f + 1` freeze certificate the specification's bind guard consumes. |
| `Gather/Composition.lean` | 1518 | **The gather instance, composed**: `n` gather programs beside the gather network, in parallel with `2n` composed broadcast instances — `Gather.instanceOverBroadcastSpecification` over the broadcast specifications and `Gather.instanceOverBracha` over Bracha's — read back over the gather alphabet extended by the call loop. |
| `Gather/MessagesAndCommonCore.lean` | 173 | The records a gather instance is written over — the `ECHO`/`VOTE` messages and the per-process record — and the core `coreOf` of a gather network state, with the incidence lemmas the counting argument sums. |
| `Gather/RefinesSpecification.lean` | 980 | `gatherCore`: the gather-over-BRB instance refines TS 4. The return run commits the entries it reads, freezes the core at `coreOf` of the network state, and returns, in one weak transition. |
| `Gather/StepOverBracha.lean` | 534 | `Gather.StepOverBracha`, the same table with each broadcast coordinate a composed Bracha instance, whose own rows a gather row carries as a hypothesis, with the row characterisation `instanceOverBracha_step_iff_row`. |
| `Gather/StepOverBroadcastSpecification.lean` | 623 | `Gather.StepOverBroadcastSpecification`, the rule table of the gather instance over `2n` BRB specification coordinates (blueprint Algorithm 4, the binding form of AFW25's Algorithm 5), stated over the composition's state, with the row characterisation `instanceOverBroadcastSpecification_step_iff_row`. |
| `Gather/Specification.lean` | 215 | The gather specification (blueprint TS 4): call/commit split (D26) and the write-once core the return labels announce (D29). |

**`ABA/GBCA/`** — the graded-agreement specification, and the binding it carries.

| file | lines | what it is |
|---|---|---|
| `GBCA/Specification.lean` | 292 | The graded binding crusader agreement specification, per round. Binding is negative, and every return announces the round's bound bit (D19, D29). |
| `GBCA/SpecificationSafety.lean` | 875 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. `specInst_binding` reads binding off a trace. |

**`ABA/GBCA/ABDY/`** — ABDY22's implementation of that specification, and its refinement.

| file | lines | what it is |
|---|---|---|
| `GBCA/ABDY/Implementation.lean` | 876 | **The GBCA implementation**, ABDY22's Algorithm 6 in full (D18). Its state is the stage records beside the round's network state, which holds the round's bound bit (D29). |
| `GBCA/ABDY/RefinesSpecification.lean` | 2013 | The per-instance refinement `implRefines`, by exclude-on-demand: `excluded` carried as a receipt-pattern certificate; its soundness inclusion `implInst_refines` with the binding it carries, `implInst_binding`; and the broadcast compatibility of the relation with the `fail` act (`instRel_corrupt`), which the family lifting consumes. Two axiom checks. |

**`ABA/Composition/`** — the components the composed systems are built from, the composed
reading over them, and the hybrid.

| file | lines | what it is |
|---|---|---|
| `Composition/ABAState.lean` | 380 | The ABA-side state as one object: the round-loop records beside the DECIDED network, with the accessors the invariant is stated in. |
| `Composition/Components.lean` | 849 | The extended alphabet `ExtendedLabel n` at ABDY22's messages, the coin oracle read along its label pullback, the round loop of one process, and the ABA-side network — the pieces the two compositions are built from. |
| `Composition/GBCAInstanceByABDY.lean` | 1659 | **The round's graded-agreement instance** and the licence to replace it, `subSim`. |
| `Composition/HybridAndSubstitution.lean` | 699 | **`ABDY.composed`**, **`ABDY.substSim`**: the same protocol read as four components, one round instance per round retained at every moment, and that graded-agreement component then replaced by its specification under the four congruences. |

**`ABA/GBCA/AFW/`** — the two-gather round and the three tiers that carry it.

| file | lines | what it is |
|---|---|---|
| `GBCA/AFW/Binding.lean` | 301 | Binding of the round over the family alphabet: `BindingTraceN` and `specificationOverRoundAlphabet_binding`, the round composite `gatherImplRefines` and `gatherRoundRefines`, and the binding each tier carries — `GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding`. Six axiom checks. |
| `GBCA/AFW/Composition.lean` | 1155 | **The graded-agreement round, composed**: `n` round programs beside the layer's network, in parallel with two gather instances — `GBCA.ByAFW.roundOverGatherSpecifications` over the gather specifications, `GBCA.ByAFW.roundOverBroadcastSpecification` over gather-over-BRB, and **`GBCA.ByAFW.roundOverBracha`, the gather-based GBCA implementation**, over gather-over-Bracha — read over the family alphabet `ExtendedLabel n`. |
| `GBCA/AFW/Counting.lean` | 362 | **The counting of the two-gather round** (AFW25 Algorithm 4 at R = 2, its approximate-agreement subroutine replaced by a local count, D24): the candidate/grade kit `cand` and `gradeOf`, the bound bit `boundOfCore` read off the first gather's core (D29), and the entry counts the refinement consumes. |
| `GBCA/AFW/GatherSubstitutions.lean` | 218 | `lowPairRefines` and `idealRefines`: the two gather substitutions inside the round, componentwise. |
| `GBCA/AFW/RefinesSpecification.lean` | 1437 | `pairRefines`: the two-gather round refines the GBCA specification. Exclusion and grade certified on the two frozen cores, the surviving bit pinned by the bound bit; exclude-on-demand. |
| `GBCA/AFW/StepOverGatherSpecifications.lean` | 449 | `GBCA.ByAFW.StepOverGatherSpecifications`, the rule table of the round over two gather specifications, stated over the round's state, with the row characterisation `roundOverGatherSpecifications_step_iff_row`. |

**`ABA/HybridRefinesSpecification/`** — the core simulation of the blueprint's §3,
`hybrid ⊑ ABA.spec`, and its witnesses.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/AbstractStatePreservation.lean` | 327 | `Abs` preservation for the stutter rows, and the assembly `Inv.step`. |
| `HybridRefinesSpecification/InvariantPreservation.lean` | 3907 | Step inversion for `hybrid`, then preservation of `Inv` across every row. The bulk of the proof text. |
| `HybridRefinesSpecification/NonVacuity.lean` | 648 | A concrete 20-step run of `hybrid P4` to a `retABA` decision, so the simulation about it is not vacuous. |
| `HybridRefinesSpecification/Relation.lean` | 683 | The core simulation's relation: the lazy abstract state `Abs` and the concrete invariant `Inv`. |
| `HybridRefinesSpecification/Simulation.lean` | 414 | **`coreSim`**: the simulation proof itself, one row per concrete step class. |
| `HybridRefinesSpecification/WeakTransitions.lean` | 53 | The abstract-state run kit: `SpecStep.decide` as a τ-run (`decide_step`), and a run closed by a visible step (`weakStep_of_run_then_step`). |

**`ABA/ImplementationByABDY/`** — ABDY22's protocol as it runs, and its link to the
composed reading.

| file | lines | what it is |
|---|---|---|
| `ImplementationByABDY/Simulation.lean` | 1095 | **`ABDY.protocolSim`**, **`ABDY.protocol_composed`**: the protocol carried into the composed reading along `ABDY.ProtocolRel`, whose five unguarded conjuncts determine the composed state. |
| `ImplementationByABDY/System.lean` | 824 | **ABDY22's protocol as it runs**, and the subject of the protocol chain: the flat reading at ABDY22's Algorithm 6 — its fourteen stage-side rows, the payload the call multicasts, the adversary's bound-bit ghost, and the inversions they answer. |

**`ABA/`** — the headlines.

| file | lines | what it is |
|---|---|---|
| `Results.lean` | 220 | The deliverables of the protocol chain, gathered so every citable statement is in one file. Thirteen `#guard_msgs` axiom checks. |

**`ABA/ImplementationByAFW/`** — the gather-based chain, and the protocol beneath it.

| file | lines | what it is |
|---|---|---|
| `ImplementationByAFW/CompositionChain.lean` | 398 | **The gather-based chain**: the sides `roundFamilyOverBracha`, `roundFamilyOverBroadcastSpecification` and `roundFamilyOverGatherSpecifications`, the three stages `AFW.composed ⊑ AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid`, and the composed-level headlines `AFW.composed_refines`, `AFW.composed_safe`, `AFW.chainSimComposed`. Four axiom checks. |
| `ImplementationByAFW/RoundProjection.lean` | 814 | `AFW.toRound`, the view that computes a composed state from a flat one, the relation `AFW.ProtocolRel` it carries, and the builders that assemble a transition of the composed reading. |
| `ImplementationByAFW/RoundProjectionStep.lean` | 2855 | The view of the composed round after one flat row: for each row of the flat reading, the round's view after it is the view before it with the composed round's own effect applied. |
| `ImplementationByAFW/Simulation.lean` | 2161 | **`AFW.protocolSim`**, **`AFW.main`**: the gather-based protocol carried into `AFW.composed` along a relation that computes the composed state from the flat one, the ghost record included, and the headlines `AFW.refines`, `AFW.main`, `AFW.chainSim` it yields. Five axiom checks. |
| `ImplementationByAFW/System.lean` | 829 | **The gather-based protocol as it runs**: the flat reading at AFW25's two-gather construction — the tagged message type collapsing a round's `4n + 2` network states into one sent-set family, the process-major stage record, the adversary's ghost record of the two cores and the bound bit, and the 23 stage-side rows. |

**`ABA/GhostErasure/`** — the ghost-free reading of each protocol, and the erasure that
reaches it.

| file | lines | what it is |
|---|---|---|
| `GhostErasure/GhostFreeSystem.lean` | 407 | **The ghost-free reading** `Implementation.systemGhostFree`: the reading of `Implementation/System.lean` over a one-element ghost record, with its returns free to announce any bit, and `Implementation.system_erasure`, the two readings' equality of achievable trace distributions, by a state erasure of the network adversary carried through the pipeline. |
| `GhostErasure/ImplementationByABDY.lean` | 100 | **`ABDY.protocol₀`** and **`ABDY.protocol_erasure`**: the protocol with the adversary's bound-bit record dropped, and the headlines re-derived at it — `protocol₀_composed`, `protocol₀_refines`, `protocol₀_safe`, `protocol₀_traces`. Three axiom checks. |
| `GhostErasure/ImplementationByAFW.lean` | 111 | **`AFW.protocol₀`** and **`AFW.protocol_erasure`**: the gather-based protocol with the adversary's record of the two cores and the bound bit dropped, and the headlines re-derived at it — `protocol₀_composed`, `protocol₀_refines`, `protocol₀_safe`, `protocol₀_traces`. Five axiom checks. |

The pieces both compositions are built from are in `Composition/Components.lean`, over the
alphabet of `Implementation/Alphabet.lean`. `ImplementationByABDY/System.lean` and
`Composition/GBCAInstanceByABDY.lean` each import it and neither imports the other, so the
two readings of the protocol are assembled independently over one set of components.
`Implementation/System.lean` sits beside `Composition/Components.lean` over the same
alphabet and imports no implementation, which is what lets both flat readings instantiate
it. The specification side — `Composition/GBCAInstanceByABDY.lean`,
`Composition/HybridAndSubstitution.lean` and the core simulation above them — never
imports `ImplementationByABDY/System.lean`; the protocol enters only at
`ImplementationByABDY/Simulation.lean`, which is where the two readings meet, and
`Results.lean` reaches it through that file.

The gather-based files form their own stack over `Vocabulary/ProcessAndNetworkState.lean`
and `GBCA/Specification.lean`, meeting the rest of the development in four places:
`GBCA/AFW/Counting.lean` reads the shared round alphabet, `GBCA/AFW/Composition.lean`
imports `Composition/GBCAInstanceByABDY.lean`, whose `GBCA.ByABDY.gbcaLabelMap` and
`GBCA.ByABDY.specificationOverRoundAlphabet` read the graded-agreement specification over
the family alphabet the round speaks, `ImplementationByAFW/System.lean` instantiates
`Implementation/System.lean`, and `ImplementationByAFW/CompositionChain.lean` imports
`Results.lean` for the shared links from `hybrid` up. Nothing in the protocol chain
imports a gather-based file, so either chain reads standalone.

## Suggested first read

`Vocabulary/Parameters.lean` → `Vocabulary/Labels.lean` → `Specifications/ABA.lean` → skim
`Specifications/ABASafety.lean`'s two trace predicates →
`HybridRefinesSpecification/Relation.lean`'s module docstring →
`ImplementationByABDY/System.lean`'s (the system the headlines are about) →
`Composition/HybridAndSubstitution.lean`'s (the system the core simulation starts from) →
`Results.lean`, whose docstring names the three steps of the chain and their files. Follow
it into the statements along `ABDY.protocolSim` → `ABDY.substSim` → `coreSim`, with
`Composition/ABAState.lean`'s `ABAState` beside the last. That is roughly 700 lines of
reading and gives the full statement-level picture; descend into the GBCA and
core-simulation proofs only when you want them.

For the two sub-protocol interfaces, read the specification beside the trace property it
carries: `GBCA/Specification.lean` with `GBCA/SpecificationSafety.lean`'s
`specInst_binding`, and `Gather/Specification.lean` with
`Gather/CommonCoreAtSpecification.lean`'s `specInst_core`.

For the gather-based chain, by module docstring:
`ReliableBroadcast/BrachaComposition.lean` → `Gather/Composition.lean` →
`GBCA/AFW/Composition.lean` → `GBCA/AFW/StepOverGatherSpecifications.lean` →
`ImplementationByAFW/CompositionChain.lean` → `ImplementationByAFW/Simulation.lean`. The
first three give the components of one level each, the alphabet they speak and the row
characterisation that reads a transition of the composition off its label;
`GBCA/AFW/StepOverGatherSpecifications.lean` is the row table the counting refinement runs
on; `ImplementationByAFW/CompositionChain.lean` is the assembly at the protocol shape and
`ImplementationByAFW/Simulation.lean` the link to `ImplementationByAFW/System.lean`, the
system that runs. The two counting arguments are `Gather/CommonCoreCounting.lean`, read
against `Gather/Specification.lean` alone, and `GBCA/AFW/Counting.lean`. Each refinement
rests on the row characterisation of the composition it is about, so it is readable
against the file that states those rows.

## Where else to look

`../README.md` maps the library and its shared framework. `../DESIGN-Composition.md` is why
the chains are cut where they are; `../DESIGN-CoreSim.md` and `../DESIGN-GBCASim.md` are the
narrative accounts of the two large protocol-chain proofs, and `../DESIGN-GatherTiers.md`
of the gather-based stack — including the counting argument behind the gather
specification's core; `../NOTES-Fidelity.md` is the encoding against
its sources and `../NOTES-Liveness-Roadmap.md` what termination would take. The prose
account is the ABA chapter of `../../blueprint/src/`, in two editions over one set of
statements: the default one (`content.tex`, each object and result stated against its Lean
declaration) and the full one (`content-full.tex`, adding the rule inventories, the
pseudocode and the proof bodies).

## Future work

- **Achievability theorem**: one explicit scheduler taking `protocol P4` to a two-return
  decision trace `t`, with `∃ D ∈ achievableTraceDists (protocol P4), D t ≠ 0` — the
  machine-checked non-vacuity for `ABDY.main`'s own system, exercising Agreement with two
  returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `ImplementationByABDY/System.lean` the budget is a component guard on the one local
  state that owns the corrupted set, so `ABDY.protocol_safe` and `ABDY.protocol_traces`
  need no hypothesis on the trace.
- **By-type finiteness of the environment coordinates** (not pursued): the process types
  enforce finitely many variables by construction — the finite map of stage records, one
  round counter — where the network's round-indexed sent sets, the coin family, and the
  composed reading's instance family are `ℕ`-indexed types whose reachable states have
  finite support. The by-type form is available throughout, by finite maps at the sent
  sets and a finitely-supported family combinator in `Framework/`. The finite-program
  principle does not ask for it: the network is the adversary, the coin an assumed oracle,
  and the instance family a specification-side reading.
