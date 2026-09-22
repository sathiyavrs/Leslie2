# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary agreement,
following the "Verifying ABA with Leslie" blueprint. The headlines of both chains are in
`Results.lean` — `ABDY.main`, `ABDY.refines`, `ABDY.chainSimulation`, `ABDY.protocol_safe`,
`ABDY.protocol_traces`, `ABDY.composed_safe` for the protocol chain, and `AFW.main`,
`AFW.refines`, `AFW.chainSimulation`, `AFW.composed_refines`, `AFW.composed_safe`,
`AFW.chainSimulationOfComposed` for the gather-based one — beside the shared `hybrid_spec` in
`HybridRefinesSpecification/Simulation.lean` and `GBCA.roundOverBracha_specificationTraces` in
`GBCA/AFW/Binding.lean`, all axiom-clean and guarded.
Each chain carries two headlines about its ghost-free system, in
`GhostErasure/ImplementationByABDY.lean` and `GhostErasure/ImplementationByAFW.lean`:
`protocol_erasure`, the equality of achievable trace distributions between the protocol and that
ghost-free system, and `protocol₀_safe`, Validity and Agreement at it. The two sub-protocol
interfaces carry headlines of their own: `GBCA.specInst_binding` in `GBCA/SpecificationSafety.lean`,
with its four implementations `GBCA.ByABDY.implementation_binding` in
`GBCA/ABDY/RefinesSpecification.lean` and `GBCA.roundOverGatherSpecifications_binding`,
`GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding` in
`GBCA/AFW/Binding.lean`; and `Gather.specInst_core` in `Gather/CommonCoreAtSpecification.lean`, with
the two implementations `Gather.instanceOverBroadcastSpecification_core` in
`Gather/RefinesSpecification.lean` and `Gather.instanceOverBracha_core` in
`Gather/BroadcastSubstitution.lean`.

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
three inner inclusions of the second line each replace one tier of those components by the tier
above it.

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
sets, the coin handshake, corruption, the network and the composition pipeline — is
settled by the round interface and the specification, so `Implementation/System.lean` writes it
once, parametric in the round message type, the per-process per-round record, the round rows, and a
per-round ghost record of the network, updated on every row and read as the guard of the
two graded-agreement return rows (D30). `ImplementationByABDY/System.lean` supplies ABDY22's;
`ImplementationByAFW/System.lean` supplies the gather-based one.

- `ABDY.protocol` — ABDY22's protocol as it runs: `n` programs beside the network, which
  owns the message sets and the corrupted set, and the coin oracle, the only component whose
  transitions are not Dirac. A program reads its own replacement flag and nothing else about
  corruption: not the corrupted set, not the budget, not another process's status. A corruption
  replaces the program of the process it names (D23). A program holds its round loop beside its
  round records — the round record of every round the process has touched, in a finite map — and
  terminates once its own return has fired and `2f + 1` DECIDED receipts are on record (D22).
- `ABDY.composed` — the same protocol read as a composition of components: the round instances, the
  `n` round loops, the ABA network holding the DECIDED sets, and the coin oracle. `ABDY.protocolSimulation`
  carries `ABDY.protocol` into it along the Dirac lift of `ABDY.ProtocolRelation`, and
  `ABDY.protocol_composed` is the inclusion it yields. The relation determines every composed coordinate
  from the protocol state: the entry of process `j` in the instance of round `r` is the round
  record of round `r` that `j` holds (D22). What makes the inclusion one-directional is on the
  composed system. A round instance has a row for the Byzantine graded-agreement rows and no program
  of the protocol has one (D11), and the instance's round rules carry no termination guard, so the
  instance answers a send or a delivery at a process the protocol has terminated. This is where the
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
written once by an internal rule. The implementations hold the same value as ghost state, in each
case at the component whose own state determines it. A gather instance's core is a field of the
gather network, computed by `Gather.coreOf` from that network's sent sets and corrupted set alone.
ABDY22's round holds the bound bit as a field of the round's network state; the gather-based round
gives it a component of its own, the round's network, which carries no messages and holds the bit
alone. In the implementations both belong to the network, which holds a ghost record per
round (D30). No program's record carries either and no program's row reads one. The two
graded-agreement return rows of the network do read the round's record, and what they read from it
is the value the label announces, never whether the row fires: the read admits a bit at every state
(`ghostOutput_total` in `GhostErasure/GhostFreeSystem.lean`). The announcement therefore leaves every
execution of the protocol as it is.

What a program does hold of a sub-protocol's answer is its own record of what the instances have
returned to it: the fields `Gather.ProcessRecord.inputBroadcastReturned` and
`bindBroadcastReturned`, written on the broadcast return events. Four rows of a gather program read
them — `sendEcho`, `sendVote`, `bindCall` and `ret` — so they are state a guard consults and not
ghost state.

For the bound bit that inertness is a theorem. `GhostErasure/GhostFreeSystem.lean` erases
the adversary's ghost record onto the ghost-free system `Implementation.systemGhostFree`, whose
returns announce any bit, and `ABDY.protocol_erasure` and `AFW.protocol_erasure` are the
resulting equalities of achievable trace distributions. No map on labels appears in either
statement: `Label.retG` lies in `Label.hiddenAPI`, so the announced bit is silent at protocol
level and the final hiding frame discharges the label identification the erasure runs on.

What the announcement buys is binding as a property of a single trace, at the instance level. Every
round-`r` return of a trace of `GBCA.specInst` names one bit, and every one of them that hands out a
value hands out that bit (`GBCA.BindingTrace`, `GBCA.specInst_binding`). Every return of a trace of
`Gather.specInst` names one payload set, of at least `n − f` entries and below the returned map
(`Gather.CoreTrace`, `Gather.specInst_core`). Both predicates are read off labels alone, so a
trace-distribution inclusion transports them. `GBCA.ByABDY.implementation_binding`,
`GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding` and
`GBCA.roundOverBracha_binding` are binding at the two verified graded-agreement implementations and
at the two tiers between them, along their own refinements, and
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
rule is a rule of the model, not a result: no theorem says when it fires, or that it ever
does.

## Deviations

Each departure from the source blueprint carries a label D1–D36, cited at the point where
it applies. The registry — every active label glossed, and the numbers the range skips —
is the Deviations paragraph of `../../blueprint/src/content.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its sources beyond that
registry.

## The files

Each file's module docstring is the account of record for it. The table gives one clause per
file: what it holds, and the declarations a reader looks for. The folders are given in import order, and no folder imports one below it:
`Vocabulary/` is written over by everything, `GhostErasure/` writes over everything.
Within a folder the files are alphabetical. Each file holds one object or one result together
with the lemmas that exist only to prove it, and Mathlib's `linter.style.longFile` caps a file
at 1500 lines, a file over the cap carrying an explicit `set_option linter.style.longFile`
raise.


**`ABA/Vocabulary/`** — the records and alphabets every implementation is written over.

| file | lines | what it is |
|---|---|---|
| `Vocabulary/Labels.lean` | 147 | The shared label alphabet `Label n`: the visible API, the hidden sub-protocol handshakes, `τ`. |
| `Vocabulary/Parameters.lean` | 144 | The parameters `P` — `n`, `f` with `n > 3f`, the reliable broadcast's `ECHO` quorum `echoReceiptQuorum`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Vocabulary/ProcessAndNetworkState.lean` | 435 | The two-part vocabulary of the gather-based development: network state (D5) beside `n` process local states, with the multicast/delivery/corrupt operations and the quorum-intersection lemmas, stated once and shared by the three sub-protocol encodings. |
| `Vocabulary/RoundLoop.lean` | 248 | **The ABA round loop**, per process and nothing else: the phase machine, the control record, the round-loop record. |

**`ABA/Specifications/`** — the specification all safety is measured against, and the
coin the protocol calls.

| file | lines | what it is |
|---|---|---|
| `Specifications/ABA.lean` | 250 | **The top-level ABA specification**, the system all safety is measured against. Eight rules over `SpecState`, whose control mode carries the flip (D21) and two of which are the corrupted interface (D23). The decision is guarded by the `f + 1` support guard `InputSupport` alone (D13). |
| `Specifications/ABASafety.lean` | 894 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `Specifications/WCC.lean` | 259 | The weak common coin specification, per round, and the coin value domain `CoinValue`. The call carries three rows: an unguarded loop that records nothing, one that records a caller, and one that records the caller whose access carries the count above `f` and draws the coin in the same step (D31). Held at specification level by design. |

**`ABA/Implementation/`** — the shape of a protocol as it runs, written once and
parametric in the graded-agreement implementation: the process programs, the network
adversary, the adversary's ghost record, the composition of the three beside the coin
oracle, and the lemmas that read a transition off its label.

| file | lines | what it is |
|---|---|---|
| `Implementation/Alphabet.lean` | 206 | The rendezvous alphabet `ExtendedLabel n M` the implementation speaks, parametric in the round message type, with the label pullback the coin oracle is read along. |
| `Implementation/CompositeTransitions.lean` | 228 | The transitions of the implementation, read off their labels: the pipeline `relabel ∘ abstract ∘ parallel ∘ parallel ∘ synchronisedProduct` unfolded to the rows of the process group, of the network and of the coin oracle, and the constraint a graded-agreement return places on the bound bit its label carries. |
| `Implementation/NetworkStateWritesAndErasures.lean` | 217 | The field algebra of the network's four writes: a round multicast, a DECIDED multicast, corruption and the ghost write, each read down to the fields of the state it delivers. With them the two erasures, `NetworkState.forgetGhost` to the state over the trivial ghost `Unit` and `forgetBound` to the label with the announced bound bit fixed at `false`. |
| `Implementation/StepInversion.lean` | 490 | The transitions of one program and of the network, read off their labels: the participant's row as its guards together with the Dirac it produces, the idle row of a non-participant as the identity, and the determinacy of both tables. |
| `Implementation/System.lean` | 687 | **The implementation of a protocol**, parametric in the graded-agreement implementation: the shared rows of a program and of the network, the adversary's per-round ghost record with its update and its output (D30), the pipeline that composes them beside the coin oracle, and `IsRoundRuleTable`, what an implementation states about its own rows. |

**`ABA/ReliableBroadcast/`** — the reliable-broadcast specification and Bracha's
implementation of it.

| file | lines | what it is |
|---|---|---|
| `ReliableBroadcast/BrachaComposition.lean` | 257 | **The Bracha instance, composed**: `BRB.brachaInstance`, the `n` per-process programs beside the instance's network with the instance's own events hidden, over the interface alphabet in which the call loop is a label of its own. |
| `ReliableBroadcast/BrachaCompositionStepInversion.lean` | 581 | The transitions of `BRB.brachaInstance` read off their labels: a step of the instance split into a hidden rendezvous and an interface label, a joint step read as the rows of the programs and the network, one program's row and the network's row per label class, the write each row makes on the composed state, and the row characterisation `brachaInstance_step_iff_row`. |
| `ReliableBroadcast/BrachaImplementation.lean` | 151 | `BRB.BrachaStep`, the rows of the composed instance `BRB.brachaInstance`: Bracha's three message levels in the form of AFW25's Algorithm 1 (D34) over the two-part state, one row per case of `brachaInstance_step_iff_row`. A relation on that state; the system is the composition of `ReliableBroadcast/BrachaComposition.lean`. |
| `ReliableBroadcast/BrachaRefinesSpecification.lean` | 1082 | `brachaRefinesSpecification`: the Bracha instance refines TS 6, the committed value certified by an ECHO receipt quorum, the commit fired on demand. Carries the relation `BRB.SpecificationRelation`, which the gather substitution lifts, and the instance invariant `BRB.Invariant`, which the simulation of the implementation into its composed system carries. |
| `ReliableBroadcast/BrachaSpecificationOverInstanceAlphabet.lean` | 218 | `BRB.specificationOverInstanceAlphabet`: the broadcast specification read along `BRB.specificationLabelMap`, which sends the call loop to the call it stands for; the determinacy of the composition's rules, and the sections along which a weak run of the specification is read back over the instance's interface. |
| `ReliableBroadcast/Specification.lean` | 160 | The reliable-broadcast specification, per leader (blueprint TS 6, safety-only): the input/committed-value split with the guarded commit (D27). |

**`ABA/Gather/`** — gather over reliable broadcast.

| file | lines | what it is |
|---|---|---|
| `Gather/BroadcastSubstitution.lean` | 150 | `broadcastSubstitution`: the broadcast substitution inside gather, per coordinate, carried through the composition by the congruences. |
| `Gather/CommonCoreAtSpecification.lean` | 148 | `CoreTrace`, the common core read off a trace, and `specInst_core` at the specification. |
| `Gather/CommonCoreCounting.lean` | 1520 | The invariant of the gather-over-BRB instance and the counting argument for its core: `coreOf` has `n − f` committed entries and lies below the committed `BIND` payload of every process outside `F`, with the `f + 1` certificate the specification's bind guard consumes. |
| `Gather/Composition.lean` | 753 | **The gather instance, composed**: `n` gather programs beside the gather network, in parallel with `2n` composed broadcast instances — `Gather.instanceOverBroadcastSpecification` over the broadcast specifications and `Gather.instanceOverBracha` over Bracha's — read back over the gather alphabet extended by the call loop. |
| `Gather/CompositionStepInversion.lean` | 656 | The transitions of `Gather.instanceOverBroadcasts` read off their labels: a step of the instance split into a hidden gather event and an interface label, a joint step read as the rows of the four factors, the pullbacks computed label by label, one gather program's row and the gather network's row per label class, and the write each row makes on the composed state. |
| `Gather/MessagesAndCommonCore.lean` | 174 | The records a gather instance is written over — the `ECHO`/`VOTE` messages and the per-process record — and the core `coreOf` of a gather network state, with the incidence lemmas the counting argument sums. |
| `Gather/RefinesSpecification.lean` | 1018 | `refinesSpecification`: the gather-over-BRB instance refines TS 4. The return run commits the entries it reads, writes the core at `coreOf` of the network state, and returns, in one weak transition. |
| `Gather/Specification.lean` | 215 | The gather specification (blueprint TS 4): call/commit split (D26) and the write-once core the return labels announce (D29). |
| `Gather/SpecificationOverInstanceAlphabet.lean` | 157 | `Gather.specificationOverInstanceAlphabet`: the gather specification read along `Gather.specificationLabelMap`, which sends the call loop to the call it stands for, with the sections along which a weak run of the specification is read back over the instance's interface. |
| `Gather/StepOverBracha.lean` | 589 | `Gather.StepOverBracha`, the rows of `Gather.instanceOverBracha` stated over the composition's state, one per case of `instanceOverBracha_step_iff_row`; a row that reaches a broadcast coordinate carries that Bracha instance's own row as a hypothesis. A relation on that state; the system is the composition of `Gather/Composition.lean`. |
| `Gather/StepOverBroadcastSpecification.lean` | 679 | `Gather.StepOverBroadcastSpecification`, the rows of `Gather.instanceOverBroadcastSpecification` (blueprint Algorithm 4, the binding form of AFW25's Algorithm 5) stated over the composition's state, one per case of `instanceOverBroadcastSpecification_step_iff_row`. A relation on that state; the system is the composition of `Gather/Composition.lean`. |

**`ABA/GBCA/`** — the graded-agreement specification, and the binding it carries.

| file | lines | what it is |
|---|---|---|
| `GBCA/Specification.lean` | 291 | The graded binding crusader agreement specification, per round. Binding is negative, and every return announces the round's bound bit (D19, D29). |
| `GBCA/SpecificationSafety.lean` | 874 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. `specInst_binding` reads binding off a trace. |

**`ABA/GBCA/ABDY/`** — ABDY22's implementation of that specification, and its refinement.

| file | lines | what it is |
|---|---|---|
| `GBCA/ABDY/ExclusionCertificate.lean` | 329 | The exclude certificates `EchoReceiptQuorum` (Case A), `VoteQuorumAgainst` (Case B) and their disjunction `ExclusionCertificate`: monotone receipt evidence that a bit can never gain grade-≥1 support. The derivation chains read a certificate off a return's own receipts. |
| `GBCA/ABDY/Implementation.lean` | 886 | **The GBCA implementation**, ABDY22's Algorithm 6 in full (D18). Its state is the round records beside the round's network state, which holds the round's bound bit (D29). |
| `GBCA/ABDY/Invariant.lean` | 807 | The inductive invariant `Invariant` of the implementation instance: the corruption budget, delivery soundness, protocol conformance and write-once recording of correct multicasts, participation, budget-robust input origin, and the `f + 1` genuine-holder support `InputSupport` (D15). `Invariant.initial` and `Invariant.step` hold it at the initial state and along every row. |
| `GBCA/ABDY/RefinesSpecification.lean` | 661 | The per-instance refinement `refinesSpecification`, by exclude-on-demand; its soundness inclusion `implementation_refines` with the binding it carries, `implementation_binding`; and the broadcast compatibility of the relation with the `fail` act (`specificationRelation_corrupt`), which the family lifting consumes. Two axiom checks. |
| `GBCA/ABDY/SpecificationRelation.lean` | 344 | The simulation relation `specificationRelation`: the specification's `call`, `ret` and `F` read off the implementation state, `excluded` and `grade` carried as receipt-pattern certificates, and the round's bound bit tied to `excluded`. The specification's guards and the two-step exclusion-then-return runs are derived from it. |

**`ABA/Composition/`** — the components the composed systems are built from, the composed
system over them, and the hybrid.

| file | lines | what it is |
|---|---|---|
| `Composition/ABAState.lean` | 384 | The ABA state as one object: the round-loop records beside the DECIDED network, with the accessors the invariant is stated in. |
| `Composition/Components.lean` | 847 | The extended alphabet `ExtendedLabel n` at ABDY22's messages, the coin oracle read along its label pullback, the round loop of one process, and the ABA network — the pieces the two compositions are built from. |
| `Composition/HybridAndSubstitution.lean` | 700 | **`ABDY.composed`**, **`ABDY.substitutionSimulation`**: the same protocol read as four components, one round instance per round retained at every moment, and that graded-agreement component then replaced by its specification under the four congruences. |
| `Composition/RoundFamilyOwnedLabels.lean` | 84 | The routing table of the round-indexed family, evaluated: `GBCA.ByABDY.roundOwnsLabel` and `GBCA.ByABDY.isFailLabel` at every label of the extended alphabet, which is what discharges the routing premises of the composed system by `simp`. |

**`ABA/Composition/GBCAInstanceByABDY/`** — the round's graded-agreement instance, and the licence
to replace it by the graded-agreement specification.

| file | lines | what it is |
|---|---|---|
| `Composition/GBCAInstanceByABDY/Instance.lean` | 648 | **The round's graded-agreement instance**: `n` corruption-blind local programs beside the round's own network, the instance-internal alphabet that carries their two rendezvous, the round-indexed family `gbcaInstanceFamily`, and the readers and builders of one instance transition. |
| `Composition/GBCAInstanceByABDY/ProjectsOntoImplementation.lean` | 245 | `composition_projects`: every transition of the round instance is a transition of the round's implementation at that same state, one step for one step, with no stuttering. One axiom check. |
| `Composition/GBCAInstanceByABDY/SpecificationOverRoundAlphabet.lean` | 184 | `GBCA.ByABDY.specificationOverRoundAlphabet`: the graded-agreement specification read along `GBCA.ByABDY.gbcaLabelMap`, which identifies the three Byzantine handshake rows and the call loop with the specification labels they stand for, with the sections along which a weak run of the specification is read back over the round's interface. |
| `Composition/GBCAInstanceByABDY/StepInversion.lean` | 507 | The transitions of the round instance read off their labels: one program's row and the network's row per label class, the round records beside the network state read as one implementation state, the two inversions of the composition, and the network's row off a round-tagged label. |
| `Composition/GBCAInstanceByABDY/Substitution.lean` | 127 | **`instanceSubstitution`**: the licence to replace the round instance by the graded-agreement specification, with the broadcast corruption act at the round's alphabet and the two premises the family lift consumes. One axiom check. |

**`ABA/GBCA/AFW/`** — the two-gather round and the three tiers that carry it.

| file | lines | what it is |
|---|---|---|
| `GBCA/AFW/Binding.lean` | 317 | Binding of the round over the family alphabet: `BindingTraceExtended` and `specificationOverRoundAlphabet_binding`, the round composite `roundOverBracha_refinesSpecification` and `roundOverBracha_specificationTraces`, and the binding each tier carries — `GBCA.roundOverGatherSpecifications_binding`, `GBCA.roundOverBroadcastSpecification_binding`, `GBCA.roundOverBracha_binding`. Six axiom checks. |
| `GBCA/AFW/Composition.lean` | 838 | **The graded-agreement round, composed**: `n` round programs beside the round's network, in parallel with two gather instances — `GBCA.ByAFW.roundOverGatherSpecifications` over the gather specifications, `GBCA.ByAFW.roundOverBroadcastSpecification` over gather-over-BRB, and **`GBCA.ByAFW.roundOverBracha`, the gather-based GBCA implementation**, over gather-over-Bracha — read over the family alphabet `ExtendedLabel n`. |
| `GBCA/AFW/CompositionStepInversion.lean` | 455 | The transitions of `GBCA.ByAFW.roundOverGathers` read off their labels: a step of the round split into a hidden event and a family label, a joint step read as the rows of the round's programs, the round's network and the two gather instances, and one graded-agreement program's row and the round's network's row per label class. |
| `GBCA/AFW/Counting.lean` | 368 | **The counting of the two-gather round** (AFW25 Algorithm 4 at R = 2, its approximate-agreement subroutine replaced by a local count, D24): the candidate and the grade, `candidate` and `gradeOf`, the bound bit `boundOfCore` read off the first gather's core (D29), and the entry counts the refinement consumes. |
| `GBCA/AFW/GatherSubstitutions.lean` | 242 | `broadcastSubstitution` and `gatherSubstitution`: the two gather substitutions inside the round, componentwise. |
| `GBCA/AFW/RefinesSpecification.lean` | 1498 | `refinesSpecification`: the two-gather round refines the GBCA specification. Exclusion and grade certified on the two recorded cores, the surviving bit fixed by the bound bit; exclude-on-demand. |
| `GBCA/AFW/StepOverGatherSpecifications.lean` | 527 | `GBCA.ByAFW.StepOverGatherSpecifications`, the rows of `GBCA.ByAFW.roundOverGatherSpecifications` stated over the round's state, one per case of `roundOverGatherSpecifications_step_iff_row`. A relation on that state; the system is the composition of `GBCA/AFW/Composition.lean`. |

**`ABA/HybridRefinesSpecification/`** — the core simulation of the blueprint's §3,
`hybrid ⊑ ABA.spec`, and its witnesses.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/AbstractStatePreservation.lean` | 323 | `AbstractState` preservation for the stutter rows, and the assembly `Invariant.step`. |
| `HybridRefinesSpecification/InvariantPreservation.lean` | 30 | The module that imports the eleven files of `InvariantPreservation/`. |
| `HybridRefinesSpecification/NonVacuity.lean` | 813 | A concrete 20-step run of `hybrid fourProcesses` to a `retABA` decision, so the simulation about it is not vacuous. |
| `HybridRefinesSpecification/Relation.lean` | 691 | The core simulation's relation: the lazy abstract state `AbstractState` and the concrete invariant `Invariant`. |
| `HybridRefinesSpecification/Simulation.lean` | 441 | **`hybridRefinesSpecification`**: the simulation proof itself, one row per concrete step class, and `hybrid_spec`, its soundness inclusion. One axiom check. |
| `HybridRefinesSpecification/WeakTransitions.lean` | 52 | The abstract-state run lemmas: `SpecStep.decide` as a τ-run (`decide_step`), and a run closed by a visible step (`weakStep_of_run_then_step`). |

**`ABA/HybridRefinesSpecification/InvariantPreservation/`** — step inversion for `hybrid`, and the
preservation of `Invariant` across the rows of each label class.

| file | lines | what it is |
|---|---|---|
| `HybridRefinesSpecification/InvariantPreservation/CallABA.lean` | 224 | `Invariant.step_callABA`: `Invariant` across a call of the ABA interface — a never-corrupted process's genuine external input, or the idle self-loop. |
| `HybridRefinesSpecification/InvariantPreservation/CallG.lean` | 505 | `Invariant.step_callG`: `Invariant` across a call of the graded-agreement specification, which touches `.call` at the GBCA instance and `.phase` at the core. |
| `HybridRefinesSpecification/InvariantPreservation/CallW.lean` | 465 | `Invariant.step_callW`: `Invariant` across a call of the coin, over the three rows of `WCC.step_callW_inversion` — the enabledness loop, the recording call, and the resolving call that writes the drawn outcome. |
| `HybridRefinesSpecification/InvariantPreservation/Fail.lean` | 221 | `Invariant.step_fail`: `Invariant` across a synchronised corruption of all three components, where `F` gains exactly the named process. |
| `HybridRefinesSpecification/InvariantPreservation/GBCATau.lean` | 343 | `Invariant.step_gbcaTau`: `Invariant` across `bindUnset`, the graded-agreement family's only genuine `τ`-step. |
| `HybridRefinesSpecification/InvariantPreservation/RetABA.lean` | 153 | `Invariant.step_retABA`: `Invariant` across a return of the ABA interface, which sets `returned` alone. |
| `HybridRefinesSpecification/InvariantPreservation/RetG.lean` | 943 | `Invariant.step_retG`: `Invariant` across a return of the graded-agreement specification, with the two round-chaining lemmas the proof runs on. |
| `HybridRefinesSpecification/InvariantPreservation/RetW.lean` | 457 | `Invariant.step_retW`: `Invariant` across a return of the coin, the row that closes a round and sends DECIDED on a grade-2. |
| `HybridRefinesSpecification/InvariantPreservation/RoundLoopTau.lean` | 344 | `Invariant.step_roundLoopTau`: `Invariant` across a core `τ` — DECIDED delivery, echo, or byzantine injection. |
| `HybridRefinesSpecification/InvariantPreservation/SpecificationStateCorruption.lean` | 51 | The four readings of corruption at a graded-agreement or coin specification state that the `fail` row consumes. |
| `HybridRefinesSpecification/InvariantPreservation/StepInversion.lean` | 564 | `hybrid_step_callABA`, `hybrid_step_retABA`, `hybrid_step_fail` and `hybrid_step_tau`: a transition of `hybrid` read back into the rows of its four components, with `corrupted_eq_false_iff`, the reading of a round loop's replacement flag on the corrupted set. |

**`ABA/ImplementationByABDY/`** — ABDY22's protocol as it runs, and its simulation into the composed
system.

| file | lines | what it is |
|---|---|---|
| `ImplementationByABDY/Simulation.lean` | 1068 | **`ABDY.protocolSimulation`**, **`ABDY.protocol_composed`**: the protocol carried into the composed system along `ABDY.ProtocolRelation`, whose five unguarded conjuncts determine the composed state. |
| `ImplementationByABDY/System.lean` | 849 | **ABDY22's protocol as it runs**, and the subject of the protocol chain: the implementation at ABDY22's Algorithm 6 — its fourteen round rows, the payload the call multicasts, the adversary's bound-bit ghost, and the inversions they answer. |

**`ABA/ImplementationByAFW/`** — the gather-based chain, and the protocol beneath it.

| file | lines | what it is |
|---|---|---|
| `ImplementationByAFW/CompositionChain.lean` | 382 | **The gather-based chain**: the families `roundFamilyOverBracha`, `roundFamilyOverBroadcastSpecification` and `roundFamilyOverGatherSpecifications`, and the three stages `AFW.composed ⊑ AFW.composedOverBroadcastSpecification ⊑ AFW.composedOverGatherSpecifications ⊑ hybrid`. One axiom check. |
| `ImplementationByAFW/RoundProjection.lean` | 876 | `AFW.roundProjection`, the view that computes a composed state from the implementation, the relation `AFW.ProtocolRelation` it carries, and the builders that assemble a transition of the composed system. |
| `ImplementationByAFW/RoundProjectionStep.lean` | 35 | The module that imports the ten files of `RoundProjectionStep/`. |
| `ImplementationByAFW/Simulation.lean` | 866 | **`AFW.protocolSimulation`**, **`AFW.protocol_composed`**: the matching label class by label class, and the gather-based protocol carried into `AFW.composed` along a relation that computes the composed state from the implementation, the ghost record included. Two axiom checks. |
| `ImplementationByAFW/SimulationRows.lean` | 1462 | Each row of the gather-based implementation answered by a run of `AFW.composed`: the readers that identify a row off its label, the builders of a transition of one gather instance and of one round, the broadcast invariant across a row, and the returned value read against the implementation's `2f + 1` `VOTE` receipt quorum. |
| `ImplementationByAFW/System.lean` | 921 | **The gather-based protocol as it runs**: the implementation at AFW25's two-gather construction — the tagged message type collapsing a round's `4n + 2` network states into one sent-set family, the process-major round record, the adversary's ghost record of the two cores and the bound bit, and the 23 round rows. |

**`ABA/ImplementationByAFW/RoundProjectionStep/`** — the view of the composed round after one row
of the gather-based implementation, one file per row class.

| file | lines | what it is |
|---|---|---|
| `ImplementationByAFW/RoundProjectionStep/BroadcastSend.lean` | 498 | `roundProjection_firstGatherInputBroadcastSend` and its three companions: the view after a Bracha send in one broadcast instance of either gather, which leaves the returned value where it stands. |
| `ImplementationByAFW/RoundProjectionStep/ByzantineInjection.lean` | 399 | `roundProjection_byzantineFirstGather` and its five companions: the view after the adversary multicasts on behalf of a corrupted sender, a row that moves no record. |
| `ImplementationByAFW/RoundProjectionStep/Delivery.lean` | 842 | `roundProjection_deliverFirstGather` and its nine companions: the view after a delivery, a broadcast delivery that completes a `2f + 1` `VOTE` quorum at the receiver being answered by the instance's delivery and then its return. |
| `ImplementationByAFW/RoundProjectionStep/GatherAndBroadcastRows.lean` | 587 | `roundProjection_firstGatherEcho` and its thirteen companions: the view after each `ECHO`, `VOTE` and `BIND` row of the two gathers and of their four broadcast families. |
| `ImplementationByAFW/RoundProjectionStep/GatherSend.lean` | 208 | `roundProjection_firstGatherSend` and `roundProjection_secondGatherSend`: the view after a gather's `ECHO` or `VOTE`. |
| `ImplementationByAFW/RoundProjectionStep/GradedAgreementCall.lean` | 165 | `roundProjection_callG` and `roundProjection_gbcaCallLoop`: the view after the fused graded-agreement call, and after a call against an already-called record. |
| `ImplementationByAFW/RoundProjectionStep/OtherRoundsUnchanged.lean` | 120 | `roundProjection_otherRow` and its three companions: the rounds a row does not name read exactly as the row found them, and `toRoundFamily` and its two companions state that as a one-point update of the family of rounds. |
| `ImplementationByAFW/RoundProjectionStep/ProtocolRelationClauses.lean` | 117 | `broadcastReturnsInvariant_of`, `broadcastReturnsInvariant_congr` and `boundInvariant_writeGhost`: the two conjuncts of `AFW.ProtocolRelation` that no frame lemma supplies. |
| `ImplementationByAFW/RoundProjectionStep/ReturnThenCall.lean` | 350 | `roundProjection_firstGatherReturn_secondGatherCall` and `roundProjection_secondGatherReturn_retG`: the two rows that two events of the composed round answer, through a named intermediate state. |
| `ImplementationByAFW/RoundProjectionStep/ViewAfterOneWrite.lean` | 603 | `roundProjection_write` and `roundProjection_writeNoSent`, the round-record write and the tagged send every row performs, read through the view, with the sent algebra and the readers of the written view the row classes run on. |

**`ABA/`** — the headlines.

| file | lines | what it is |
|---|---|---|
| `Results.lean` | 318 | The deliverables of both chains, gathered so every citable statement is in one file. Seventeen `#guard_msgs` axiom checks. |

**`ABA/GhostErasure/`** — the ghost-free system of each protocol, and the erasure that
reaches it.

| file | lines | what it is |
|---|---|---|
| `GhostErasure/GhostFreeSystem.lean` | 415 | **The ghost-free system** `Implementation.systemGhostFree`: `Implementation/System.lean` over a one-element ghost record, with its returns free to announce any bit, and `Implementation.system_erasure`, the two systems' equality of achievable trace distributions, by a state erasure of the network carried through the pipeline. |
| `GhostErasure/ImplementationByABDY.lean` | 104 | **`ABDY.protocol₀`** and **`ABDY.protocol_erasure`**: the protocol with the adversary's bound-bit record dropped, and the headlines re-derived at it — `protocol₀_composed`, `protocol₀_refines`, `protocol₀_safe`, `protocol₀_traces`. Three axiom checks. |
| `GhostErasure/ImplementationByAFW.lean` | 111 | **`AFW.protocol₀`** and **`AFW.protocol_erasure`**: the gather-based protocol with the adversary's record of the two cores and the bound bit dropped, and the headlines re-derived at it — `protocol₀_composed`, `protocol₀_refines`, `protocol₀_safe`, `protocol₀_traces`. Five axiom checks. |

The pieces both compositions are built from are in `Composition/Components.lean`, over the
alphabet of `Implementation/Alphabet.lean`. `ImplementationByABDY/System.lean` and
`Composition/GBCAInstanceByABDY/Instance.lean` each import it and neither imports the other, so the
two systems of the protocol are assembled independently over one set of components.
`Implementation/System.lean` sits beside `Composition/Components.lean` over the same
alphabet and imports no implementation, which is what lets both implementations instantiate
it. The specification family — `Composition/GBCAInstanceByABDY/`,
`Composition/HybridAndSubstitution.lean` and the core simulation above them — never
imports `ImplementationByABDY/System.lean`; the protocol enters only at
`ImplementationByABDY/Simulation.lean`, which is where the two systems meet, and
`Results.lean` reaches it through that file.

The gather-based files form their own stack over `Vocabulary/ProcessAndNetworkState.lean` and
`GBCA/Specification.lean`, meeting the rest of the development in four places:
`GBCA/AFW/Counting.lean` reads the shared round alphabet, `GBCA/AFW/Composition.lean` imports
`Composition/GBCAInstanceByABDY/Instance.lean` and `GBCA/AFW/RefinesSpecification.lean` imports
`Composition/GBCAInstanceByABDY/SpecificationOverRoundAlphabet.lean`, whose
`GBCA.ByABDY.gbcaLabelMap` and `GBCA.ByABDY.specificationOverRoundAlphabet` read the
graded-agreement specification over the family alphabet the round speaks, `ImplementationByAFW/System.lean` instantiates
`Implementation/System.lean`, and `ImplementationByAFW/CompositionChain.lean` imports
`Composition/HybridAndSubstitution.lean` for `hybrid`, the system its third stage lands on. No file
of the protocol chain imports a gather-based one, and `Results.lean` is where the two chains meet,
so either chain reads standalone below it.

## Suggested first read

`Vocabulary/Parameters.lean` → `Vocabulary/Labels.lean` → `Specifications/ABA.lean` → skim
`Specifications/ABASafety.lean`'s two trace predicates →
`HybridRefinesSpecification/Relation.lean`'s module docstring →
`ImplementationByABDY/System.lean`'s (the system the headlines are about) →
`Composition/HybridAndSubstitution.lean`'s (the system the core simulation starts from) →
`Results.lean`, whose docstring names the steps of both chains and their files. Follow
it into the statements along `ABDY.protocolSimulation` → `ABDY.substitutionSimulation` →
`hybridRefinesSpecification`, with `Composition/ABAState.lean`'s `ABAState` beside the last. That is
roughly 700 lines of reading and gives the full statement-level picture; descend into the GBCA and
core-simulation proofs only when you want them.

For the two sub-protocol interfaces, read the specification beside the trace property it
carries: `GBCA/Specification.lean` with `GBCA/SpecificationSafety.lean`'s
`specInst_binding`, and `Gather/Specification.lean` with
`Gather/CommonCoreAtSpecification.lean`'s `specInst_core`.

For the gather-based chain, by module docstring: `ReliableBroadcast/BrachaComposition.lean` →
`ReliableBroadcast/BrachaCompositionStepInversion.lean` → `Gather/Composition.lean` →
`Gather/CompositionStepInversion.lean` → `GBCA/AFW/Composition.lean` →
`GBCA/AFW/CompositionStepInversion.lean` → `GBCA/AFW/StepOverGatherSpecifications.lean` →
`ImplementationByAFW/CompositionChain.lean` → `ImplementationByAFW/Simulation.lean`. The first six
give the components of one level each, the alphabet they speak and the row characterisation that
reads a transition of the composition off its label; `GBCA/AFW/StepOverGatherSpecifications.lean` is the row table the counting refinement runs
on; `ImplementationByAFW/CompositionChain.lean` is the assembly at the protocol shape and
`ImplementationByAFW/Simulation.lean` the simulation into `ImplementationByAFW/System.lean`, the
system that runs, over the row answers of `ImplementationByAFW/SimulationRows.lean`. The two
counting arguments are `Gather/CommonCoreCounting.lean`, read against `Gather/Specification.lean`
alone, and `GBCA/AFW/Counting.lean`. Each refinement rests on the row
characterisation of the composition it is about, so it is readable against the file that states
those rows.

## Where else to look

`../README.md` maps the library and its shared framework. `../DESIGN-Composition.md` is why
the chains are cut where they are; `../DESIGN-HybridRefinesSpecification.md` and `../DESIGN-GBCARefinesSpecification.md` are the
narrative accounts of the two large protocol-chain proofs, and `../DESIGN-GatherComposition.md`
of the gather-based stack — including the counting argument behind the gather
specification's core; `../NOTES-Fidelity.md` is the encoding against
its sources and `../NOTES-Liveness-Roadmap.md` what termination would take. The prose
account is the ABA chapter of `../../blueprint/src/`, in two editions over one set of
statements: the default one (`content.tex`, each object and result stated against its Lean
declaration) and the full one (`content-full.tex`, adding the rule inventories, the
pseudocode and the proof bodies).

## Future work

- **Achievability theorem**: one explicit scheduler taking `protocol fourProcesses` to a two-return
  decision trace `t`, with `∃ D ∈ achievableTraceDists (protocol fourProcesses), D t ≠ 0` — the
  machine-checked non-vacuity for `ABDY.main`'s own system, exercising Agreement with two
  returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `ImplementationByABDY/System.lean` the budget is a component guard on the one local
  state that owns the corrupted set, so `ABDY.protocol_safe` and `ABDY.protocol_traces`
  need no hypothesis on the trace.
- **By-type finiteness of the environment coordinates** (not pursued): the process types enforce
  finitely many variables by construction — the finite map of round records, one round counter —
  where the network's round-indexed sent sets, the coin family, and the composed system's instance
  family are `ℕ`-indexed types whose reachable states have finite support. The by-type form is
  available throughout, by finite maps at the sent sets and a finitely-supported family combinator
  in `Framework/`. The finite-program principle does not ask for it: the network is the adversary,
  the coin an assumed oracle, and the instance family a specification.
