# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary
agreement, following the "Verifying ABA with Leslie" blueprint. The headlines of the
protocol chain are in `Results.lean` — `ABDY.main`, `ABDY.refines`, `ABDY.chainSim`,
`ABDY.protocol_safe`, `ABDY.protocol_traces`, `ABDY.composed_safe`, and the shared
`hybrid_spec` — and those of the gather-based chain in `AFW/FlatSim.lean` — `AFW.main`,
`AFW.refines`, `AFW.chainSim`, `AFW.protocol_composed` — beside the composed-level
`AFW.composed_refines`, `AFW.composed_safe`, `AFW.chainSimComposed` and
`GBCA.gatherRoundRefines` in `Round/Binding.lean`, all axiom-clean and guarded. Each chain
carries two headlines about its ghost-free reading, in `ABDY/Erasure.lean` and
`AFW/Erasure.lean`: `protocol_erasure`, the equality of achievable trace distributions
between the protocol and that reading, and `protocol₀_safe`, Validity and Agreement at it. The two
sub-protocol interfaces carry headlines of their own: `GBCA.specInst_binding` in
`Spec/GBCASafety.lean`, with its four implementation readings
`GBCA.implInst_binding` in `ABDY/ImplSim.lean` and `GBCA.pairInst_binding`,
`GBCA.idealInst_binding`, `GBCA.lowPairInst_binding` in `Round/Binding.lean`; and `Gather.specInst_core` in
`Gather/Safety.lean`, with the two implementation readings `Gather.idealInst_core` in
`Gather/IdealSim.lean` and `Gather.lowInst_core` in `Gather/LowSim.lean`.

The architecture in two lines, all of it in the protocol's own coordinates:

```
ABDY.protocol  ⊑  ABDY.composed                                  ⊑  hybrid  ⊑  ABA.spec
 AFW.protocol  ⊑   AFW.composed  ⊑  AFW.hybrid1  ⊑  AFW.hybrid2  ⊑  hybrid  ⊑  ABA.spec
```

One GBCA specification, two verified implementations, each carried from the protocol
as it runs. The first line carries the direct implementation (ABDY22's Algorithm 6,
D18), the second the gather-based one (AFW25's two-gather construction, D24), and the
two chains share every link from `hybrid` up.

A system below that meeting point belongs to one implementation or the other and is
named for its source: `ABDY`, after Abraham, Ben-David and Yandamuri, and `AFW`, after
Attiya, Flam and Welch. Across the two namespaces a name means the same thing —
`AFW.composed` is to the gather-based implementation what `ABDY.composed` is to the
ABDY22's — and `hybrid` and `ABA.spec`, which the chains share, are named in neither.
The rest of the gather-based chain sits in `AFW` as well: its headlines are `AFW.main`
and `AFW.refines`, where ABDY22's are `ABDY.main` and `ABDY.refines`. A `G` elsewhere in the
development is graded agreement — `callG`, `retG`, `GSub`, `GNetState` — and never the
chain.

Both flat readings are one construction. What a protocol reading fixes — the round
loop, the DECIDED sets, the coin handshake, corruption, the network adversary and
the composition pipeline — is settled by the round interface and the specification,
so `Reading/Flat.lean` writes it once, parametric in the stage message type, the
per-process per-round stage record, the stage-side rows, and a per-round ghost record
of the network adversary, updated on every row and read as the guard of the two
graded-agreement return rows (D30). `ABDY/Protocol.lean` supplies ABDY22's;
`AFW/Flat.lean` supplies the gather-based one.

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
  `ABDY.ProtocolRel`, and `ABDY.protocol_composed` is the inclusion it yields. The relation pins every
  composed coordinate against the protocol state: the entry of process `j` in the instance of
  round `r` is the stage record of round `r` that `j` holds (D22). What makes the inclusion
  one-directional is on the composed side. A round instance has a row for the Byzantine
  graded-agreement rows and no program of the protocol has one (D11), and the instance's
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
same value as ghost state: the bound bit is a field of the round's network state, and the
core a field of the gather instance's state, computed by `Gather.coreOf` from that
instance's network state alone. In the flat readings both belong to the network
adversary, which holds a ghost record per round (D30). No program's record carries
either and no program's row reads one. The two graded-agreement return rows of the
network do read the round's record, and what they read from it is the value the label
announces, never whether the row fires: the read admits a bit at every state
(`ghostOut_total` in `Reading/Erase.lean`). The announcement therefore leaves every
execution of the protocol as it is.

For the bound bit that inertness is a theorem.
`Reading/Erase.lean` erases the adversary's ghost record onto the ghost-free reading
`Net.flat₀`, whose returns announce any bit, and `ABDY.protocol_erasure` and
`AFW.protocol_erasure` are the resulting equalities of achievable trace distributions.
No map on labels appears in either statement: `Lab.retG` lies in `Lab.hiddenAPI`, so the
announced bit is silent at protocol level and the final hiding frame discharges the
label identification the erasure runs on.

What the announcement buys is binding as a property of a single trace, at the instance
level. Every round-`r` return of a trace of `GBCA.specInst` names one bit, and every one
of them that hands out a value hands out that bit (`GBCA.BindingTrace`,
`GBCA.specInst_binding`). Every return of a trace of `Gather.specInst` names one payload
set, of at least `n − f` entries and below the returned map (`Gather.CoreTrace`,
`Gather.specInst_core`). Both predicates are read off labels alone, so a
trace-distribution inclusion transports them. `GBCA.implInst_binding`,
`GBCA.pairInst_binding`, `GBCA.idealInst_binding` and `GBCA.lowPairInst_binding` are binding
at the two verified graded-agreement implementations and at the two tiers between them,
along their own refinements, and `Gather.idealInst_core` and `Gather.lowInst_core` are the two gather
implementations' readings along theirs.

## Scope

GBCA is verified to **implementation** level, by both implementations — the
gather-based one down through gather and Bracha's reliable broadcast, both encoded at
specification and implementation level of their own; WCC is **assumed** at specification level
(its coin is `wccPMF`). Both trace predicates are read at never-corrupted returners.
`ValidityTrace` is the paper-form predicate (D13): every return of `b` by a never-corrupted
process is preceded by a `callABA _ b` from a caller that is never corrupted anywhere in the
trace, and `AgreementTrace` asks two such returns to carry the same bit. That is the
quantification of the papers' own contracts, and it is what the model forces: the model
contains the corrupted interface, so a corrupted process may call one bit and record
another, and may return either bit at any time (D23). The `f + 1` `SuppOK` support counts
are the invariant machinery that makes this provable, not the predicate itself. Safety
only — no termination, liveness, unpredictability or fairness. The protocol's `terminate`
rule is a rule of the model, not a result: no theorem says when it fires, or that it ever
does.

## Deviations

Each departure from the source blueprint carries a label D1–D33, cited at the point where
it applies. The registry — every active label glossed, and the numbers the range skips —
is the Deviations paragraph of `../../blueprint/src/content.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its two sources beyond that
registry.

## The files

Each file's module docstring is the account of record for it; the table says only what
the file is. The folders are given in dependency order, and no folder imports one
below it: `Vocabulary/` is written over by everything, `AFW/` writes over
everything. Within a folder the files are alphabetical.


**`ABA/Vocabulary/`** — the records and alphabets every reading is written over.

| file | lines | what it is |
|---|---|---|
| `Vocabulary/NetworkState.lean` | 408 | The two-part vocabulary of the gather-based development: network state (D5) beside `n` process local states, with the multicast/delivery/corrupt operations and the quorum-intersection kit, stated once and shared by the three sub-protocol encodings. |
| `Vocabulary/Labels.lean` | 147 | The shared label alphabet `Lab n`: the visible API, the hidden sub-protocol handshakes, `τ`. |
| `Vocabulary/Params.lean` | 125 | The parameters `P` — `n`, `f` with `n > 3f`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Vocabulary/RoundLoop.lean` | 249 | **The ABA round loop**, per process and nothing else: the phase machine, the control record, the round-loop record. |

**`ABA/Spec/`** — what both implementations are measured against.

| file | lines | what it is |
|---|---|---|
| `Spec/ABA.lean` | 235 | **The top-level ABA specification**, the system all safety is measured against. Eight rules over `SpecState`, whose control mode carries the flip (D21) and two of which are the corrupted interface (D23). The decision is guarded by the `f + 1` support guard `SuppOK` alone (D13). |
| `Spec/ABASafety.lean` | 717 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `Spec/GBCA.lean` | 292 | The graded binding crusader agreement specification, per round. Binding is negative, and every return announces the round's bound bit (D19, D29). |
| `Spec/GBCASafety.lean` | 683 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. `specInst_binding` reads binding off a trace. |
| `Spec/WCC.lean` | 259 | The weak common coin specification, per round, and the coin value domain `TVal`. The call carries three rows: an unguarded loop that records nothing, one that records a caller, and one that records the caller whose access carries the count above `f` and draws the coin in the same step (D31). Held at specification level by design. |

**`ABA/Reading/`** — the flat reading, parametric in the graded-agreement implementation.

| file | lines | what it is |
|---|---|---|
| `Reading/Alphabet.lean` | 209 | The rendezvous alphabet `NLabP n M` a flat reading speaks, parametric in the stage message type, with the label pullback the coin oracle is read along. |
| `Reading/Flat.lean` | 1534 | **The flat reading of a protocol**, parametric in the graded-agreement implementation: the shared rows of a program and of the network adversary, the adversary's per-round ghost record with its update and its output (D30), the pipeline that composes them beside the coin oracle, and the inversion lemmas that read a row off its label. |
| `Reading/Erase.lean` | 405 | **The ghost-free reading** `Net.flat₀`, the same reading over a one-element ghost record with its returns free to announce any bit, and `Net.flat_erasure`: the two readings achieve the same trace distributions, by a state erasure of the network adversary carried through the pipeline. |

**`ABA/ABDY/`** — the implementation of ABDY22, and the composed reading over it.

| file | lines | what it is |
|---|---|---|
| `ABDY/ABAState.lean` | 380 | The ABA-side state as one object: the round-loop records beside the DECIDED network, with the accessors the invariant is stated in. |
| `ABDY/Components.lean` | 850 | The extended alphabet `NLab n` at ABDY22's messages, the coin oracle read along its label pullback, the round loop of one process, and the ABA-side network — the pieces the two compositions are built from. |
| `ABDY/Hybrid.lean` | 699 | **`ABDY.composed`**, **`ABDY.substSim`**: the same protocol read as four components, one round instance per round retained at every moment, and that graded-agreement component then replaced by its specification under the four congruences. |
| `ABDY/Instances.lean` | 1659 | **The round's graded-agreement instance** and the licence to replace it, `subSim`. |
| `ABDY/Impl.lean` | 882 | **The GBCA implementation**, ABDY22's Algorithm 6 in full (D18). Its state is the stage records beside the round's network state, which holds the round's bound bit (D29). |
| `ABDY/ImplSim.lean` | 2013 | The per-instance refinement `implRefines`, by exclude-on-demand: `excluded` carried as a receipt-pattern certificate; its soundness inclusion `implInst_refines` with the binding it carries, `implInst_binding`; and the broadcast compatibility of the relation with the `fail` act (`instRel_corrupt`), which the family lifting consumes. Two axiom checks. |
| `ABDY/Protocol.lean` | 828 | **ABDY22's protocol as it runs**, and the subject of the protocol chain: the flat reading at ABDY22's Algorithm 6 — its fourteen stage-side rows, the payload the call multicasts, the adversary's bound-bit ghost, and the inversions they answer. |
| `ABDY/ProtocolSim.lean` | 1095 | **`ABDY.protocolSim`**, **`ABDY.protocol_composed`**: the protocol carried into the composed reading along `ABDY.ProtocolRel`, whose five unguarded conjuncts determine the composed state. |
| `ABDY/Erasure.lean` | 100 | **`ABDY.protocol₀`** and **`ABDY.protocol_erasure`**: the protocol with the adversary's bound-bit record dropped, and the headlines re-derived at it — `protocol₀_composed`, `protocol₀_refines`, `protocol₀_safe`, `protocol₀_traces`. Three axiom checks. |

**`ABA/Core/`** — the simulation of the hybrid by the ABA specification, and its witnesses.

| file | lines | what it is |
|---|---|---|
| `Core/Abs.lean` | 332 | `Abs` preservation for the stutter rows, and the assembly `Inv.step`. |
| `Core/Run.lean` | 53 | The abstract-state run kit: `SpecStep.decide` as a τ-run (`decide_step`), and a run closed by a visible step (`weakStep_of_run_then_step`). |
| `Core/Inv.lean` | 3900 | Step inversion for `hybrid`, then preservation of `Inv` across every row. The bulk of the proof text. |
| `Core/NonVacuity.lean` | 648 | A concrete 20-step run of `hybrid P4` to a `retABA` decision, so the simulation about it is not vacuous. |
| `Core/Rel.lean` | 676 | The core simulation's relation: the lazy abstract state `Abs` and the concrete invariant `Inv`. |
| `Core/Sim.lean` | 415 | **`coreSim`**: the simulation proof itself, one row per concrete step class. |

**`ABA/`** — the headlines.

| file | lines | what it is |
|---|---|---|
| `Results.lean` | 218 | The deliverables of the protocol chain, gathered so every citable statement is in one file. Thirteen `#guard_msgs` axiom checks. |

**`ABA/Broadcast/`** — Bracha's reliable broadcast.

| file | lines | what it is |
|---|---|---|
| `Broadcast/Impl.lean` | 145 | Bracha's three message levels (blueprint Algorithm 6) over the two-part state. |
| `Broadcast/ImplSim.lean` | 996 | `brbRefines`: the Bracha instance refines TS 6, the committed value certified by an ECHO receipt quorum, the commit fired on demand. Exports the chain-data answers the gather files replay. |
| `Broadcast/Spec.lean` | 160 | The reliable-broadcast specification, per leader (blueprint TS 6, safety-only): the input/committed-value split with the guarded commit (D27). |
| `Broadcast/Sub.lean` | 951 | **The Bracha instance, composed**: `BRB.implInst`, the `n` per-process programs beside the instance's network with the instance's own events hidden, and the row characterisation `implInst_step_iff_row` that reads a transition off its label. |

**`ABA/Gather/`** — gather over reliable broadcast.

| file | lines | what it is |
|---|---|---|
| `Gather/Core.lean` | 1405 | The invariant of the gather-over-BRB instance and the counting argument for its core: `coreOf` has `n − f` committed entries and lies below the committed `BIND` payload of every process outside `F`, with the `f + 1` freeze certificate the specification's bind guard consumes. |
| `Gather/Ideal.lean` | 603 | `Gather.IdealStep`, the rule table of the gather instance over `2n` BRB specification coordinates (blueprint Algorithm 4, the binding form of AFW25's Algorithm 5), stated over the composition's state, with the row characterisation `idealInst_step_iff_row`. |
| `Gather/IdealSim.lean` | 962 | `gatherCore`: the gather-over-BRB instance refines TS 4. The return run commits the entries it reads, freezes the core at `coreOf` of the network state, and returns, in one weak transition. |
| `Gather/Low.lean` | 518 | `Gather.LowStep`, the same table with each BRB coordinate a composed Bracha instance; delivery as a receipt-quorum predicate (D28). |
| `Gather/LowSim.lean` | 134 | `gatherLow`: the broadcast substitution inside gather, per coordinate, carried through the composition by the congruences. |
| `Gather/Safety.lean` | 148 | `CoreTrace`, the common core read off a trace, and `specInst_core` at the specification. |
| `Gather/Spec.lean` | 215 | The gather specification (blueprint TS 4): call/commit split (D26) and the write-once core the return labels announce (D29). |
| `Gather/Sub.lean` | 1469 | **The gather instance, composed**: `n` gather programs beside the gather network, in parallel with `2n` composed broadcast instances — `Gather.idealInst` over the broadcast specifications and `Gather.lowInst` over Bracha's — read back over the gather alphabet extended by the call loop. |
| `Gather/Vocabulary.lean` | 167 | The records a gather instance is written over — the `ECHO`/`VOTE` messages and the per-process record — and the core `coreOf` of a gather network state, with the incidence lemmas the counting argument sums. |

**`ABA/Round/`** — the two-gather round and the three tiers that carry it.

| file | lines | what it is |
|---|---|---|
| `Round/Binding.lean` | 301 | Binding of the round over the family alphabet: `BindingTraceN` and `liftedSpec_binding`, the round composite `gatherImplRefines` and `gatherRoundRefines`, and the binding each tier carries — `GBCA.pairInst_binding`, `GBCA.idealInst_binding`, `GBCA.lowPairInst_binding`. Six axiom checks. |
| `Round/Counting.lean` | 362 | **The counting of the two-gather round** (AFW25 Algorithm 4 at R = 2, its approximate-agreement subroutine replaced by a local count, D24): the candidate/grade kit `cand` and `gradeOf`, the bound bit `boundOfCore` read off the first gather's core (D29), and the entry counts the refinement consumes. |
| `Round/Pair.lean` | 449 | `GBCA.PairStep`, the rule table of the round over two gather specifications, stated over the round's state, with the row characterisation `pairInst_step_iff_row`. |
| `Round/PairSim.lean` | 1437 | `pairRefines`: the two-gather round refines the GBCA specification. Exclusion and grade certified on the two frozen cores, the surviving bit pinned by the bound bit; exclude-on-demand. |
| `Round/Sub.lean` | 1155 | **The graded-agreement round, composed**: `n` round programs beside the layer's network, in parallel with two gather instances — `GBCA.pairInst` over the gather specifications, `GBCA.idealInst` over gather-over-BRB, and **`GBCA.lowPairInst`, the gather-based GBCA implementation**, over gather-over-Bracha — read over the family alphabet `NLab n`. |
| `Round/Substitutions.lean` | 218 | `lowPairRefines` and `idealRefines`: the two gather substitutions inside the round, componentwise. |

**`ABA/AFW/`** — the gather-based chain, and the protocol beneath it.

| file | lines | what it is |
|---|---|---|
| `AFW/Chain.lean` | 398 | **The gather-based chain**: the sides `lowSide`, `idealSide` and `pairSide`, the three stages `AFW.composed ⊑ AFW.hybrid1 ⊑ AFW.hybrid2 ⊑ hybrid`, and the composed-level headlines `AFW.composed_refines`, `AFW.composed_safe`, `AFW.chainSimComposed`. Four axiom checks. |
| `AFW/Flat.lean` | 721 | **The gather-based protocol as it runs**: the flat reading at AFW25's two-gather construction — the tagged message type collapsing a round's `4n + 2` network states into one sent-set family, the process-major stage record, the adversary's ghost record of the two cores and the bound bit, and the 23 stage-side rows. |
| `AFW/FlatSim.lean` | 2155 | **`AFW.protocolSim`**, **`AFW.main`**: the gather-based protocol carried into `AFW.composed` along a relation that computes the composed state from the flat one, the ghost record included, and the headlines `AFW.refines`, `AFW.main`, `AFW.chainSim` it yields. Five axiom checks. |
| `AFW/Erasure.lean` | 111 | **`AFW.protocol₀`** and **`AFW.protocol_erasure`**: the gather-based protocol with the adversary's record of the two cores and the bound bit dropped, and the headlines re-derived at it — `protocol₀_composed`, `protocol₀_refines`, `protocol₀_safe`, `protocol₀_traces`. Five axiom checks. |
| `AFW/Frame.lean` | 2726 | The view of the composed round after one flat row: for each row of the flat reading, the round's view after it is the view before it with the composed round's own effect applied. |
| `AFW/View.lean` | 790 | `AFW.toRound`, the view that computes a composed state from a flat one, the relation `AFW.ProtocolRel` it carries, and the builders that assemble a transition of the composed reading. |

The pieces both compositions are built from are in `ABDY/Components.lean`, over the alphabet of
`Reading/Alphabet.lean`. `ABDY/Protocol.lean` and `ABDY/Instances.lean` each import it and neither
imports the other, so the two readings of the protocol are assembled independently over one
set of components. `Reading/Flat.lean` sits beside `ABDY/Components.lean` over the same alphabet
and imports no implementation, which is what lets both flat readings instantiate it. The specification side —
`ABDY/Instances.lean`, `ABDY/Hybrid.lean` and the core simulation above them — never imports
`ABDY/Protocol.lean`; the protocol enters only at `ABDY/ProtocolSim.lean`, which is where the two
readings meet, and `Results.lean` reaches it through that file.

The gather-based files form their own stack over `Vocabulary/NetworkState.lean` and the unchanged
`Spec/GBCA.lean`, meeting the rest of the development in three places: `Round/Counting.lean`
reads the shared round alphabet, `AFW/Flat.lean` instantiates `Reading/Flat.lean`, and
`AFW/Chain.lean` imports `Results.lean` for the shared links from `hybrid` up. Nothing
in the protocol chain imports a gather-based file, so either chain reads standalone.

## Suggested first read

`Vocabulary/Params.lean` → `Vocabulary/Labels.lean` → `Spec/ABA.lean` → skim
`Spec/ABASafety.lean`'s two trace predicates → `Core/Rel.lean`'s module docstring →
`ABDY/Protocol.lean`'s (the system the headlines are about) → `ABDY/Hybrid.lean`'s (the
system the core simulation starts from) → `Results.lean`, whose docstring names the three
steps of the chain and their files. Follow it into the statements along
`ABDY.protocolSim` → `ABDY.substSim` → `coreSim`, with `ABDY/ABAState.lean`'s `ABAState`
beside the last. That is roughly 700 lines of reading and gives the full statement-level
picture; descend into the GBCA and core-simulation proofs only when you want them.

For the two sub-protocol interfaces, read the specification beside the trace property it
carries: `Spec/GBCA.lean` with `Spec/GBCASafety.lean`'s `specInst_binding`, and
`Gather/Spec.lean` with `Gather/Safety.lean`'s `specInst_core`.

For the gather-based chain: `Broadcast/Spec.lean` → `Gather/Spec.lean` →
`Round/Counting.lean`'s module docstring (the algorithm and its counting) →
`Round/Sub.lean`'s (the round's components) → `AFW/Flat.lean`'s (the system that runs) →
`AFW/Chain.lean`'s and `AFW/FlatSim.lean`'s (the assembly). `Gather/Core.lean`'s
docstring is the counting argument behind the core, and is read against
`Gather/Spec.lean` alone. The simulation files export their answers as τ-chain data
consumed one level up, so each `*Sim` file is readable against the one below it.

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
  machine-checked non-vacuity for `ABDY.main`'s own system, exercising Agreement with two returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `ABDY/Protocol.lean` the budget is a component guard on the one local state that owns the corrupted
  set, so `ABDY.protocol_safe` and `ABDY.protocol_traces` need no hypothesis on the trace.
- **`ValidityTrace` witness strengthening**: the current witness clause accepts any
  preceding `callABA id' b`; the proof yields a stronger ghost-backed witness. Care: while
  nothing is decided the D13 ghost record holds the bit of the *last* `SpecStep.callSet`
  (D16 overwrite), so a "first call" restatement is not immediate.
- **By-type finiteness of the environment coordinates** (not pursued): the process types
  enforce finitely many variables by construction — the finite map of stage records, one
  round counter — where the network's round-indexed sent sets, the coin family, and the
  composed reading's instance family are `ℕ`-indexed types whose reachable states have
  finite support. The by-type form is available throughout, by finite maps at the sent sets
  and a finitely-supported family combinator in `Framework/`. The finite-program
  principle does not ask for it: the network is the adversary, the coin an assumed
  oracle, and the instance family a specification-side reading.
- **Decomposing the gather-based composed reading**: its graded-agreement side is a family
  of single rule tables over joint states (D28), where the protocol chain's round is a
  composition of the stage programs beside their network. The target, and what
  reaching it takes, is `../TODO-Decomposing-AFW-Composed.md`.
