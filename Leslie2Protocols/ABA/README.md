# The ABA case study — file guide

Machine-checked safety (Validity ∧ Agreement) for randomized asynchronous binary
agreement, following the "Verifying ABA with Leslie" blueprint. The headlines of the
protocol chain are in `Results.lean` — `ABDY.main`, `ABDY.refines`, `ABDY.chainSim`,
`ABDY.protocol_safe`, `ABDY.protocol_traces`, `ABDY.composed_safe`, and the shared
`hybrid_spec` — and those of the gather-based chain in `GatherFlatSim.lean` — `AFW.main`,
`AFW.refines`, `AFW.chainSim`, `AFW.protocol_composed` — beside the composed-level
`AFW.composed_refines`, `AFW.composed_safe`, `AFW.chainSimComposed` and
`GBCA.gatherRoundRefines` in `GatherChain.lean`, all axiom-clean and guarded.

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
ladder — and `hybrid` and `ABA.spec`, which the chains share, are named in neither.
The rest of the gather-based chain sits in `AFW` as well: its headlines are `AFW.main`
and `AFW.refines`, where the ladder's are `ABDY.main` and `ABDY.refines`. A `G` elsewhere in the
development is graded agreement — `callG`, `retG`, `GSub`, `GNetState` — and never the
chain.

Both flat readings are one construction. What a protocol reading fixes — the round
loop, the DECIDED pools, the coin handshake, corruption, the network adversary and
the composition pipeline — is settled by the round interface and the specification,
so `FlatReading.lean` writes it once, parametric in the stage message type, the
per-process per-round stage record and the stage-side rows. `Protocol.lean` supplies
the ladder's; `GatherFlat.lean` supplies the gather-based one.

- `ABDY.protocol` — the ladder protocol as it runs: `n` programs beside the network
  adversary, which owns the message pools and the corrupted set, and the coin oracle,
  the only component whose transitions are not Dirac. A program reads its own replacement
  flag and nothing else about corruption: not the corrupted set, not the budget, not
  another process's status. A corruption replaces the program of the process it names
  (D23). A program holds its round loop beside
  its stage-side record — the stage record of every round the process has touched, in a
  finite map — and terminates once its own return has fired and `2f + 1` DECIDED receipts
  are on record (D22).
- `ABDY.composed` — the same protocol read as a composition of components: the round
  instances, the `n` round loops, the ABA-side network holding the DECIDED pools, and the
  coin oracle. `ABDY.protocolSim` carries `ABDY.protocol` into it along the Dirac lift of
  `ABDY.ProtocolRel`, and `ABDY.protocol_composed` is the inclusion it yields. The relation pins every
  composed coordinate against the protocol state: the entry of process `j` in the instance of
  round `r` is the stage record of round `r` that `j` holds (D22). What makes the inclusion
  one-directional is on the composed side. A round instance has a row for the Byzantine
  graded-agreement drives and no program of the protocol has one (D11), and the instance's
  stage rules carry no termination guard, so the instance answers a send or a delivery at a
  process the protocol has terminated. This is where the chain passes from implementation to
  specification.
- `hybrid` — each round's instance replaced by the graded agreement specification
  (`ABDY.substSim`), the other three components untouched. This is what the core simulation runs on.
- `ABA.spec` — the single-automaton reading of agreement, reached by `coreSim`.

Components talk only through synchronized labels, and no component reads another's state.
Why the cut sits there, and what it buys, is `../DESIGN-Composition.md`.

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

Each departure from the source blueprint carries a label D1–D28, cited at the point where
it applies. The registry — every active label glossed — is the Deviations paragraph of
`../../blueprint/src/content.tex`.
`../NOTES-Fidelity.md` covers how the encoding stands against its two sources beyond that
registry.

## The files

Each file's module docstring is the account of record for it; the table says only what
the file is. The order is the dependency order.

| file | lines | what it is |
|---|---|---|
| `Params.lean` | 125 | The parameters `P` — `n`, `f` with `n > 3f`, and the coin distribution `wccPMF` with its ε/δ bounds. |
| `Labels.lean` | 141 | The shared label alphabet `Lab n`: the visible API, the hidden sub-protocol handshakes, `τ`. |
| `Spec.lean` | 235 | **The top-level ABA specification**, the system all safety is measured against. Eight rules over `SpecState`, whose control mode carries the flip (D21) and two of which are the corrupted interface (D23). The decision is gated on the `f + 1` support guard `SuppOK` alone (D13). |
| `WCCSpec.lean` | 163 | The weak common coin specification, per round, and the coin value domain `TVal`. Held at specification level by design. |
| `GBCASpec.lean` | 268 | The graded binding crusader agreement specification, per round. Binding is negative (D19). |
| `SpecSafety.lean` | 717 | `spec_safe`: every positive-mass trace of `ABA.spec` is valid and agreeing. The trace predicates live here. |
| `GBCASafety.lean` | 590 | Binding, graded agreement and Validity's safety half for the GBCA specification instance. |
| `GBCAImpl.lean` | 748 | **The GBCA implementation**, ABDY22's Algorithm 6 in full (D18). Its state is the stage records beside the round's fabric. |
| `GBCASim.lean` | 1808 | The per-instance refinement `implRefines`, by kill-on-demand: `dead` carried as a receipt-pattern certificate; and the broadcast compatibility of its relation with the `fail` act (`instRel_corrupt`), which the family lifting consumes. |
| `Core.lean` | 249 | **The ABA round loop**, per process and nothing else: the phase machine, the control record, the round-loop record. |
| `NetAlphabet.lean` | 206 | The rendezvous alphabet `NLabP n M` a flat reading speaks, parametric in the stage message type, with the label pullback the coin oracle is read along. |
| `Components.lean` | 839 | The extended alphabet `NLab n` at the ladder's messages, the coin oracle read along its label pullback, the round loop of one process, and the ABA-side network — the pieces the two compositions are built from. |
| `FlatReading.lean` | 1193 | **The flat reading of a protocol**, parametric in the graded-agreement implementation: the shared rows of a program and of the network adversary, the pipeline that composes them beside the coin oracle, and the inversion lemmas that read a row off its label. |
| `ABAState.lean` | 380 | The ABA-side state as one object: the round-loop records beside the DECIDED network, with the accessors the invariant is stated in. |
| `Protocol.lean` | 679 | **The ladder protocol as it runs**, and the subject of the protocol chain: the flat reading at ABDY22's Algorithm 6 — its fourteen stage-side rows, the payload the call multicasts, and the inversions they answer. |
| `GBCAInstances.lean` | 1635 | **The round's graded-agreement instance** and the licence to replace it, `subSim`. |
| `Hybrid.lean` | 739 | **`ABDY.composed`**, **`ABDY.substSim`**: the same protocol read as four components, one round instance per round retained at every moment, and that graded-agreement component then replaced by its specification under the four congruences. |
| `CoreSimRel.lean` | 674 | The core simulation's relation: the lazy abstract twin `Abs` and the concrete invariant `Inv`. |
| `CoreSimInv.lean` | 3947 | Step inversion for `hybrid`, then preservation of `Inv` across every row. The bulk of the proof text. |
| `CoreSimAbs.lean` | 335 | `Abs` preservation for the stutter rows, and the assembly `Inv.step`. |
| `CoreSimBurst.lean` | 53 | The abstract-twin burst kit: `SpecStep.decide` as a τ-burst (`decide_step`), and a burst closed by a visible step (`weakStep_of_burst_then_step`). |
| `CoreSim.lean` | 425 | **`coreSim`**: the simulation proof itself, one row per concrete step class. |
| `ProtocolSim.lean` | 1050 | **`ABDY.protocolSim`**, **`ABDY.protocol_composed`**: the protocol carried into the composed reading along `ABDY.ProtocolRel`, whose five unguarded conjuncts determine the composed state. |
| `Results.lean` | 215 | The deliverables of the protocol chain, gathered so every citable statement is in one file. Twelve `#guard_msgs` axiom firewalls. |
| `NonVacuity.lean` | 629 | A concrete 21-step run of `hybrid P4` to a `retABA` decision, so the simulation about it is not vacuous. |
| `Fabric.lean` | 407 | The two-box vocabulary of the gather-based development: message fabric (D5) beside `n` process boxes, with the multicast/delivery/corrupt operations and the quorum-intersection kit, stated once and shared by the three sub-protocol encodings. |
| `BRBSpec.lean` | 160 | The reliable-broadcast specification, per leader (blueprint TS 6, safety-only): the input/committed-value split with the guarded commit (D27). |
| `BRBImpl.lean` | 154 | Bracha's ladder (blueprint Algorithm 6) over the two-box state. |
| `BRBSim.lean` | 965 | `brbRefines`: the Bracha instance refines TS 6, the committed value certified by an ECHO receipt quorum, the commit fired on demand. Exports the chain-data answers the gather files replay. |
| `GatherSpec.lean` | 223 | The gather specification (blueprint TS 4): call/commit split (D26) and the write-once core family (D25). |
| `GatherMid.lean` | 256 | The gather implementation over `2n` BRB specification coordinates (blueprint Algorithm 4, from AFW25): approval as commitment, the ECHO/VOTE ladder over entry sets, BIND by broadcast (D28). |
| `GatherSim.lean` | 1443 | `gatherCore`: the gather-over-BRB instance refines TS 4. The core family is read off `f + 1` honest quorum members' committed BIND payloads; the return burst commits, binds and returns in one weak transition. |
| `GatherLow.lean` | 187 | The same table with each BRB coordinate a Bracha instance; delivery as a receipt-quorum predicate (D28). |
| `GatherLowSim.lean` | 652 | `gatherLow`: the broadcast substitution inside gather, per coordinate, lagging commits fired as τ-chains. |
| `GBCAPair.lean` | 438 | **The two-gather round** (AFW25 Algorithm 4 at R = 1, no approximate agreement, D24) over two gather specifications, with the candidate/grade counting kit in member form. |
| `GBCAPairSim.lean` | 1067 | `pairRefines`: the two-gather round refines the GBCA specification. Exclusion and grade certified on the core families; kill-on-demand. |
| `GBCAIdeal.lean` | 97 | The round over gather-over-BRB components. |
| `GBCAIdealSim.lean` | 197 | `idealRefines`: the gather substitution inside the round, componentwise. |
| `GBCALow.lean` | 99 | **The gather-based GBCA implementation**: the round over gather-over-Bracha components — two gather ladders, `4n` Bracha instances beneath. |
| `GBCALowSim.lean` | 207 | `lowRefines`: the broadcast substitution inside the round, componentwise. |
| `GatherChain.lean` | 486 | **The gather-based chain**: the round composite `gatherImplRefines`, the lifted sides `AFW.composed ⊑ AFW.hybrid1 ⊑ AFW.hybrid2 ⊑ hybrid`, and the composed-level headlines `AFW.composed_refines`, `AFW.composed_safe`, `AFW.chainSimComposed`. Six axiom firewalls. |
| `GatherFlat.lean` | 599 | **The gather-based protocol as it runs**: the flat reading at AFW25's two-gather construction — the tagged message type collapsing a round's `4n + 2` fabrics into one pool family, the process-major stage record, and the 23 stage-side rows. |
| `GatherFlatSim.lean` | 2894 | **`AFW.protocolSim`**, **`AFW.main`**: the gather-based protocol carried into `AFW.composed` along a relation that computes the composed state from the flat one, and the headlines `AFW.refines`, `AFW.main`, `AFW.chainSim` it yields. Five axiom firewalls. |

The pieces both compositions are built from are in `Components.lean`, over the alphabet of
`NetAlphabet.lean`. `Protocol.lean` and `GBCAInstances.lean` each import it and neither
imports the other, so the two readings of the protocol are assembled independently over one
set of components. `FlatReading.lean` sits beside `Components.lean` over the same alphabet
and imports no implementation, which is what lets both flat readings instantiate it. The specification side —
`GBCAInstances.lean`, `Hybrid.lean` and the core simulation above them — never imports
`Protocol.lean`; the protocol enters only at `ProtocolSim.lean`, which is where the two
readings meet, and `Results.lean` reaches it through that file.

The gather-based files form their own stack over `Fabric.lean` and the unchanged
`GBCASpec.lean`, meeting the rest of the development in three places: `GBCAPair.lean`
reads the shared round alphabet, `GatherFlat.lean` instantiates `FlatReading.lean`, and
`GatherChain.lean` imports `Results.lean` for the shared links from `hybrid` up. Nothing
in the protocol chain imports a gather-based file, so either chain reads standalone.

## Suggested first read

`Params` → `Labels` → `Spec` → skim `SpecSafety`'s two trace predicates → `Core`'s module
docstring → `Protocol`'s (the system the headlines are about) → `Hybrid`'s (the system the
core simulation starts from) → `Results`, whose docstring names the three steps of the
chain and their files. Follow it into the statements along `ProtocolSim.protocolSim` →
`Hybrid.substSim` → `CoreSim.coreSim`, with `ABAState`'s `ABAState` beside the last.
That is roughly 700 lines of reading and gives the full statement-level picture; descend
into the GBCA and core-simulation proofs only when you want them.

For the gather-based chain: `BRBSpec` → `GatherSpec` → `GBCAPair`'s module docstring
(the algorithm and its counting) → `GBCALow`'s (the round's components) → `GatherFlat`'s
(the system that runs) → `GatherChain`'s and `GatherFlatSim`'s (the assembly). The
simulation files export their answers as τ-chain data consumed one level up, so each
`*Sim` file is readable against the one below it.

## Where else to look

`../README.md` maps the library and its shared framework. `../DESIGN-Composition.md` is why
the chain is cut where it is; `../DESIGN-CoreSim.md` and `../DESIGN-GBCASim.md` are the
narrative accounts of the two large protocol-chain proofs, and `../DESIGN-GatherTower.md`
of the gather-based stack — including why the gather specification carries a core family;
`../NOTES-Fidelity.md` is the encoding against
its sources and `../NOTES-Liveness-Roadmap.md` what termination would take. The prose
account is the ABA chapter of `../../blueprint/src/`, in two editions over one set of
statements: the default one (`content.tex`, each object and result stated against its Lean
declaration) and the full one (`content-full.tex`, adding the rule inventories, the
pseudocode and the proof bodies).

## Future work

- **Achievability theorem**: one explicit scheduler for `protocol P4` driving a two-return
  decision trace `t`, with `∃ D ∈ achievableTraceDists (protocol P4), D t ≠ 0` — the
  machine-checked non-vacuity for `ABDY.main`'s own system, exercising Agreement with two returns.
- **Budget as an assumption throughout** (not pursued): the alternative shape is an
  unguarded `fail` in every system, `|F| ≤ f` relativized out of the invariants, and every
  headline conditional on a trace-level budget predicate. It is unnecessary here: in
  `Protocol.lean` the budget is a component guard on the one box that owns the corrupted
  set, so `ABDY.protocol_safe` and `ABDY.protocol_traces` need no hypothesis on the trace.
- **`ValidityTrace` witness strengthening**: the current witness clause accepts any
  preceding `callABA id' b`; the proof yields a stronger ghost-backed witness. Care: while
  nothing is decided the D13 ghost record holds the bit of the *last* `SpecStep.callSet`
  (D16 overwrite), so a "first call" restatement is not immediate.
- **By-type finiteness of the environment coordinates** (not pursued): the process types
  enforce finitely many variables by construction — the finite map of stage records, one
  round counter — where the network's round-indexed pools, the coin family, and the
  composed reading's instance family are `ℕ`-indexed types whose reachable states have
  finite support. The by-type form is available throughout, by finite maps at the pools
  and a finitely-supported family combinator in `Framework/`. The finite-program
  principle does not ask for it: the network is the adversary, the coin an assumed
  oracle, and the instance family a specification-side reading.
