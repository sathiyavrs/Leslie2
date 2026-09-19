# Leslie2Protocols — the protocol case studies

The second of the repository's three Lake libraries. It imports the core `Leslie2` and
nothing in the core imports it. Both are default `lake build` targets, so the API
documentation covers them and the blueprint's links resolve.

## `ABA/`

The asynchronous binary agreement development: machine-checked safety for randomized ABA,
from the protocol as it runs down to a small specification, by probabilistic forward
simulation, with two verified implementations of its graded-agreement sub-protocol —
one direct, one built over gather and reliable broadcast. Each is carried from the
protocol as it runs, through one flat reading written parametrically in the
implementation and instantiated twice. 53 files in nine content-themed
sub-folders, given in dependency order in its own file guide,
[`ABA/README.md`](ABA/README.md).

## `Framework/`

The protocol-independent combinators the case study composes with. One of them —
restriction along the left summand of an extended alphabet — is a fourth precongruence,
beside the three in the core.

| file | lines | what it is |
|---|---|---|
| [`TraceSupport.lean`](Framework/TraceSupport.lean) | 572 | From trace-distribution support to genuine executions: the safety transfer, the invariant inductions, and the label-side transport of a run. |
| [`IdleFamily.lean`](Framework/IdleFamily.lean) | 216 | Idle padding, partial label pullbacks, and ℕ-indexed instance families with a broadcast disjunct. |
| [`FamilySim.lean`](Framework/FamilySim.lean) | 373 | Forward simulation is a congruence for `System.family`: per-instance refinement lifts to the family. |
| [`SyncProduct.lean`](Framework/SyncProduct.lean) | 177 | Full-synchronisation product of a finite family — a visible label moves every component, τ moves one. |
| [`Relabel.lean`](Framework/Relabel.lean) | 468 | Extended alphabets and restriction along the left summand, with the precongruence for it. |
| [`WeakRun.lean`](Framework/WeakRun.lean) | 196 | Weak runs from step chains: prepending a silent step, and the k-fold run — a chain of silent steps closed by one external step. |
| [`MapIdleSim.lean`](Framework/MapIdleSim.lean) | 191 | Forward simulation is a congruence for reading both systems over a finer alphabet along a partial label map. |
| [`Congruence.lean`](Framework/Congruence.lean) | 850 | Forward simulation is a congruence for the operators a composition is built from — binary parallel on either side, the full-synchronisation product of a finite family, hiding and restriction — with the weak-run splitting and transport lemmas the four proofs share. |
| [`Erasure.lean`](Framework/Erasure.lean) | 376 | Erasure of a state component no transition's firing depends on: the projection and lift clauses, the equality of achievable trace distributions they give, and the congruences that carry an erasure through composition, hiding and restriction. |

## Notes

| file | what it is for |
|---|---|
| [`DESIGN-Decomposition.md`](DESIGN-Decomposition.md) | The five constraints the decomposition proofs impose on the gather-based chain's compositions — the loop label, the call record on the input instance, the grade dropped on return, the blocking of off-interface labels, the broadcast invariant carried on the composed side — each with the statement that fails without it. |
| [`DESIGN-Composition.md`](DESIGN-Composition.md) | Why the chains are cut where they are: what the composition buys, what each component owns and where it disappears, and what the DECIDED model already weakens. |
| [`DESIGN-CoreSim.md`](DESIGN-CoreSim.md) | The narrative account of the core simulation `hybrid ⊑ ABA.spec` — the abstract state, the invariant, and the certificates decided values ride on. |
| [`DESIGN-GBCASim.md`](DESIGN-GBCASim.md) | The narrative account of the per-instance GBCA refinement — exclude-on-demand, the receipt-pattern certificates, and the run structure. |
| [`DESIGN-GatherTiers.md`](DESIGN-GatherTiers.md) | The narrative account of the gather-based GBCA stack — the compositions at each level, the counting argument behind the gather specification's core, the BIND-by-broadcast pinning, the counting at the pair tier, the substitutions as congruence applications, and the flat reading beneath the composed one. |
| [`NOTES-Fidelity.md`](NOTES-Fidelity.md) | How the encoding stands against its sources — the Leslie blueprint, ABDY22 and AFW25: where it follows one against another, and what it deliberately does not reproduce. |
| [`NOTES-Liveness-Roadmap.md`](NOTES-Liveness-Roadmap.md) | Termination is out of scope; this is what proving it would take. |

The prose account of the case study is the ABA chapter of the repository's blueprint
(`../blueprint/src/`), which carries it in two editions over one set of statements.
