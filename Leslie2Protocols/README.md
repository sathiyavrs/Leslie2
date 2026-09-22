# Leslie2Protocols — the protocol case studies

The second of the repository's three Lake libraries. It imports the core `Leslie2` and
nothing in the core imports it. Both are default `lake build` targets, so the API
documentation covers them and the blueprint's links resolve.

## `ABA/`

The asynchronous binary agreement development: machine-checked safety for randomized ABA,
from the protocol as it runs down to a small specification, by probabilistic forward
simulation, with two verified implementations of its graded-agreement sub-protocol —
one direct, one built over gather and reliable broadcast. Each is carried from the
protocol as it runs, through one implementation shape written parametrically in the
graded-agreement implementation and instantiated twice. 53 files, `ABA/Results.lean`
beside thirteen content-themed sub-folders, given in import order in its own file
guide, [`ABA/README.md`](ABA/README.md).

## `Framework/`

The protocol-independent combinators the case study composes with, and the couplings a
Dirac-lifted relation admits. One of the combinators — restriction along the left summand of
an extended alphabet — is a fourth precongruence, beside the three in the core. Eleven files,
given in import order in its own file guide, [`Framework/README.md`](Framework/README.md).

| file | lines | what it is |
|---|---|---|
| [`DiracRelationCoupling.lean`](Framework/DiracRelationCoupling.lean) | 57 | The couplings a Dirac-lifted relation admits: a Dirac source matched by a related target, and a source pushed forward along a map matched outcome by outcome. |
| [`TraceDistributionSupport.lean`](Framework/TraceDistributionSupport.lean) | 569 | From trace-distribution support to genuine executions: the safety transfer, the invariant inductions, and the label transport of a run. |
| [`LoopsAndInstanceFamilies.lean`](Framework/LoopsAndInstanceFamilies.lean) | 218 | Idle padding, partial label pullbacks, and ℕ-indexed instance families with a broadcast disjunct. |
| [`FamilySimulation.lean`](Framework/FamilySimulation.lean) | 375 | Forward simulation is a congruence for `System.family`: per-instance refinement lifts to the family. |
| [`SynchronisedProduct.lean`](Framework/SynchronisedProduct.lean) | 184 | Full-synchronisation product of a finite family — a visible label moves every component, τ moves one. |
| [`SynchronisedProductAlongPullbacks.lean`](Framework/SynchronisedProductAlongPullbacks.lean) | 161 | A family of components each read along its own pullback, under the synchronised product: the label with no image, the visible step, the silent step, and the family of Dirac steps at an update of one component. |
| [`Relabel.lean`](Framework/Relabel.lean) | 472 | Extended alphabets and restriction along the left summand, with the precongruence for it. |
| [`WeakTransitionsFromChains.lean`](Framework/WeakTransitionsFromChains.lean) | 196 | Weak runs from step chains: prepending a silent step, and the k-fold run — a chain of silent steps closed by one external step. |
| [`FinerAlphabetCongruence.lean`](Framework/FinerAlphabetCongruence.lean) | 193 | Forward simulation is a congruence for reading both systems over a finer alphabet along a partial label map. |
| [`Congruence.lean`](Framework/Congruence.lean) | 849 | Forward simulation is a congruence for the operators a composition is built from — binary parallel in either position, the full-synchronisation product of a finite family, hiding and restriction — with the weak-run splitting and transport lemmas the four proofs share. |
| [`Erasure.lean`](Framework/Erasure.lean) | 375 | Erasure of a state component no transition's firing depends on: the projection and lift clauses, the equality of achievable trace distributions they give, and the congruences that carry an erasure through composition, hiding and restriction. |

## Notes

| file | what it is for |
|---|---|
| [`DESIGN-Decomposition.md`](DESIGN-Decomposition.md) | The five constraints the decomposition proofs impose on the gather-based chain's compositions — the loop label, the call record on the input instance, the grade dropped on return, the blocking of off-interface labels, the broadcast invariant carried on the composed system — each with the statement that fails without it. |
| [`DESIGN-Composition.md`](DESIGN-Composition.md) | Why the chains are cut where they are: what the composition buys, what each component owns and where it disappears, and what the DECIDED model already weakens. |
| [`DESIGN-HybridRefinesSpecification.md`](DESIGN-HybridRefinesSpecification.md) | The narrative account of the core simulation `hybrid ⊑ ABA.spec` — the abstract state, the invariant, and the certificates decided values ride on. |
| [`DESIGN-GBCARefinesSpecification.md`](DESIGN-GBCARefinesSpecification.md) | The narrative account of the per-instance GBCA refinement — exclude-on-demand, the receipt-pattern certificates, and the run structure. |
| [`DESIGN-GatherComposition.md`](DESIGN-GatherComposition.md) | The narrative account of the gather-based GBCA stack — the compositions at each level, the counting argument behind the gather specification's core, the BIND payloads sent by reliable broadcast, the counting at the round over the gather specifications, the substitutions as congruence applications, and the implementation beneath the composed one. |
| [`NOTES-Fidelity.md`](NOTES-Fidelity.md) | How the encoding stands against its sources — the Leslie blueprint, ABDY22 and AFW25: where it follows one against another, and what it deliberately does not reproduce. |
| [`NOTES-Liveness-Roadmap.md`](NOTES-Liveness-Roadmap.md) | Termination is out of scope; this is what proving it would take. |

The prose account of the case study is the ABA chapter of the repository's blueprint
(`../blueprint/src/`), which carries it in two editions over one set of statements.
