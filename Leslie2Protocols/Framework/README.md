# The framework — file guide

The protocol-independent combinators the ABA case study composes with, the congruences that
carry a forward simulation through them, and the couplings a Dirac-lifted relation admits. One
of the combinators — restriction along the left summand of an extended alphabet, in
`Relabel.lean` — is a fourth precongruence, beside the three in the core library. The eleven
files, in import order:

| file | lines | what it is |
|---|---|---|
| `DiracRelationCoupling.lean` | 57 | The couplings a Dirac-lifted relation admits: a Dirac source matched by a related target, and a source pushed forward along a map matched outcome by outcome. |
| `TraceDistributionSupport.lean` | 569 | From trace-distribution support to genuine executions: the safety transfer, the invariant inductions, and the label transport of a run. |
| `LoopsAndInstanceFamilies.lean` | 218 | Idle padding, partial label pullbacks, and ℕ-indexed instance families with a broadcast disjunct. |
| `FamilySimulation.lean` | 375 | Forward simulation is a congruence for `System.family`: per-instance refinement lifts to the family. |
| `SynchronisedProduct.lean` | 184 | Full-synchronisation product of a finite family — a visible label moves every component, τ moves one. |
| `SynchronisedProductAlongPullbacks.lean` | 161 | A family of components each read along its own pullback, under the synchronised product: the label with no image, the visible step, the silent step, and the family of Dirac steps at an update of one component. |
| `Relabel.lean` | 472 | Extended alphabets and restriction along the left summand, with the precongruence for it. |
| `WeakTransitionsFromChains.lean` | 196 | Weak runs from step chains: prepending a silent step, and the k-fold run — a chain of silent steps closed by one external step. |
| `FinerAlphabetCongruence.lean` | 193 | Forward simulation is a congruence for reading both systems over a finer alphabet along a partial label map. |
| `Congruence.lean` | 849 | Forward simulation is a congruence for the operators a composition is built from — binary parallel in either position, the full-synchronisation product of a finite family, hiding and restriction — with the weak-run splitting and transport lemmas the four proofs share. |
| `Erasure.lean` | 375 | Erasure of a state component no transition's firing depends on: the projection and lift clauses, the equality of achievable trace distributions they give, and the congruences that carry an erasure through composition, hiding and restriction. |
