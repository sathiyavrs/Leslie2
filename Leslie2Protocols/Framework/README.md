# The framework — file guide

The protocol-independent combinators the ABA case study composes with, the congruences that
carry a forward simulation through them, and the couplings a Dirac-lifted relation admits. One
of the combinators — restriction along the left summand of an extended alphabet, in
`Relabel.lean` — is a fourth precongruence, beside the three in the core library. The twelve
files, in import order:

| file | lines | what it is |
|---|---|---|
| `DiracRelationCoupling.lean` | 57 | The couplings a Dirac-lifted relation admits: a Dirac source matched by a related target, and a source pushed forward along a map matched outcome by outcome. |
| `TraceDistributionSupport.lean` | 569 | From trace-distribution support to genuine executions: the safety transfer, the invariant inductions, and the relabelling of a run. |
| `LoopsAndInstanceFamilies.lean` | 432 | Idle padding, partial label pullbacks, and ℕ-indexed instance families with a broadcast disjunct, on a state that records the broadcasts and a finite map of the touched instances. |
| `FamilySimulation.lean` | 634 | Forward simulation is a congruence for `System.family`: per-instance refinement lifts to the family, when a step at an untouched round is matched by a run whose first transition carries its label; with `AlterSeq.endState_cons` and `is_partial_exec_cons`, an execution with one step prepended, from which the weak runs of `WeakTransitionsFromChains.lean` and `Congruence.lean` are built. |
| `SynchronisedProduct.lean` | 185 | Full-synchronisation product of a finite family — a visible label moves every component, τ moves one. |
| `InputEnabledness.lean` | 173 | Input-enabledness and compatibility (LeslieBP §1.3, the simulations paper's Assumption 1 and Definition 2), preserved by idle padding, pullbacks, binary parallel, the full-synchronisation product and instance families. |
| `SynchronisedProductAlongPullbacks.lean` | 161 | A family of components each read along its own pullback, under the synchronised product: the label with no image, the visible step, the silent step, and the family of Dirac steps at an update of one component. |
| `Relabel.lean` | 473 | Extended alphabets and restriction along the left summand, with the precongruence for it. |
| `WeakTransitionsFromChains.lean` | 173 | Weak runs from step chains: prepending a silent step, and the k-fold run — a chain of silent steps closed by one external step. |
| `FinerAlphabetCongruence.lean` | 195 | Forward simulation is a congruence for reading both systems over a finer alphabet along a partial label map. |
| `Congruence.lean` | 810 | Forward simulation is a congruence for the operators a composition is built from — binary parallel in either position, the full-synchronisation product of a finite family, hiding and restriction — with the weak-run splitting and mapping lemmas the four proofs share. |
| `AuxiliaryVariableRemoval.lean` | 459 | Removal of a state component that no transition reads except to fix the value a label announces or to decide whether a transition on a label of a set `K` fires without moving the rest of the state: the projection and lift clauses, the forward simulation along the projection, the equality of achievable trace distributions once `K` is silent, and the congruences that carry a removal through composition, hiding and restriction. |
