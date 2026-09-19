# TODO — decomposing `AFW.composed`

The gather-based chain's graded-agreement side is a family of single rule tables over joint
states. `GBCA.lowPairInst`, `GBCA.idealInst`, `Gather.lowInst` and `Gather.idealInst` are each
one inductive over a product state, so a round's `4n + 2` network states are fields of one
system rather than components of a composition. That is deviation D28, with the two clauses
that follow from it: a sub-protocol's call and return are fused into the rows of the caller,
and a sub-instance's delivery is a derived predicate on its coordinate — `Gather.apIn`,
`Gather.apBind` — rather than an event.

The protocol chain is decomposed at the corresponding place. `GSub.sub` is the `n` stage
programs under `System.syncProduct` beside the round's network `GSub.gNet`, its own send
and delivery events hidden and the result read back over the shared alphabet; `GSub.sub_projects`
relates that composition to the joint table `GBCA.implInst`, one step for one step.

This note records the intent to bring the gather-based stack to that same shape, and what
discharging it requires. Nothing here is built.

## The target

Every instance a component, each message-passing instance owning its network, and the
two sub-protocol substitutions inside a round congruence applications rather than hand-built
simulations.

```
gatherSide  =  System.family (round ·)                        one member per round
  round r   =  syncProduct [gbcaProc j]ⱼ ∥ gather₁ ∥ gather₂  at payload 𝔹 and 𝔹 ∪ {⊥}
  gatherᵢ   =  (syncProduct [gaProc j]ⱼ ∥ gaNet)
                 ∥ brbIn₁ ∥ … ∥ brbInₙ ∥ brbBind₁ ∥ … ∥ brbBindₙ
  brbₖ      =  syncProduct [brbProc j]ⱼ ∥ brbNet
```

Per round that is two gather instances and `4n` broadcast instances; `n` graded-agreement
programs, `2n` gather programs and `4n²` broadcast programs, so `4n² + 7n + 2` leaf systems in
all; and `4n + 2` networks, none of them the graded-agreement layer's. The other three
components of the composed reading — the `n` round loops, the ABA-side network and the coin
oracle — are untouched, and so is the context term they form.

The change reaches the three protocol-shaped systems with it. `AFW.composed`, `AFW.hybrid1`
and `AFW.hybrid2` are each their tier's family beside those same three components, so each
acquires a decomposed first factor and a state of a new shape. The chain keeps its length and
its meeting point.

## The graded-agreement layer

The layer the round's own rows belong to has neither per-process records nor a network
today, and the two absences have different causes.

It has no per-process record because its data is read off the instances beneath it. The
docstring of `GBCA.PairState` records the economy: the per-process input is the first gather's
call record, the candidate the second's, and the round's return flag the second's return flag.
Decomposition undoes that, a component not being allowed to read another's state. Each process
takes a record of its own holding its input, its candidate and its return flag; the gather call
records continue to hold what those instances were called with, and the two are tied by the
rendezvous rather than by identity.

It has no network because the construction sends nothing. AFW25 records of the crusader
case that it "makes one call to a gather subroutine and does no additional communication", and
D24 removes the step that still communicated at `R = 2`, the approximate-agreement call of
line 7. A round is two subroutine calls with local counting between and after them, so there is
no traffic for a network to hold and the decomposed layer is programs alone.

ABDY22's graded agreement is the contrast, and what separates the two chains here is the
algorithms rather than the encodings. It carries `GBCA.ProcState` per process and
`GSub.GNetState` beside them, because its Algorithm 6 is itself a message-passing protocol of
five levels.

## The boundary

The decomposition reaches `AFW.composed` and everything below it. `AFW.protocol` stays as it
stands: it is the protocol as it runs, a process there takes one row per thing it does, and
its fused rows are the honest presentation of that. D28's fusion clause therefore continues to
describe the flat reading, and `ABA/AFW/Flat.lean` keeps its citation of it.

That boundary is where the cost falls. `ABA/AFW/FlatSim.lean` carries the link between the two
readings and is written against the joint-table shape throughout: `AFW.toLow1` and `AFW.toLow2`
build a `Gather.LowState` by transposing local-state vectors out of the process records and
slicing network states out of the adversary's tagged sent family, and `AFW.toPair` assembles
the triple beside the bound bit. Against a decomposed target, each fused flat row is instead
answered by a synchronised run of several components.

## The precedent to copy

One level of this already exists, in `ABA/ABDY/Instances.lean`, and the work is that template
four levels deep with instance indices:

| piece | what it does |
|---|---|
| `GSub.GEvt` | the instance's own send and delivery events |
| `GSub.GLab` | the instance-internal alphabet, the shared one plus those events |
| `GSub.gEvents` | the set the instance hides |
| `GSub.subPre` | the programs beside the network |
| `GSub.sub` | that composition, hidden and read back |
| `GSub.sub_projects` | the composition against the joint table, one step for one step |
| `GSub.gPull` | the label pullback the specification is read along |
| `GSub.gOwns`, `GSub.gAct` | the family's routing and its corruption broadcast |

## What has to be built

**Four nested event alphabets**, bottom-up: broadcast send and delivery, broadcast call and
return, gather send and delivery, gather call and return. Each needs its own sum alphabet, its
hidden set, and an `abstract`-then-`relabel` frame, on the pattern of `GSub.GLab` and
`GSub.gEvents`. Every simulation below the round is then transported through four frames
instead of none.

**Instance-indexed label families.** `BRB.Lab.ret id m` names the returner and the payload but
not which of the `4n` instances it belongs to. Each instance's labels must be lifted along a
pullback naming its index, by `System.mapIdle` (`Framework/MapIdleSim.lean`), or the events
must carry the index outright. The same holds for the two gather instances of a round.

**Per-process delivery stores.** A component may not read another component's state, so
`Gather.apIn` and `Gather.apBind` cannot survive: they read `(s.brbIn k).recvCount j` and
`(s.brbIn k).val` at a neighbouring coordinate. Gather's per-process record `Gather.PRec`
gains a delivered map per broadcast family, written when the process synchronises on that
instance's return, and each level gains an invariant clause tying the store to the instance's
committed value. This is the clause of D28 whose removal costs state rather than syntax.

**Two of the three substitutions re-proved.** A congruence needs both sides decomposed, so the
requirement cascades upward. `GBCA.lowRefines` becoming `parallel_right`
(`Leslie2/Results.lean`) plus the family congruence (`Framework/FamilySim.lean`) forces
`GBCA.idealInst` to be a composition, and `GBCA.idealRefines` then forces `GBCA.pairInst` to be
one. Their present relations give way to the composites the congruences produce —
`GBCA.LowPairRel` is `Gather.LowRel` at each gather beside an equality on the bound bit, and
`GBCA.IdealRel` is `Gather.CoreRel` likewise.

`GBCA.pairRefines` stays hand-proved, and should. Its target `GBCA.specInst` is a single
specification with no components to match, and it is the interface the protocol chain is
measured against as well, so decomposing it would move the point where the two chains meet. It
is not the same kind of step as the two below it either: where they replace a sub-component by
its specification, this one collapses the two frozen cores into `excluded` and `grade`, which
is the counting argument of the tier and has nothing to hold fixed.

**A `parallel_left` precongruence**, which does not exist.
`ProbabilisticForwardSimulation.parallel_right` refines the left factor, so in a right-nested
composition only the leftmost component is reachable, and a gather has `2n` broadcast siblings
of which one can be leftmost. Reaching the rest needs the mirror, and with it the substitution
inside a gather is `2n` congruence applications rather than one.

Two routes. The first conjugates: `System.parallel_swap_step` and `prodPMF_map_swap`
(`Leslie2/ProcessAlgebra/Composition.lean`) already relate `sys₁ ∥ sys₂` to `sys₂ ∥ sys₁` under
`Prod.swap`, so reading the swap as a functional strong matching each way
(`ProbabilisticForwardSimulation.ofStrongFunctional` and its converse) gives the theorem as a
composite of three by `ProbabilisticForwardSimulation.trans`. The second proves it directly, and
the supporting lemmas are less help there than they look. `Leslie2/ProcessAlgebra/Parallel.lean`
carries `weakTau_parallel_left`, a **weak closure** of the refined component transported by
`weakTau_embed`, beside `weakTau_parallel_right`, a **single step** of the held component matched
one to one. They are not mirror images: in `parallel_right` the refined side runs weak
transitions and the held side only ever steps once, so the right-hand lemma was never needed at
closure strength. A direct proof supplies it, at `ι = (s_A, ·)`.

It belongs in `Framework/`, beside `ProbabilisticForwardSimulation.relabel` in
`Framework/Relabel.lean`: the fourth precongruence sits there rather than in the core, and Lean
changes stay inside this library.

**The flat link rebuilt.** `ABA/AFW/FlatSim.lean`, per the boundary above.

## What stays outside the theory

No congruence exists for `System.syncProduct` — `Framework/SyncProduct.lean` carries its
definition, a step characterisation and `System.syncProduct_isLTS`, and nothing about
simulation. So refining one process's program and lifting the result remains impossible, and
that is unaffected by this work.

It blocks none of the substitutions here, the instances being parallel factors rather than
members of a synchronised product. What it bounds is the claim available at the end: contextual
refinement will hold for contexts built from `parallel`, `interleave`, `abstract`, `relabel`,
`System.family` and `System.mapIdle`, and not for one that places a component inside a
synchronised product.

## Where the ghosts go

Decomposing the round forces a placement the joint tables never had to make.

A gather instance's core is computed by `Gather.coreOf` from the network state and the
corrupted set alone (`Gather.coreOf_networkState_only`), so it belongs with that instance's
network component and moves there without argument.

The round's bound bit has no such owner. It is the third factor of `GBCA.LowPairState` today,
written at the `link` row as `GBCA.boundOfCore` of the first gather's core. It is one bit for
the round rather than one per process, so the per-process graded-agreement records cannot hold
it, and neither gather may read the other's core. Either it travels on the label the first
gather returns on and the second gather holds it, or a component of its own does. That choice
is open.

The `link` row splits, and that is where the write lands. `GBCA.PairStep.link` fuses the first
gather's return to a process with that process's call of the second gather, in the one row that
also writes the bit. Across components those are two labels and two steps, so an intermediate
state appears in which a process holds its candidate and has not yet called the second gather,
and the write attaches to whichever of the two carries the core.

## What it retires, and what it does not

D28 has three clauses, and they do not all go.

- **Single rule tables over joint states** — retired for the gather stack.
- **Delivery as a derived predicate** — retired with it; the two are not separable, since the
  derived predicate is legitimate only while the coordinates belong to one system.
- **Call and return fused into the caller's rows** — survives at the flat reading, which is
  not being decomposed.

So the registry entry is re-glossed rather than deleted, and the label is not freed. Its
citations reach wider than the stack being changed: both blueprint content roots, the
gather-simulation figure, the node files of the gather definitions in each of the two node
directories, the four Lean modules `ABA/AFW/Flat.lean`, `ABA/AFW/FlatSim.lean`,
`ABA/Gather/Ideal.lean` and `ABA/Gather/Low.lean`, and the guides of this directory. The
registry's convention of listing out-of-use numbers explicitly applies to whatever part of the
label is freed.

## What must still hold at the end

- `GBCA.gatherRoundRefines` and the three tier inclusions beneath it.
- The four binding readings `GBCA.pairInst_binding`, `GBCA.idealInst_binding`,
  `GBCA.lowPairInst_binding`, and the two common-core readings `Gather.idealInst_core` and
  `Gather.lowInst_core`.
- `AFW.protocolSim` and every headline above it: `AFW.refines`, `AFW.main`, `AFW.chainSim`,
  `AFW.composed_refines`, `AFW.composed_safe`, and the erasure pair `AFW.protocol_erasure` and
  `AFW.protocol₀_safe`.
- The context term of the four congruences staying the same expression it is in
  `ABA/ABDY/Hybrid.lean`, so that `AFW.substSimPair` still lands on `hybrid` itself and the two
  chains still meet there.
- Every `#guard_msgs` axiom check of `ABA/AFW/Chain.lean` and `ABA/AFW/FlatSim.lean`.

Of those, the ones naming `AFW.protocol` and `ABA.spec` survive verbatim, neither system
changing. The ones naming `AFW.composed`, `AFW.hybrid1`, `AFW.hybrid2` or the chain's relations
change shape with the state types — `AFW.composed_refines`, `AFW.chainSim` and
`AFW.chainSimComposed` among them.

## Cost

The files the decomposition rewrites, with their present sizes:

| file | lines | why |
|---|---|---|
| `ABA/AFW/FlatSim.lean` | 3157 | the views and all the row matching |
| `ABA/Gather/IdealSim.lean` | 807 | the gather substitution, re-proved by congruence |
| `ABA/Gather/LowSim.lean` | 665 | the broadcast substitution, likewise |
| `ABA/Gather/Ideal.lean` | 331 | the joint table split into components |
| `ABA/Gather/Low.lean` | 201 | likewise, and `Gather.apIn` / `Gather.apBind` retired |
| `ABA/Round/Substitutions.lean` | 218 | the componentwise wrappers |
| `ABA/Round/Sub.lean` | 1155 | the round tier split |

Against `ABA/ABDY/Instances.lean` at 1659 lines, which is what one such level costs in the
protocol chain, including its own alphabet, the pullback lift and `GSub.sub_projects`.

`ABA/Broadcast/Impl.lean` and `ABA/Broadcast/Spec.lean` are already the two-part shape of
`ABA/Vocabulary/NetworkState.lean` and need no change in themselves; what changes is that their
instances become components, with the labels and frames that entails.

## What it buys

The three in-round substitutions become congruence applications, so each rests on
`ProbabilisticForwardSimulation.parallel_right` and `ForwardSimulation.family` rather than on
a relation written by hand. The gather stack then states, as the protocol chain already does
through `GSub.sub_projects`, that a round is `n` programs beside the networks they own —
a claim about the protocol rather than a convenience of its encoding. And the two chains
become uniform in shape, where at present only one of them is decomposed below the round.
