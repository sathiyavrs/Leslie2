# Design — the gather-based GBCA stack `GBCA.lowPairInst ⊑ … ⊑ GBCA.specInst` and its chain

Companion design document to the gather-based implementation of graded
agreement: the sub-protocol encodings (`ABA/Vocabulary/NetworkState.lean`, `ABA/Broadcast/Spec.lean`,
`ABA/Broadcast/Impl.lean`, `ABA/Gather/Spec.lean`, `ABA/Gather/Ideal.lean`,
`ABA/Gather/Low.lean`), their refinements (`ABA/Broadcast/ImplSim.lean`,
`ABA/Gather/IdealSim.lean`, `ABA/Gather/LowSim.lean`), the two-gather round and its
three readings (`ABA/Round/Counting.lean`, `ABA/Round/Sub.lean`,
`ABA/Round/Pair.lean` and the simulation files), the assembly at the protocol shape
(`ABA/AFW/Chain.lean`), and the protocol beneath it (`ABA/AFW/Flat.lean`,
`ABA/AFW/FlatSim.lean`). The gather subsections of
`blueprint/src/content.tex` are a condensation of this document; the
deviations D24, D26–D30 it realises are glossed in that file's registry, and the
source-fidelity items it rests on are §§2, 5 and 6 of `NOTES-Fidelity.md`.

## Systems

Per round, four systems over the shared round alphabet `Lab P.n`, three plain
forward simulations between them, and their probabilistic composite:

```
lowPairInst P r   -- two gather-over-Bracha instances: 2 network states + 4n Bracha instances
  ⊑ lowRefines        (broadcast substitution, componentwise)
idealInst P r     -- two gather-over-BRB.Spec instances
  ⊑ idealRefines      (gather substitution, componentwise)
pairInst P r      -- two Gather.SpecState coordinates + the bound bit + counting
  ⊑ pairRefines       (core counting into TS 2)
GBCA.specInst P r -- Spec/GBCA.lean, D19/D29

gatherImplRefines P r : lowPairInst ⊑ specInst   (probabilistic, trans ×2)
```

Beneath the round, two standalone tier sequences with their own alphabets, citable on
their own and consumed by the round through exported chain data:

```
BRB.implInst P ldr M ⊑ BRB.specInst P ldr M    (brbRefines, Broadcast/ImplSim.lean)
Gather.lowInst P X   ⊑ Gather.idealInst P X      (gatherLow,  Gather/LowSim.lean)
Gather.idealInst P X ⊑ Gather.specInst P X       (gatherCore, Gather/IdealSim.lean)
```

At the protocol shape (`AFW/Chain.lean`), each round reading is lifted over
the extended alphabet along `GSub.gPull`, gathered into the ℕ-indexed family
under the corruption broadcast, and put through the composed reading's
pipeline; the three substitutions become three stages whose last lands on
`hybrid P`:

```
AFW.protocol ⊑ AFW.composed ⊑ AFW.hybrid1 ⊑ AFW.hybrid2 ⊑ hybrid ⊑ ABA.spec
```

Beneath `AFW.composed` is `AFW.protocol`, the gather-based protocol as it runs
(`ABA/AFW/Flat.lean`), carried into the composed reading by `AFW.protocolSim`
(`ABA/AFW/FlatSim.lean`). Everything from `hybrid` up — the core simulation,
`spec_safe`, the safety transfer — is shared with the protocol chain.

Every protocol-shaped system and headline of this chain sits in the namespace
`AFW`, after Attiya, Flam and Welch, and carries the name of its counterpart in
the protocol chain: `AFW.composed` is to the gather-based implementation what
`ABDY.composed` is to ABDY22's. A `G` elsewhere in the development is graded
agreement — `callG`, `retG`, `GSub`, `GNetState` — and never the chain.

## The core of the gather specification

The classical binding property of gather says: once the first correct process
returns, there is a set of at least `n − f` entries on which every future
correct return is defined. TS 4 states this with a single set, and
`Gather.SpecState.core : Option (APSet n X)` carries it. The internal rule
`Gather.Step.bindCore` is its only writer and fires only from `core = none`,
under two guards: the set's entries are committed entries (`hval`), and it has
at least `n − f` of them (`hcard`). `Gather.Step.ret` demands that the returned
map dominate it, and the return label carries it (D29).

A forward simulation has to produce that write at a reachable prefix state, no
later than the first return it answers, and then hold every later return above
the set it chose. `ABA/Gather/Core.lean` is the argument that the
gather-over-BRB instance determines such a set.

**The core.** Let `w` be the gather network state of a state of the instance:
the per-sender sent sets beside the corrupted set `F`. Say that `q` *dominates*
`j` when every `VOTE` payload `q` has multicast lies above some `ECHO` payload
of `j`. Write `dominatedBy w q` for the senders `q` dominates and
`dominators w j` for the processes outside `F` that dominate `j`.
`Gather.coreOf P w` is the `ECHO` payload of a sender outside `F` carrying at
least `f + 1` dominators, and `∅` where there is no such sender. It reads the
sent sets and the corrupted set alone (`coreOf_networkState_only`), so the network
component of a flat reading computes it from its own state.

**The counting.** Read `dominatedBy` as an incidence whose rows and columns are
the processes outside `F`. A `VOTE` payload of a process outside `F` is
multicast above `n − f` delivered `ECHO` payloads, and `VOTE` is write-once, so
`n − f ≤ (dominatedBy w q).card` for every `q` outside `F` — vacuously for a `q`
that has multicast no `VOTE`, whose row is everything (`dominatedBy_card`).
Restricting a row to the columns costs at most `|F|`, so every row carries at
least `n − f − |F|` of them (`dominatedBy_honest_card`). Summing the rows and
reading the same sum by columns (`sum_dominatedBy`) gives a column `j₀` outside
`F` with `n − f − |F| ≤ (dominators w j₀).card` (`exists_dominators`), and
`n − f − |F| ≥ f + 1` under `n > 3f` and `|F| ≤ f`. The core is `j₀`'s `ECHO`
payload, whose own send guard gives it `n − f` entries.

**The transfer.** Take a committed `BIND` payload `U` of a process outside `F`.
It is that process's contributed payload, multicast above `n − f` delivered
`VOTE` payloads. Those `n − f` senders meet the `f + 1` dominators of `j₀` in a
process `q`, whose write-once `VOTE` payload lies above the core by domination
and below `U` by the bind guard, so `coreOf P w ⊆ U` (`transfer`,
`single_core`). Every `ECHO` field holds committed input-BRB entries, so the
core's entries are committed entries (`single_core_approved`), which is
`bindCore`'s other guard.

**The freeze certificate.** `coreOf_freeze` packages the three facts with the
count the simulation carries along the run: at least `f + 1` coordinates hold a
committed `BIND` payload above the core (`Gather.bindAbove`). That count is
blind to `F` and monotone under every rule (`bindAbove_mono`), so it survives
every later corruption, and it is what holds the returns after the first to the
set the first one froze. A returner's quorum of `n − f` committed payloads meets
the `f + 1` certified coordinates, and BRB values are functional, so the
returned map lies above the frozen core.

**Why the counting closes here.** `BIND` payloads travel by reliable broadcast
rather than on the gather network, so a committed payload is write-once
whatever happens to its sender afterwards, where a multicast payload is pinned
only by its sender's honesty and D1 withdraws that at any moment.
`Gather.IdealState` holds one bind-BRB instance per process (`brbBind`) and the
`BIND` send is that instance's call (D28's fusion), which is what makes the
objects the certificate counts stable.

## The commit splits (D26, D27)

The same dynamic-corruption reading, one level down. TS 6 pins the delivered
value at an honest `call`; Bracha's rounds with the leader corrupted after
its `INIT` but before any honest ECHO quorum can deliver a different value,
so the pinned specification excludes its own implementation
(`NOTES-Fidelity.md` §5). `BRB.SpecState` therefore splits `input` (the
call's record) from `val` (the committed value), with the commit τ-rule
guarded `ldr ∈ F ∨ input = some m`: the corrupted leader's power is a commit
of any value, the honest leader's value is pinned, and the window closes at
the commit. `Gather.SpecState` carries the per-entry form: `call` and `val`
split, `Gather.Step.commit` guarded `k ∈ F ∨ call k = some v`.

The refinement counterpart is *commit-on-demand*: the abstract commit is a
τ-rule with no implementation event to synchronise with, so the simulations
fire it inside the weak answer of the first row that reads it —
`BRB.commitReach` under a return, the `commitOne/commitList` chains of
`ABA/Gather/IdealSim.lean` under an approval-reading row.

## Counting at the pair tier (`pairRefines`)

`pairInst` is AFW25's Algorithm 4 at `R = 2`, its two-gather branch (D24): candidate at
`|dom g| − f` occurrences after the first gather, grade at
`|dom h| − f` / `f + 1` after the second. The refinement into TS 2 certifies
the specification's `excluded` and `grade` on the two instances' frozen cores.
One transfer lemma carries a count from a returned map down to a core below
it: `cnt_heavy_of_subMap` (AFW25 Lemma 13) says that a map heavy at `x` — all
but `f` of its entries — makes such a core heavy at `x` too, the core sitting
below the map and losing at most `f` entries to it.

A core has at least `n − f > 2f` entries, so at most one value is heavy in it,
and the three certificates are readings of that:

- the round's bound bit is `GBCA.boundOfCore` of the first instance's core —
  its heavy bit where one exists (`boundOfCore_of_heavy`), the complement
  being light (`cnt_boundOfCore_light`);
- the exclusion certificate is
  `ExcludedEv b = ∃ S, core₁ = some S ∧ cnt S b < |S| − f`. The core is
  write-once, so the certificate is frozen the moment it holds — monotonicity
  for free, where the direct implementation's refinement maintains monotone
  receipt walls;
- the A/C grade exclusivity is the second instance's core being heavy at
  `some v` on the A side and light at both bits on the C side.

The return rows then mirror `GBCASim.implRefines` shape for shape: a candidate
reaching the second gather is heavy in the first core (the invariant clause
`cand_heavy`, recorded when the link row computed the candidate, which refutes
a standing `ExcludedEv` for it), an `A`/`B` return hands out the bound bit and
certifies `ExcludedEv` of its complement, and the `C`-return announces the bit
the link already wrote. The D15 support counts come off the first core through
the committed-entry provenance — a core entry is a committed entry, a committed
entry of an honest process is its call, and the count is `F`-blind
(`supp_spec_of_core`) — or off an honest `⊥` candidate, which certifies `f + 1`
for both bits (`cand_bot`). Exclusions fire on demand as the two-step run
`bindUnset; ret`, as in the direct refinement.

## The chain-data export discipline

Each simulation exports its answers as *chain data* — a `List.IsChain` of
Dirac τ-steps of the abstract system, plus the final row's guards and the
relation at the end state — rather than as a finished weak run:

- `ABA/Broadcast/ImplSim.lean` exports `instRel_tau`, `instRel_call`,
  `commitReach`;
- `ABA/Gather/IdealSim.lean` exports `retRun`, `coreRel_call`, `coreRel_tau`,
  and the core equality `CoreRel.core_eq` the return labels are matched by;
- `ABA/Gather/LowSim.lean` exports `lowRel_call`, `lowTau_reach`, `lowRetRun`,
  and `LowRel.core_eq`.

A consumer one level up maps the chain into its own embedded rows with a
ten-line `chain_map` lemma (the rows of `idealInst`/`lowPairInst` carry the
component's row as a premise), splices chains where a fused row answers two
components (the `link` row), and closes with `Framework/WeakRun.lean`:
`weakLSilent_ofChain` for silent answers, `weakLStep_tausThen` for a chain
closed by an external step. This is why the wrapper simulations
(`ABA/Round/Substitutions.lean`) are two hundred lines
against the tiers' thousands: they replay, they do not re-prove.

## The assembly at the protocol shape (`AFW/Chain.lean`)

Three ingredients, none new to the chain:

- **The read-back congruence** (`ForwardSimulation.mapIdle`,
  `Framework/MapIdleSim.lean`): each per-round simulation lifts over
  `NLab P.n` along `GSub.gPull` with no further proof obligation — the τ
  round-trip is `gPull_tau`/`gPull_eq_tau`, and the congruence needs no
  section of the map (it relabels the witness execution per transition).
- **The family congruence** (`ForwardSimulation.family`): per-round
  simulations lift to the ℕ-indexed sides; the broadcast hypothesis is each
  relation's lockstep-corruption statement (`lowPairRel_corrupt`,
  `idealRel_corrupt`, `pairRel_corrupt`), exactly as `subSim_failAct`
  discharges it for the protocol chain.
- **The four congruences** (`parallel_right`, `abstract`, `relabel`,
  `abstract`): each family substitution runs under the composed reading's
  own context, the same term `ABDY/Hybrid.lean`'s `ABDY.substSim` uses, so the third
  stage's target is definitionally `hybrid P`.

The stages compose by `ProbabilisticForwardSimulation.trans`; the inclusions
compose by `Set.Subset.trans` and never invoke transitivity of simulation —
the two routes of `Results.lean`, reproduced.

## The protocol beneath the composed reading (`AFW/Flat.lean`, `AFW/FlatSim.lean`)

`AFW.composed P` is the gather-based protocol read as a composition of
components. What runs is a flat system: `n` programs, each reading its own
records and nothing else, beside one network adversary holding every sent set and
the corrupted set, beside the coin oracle. That shape is the same for either
implementation of graded agreement — the round loop, the DECIDED sets, the
coin handshake, corruption, the adversary's table and the composition pipeline
are fixed by the round interface and the specification — so `ABA/Reading/Flat.lean`
writes it once, parametric in the stage message type `M`, the per-process per-round
stage record `S`, the stage-side rows, supplied as a relation embedded in one
constructor of the program table, and the adversary's per-round ghost record
`G` with its update `ghostStep` and its output `ghostOut` (D30).
`ABA/ABDY/Protocol.lean` instantiates it at ABDY22's implementation;
`ABA/AFW/Flat.lean` instantiates it here.

The division of labour is by label. `Net.stageOwn j` is the set of label
classes an implementation owns at process `j`: the graded-agreement call and
return, `j`'s own stage multicast, a delivery addressed to `j`, and `j`'s call
against an already-opened record. An instantiation supplies `Net.IsStageTable`
— its rows carry such a label, fire only at an unreplaced program, and are
Dirac — and the shared inversion lemmas consume exactly those three facts.
`Net.stageRow_of_own` runs the argument the other way: a program's step on a
label of `stageOwn j` is a step of the implementation, which is what lets each
case of the simulation rule the others out.

Two rearrangements separate the flat stage side from the composed reading's,
and both are forced by the flat shape.

- **The tagged sent set.** A round of `AFW.composed` carries `4n + 2`
  network states — one per gather instance, one per Bracha instance. A flat
  adversary carries one sent-set family per round, so `AFW.Msg n` tags each
  message with the network state it belongs to, and for a Bracha message with the
  instance, whose index is its leader. The sender index stays the sender, so a
  threshold still counts distinct senders (D5). No new adversary rows are
  needed: recording a multicast, checking a delivery and authorising a handshake row are
  already payload-blind.
- **The transposition.** `Gather.LowState` indexes local states by instance and then
  by process. A program must hold its own data and no one else's, so
  `AFW.StageRec n` is process-major: process `j`'s local state in each gather
  instance, and its local state in each of the `n` instances of each broadcast family.
  Nothing is lost, because every guard of the gather-based implementation
  reads the acting process's own local states and the network states, and the two rows that
  read a network state — the adversary's delivery and its Byzantine injection —
  belong to the adversary either way.

`AFW.ProtocolRel` therefore has five conjuncts, not twenty: the round loop, the
coin oracle and the ABA-side network are shared objects, and the round family
is *computed* from the flat state by `AFW.toPair`, which undoes both
rearrangements — transposing the local states back and slicing each network state's sent set out
of the tagged family by `Finset.filterMap`. Four of the five are that
computation, so there is nothing to choose in the witness.

The ghost is part of that computation. The round instance carries three fields
no guard of it reads — the core of each of its two gather instances and the
round's bound bit — and the adversary holds the same three as the round's ghost
record `AFW.Ghost`, which `AFW.toPair` reads them off. Two rows write the
record. The link's broadcast of the candidate freezes the first gather's core at
`Gather.coreOf` of that gather's slice of the tagged sent sets, and the bound bit
at `GBCA.boundOfCore` of that core; a graded return freezes the second core the
same way. The composed `link` and `retG` freeze the same two values off the core
their embedded gather return carries, and the values agree because each is
`Gather.coreOf` of one network state (`coreOf_toLow1`, `coreOf_toLow2`).

The fifth conjunct, `AFW.BoundInv`, is the one clause that is not a reading of
the flat state, and it is what makes the announced bits agree: a process whose
round-`r` second-gather local state carries an input has passed that round's
link, so the round's bound bit is on record. The link is the only row that
extends the clause, and it writes the bit at the same moment.

The proof is organised around that computation. One master lemma,
`AFW.toPair_write`, says what a one-point stage write and a single sent set
insertion do to the view, pushing them inside all twelve coordinates; each row
of the implementation then owes only slice algebra — which of the six slices
takes the message, and which are untouched — discharged by `slice_post_some`
and `slice_post_none`. On that basis a send and a delivery are internal to the
round instance and are answered by one of its silent rules, the adversary's
authenticity conjunct becoming membership in the sliced sent set; the call and the
return are the instance's own. The remaining labels move the round loop and
the ABA-side network while the family of rounds stands still, and corruption
is one broadcast, the corrupted set the adversary holds being the corrupted
set of every network state under the same guard.

`ABA/AFW/FlatSim.lean` closes with the headlines mirroring `Results.lean`'s:
`AFW.protocol_composed`, `AFW.refines`, `AFW.main` and `AFW.chainSim`, each behind a
`#print axioms` check.

## Boundaries

- The union sends of the source's Algorithm 4 are read as bounds
  (`NOTES-Fidelity.md` §2); the widening is monotone in every guard the
  proofs consume.
- Liveness — gather Termination, BRB Totality — is unclaimed throughout
  (`NOTES-Fidelity.md` §6).
