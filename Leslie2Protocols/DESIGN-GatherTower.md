# Design — the gather-based GBCA stack `GBCA.lowPairInst ⊑ … ⊑ GBCA.specInst` and its chain

Companion design document to the gather-based implementation of graded
agreement: the sub-protocol encodings (`ABA/Vocabulary/Fabric.lean`, `ABA/Broadcast/Spec.lean`,
`ABA/Broadcast/Impl.lean`, `ABA/Gather/Spec.lean`, `ABA/Gather/Ideal.lean`,
`ABA/Gather/Low.lean`), their refinements (`ABA/Broadcast/ImplSim.lean`,
`ABA/Gather/IdealSim.lean`, `ABA/Gather/LowSim.lean`), the two-gather round and its
three readings (`ABA/Round/Pair.lean`, `ABA/Round/Ideal.lean`, `ABA/Round/Low.lean`
and the three `*Sim` files), the assembly at the protocol shape
(`ABA/AFW/Chain.lean`), and the protocol beneath it (`ABA/AFW/Flat.lean`,
`ABA/AFW/FlatSim.lean`). The gather subsections of
`blueprint/src/content.tex` are a condensation of this document; the
deviations D24–D28 it realises are glossed in that file's registry, and the
source-fidelity items it rests on are §§2, 5 and 6 of `NOTES-Fidelity.md`.

## Systems

Per round, four systems over the shared round alphabet `Lab P.n`, three plain
forward simulations between them, and their probabilistic composite:

```
lowPairInst P r   -- two gather-over-Bracha instances: 2 fabrics + 4n Bracha instances
  ⊑ lowRefines        (broadcast substitution, componentwise)
idealInst P r     -- two gather-over-BRB.Spec instances
  ⊑ idealRefines      (gather substitution, componentwise)
pairInst P r      -- two Gather.SpecState coordinates + counting
  ⊑ pairRefines       (member-form counting into TS 2)
GBCA.specInst P r -- unchanged (GBCASpec.lean, D19)

gatherImplRefines P r : lowPairInst ⊑ specInst   (probabilistic, trans ×2)
```

Beneath the round, two standalone towers with their own alphabets, citable on
their own and consumed by the round through exported chain data:

```
BRB.implInst P ldr M ⊑ BRB.specInst P ldr M      (brbRefines, BRBSim.lean)
Gather.lowInst P X   ⊑ Gather.idealInst P X        (gatherLow, GatherLowSim.lean)
Gather.idealInst P X   ⊑ Gather.specInst P X       (gatherCore, GatherSim.lean)
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

## Why the gather specification carries a core family (D25)

The classical binding property of gather says: once the first correct process
returns, there is a set `S` of size `≥ n − f` such that every future correct
return is defined on `S`. TS 4 states this with a single `bind` set, written
once by an internal rule and read by every return. A forward simulation must
produce the abstract bind step at some concrete prefix state — no later than
the first return it answers — and the invariant must then keep every future
return above the chosen set. At `n = 3f + 1` no state predicate can do this
with a single `n − f`-sized set. Two natural routes both fail.

**The pigeonhole route fails.** At the first return's state, as few as
`n − 2f = f + 1` honest processes have cast their `VOTE`; the returner's
`n − f` quorum of BIND payloads contains only `f + 1` honest-at-that-state
members. Every argument that tries to cut a single `n − f`-sized entry set
out of that evidence needs an intersection bound of the form
`2(n − f) − n ≥ n − f`, i.e. `n ≥ 2f + something` beyond `3f < n` — at
`n = 3f + 1` the arithmetic closes only for sets of size `≥ n − f` *pairwise*,
never for their global intersection at a prefix.

**The sender-honesty route fails under dynamic corruption.** Quorum overlap
puts a common member behind any two `n − f` quorums, and with a *static*
adversary one argues: some common member is honest, its write-once payload
dominates both sides. Under D1 the adversary corrupts adaptively; the common
member may be corrupted *after* its sends, and a fabric multicast from a
sender corrupted later pins nothing — the injections of the now-corrupted
sender can put any payload beside it.

AFW25's Remark 1 says the same from above: for a gather without binding the
core set "is determined only in hindsight, and could be captured as a
prophecy variable". The `n − f`-sized single core is a fact about complete
executions. A specification whose internal rule must fire at a reachable
state can only bind what a reachable state determines.

**What a reachable state determines** is the family of committed BIND
payloads, and it satisfies a *pairwise* bound: each committed payload is
backed by an `n − f` VOTE receipt quorum; two such quorums share an honest
voter; that voter's vote is write-once and carries `≥ n − f` entries; and it
sits below both payloads. Hence:

- `Gather.SpecState.cores : Option (Finset (APSet n X))` — a write-once
  *family* of committed-entry sets, nonempty, any two members (each with
  itself, giving the size bound) sharing `≥ n − f` entries, every return
  dominating some member (`Gather.Step.bindCores`, `Gather.Step.ret`).
- The classical core is `⋂ cores`, of size `≥ n − f` once all honest votes
  are in — a complete-execution corollary, not a state invariant, and no
  statement of the development needs it: every consumer argument re-derives
  from the pairwise bound (see the counting section below).

**BIND travels by reliable broadcast** rather than on the gather fabric.
"Committed" must survive the sender's later corruption, and a BRB value is
write-once whatever happens to its sender afterwards. This is what makes the
family's members stable objects: `Gather.IdealState` holds one bind-BRB
instance per process (`brbBind`), the BIND send is that instance's call
(D28's fusion), and the certificate the simulation carries —
`f + 1 ≤ #{q | (brbBind q).val ∈ Cs}` — is F-blind, monotone, and immune to
corruption of the senders it counts.

**Producing and matching the family in the simulation** (`gatherCore`): a
return's `n − f` quorum of committed bind payloads contains `f + 1` members
honest at that state; their payloads form a family satisfying the pairwise
bound (fresh bind), and each dominates the output. When a family is already
bound, the return's quorum meets the `f + 1` certified coordinates in some
`q`; BRB values are functional, so the output dominates the standing member
at `q` and no second bind is needed.

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
`GatherSim` under an approval-reading row.

## Member-form counting at the pair tier (`pairRefines`)

`pairInst` is AFW25's Algorithm 4 at `R = 1` (D24): candidate at
`|dom g| − f` occurrences after the first gather, grade at
`|dom h| − f` / `f + 1` after the second. The refinement into TS 2 certifies
the specification's `dead` and `grade` on the two core families, and every
count is in *member form* — about family members, never about a global core:

- `cnt_heavy_of_subMap` (AFW25 Lemma 11, member form): a returned map heavy
  at `x` — all but `f` entries — makes every member of the family heavy at
  `x`, since the member sits below the map and loses at most `f` entries.
- `members_agree` (Proposition 12, member form): two members heavy at `x`
  and `y` share `≥ n − f ≥ 2f + 1` entries, of which at most `2f` miss a
  value; a common entry carries both, so `x = y`.
- `members_heavy_light` (Lemma 16 / A–C exclusivity): a member heavy at `x`
  leaves every value `≠ x` at most `f` entries on any member, through the
  shared entries again.

The exclusion certificate is
`DeadEv b = ∃ Cs, cores₁ = some Cs ∧ ∀ U ∈ Cs, cnt U b < |U| − f`. The
family is write-once, so the certificate is frozen the moment it holds —
monotonicity for free, where the direct implementation's refinement
maintains monotone receipt walls. The return rows then mirror
`GBCASim.implRefines` shape for shape: a candidate reaching the second
gather is heavy in the first family (refuting any standing `DeadEv` for it),
an `A`/`B` return certifies `DeadEv` of the other bit from its own map, the
`B`-return's `f + 1` dissent support is read off the `> f` non-candidate
entries of the returned map (each an honest caller or corrupted — the D15
form), and the `C`-return picks its killed bit by a case split on whether
some member is heavy at a bit. Kills fire on demand as the two-step burst
`bindUnset; ret`, unchanged from the direct refinement.

## The chain-data export discipline

Each simulation exports its answers as *chain data* — a `List.IsChain` of
Dirac τ-steps of the abstract system, plus the final row's guards and the
relation at the end state — rather than as a finished weak run:

- `BRBSim` exports `instRel_tau`, `instRel_call`, `commitReach`;
- `GatherSim` exports `retBurst`, `coreRel_call`, `coreRel_tau`;
- `GatherLowSim` exports `lowRel_call`, `lowTau_reach`, `lowRetBurst`.

A consumer one level up maps the chain into its own embedded rows with a
ten-line `chain_map` lemma (the rows of `idealInst`/`lowPairInst` carry the
component's row as a premise), splices chains where a fused row answers two
components (the `link` row), and closes with `Framework/WeakBurst.lean`:
`weakLSilent_ofChain` for silent answers, `weakLStep_tausThen` for a chain
closed by an external step. This is why the wrapper simulations
(`GBCAIdealSim`, `GBCALowSim`) are two hundred lines against the towers'
thousands: they replay, they do not re-prove.

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
records and nothing else, beside one network adversary holding every pool and
the corrupted set, beside the coin oracle. That shape is the same for either
implementation of graded agreement — the round loop, the DECIDED pools, the
coin handshake, corruption, the adversary's table and the composition pipeline
are fixed by the round interface and the specification — so `ABA/Reading/Flat.lean`
writes it once, parametric in three things: the stage message type `M`, the
per-process per-round stage record `S`, and the stage-side rows, supplied as a
relation embedded in one constructor of the program table. `ABA/ABDY/Protocol.lean`
instantiates it at ABDY22's implementation; `ABA/AFW/Flat.lean` instantiates it here.

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

- **The tagged pool.** A round of `AFW.composed` carries `4n + 2` message
  fabrics — one per gather instance, one per Bracha instance. A flat
  adversary carries one pool family per round, so `AFW.Msg n` tags each
  message with the fabric it belongs to, and for a Bracha message with the
  instance, whose index is its leader. The pool index stays the sender, so a
  threshold still counts distinct senders (D5). No new adversary rows are
  needed: pooling a multicast, checking a delivery and authorising a drive are
  already payload-blind.
- **The transposition.** `Gather.LowState` indexes boxes by instance and then
  by process. A program must hold its own data and no one else's, so
  `AFW.StageRec n` is process-major: process `j`'s box in each gather
  instance, and its box in each of the `n` instances of each broadcast family.
  Nothing is lost, because every guard of the gather-based implementation
  reads the acting process's own boxes and the fabrics, and the two rows that
  read a fabric — the adversary's delivery and its Byzantine injection —
  belong to the adversary either way.

`AFW.ProtocolRel` therefore has four conjuncts, not twenty: the round loop, the
coin oracle and the ABA-side network are shared objects, and the round family
is *computed* from the flat state by `AFW.toPair`, which undoes both
rearrangements — transposing the boxes back and slicing each fabric's pool out
of the tagged family by `Finset.filterMap`. The relation is a function, so
there is nothing to choose in the witness.

The proof is organised around that computation. One master lemma,
`AFW.toPair_write`, says what a one-point stage write and a single pool
insertion do to the view, pushing them inside all twelve coordinates; each row
of the implementation then owes only slice algebra — which of the six slices
takes the message, and which are untouched — discharged by `slice_post_some`
and `slice_post_none`. On that basis a send and a delivery are internal to the
round instance and are answered by one of its silent rules, the adversary's
authenticity conjunct becoming membership in the sliced pool; the call and the
return are the instance's own. The remaining labels move the round loop and
the ABA-side network while the family of rounds stands still, and corruption
is one broadcast, the corrupted set the adversary holds being the corrupted
set of every fabric under the same guard.

`ABA/AFW/FlatSim.lean` closes with the headlines mirroring `Results.lean`'s:
`AFW.protocol_composed`, `AFW.refines`, `AFW.main` and `AFW.chainSim`, each behind a
`#print axioms` firewall.

## Boundaries

- The union sends of the source's Algorithm 4 are read as bounds
  (`NOTES-Fidelity.md` §2); the widening is monotone in every guard the
  proofs consume.
- Liveness — gather Termination, BRB Totality — is unclaimed throughout
  (`NOTES-Fidelity.md` §6).
