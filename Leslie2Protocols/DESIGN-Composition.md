# Composition — why the chains are cut where they are

The ABA case study relates two protocols, each as it runs, to one small specification:

```
ABDY.protocol  ⊑  ABDY.composed                                  ⊑  hybrid  ⊑  ABA.spec
 AFW.protocol  ⊑   AFW.composed  ⊑  AFW.hybrid1  ⊑  AFW.hybrid2  ⊑  hybrid  ⊑  ABA.spec
```

A protocol is what runs: `n` programs beside a network adversary and a coin oracle. A
program reads its own replacement flag and nothing else about corruption: not the corrupted
set, not the budget, not another process's status (D23). A composed reading is the same
protocol read as a composition of components. `hybrid` replaces each round's
graded-agreement instance by the graded agreement specification, and is where the two chains
meet: every link above it is shared. `ABA.spec` is the single-automaton reading of
agreement.

The two protocols differ only in how graded agreement is implemented. `ABDY.protocol` runs
ABDY22's Algorithm 6 (D18), which calls no sub-protocol, so one substitution takes it to
`hybrid`. `AFW.protocol` runs AFW25's two-gather construction over reliable broadcast (D24),
so the recursion continues two levels further and its chain carries three.

This note records why the cut is placed where it is, what it buys, and what the model
already weakens. The systems themselves are in `ABA/ABDY/Protocol.lean`, `ABA/AFW/Flat.lean`
and `ABA/Spec/ABA.lean`; `ABA/ABDY/Hybrid.lean` carries `ABDY.composed` and `hybrid` over the
components of `ABA/ABDY/Components.lean`, and `ABA/AFW/Chain.lean` carries the three
gather-based stages. The first links are `ABA/ABDY/ProtocolSim.lean` and
`ABA/AFW/FlatSim.lean`. The file guide is `ABA/README.md`, and the gather stack's own proofs
are `DESIGN-GatherTiers.md`.

## The first link

The first link is where a chain passes from implementation to specification: a protocol is
the system that runs, and everything above it is specification. Both first links are
therefore inclusions, `ABDY.protocol_composed` and `AFW.protocol_composed`, and not
equalities.

The two protocols are one construction. What a protocol reading fixes — the round loop, the
DECIDED sets, the coin handshake, corruption, the network adversary and the composition
pipeline — is settled by the round interface and the specification, so `ABA/Reading/Flat.lean`
writes it once, parametric in the stage message type, the per-process per-round stage record,
the stage-side rows and the adversary's per-round ghost record (D30). `ABA/ABDY/Protocol.lean`
and `ABA/AFW/Flat.lean` supply the two instances.

A process record of a protocol carries the round-loop record beside the stage record of every
round the process has touched, and a flag saying whether the process has terminated (D22). A
composed state carries one graded-agreement instance per round at every moment, and no
termination flag. `ABDY.ProtocolRel` and `AFW.ProtocolRel` pin every composed coordinate
against the protocol state: a round instance's local states are the stage records the
processes hold for that round, and its network states are the adversary's sent sets for it.
Those conjuncts are unguarded, so a composed state is determined by any protocol state
related to it. `AFW.ProtocolRel` carries one further conjunct, `AFW.BoundInv`, which is not
a reading of the protocol state: a round whose second gather has been called has its bound
bit on record, which is what the graded return's announced bit rests on.

What makes each link one-directional is on the composed side, and it is the same on both. A
round instance has a row for the Byzantine graded-agreement rows and no program of a protocol
has one (D11), and the instance's stage rules carry no termination guard, so the instance
answers a send or a delivery at a process the protocol has terminated.

## What the composition buys

A sub-protocol is swappable exactly when its component boundary owns its network.

Giving each round its own network is what makes the round a component, and a
component can be replaced. The substitution is one family congruence and one parallel
precongruence, then `abstract`, `relabel`, `abstract` to run the composition pipeline
out. Nothing else in the chain is touched.

That is a modular axis rather than a one-off. Varying the power of the network —
losses, reordering, a different forgery model — is a change inside the round instance,
swapped in by the same precongruence. Exchanging the whole implementation of graded agreement
is that same move at that same place, which is what the second chain is.

Idealizing the round also exposes an asymmetry worth naming. The round's sent sets, its
delivery guards and its injections die with the graded-agreement idealization. The
DECIDED sets, the corruption budget and the authorisation `k ∈ F` of every Byzantine
handshake row survive it, at the ABA-side network. What a component owns is what disappears with
it.

## The gather-based chain

The gather-based implementation applies that device three more times, inside the round,
before the round itself is exchanged at `hybrid`.

One record shape carries every level. `ABA.SubState n Pr M` is `n` local states beside one
network state `ABA.NetworkState n M`, which holds the per-sender sent sets and the corrupted set
and nothing else (D5). Bracha's instance is `BRB.ImplState`, that shape at the broadcast
message type; a gather instance holds its own in the field `ga`; and `GBCA.ImplState` is the
ABDY22 analogue, the stage records beside the round's network state. A sub-protocol
implementation here is always local states beside the one network state it owns.

A round is two gather instances beside the round's bound bit, at each of the three tiers:

```
GBCA.LowPairState n = Gather.LowState   n Bool × Gather.LowState   n (Option Bool) × Option Bool
GBCA.IdealState   n = Gather.IdealState n Bool × Gather.IdealState n (Option Bool) × Option Bool
GBCA.PairState    n = Gather.SpecState  n Bool × Gather.SpecState  n (Option Bool) × Option Bool
```

and a gather instance carries its own network state beside the `2n` broadcast instances its
payloads travel by. `Gather.LowState` holds `ga` beside `2n` Bracha instances, `n` carrying the
entries and `n` the `BIND` payloads; `Gather.IdealState` holds `ga` beside the same `2n` at
broadcast specifications; and `Gather.SpecState` holds
no network state at all — the call records, the committed entries, the return flags, the core
and the corrupted set.

Three substitutions take one tier to the next, and each removes exactly what the component it
replaces owned.

- `GBCA.lowRefines` replaces each of the round's `4n` Bracha instances by a broadcast
  specification, componentwise through `Gather.gatherLow`. The Bracha network states die;
  what survives of each is the committed value, written once.
- `GBCA.idealRefines` replaces each gather-over-broadcast instance by the gather
  specification, componentwise through `Gather.gatherCore`. A gather's own network state and
  the `2n` broadcast specifications beneath it die together; what survives is the per-entry
  committed record and the frozen core.
- `GBCA.pairRefines` replaces the two-gather round by `GBCA.specInst`. The two gather
  specifications die; what survives is `excluded` and `grade`.

Each of those tiers is a single rule table over a product state rather than a composition, so
a round's network states are fields of one system and not components of one (D28), where the
protocol chain's round is the `n` stage programs beside `GSub.gNet`. Bringing the two chains
to one shape is the subject of `TODO-Decomposing-AFW-Composed.md`.

The round's bound bit is the third factor at every tier and is the gather-side counterpart of
`GSub.GNetState.bound`. It is written at the `link` row from the first gather's core, no
program reads it, and it meets the specification only at the last of the three substitutions,
where `GBCA.PairRel` ties it to `excluded`. The frozen core plays the same part one level
down: it is a field of `Gather.LowState` and of `Gather.IdealState` that no process reads and
no guard consults, and the gather specification's own core is the value its return labels
announce (D29).

Which component owns a payload is a design decision and not bookkeeping. A gather's `BIND`
payloads travel by reliable broadcast rather than on the gather network, so a committed
payload is write-once whatever later happens to its sender. A payload held in a network
is pinned only by its sender's honesty, and D1 withdraws that at any moment. The decision is
legible in the message types: `Gather.GaMsg` carries `echo` and `vote` and no `BIND`
constructor, and at the protocol a bind payload is tagged `brbBind1` or `brbBind2`, a
broadcast instance's message rather than a gather's. The counting argument the choice enables
is `DESIGN-GatherTiers.md`.

At the protocol shape the three stages are `AFW.composed ⊑ AFW.hybrid1 ⊑ AFW.hybrid2 ⊑
hybrid`, each the four congruences applied to one family substitution under a single context
term:

```
(((SIDE.parallel ((System.syncProduct (coreProcN P)).parallel
                  ((aNet P).parallel (wccLift P)))).abstract
    (netEvtLabels P.n)).relabel).abstract (Lab.hiddenAPI P.n)
```

`SIDE` is the family of round tiers — `AFW.lowSide`, `AFW.idealSide`, `AFW.pairSide` — and
`GSub.gbcaSide` and `specSide` stand in the same position in the other chain. The context
term is the same expression in all five, which is why the third stage's target is `hybrid P`
itself and why the two chains meet there.

Beneath `AFW.composed` the protocol collapses the round's `4n + 2` network states into the
one sent-set family the adversary holds, tagging each message with the instance it belongs
to: `AFW.Msg` carries a constructor per layer, `ga1`, `ga2`, `brbIn1`, `brbBind1`, `brbIn2`
and `brbBind2`. `AFW.StageRec` is the composed reading's instance-major indexing transposed,
one process's local state in each of those instances, and `AFW.Ghost` is the adversary's
record for one round, the two frozen cores beside the bound bit.

## Where each network is external

No network is internal to a process, and none is a field of a process record.

Both chains carry the ABA-side DECIDED network `Comp.aNet`. It is a component of every system
of both chains and the second component of `ABAState`, the state `coreRel` is defined on, and
neither chain idealizes it.

Below that the two chains own different things. ABDY22's carries one further network, the
round's network `GSub.gNet`, a component of `ABDY.composed` and of `hybrid`, which
disappears at the substitution inside the component that is exchanged. It is also the second
component of `GBCA.ImplState`, the state the round refinement is defined on. It carries one
field that is not a message set: the round's bound bit, the value the round's graded returns
announce on their labels (D29). The field is a ghost — no program reads it, and the three
return rows are the only rows that touch it — and it belongs to the round for the same reason
the sent sets do, so it disappears with the round at the substitution.

The gather-based chain carries `4n + 2` of them per round: one for each gather instance, and
one for each of the `4n` broadcast instances beneath the two. They disappear in two stages
rather than one, the broadcast networks at `GBCA.lowRefines` and the gather networks
at `GBCA.idealRefines`, each inside the component being exchanged.

Every invariant therefore reads its network through accessors on a pair — the
`GBCA.ImplState` accessors in `ABA/ABDY/Impl.lean`, the `ABAState` accessors in
`ABA/ABDY/ABAState.lean`, the `ABA.SubState` accessors in `ABA/Vocabulary/NetworkState.lean` —
and names the network's own sent sets rather than a copy of them held inside a record.
Weakening any one of them is a change to that one component.

The ghost field of the network is removable, and `ABA/Reading/Erase.lean` removes it. The
ghost-free reading `Net.flat₀` is the flat reading over a one-element ghost record, its two
graded-agreement return rows free to announce either bit; the map that drops the record is
a state erasure of the adversary onto it (`Framework/Erasure.lean`), and the congruences of
that file carry the erasure through the same pipeline the composition is built by — the
coin oracle, the process group, the rendezvous hiding and the restriction. Hiding
`Lab.hiddenAPI` collapses the label identification the erasure runs on, since every label it
moves is a `retG`, so `ABDY.protocol_erasure` and `AFW.protocol_erasure` are equalities of
achievable trace distributions with no map on labels in them. The bound bit is therefore a
field the chain may keep or drop, and the choice to keep it is a choice about what the
invariants read, not about what the protocol does.

## Every state is a component's own record or a product of them

The property holds across the development, and a reader should not have to re-derive it.

Each leaf record holds exactly one local state's data: `ProcCore` and `CoreRec` for a round loop,
`GBCA.ProcState` and `GBCA.StageRec` for a graded-agreement stage, `Net.StageSideRec` and
`AFW.StageSideRec` for the stage side of one process, `GSub.GNetState` for a round's network
state beside its bound bit, `ABA.NetworkState` for the network state of any other sub-protocol
instance, `Comp.ANetState` for the DECIDED network, and one `SpecState` for each of the five
specifications. Each composite state is an explicit product of those: `Net.ProcRec`,
`AFW.ProcRec`, `ABA.SubState`, `GBCA.ImplState`, `ABAState`, `Comp.ComposedState` and
`HybridState` on one side, and `Gather.LowState`, `Gather.IdealState`, `GBCA.LowPairState`,
`GBCA.IdealState`, `GBCA.PairState` and `AFW.StageRec` on the other.

One record holds two kinds of message set at once, and it is the right one to.
`Net.NetState` (`ABA/ABDY/Protocol.lean`) and `AFW.NetState` (`ABA/AFW/Flat.lean`) carry the
stage sent sets, the DECIDED sets and the corrupted set together, because each is the network
adversary of a protocol — the subject of a chain, not a vehicle for proving anything about
it. Each carries one ghost record per round beside them (D30), for the same reason: the value
a graded return announces is determined by the round's messages and the corrupted set, which
this record holds. The flat reading of `ABA/Reading/Flat.lean` is parametric in that record's
type, its update `ghostStep`, applied on every row to the round the label names, and its
output `ghostOut`, which the two graded-agreement return rows read. What a row reads there is
the value its label announces, not whether it fires: the read admits a bit at every state
(`ghostOut_total`), which is what makes the record erasable.
`ABDY.protocol_composed` and `AFW.protocol_composed` carry those readings into ones where
each round owns its network states beside `Comp.ANetState`, and every step above the first
link runs there. A round's ghost record is the composed reading of the values the round's own
state holds, which is one conjunct of each protocol relation.

## What the DECIDED model already weakens

The ABA-side network is the one neither chain idealizes, so what it assumes is what the
development assumes. Much of the weakening one might ask for is already in it.

`dsent` is a `Finset`, so there is no delivery order to disturb. Receipts are sets too and
`CoreRec.recvDec` files by insertion, so a repeated delivery of one (receiver, sender,
bit) triple carries no information: `Comp.ANetStep.ddlv` consumes nothing, and the
receiver's `Comp.CoreProcStepN.ddlvRecv` declines the repeat under `b ∉ decIn k` rather
than taking a step that would change no state. Duplication is immaterial here, not assumed
away.

No rule forces a delivery, so any subset of the multicasts may be lost. `byzD` injects
either bit for any `k ∈ F`, so a corrupted process may equivocate in the DECIDED sets.
`Comp.ANetStep.retByz` lets a corrupted process return either bit at any time with no
DECIDED evidence at all, its round-loop half being the self-loop of the replaced program
(D23), so the DECIDED quorum is a condition on honest returns alone.

What remains assumed is unforgeability of an honest process's DECIDED multicast. The
delivery guard `b ∈ dsent j` attributes every receipt to a genuine send by the named
sender, and no rule lets one process record a send under another's name.
