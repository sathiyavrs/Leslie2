# Design — the decomposition of the gather-based chain

The gather-based chain runs over compositions at every level. A reliable-broadcast
instance is `n` programs beside the instance's network (`BRB.implInst`,
`ABA/ReliableBroadcast/BrachaComposition.lean`); a gather instance is `n` programs beside
the gather network, in parallel with `2n` broadcast instances read along pullbacks naming
them (`Gather.instAt`, `ABA/Gather/Composition.lean`); a round is `n` graded-agreement
programs beside the network of the graded-agreement layer, in parallel with two gathers
(`GBCA.ByAFW.roundInstAt`, `ABA/GBCA/AFW/Composition.lean`). The protocol chain's round,
`GBCA.ByABDY.sub` (`ABA/Composition/GBCAInstanceByABDY.lean`), is the template every level
copies: components synchronise on the instance's own events, the events are hidden, and
the result is read back over the instance's interface. `DESIGN-GatherTiers.md` is the
account of the stack; `DESIGN-Composition.md` is the account of what each component owns.

This note records five constraints the proofs impose on that shape. Each names
the statement that is false or unprovable without it, so that a reader can
tell a constraint from a convention.

## 1. The call loop is a label of its own

A specification answers its call label on two rows, the call and the
input-enabledness loop (`BRB.Step.call`, `BRB.Step.callLoop`;
`Gather.Step.call`, `Gather.Step.callLoop`). A composition splits the caller and
the network into components, and on one shared label each takes either row.
Two of the four combinations are behaviours of no row table: the leader loops
while the network posts `⟨INIT, m⟩`, and the leader records while the network
posts nothing. The first reaches a state whose network holds the message and
whose leader holds no input, which only `BRB.ImplStep.byz` produces and only
under `ldr ∈ F`.

**What fails.** The row characterisation stated label by label,
`implInst.step s l μ ↔ ∃ l₀, specPull l = some l₀ ∧ ImplStep s l₀ μ`, is
false: at the call label the right side admits the loop and the left side
offers the call alone, and at the loop label the reverse. The refinement into
the specification fails with it, since a second call with another payload would
let the specification record and commit a value the instance never broadcast.

**The constraint.** Each composition speaks an alphabet in which the loop is its own
label: `BRB.InstLab = Lab ⊕ Extra` with `Extra.callLoop m`, `Gather.InstLab = Lab ⊕ Extra`
with `Extra.callLoop id x`, and the round speaks `NLab` natively, whose `NetEvt.gcallLoop`
and `byzCallGLoop` are its loop labels. On the call label the caller has one row and the
network posts; on the loop label every component stands still. The specification is read
along a pullback that sends the loop to the call (`BRB.specPull`, `Gather.specPull`,
`GBCA.ByABDY.gPull`), so its own loop row answers the loop label. The level above pulls
the composition's alphabet back from its own (`Gather.inPull`, `Gather.bindPull`,
`GBCA.ByAFW.ga1Pull`, `GBCA.ByAFW.ga2Pull`). The row characterisation is then exact in the
form quantified over the interface labels:
`(∃ l, specPull l = some l₀ ∧ implInst.step s l μ) ↔ ImplStep s l₀ μ`
(`BRB.implInst_step_iff_row`, `Gather.idealInst_step_iff_row`,
`Gather.lowInst_step_iff_row`, `GBCA.ByAFW.pairInst_step_iff_row`).

## 2. The gather specification's call record follows the input instance

At the tier over broadcast specifications, the input broadcast of process `k`
is `BRB.liftedSpec` read along `inPull k`, and a specification answers the
gather's call and the gather's loop on either of its two rows. Over one
specification label the composition therefore has four call rows
(`Gather.IdealStep.call`, `callSpecLoop`, `callProcLoop`, `callLoop`): both
record, the program alone, the instance alone, neither.

**What fails.** A clause tying the gather program's input to the instance's
record is inductive in neither direction, since `callSpecLoop` writes the one
and `callProcLoop` the other. With `callProcLoop k x` followed by the
instance's commit of `x`, the state has `(brbIn k).val = some x`, no input at
`k`'s program and `k ∉ F`, and the return run must discharge the gather
specification's commit guard `k ∈ F ∨ call k = some x`. If the specification's
`call` tracked the program's input, that guard is false there, and
`Gather.gatherCore` is unprovable.

**The constraint.** `Gather.CoreRel.call_eq : ∀ k, t.call k = (brbIn s k).input`.
The specification's call record and an input instance's record move on the
same interface labels under the same write-once guard, so `coreRel_row` answers
`callProcLoop` with `Gather.Step.call` and `callSpecLoop` with
`Gather.Step.callLoop`. `Gather.IdealConf` carries no clause on the two records;
`coreRel_call` takes both guards. The permissiveness sits at a
specification-side tier: the concrete gather over Bracha has one row per label.

## 3. The composed program drops its grade on the graded return

`GBCA.ByAFW.ProcStep.retG` is guarded by `out = some out` and `returned = false` and
writes `out := none, returned := true`.

**What fails.** The flat link's relation computes the composed state from the flat one
(`AFW.toRound`), and the flat state keeps a process's grade in its round-loop record
alone, overwritten every round. A round's grade after its return is not recoverable from
the flat state. If the program's record kept the grade, `AFW.toProc` could not be a
function, `AFW.ProtocolRel` would lose the conjunct `t.1 = fun r => toRound P u w r`, and
every frame lemma of `ABA/ImplementationByAFW/RoundProjectionStep.lean`, which states the
view after a row as that function applied, would have no statement.

**The constraint.** The grade is held only between `ret2` and `retG`, inside a
run whose intermediate state is named (`AFW.afterRet2`) and related to no flat
state; `toProc` sets `out := none`; `GBCA.ByAFW.PairInv.out_cert` is vacuous for a
returned process.

## 4. A label outside a round's interface blocks the round

The round is read over `NLab` natively. A family label that is none of the
round's own — `callABA`, `retABA`, `callW`, `retW`, the protocol network's
rendezvous — must not be answered by every factor standing still.

**What fails.** If every pullback returned `none` on such a label, the round
would self-loop on it. The rendezvous have no specification label under
`GBCA.ByABDY.gPull`, so `GBCA.ByAFW.pairInst_step_row` is false there. The ABA and coin
labels have one, and `GBCA.Step` has no row at it, so
`GBCA.ByAFW.pairInst_step_iff_row` is false there and `GBCA.ByAFW.pairRefines` is
unprovable: `GBCA.ByABDY.liftedSpec` has no transition at those labels, and neither
has `GBCA.ByABDY.sub`.

**The constraint.** `GBCA.ByAFW.procPull` sends every off-interface family label to
`PLab.outside`, on which neither `GBCA.ByAFW.ProcStep` nor `GBCA.ByAFW.NetStep` has a row,
so the round blocks exactly where `GBCA.ByABDY.sub` blocks. `fail` alone maps to
`none`: the layer stands still on the round's own `fail` row, the gathers
corrupt, and in the family the label is answered by the broadcast act
(`AFW.gActLow`) and not by the instance.

## 5. The flat link carries the broadcast invariant on the composed side

The flat reading has no broadcast return: a gather guard reads an `n − f`
`VOTE` receipt quorum on the acting process's own local state in the instance
(`AFW.apIn1` and its companions). A composed gather program reads its store,
written on the instance's return event, whose guard is the same count. The view
defines a store as the value with a quorum on that local state, chosen
classically (`AFW.storeIn`).

**What fails.** A flat row hands its composed counterpart a specific value `x`
with a quorum; the composed row needs `delivIn k = some x`; the store holds the
value the view chose. The two coincide only if two vote quorums at one process
name one value. Without that fact the composed row's guard cannot be
discharged and `AFW.protocolSim` is unprovable. A store defined as a relation
rather than a function, filled inside the matching run, needs the same fact: an
earlier fill with another value would leave the instance returned and the
second value unreachable.

**The constraint.** `AFW.ProtocolRel` carries `AFW.StoreInv`, the invariant
`BRB.Inv` at every broadcast instance of the view, and
`AFW.storeIn_eq_of_quorum` reads the uniqueness off it through
`BRB.echoCert_of_vote_quorum` and `BRB.echoCert_unique`. The invariant holds
initially by `BRB.Inv.initial`, and after each matched row the view's instances
have moved by their own rows or stood still (`AFW.InvStep`), so `BRB.Inv.step`
re-establishes it. No invariant over the flat adversary's sent sets is written.
`storeIn` carries `[DecidableEq X]` explicitly, so its count is syntactically
the count `BRB.Inv` is stated on.

## Two consequences for the theory

`Framework/Congruence.lean` proves forward simulation between labelled
transition systems a congruence for parallel composition on either side, the
synchronised product of a finite family, hiding and restriction, with no
hypothesis that the systems are Dirac, and proves two simulations compose.
Contextual refinement therefore covers contexts built from `syncProduct` as
well as from `parallel`, `abstract`, `relabel`, `System.family` and
`System.mapIdle`. The substitutions inside a gather instance and inside a round
(`Gather.gatherLow`, `GBCA.ByAFW.lowPairRefines`, `GBCA.ByAFW.idealRefines`) are
applications of these congruences and of nothing else.

The `2n` broadcast instances of a gather and the two gathers of a round are
placed under `syncProduct` and `parallel` after a `mapIdle` lift along a
pullback naming each instance, so a label carrying another instance's index
leaves an instance standing still. A chain of binary parallel compositions
indexed by a symbolic `n` has no expression; the product of lifted instances is
what carries a family of instances.
