# Design — the decomposition of the gather-based chain

The gather-based chain runs over compositions at every level. A reliable-broadcast instance is `n`
programs beside the instance's network (`BRB.brachaInstance`,
`ABA/ReliableBroadcast/Bracha/Composition.lean`); a gather instance is `n` programs beside the
gather network, in parallel with `n` broadcast instances read along the pullback naming them
(`Gather.instanceOverBroadcasts`, `ABA/Gather/Composition.lean`); a round is `n` graded-agreement
programs beside the round's network, in parallel with two gathers (`GBCA.ByAFW.roundOverGathers`,
`ABA/GBCA/AFW/Composition.lean`). The ABDY chain's round, `GBCA.ByABDY.composition`
(`ABA/GBCA/ABDY/Composition.lean`), is the template every level copies: components
synchronise on the instance's own events, the events are hidden, and the result is read back over
the instance's interface. `DESIGN-GatherComposition.md` is the account of the stack;
`DESIGN-Composition.md` is the account of what each component holds.

This note records five constraints the proofs impose on that shape. Each names
the statement that is false or unprovable without it, so that a reader can
tell a constraint from a convention.

## 1. A call sends nothing

A specification takes its call label on two transitions, the call and the input-enabledness
loop (`BRB.Step.call`, `BRB.Step.callLoop`; `Gather.Step.call`, `Gather.Step.callLoop`). A
composition takes it on the program the call names: `BRB.ProgramStep.call` records the payload
at a leader holding no input, `BRB.ProgramStep.callLoop` leaves a leader holding one where it
stands, and the same pair stands at `Gather.ProgramStep`, `GBCA.ByABDY.GBCAProgramStep` and
`GBCA.ByAFW.ProgramStep`. Every other component takes the call label on a Dirac self-loop. A
program's first message is a send of its own, guarded by the recorded input: the leader's
`⟨INIT, m⟩` is `BRB.ProgramStep.sendInit`.

**What fails.** Let the call also post a message at the network. On the call label the leader
records or loops and the network posts in both cases, and the loop with the post is a behaviour
of no algorithm: it reaches a state whose network holds `⟨INIT, m'⟩` while the leader holds the
payload `m` of an earlier call, which only `BRB.BrachaAlgorithm.byzantine` produces and only
under `ldr ∈ F`. The characterisation by the algorithm, `brachaInstance.step s l μ ↔
BrachaAlgorithm s l μ`, is false at the call label, and the refinement into the specification
fails with it, since a second call with another payload would let the specification commit a
value the instance never broadcast.

**The constraint.** The network transitions on a call label are Dirac self-loops
(`BRB.NetworkStep.call`, `Gather.NetworkStep.call`, `GBCA.ByABDY.GBCANetworkStep.callG`,
`GBCA.ByAFW.NetworkStep.callG`), and the loop is a case of the algorithm on the call label
(`BRB.BrachaAlgorithm.callLoop` and its companions), so the characterisation holds label by
label: `BRB.brachaInstance_step_iff_algorithm`,
`Gather.instanceOverBroadcastSpecification_step_iff_algorithm`,
`Gather.instanceOverBracha_step_iff_algorithm`,
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm`. The guard of the loop on a filled
input is a convention: the specification's unguarded loop matches a program that drops a first
call, so no statement turns on it, and the guard makes the program's transition on its call
a function of its state, as at the ABA interface (D36).

## 2. The gather specification's call follows the gather's variables

At the composition over the broadcast specifications, the input broadcast of process `k` is
`BRB.specInst` read along `inputBroadcastLabelMap k`, which sends the event
`inputBroadcastCall k x` to that instance's call and the gather's own `call` to no image. The
instance takes that event on either of its two call transitions
(`Gather.AlgorithmOverBroadcastSpecification.inputBroadcastCall`, `inputBroadcastCallLoop`): it
records the payload, or it loops and nothing moves.

**What fails.** A clause tying the specification's call to an input instance's variables is
not inductive: `Gather.AlgorithmOverBroadcastSpecification.call` moves the gather's variables and
the specification's call on the one interface label and leaves every instance where it stands,
so right after a call the program holds `some x` and the instance holds `none`. A relation that
took the specification's call from the instance would be false there, and
`Gather.refinesSpecification` is unprovable.

**The constraint.** `Gather.SpecificationRelation.call_eq : ∀ k, t.call k = ((gatherProgramsAndNetwork s).processVariables
k).input`. The specification's call and the gather's variables move on the one interface label
under the one write-once guard, and `specificationRelation_call` takes that guard alone;
`specificationRelation_inputBroadcastCall` is matched by a stutter of the specification.
`Gather.Conformance.inputBroadcastCall_backed` carries the instance's variables back: the payload an
input instance of a correct process was called with is the payload that process's gather variables
hold. A return then discharges the gather specification's commit guard `k ∈ F ∨ call k = some x`
through `val_witness`, which bounds a committed specification entry by the instance's
commitment, `inputBroadcastVal_of_instanceInput`, which reads that commitment back to the
instance's call, and that clause, which reads the call back to the gather's variables.

## 3. The composed program drops its grade on the graded return

`GBCA.ByAFW.ProgramStep.retG` is guarded by `out = some out` and `returned = false` and
writes `out := none, returned := true`.

**What fails.** The simulation of the implementation into its composed system computes the composed
state from the implementation (`AFW.roundProjection`), and the implementation's state keeps a
process's grade in its round-loop variables alone, overwritten every round. A round's grade after
its return is not recoverable from the implementation's state. If the program's variables kept the
grade, `AFW.programProjection` could not be a function, `AFW.ProtocolRelation` would lose the
conjunct `t.1 = fun r => roundProjection P u w r`, and the lemmas of
`ABA/AFW/RoundProjectionStep/`, which state the projection after a transition as that
function applied, would have no statement.

**The constraint.** The grade is held only between `secondGatherReturn` and `retG`, inside a run
whose intermediate state is named (`AFW.afterSecondGatherReturn`) and related to no implementation
state; `programProjection` sets `out := none`; `GBCA.ByAFW.Invariant.out_witness` is vacuous for
a returned process.

## 4. A label outside a round's interface blocks the round

The round is read over `ExtendedLabel` natively. A family label that is none of the
round's own — `callABA`, `retABA`, `callW`, `retW`, the labels the protocol's
network synchronises on — must not leave every factor unchanged.

**What fails.** If every pullback returned `none` on such a label, the round
would self-loop on it. The synchronisation labels have no specification label under
`GBCA.specificationLabelMap`, so `GBCA.ByAFW.roundOverGatherSpecifications_step_algorithm` is false
there. The ABA and coin labels have one, and `GBCA.Step` has no transition at it, so
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm` is false there and
`GBCA.ByAFW.refinesSpecification` is unprovable: `GBCA.specificationOverRoundAlphabet` has no
transition at those labels, and neither has `GBCA.ByABDY.composition`.

**The constraint.** `GBCA.ByAFW.programLabelMap` sends every off-interface family label to
`ProgramLabel.outside`, on which neither `GBCA.ByAFW.ProgramStep` nor `GBCA.ByAFW.NetworkStep` has a
transition, so the round blocks exactly where `GBCA.ByABDY.composition` blocks. `fail` alone maps to
`none`: the round's programs remain unchanged on the round's own `fail` transition, the gathers
corrupt, and in
the family the label is taken by the broadcast act (`AFW.corruptionOverBracha`) and not by the
instance.

## 5. A broadcast instance's return is a transition of the implementation

A composed gather program reads what each of its instances returned, written on the instance's
return event under a `2f + 1` `VOTE` quorum at the receiver. The implementation holds the same
value: its round variables carry each gather local state over `Gather.ProcessVariables`, and
`AFW.RoundStep.firstGatherInputBroadcastReturn` and its companion at the second gather write it
under that same quorum. A gather guard of the implementation then reads those variables
(`Gather.ProcessVariables.accepted`, `Gather.approvedBy`, `Gather.holdsInputBroadcastReturn`)
and the received `BIND` messages, exactly as the guard of the composed gather program does.

**What fails without it.** Let the implementation keep no returned value and read a quorum on the
acting process's own local state in the instance instead. An implementation transition then hands
its composed counterpart a specific value `x` with a quorum, while the composed transition needs
`inputBroadcastReturned k = some x` for the value the instance returned. The two coincide only if
two vote quorums at one process name one value, so the relation has to carry `BRB.Invariant` at
each of a round's `2n` instances and re-establish it after every matched transition, and a
delivery completing a quorum is matched by the instance's delivery and then its return, a run of
two events. Every one of those obligations follows from not recording the return.

**The constraint.** The return is a transition, so the two guards are the one guard, the relation
carries no broadcast invariant, and each delivery is matched by one event.

## Two consequences for the theory

`Framework/Congruence.lean` proves forward simulation between labelled transition systems a
congruence for parallel composition in either position, the synchronised product of a finite family,
hiding and restriction, with no hypothesis that the systems are Dirac, and proves two simulations
compose. Contextual refinement therefore covers contexts built from `synchronisedProduct` as well as
from `parallel`, `abstract`, `relabel`, `System.family` and `System.mapIdle`. The substitutions
inside a gather instance and inside a round (`Gather.broadcastSubstitution`,
`GBCA.ByAFW.broadcastSubstitution`, `GBCA.ByAFW.gatherSubstitution`) are applications of these
congruences and of nothing else.

The `n` broadcast instances of a gather and the two gathers of a round are
placed under `synchronisedProduct` and `parallel` after a `mapIdle` lift along a
pullback naming each instance, so a label carrying another instance's index
leaves an instance unchanged. A chain of binary parallel compositions
indexed by a symbolic `n` has no expression; the product of lifted instances is
what carries a family of instances.
