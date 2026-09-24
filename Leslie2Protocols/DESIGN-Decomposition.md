# Design — the decomposition of the gather-based chain

The gather-based chain runs over compositions at every level. A reliable-broadcast instance is `n`
programs beside the instance's network (`BRB.brachaInstance`,
`ABA/ReliableBroadcast/Bracha/Composition.lean`); a gather instance is `n` programs beside the
gather network, in parallel with `2n` broadcast instances read along pullbacks naming them
(`Gather.instanceOverBroadcasts`, `ABA/Gather/Composition.lean`); a round is `n` graded-agreement
programs beside the round's network, in parallel with two gathers (`GBCA.ByAFW.roundOverGathers`,
`ABA/GBCA/AFW/Composition.lean`). The protocol chain's round, `GBCA.ByABDY.composition`
(`ABA/GBCA/ABDY/Composition.lean`), is the template every level copies: components
synchronise on the instance's own events, the events are hidden, and the result is read back over
the instance's interface. `DESIGN-GatherComposition.md` is the account of the stack;
`DESIGN-Composition.md` is the account of what each component owns.

This note records five constraints the proofs impose on that shape. Each names
the statement that is false or unprovable without it, so that a reader can
tell a constraint from a convention.

## 1. The call loop is a label of its own

A specification answers its call label on two transitions, the call and the
input-enabledness loop (`BRB.Step.call`, `BRB.Step.callLoop`;
`Gather.Step.call`, `Gather.Step.callLoop`). A composition splits the caller and
the network into components, and on one shared label each takes either transition.
Two of the four combinations are behaviours of no algorithm: the leader loops
while the network posts `⟨INIT, m⟩`, and the leader records while the network
posts nothing. The first reaches a state whose network holds the message and
whose leader holds no input, which only `BRB.BrachaAlgorithm.byzantine` produces and only
under `ldr ∈ F`.

**What fails.** The characterisation by the algorithm stated label by label,
`brachaInstance.step s l μ ↔ ∃ l₀, specificationLabelMap l = some l₀ ∧ BrachaAlgorithm s l₀ μ`,
is false: at the call label the right-hand
side admits the loop and the left-hand side offers the call alone, and at the loop label the
reverse. The refinement into the specification fails with it, since a second call with another
payload would let the specification record and commit a value the instance never broadcast.

**The constraint.** Each composition speaks an alphabet in which the loop is its own
label: `BRB.InstanceLabel = Label ⊕ LoopLabel` with `LoopLabel.callLoop m`,
`Gather.InstanceLabel = Label ⊕ LoopLabel`
with `LoopLabel.callLoop id x`, and the round speaks `ExtendedLabel` natively, whose
`NetworkEvent.gbcaCallLoop` and `byzantineCallGLoop` are its loop labels. On the call label the
caller has one transition and the network posts; on the loop label every component is unchanged.
The specification is read along a pullback that sends the loop to the call
(`BRB.specificationLabelMap`, `Gather.specificationLabelMap`, `GBCA.specificationLabelMap`),
so its own loop transition answers the loop label. The level above pulls the composition's alphabet
back from its own (`Gather.inputBroadcastLabelMap`, `Gather.bindBroadcastLabelMap`,
`GBCA.ByAFW.firstGatherLabelMap`, `GBCA.ByAFW.secondGatherLabelMap`). The characterisation by the
algorithm is then exact in the form quantified over the interface labels: `(∃ l,
specificationLabelMap l = some l₀ ∧ brachaInstance.step s l μ) ↔ BrachaAlgorithm s l₀ μ`
(`BRB.brachaInstance_step_iff_algorithm`,
`Gather.instanceOverBroadcastSpecification_step_iff_algorithm`,
`Gather.instanceOverBracha_step_iff_algorithm`,
`GBCA.ByAFW.roundOverGatherSpecifications_step_iff_algorithm`).

## 2. The gather specification's call record follows the gather record

At the tier over broadcast specifications, the input broadcast of process `k` is
`BRB.specificationOverInstanceAlphabet` read along `inputBroadcastLabelMap k`, which sends the
event `inputBroadcastCall k x` to that instance's call and the gather's own `call` and call loop to
no image. The instance answers that event on either of its two call transitions
(`Gather.AlgorithmOverBroadcastSpecification.inputBroadcastCall`,
`inputBroadcastCallSpecificationLoop`): it records the payload, or it loops and nothing moves.

**What fails.** A clause tying the specification's call record to an input instance's record is
not inductive: `Gather.AlgorithmOverBroadcastSpecification.call` moves the gather record and the
specification's call record on the one interface label and leaves every instance where it stands,
so right after a call the program holds `some x` and the instance holds `none`. A relation that
read the specification's call record off the instance would be false there, and
`Gather.refinesSpecification` is unprovable.

**The constraint.** `Gather.SpecificationRelation.call_eq : ∀ k, t.call k = ((gatherTier s).process
k).input`. The specification's call record and the gather record move on the one interface label
under the one write-once guard, and `specificationRelation_call` takes that guard alone;
`specificationRelation_inputBroadcastCall` is matched by a stutter of the specification.
`Gather.Invariant.inputBroadcastCall_backed` carries the instance's record back: the payload an
input instance of a correct process was called with is the payload that process's gather record
holds. A return then discharges the gather specification's commit guard `k ∈ F ∨ call k = some x`
through `val_certificate`, which bounds a committed specification entry by the instance's
commitment, `inputBroadcastVal_provenance`, which reads that commitment back to the instance's call
record, and that clause, which reads the call record back to the gather record.

## 3. The composed program drops its grade on the graded return

`GBCA.ByAFW.ProgramStep.retG` is guarded by `out = some out` and `returned = false` and
writes `out := none, returned := true`.

**What fails.** The simulation of the implementation into its composed system computes the composed
state from the implementation (`AFW.roundProjection`), and the implementation's state keeps a
process's grade in its round-loop record alone, overwritten every round. A round's grade after its
return is not recoverable from the implementation's state. If the program's record kept the grade,
`AFW.programProjection` could not be a function, `AFW.ProtocolRelation` would lose the conjunct `t.1
= fun r => roundProjection P u w r`, and the frame lemmas of
`ABA/AFW/RoundProjectionStep/`, which state the view after a transition as that
function applied, would have no statement.

**The constraint.** The grade is held only between `secondGatherReturn` and `retG`, inside a run
whose intermediate state is named (`AFW.afterSecondGatherReturn`) and related to no implementation
state; `programProjection` sets `out := none`; `GBCA.ByAFW.Invariant.out_certificate` is vacuous for
a returned process.

## 4. A label outside a round's interface blocks the round

The round is read over `ExtendedLabel` natively. A family label that is none of the
round's own — `callABA`, `retABA`, `callW`, `retW`, the protocol network's
rendezvous — must not be answered by every factor unchanged.

**What fails.** If every pullback returned `none` on such a label, the round
would self-loop on it. The rendezvous have no specification label under
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
the family the label is answered by the broadcast act (`AFW.corruptionOverBracha`) and not by the
instance.

## 5. A broadcast instance's return is a transition of the implementation

A composed gather program reads what each of its instances returned, written on the instance's
return event under a `2f + 1` `VOTE` quorum at the receiver. The implementation holds the same
record: its round record carries each gather local state over `Gather.ProcessRecord`, and
`AFW.RoundStep.firstGatherInputBroadcastReturn` and its three companions write it under that same
quorum. A gather guard of the implementation then reads the record
(`Gather.ProcessRecord.accepted`, `Gather.approvedBy`, `Gather.holdsInputBroadcastReturn`,
`Gather.holdsBindBroadcastReturn`), exactly as the guard of the composed gather program does.

**What fails without it.** Let the implementation keep no returned value and read a quorum on the
acting process's own local state in the instance instead. An implementation transition then hands
its composed counterpart a specific value `x` with a quorum, while the composed transition needs
`inputBroadcastReturned k = some x` for the value the instance returned. The two coincide only if
two vote quorums at one process name one value, so the relation has to carry `BRB.Invariant` at
each of a round's `4n` instances and re-establish it after every matched transition, and a
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

The `2n` broadcast instances of a gather and the two gathers of a round are
placed under `synchronisedProduct` and `parallel` after a `mapIdle` lift along a
pullback naming each instance, so a label carrying another instance's index
leaves an instance unchanged. A chain of binary parallel compositions
indexed by a symbolic `n` has no expression; the product of lifted instances is
what carries a family of instances.
