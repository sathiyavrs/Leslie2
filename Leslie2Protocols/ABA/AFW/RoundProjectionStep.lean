/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.BroadcastSend
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ByzantineInjection
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.Delivery
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GatherAndBroadcastTransitions
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GatherSend
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GradedAgreementCall
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.OtherRoundsUnchanged
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProtocolRelationConjuncts
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ReturnThenCall
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The view of the composed round after one transition of the implementation

`AFW.roundProjection` (`ABA/AFW/RoundProjection.lean`) computes the round-`r` state
of the composed system from a state of `AFW.protocol P`. The files of
`AFW/RoundProjectionStep/` say where that state stands after one transition of the
implementation. `RoundProjectionStep/ViewAfterOneWrite.lean` is the write every transition
performs, read through the view. Each of the eight files then states, for its class of transitions,
the view after the transition as the view before it with the composed round's own effect applied,
written through the updaters `GBCA.ByAFW.setPrograms`, `GBCA.ByAFW.setBound`,
`GBCA.ByAFW.setFirstGather`, `GBCA.ByAFW.setSecondGather`, `Gather.setGatherTier`,
`Gather.setInputBroadcasts`, `Gather.setBindBroadcasts` and `Gather.setCore` exactly as the
composed transitions write them. Three transitions are matched by two events of the composed
round, through a named intermediate state: `RoundProjectionStep/ReturnThenCall.lean` holds two of
them and `RoundProjectionStep/Delivery.lean` the third.
`RoundProjectionStep/ProtocolRelationConjuncts.lean` holds the two conjuncts of
`AFW.ProtocolRelation` that no frame lemma supplies.
`ABA/AFW/SimulationOfEachTransition.lean` matches each transition of the implementation from
these.
-/
