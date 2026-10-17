/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.BroadcastReturn
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.BroadcastSend
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ByzantineInjection
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.Delivery
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.FirstGatherReturn
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GatherAndBroadcastTransitions
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GatherSend
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GradedAgreementCall
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.GradedReturn
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.InputBroadcastCall
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.OtherRoundsUnchanged
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProtocolRelationConjuncts
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.SecondGatherCall
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.SecondGatherReturn
import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# The projection of the composed round after one transition of the implementation

`AFW.roundProjection` (`ABA/AFW/RoundProjection.lean`) computes the round-`r` state
of the composed system from a state of `AFW.protocol P`. The files of
`AFW/RoundProjectionStep/` say where that state stands after one transition of the
implementation. `RoundProjectionStep/ProjectionAfterOneWrite.lean` is the write every transition
performs, read through the projection. Thirteen of the files beside it each state, for one
class of transitions, the projection after the transition as the projection before it with the
composed round's own effect applied, written through the updaters `GBCA.ByAFW.setPrograms`,
`GBCA.ByAFW.setNetwork`, `GBCA.ByAFW.setFirstGather`, `GBCA.ByAFW.setSecondGather`,
`Gather.setGatherProgramsAndNetwork`, `Gather.setInputBroadcasts` and `Gather.setCore` exactly as
the composed transitions write them. Each transition is matched by one
event of the composed round, the first gather's return by its return event followed by the round
network's `firstGatherCore` event. `RoundProjectionStep/ProtocolRelationConjuncts.lean` carries the
four conjuncts of `AFW.ProtocolRelation` that are not projections across a transition.
`ABA/AFW/SimulationOfEachTransition.lean` matches each transition of the implementation from
these.
-/
