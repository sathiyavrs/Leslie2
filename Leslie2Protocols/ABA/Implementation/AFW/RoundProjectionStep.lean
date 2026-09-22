/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.BroadcastSend
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.ByzantineInjection
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.Delivery
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.GatherAndBroadcastRows
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.GatherSend
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.GradedAgreementCall
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.OtherRoundsUnchanged
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.ProtocolRelationConjuncts
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.ReturnThenCall
import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# The view of the composed round after one implementation row

`AFW.roundProjection` (`ABA/Implementation/AFW/RoundProjection.lean`) computes the round-`r` state
of the composed system from a state of `AFW.protocol P`. The files of
`Implementation/AFW/RoundProjectionStep/` say where that state stands after one row of the
implementation. `RoundProjectionStep/ViewAfterOneWrite.lean` is the write every row performs, read
through the view. Each of the eight row files then states, for its class of rows, the view after
the row as the view before it with the composed round's own effect applied, written through the
updaters `GBCA.ByAFW.setPrograms`, `GBCA.ByAFW.setBound`, `GBCA.ByAFW.setFirstGather`,
`GBCA.ByAFW.setSecondGather`, `Gather.setGatherTier`, `Gather.setInputBroadcasts`,
`Gather.setBindBroadcasts` and `Gather.setCore` exactly as the composed rows write them. Three rows
are answered by two events of the composed round, through a named intermediate state:
`RoundProjectionStep/ReturnThenCall.lean` holds two of them and `RoundProjectionStep/Delivery.lean`
the third. `RoundProjectionStep/ProtocolRelationConjuncts.lean` holds the two conjuncts of
`AFW.ProtocolRelation` that no frame lemma supplies.
`ABA/Implementation/AFW/SimulationRows.lean` answers each row of the implementation from these.
-/
