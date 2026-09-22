/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.CallABA
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.CallG
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.CallW
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.Fail
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.GBCATau
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.RetABA
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.RetG
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.RetW
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.RoundLoopTau
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.SpecificationStateCorruption
import Leslie2Protocols.ABA.HybridRefinesSpecification.InvariantPreservation.StepInversion

/-!
# Step inversion and `Invariant` preservation for `hybrid`

Stages A and B of the proof that `hybridSpecificationStateRelation` is a simulation relation
(`DESIGN-HybridRefinesSpecification.md`), on top of the relation and invariant of
`HybridRefinesSpecification/Relation.lean`. `InvariantPreservation/StepInversion.lean` holds Stage
A, the step inversion for `hybrid`, and `InvariantPreservation/SpecificationStateCorruption.lean`
the readings of corruption at a specification state that the `fail` row consumes. Stage B, the
preservation of `Invariant`, is one file per label class, each carrying all forty invariant fields
across the rows of its class. `HybridRefinesSpecification/AbstractStatePreservation.lean` assembles
the two stages into `Invariant.step`, beside the `AbstractState` stutter lemmas it is stated with.
-/
