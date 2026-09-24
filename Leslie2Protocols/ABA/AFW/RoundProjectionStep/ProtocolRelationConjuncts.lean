/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjection

/-!
# The conjunct of the protocol relation that is not a projection

`BoundInvariant` is the conjunct of `AFW.ProtocolRelation` that no frame lemma supplies.
`boundInvariant_writeGhost` carries it across a transition that leaves the candidate, the second
gather's input and the graded outcome where they stand and writes the ghost.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

variable {P : Parameters}

/-! ### The conjunct that is not a projection

`BoundInvariant` is the conjunct of `AFW.ProtocolRelation` that no frame lemma supplies. It reads
the candidate, the second gather's input and the graded outcome, so a transition that leaves the
three where they stand and writes the ghost keeps the conjunct. -/

section Invariants

variable {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w v : NetworkState P.n}

/-- The bound invariant survives a transition that leaves the three fields it reads where they
stand and writes the ghost through `AFW.ghostStep`. -/
theorem boundInvariant_writeGhost (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundRecord r).candidate = ((u i).2.roundRecord r).candidate)
    (hinput : ∀ i r,
      (((x i).2.roundRecord r).secondGather.process).input = (((u i).2.roundRecord
        r).secondGather.process).input)
    (hout : ∀ i r, ((x i).2.roundRecord r).output = ((u i).2.roundRecord r).output)
    (hv : ∀ r, v.ghostRecord r = w.ghostRecord r)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) :
    BoundInvariant P x (v.writeGhost (ghostStep P) L) :=
  boundInvariant_of hI hcand hinput hout
    (fun r h => writeGhost_bound L (by rw [hv r]; exact h))

end Invariants

end AFW
end ABA
end PLTS
