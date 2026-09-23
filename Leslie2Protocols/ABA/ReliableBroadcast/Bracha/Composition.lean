/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Components
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The reliable-broadcast instance, composed

`BRB.brachaInstance`: one Byzantine Reliable Broadcast instance with designated leader `ldr` over
an arbitrary payload type `M`, assembled from the `n` per-process programs and the instance's
network of `ABA/ReliableBroadcast/Bracha/Components.lean`.

`brachaInstanceExtended` is the synchronised group of programs in parallel with the network, over
the instance-internal alphabet. `brachaInstance` hides the two rendezvous there and reads the
result back over the interface alphabet `InstanceLabel n M`, in which the instance's interface is
the leader's call, the per-process returns, corruption and the call loop. Both run on the composed
state `BrachaState n M`, and `brachaInstance_init` is the initial state they start from.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M]

/-- The programs beside the network, over the instance-internal alphabet. -/
noncomputable def brachaInstanceExtended (P : Parameters) (ldr : Fin P.n) (M : Type)
  [DecidableEq M] :
    System (BrachaState P.n M) (BroadcastLabel P.n M) :=
  (System.synchronisedProduct (broadcastProgram P ldr (M := M))).parallel (broadcastNetwork P ldr M)

/-- **The reliable-broadcast instance**: the programs beside the network, the
two rendezvous hidden, the result read back over the interface alphabet. -/
noncomputable def brachaInstance (P : Parameters) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (BrachaState P.n M) (InstanceLabel P.n M) :=
  ((brachaInstanceExtended P ldr M).abstract (broadcastEvents P.n M)).relabel

@[simp] theorem brachaInstance_init (P : Parameters) (ldr : Fin P.n) :
    (brachaInstance P ldr M).init = BrachaState.initial P.n M := rfl

end BRB
end ABA
end PLTS
