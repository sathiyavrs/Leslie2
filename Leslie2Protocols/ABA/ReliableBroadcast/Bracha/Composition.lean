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
the instance-internal alphabet. `brachaInstance` hides the two synchronisation labels there and
reads the result back over the specification's alphabet `Label n M`: the leader's call, the
per-process returns and corruption. Both run on the composed state `BrachaState n M`, and
`brachaInstance_init` is the initial state they start from.

Every program transition and every network transition is Dirac, so the programs, the network and
the instance are each an LTS. No program transition fires on the silent label, so the instance's
silent transitions are the network's injections and the hidden synchronisations
(`programStep_no_tau`).
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
two synchronisation labels hidden, the result read back over the specification's alphabet. -/
noncomputable def brachaInstance (P : Parameters) (ldr : Fin P.n) (M : Type) [DecidableEq M] :
    System (BrachaState P.n M) (Label P.n M) :=
  ((brachaInstanceExtended P ldr M).abstract (broadcastEvents P.n M)).relabel

@[simp] theorem brachaInstance_init (P : Parameters) (ldr : Fin P.n) :
    (brachaInstance P ldr M).init = BrachaState.initial P.n M := rfl

/-! ### Determinacy

Every program transition and every network transition is Dirac, so the instance is an LTS. -/

/-- Every program transition is Dirac. -/
theorem programStep_dirac {P : Parameters} {ldr j : Fin P.n}
    {p : LocalState P.n (ProcessVariables M) (Message M)} {l : BroadcastLabel P.n M}
    {ν : PMF (LocalState P.n (ProcessVariables M) (Message M))} (h : ProgramStep P ldr j p l ν) :
    ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem networkStep_dirac {P : Parameters} {ldr : Fin P.n} {w : NetworkState P.n (Message M)}
    {l : BroadcastLabel P.n M} {μ : PMF (NetworkState P.n (Message M))}
    (h : NetworkStep P ldr w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem broadcastProgram_isLTS (P : Parameters) (ldr j : Fin P.n) :
    (broadcastProgram P ldr j (M := M)).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The network is an LTS. -/
theorem broadcastNetwork_isLTS (P : Parameters) (ldr : Fin P.n) :
    (broadcastNetwork P ldr M).IsLTS :=
  fun _ _ _ h => networkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem broadcastProgramProduct_isLTS (P : Parameters) (ldr : Fin P.n) :
    (System.synchronisedProduct (broadcastProgram P ldr (M := M))).IsLTS :=
  System.synchronisedProduct_isLTS (broadcastProgram_isLTS P ldr)

/-- The programs beside the network form an LTS. -/
theorem brachaInstanceExtended_isLTS (P : Parameters) (ldr : Fin P.n) :
    (brachaInstanceExtended P ldr M).IsLTS :=
  System.parallel_isLTS (broadcastProgramProduct_isLTS P ldr) (broadcastNetwork_isLTS P ldr)

/-- The instance is an LTS. -/
theorem brachaInstance_isLTS (P : Parameters) (ldr : Fin P.n) : (brachaInstance P ldr M).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (brachaInstanceExtended_isLTS P ldr) _)

/-- No program transition fires on `τ`: a program moves only on a synchronisation label or on one
of the instance's interface labels. The instance's silent transitions are therefore exactly the
network's injections and the hidden synchronisations. -/
theorem programStep_no_tau {P : Parameters} {ldr j : Fin P.n}
    {p : LocalState P.n (ProcessVariables M) (Message M)}
    {ν : PMF (LocalState P.n (ProcessVariables M) (Message M))}
    (h : ProgramStep P ldr j p (Silent.τ : BroadcastLabel P.n M) ν) : False := by
  rw [broadcastLabel_tau] at h; cases h

end BRB
end ABA
end PLTS
