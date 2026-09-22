/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.AFW.RoundProjection

/-!
# The two conjuncts of the protocol relation that are not projections

`BroadcastReturnsInvariant` and `BoundInvariant` are the conjuncts of `AFW.ProtocolRelation` that
no frame lemma supplies. `broadcastReturnsInvariant_of` carries the first across a row from the
moves of the round's `4n` broadcast instances, each an `InvariantStep` and so an application of
`BRB.Invariant.step`, and `broadcastReturnsInvariant_congr` covers a row that leaves every round's
view where it stands. `boundInvariant_writeGhost` carries the second, a process's second-gather
local input being written at the return-then-call step alone.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

/-! ### The two conjuncts that are not projections

`BroadcastReturnsInvariant` and `BoundInvariant` are the conjuncts of `AFW.ProtocolRelation` that no
frame lemma supplies. Each survives a row instance by instance: a broadcast instance either stands
still or takes a row of `BRB.BrachaStep`, which `BRB.Invariant.step` carries, and a process's
second-gather local input is written at the return-then-call step alone. -/

section Invariants

/-- One broadcast instance's move across a row: it is unchanged, or it takes a
row of `BRB.BrachaStep`. -/
def InvariantStep (P : Parameters) {M : Type} [DecidableEq M] (ldr : Fin P.n)
    (s s' : BRB.BrachaState P.n M) : Prop :=
  s' = s ∨ ∃ l, BRB.BrachaStep P ldr s l (PMF.pure s')

/-- An instance that is unchanged. -/
theorem InvariantStep.unchanged {M : Type} [DecidableEq M] (P : Parameters) (ldr : Fin P.n)
    (s : BRB.BrachaState P.n M) : InvariantStep P ldr s s := Or.inl rfl

/-- An instance that takes a row. -/
theorem InvariantStep.row {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} {l : BRB.Label P.n M}
    (h : BRB.BrachaStep P ldr s l (PMF.pure s')) : InvariantStep P ldr s s' := Or.inr ⟨l, h⟩

/-- **The broadcast invariant survives one instance's move.** -/
theorem InvariantStep.invariant {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}
    {s s' : BRB.BrachaState P.n M} (h : InvariantStep P ldr s s') (hInv : BRB.Invariant P ldr s) :
    BRB.Invariant P ldr s' := by
  rcases h with rfl | ⟨l, hl⟩
  · exact hInv
  · exact hInv.step hl (by simp)

/-- A row that moves one instance of a family: that instance takes its row and
every other instance is unchanged. -/
theorem invariantStep_update {M : Type} [DecidableEq M] {P : Parameters}
    (b : Fin P.n → BRB.BrachaState P.n M) (i : Fin P.n) (s' : BRB.BrachaState P.n M)
    {l : BRB.Label P.n M} (h : BRB.BrachaStep P i (b i) l (PMF.pure s')) (k : Fin P.n) :
    InvariantStep P k (b k) (Function.update b i s' k) := by
  by_cases hk : k = i
  · subst hk; rw [Function.update_self]; exact InvariantStep.row h
  · rw [Function.update_of_ne hk]; exact InvariantStep.unchanged P k (b k)

variable {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w v : NetworkState P.n}

/-- **The broadcast invariant survives a row**: at each of a round's `4n`
instances the state after the row is the state before it or a `BRB.BrachaStep`
successor of it. -/
theorem broadcastReturnsInvariant_of (hI : BroadcastReturnsInvariant P u w)
    (h1 : ∀ r k,
      InvariantStep P k (Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjection P u w r))
        k)
        (Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjection P x v r)) k))
    (h2 : ∀ r k,
      InvariantStep P k (Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjection P u w r)) k)
        (Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjection P x v r)) k))
    (h3 : ∀ r k,
      InvariantStep P k (Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjection P u w r))
        k)
        (Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjection P x v r)) k))
    (h4 : ∀ r k,
      InvariantStep P k (Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjection P u w r))
        k)
        (Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjection P x v r)) k)) :
    BroadcastReturnsInvariant P x v :=
  fun r k => ⟨(h1 r k).invariant (hI r k).1, (h2 r k).invariant (hI r k).2.1,
    (h3 r k).invariant (hI r k).2.2.1, (h4 r k).invariant (hI r k).2.2.2⟩

/-- A row that leaves every round's view where it stands keeps the broadcast
invariant. -/
theorem broadcastReturnsInvariant_congr (hI : BroadcastReturnsInvariant P u w)
    (h : ∀ r, roundProjection P x v r = roundProjection P u w r) :
    BroadcastReturnsInvariant P x v :=
  fun r k => by rw [h r]; exact hI r k

/-- The bound invariant survives a row that leaves every process's
second-gather local input where it stands and writes the ghost through
`AFW.ghostStep`. -/
theorem boundInvariant_writeGhost (hI : BoundInvariant P u w)
    (hx : ∀ i r,
      (((x i).2.roundRecord r).secondGather.process).input = (((u i).2.roundRecord
        r).secondGather.process).input)
    (hv : ∀ r, v.ghostRecord r = w.ghostRecord r) (L : ExtendedLabel P.n (Message P.n)) :
    BoundInvariant P x (v.writeGhost (ghostStep P) L) :=
  boundInvariant_of hI hx (fun r h => writeGhost_bound L (by rw [hv r]; exact h))

end Invariants

end AFW
end ABA
end PLTS
