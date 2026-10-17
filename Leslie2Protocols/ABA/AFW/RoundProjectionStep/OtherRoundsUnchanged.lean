/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# Every other round is unchanged

`roundProjection_otherTransition` and its three companions: the rounds a transition does not name
read exactly as the transition found them. The acting process's variables in its other rounds are
untouched, and the adversary's sent sets and its ghost are written at one round only, through the
accessors `sent r` and `ghost r` of their finite maps. `toRoundFamily`, `toRoundFamilyNoSent` and
`toRoundFamilySent` state a transition's effect on the whole family of rounds through the family's
accessor: where every round of the family is the projection before the transition, every round of
the family with round `r` set to the projection of round `r` after it is the projection after it
(`setInstanceState_roundProjection`).
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

variable {P : Parameters}

section Transitions

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}

/-! ### Every other round is unchanged

A transition names one round. The rounds it does not name read exactly as they did:
the acting process's variables in its other rounds are untouched, the adversary's sent
family is written at one round only, and so is its ghost. -/

/-- The projection of a round the transition does not name. -/
theorem roundProjection_otherTransition (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr :
  RoundVariables P.n)
    (v : NetworkState P.n) (hsent : v.sent r' = w.sent r') (hF : v.F = w.F)
    (hghost : v.ghost r' = w.ghost r') :
    roundProjection P (Function.update u j (c, p.setRoundVariables r sr)) v r' = roundProjection P u
      w
    r' := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection,
    roundVariables_update_ne hu hr, hsent, hF, hghost]

/-- A send of round `r`, read at another round. -/
theorem roundProjection_other (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr : RoundVariables P.n)
    (m : Message P.n) {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    (hL : roundOf L = some r) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r sr))
        ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r' = roundProjection P u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  exact roundProjection_otherTransition hu hr sr _ (recordGBCASend_sent_ne w r j m hr) rfl rfl

/-- A transition of round `r` that records nothing, read at another round. -/
theorem roundProjection_otherNoSent (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : RoundVariables P.n) {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    (hL : roundOf L = some r) :
    roundProjection P (Function.update u j (c, p.setRoundVariables r sr))
        (w.writeGhost (ghostStep P) L) r' = roundProjection P u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  exact roundProjection_otherTransition hu hr sr w rfl rfl rfl

/-- A Byzantine injection of round `r`, read at another round. -/
theorem roundProjection_otherSent (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState
  P.n)
    {r r' : ℕ} (hr : r' ≠ r) (k : Fin P.n) (m : Message P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    (hL : roundOf L = some r) :
    roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r' = roundProjection P
      u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  simp only [roundProjection, firstGatherProjection, secondGatherProjection,
    recordGBCASend_sent_ne w r k m hr, recordGBCASend_F, recordGBCASend_ghost]

/-- **The family of rounds after a transition that moves one round**: where every round of the
family `G` is the projection before the transition, every round of `G.setInstanceState r X` is the
projection after it, given that `X` is the projection of round `r` after the transition and that
every other round's projection stands. -/
theorem setInstanceState_roundProjection {x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {v : NetworkState P.n} {G : RoundFamilyOverBrachaState P}
    (hG : ∀ r', G r' = roundProjection P u w r') {r : ℕ} {X : GBCA.ByAFW.RoundStateOverBracha P.n}
    (hX : roundProjection P x v r = X)
    (hother : ∀ r', r' ≠ r → roundProjection P x v r' = roundProjection P u w r') (r' : ℕ) :
    G.setInstanceState r X r' = roundProjection P x v r' := by
  by_cases hr : r' = r
  · subst hr; rw [InstanceFamilyState.setInstanceState_apply_same, hX]
  · rw [InstanceFamilyState.setInstanceState_apply_ne _ _ hr, hG r', hother r' hr]

/-- **The whole family of rounds after a send**: the round the transition names moves,
and the rest stand. -/
theorem toRoundFamily (hu : (u j).2 = p) (r : ℕ) (sr : RoundVariables P.n) (m : Message P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} (hL : roundOf L = some r)
    {G : RoundFamilyOverBrachaState P} (hG : ∀ r', G r' = roundProjection P u w r')
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P (Function.update u j (c, p.setRoundVariables r sr))
      ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r = X) (r' : ℕ) :
    G.setInstanceState r X r' =
      roundProjection P (Function.update u j (c, p.setRoundVariables r sr))
        ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r' :=
  setInstanceState_roundProjection hG hX (fun _ hr => roundProjection_other hu hr sr m hL) r'

/-- The same, for a transition that records nothing. -/
theorem toRoundFamilyNoSent (hu : (u j).2 = p) (r : ℕ) (sr : RoundVariables P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} (hL : roundOf L = some r)
    {G : RoundFamilyOverBrachaState P} (hG : ∀ r', G r' = roundProjection P u w r')
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P (Function.update u j (c, p.setRoundVariables r sr))
      (w.writeGhost (ghostStep P) L) r = X) (r' : ℕ) :
    G.setInstanceState r X r' =
      roundProjection P (Function.update u j (c, p.setRoundVariables r sr))
        (w.writeGhost (ghostStep P) L) r' :=
  setInstanceState_roundProjection hG hX (fun _ hr => roundProjection_otherNoSent hu hr sr hL) r'

/-- The same, for a Byzantine injection. -/
theorem toRoundFamilySent (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n)
    (r : ℕ) (k : Fin P.n) (m : Message P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    (hL : roundOf L = some r)
    {G : RoundFamilyOverBrachaState P} (hG : ∀ r', G r' = roundProjection P u w r')
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r = X)
    (r' : ℕ) :
    G.setInstanceState r X r' =
      roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r' :=
  setInstanceState_roundProjection hG hX (fun _ hr => roundProjection_otherSent u w hr k m hL) r'

end Transitions

end AFW
end ABA
end PLTS
