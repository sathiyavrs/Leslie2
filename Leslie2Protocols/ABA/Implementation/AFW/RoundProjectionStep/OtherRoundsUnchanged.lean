/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.AFW.RoundProjectionStep.ViewAfterOneWrite

/-!
# Every other round is unchanged

`roundProjection_otherRow` and its three companions: the rounds a row does not name read exactly as
the row found them. The acting process's other round records are untouched, the adversary's sent
family is written at one round only, and so is its ghost record. `toRoundFamily`,
`toRoundFamilyNoSent` and `toRoundFamilySent` state a row's effect on the whole family of rounds as
a one-point update.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

variable {P : Parameters}

section Rows

variable {u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w : NetworkState P.n} {j : Fin P.n}
    {c : RoundLoopRecord P.n} {p : RoundRecordMap P.n}

/-! ### Every other round is unchanged

A row names one round. The rounds it does not name read exactly as they did:
the acting process's other round records are untouched, the adversary's sent
family is written at one round only, and so is its ghost record. -/

/-- The view of a round the row does not name. -/
theorem roundProjection_otherRow (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr : RoundRecord P.n)
    (v : NetworkState P.n) (hsent : v.sent r' = w.sent r') (hF : v.F = w.F)
    (hghost : v.ghostRecord r' = w.ghostRecord r') :
    roundProjection P (Function.update u j (c, p.setRoundRecord r sr)) v r' = roundProjection P u w
    r' := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection,
    roundRecord_update_ne hu hr, hsent, hF, hghost]

/-- A send of round `r`, read at another round. -/
theorem roundProjection_other (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r) (sr : RoundRecord P.n)
    (m : Message P.n) {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
        ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r' = roundProjection P u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  exact roundProjection_otherRow hu hr sr _ (recordGBCASend_sent_ne w r j m hr) rfl rfl

/-- A row of round `r` that records nothing, read at another round. -/
theorem roundProjection_otherNoSent (hu : (u j).2 = p) {r r' : ℕ} (hr : r' ≠ r)
    (sr : RoundRecord P.n) {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r) :
    roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
        (w.writeGhost (ghostStep P) L) r' = roundProjection P u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  exact roundProjection_otherRow hu hr sr w rfl rfl rfl

/-- A Byzantine injection of round `r`, read at another round. -/
theorem roundProjection_otherSent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n)
    {r r' : ℕ} (hr : r' ≠ r) (k : Fin P.n) (m : Message P.n)
    {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r) :
    roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r' = roundProjection P
      u w r' := by
  rw [roundProjection_writeGhost_ne _ _ hL hr]
  simp only [roundProjection, firstGatherProjection, secondGatherProjection,
    recordGBCASend_sent_ne w r k m hr, recordGBCASend_F, recordGBCASend_ghostRecord]

/-- **The whole family of rounds after a send**: the round the row names moves,
the rest remain unchanged. -/
theorem toRoundFamily (hu : (u j).2 = p) (r : ℕ) (sr : RoundRecord P.n) (m : Message P.n)
    {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r)
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r = X)
    :
    (fun r' => roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      ((w.recordGBCASend r j m).writeGhost (ghostStep P) L) r')
    = Function.update (fun r' => roundProjection P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, roundProjection_other hu hr sr m hL]

/-- The same, for a row that records nothing. -/
theorem toRoundFamilyNoSent (hu : (u j).2 = p) (r : ℕ) (sr : RoundRecord P.n)
    {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r)
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      (w.writeGhost (ghostStep P) L) r = X)
    :
    (fun r' => roundProjection P (Function.update u j (c, p.setRoundRecord r sr))
      (w.writeGhost (ghostStep P) L) r')
    = Function.update (fun r' => roundProjection P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, roundProjection_otherNoSent hu hr sr hL]

/-- The same, for a Byzantine injection. -/
theorem toRoundFamilySent (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ)
    (k : Fin P.n) (m : Message P.n) {L : ExtendedLabel P.n (Message P.n)} (hL : roundOf L = some r)
    (X : GBCA.ByAFW.RoundStateOverBracha P.n)
    (hX : roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r = X) :
    (fun r' => roundProjection P u ((w.recordGBCASend r k m).writeGhost (ghostStep P) L) r')
      = Function.update (fun r' => roundProjection P u w r') r X := by
  funext r'
  by_cases hr : r' = r
  · subst hr; rw [Function.update_self, hX]
  · rw [Function.update_of_ne hr, roundProjection_otherSent u w hr k m hL]

end Rows

end AFW
end ABA
end PLTS
