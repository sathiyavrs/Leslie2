/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY.Instance

/-!
# The routing table of the round-indexed family, evaluated

`GBCA.ByABDY.roundOwnsLabel` and `GBCA.ByABDY.isFailLabel` are decided by a `rfl` at every label of
the extended alphabet. The composed system composes `GBCA.ByABDY.gbcaInstanceFamily` with local
states that speak that alphabet, so it discharges the routing premises by `simp`; the table here is
what `simp` uses, and it lives under `PLTS.ABA.Composition` with the rest of the components'
vocabulary. `corruptionAct_fail` evaluates the family's corruption act on a `fail` label.
-/

namespace PLTS
namespace ABA
namespace Composition

open Implementation

/-! ### Which labels the round-indexed family owns -/

section OwnedLabels
variable {n : ℕ}

@[simp] theorem roundOwnsLabel_callG (r : ℕ) (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.callG r id b) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_retG (r : ℕ) (id : Fin n) (out : GBCAOutput) (bnd : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.retG r id out bnd) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_gbcaCallLoop (r : ℕ) (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.gbcaCallLoop r id b) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_byzantineCallG (r : ℕ) (k : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineCallG r k b) : ExtendedLabel n) = some r := rfl
@[simp] theorem roundOwnsLabel_byzantineCallGLoop (r : ℕ) (k : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineCallGLoop r k b) : ExtendedLabel n) = some r :=
      rfl
@[simp] theorem roundOwnsLabel_byzantineRetG (r : ℕ) (k : Fin n) (out : GBCAOutput) (bnd : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineRetG r k out bnd) : ExtendedLabel n) = some r :=
      rfl

@[simp] theorem roundOwnsLabel_tau : GBCA.ByABDY.roundOwnsLabel (Sum.inl Label.tau : ExtendedLabel
  n) = none := rfl
@[simp] theorem roundOwnsLabel_callABA (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.callABA id b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_retABA (id : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.retABA id b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_callW (r : ℕ) (id : Fin n) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.callW r id) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_retW (r : ℕ) (id : Fin n) (c : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.retW r id c) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_fail (k : Fin n) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inl (Label.fail k) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_gbcaSend (r : ℕ) (j : Fin n) (m : GBCA.ByABDY.Message) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.gbcaSend r j m) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_gbcaDeliver (r : ℕ) (i j : Fin n) (m : GBCA.ByABDY.Message) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.gbcaDeliver r i j m) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_decidedSend (j : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.decidedSend j b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_decidedDeliver (i j : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.decidedDeliver i j b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_retWPublish (r : ℕ) (id : Fin n) (c b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.retWPublish r id c b) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_byzantineCallW (r : ℕ) (k : Fin n) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineCallW r k) : ExtendedLabel n) = none := rfl
@[simp] theorem roundOwnsLabel_byzantineRetW (r : ℕ) (k : Fin n) (b : Bool) :
    GBCA.ByABDY.roundOwnsLabel (Sum.inr (.byzantineRetW r k b) : ExtendedLabel n) = none := rfl

@[simp] theorem isFailLabel_fail (k : Fin n) :
    GBCA.ByABDY.isFailLabel (Sum.inl (Label.fail k) : ExtendedLabel n) := trivial

theorem corruptionAct_fail {P : Parameters} (k : Fin P.n)
  (s : GBCA.ByABDY.ImplementationState P.n) :
    GBCA.ByABDY.corruptionAct P (Sum.inl (Label.fail k)) s = (s.1, s.2.corrupt P k) := rfl

end OwnedLabels
end Composition
end ABA
end PLTS
