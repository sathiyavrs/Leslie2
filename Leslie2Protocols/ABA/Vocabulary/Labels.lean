/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2.Systems.Trace
import Leslie2Protocols.ABA.Vocabulary.Parameters

/-!
# The shared label alphabet of the ABA development

Every system of the case study — the round loops, `ABA.Spec`, the `GBCA` instance
families and the `WCC` spec family — lives over the single label type
`ABA.Label n`. Sub-protocol API labels are tagged with their round `r : ℕ`
(the source blueprint's Algorithm 1 uses countably many `GBCA_r` / `WCC_r`
instances).

Composition is by the core's full-synchronisation `System.parallel`: a visible
label fires iff *every* component steps on it. Components therefore carry
self-loops on labels that are not their business (added by the `withIdle` /
`family` combinators, not here), which makes full synchronisation emulate the
blueprint's sync-set composition `∥_S`: the genuine participants of a label
handshake while everyone else no-ops in place.

* `callG/retG r id …`, `callW/retW r id …` — handshakes between a round loop
  and the round-`r` instance of the respective family. A `retG` label names the
  round, the process being answered, the graded outcome it receives and the
  round's bound bit.
* `fail id` — corruption; a genuine synchronisation of **all** components
  (each keeps its own copy of the corrupted set `F`, updated in lockstep).
* `hiddenAPI` — the sub-protocol API labels, hidden (sent to `τ`) in the
  composed systems via `System.abstract`.

The WCC `guess` label of the blueprint is omitted: it exists solely for the
Unpredictability property, which is out of scope here.
-/

namespace PLTS
namespace ABA

/-- Graded outcome of a GBCA instance: `(b, A)`, `(b, B)` or `(⊥, C)`. -/
inductive GbcaOut : Type
  /-- Highest grade: output `b` with grade `A` (decide). -/
  | A (b : Bool)
  /-- Middle grade: output `b` with grade `B` (adopt). -/
  | B (b : Bool)
  /-- Lowest grade: no output (`⊥`), grade `C` (adopt the coin). -/
  | C
  deriving DecidableEq, Repr

/-- The shared label alphabet of the ABA development over `n` processes.
GBCA/WCC API labels are tagged with their round `r : ℕ`. -/
inductive Label (n : ℕ) : Type
  /-- The silent label. -/
  | tau
  /-- Environment calls ABA at process `id` with input bit `b`. -/
  | callABA (id : Fin n) (b : Bool)
  /-- Process `id` returns `b` from ABA. -/
  | retABA (id : Fin n) (b : Bool)
  /-- Process `id` calls round-`r` GBCA with input `b`. -/
  | callG (r : ℕ) (id : Fin n) (b : Bool)
  /-- Round-`r` GBCA returns to process `id` the graded outcome `out` and the
  round's bound bit `bnd`. The graded outcome is program data: a round loop
  reads it and retains it. The bound bit is a ghost output — the bound value the
  round's specification holds, announced on the label — and no program reads
  it. Announcing it makes binding, a property of the branching structure, a
  property of the trace alone. -/
  | retG (r : ℕ) (id : Fin n) (out : GbcaOut) (bnd : Bool)
  /-- Process `id` calls round-`r` WCC. -/
  | callW (r : ℕ) (id : Fin n)
  /-- Round-`r` WCC returns the coin bit `b` to `id`. -/
  | retW (r : ℕ) (id : Fin n) (b : Bool)
  /-- Corruption of process `id` (synchronised across all components). -/
  | fail (id : Fin n)
  deriving DecidableEq, Repr

instance {n : ℕ} : Silent (Label n) := ⟨Label.tau⟩

namespace Label

variable {n : ℕ}

@[simp] theorem silent_eq : (Silent.τ : Label n) = Label.tau := rfl

/-- The GBCA round a label belongs to, if any. -/
def gbcaRound : Label n → Option ℕ
  | callG r _ _ => some r
  | retG r _ _ _ => some r
  | _ => none

/-- The WCC round a label belongs to, if any. -/
def wccRound : Label n → Option ℕ
  | callW r _ => some r
  | retW r _ _ => some r
  | _ => none

/-- A label is global iff it is a corruption event: every component of the
composition (and every instance of a family) steps on it simultaneously. -/
def isFail : Label n → Prop
  | fail _ => True
  | _ => False

instance : DecidablePred (isFail (n := n)) := fun l => by
  cases l <;> simp only [isFail] <;> infer_instance

/-- The sub-protocol API: every GBCA- or WCC-tagged label. These are the
labels hidden (sent to `τ`) in the hybrids. `τ`, the ABA API and `fail`
stay visible. -/
def hiddenAPI (n : ℕ) : Set (Label n) :=
  {l | l.gbcaRound ≠ none ∨ l.wccRound ≠ none}

@[simp] theorem tau_not_mem_hiddenAPI : Label.tau ∉ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound, wccRound]

@[simp] theorem callG_mem_hiddenAPI (r : ℕ) (id : Fin n) (b : Bool) :
    Label.callG r id b ∈ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound]

@[simp] theorem retG_mem_hiddenAPI (r : ℕ) (id : Fin n) (out : GbcaOut)
    (bnd : Bool) : Label.retG r id out bnd ∈ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound]

@[simp] theorem callW_mem_hiddenAPI (r : ℕ) (id : Fin n) :
    Label.callW r id ∈ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound, wccRound]

@[simp] theorem retW_mem_hiddenAPI (r : ℕ) (id : Fin n) (b : Bool) :
    Label.retW r id b ∈ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound, wccRound]

@[simp] theorem callABA_not_mem_hiddenAPI (id : Fin n) (b : Bool) :
    Label.callABA id b ∉ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound, wccRound]

@[simp] theorem retABA_not_mem_hiddenAPI (id : Fin n) (b : Bool) :
    Label.retABA id b ∉ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound, wccRound]

@[simp] theorem fail_not_mem_hiddenAPI (id : Fin n) :
    Label.fail id ∉ hiddenAPI n := by
  simp [hiddenAPI, gbcaRound, wccRound]

end Label

end ABA
end PLTS
