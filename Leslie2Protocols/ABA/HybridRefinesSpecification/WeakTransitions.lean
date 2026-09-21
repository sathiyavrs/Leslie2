/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.HybridRefinesSpecification.Relation
import Leslie2.Weak.WeakTransition

/-!
# Abstract-state run machinery

Pure `ABA.spec`-side weak-τ lemmas, with no composed-side/`Inv`/`Abs`
reasoning: given an abstract `SpecState`, these package the internal
`SpecStep` rules (`Specifications/ABA.lean`) into the `weakTau`/`weakStep` chains
(`WeakTransition.lean`) that the simulation rows (`HybridRefinesSpecification/Simulation.lean`)
consume. Every lemma here is standalone and never mentions `Inv`/`Abs`/the concrete
`(g, c, w)` state.

* `decide_step`: `SpecStep.decide` as a one-step `weakTau` run, the τ-tail
  that leads the first visible return.
* `weakStep_of_run_then_step`: a `weakTau` run followed by a genuine
  visible step is a `weakStep`.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-! ### The decide run -/

/-- `SpecStep.decide` as a `weakTau` run. The rule is Dirac, so the run is
a single step: `val` takes `b` and the mode returns to `Mode.idle`. -/
theorem decide_step {a : SpecState P.n} {b : Bool} (hv : a.val = none)
    (hs : SuppOK P a b) (hm : a.mode ≠ .terminal) :
    weakTau (spec P) (PMF.pure a)
      (PMF.pure { a with val := some b, mode := .idle }) :=
  weakTau_of_step rfl (SpecStep.decide a b hv hs hm)

/-! ### Convenience: closing a run with a visible step -/

/-- A `weakTau` run followed by a genuine (possibly visible) single step is a `weakStep`: the
run is the leading τ-closure, the step is the middle hyper-step (`hyperStep_pure_of_step`), and
the trailing τ-closure is the trivial reflexivity at the final state. -/
theorem weakStep_of_run_then_step {a a' a'' : SpecState P.n} {l : Lab P.n}
    (hrun : weakTau (spec P) (PMF.pure a) (PMF.pure a'))
    (hstep : SpecStep P a' l (PMF.pure a'')) :
    weakStep (spec P) (PMF.pure a) l (PMF.pure a'') :=
  ⟨PMF.pure a', PMF.pure a'', hrun, hyperStep_pure_of_step hstep, weakTau_refl _ _⟩

end ABA
end PLTS
