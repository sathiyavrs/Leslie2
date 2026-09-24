/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.RefinesSpecification
import Leslie2Protocols.ABA.GBCA.BindingOverRoundAlphabet

/-!
# Binding of the round's graded-agreement composition

The round-`r` composition of `GBCA/ABDY/Composition.lean` reaches
`GBCA.specificationOverRoundAlphabet`, the graded agreement specification read over the family
alphabet, through `GBCA.ByABDY.refinesSpecification`. `composition_specificationTraces`
(`GBCA/ABDY/RefinesSpecification.lean`) is the trace-distribution inclusion of that refinement.

Binding is a property of the labels (`GBCA.BindingTraceExtended`), so the inclusion carries it from
`GBCA.specificationOverRoundAlphabet_binding`: `composition_binding` is binding of the round.
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation Composition

/-! ### Binding of the round -/

/-- **Binding of the round's composition, on a trace.** Every positive-probability trace of the
round-`r` composition is bound to one bit: all its round-`r` returns announce that bit, and every
one of them that hands out a value hands out it. Binding is a property of the labels
(`GBCA.BindingTraceExtended`), so `composition_specificationTraces` carries it from
`GBCA.specificationOverRoundAlphabet_binding`. -/
theorem composition_binding (P : Parameters) (r : ℕ) :
    ∀ D ∈ achievableTraceDists (composition P r), ∀ t, D t ≠ 0 →
      GBCA.BindingTraceExtended P r t :=
  safety_transfer (composition_specificationTraces P r)
    (GBCA.specificationOverRoundAlphabet_binding P Message r)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.composition_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composition_binding

end GBCA.ByABDY
end ABA
end PLTS
