/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Round.Pair
import Leslie2Protocols.ABA.Gather.Ideal

/-!
# The GBCA implementation over the gather-over-BRB instances

The round-`r` GBCA implementation with its two gather instances at the
gather-over-BRB-specification level (`ABA/Gather/Ideal.lean`): the same fused
rule table as the GBCA-over-gather instance (`ABA/Round/Pair.lean`), each
gather specification component replaced by the gather implementation over
the BRB specification. The candidate and the grade are computed by the same
`GBCA.cand` / `GBCA.gradeOf` at the same fused rows.

The round and the gather instances beneath it are each named for the layer
they idealise, so `GBCA.IdealState` is the pair of `Gather.IdealState`s one
level down, beside the round's bound bit.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Gather

/-- **The state**: the two gather-over-BRB instances beside the round's bound
bit. -/
abbrev IdealState (n : ℕ) : Type :=
  Gather.IdealState n Bool × Gather.IdealState n (Option Bool) × Option Bool

/-- The initial state. -/
def IdealState.initial (n : ℕ) : IdealState n :=
  (Gather.IdealState.initial n Bool, Gather.IdealState.initial n (Option Bool), none)

/-- The step relation of the round-`r` GBCA-over-gather-over-BRB instance:
the fused table of `GBCA.PairStep`, each gather component moving by its own
implementation rows. All transitions are Dirac. -/
inductive IdealStep (P : Params) (r : ℕ) :
    IdealState P.n → Lab P.n → PMF (IdealState P.n) → Prop
  /-- The environment call is the first gather's call. -/
  | callG (s : IdealState P.n) (id : Fin P.n) (b : Bool)
      (t1' : Gather.IdealState P.n Bool)
      (h : Gather.IdealStep P s.1 (.call id b) (PMF.pure t1')) :
      IdealStep P r s (.callG r id b) (PMF.pure (t1', s.2))
  /-- An internal step of the first gather instance. -/
  | ga1Tau (s : IdealState P.n) (t1' : Gather.IdealState P.n Bool)
      (h : Gather.IdealStep P s.1 Gather.Lab.tau (PMF.pure t1')) :
      IdealStep P r s .tau (PMF.pure (t1', s.2))
  /-- An internal step of the second gather instance. -/
  | ga2Tau (s : IdealState P.n) (t2' : Gather.IdealState P.n (Option Bool))
      (h : Gather.IdealStep P s.2.1 Gather.Lab.tau (PMF.pure t2')) :
      IdealStep P r s .tau (PMF.pure (s.1, t2', s.2.2))
  /-- The first gather returns to `id`, `id` calls the second gather with the
  candidate, and the round's bound bit is written from the core the return
  carries if it is unwritten. -/
  | link (s : IdealState P.n) (id : Fin P.n) (g : Fin P.n → Option Bool)
      (C : APSet P.n Bool) (t1' : Gather.IdealState P.n Bool)
      (h : Gather.IdealStep P s.1 (.ret id g C) (PMF.pure t1'))
      (h2 : (s.2.1.ga.proc id).input = none) :
      IdealStep P r s .tau
        (PMF.pure (t1',
          { s.2.1 with
            ga := s.2.1.ga.setProc id
              { s.2.1.ga.proc id with input := some (cand P g) }
            brbIn := Function.update s.2.1.brbIn id
              { s.2.1.brbIn id with input := some (cand P g) } },
          some (s.2.2.getD (boundOfCore P C))))
  /-- The second gather returns to `id` and the round returns the graded
  outcome, announcing the round's bound bit. -/
  | retG (s : IdealState P.n) (id : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (C : APSet P.n (Option Bool)) (t2' : Gather.IdealState P.n (Option Bool))
      (h : Gather.IdealStep P s.2.1 (.ret id g C) (PMF.pure t2')) :
      IdealStep P r s
        (.retG r id (gradeOf P g) (s.2.2.getD (boundOfCore P ∅)))
        (PMF.pure (s.1, t2', s.2.2))
  /-- Corruption (deviation D1), in lockstep across both instances. -/
  | fail (s : IdealState P.n) (id : Fin P.n) :
      IdealStep P r s (.fail id)
        (PMF.pure (s.1.corruptAll P id, s.2.1.corruptAll P id, s.2.2))

/-- The round-`r` GBCA-over-gather-over-BRB instance. -/
noncomputable def idealInst (P : Params) (r : ℕ) :
    System (IdealState P.n) (Lab P.n) where
  init := IdealState.initial P.n
  step := IdealStep P r

@[simp] theorem idealInst_init (P : Params) (r : ℕ) :
    (idealInst P r).init = IdealState.initial P.n := rfl

@[simp] theorem idealInst_step (P : Params) (r : ℕ) (s : IdealState P.n)
    (l : Lab P.n) (μ : PMF (IdealState P.n)) :
    (idealInst P r).step s l μ ↔ IdealStep P r s l μ := Iff.rfl

/-- Every transition is Dirac: the instance is an LTS. -/
theorem idealInst_isLTS (P : Params) (r : ℕ) : (idealInst P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end GBCA
end ABA
end PLTS
