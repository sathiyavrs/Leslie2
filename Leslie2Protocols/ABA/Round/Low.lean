/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Round.Ideal
import Leslie2Protocols.ABA.Gather.Low

/-!
# The GBCA implementation

The round-`r` gather-based GBCA implementation (deviation D24), fully
concrete: the same fused rule table as the readings above it, each gather
component at the gather-over-Bracha level (`ABA/Gather/Low.lean`). This is
the protocol as it runs — the two gather calls with their `ECHO` and `VOTE`
exchanges, and underneath them the `4n` Bracha instances carrying the inputs
and the `BIND` payloads.
-/

namespace PLTS
namespace ABA
namespace GBCA

open Gather

/-- **The state**: the two gather-over-Bracha instances beside the round's
bound bit. -/
abbrev LowPairState (n : ℕ) : Type :=
  Gather.LowState n Bool × Gather.LowState n (Option Bool) × Option Bool

/-- The initial state. -/
def LowPairState.initial (n : ℕ) : LowPairState n :=
  (Gather.LowState.initial n Bool, Gather.LowState.initial n (Option Bool), none)

/-- The step relation of the round-`r` GBCA implementation: the fused table
of `GBCA.PairStep`, each gather component moving by its gather-over-Bracha
rows. All transitions are Dirac. -/
inductive LowPairStep (P : Params) (r : ℕ) :
    LowPairState P.n → Lab P.n → PMF (LowPairState P.n) → Prop
  /-- The environment call is the first gather's call. -/
  | callG (s : LowPairState P.n) (id : Fin P.n) (b : Bool)
      (t1' : Gather.LowState P.n Bool)
      (h : Gather.LowStep P s.1 (.call id b) (PMF.pure t1')) :
      LowPairStep P r s (.callG r id b) (PMF.pure (t1', s.2))
  /-- An internal step of the first gather instance. -/
  | ga1Tau (s : LowPairState P.n) (t1' : Gather.LowState P.n Bool)
      (h : Gather.LowStep P s.1 Gather.Lab.tau (PMF.pure t1')) :
      LowPairStep P r s .tau (PMF.pure (t1', s.2))
  /-- An internal step of the second gather instance. -/
  | ga2Tau (s : LowPairState P.n) (t2' : Gather.LowState P.n (Option Bool))
      (h : Gather.LowStep P s.2.1 Gather.Lab.tau (PMF.pure t2')) :
      LowPairStep P r s .tau (PMF.pure (s.1, t2', s.2.2))
  /-- The first gather returns to `id`, `id` calls the second gather with the
  candidate, and the round's bound bit is written from the core the return
  carries if it is unwritten. -/
  | link (s : LowPairState P.n) (id : Fin P.n) (g : Fin P.n → Option Bool)
      (C : APSet P.n Bool) (t1' : Gather.LowState P.n Bool)
      (h : Gather.LowStep P s.1 (.ret id g C) (PMF.pure t1'))
      (h2 : (s.2.1.ga.proc id).input = none)
      (hb2 : ((s.2.1.brbIn id).proc id).input = none) :
      LowPairStep P r s .tau
        (PMF.pure (t1',
          { s.2.1 with
            ga := s.2.1.ga.setProc id
              { s.2.1.ga.proc id with input := some (cand P g) }
            brbIn := Function.update s.2.1.brbIn id
              (((s.2.1.brbIn id).setProc id
                { (s.2.1.brbIn id).proc id with input := some (cand P g) }).mcast
                id (.init (cand P g))) },
          some (s.2.2.getD (boundOfCore P C))))
  /-- The second gather returns to `id` and the round returns the graded
  outcome, announcing the round's bound bit. -/
  | retG (s : LowPairState P.n) (id : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (C : APSet P.n (Option Bool)) (t2' : Gather.LowState P.n (Option Bool))
      (h : Gather.LowStep P s.2.1 (.ret id g C) (PMF.pure t2')) :
      LowPairStep P r s
        (.retG r id (gradeOf P g) (s.2.2.getD (boundOfCore P ∅)))
        (PMF.pure (s.1, t2', s.2.2))
  /-- Corruption (deviation D1), in lockstep across both instances. -/
  | fail (s : LowPairState P.n) (id : Fin P.n) :
      LowPairStep P r s (.fail id)
        (PMF.pure (s.1.corruptAll P id, s.2.1.corruptAll P id, s.2.2))

/-- The round-`r` GBCA implementation. -/
noncomputable def lowPairInst (P : Params) (r : ℕ) :
    System (LowPairState P.n) (Lab P.n) where
  init := LowPairState.initial P.n
  step := LowPairStep P r

@[simp] theorem lowPairInst_init (P : Params) (r : ℕ) :
    (lowPairInst P r).init = LowPairState.initial P.n := rfl

@[simp] theorem lowPairInst_step (P : Params) (r : ℕ) (s : LowPairState P.n)
    (l : Lab P.n) (μ : PMF (LowPairState P.n)) :
    (lowPairInst P r).step s l μ ↔ LowPairStep P r s l μ := Iff.rfl

/-- Every transition is Dirac: the instance is an LTS. -/
theorem lowPairInst_isLTS (P : Params) (r : ℕ) : (lowPairInst P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end GBCA
end ABA
end PLTS
