/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.System

/-!
# The transitions of one program and of the network, determined by their labels

`programStep_*` determines one program's transition from its label: the participant's
transition as its guards together with the Dirac it produces, the loop that takes an input where
the participant's transition is not enabled, and the idle transition of a non-participant as the
identity. The state and the distribution are variables, so `cases` unifies against any round
variables. A participant's transition carries the replacement guard `corrupted = false`, and on a
label outside `actsAt j` the replaced program's self-loop is a further transition on the same
label (D23).

These lemmas hold for every implementation, because a label outside `roundOwn j` has a
transition written for all of them and `IsRoundStep` confines the implementation's own transitions
to `roundOwn j`. A corrupted process's two sub-protocol calls and the announcement `boundG` are
outputs of the network, and every program idles on them, the process the label names included
(D11, D29).

`programStep_notRound` reads a program's transition on a label outside `roundOwn j`, other than
`τ` and a `fail`: it leaves the replacement flag and the round variables.

`networkStep_*` does the same for the network, on the interface labels, on the synchronisation
labels and on the silent label. `programStep_dirac` and `networkStep_dirac` state that both step
relations are Dirac, provided the implementation's own transitions are; the composite carries the
probabilistic coin resolution and is not.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### Determinacy of the two step relations

The composite is not an LTS — the coin resolution is probabilistic — but both
step relations written here are Dirac, provided the implementation's own
transitions are. -/

section Cases

variable {P : Parameters} {M E S : Type}
    {roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop}
    {j : Fin P.n} {q : ProcessVariables P.n S} {ν : PMF (ProcessVariables P.n S)}

/-- Every process transition is Dirac: the transitions here are, and so are the
implementation's own by `IsRoundStep.dirac`. -/
theorem programStep_dirac [IsRoundStep P M E S roundStep]
    {l : ExtendedLabel P.n M E} (h : ProgramStep P M E S roundStep j q l ν) :
    ∃ q', ν = PMF.pure q' := by
  cases h
  case roundTransition h' => exact IsRoundStep.dirac h'
  all_goals exact ⟨_, rfl⟩

variable [IsRoundStep P M E S roundStep]

/-- The one `τ` transition of a program is `terminate`: a silent step of a
program is that program's own termination, taken on a fired return and DECIDED
messages received from `2f + 1` distinct senders (D22). A replaced program has no silent
transition at all, so the implementation carries `corrupted = false` (D23), and
no graded-agreement transition is silent, `roundOwn` holding of no `τ`. -/
theorem programStep_tau_terminate
    (h : ProgramStep P M E S roundStep j q (Silent.τ : ExtendedLabel P.n M E) ν) :
    ∃ b : Bool, q.1.corrupted = false ∧ q.1.processVariables.returned = true ∧
      2 * P.f + 1 ≤ q.1.decidedCount b ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, { q.2 with terminated := true }) := by
  rw [extendedLabel_tau] at h
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case terminate b hh hret hcnt hterm => exact ⟨b, hh, hret, hcnt, hterm, rfl⟩
  case corruptedIdle hh hτ hown => exact absurd rfl hτ

/-! ### One program's transitions, by label class

Each lemma determines one transition from its label: the participant's transition as
its guards together with the Dirac it produces, the loop that takes an input where the
participant's transition is not enabled, and the idle transition of a non-participant as the
identity. The state and the distribution are variables, so `cases` unifies against any state of
the program. A participant's transition carries the replacement guard `corrupted = false`, and on
a label outside `actsAt j` the replaced program's self-loop is a further transition on the same
label (D23). -/

theorem programStep_callABA_own {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.callABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.processVariables.input = none ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with
        input := some b, estimate := some b, round := 0, phase := .toCallG }, q.2)) ∨
    ((q.1.corrupted = true ∨ q.1.processVariables.input ≠ none) ∧ ν = PMF.pure q) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem programStep_callABA_notOwn {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.callABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

/-- The process's own ABA return: the correct return, on the quorum and the process's own record
of having sent the bit, or the replaced program's self-loop (D8, D23). -/
theorem programStep_retABA_own {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.retABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.processVariables.input ≠ none ∧
      P.n - P.f ≤ q.1.decidedCount b ∧ b ∈ q.1.decidedSent ∧
      q.1.processVariables.returned = false ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with returned := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case ret =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_retABA_notOwn {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.retABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem programStep_callG_notOwn {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.callG r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact absurd (IsRoundStep.own h') hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retG_notOwn {r : ℕ} {id : Fin P.n} {out : GBCAOutput} (hid : id ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.retG r id out)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact absurd (IsRoundStep.own h') hid
  case retGIdle => rfl
  case corruptedIdle => rfl

/-- The announcement of a round's bound bit leaves every program where it stands (D29). -/
theorem programStep_boundG {r : ℕ} {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.boundG r b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case boundGIdle => rfl
  case corruptedIdle => rfl

/-- The process's own coin call: the call at an unreplaced program at the phase `toCallW` of round
`r`. The replaced program has no transition on it, since `callW r j` lies in `actsAt j` (D23). -/
theorem programStep_callW_own {r : ℕ}
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.callW r j)) ν) :
    q.1.corrupted = false ∧ q.1.processVariables.phase = .toCallW ∧
      q.1.processVariables.round = r ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with phase := .awaitW },
        q.2) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case callW => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_callW_notOwn {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.callW r id)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own coin return: the return at a program awaiting the coin of round `r`, the
loop at an unreplaced program that is not, or the replaced program's self-loop. -/
theorem programStep_retW_own {r : ℕ} {co : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.retW r j co)) ν) :
    (q.1.corrupted = false ∧ q.1.processVariables.phase = .awaitW ∧ q.1.processVariables.round = r ∧
      ν = PMF.pure (q.1.stepRound co, q.2)) ∨
    (q.1.corrupted = false ∧
      ¬ (q.1.processVariables.phase = .awaitW ∧ q.1.processVariables.round = r) ∧
      ν = PMF.pure q) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case retWLoop => exact Or.inr (Or.inl ⟨by assumption, by assumption, rfl⟩)
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr (Or.inr ⟨by assumption, rfl⟩)

theorem programStep_retW_notOwn {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.retW r id co)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case retW => exact absurd rfl hid
  case retWLoop => rfl
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag is set on a program not yet
replaced, and a replaced program is unchanged. -/
theorem programStep_fail_own (h : ProgramStep P M E S roundStep j q (Sum.inl (.fail j)) ν) :
    (q.1.corrupted = false ∧ ν = PMF.pure ({ q.1 with corrupted := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_fail_notOwn {k : Fin P.n} (hk : k ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inl (.fail k)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

/-! ### One program's transitions on the synchronisation labels

A corrupted process's two sub-protocol calls are outputs of the network, and every program idles
on them, the process the label names included (D11). -/

theorem programStep_gbcaSend_notOwn {r : ℕ} {k : Fin P.n} {m : M} (hk : k ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.gbcaSend r k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact absurd (IsRoundStep.own h') hk
  case gbcaSendIdle => rfl
  case corruptedIdle => rfl

theorem programStep_gbcaDeliver_notOwn {r : ℕ} {i k : Fin P.n} {m : M} (hi : i ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.gbcaDeliver r i k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact absurd (IsRoundStep.own h') hi
  case gbcaDeliverIdle => rfl
  case corruptedIdle => rfl

/-- The process's own DECIDED relay: the correct relay, on the quorum and the process's own record
of not having sent the bit, which records the send, or the replaced program's self-loop (D8,
D12′, D23). -/
theorem programStep_decidedRelay_self {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.decidedRelay j b)) ν) :
    (q.1.corrupted = false ∧ q.1.processVariables.input ≠ none ∧
      P.f + 1 ≤ q.1.decidedCount b ∧ b ∉ q.1.decidedSent ∧
      ν = PMF.pure (q.1.recordDecided b, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case decidedRelay =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case decidedRelayIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_decidedRelay_notOwn {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.decidedRelay k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case decidedRelay => exact absurd rfl hk
  case decidedRelayIdle => rfl
  case corruptedIdle => rfl

/-- A DECIDED delivery to the process: the receive of a payload not yet received from the sender,
the loop on one already received, or the replaced program's self-loop (D12′, D23). -/
theorem programStep_decidedDeliver_self {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.decidedDeliver j k b)) ν) :
    (q.1.corrupted = false ∧ b ∉ q.1.decidedDelivered k ∧
      ν = PMF.pure (q.1.receiveDecided k b, q.2)) ∨
    (q.1.corrupted = false ∧ b ∈ q.1.decidedDelivered k ∧ ν = PMF.pure q) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case decidedDeliverReceive => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case decidedDeliverLoop => exact Or.inr (Or.inl ⟨by assumption, by assumption, rfl⟩)
  case decidedDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr (Or.inr ⟨by assumption, rfl⟩)

theorem programStep_decidedDeliver_notOwn {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.decidedDeliver i k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case decidedDeliverReceive => exact absurd rfl hi
  case decidedDeliverLoop => exact absurd rfl hi
  case decidedDeliverIdle => rfl
  case corruptedIdle => rfl

/-- The process's own DECIDED send: the send of a grade-2 round, which records the send, clears
the grade and enters the next round's `toCallG`. The replaced program has no transition on it
(D23). -/
theorem programStep_decidedSend_self {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.decidedSend j b)) ν) :
    q.1.corrupted = false ∧ q.1.processVariables.phase = .toSendDecided ∧
      q.1.processVariables.lastGrade = some (.grade2 b) ∧
      ν = PMF.pure ((q.1.setProcessVariables
        { q.1.processVariables with lastGrade := none, phase := .toCallG }).recordDecided b,
        q.2) := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case decidedSend => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case decidedSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_decidedSend_notOwn {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.decidedSend k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  case decidedSend => exact absurd rfl hk
  case decidedSendIdle => rfl
  case corruptedIdle => rfl

/-- A round-internal call or return at another process leaves this program where it stands: the
transition is the implementation's at the process the label names, and an idle one here. -/
theorem programStep_gbcaRoundEvent_notOwn {r : ℕ} {k : Fin P.n} {e : E} (hk : k ≠ j)
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.gbcaRoundEvent r k e)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact absurd (IsRoundStep.own h') hk
  case gbcaRoundEventIdle => rfl
  case corruptedIdle => rfl

/-- A corrupted process's graded-agreement call leaves every program where it stands, the one
the label names included (D11). -/
theorem programStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.byzantineCallG r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  all_goals rfl

/-- A corrupted process's coin call leaves every program where it stands (D11). -/
theorem programStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : ProgramStep P M E S roundStep j q (Sum.inr (.byzantineCallW r k)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundTransition h' => exact (IsRoundStep.own h').elim
  all_goals rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a
process whose flag is set leaves both halves of its variables unchanged.
Every transition that writes carries the replacement guard `corrupted = false`, the
implementation's own transitions by `IsRoundStep.correct`, so every transition of a replaced
program is a self-loop. -/
theorem programStep_noStep {L : ExtendedLabel P.n M E} (hc : q.1.corrupted = true)
    (h : ProgramStep P M E S roundStep j q L ν) : ν = PMF.pure q := by
  cases h
  case roundTransition h' => rw [IsRoundStep.correct h'] at hc; exact absurd hc (by simp)
  all_goals simp_all

/-! ### A program's transition on a label of another class

A program's transition on a label outside `roundOwn j`, other than `τ` and a `fail`, leaves its
replacement flag and its round variables. -/

/-- A program's transition on a label outside `roundOwn j`, other than `τ` and a `fail`, leaves
the replacement flag and the round variables. -/
theorem programStep_notRound {q' : ProcessVariables P.n S} {L : ExtendedLabel P.n M E}
    (hL : ¬ roundOwn j L) (hτ : L ≠ Sum.inl Label.tau) (hf : ∀ k, L ≠ Sum.inl (.fail k))
    (h : ProgramStep P M E S roundStep j q L (PMF.pure q')) :
    q'.1.corrupted = q.1.corrupted ∧ q'.2 = q.2 := by
  generalize hμ : (PMF.pure q' : PMF (ProcessVariables P.n S)) = μ at h
  cases h with
  | roundTransition _ _ _ h' => exact absurd (IsRoundStep.own h') hL
  | terminate => exact absurd rfl hτ
  | failSelf => exact absurd rfl (hf _)
  | retW =>
    obtain rfl := pure_inj hμ
    refine ⟨?_, rfl⟩
    unfold RoundLoopVariables.stepRound
    split <;> rfl
  | _ => obtain rfl := pure_inj hμ; exact ⟨rfl, rfl⟩

end Cases

/-! ### The network's transitions, by label class -/

section NetworkStepCases
variable {P : Parameters} {M E G : Type} [DecidableEq M] [Inhabited G]
    {ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G}
    {ghostBound : G → Option Bool}
    {s : NetworkState P.n M G} {μ : PMF (NetworkState P.n M G)}

/-- Every network transition is Dirac. -/
theorem networkStep_dirac {l : ExtendedLabel P.n M E}
    (h : NetworkStep P M E G ghostStep ghostBound s l μ) :
    ∃ s', μ = PMF.pure s' := by
  cases h <;> exact ⟨_, rfl⟩

theorem networkStep_gbcaSend {r : ℕ} {j : Fin P.n} {m : M}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.gbcaSend r j m)) μ) :
    μ = PMF.pure ((s.recordGBCASend r j m).writeGhost ghostStep (Sum.inr (.gbcaSend r j m))) := by
  cases h; rfl

theorem networkStep_gbcaDeliver {r : ℕ} {i j : Fin P.n} {m : M}
    (h : NetworkStep P M E G ghostStep ghostBound s
      (Sum.inr (.gbcaDeliver r i j m)) μ) :
    m ∈ s.sent r j ∧ μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaDeliver r i j m))) := by
  cases h; exact ⟨by assumption, rfl⟩

/-- The network's half of a DECIDED relay records the payload, unguarded. -/
theorem networkStep_decidedRelay {j : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.decidedRelay j b)) μ) :
    μ = PMF.pure (s.recordDecided j b) := by
  cases h; rfl

theorem networkStep_decidedDeliver {i j : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s
      (Sum.inr (.decidedDeliver i j b)) μ)
    : b ∈ s.decidedSent j ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_decidedSend {j : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.decidedSend j b)) μ) :
    μ = PMF.pure (s.recordDecided j b) := by
  cases h; rfl

/-- The network's half of a round-internal call or return: it sends nothing and writes the ghost
of the round the label names. -/
theorem networkStep_gbcaRoundEvent {r : ℕ} {j : Fin P.n} {e : E}
    (h : NetworkStep P M E G ghostStep ghostBound s
      (Sum.inr (.gbcaRoundEvent r j e)) μ) :
    μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaRoundEvent r j e))) := by
  cases h; rfl

/-- A corrupted process's coin call is output under `k ∈ F` at a started round (D11, D37). -/
theorem networkStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : NetworkStep P M E G ghostStep ghostBound s
      (Sum.inr (.byzantineCallW r k)) μ) :
    k ∈ s.F ∧ r ∈ s.startedRounds ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallW r k))) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

/-- A corrupted process's graded-agreement call is output under `k ∈ F` at a started round
(D11, D37). -/
theorem networkStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s
      (Sum.inr (.byzantineCallG r k b)) μ) :
    k ∈ s.F ∧ r ∈ s.startedRounds ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallG r k b))) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem networkStep_callABA {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.callABA id b)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

/-- The network takes an ABA return on one unguarded transition with the identity successor. -/
theorem networkStep_retABA {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.retABA id b)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

/-- A graded-agreement call sends nothing. Where the caller lies outside the corrupted set, the
called round enters the started rounds (D37). -/
theorem networkStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.callG r id b)) μ) :
    μ = PMF.pure ((s.recordStartedRound r id).writeGhost ghostStep (Sum.inl (.callG r id b))) := by
  cases h; rfl

/-- A graded-agreement return sends nothing and writes the ghost of its round. -/
theorem networkStep_retG {r : ℕ} {id : Fin P.n} {out : GBCAOutput}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.retG r id out)) μ) :
    μ = PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out))) := by
  cases h; rfl

/-- The announcement of a round's bound bit fires with the bit the round's ghost holds (D29). -/
theorem networkStep_announceBound {r : ℕ} {b : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.boundG r b)) μ) :
    ghostBound (s.ghost r) = some b ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inl (.boundG r b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_callW {r : ℕ} {id : Fin P.n}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.callW r id)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem networkStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.retW r id c)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem networkStep_fail {k : Fin P.n}
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.fail k)) μ) :
    k ∉ s.F ∧ s.F.card < P.f ∧ μ = PMF.pure (s.corrupt P k) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

/-- The network's silent transitions are its two injections: a round message of a corrupted
sender at a started round, or a DECIDED payload of a corrupted sender (D11, D12′, D37). -/
theorem networkStep_tau
    (h : NetworkStep P M E G ghostStep ghostBound s (Sum.inl .tau) μ) :
    (∃ (r : ℕ) (k : Fin P.n) (m : M), k ∈ s.F ∧ r ∈ s.startedRounds ∧
      μ = PMF.pure (s.recordGBCASend r k m)) ∨
    (∃ (k : Fin P.n) (b : Bool), k ∈ s.F ∧ μ = PMF.pure (s.recordDecided k b)) := by
  cases h
  case byzantineGBCA => exact Or.inl ⟨_, _, _, by assumption, by assumption, rfl⟩
  case byzantineDecided => exact Or.inr ⟨_, _, by assumption, rfl⟩

end NetworkStepCases
end Implementation
end ABA
end PLTS
