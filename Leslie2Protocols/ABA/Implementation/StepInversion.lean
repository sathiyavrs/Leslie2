/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.System

/-!
# The transitions of one program and of the network, read off their labels

`programStep_*` reads a row of one program's table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a non-participant as the identity.
The record and the distribution are variables, so `cases` unifies against any round record. A
participant's row carries the health guard `corrupted = false`, and on a label outside `actsAt j`
the replaced program's self-loop is a second row on the same label (D23).

The readers hold for every implementation, because a label outside `roundOwn j` is answered by a
row of the table written for all of them and `IsRoundRuleTable` confines the implementation's own
rows to `roundOwn j`. The Byzantine round rows have no row at the process they name (D22, D23), so
on `byzantineCallG`, `byzantineCallGLoop` and `byzantineRetG` every process idles and there is no
participant's row to read.

`networkStep_*` does the same for the network, on the interface labels, on the rendezvous alphabet
and on the silent label. `programStep_dirac` and `networkStep_dirac` state that both tables are
Dirac, provided the implementation's own rows are; the composite carries the probabilistic coin
resolution and is not.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### Determinacy of the two rule tables

The composite is not an LTS — the coin resolution is probabilistic — but both
tables written here are Dirac, provided the implementation's own rows are. -/

section Inversion

variable {P : Parameters} {M S : Type}
    {roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop}
    {j : Fin P.n} {q : ProcessRecord P.n S} {ν : PMF (ProcessRecord P.n S)}

/-- Every process transition is Dirac: the rows here are, and so are the
implementation's own by `IsRoundRuleTable.dirac`. -/
theorem programStep_dirac [IsRoundRuleTable P M S roundStep]
    {l : ExtendedLabel P.n M} (h : ProgramStep P M S roundStep j q l ν) :
    ∃ q', ν = PMF.pure q' := by
  cases h
  case roundRow h' => exact IsRoundRuleTable.dirac h'
  all_goals exact ⟨_, rfl⟩

variable [IsRoundRuleTable P M S roundStep]

/-- The one `τ` row of a program's table is `terminate`: a silent step of a
program is that program's own termination, taken on a fired return and DECIDED
receipts from `2f + 1` distinct senders (D22). A replaced program has no silent
row at all, so the implementation carries `corrupted = false` (D23), and no
graded-agreement row is silent, `roundOwn` holding of no `τ`. -/
theorem programStep_tau_terminate
    (h : ProgramStep P M S roundStep j q (Silent.τ : ExtendedLabel P.n M) ν) :
    ∃ b : Bool, q.1.corrupted = false ∧ q.1.process.returned = true ∧
      2 * P.f + 1 ≤ q.1.decidedCount b ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, { q.2 with terminated := true }) := by
  rw [extendedLabel_tau] at h
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case terminate b hh hret hcnt hterm => exact ⟨b, hh, hret, hcnt, hterm, rfl⟩
  case corruptedIdle hh hτ hown => exact absurd rfl hτ

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as
its guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any record. A participant's row carries the health
guard `corrupted = false`, and on a label outside `actsAt j` the replaced
program's self-loop is a second row on the same label (D23). -/

theorem programStep_callABA_own {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.process.input = none ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with
        input := some b, estimate := some b, round := 0, phase := .toCallG }, q.2)) ∨
    ((q.1.corrupted = true ∨ q.1.process.input ≠ none) ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case input => exact Or.inl ⟨by assumption, by assumption, rfl⟩
  case inputLoop => exact Or.inr ⟨Or.inr (by assumption), rfl⟩
  case callABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨Or.inl (by assumption), rfl⟩

theorem programStep_callABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case input => exact absurd rfl hid
  case inputLoop => exact absurd rfl hid
  case callABAIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retABA_own {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retABA j b)) ν) :
    (q.1.corrupted = false ∧ q.1.process.input ≠ none ∧
      P.n - P.f ≤ q.1.decidedCount b ∧ q.1.process.returned = false ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with returned := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case ret =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retABAIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_retABA_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retABA id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case ret => exact absurd rfl hid
  case retABAIdle => rfl
  case corruptedIdle => rfl

theorem programStep_callG_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callG r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hid
  case callGIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retG_foreign {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retG r id out bnd)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hid
  case retGIdle => rfl
  case corruptedIdle => rfl

theorem programStep_callW_own {r : ℕ}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callW r j)) ν) :
    (q.1.corrupted = false ∧ q.1.process.phase = .toCallW ∧ q.1.process.round = r ∧
      ν = PMF.pure (q.1.setProcess { q.1.process with phase := .awaitW }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case callW => exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case callWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_callW_foreign {r : ℕ} {id : Fin P.n} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.callW r id)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case callW => exact absurd rfl hid
  case callWIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retW_own {r : ℕ} {co : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retW r j co)) ν) :
    (q.1.corrupted = false ∧ q.1.process.phase = .awaitW ∧ q.1.process.round = r ∧
      (∀ v : Bool, q.1.process.lastGrade ≠ some (.grade2 v)) ∧
      ν = PMF.pure (q.1.stepRound co, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retW =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_retW_foreign {r : ℕ} {id : Fin P.n} {co : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.retW r id co)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retW => exact absurd rfl hid
  case retWIdle => rfl
  case corruptedIdle => rfl

/-- The process's own corruption (D23): the flag goes up on a program not yet
replaced, and a replaced program is unchanged. -/
theorem programStep_fail_own (h : ProgramStep P M S roundStep j q (Sum.inl (.fail j)) ν) :
    (q.1.corrupted = false ∧ ν = PMF.pure ({ q.1 with corrupted := true }, q.2)) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case failSelf => exact Or.inl ⟨by assumption, rfl⟩
  case failIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_fail_foreign {k : Fin P.n} (hk : k ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inl (.fail k)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case failSelf => exact absurd rfl hk
  case failIdle => rfl
  case corruptedIdle => rfl

/-! ### One program's rules on the rendezvous alphabet

The Byzantine round rows have no row at the process they name (D22, D23), so on `byzantineCallG`,
`byzantineCallGLoop` and `byzantineRetG` every process idles and there is no participant's row to
read. -/

theorem programStep_gbcaSend_foreign {r : ℕ} {k : Fin P.n} {m : M} (hk : k ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.gbcaSend r k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hk
  case gbcaSendIdle => rfl
  case corruptedIdle => rfl

theorem programStep_gbcaDeliver_foreign {r : ℕ} {i k : Fin P.n} {m : M} (hi : i ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.gbcaDeliver r i k m)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hi
  case gbcaDeliverIdle => rfl
  case corruptedIdle => rfl

theorem programStep_decidedSend_self {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedSend j b)) ν) :
    (q.1.corrupted = false ∧ q.1.process.input ≠ none ∧
      P.f + 1 ≤ q.1.decidedCount b ∧ ν = PMF.pure q) ∨
    (q.1.corrupted = true ∧ ν = PMF.pure q) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedSendRelay =>
    exact Or.inl ⟨by assumption, by assumption, by assumption, rfl⟩
  case decidedSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => exact Or.inr ⟨by assumption, rfl⟩

theorem programStep_decidedSend_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedSend k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedSendRelay => exact absurd rfl hk
  case decidedSendIdle => rfl
  case corruptedIdle => rfl

theorem programStep_decidedDeliver_self {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedDeliver j k b)) ν) :
    q.1.corrupted = false ∧ b ∉ q.1.decidedDelivered k ∧
      ν = PMF.pure (q.1.receiveDecided k b, q.2) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedDeliverReceive => exact ⟨by assumption, by assumption, rfl⟩
  case decidedDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_decidedDeliver_foreign {i k : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.decidedDeliver i k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case decidedDeliverReceive => exact absurd rfl hi
  case decidedDeliverIdle => rfl
  case corruptedIdle => rfl

theorem programStep_retWPublish_self {r : ℕ} {co b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.retWPublish r j co b)) ν) :
    q.1.corrupted = false ∧
      q.1.process.phase = .awaitW ∧ q.1.process.round = r ∧
      q.1.process.lastGrade = some (.grade2 b) ∧
      ν = PMF.pure (q.1.stepRound co, q.2) := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retWPublish =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retWPublishIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retWPublish_foreign {r : ℕ} {id : Fin P.n} {co b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.retWPublish r id co b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  case retWPublish => exact absurd rfl hid
  case retWPublishIdle => rfl
  case corruptedIdle => rfl

theorem programStep_gbcaCallLoop_foreign {r : ℕ} {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : ProgramStep P M S roundStep j q (Sum.inr (.gbcaCallLoop r id b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact absurd (IsRoundRuleTable.own h') hid
  case gbcaCallLoopIdle => rfl
  case corruptedIdle => rfl

theorem programStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineCallGLoop r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  all_goals rfl

theorem programStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineCallW r k)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  all_goals rfl

theorem programStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineRetW r k b)) ν) :
    ν = PMF.pure q := by
  cases h
  case roundRow h' => exact (IsRoundRuleTable.own h').elim
  all_goals rfl

/-- The Byzantine graded-agreement call has no row at the process it names
(D11, D22, D23): the row carries its effect outside the program, and the
replaced program has no row on a label it acts on. -/
theorem programStep_byzantineCallG_noStep {r : ℕ} {b : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineCallG r j b)) ν) : False := by
  cases h with
  | roundRow _ _ _ h' => exact (IsRoundRuleTable.own h').elim
  | byzantineCallGIdle _ _ _ _ _ hk => exact hk rfl
  | corruptedIdle _ _ _ _ _ hown => exact hown rfl

/-- The Byzantine graded-agreement return has no row at the process it names
(D11, D22, D23). -/
theorem programStep_byzantineRetG_noStep {r : ℕ} {out : GBCAOutput} {bnd : Bool}
    (h : ProgramStep P M S roundStep j q (Sum.inr (.byzantineRetG r j out bnd)) ν) :
    False := by
  cases h with
  | roundRow _ _ _ h' => exact (IsRoundRuleTable.own h').elim
  | byzantineRetGIdle _ _ _ _ _ _ hk => exact hk rfl
  | corruptedIdle _ _ _ _ _ hown => exact hown rfl

/-- **The replaced program writes nothing** (D23). Whatever the label, a
process whose flag is up leaves both halves of its record where they stand.
Every row that writes carries the health guard, the implementation's own rows by
`IsRoundRuleTable.correct`, so no row of a replaced program survives except a
self-loop. -/
theorem programStep_noStep {L : ExtendedLabel P.n M} (hc : q.1.corrupted = true)
    (h : ProgramStep P M S roundStep j q L ν) : ν = PMF.pure q := by
  cases h
  case roundRow h' => rw [IsRoundRuleTable.correct h'] at hc; exact absurd hc (by simp)
  all_goals simp_all

end Inversion

/-! ### The network's rules, by label class -/

section NetInversion

variable {P : Parameters} {M G : Type} [DecidableEq M]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G}
    {ghostOutput : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop}
    {s : NetworkState P.n M G} {μ : PMF (NetworkState P.n M G)}

/-- Every network transition is Dirac. -/
theorem networkStep_dirac {l : ExtendedLabel P.n M}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s l μ) :
    ∃ s', μ = PMF.pure s' := by
  cases h <;> exact ⟨_, rfl⟩

theorem networkStep_gbcaSend {r : ℕ} {j : Fin P.n} {m : M}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.gbcaSend r j m)) μ) :
    μ = PMF.pure ((s.recordGBCASend r j m).writeGhost ghostStep (Sum.inr (.gbcaSend r j m))) := by
  cases h; rfl

theorem networkStep_gbcaDeliver {r : ℕ} {i j : Fin P.n} {m : M}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.gbcaDeliver r i j m)) μ) :
    m ∈ s.sent r j ∧ μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaDeliver r i j m))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_decidedSend {j : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.decidedSend j b)) μ) :
    b ∉ s.decidedSent j ∧ μ = PMF.pure (s.recordDecided j b) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_decidedDeliver {i j : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.decidedDeliver i j b)) μ)
    : b ∈ s.decidedSent j ∧ μ = PMF.pure s := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_retWPublish {r : ℕ} {id : Fin P.n} {c b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.retWPublish r id c b)) μ)
    :
    μ = PMF.pure ((s.recordDecided id b).writeGhost ghostStep (Sum.inr (.retWPublish r id c b))) :=
    by
  cases h; rfl

theorem networkStep_gbcaCallLoop {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.gbcaCallLoop r id b)) μ) :
    μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaCallLoop r id b))) := by
  cases h; rfl

theorem networkStep_byzantineCallGLoop {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s
      (Sum.inr (.byzantineCallGLoop r k b)) μ) :
    k ∈ s.F ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallGLoop r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_byzantineCallW {r : ℕ} {k : Fin P.n}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineCallW r k)) μ) :
    k ∈ s.F ∧ μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallW r k))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_byzantineRetW {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineRetW r k b)) μ) :
    k ∈ s.F ∧ μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetW r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_byzantineCallG {r : ℕ} {k : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inr (.byzantineCallG r k b)) μ)
    :
    k ∈ s.F ∧ μ = PMF.pure ((s.recordGBCASend r k (callPayload k b)).writeGhost ghostStep
      (Sum.inr (.byzantineCallG r k b))) := by
  cases h; exact ⟨by assumption, rfl⟩

/-- A Byzantine graded-agreement return is authorised by the corrupted set, and
the bound bit on its label stands in the round's ghost relation (D11). -/
theorem networkStep_byzantineRetG {r : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s
      (Sum.inr (.byzantineRetG r k out bnd)) μ) :
    k ∈ s.F ∧ ghostOutput s r k out bnd ∧
      μ = PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineRetG r k out bnd))) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem networkStep_callABA {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.callABA id b)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

/-- A return is authorised either by the DECIDED sent of the returning process
or by its corruption (D23); the two rows share the label and the identity
successor. -/
theorem networkStep_retABA {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retABA id b)) μ) :
    (b ∈ s.decidedSent id ∨ id ∈ s.F) ∧ μ = PMF.pure s := by
  cases h
  case retABA => exact ⟨Or.inl (by assumption), rfl⟩
  case retByzantine => exact ⟨Or.inr (by assumption), rfl⟩

theorem networkStep_callG {r : ℕ} {id : Fin P.n} {b : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.callG r id b)) μ) :
    μ = PMF.pure
    ((s.recordGBCASend r id (callPayload id b)).writeGhost ghostStep (Sum.inl (.callG r id b))) :=
    by
  cases h; rfl

/-- A graded-agreement return announces the round's ghost output: the bound bit
on the label stands in `ghostOutput` at the state the row starts from. -/
theorem networkStep_retG {r : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retG r id out bnd)) μ) :
    ghostOutput s r id out bnd ∧ μ = PMF.pure
    (s.writeGhost ghostStep (Sum.inl (.retG r id out bnd))) := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_callW {r : ℕ} {id : Fin P.n}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.callW r id)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem networkStep_retW {r : ℕ} {id : Fin P.n} {c : Bool}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.retW r id c)) μ) :
    μ = PMF.pure s := by
  cases h; rfl

theorem networkStep_fail {k : Fin P.n}
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl (.fail k)) μ) :
    k ∉ s.F ∧ s.F.card < P.f ∧ μ = PMF.pure (s.corrupt P k) := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

theorem networkStep_tau
    (h : NetworkStep P M G callPayload ghostStep ghostOutput s (Sum.inl .tau) μ) :
    (∃ (r : ℕ) (k : Fin P.n) (m : M), k ∈ s.F ∧ μ = PMF.pure (s.recordGBCASend r k m)) ∨
    (∃ (k : Fin P.n) (b : Bool), k ∈ s.F ∧ μ = PMF.pure (s.recordDecided k b)) := by
  cases h
  case byzantineGBCA => exact Or.inl ⟨_, _, _, by assumption, rfl⟩
  case byzantineDecided => exact Or.inr ⟨_, _, by assumption, rfl⟩

end NetInversion

end Implementation
end ABA
end PLTS
