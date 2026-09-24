/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.AFW.Components
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The graded-agreement round, composed

`GBCA.ByAFW.roundOverGathers`: the round-`r` graded-agreement round over two gather instances,
assembled from the round's programs of `ABA/GBCA/AFW/Components.lean` — the `n` graded-agreement
programs beside the round's network — and two gather instances, both in the binding form (D33),
each lifted along the pullback that names it. `roundOverGathersExtended` is the three factors in
parallel over the round-internal alphabet; `roundOverGathers` hides the round's three events there
and reads the result back over the family alphabet `ExtendedLabel n Empty`.

The composition is generic in the two gather instances: `roundOverGathers` takes them as arguments,
`roundOverBracha` supplies the gather instances over Bracha's broadcast,
`roundOverBroadcastSpecification` supplies the gather instances over the broadcast specification,
and `roundOverGatherSpecifications` supplies the lifted gather specifications
(`Gather.specificationOverInstanceAlphabet`). All three run on `RoundStateOverGathers n G₁ G₂`, and
the four `init` lemmas are the states they start from. `roundOverBracha` is the gather-based GBCA
implementation: AFW25's Algorithm 4 at `R = 2`, its two-gather branch, with the grade read off the
second gather's counts in place of the approximate-agreement subroutine of its lines 7 and 8 (D24).

## Views of the round's state

`programs`, `bound`, `firstGather` and `secondGather` read the four components of the round's
state, and `setPrograms`, `setBound`, `setFirstGather` and `setSecondGather` are the four writes
that reach one of them. `corruptAll` corrupts the two gather coordinates at once, the programs and
the round's bound bit untouched (D1).

## Determinacy

The transitions of the graded-agreement program and of the round's network
(`ABA/GBCA/AFW/Components.lean`) are Dirac, so the round is an LTS whenever the two gather
instances are: `roundOverBracha_isLTS`, `roundOverBroadcastSpecification_isLTS` and
`roundOverGatherSpecifications_isLTS` are the three instances of that.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-- The state of the round whose gather instances have states `G₁` and `G₂`. -/
abbrev RoundStateOverGathers (n : ℕ) (G₁ G₂ : Type) : Type :=
  ((∀ _ : Fin n, ProcessRecord n) × Option Bool) × (G₁ × G₂)

/-- The round's programs beside the two gather instances, over the round-internal alphabet. -/
noncomputable def roundOverGathersExtended (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))) :
    System (RoundStateOverGathers P.n G₁ G₂) (RoundLabel P.n) :=
  (roundPrograms P r).parallel ((firstGather.mapIdle (firstGatherLabelMap P.n)).parallel
    (secondGather.mapIdle
    (secondGatherLabelMap P.n)))

/-- **The round-`r` graded-agreement round** over the gather instances `firstGather`,
`secondGather`: the round's programs beside the two of them, the round's events hidden, the result
read over the family alphabet. -/
noncomputable def roundOverGathers (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))) :
    System (RoundStateOverGathers P.n G₁ G₂) (ExtendedLabel P.n Empty) :=
  ((roundOverGathersExtended P r firstGather secondGather).abstract (roundEvents P.n)).relabel

@[simp] theorem roundOverGathers_init (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))) :
    (roundOverGathers P r firstGather secondGather).init =
      (((fun _ => ProcessRecord.initial P.n), none), (firstGather.init, secondGather.init)) := rfl

/-- The state of the round over the gather instances over Bracha's
broadcast. -/
abbrev RoundStateOverBracha (n : ℕ) : Type :=
  RoundStateOverGathers n (Gather.StateOverBracha n Bool) (Gather.StateOverBracha n (Option Bool))

/-- The state of the round over the gather instances over the broadcast
specification. -/
abbrev RoundStateOverBroadcastSpecification (n : ℕ) : Type :=
  RoundStateOverGathers n (Gather.StateOverBroadcastSpecification n Bool)
    (Gather.StateOverBroadcastSpecification n (Option Bool))

/-- The state of the round over the gather specifications. -/
abbrev RoundStateOverGatherSpecifications (n : ℕ) : Type :=
  RoundStateOverGathers n (Gather.SpecState n Bool) (Gather.SpecState n (Option Bool))

/-- **The round over the gather instances over Bracha's broadcast.** -/
noncomputable def roundOverBracha (P : Parameters) (r : ℕ) :
    System (RoundStateOverBracha P.n) (ExtendedLabel P.n Empty) :=
  roundOverGathers P r (Gather.instanceOverBracha P Bool) (Gather.instanceOverBracha P (Option
    Bool))

/-- **The round over the gather instances over the broadcast
specification.** -/
noncomputable def roundOverBroadcastSpecification (P : Parameters) (r : ℕ) :
    System (RoundStateOverBroadcastSpecification P.n) (ExtendedLabel P.n Empty) :=
  roundOverGathers P r (Gather.instanceOverBroadcastSpecification P Bool)
    (Gather.instanceOverBroadcastSpecification P (Option Bool))

/-- **The round over the gather specifications.** -/
noncomputable def roundOverGatherSpecifications (P : Parameters) (r : ℕ) :
    System (RoundStateOverGatherSpecifications P.n) (ExtendedLabel P.n Empty) :=
  roundOverGathers P r (Gather.specificationOverInstanceAlphabet P Bool)
    (Gather.specificationOverInstanceAlphabet P (Option Bool))

@[simp] theorem roundOverBracha_init (P : Parameters) (r : ℕ) :
    (roundOverBracha P r).init =
      (((fun _ => ProcessRecord.initial P.n), none),
        ((Gather.instanceOverBracha P Bool).init,
          (Gather.instanceOverBracha P (Option Bool)).init)) := rfl

@[simp] theorem roundOverBroadcastSpecification_init (P : Parameters) (r : ℕ) :
    (roundOverBroadcastSpecification P r).init =
      (((fun _ => ProcessRecord.initial P.n), none),
        ((Gather.instanceOverBroadcastSpecification P Bool).init,
          (Gather.instanceOverBroadcastSpecification P (Option Bool)).init)) := rfl

@[simp] theorem roundOverGatherSpecifications_init (P : Parameters) (r : ℕ) :
    (roundOverGatherSpecifications P r).init =
      (((fun _ => ProcessRecord.initial P.n), none),
        (Gather.SpecState.initial P.n Bool, Gather.SpecState.initial P.n (Option Bool))) := rfl

/-! ### Views of the round's state

The four components of the round's state, and the four writes that reach one of
them. A transition is stated through these, so that a guard reads `programs s id`
where the implementation reads the program function. -/

section Views

variable {n : ℕ} {G₁ G₂ : Type}

/-- The programs. -/
def programs (s : RoundStateOverGathers n G₁ G₂) : ∀ _ : Fin n, ProcessRecord n := s.1.1

/-- The round's bound bit. -/
def bound (s : RoundStateOverGathers n G₁ G₂) : Option Bool := s.1.2

/-- The first gather instance. -/
def firstGather (s : RoundStateOverGathers n G₁ G₂) : G₁ := s.2.1

/-- The second gather instance. -/
def secondGather (s : RoundStateOverGathers n G₁ G₂) : G₂ := s.2.2

/-- Overwrite the programs. -/
def setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n, ProcessRecord n) :
    RoundStateOverGathers n G₁ G₂ := ((u, s.1.2), s.2)

/-- Overwrite the round's bound bit. -/
def setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) : RoundStateOverGathers n G₁ G₂
  :=
  ((s.1.1, v), s.2)

/-- Overwrite the first gather instance. -/
def setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) : RoundStateOverGathers n G₁ G₂ :=
  (s.1, (c, s.2.2))

/-- Overwrite the second gather instance. -/
def setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) : RoundStateOverGathers n G₁ G₂ :=
  (s.1, (s.2.1, d))

@[simp] theorem programs_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : programs (setPrograms s u) = u := rfl
@[simp] theorem bound_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : bound (setPrograms s u) = bound s := rfl
@[simp] theorem firstGather_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : firstGather (setPrograms s u) = firstGather s := rfl
@[simp] theorem secondGather_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : secondGather (setPrograms s u) = secondGather s := rfl

@[simp] theorem programs_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    programs (setBound s v) = programs s := rfl
@[simp] theorem bound_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    bound (setBound s v) = v := rfl
@[simp] theorem firstGather_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    firstGather (setBound s v) = firstGather s := rfl
@[simp] theorem secondGather_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    secondGather (setBound s v) = secondGather s := rfl

@[simp] theorem programs_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
    programs (setFirstGather s c) = programs s := rfl
@[simp] theorem bound_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
    bound (setFirstGather s c) = bound s := rfl
@[simp] theorem firstGather_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
  firstGather (setFirstGather s c) = c := rfl
@[simp] theorem secondGather_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
    secondGather (setFirstGather s c) = secondGather s := rfl

@[simp] theorem programs_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
    programs (setSecondGather s d) = programs s := rfl
@[simp] theorem bound_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
    bound (setSecondGather s d) = bound s := rfl
@[simp] theorem firstGather_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
    firstGather (setSecondGather s d) = firstGather s := rfl
@[simp] theorem secondGather_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
  secondGather (setSecondGather s d) = d := rfl

/-- Corruption (deviation D1): the two gather instances corrupted at `id`, the
programs and the round's bound bit untouched. -/
def corruptAll (P : Parameters) (id : Fin P.n) (corruptFirstGather : Fin P.n → G₁ → G₁)
    (corruptSecondGather : Fin P.n → G₂ → G₂) (s : RoundStateOverGathers P.n G₁ G₂) :
    RoundStateOverGathers P.n G₁ G₂ :=
  (s.1, (corruptFirstGather id s.2.1, corruptSecondGather id s.2.2))

@[simp] theorem programs_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    programs (corruptAll P id corruptFirstGather corruptSecondGather s) = programs s := rfl
@[simp] theorem bound_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    bound (corruptAll P id corruptFirstGather corruptSecondGather s) = bound s := rfl
@[simp] theorem firstGather_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    firstGather (corruptAll P id corruptFirstGather corruptSecondGather s) =
      corruptFirstGather id (firstGather s) := rfl
@[simp] theorem secondGather_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    secondGather (corruptAll P id corruptFirstGather corruptSecondGather s) =
      corruptSecondGather id (secondGather s) := rfl

end Views

/-! ### Determinacy

The transitions of the graded-agreement program and of the round's network
(`ABA/GBCA/AFW/Components.lean`) are Dirac, so the round is an LTS whenever the
two gather instances are. -/

section Determinacy

variable {P : Parameters} {r : ℕ}

/-- Every program transition is Dirac. -/
theorem programStep_dirac {j : Fin P.n} {p : ProcessRecord P.n} {l : ProgramLabel P.n}
    {ν : PMF (ProcessRecord P.n)} (h : ProgramStep P r j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every transition of the round's network is Dirac. -/
theorem networkStep_dirac {w : Option Bool} {l : ProgramLabel P.n} {μ : PMF (Option Bool)}
    (h : NetworkStep P r w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem gbcaProgram_isLTS (P : Parameters) (r : ℕ) (j : Fin P.n) : (gbcaProgram P r j).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The round's network is an LTS. -/
theorem GBCANetwork_isLTS (P : Parameters) (r : ℕ) : (GBCANetwork P r).IsLTS :=
  fun _ _ _ h => networkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem programsProduct_isLTS (P : Parameters) (r : ℕ) :
    (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap P.n))).IsLTS
      :=
  System.synchronisedProduct_isLTS (fun j => System.mapIdle_isLTS _ (gbcaProgram_isLTS P r j))

/-- The round's programs form an LTS. -/
theorem roundPrograms_isLTS (P : Parameters) (r : ℕ) : (roundPrograms P r).IsLTS :=
  System.parallel_isLTS (programsProduct_isLTS P r)
    (System.mapIdle_isLTS _ (GBCANetwork_isLTS P r))

/-- The round's programs beside the two gather instances is an LTS. -/
theorem roundOverGathersExtended_isLTS (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    {firstGather : System G₁ (Gather.InstanceLabel P.n Bool)}
    {secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))} (h1 : firstGather.IsLTS)
    (h2 : secondGather.IsLTS) : (roundOverGathersExtended P r firstGather secondGather).IsLTS :=
  System.parallel_isLTS (roundPrograms_isLTS P r)
    (System.parallel_isLTS (System.mapIdle_isLTS _ h1) (System.mapIdle_isLTS _ h2))

/-- The round is an LTS. -/
theorem roundOverGathers_isLTS (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    {firstGather : System G₁ (Gather.InstanceLabel P.n Bool)}
    {secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))} (h1 : firstGather.IsLTS)
    (h2 : secondGather.IsLTS) : (roundOverGathers P r firstGather secondGather).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (roundOverGathersExtended_isLTS P r h1 h2) _)

/-- The round over the gather instances over Bracha's broadcast is an LTS. -/
theorem roundOverBracha_isLTS (P : Parameters) (r : ℕ) : (roundOverBracha P r).IsLTS :=
  roundOverGathers_isLTS P r (Gather.instanceOverBracha_isLTS P) (Gather.instanceOverBracha_isLTS P)

/-- The round over the gather instances over the broadcast specification is an
LTS. -/
theorem roundOverBroadcastSpecification_isLTS (P : Parameters) (r : ℕ) :
  (roundOverBroadcastSpecification P r).IsLTS :=
  roundOverGathers_isLTS P r (Gather.instanceOverBroadcastSpecification_isLTS P)
    (Gather.instanceOverBroadcastSpecification_isLTS P)

/-- The round over the gather specifications is an LTS. -/
theorem roundOverGatherSpecifications_isLTS (P : Parameters) (r : ℕ) :
    (roundOverGatherSpecifications P r).IsLTS :=
  roundOverGathers_isLTS P r (Gather.specificationOverInstanceAlphabet_isLTS P)
    (Gather.specificationOverInstanceAlphabet_isLTS P)

/-- No program transition fires on the silent label: a program only ever moves on one
of the round's ports or one of its events. -/
theorem programStep_no_tau {j : Fin P.n} {p : ProcessRecord P.n} {ν : PMF (ProcessRecord P.n)}
    (h : ProgramStep P r j p (Silent.τ : ProgramLabel P.n) ν) : False := by
  rw [programLabel_tau] at h; cases h

/-- No transition of the round's network fires on the silent label. -/
theorem networkStep_no_tau {w : Option Bool} {μ : PMF (Option Bool)}
    (h : NetworkStep P r w (Silent.τ : ProgramLabel P.n) μ) : False := by
  rw [programLabel_tau] at h; cases h

/-- No program transition fires on a family label outside the round's interface. -/
theorem programStep_outside {j : Fin P.n} {p : ProcessRecord P.n} {ν : PMF (ProcessRecord P.n)}
    (h : ProgramStep P r j p ProgramLabel.outside ν) : False := by cases h

/-- No transition of the round's network fires on a family label outside the round's interface. -/
theorem networkStep_outside {w : Option Bool} {μ : PMF (Option Bool)}
    (h : NetworkStep P r w ProgramLabel.outside μ) : False := by cases h

/-- The program group has no silent transition. -/
theorem programsProduct_no_tau {u : ∀ _ : Fin P.n, ProcessRecord P.n}
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n)}
    (h : (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap
      P.n))).step u
      (Silent.τ : RoundLabel P.n) μ) : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau ((System.mapIdle_step_some (programLabelMap_tau P.n) _).mp hstep)

/-- The round's programs have no silent transition: neither a program nor the round's network fires
on the silent label. -/
theorem roundPrograms_no_tau {u : ∀ _ : Fin P.n, ProcessRecord P.n} {v : Option Bool}
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) (Silent.τ : RoundLabel P.n) μ) : False := by
  rw [roundPrograms, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, -⟩ | ⟨-, μ₂, hn, -⟩
  · exact hτ rfl
  · exact programsProduct_no_tau hs
  · exact networkStep_no_tau ((System.mapIdle_step_some (programLabelMap_tau P.n) _).mp hn)

end Determinacy

end GBCA.ByAFW
end ABA
end PLTS
